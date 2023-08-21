From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Common Ergs Memory MemoryContext.

Import Common Ergs MemoryContext Memory List ListNotations.

Section Callstack.

  Context (CALLSTACK_LIMIT : nat).
  Context {state_checkpoint: Type} {ins: Type} (ins_invalid: ins).

  Definition exception_handler := code_address.

  (** # Call stack

EraVM operates with two stacks:

1. call stack, which supports function and contract execution
2. data stack, aiding in computations.

Data stack has a role similar to the stack in JVM and other language virtual
machines.
Call stack may be implemented in any way, but it is separated from data
stack.
This section covers the call stack in detail.


A **stack frame**, or **call frame**, is a data structure representing a
  fragment of current execution environment associated with a running instance
  of a contract or a function.

There are two types of stack frames:

- External frames [%ExternalCall]: created on far calls (by instructions [%OpFarCall],
  [%OpMimicCall], [%OpDelegateCall]).
- Internal frames [%InternalCall]: created by near calls (by instruction [%OpNearCall]).

Each external frame is **associated** with a contract address. It means that it
was created when the associated contract address was far called.
Naturally, each contract may be called many times recursively, therefore at each
moment of time any contract may have multiple external frames associated to it.


**[%callstack]** is a stack of a maximum of [%CALLSTACK_LIMIT] stack frames.
It is unrelated to the [%stack_page] which holds data stack.

There is one callstack per execution, stored in [%state] in [%gs_callstack] field.

Internal call frames hold the following information:

- [%cf_exception_handler_location]: a [%code_address] of an exception handler.
  On revert or panic VM destroys the topmost frame and jumps to this handler.
- [%cf_sp]: current **data stack** pointer. The topmost element in data stack is located
  at [%cf_sp-1] in the currently [%active_stackpage].
- [%cf_ergs_remaining]: ergs allocated for the current function or contract.
  It decreases as VM spends ergs for its operation.
- [%cf_saved_checkpoint] : a snapshot of the state for a rollback. In case of panic or revert, the state of storage and event queues will be restored.
*)
  Record callstack_common := mk_cf {
                                 cf_exception_handler_location: exception_handler;
                                 cf_sp: stack_address;
                                 cf_pc: code_address;
                                 cf_ergs_remaining: ergs;
                                 cf_saved_checkpoint: state_checkpoint;
                               }.

  (* begin hide *)
  #[export] Instance etaCFC : Settable _ :=
    settable! mk_cf < cf_exception_handler_location; cf_sp; cf_pc; cf_ergs_remaining; cf_saved_checkpoint >.
  (* end hide *)
(** External call frames hold the same information as internal. Additionally, they
hold:

- Three associated contract addresses:

   1. [%ecf_this_address] : the stack frame was created when this contract was called.
   2. [%ecf_msg_sender] : the stack frame was created when this contract invoked one
  of far call instructions.
   3. [%ecf_code_address] : which contract owns the code associated with the stack frame. It is not always the same contract as [%ecf_this_address].

- [%ecf_mem_ctx] : current [%mem_ctx] holding ids of active stack, heap variants, code, const pages and bounds of data pages.
- boolean [%ecf_is_static] : true if the code associated with this frame is being executed in static mode.
- [%ecf_context_u128_value] : captured value of [%gs_context_u128]. It
  represents a snapshot of the value of global register [%gs_context_u128] in a
  moment of far call to the current contract.
- [%ecf_shards] : shards associated with [%ecf_this_address], [%ecf_msg_sender] and [%ecf_code_address].
 *)

  Record active_shards := mk_shards {
                              shard_this: shard_id;
                              shard_caller: shard_id;
                              shard_code: shard_id;
                            }.

  (* begin hide *)
  #[export] Instance etaSH: Settable _ :=
    settable! mk_shards < shard_this; shard_caller; shard_code>.
  (* end hide *)

  Record associated_contracts :=
    mk_assoc_contracts {
        ecf_this_address: contract_address;
        ecf_msg_sender: contract_address;
        ecf_code_address: contract_address;
      }.

  Record callstack_external :=
    mk_extcf {
        ecf_associated:> associated_contracts;
        ecf_mem_ctx: mem_ctx;
        ecf_is_static: bool; (* forbids any write-like "log" and so state modifications, event emissions, etc *)
        ecf_context_u128_value: u128;
        ecf_shards:> active_shards;
        ecf_common :> callstack_common
      }.

  (* begin hide *)
  #[export] Instance etaACE : Settable _ := settable! mk_assoc_contracts < ecf_this_address; ecf_msg_sender; ecf_code_address >.
  #[export] Instance etaCFE : Settable _ :=
    settable! mk_extcf < ecf_associated; ecf_mem_ctx; ecf_is_static; ecf_context_u128_value; ecf_shards; ecf_common>.
  (* end hide *)

  Inductive callstack :=
  | InternalCall (_: callstack_common) (tail: callstack): callstack
  | ExternalCall (_: callstack_external) (tail: option callstack): callstack.

  Fixpoint callstack_depth cf :=
    (match cf with
     | InternalCall x tail => 1 + callstack_depth tail
     | ExternalCall x (Some tail)=> 1 + callstack_depth tail
     | ExternalCall x None => 1
     end)%nat.

  (** ## Operation

When the server starts forming a new block, it starts a new instance of VM to execute the code called [%Bootloader].
Bootloader is a contract with an address [%BOOTLOADER_SYSTEM_CONTRACT_ADDRESS].
To support its execution, a corresponding [%ExternalCall] frame with is pushed to the call stack.

Handling each transaction requires executing [%OpFarCall], which pushes another
call frame to the callstack.

As the transaction is executed, call stack changes as follows:

- [%OpNearCall] pushes an [%InternalCall] frame to callstack.
- [%OpFarCall], [%OpDelegateCall], or [%OpMimicCall] push an [%ExternalCall] frame to callstack.
- [%OpNearRet], [%OpNearRetTo], [%OpNearRevert], [%OpNearRevertTo], [%OpPanic], [%OpFarRet], [%OpFarRevert] pop a frame from callstack.

Attempting to have more than [%CALLSTACK_LIMIT] elements in callstack will force the VM into panic.

Panics are equivalent to executing [%OpPanic], so they pop up the topmost stack frame and pass the control to the exception handler, specified in the popped frame.

Executing any instruction $I$ changes the topmost frame:

1. [%cf_pc] is incremented, unless $I$ is [%OpJump] .
2. [%cf_sp] may be modified if $I$ affects the data stack pointer through addressing modes [%RelSpPop] or [%RelSpPop].
3. [%cf_ergs_remaining] is decreased by the **total cost** of $I$. Total cost
   is a sum of [%base_cost] and additional costs, described by the small step
   predicates like [%step_jump].

   *)
  Definition stack_overflow (xstack:callstack) : bool :=
    Nat.ltb CALLSTACK_LIMIT (callstack_depth xstack).

  Definition cfc (ef: callstack) : callstack_common :=
    match ef with
    | InternalCall x _ => x
    | ExternalCall x _ => x
    end.

  Definition cfc_map (f:callstack_common->callstack_common) (ef: callstack) : callstack :=
    match ef with
    | InternalCall x tail => InternalCall (f x) tail
    | ExternalCall x tail => ExternalCall (x <| ecf_common ::= f |>) tail
    end.


  Section ErgsManagement.

    Import ZMod.
    Open Scope ZMod_scope.

    Definition ergs_remaining (ef:callstack) : ergs := (cfc ef).(cf_ergs_remaining).
    Definition ergs_map (f: ergs->ergs) (ef:callstack) : callstack
      := cfc_map (fun x => x <| cf_ergs_remaining ::= f |>) ef.
    Definition ergs_set newergs := ergs_map (fun _ => newergs).

    Inductive ergs_return: ergs -> callstack -> callstack -> Prop :=
    | er_return: forall delta new_ergs ef ef',
        delta + ergs_remaining ef = (new_ergs, false) ->
        ef' = ergs_set new_ergs ef ->
        ergs_return delta ef ef'.


    Inductive ergs_return_caller_and_drop : callstack -> callstack -> Prop
      :=
    |erc_internal: forall caller new_caller cf,
        ergs_return (ergs_remaining (InternalCall cf caller)) caller
          new_caller ->
        ergs_return_caller_and_drop (InternalCall cf caller) new_caller
    |erc_external: forall caller new_caller cf,
        ergs_return (ergs_remaining (ExternalCall cf (Some caller))) caller
          new_caller ->
        ergs_return_caller_and_drop (ExternalCall cf (Some caller)) new_caller.

    Definition ergs_reset := ergs_set zero32.

    Definition affordable (ef: callstack) (e:ergs): bool :=
      match ergs_remaining ef - e with
      | (paid, false) => true
      | (overflowed, true) => false
      end.

    Inductive pay : ergs -> callstack -> callstack -> Prop :=
    | pay_ergs : forall e ef paid,
        ergs_remaining ef - e = (paid, false) ->
        pay e ef (ergs_set paid ef).
  End ErgsManagement.


  Section SP.
    (** Fetching value of the stack pointer itself. *)
    Definition sp_get (cf: callstack) : stack_address :=
      (cfc cf).(cf_sp).

    Definition sp_map_extcall (f:stack_address->stack_address) ef :=
      (ef <| ecf_common ::= fun cf => cf <| cf_sp ::=  f |> |>).

    Inductive sp_map_extcall_spec f: callstack_external -> callstack_external -> Prop :=
    | sme_apply: forall a d e g h eh sp pc ss ergs,
        sp_map_extcall_spec f (mk_extcf a d e g h (mk_cf eh sp pc ergs ss))
          (mk_extcf a d e g h (mk_cf eh (f sp) pc ergs ss)).

    Theorem sp_map_extcall_correct:
      forall f ef, sp_map_extcall_spec f ef (sp_map_extcall f ef).
    Proof.
      intros f [].
      destruct ecf_common0.
      constructor.
    Qed.

    Definition sp_map (f:stack_address->stack_address) ef : callstack :=
      match ef with
      | InternalCall x tail => InternalCall (x <| cf_sp ::=  f |>) tail
      | ExternalCall x tail => ExternalCall (sp_map_extcall f x) tail
      end.

    Definition sp_update new_sp := sp_map (fun _ => new_sp).

    Inductive sp_map_spec f : callstack -> callstack -> Prop :=
    | usp_ext:
      forall ecf ecf' tail,
        sp_map_extcall_spec f ecf ecf' ->
        sp_map_spec f (ExternalCall ecf tail) (ExternalCall ecf' tail)
    | usp_int:
      forall  eh sp pc ergs tail ss,
        sp_map_spec f (InternalCall (mk_cf eh sp pc ergs ss ) tail) (InternalCall (mk_cf eh (f sp) pc ergs ss) tail).

    Theorem sp_map_spec_correct f:
      forall ef, sp_map_spec f ef (sp_map f ef).
    Proof.
      destruct ef; destruct c; constructor.
      apply sp_map_extcall_correct.
    Qed.

  End SP.


  Section PC.
    Definition pc_get (ef: callstack) : code_address :=
      match ef with
      | InternalCall cf _ => cf.(cf_pc)
      | ExternalCall ef tail => ef.(ecf_common).(cf_pc)
      end.

    Definition pc_map f ef :=
      match ef with
      | InternalCall x tail => InternalCall (x <| cf_pc ::=  f |>) tail
      | ExternalCall x tail => ExternalCall (x <| ecf_common ::= fun cf => cf <| cf_pc ::=  f |> |>) tail
      end.


    Definition pc_set new := pc_map (fun _ => new).

    Inductive pc_map_cfc_spec f : callstack_common -> callstack_common
                              -> Prop :=
    | upc_map:
      forall ehl sp ergs pc pc' ss,
        f pc = pc' ->
        pc_map_cfc_spec f (mk_cf ehl sp pc ergs ss) (mk_cf ehl sp pc' ergs ss).

    Inductive pc_map_extcall_spec f: callstack_external -> callstack_external
                                 -> Prop :=
    | upe_update:
      forall cf cf' ac memory is_static context_u128_value cc,
        pc_map_cfc_spec f cf cf' ->
        pc_map_extcall_spec f
          (mk_extcf ac memory is_static
             context_u128_value cc cf)
          (mk_extcf ac memory is_static
             context_u128_value cc cf')
    .

    Inductive pc_map_spec f : callstack -> callstack -> Prop :=
    | upc_ext:
      forall ecf ecf' tail ,
        pc_map_extcall_spec f ecf ecf' ->
        pc_map_spec f (ExternalCall ecf tail) (ExternalCall ecf' tail)
    | upc_int:
      forall cf cf' tail,
        pc_map_cfc_spec f cf cf' ->
        pc_map_spec f (InternalCall cf tail) (InternalCall cf' tail).

    Theorem pc_map_correct:
      forall ef f, pc_map_spec f ef (pc_map f ef).
    Proof.
      intros [ []|[] ] pc; simpl; [|destruct ecf_common0]; repeat constructor.
    Qed.

  End PC.

  Section TopmostExternalFrame.

    Fixpoint active_extframe (ef : callstack) : callstack_external :=
      match ef with
      | InternalCall _ tail => active_extframe tail
      | ExternalCall x tail => x
      end.

    Inductive active_extframe_spec : callstack -> callstack_external -> Prop :=
    | te_Top: forall x t, active_extframe_spec (ExternalCall x t) x
    | te_Deeper: forall c t f,
        active_extframe_spec t f -> active_extframe_spec (InternalCall c t) f
    .
    Theorem active_extframe_correct:
      forall ef, active_extframe_spec ef (active_extframe ef).
    Proof.
      induction ef; constructor; auto.
    Qed.


    Fixpoint change_active_extframe f (ef:callstack) : callstack :=
      match ef with
      | InternalCall x tail => InternalCall x (change_active_extframe f tail)
      | ExternalCall x tail => ExternalCall (f x) tail
      end.

    Inductive change_active_extframe_spec f : callstack -> callstack -> Prop :=
    | ct_base: forall cf t,
        change_active_extframe_spec f (ExternalCall cf t) (ExternalCall (f cf) t)
    | ct_ind: forall cf t t',
        change_active_extframe_spec f t t' ->
        change_active_extframe_spec f (InternalCall cf t) (InternalCall cf t')
    .

    Lemma change_active_extframe_correct : forall f ef,
        change_active_extframe_spec f ef (change_active_extframe f ef).
    Proof.
      intros f ef.
      induction ef as [x tail | x tail]; simpl.
      - apply ct_ind; apply IHtail.
      - simpl.
        apply ct_base.
    Qed.

    Definition update_memory_context (ctx:mem_ctx): callstack -> callstack :=
      change_active_extframe (fun ef => ef <| ecf_mem_ctx := ctx |> ).

    Definition revert_state (cs:callstack) : state_checkpoint :=
      match cs with
      | InternalCall x tail => x.(cf_saved_checkpoint)
      | ExternalCall x tail => x.(ecf_common).(cf_saved_checkpoint)
      end .


    Definition current_shard xstack : shard_id := (active_extframe xstack).(ecf_shards).(shard_this).

    Definition current_contract xstack : contract_address := ecf_this_address (active_extframe xstack).

  End TopmostExternalFrame.


  Section ActiveMemory.

    Section ActivePageId.

      Context (ef:callstack) (active_extframe := active_extframe ef).


      Definition get_mem_ctx: mem_ctx := active_extframe.(ecf_mem_ctx).

      Definition active_code_id: page_id := get_mem_ctx.(ctx_code_page_id).

      Definition active_stack_id: page_id := get_mem_ctx.(ctx_stack_page_id).

      Definition active_const_id: page_id := get_mem_ctx.(ctx_const_page_id).

      Definition active_heap_id : page_id := get_mem_ctx.(ctx_heap_page_id).

      Definition active_auxheap_id : page_id := get_mem_ctx.(ctx_auxheap_page_id).

      Definition heap_bound := get_mem_ctx.(ctx_heap_bound).

      Definition auxheap_bound := get_mem_ctx.(ctx_auxheap_bound).

      Definition heap_variant_bound (page_type:data_page_type):  mem_address :=
        match page_type with
        | Heap => heap_bound
        | AuxHeap => auxheap_bound
        end.

      Definition heap_variant_page_id (page_type: data_page_type)
        : page_id :=
        match page_type with
        | Heap => active_heap_id
        | AuxHeap => active_auxheap_id
        end.
    End ActivePageId.



    Section ActivePages.

      Context {code_page const_page data_page stack_page} (page_has_id: page_id -> @page code_page const_page data_page stack_page -> Prop).

      Definition active_exception_handler (ef: callstack) : exception_handler :=
        (cfc ef).(cf_exception_handler_location).


      Context (ef: callstack) (page_id := fun i => page_has_id (i ef)).

      Inductive active_codepage : code_page -> Prop :=
      | ap_active_code: forall codepage,
          page_id active_code_id (mk_page (CodePage codepage)) ->
          active_codepage codepage.

      Inductive active_constpage : const_page -> Prop :=
      | ap_active_const: forall constpage,
          page_id  active_const_id (mk_page (ConstPage constpage)) ->
          active_constpage  constpage.

      Inductive active_stackpage : stack_page -> Prop :=
      | ap_active_stack: forall  stackpage,
          page_id active_stack_id (mk_page (StackPage stackpage)) ->
          active_stackpage stackpage.

      Inductive active_heappage : data_page -> Prop :=
      | ap_active_heap: forall p,
          page_id active_heap_id (mk_page (DataPage p)) ->
          active_heappage p.

      Inductive active_auxheappage : data_page -> Prop :=
      | ap_active_auxheap: forall p,
          page_id active_auxheap_id (mk_page (DataPage p)) ->
          active_auxheappage p.
    End ActivePages.

  End ActiveMemory.
End Callstack.
