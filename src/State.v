From RecordUpdate Require Import RecordSet.
Require ABI Core Decommitter GPR Ergs Event Memory History CallStack VMPanic.

Import Core Flags ZArith ABI Common GPR Ergs Event CallStack History MemoryBase Memory ZMod List Decommitter Predication VMPanic.
Import ListNotations RecordSetNotations.

Section Definitions.

Definition exception_handler := code_address.

(* begin details: helpers *)
Definition instruction_invalid : predicated Assembly.asm_instruction := invalid Assembly.OpInvalid.
Definition decommitter := decommitter instruction_invalid.
Definition code_page := code_page instruction_invalid.
Definition memory := @memory code_page const_page data_page stack_page.
Definition query := @query contract_address PrecompileParameters.params.
Definition event := @event contract_address.
Definition page_has_id := @page_has_id code_page const_page data_page stack_page.


(* end details *)

(** # EraVM state

EraVM employs a [%state] that comprises the following components:

1. The [%global_state] contains:
- current price of publishing one byte of **pubdata** to L1 [%gs_current_ergs_per_pubdata_byte].
- transaction number in the current block [%gs_tx_number_in_block]
- decommitter [%gs_contracts]
- a revertable part [%state_checkpoint]. It houses the **depot** state, embodying
   all contracts storages across all shards, as well as two queues for events
   and L1 messages.

   Launching a contract (far call) or a function (near call) defines a
   checkpoint.
   If a contract or a function reverts or panics, the state rolls back
   to the latest snapshot (see [%rollback]).

   The rollback may be implemented in any efficient way conforming to this behavior.
*)
Record state_checkpoint := {
    gs_depot: depot;
    gs_events: @history query;
    gs_l1_msgs: @history event;
  }.

Record global_state :=
  mk_gstate {
    gs_current_ergs_per_pubdata_byte: ergs;
    gs_tx_number_in_block: tx_num;
    gs_contracts: decommitter;
    gs_revertable:> state_checkpoint;
    }.

Inductive rollback checkpoint: global_state -> global_state -> Prop :=
| rb_apply: forall e tx ccs ___,
  rollback checkpoint (mk_gstate e tx ccs ___) (mk_gstate e tx ccs checkpoint).

(** 2. The [%transient_state] contains:
  - flags [%gs_flags]: boolean values representing some characteristics of the computation results. See [%Flags].
  - general purpose registers [%gs_regs]: 15 mutable tagged words (primitive values) [%r1]--[%r15], and a reserved read-only zero valued [%r0]. See [%Registers].
  - all memory [%gs_pages] allocated by VM, including code pages, data stack pages, data pages for heap variants etc. See [%memory].
  - [%gs_callstack], where each currently running contract and function has a stack frame. Note, that program counter, data stack pointer, and the remaining ergs allocated for the current function's run are parts of a stack frame. See [%CallStack].
  - 128-bit register [%gs_context_u128]. Its usage is detailed below.
 *)
(* begin details: helpers *)
Definition callstack := @callstack state_checkpoint.
(* end details *)

Record transient_state :=
  mk_transient_state {
      gs_flags : flags_state;
      gs_regs: regs_state;
      gs_pages: memory;
      gs_callstack: callstack;
      gs_context_u128: u128;
      gs_status: status;
    }.

Record state :=
  mk_state {
      gs_transient :> transient_state;
      gs_global :> global_state;
    }.

(** ## Context register

The 128-bit context value occurs in two places in EraVM:

- In the mutable [%gs_context_u128] register, forming a part of the EraVM state [%state].
- In the read-only [%ecf_context_u128_value] of each external call stack frame [%callstack_external].

These values are distinct: the value in callstack is a snapshot of the register
[%gs_context_u128] in a moment of a far call.

The typical usage of the context value is as follows:

1. Set the value of [%gs_context_u128] to $C$ by executing the instruction [%OpContextSetContextU128].
2. Launch a contract using one of the far call instructions. This action pushes a new [%callstack_external] frame $F$ onto the [%gs_callstack]. The value of the $F$'s field [%ecf_context_u128_value] is equal to $C$. In addition, far calls reset [%gs_context_u128] to 0.
3. Retrieve the context value by executing the instruction [%OpContextGetContextU128] to use it.
4. On contract code completion, the [%gs_context_u128] is reset to zero by either [%OpFarRet], [%OpFarRevert], or [%OpPanic].

Note that setting the context register [%gs_context_u128] is forbidden in [%StaticMode]. See [%forbidden_static].

Context is used to simulate `msg.value`, a Solidity construction standing for the amount of wei sent in a transaction.
A system contract `MsgValueSimulator` is respondible for ensuring that whenever this context value is set to $C$, there is indeed $C$ wei transfered to the callee.
 *)

(* begin hide *)

#[export] Instance etaXGS : Settable _ := settable! mk_gstate <gs_current_ergs_per_pubdata_byte; gs_tx_number_in_block; gs_contracts; gs_revertable>.
#[export] Instance etaXS : Settable _ := settable! mk_transient_state <gs_flags ; gs_regs; gs_pages; gs_callstack; gs_context_u128; gs_status>.
#[export] Instance etaXGGS : Settable _ := settable! mk_state <gs_transient; gs_global> .

(* end hide *)

(* begin details: Helpers *)
Inductive global_state_new_depot: depot -> global_state -> global_state -> Prop :=
| gsnd_apply: forall current_ergs_per_pubdata_byte tx codes d evs l1s d',
  global_state_new_depot d'
  {|
    gs_current_ergs_per_pubdata_byte := current_ergs_per_pubdata_byte;
    gs_tx_number_in_block := tx;
    gs_contracts := codes;
    gs_revertable := {| gs_depot := d; gs_events := evs; gs_l1_msgs := l1s |} ;
  |}
  {|
    gs_current_ergs_per_pubdata_byte := current_ergs_per_pubdata_byte;
    gs_tx_number_in_block := tx;
    gs_contracts := codes;
    gs_revertable := {| gs_depot := d'; gs_events := evs; gs_l1_msgs := l1s |} ;
  |}.


Inductive emit_event e: global_state -> global_state -> Prop :=
| ee_apply: forall current_ergs_per_pubdata_byte tx codes d evs l1s d',
  emit_event e
  {|
    gs_current_ergs_per_pubdata_byte := current_ergs_per_pubdata_byte;
    gs_tx_number_in_block := tx;
    gs_contracts := codes;
    gs_revertable := {| gs_depot := d; gs_events := evs; gs_l1_msgs := l1s |} ;
  |}
  {|
    gs_current_ergs_per_pubdata_byte := current_ergs_per_pubdata_byte;
    gs_tx_number_in_block := tx;
    gs_contracts := codes;
    gs_revertable := {| gs_depot := d'; gs_events := e::evs; gs_l1_msgs := l1s |} ;
  |}.

Inductive emit_l1_msg e: global_state -> global_state -> Prop :=
| eel1_apply: forall current_ergs_per_pubdata_byte tx codes d evs l1s d',
  emit_l1_msg e
  {|
    gs_current_ergs_per_pubdata_byte := current_ergs_per_pubdata_byte;
    gs_tx_number_in_block := tx;
    gs_contracts := codes;
    gs_revertable := {| gs_depot := d; gs_events := evs; gs_l1_msgs := l1s |} ;
  |}
  {|
    gs_current_ergs_per_pubdata_byte := current_ergs_per_pubdata_byte;
    gs_tx_number_in_block := tx;
    gs_contracts := codes;
    gs_revertable := {| gs_depot := d'; gs_events := evs; gs_l1_msgs := e::l1s |} ;
  |}.

Inductive tx_inc : tx_num -> tx_num -> Prop := | txi_apply: forall n m, uinc_overflow _ n = (m, false) -> tx_inc n m.

Inductive global_state_increment_tx tx_mod: global_state -> global_state -> Prop :=
| gsit_apply: forall current_ergs_per_pubdata_byte tx new_tx codes rev ,
  tx_mod tx new_tx ->
  global_state_increment_tx tx_mod
  {|
    gs_current_ergs_per_pubdata_byte := current_ergs_per_pubdata_byte;
    gs_tx_number_in_block := tx;
    gs_contracts := codes;
    gs_revertable := rev;
  |}
  {|
    gs_current_ergs_per_pubdata_byte := current_ergs_per_pubdata_byte;
    gs_tx_number_in_block := new_tx;
    gs_contracts := codes;
    gs_revertable := rev;
  |}.

End Definitions.

Definition heap_variant_page_id (page_type: data_page_type)
  : callstack -> page_id :=
  match page_type with
  | Heap => @active_heap_id state_checkpoint
  | AuxHeap => @active_auxheap_id state_checkpoint
  end.


Definition heap_variant_page (page_type: data_page_type) (cs:callstack) (mem:memory) :=
    match page_type with
    | Heap => active_heappage
    | AuxHeap =>  active_auxheappage
    end (page_has_id mem) cs .

Definition heap_variant_id (page_type: data_page_type)
  :  callstack -> page_id :=
  match page_type with
  | Heap => @active_heap_id
  | AuxHeap => @active_auxheap_id
  end state_checkpoint.

(* end details *)
