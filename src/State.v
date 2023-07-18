From RecordUpdate Require Import RecordSet.
Require ABI Core Decommitter GPR Ergs Event Memory History Instruction CallStack .

Import Core Flags ZArith ABI Common GPR Ergs Event CallStack History MemoryBase Memory Instruction ZMod List Decommitter.
Import ListNotations RecordSetNotations.

Section Definitions.

Definition CALLSTACK_LIMIT := 1024%nat.

Definition exception_handler := code_address.

(* begin details: helpers *)
Definition era_pages := @era_pages instruction_predicated instruction_invalid.
Definition page := @page era_pages.
Definition decommitter := decommitter instruction_invalid.
Definition memory := @memory era_pages.

Definition query := @query contract_address PrecompileParameters.inner_params.
Definition event := @event contract_address.


(* end details *)

(** # EraVM state

EraVM employs a [%state] that comprises the following components:

1. A revertable part [%state_checkpoint]. It houses the depot state, embodying
   all contracts storages across all shards, as well as two queues for events
   and L1 messages.
   Launching a contract (far call) or a function (near call) defines a
   checkpoint; if a contract or a function reverts or panics, the state rolls back
   to the snapshot (see [%roll_back]).

   Note, that the rollback mechanism may be implemented in any efficient way
   matching this behavior.
 *)
Record state_checkpoint := {
    gs_depot: depot;
    gs_events: @history query;
    gs_l1_msgs: @history event;
  }.

Definition callstack := @callstack state_checkpoint.

(** 2. Global parameters:
- current price of accessing data in storage [%gs_current_ergs_per_pubdata_byte].
- transaction number in the current block [%gs_tx_number_in_block]
- decommitter [%gs_contracts]
 *)
Record global_state :=
  mk_gstate {
    gs_current_ergs_per_pubdata_byte: ergs;
    gs_tx_number_in_block: tx_num;
    gs_contracts: decommitter;
    gs_revertable: state_checkpoint;
    }.

Inductive roll_back checkpoint: global_state -> global_state -> Prop :=
| rb_apply: forall e tx ccs ___,
  roll_back checkpoint (mk_gstate e tx ccs ___) (mk_gstate e tx ccs checkpoint).

(** 3. Transient execution state [%exec_state] contains:
  - flags [%gs_flags]: boolean values representing some characteristics of the computation results. See [%Flags].
  - general purpose registers [%gs_regs]: 15 mutable tagged words (primitive values) [%r1]--[%r15], and a reserved read-only zero valued [%r0].
  - all memory pages allocated by VM, including code pages, data stack pages, data pages for heap variants etc. See [%memory].
  - call stack, where each currently running contract and function has a stack frame. Note, that program counter, data stack pointer, and current balance are parts of the current stack frame. See [%CallStack].
 *)
Record exec_state :=
  mk_exec_state {
      gs_flags : flags_state;
      gs_regs: regs_state;
      gs_pages: memory;
      gs_callstack: callstack;
    }.

(**
4. In addition to that, a  128-bit register [%gs_context_u128] is used. Its usage is detailed below.
 *)
Record state :=
  mk_state {
      gs_xstate :> exec_state;
      gs_context_u128: u128;
      gs_global :> global_state;
    }.

(** ## Context register

The 128-bit context value occurs in two places in EraVM:

- In the [%gs_context_u128] register, forming a part of the EraVM state [%state].
- In the [%ecf_context_u128_value], forming part of an external call stack frame [%callstack_external].

These values are distinct: the second one is a snapshot of the first one in a moment of a far call.

Here is how context value is typically used:

1. Set the value of [%gs_context_u128] to $C$ by executing the instruction [%OpContextSetContextU128].
2. Launch a contract using one of the far call instructions. This action pushes a new [%callstack_external] frame $F$ onto the [%gs_callstack]. The value of the $F$'s field [%ecf_context_u128_value] is equal to $C$. Ina ddition, far calls reset [%gs_context_u128] to 0.
3. Retrieve the context value by executing the instruction [%OpContextGetContextU128].
4. On contract code completion, the [%gs_context_u128] is reset to zero by either [%OpFarRet], [%OpFarRevert], or [%OpPanic].

Note that setting the context register [%gs_context_u128] is forbidden in [%StaticMode]. See [%forbidden_static].
 *)

(* begin hide *)

#[export] Instance etaXGS : Settable _ := settable! mk_gstate <gs_current_ergs_per_pubdata_byte; gs_tx_number_in_block; gs_contracts; gs_revertable>.
#[export] Instance etaXS : Settable _ := settable! mk_exec_state <gs_flags ; gs_regs; gs_pages; gs_callstack>.
#[export] Instance etaXGGS : Settable _ := settable! mk_state <gs_xstate; gs_context_u128; gs_global> .

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

Definition page_has_id mem := page_has_id mem (config := era_pages).

Definition heap_variant_page (page_type: data_page_type) (cs:callstack) (mem:memory) :=
    match page_type with
    | Heap => active_heappage
    | AuxHeap =>  active_auxheappage
    end _ (page_has_id mem) cs .

Definition heap_variant_id (page_type: data_page_type)
  :  callstack -> page_id :=
  match page_type with
  | Heap => @active_heap_id
  | AuxHeap => @active_auxheap_id
  end state_checkpoint.

Definition heap_variant_bound (page_type:data_page_type):  callstack -> mem_address :=
  match page_type with
  | Heap => @heap_bound
  | AuxHeap => @auxheap_bound
  end state_checkpoint.
(* end details *)
