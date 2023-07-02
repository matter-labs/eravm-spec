From RecordUpdate Require Import RecordSet.
Require ABI Core Decommitter GPR Ergs Event Memory Log Instruction CallStack .

Import Core Condition ZArith ABI Common GPR Ergs Event CallStack Log MemoryBase Memory Instruction ZMod List Decommitter.
Import ListNotations RecordSetNotations.

Section Definitions.

  Definition era_pages := @era_pages instruction_predicated instruction_invalid.
  Definition page := @page era_pages.
(* Definition memory := memory instruction_invalid. *)
(* Definition code_manager := code_manager instruction_invalid. *)

Context (KERNEL_MODE_MAXADDR: contract_address).
Definition CALLSTACK_LIMIT := 1024%nat.

Definition exception_handler := code_address.



(* Definition update_active_pages (ps:mem_ctx): callframe -> callframe := *)
(*  change_topmost_extframe (fun ef => ef <| ecf_memory := ps |> ). *)
Definition decommitter := decommitter instruction_invalid.
Definition memory := @memory era_pages.

Definition query := @query contract_address PrecompileParameters.inner_params.
Definition event := @event contract_address.

Record state_checkpoint := {
    gs_depot: depot;
    gs_events: log query;
    gs_l1_msgs: log event;
  }.

Definition callstack := @callstack state_checkpoint.

Record global_state :=
  mk_gstate {
    gs_current_ergs_per_pubdata_byte: ergs;
    gs_tx_number_in_block: tx_num; 
    gs_contracts: decommitter;
    gs_revertable: state_checkpoint;
    }.

Record exec_state :=
  mk_exec_state {
      gs_flags : flags_state;
      gs_regs: regs_state;
      gs_pages: memory;
      gs_callstack: callstack;
    }.

Record state :=
  mk_state {
      gs_xstate :> exec_state;
      gs_context_u128: u128;
      gs_global :> global_state;
    }.
#[export] Instance etaXGS : Settable _ := settable! mk_gstate <gs_current_ergs_per_pubdata_byte; gs_tx_number_in_block; gs_contracts; gs_revertable>.
#[export] Instance etaXS : Settable _ := settable! mk_exec_state <gs_flags ; gs_regs; gs_pages; gs_callstack>.
#[export] Instance etaXGGS : Settable _ := settable! mk_state <gs_xstate; gs_context_u128; gs_global> .


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
