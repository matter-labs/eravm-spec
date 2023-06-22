From RecordUpdate Require Import RecordSet.
Require Common Ergs Memory Event Log Instruction CallStack CodeStorage Pages.

Import ZArith Condition Common CodeStorage Ergs Event CallStack Log MemoryBase Memory Instruction Pages ZMod List.
Import ListNotations RecordSetNotations.


Definition page := page instruction_invalid.
Definition memory := memory instruction_invalid.
Definition code_manager := code_manager instruction_invalid.

Definition exception_handler := code_address.

Definition KERNEL_MODE_MAXADDR : contract_address := int_mod_of _ (2^16-1).




Definition update_active_pages (ps:active_pages): callframe -> callframe :=
 change_topmost_extframe (fun ef => ef <| ecf_memory := ps |> ).


Definition addr_is_kernel (addr:contract_address) : bool :=
  lt_unsigned _ addr KERNEL_MODE_MAXADDR.

Definition is_kernel (ef:callframe) : bool :=
  let ef := topmost_extframe ef in
  addr_is_kernel ef.(ecf_this_address).

Definition tx_num := u16.


Record global_state :=
  mk_gstate {
    gs_current_ergs_per_pubdata_byte: ergs;
    gs_tx_number_in_block: tx_num; 
    gs_contracts: code_manager;
    gs_revertable: state_checkpoint;
    }.

Record exec_state :=
  mk_exec_state {
      gs_flags : flags_state;
      gs_regs: regs_state;
      gs_pages:memory;
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

Inductive global_state_increment_tx : global_state -> global_state -> Prop :=
| gsit_apply: forall current_ergs_per_pubdata_byte tx new_tx codes rev ,
  (new_tx, false) = uinc_overflow _ tx ->
  global_state_increment_tx
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
