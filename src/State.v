From RecordUpdate Require Import RecordSet.
Require Common Condition Ergs Memory Instruction CodeStorage CallStack.

Import ZArith Condition Common Ergs CallStack MemoryBase Memory CodeStorage Instruction ZMod List.
Import ListNotations RecordSetNotations.

Definition page := page instruction_predicated instruction_invalid.
Definition code_manager := code_manager instruction_predicated instruction_invalid.

Definition exception_handler := code_address.

Definition KERNEL_MODE_MAXADDR : contract_address := int_mod_of _ (2^16-1).


Section AllocatedPages.
  Import Bool Nat.

  Definition pages : Type := list (page_id * page).

  Inductive page_replace:  page_id -> page -> pages -> pages -> Prop :=
  | mm_replace_base: forall oldpage id newpage tail,
      page_replace id newpage ((id, oldpage)::tail) ((id,newpage)::tail)
  | mm_replace_ind: forall oldpage id not_id newpage tail tail',
      page_replace id newpage tail tail' ->
      id <> not_id ->
      page_replace id newpage ((not_id,oldpage)::tail) ((not_id,oldpage)::tail').

  Inductive page_has_id : pages -> page_id -> page -> Prop :=
  | mpid_select : forall mm id page,
      List.In (id, page) mm ->
      page_has_id mm id page.

  Definition is_active_page (ef:callframe) (id: page_id) : bool :=
    eqb (active_code_id ef) id ||
      eqb (active_stack_id ef) id ||
      eqb (active_const_id ef) id ||
      eqb (active_heap_id ef) id ||
      eqb (active_auxheap_id ef) id .

    Inductive active_codepage : pages -> callframe -> page -> Prop :=
    | ap_active_code: forall mm ef codepage,
        page_has_id mm (active_code_id ef) codepage ->
        active_codepage mm ef codepage.

    Inductive active_constpage : pages -> callframe -> page -> Prop :=
    | ap_active_const: forall mm ef constpage,
        page_has_id mm (active_const_id ef) constpage ->
        active_constpage mm ef constpage.

    Inductive active_stackpage : pages -> callframe -> page -> Prop :=
    | ap_active_stack: forall mm ef stackpage,
        page_has_id mm (active_stack_id ef) stackpage ->
        active_stackpage mm ef stackpage.

    Inductive active_heappage : pages -> callframe -> page -> Prop :=
    | ap_active_heap: forall mm ef heappage,
        page_has_id mm (active_heap_id ef) heappage ->
        active_heappage mm ef heappage.

    Inductive active_auxheappage : pages -> callframe -> page -> Prop :=
    | ap_active_auxheap: forall mm ef auxheappage,
        page_has_id mm (active_auxheap_id ef) auxheappage ->
        active_auxheappage mm ef auxheappage.

  Definition heap_variant_page (page_type: data_page_type)
    : pages -> callframe -> page -> Prop :=
    match page_type with
    | Heap => active_heappage
    | AuxHeap => active_auxheappage
    end.

End AllocatedPages.


Definition update_active_pages (ps:active_pages): callframe -> callframe :=
 change_topmost_extframe (fun ef => ef <| ecf_pages := ps |> ).


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
    gs_depot: depot;
    }.

Record state :=
  mk_state {
      gs_flags : flags_state;
      gs_regs: regs_state;
      gs_pages: pages;
      gs_callstack: callstack;
      gs_context_u128: u128;
      gs_global :> global_state;
    }.
#[export] Instance etaXGS : Settable _ := settable! mk_gstate <gs_current_ergs_per_pubdata_byte; gs_tx_number_in_block; gs_contracts; gs_depot>.
#[export] Instance etaXS : Settable _ := settable! mk_state <gs_flags ; gs_regs; gs_pages; gs_callstack; gs_context_u128; gs_global> .

Inductive global_state_increment_tx : global_state -> global_state -> Prop :=
| gsit_apply: forall current_ergs_per_pubdata_byte tx new_tx codes depot,
  (new_tx, false) = uinc_overflow _ tx ->
  global_state_increment_tx
  {|
    gs_current_ergs_per_pubdata_byte := current_ergs_per_pubdata_byte;
    gs_tx_number_in_block := tx;
    gs_contracts := codes;
    gs_depot := depot;
  |}
  {|
    gs_current_ergs_per_pubdata_byte := current_ergs_per_pubdata_byte;
    gs_tx_number_in_block := new_tx;
    gs_contracts := codes;
    gs_depot := depot;
  |}.
