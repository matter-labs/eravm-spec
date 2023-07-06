Require Addressing Core Common Condition CallStack Memory List Pointer Resolution Slice.

Import Addressing Core ZArith ZMod Common Condition CallStack GPR MemoryBase Memory PrimitiveValue Pointer Resolution Slice.

Section Definitions.

  Import Addressing.Coercions.

  Context {instruction: Type} (instruction_invalid:instruction)
    {state_checkpoint: Type}
    (code_page := code_page instruction_invalid)
    (primitive_value := @primitive_value word)
    (era_pages := @era_pages _ instruction_invalid)
    (StackPage := @StackPage era_pages)
    (CodePage := @CodePage era_pages)
    (ConstPage := @ConstPage era_pages)
    (callstack:= @callstack state_checkpoint)
    (pconf := Build_pages_config code_page const_page data_page stack_page)
    (memory := @memory pconf)
  .

  Section FetchStore.
    Context
        (regs: regs_state)
        (cs: callstack)
        (mem: memory)
        (page_has_id := page_has_id mem)
    .

    Inductive fetch_result : Type :=
    | FetchIns (ins: instruction )
    | FetchPV (pv: primitive_value) .

    Inductive fetch: loc -> fetch_result -> Prop :=
    | fetch_reg: forall name reg_val,
        reg_val = fetch_gpr regs name ->
        fetch (LocReg name) (FetchPV reg_val)
    | fetch_imm: forall imm imm',
        imm' = resize _ word_bits imm ->
        fetch (LocImm imm) (FetchPV (IntValue imm'))
    | fetch_stackaddr:
      forall stackpage (value: primitive_value) addr,
        @active_stackpage _ _ instruction_invalid page_has_id cs stackpage ->
        MemoryBase.load_result _ addr stackpage value ->
        fetch (LocStackAddress addr) (FetchPV value)
    | fetch_codeaddr:
      forall codepage addr ins,
        active_codepage _ page_has_id cs codepage ->
        load_result _ addr codepage ins ->
        fetch (LocCodeAddr addr) (FetchIns ins)
    | fetch_constaddr:
      forall constpage addr value,
        active_constpage _ page_has_id cs constpage ->
        load_result _ addr constpage value ->
        fetch (LocConstAddr addr) (FetchPV (IntValue value))
    .

    Definition next_ins := LocCodeAddr (pc_get cs).

    Definition fetch_instr := fetch next_ins.


    Inductive store_loc: primitive_value -> loc -> (regs_state * memory) -> Prop :=
    | store_lreg:
      forall new_regs reg_name value mem,
        store_gpr regs reg_name value new_regs ->
        store_loc value (LocReg reg_name) (new_regs, mem)
    | store_lstackaddr:
      forall new_mem stackpage addr value pid new_stackpage,
        active_stackpage _ page_has_id cs stackpage ->
        store_result _ addr stackpage value new_stackpage ->
        page_replace pid (StackPage new_stackpage) mem new_mem ->
        store_loc value (LocStackAddress addr) (regs, new_mem)
    .

    Inductive load: in_any -> callstack * primitive_value -> Prop :=
    | ld_apply : forall (arg:in_any) loc res new_cs,
        resolve_apply regs cs arg (new_cs, loc) ->
        fetch loc (FetchPV res) ->
        load arg (new_cs, res).

    Inductive load_any: in_any -> callstack * word -> Prop :=
    | lda_apply : forall (arg:in_any) loc res new_cs __,
        resolve_apply regs cs arg (new_cs, loc) ->
        fetch loc (FetchPV (mk_pv __ res)) ->
        load_any arg (new_cs, res).

    Inductive load_reg: in_reg -> primitive_value -> Prop :=
    | ldr_apply : forall  loc res,
        fetch_gpr regs loc = res ->
        load_reg (Reg loc) res.

    Inductive load_reg_any: in_reg -> word -> Prop :=
    | ldra_apply : forall  loc res __,
        fetch_gpr regs loc = (mk_pv __ res) ->
        load_reg_any (Reg loc) res.

    Definition load_int a cs w := load a (cs, IntValue w).
    Definition load_reg_int a w := load_reg a (IntValue w).

    Inductive store: out_any -> primitive_value -> regs_state * memory * callstack -> Prop :=
    | st_apply: forall (arg:out_any) loc new_regs new_mem new_cs pv,
        resolve_apply regs cs arg (new_cs, loc) ->
        store_loc pv loc (new_regs, new_mem)->
        store arg pv (new_regs, new_mem, new_cs).

    Inductive store_reg: out_reg -> primitive_value -> regs_state -> Prop :=
    | sr_apply: forall (arg:out_reg) loc new_regs  pv,
        store_gpr regs loc pv new_regs ->
        store_reg arg pv new_regs.

    Definition store_int a w rs m cs := store a (IntValue w) (rs, m, cs).

  End FetchStore.


  Inductive loads (regs:regs_state) (cs:callstack) (mem:memory) : list (in_any * primitive_value) -> callstack -> Prop :=
  | rsl_nil:
    loads regs cs mem nil cs

  | rsl_cons: forall (arg:in_any) pv (tail: list (in_any * primitive_value)) cs1 cs2,
      load regs cs mem arg (cs1, pv) ->
      loads regs cs1 mem tail cs2 ->
      loads regs cs mem ((arg,pv)::tail) cs2.

  Inductive load_regs (regs:regs_state) : list (in_reg * primitive_value) -> Prop :=
  | rslr_nil:
    load_regs regs  nil

  | rslr_cons: forall (arg:in_reg) pv (tail: list (in_reg * primitive_value)),
      load_reg regs arg pv ->
      load_regs regs tail ->
      load_regs regs ((arg,pv)::tail).

  Inductive stores (regs:regs_state) (cs:callstack) (mem:memory) : list (out_any * primitive_value) -> (regs_state * memory * callstack) -> Prop :=
  | rss_nil:
    stores regs cs mem nil (regs, mem, cs)
  | rss_cons: forall (arg:out_any) pv (tail: list (out_any * primitive_value)) regs1 mem1 cs1 regs2 mem2 cs2,
      store regs cs mem arg pv (regs1, mem1, cs1) ->
      stores regs1 cs1 mem1 tail (regs2, mem2, cs2) ->
      stores regs cs mem ((arg,pv)::tail) (regs2, mem2, cs2).

  Inductive store_regs (regs:regs_state) : list (out_reg * primitive_value) -> regs_state -> Prop :=
  | rssr_nil:
    store_regs regs nil regs
  | rssr_cons: forall (arg:out_reg) pv (tail: list (out_reg * primitive_value)) regs1 regs2 ,
      store_reg regs arg pv regs1 ->
      store_regs regs1 tail regs2 ->
      store_regs regs ((arg,pv)::tail) regs2.

End Definitions.


Section Multibyte.
  Inductive endianness := LittleEndian | BigEndian.

  Context (e:endianness) (mem:data_page).

  Definition mb_load_word (addr:mem_address) :option word :=
    match load_multicell data_page_params addr bytes_in_word mem with
    | None => None
    | Some val =>
        let fend : list u8 -> list u8 := match e with
                                        | LittleEndian => @List.rev u8
                                        | BigEndian => id
                                        end in
        Some (merge_bytes bits_in_byte word_bits (fend val))
    end
  .

  Inductive mb_load_result : mem_address -> word -> Prop :=
  | mldr_apply: forall (addr:mem_address) res,
      mb_load_word addr = Some res ->
      mb_load_result addr res.


  Definition mb_store_word (addr:mem_address) (val: word) : option data_page :=
    let ls := match e with
              | LittleEndian => word_to_bytes val
              | BigEndian => List.rev (word_to_bytes val)
              end in
    store_multicell _ addr ls mem.

  Inductive mb_store_word_result: mem_address -> word -> data_page -> Prop :=
  | sdr_apply :
    forall addr val page',
      mb_store_word addr val = Some page' ->
      mb_store_word_result addr val page'.

  Definition mb_load_slice_word (slc:data_slice) (addr:mem_address) :option word :=
    match load_multicell data_page_slice_params addr bytes_in_word slc with
    | None => None
    | Some val =>
        let fend : list u8 -> list u8 := match e with
                                        | LittleEndian => @List.rev u8
                                        | BigEndian => id
                                        end in
        Some (merge_bytes bits_in_byte word_bits (fend val))
    end.

  Inductive mb_load_slice_result (slc:data_slice): mem_address -> word -> Prop :=
  | mlsr_apply: forall (addr:mem_address) res,
      mb_load_slice_word slc addr = Some res ->
      mb_load_slice_result slc addr res.

End Multibyte.
