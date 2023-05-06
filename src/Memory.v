Require Common MemoryBase.
Import Common MemoryBase BinInt.

(** * Storage *)
(**  §1. A _word_ is a 256-bit unsigned number. *)
Definition word_bits: nat := 256.
Definition word_type : Set := ZMod.int_mod word_bits.
Definition word_zero_value: word_type := ZMod.int_mod_of word_bits 0%Z.

(** §2. A _storage_ is a linear mapping from $2^256$ #2<sup>256</sup>#
    addresses to words.

    §2.1. Therefore, each word is addressed through a  256-bit address.

    §2.1.1. Individual bytes in a word can not be addressed directly.

    §2.1.2. Both word address in storage and word capacity are 256 bits; it is a
    meaningless coincidence.

    §2.2. All words in a storage are zero-initialized on genesis.

    §2.2.1 Therefore, if there was no writes to a location in storage, reading
    from it results in a zero value.

 *)

Definition storage_params := {|
                              addressable_block := word_type;
                              address_bits := 256;
                              default_value := zero256;
                              writable := true
                            |}.

Definition storage_type : Type := mem_parameterized storage_params.

(**  §2.3. Most storages start blanks. *)
Definition storage_empty : storage_type := empty storage_params.

(** §2.4. Storage has a sequentially-consistent, strong mem model. All writes *)
(** are atomic and immediately visible; reads are guaranteed to return the last *)
(** value written.  *)

(** * Contract *)

(** §1. A _contract_ is uniquely identified by its address. *)

(** §2. Every contract has a storage. *)

Definition contracts_params := {|
                                addressable_block := storage_type;
                                address_bits := 160;
                                default_value := storage_empty;
                                writable := true
                              |}.
Definition contract_address := address contracts_params.
Definition contract_collection_type := mem_parameterized contracts_params.



(** * Mem page *)
Section Memory.

  Variable ins_type: Set.
  Variable invalid_ins: ins_type.
  Section Pages.


    (** 24 bits, byte-addressable *)
    Definition data_page_params := {|
                                    addressable_block := u8;
                                    address_bits := 32;
                                    default_value := zero8;
                                    writable := true
                                  |}.
    Definition mem_address := address data_page_params.
    (* Definition mem_address_zeroval := zero24. *)

    Record data_page := {
        mem_page_content :> mem_parameterized data_page_params;
        mem_page_accessed_bound: mem_address
      }.

    Definition mem_page_id := nat.
    (** TODO change u32 to something useful? *)
    Record fat_pointer := {
        fp_offset: u32; (* TODO what is this?*)
        fp_mem_page: mem_page_id;
        fp_start: mem_address;
        fp_length: mem_address;
      }.

    Inductive primitive_value :=
      FatPointerTag: fat_pointer -> primitive_value
    | IntValue: word_type -> primitive_value.


    Definition stack_page_params := {|
                                     addressable_block := primitive_value;
                                     address_bits := 16;
                                     default_value := IntValue zero256;
                                     writable := true
                                   |}.

    Definition stack_address := address stack_page_params.
    Definition stack_address_zero: stack_address := zero16.

    Definition stack_page := mem_parameterized stack_page_params.


    Definition const_address_bits := 16.

    Definition const_page_params := {|
                                     addressable_block := word_type;
                                     address_bits := const_address_bits;
                                     default_value := zero256;
                                     writable := false
                                   |}.
    Definition const_address :=  address const_page_params.
    Definition const_page := mem_parameterized const_page_params.



    (* should be [address code_page_params] but we don't want to introduce
      dependency between code_address and instruction type *)
    Definition code_address_bits := 16.
    Definition code_address :=  ZMod.int_mod code_address_bits.
    Definition code_page_params := {|
                                    addressable_block := ins_type;
                                    address_bits := code_address_bits;
                                    default_value := invalid_ins;
                                    writable := false
                                  |}.


    Definition code_page := mem_parameterized code_page_params.

    Record ctx_mem_pages:=
      {
        ctx_code_page_id:  mem_page_id;
        ctx_const_page_id:  mem_page_id;
        ctx_stack_page_id:  mem_page_id;
        ctx_heap_page_id:  mem_page_id;
        ctx_heap_aux_page_id:  mem_page_id;
        ctx_heap_bound: u32;  (* FIXME type, provenanc, value *)
        ctx_aux_heap_bound: u32;  (* FIXME type, provenance, value*)
      }.

    Inductive mem_page :=
    (** Heap or auxheap *)
    | DataPage : data_page -> mem_page
    | StackPage : stack_page -> mem_page
    | ConstPage : const_page -> mem_page
    | CodePage : code_page -> mem_page.

    Definition mem_pages := list (prod nat mem_page).

    Inductive page_alloc (p:mem_page) : mem_pages -> mem_pages -> Prop :=
    | PageAlloc :
      forall m, page_alloc p m (cons (length m, p) m).

  End Pages.

  (** * Registers*)
  (** There are 16 registers; [r0_reserved] always holds 0. *)
  Section Regs.
    Import List.ListNotations.

    Section GPR.
      Inductive reg_name : Set :=
        R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13
      | R14 | R15.

      Definition reg_list: list reg_name :=
        [ R0; R1; R2; R3; R4; R5; R6; R7; R8; R9; R10; R11; R12 ; R13; R14; R15 ].

      Inductive reg_n : nat -> reg_name -> Prop :=
      | rn_get: forall n (rn:reg_name),
          List.nth_error reg_list n = Some rn ->
          reg_n n rn.

      Inductive reg_readable: reg_name -> Prop :=
        rr_Any: forall reg, reg_readable reg.

      Inductive reg_writable: reg_name -> Prop :=
        RegWritableNotR0: forall reg, reg <> R0 -> reg_writable reg.


    End GPR.

    Record regs_state :=  mk_regs {
                              rs_gprs: list primitive_value;
                              rs_sp: stack_address;
                              rs_pc: code_address;
                            }.

    (** Fetching value from general purpose register. *)
    Inductive fetch_gpr : regs_state -> reg_name -> primitive_value -> Prop :=
    | fr_fetch:
      forall rs n regname val,
        reg_n n regname ->
        List.nth_error (rs_gprs rs) n = Some val ->
        fetch_gpr rs regname val.


    (** Fetching value of the stack pointer itself. *)
    Inductive fetch_sp : regs_state -> stack_address -> Prop :=
    | fsp_fetch:
      forall rs (sp_value:stack_address),
        rs_sp rs = sp_value ->
        fetch_sp rs sp_value
    .
    (** Fetching value of the program counter itself. *)
    Inductive fetch_pc : regs_state -> code_address -> Prop :=
    | fpc_fetch:
      forall rs (pc_value: code_address) ,
        rs_pc rs = pc_value ->
        fetch_pc rs pc_value
    .

    Record flags_state := mk_fs {
                              OF_LT: bool;
                              EQ: bool;
                              GT: bool;
                            }.
    Definition flags_clear : flags_state := mk_fs false false false.


  End Regs.

  Section Helpers.
  Import ZMod.

  Inductive extract_address bits: word_type -> int_mod bits -> Prop :=
  |ea_extract: forall val,
      extract_address bits val (ZMod.resize word_bits bits val).

  Definition extract_code_address: word_type -> code_address -> Prop := extract_address _.
  Definition extract_const_address: word_type -> const_address -> Prop := extract_address _.
  Definition extract_stack_address: word_type -> stack_address -> Prop
    := extract_address _.
  End Helpers.
End Memory.
