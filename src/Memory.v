From RecordUpdate Require Import RecordSet.
Require Common MemoryBase.
Import Common MemoryBase BinInt List.
Import ListNotations.
Import RecordSetNotations.

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


    Inductive primitive_value :=
      PtrValue: word_type -> primitive_value
    | IntValue: word_type -> primitive_value.

    Definition pv0 := IntValue word_zero_value.

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

    Definition page_alloc (p:mem_page) (m: mem_pages) : mem_pages :=
             cons (length m, p) m.

    Import Nat.
    Definition page_older (id: mem_page_id) (mps: ctx_mem_pages) : bool :=
      match mps with
      | Build_ctx_mem_pages ctx_code_page_id ctx_const_page_id ctx_stack_page_id
          ctx_heap_page_id ctx_heap_aux_page_id ctx_heap_bound
          ctx_aux_heap_bound =>
          ltb id ctx_code_page_id &&
            ltb id ctx_const_page_id &&
            ltb id ctx_stack_page_id &&
            ltb id ctx_heap_page_id &&
            ltb id ctx_heap_aux_page_id
      end.
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

      Definition reg_idx (r:reg_name) : nat :=
        match r with
        | R0 => 0
        | R1 => 1
        | R2 => 2
        | R3 => 3
        | R4 => 4
        | R5 => 5
        | R6 => 6
        | R7 => 7
        | R8 => 8
        | R9 => 9
        | R10 => 10
        | R11 => 11
        | R12 => 12
        | R13 => 13
        | R14 => 14
        | R15 => 15
        end.

      Inductive reg_readable: reg_name -> Prop :=
        rr_Any: forall reg, reg_readable reg.

      Inductive reg_writable: reg_name -> Prop :=
        RegWritableNotR0: forall reg, reg <> R0 -> reg_writable reg.


    End GPR.

    Record regs_state :=  mk_regs {
                              gprs_r1  : primitive_value;
                              gprs_r2  : primitive_value;
                              gprs_r3  : primitive_value;
                              gprs_r4  : primitive_value;
                              gprs_r5  : primitive_value;
                              gprs_r6  : primitive_value;
                              gprs_r7  : primitive_value;
                              gprs_r8  : primitive_value;
                              gprs_r9  : primitive_value;
                              gprs_r10  : primitive_value;
                              gprs_r11  : primitive_value;
                              gprs_r12  : primitive_value;
                              gprs_r13  : primitive_value;
                              gprs_r14  : primitive_value;
                              gprs_r15  : primitive_value;
                            }.

    Definition regs_state_zero := let z := IntValue zero256
                                  in mk_regs z z z z z z z z z z z z z z z.

    (* begin hide *)
    #[export] Instance etaGPRs : Settable _ := settable! mk_regs < gprs_r1  ; gprs_r2  ; gprs_r3  ; gprs_r4  ; gprs_r5  ; gprs_r6  ; gprs_r7  ; gprs_r8  ; gprs_r9  ; gprs_r10  ; gprs_r11  ; gprs_r12  ; gprs_r13  ; gprs_r14  ; gprs_r15  >.
    (* end hide *)

    Inductive OF_LT := Set_OF_LT | Clear_OF_LT.
    Inductive EQ := Set_EQ | Clear_EQ.
    Inductive GT := Set_GT | Clear_GT.

    Definition OF_LT_to_bool (f:OF_LT) := if f then true else false.
    Definition EQ_to_bool (f:EQ) := if f then true else false.
    Definition GT_to_bool (f:GT) := if f then true else false.

    #[reversible]
    Coercion OF_LT_to_bool : OF_LT >-> bool.
    #[reversible]
    Coercion EQ_to_bool : EQ >-> bool.
    #[reversible]
    Coercion GT_to_bool : GT >-> bool.

    Definition EQ_of_bool (f:bool) := if f then Set_EQ else Clear_EQ.
    Definition OF_LT_of_bool (f:bool) := if f then Set_OF_LT else Clear_OF_LT.
    Definition GT_of_bool (f:bool) := if f then Set_GT else Clear_GT.

    Record flags_state := mk_fs {
                              fs_OF_LT: OF_LT;
                              fs_EQ: EQ;
                              fs_GT: GT;
                            }.
    Definition flags_clear : flags_state := mk_fs Clear_OF_LT Clear_EQ Clear_GT.


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
