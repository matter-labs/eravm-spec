From RecordUpdate Require Import RecordSet.
Require Common MemoryBase lib.PMap_ext.
Import Common MemoryBase BinInt List PMap_ext.
Import ListNotations.
Import RecordSetNotations.

(** * Storage *)
(**  §1. A _word_ is a 256-bit unsigned number. *)
Definition word_bits: nat := 256.
Definition word: Set := ZMod.int_mod word_bits.
Definition word_zero_value: word := ZMod.int_mod_of word_bits 0%Z.

Section Helpers.
  Import Nat.
  Definition bytes_in_word : nat := word_bits/bits_in_byte.
  Definition z_bytes_in_word : Z := Z.of_nat bytes_in_word.

End Helpers.

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
                              addressable_block := word;
                              address_bits := 256;
                              default_value := zero256;
                              writable := true
                            |}.
Definition storage_address := ZMod.int_mod (address_bits storage_params).
Definition storage_type : Type := mem_parameterized storage_params.

(**  §2.3. Most storages start blanks. *)
Definition storage_empty : storage_type := empty storage_params.

(** §2.4. Storage has a sequentially-consistent, strong mem model. All writes *)
(** are atomic and immediately visible; reads are guaranteed to return the last *)
(** value written.  *)

(** * Contract *)

(** §1. A _contract_ is uniquely identified by its address. *)

(** §2. Every contract has a storage. *)


Definition shard_params := {|
                            addressable_block := storage_type;
                            address_bits := 160;
                            default_value := storage_empty;
                            writable := true
                          |}.
Definition contract_address := address shard_params.
Definition contract_address_bits := address_bits shard_params.
Definition shard := mem_parameterized shard_params.

Definition depot_params :=
  {|
    addressable_block := shard;
    address_bits := 8;
    default_value := empty _;
    writable := true
  |}.

Definition shard_id := ZMod.int_mod (address_bits depot_params).

Inductive shard_exists: shard_id -> Prop :=
| se_rollup: shard_exists (ZMod.int_mod_of _ 0%Z)
| se_porter: shard_exists (ZMod.int_mod_of _ 1%Z)
.

Definition depot := mem_parameterized depot_params.

(** * Mem page *)
Section Memory.

  Context {ins_type: Type} (invalid_ins: ins_type).


  (** 24 bits, byte-addressable *)
  Definition data_page_params := {|
                                  addressable_block := u8;
                                  address_bits := 32;
                                  default_value := zero8;
                                  writable := true
                                |}.
  Definition mem_address := address data_page_params.
  (* Definition mem_address_zeroval := zero24. *)

  Definition data_page := mem_parameterized data_page_params.


  Inductive primitive_value := mk_pv
                                 {
                                   is_ptr: bool;
                                   value: word;
                                 }.

  Definition pv0 := mk_pv false word_zero_value.

  Definition clear_pointer_tag (pv:primitive_value): primitive_value :=
    match pv with | mk_pv _ value => mk_pv false value end.

  Definition stack_page_params := {|
                                   addressable_block := primitive_value;
                                   address_bits := 16;
                                   default_value := mk_pv false zero256;
                                   writable := true
                                 |}.

  Definition stack_address := address stack_page_params.
  Definition stack_address_zero: stack_address := zero16.

  Definition stack_page := mem_parameterized stack_page_params.


  Definition const_address_bits := 16.

  Definition const_page_params := {|
                                   addressable_block := word;
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


  Definition code_length := code_address.


  Definition data_page_slice_params := data_page_params <| writable := false |>.
  Definition data_slice := mem_parameterized data_page_slice_params.
  
  Definition slice  (from_incl to_excl: mem_address) (m:data_page) : data_slice:=
    let from_key := MemoryBase.addr_to_key _ from_incl in
    let to_key := MemoryBase.addr_to_key _ to_excl in
    let contents := pmap_slice m from_key to_key in
    mk_mem data_page_slice_params contents.
  
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

    Definition regs_state_zero := let z := mk_pv false zero256
                                  in mk_regs z z z z z z z z z z z z z z z.

    (* begin hide *)
    #[export] Instance etaGPRs : Settable _ := settable! mk_regs < gprs_r1  ; gprs_r2  ; gprs_r3  ; gprs_r4  ; gprs_r5  ; gprs_r6  ; gprs_r7  ; gprs_r8  ; gprs_r9  ; gprs_r10  ; gprs_r11  ; gprs_r12  ; gprs_r13  ; gprs_r14  ; gprs_r15  >.
    (* end hide *)

    Definition reg_map f (rs:regs_state) : regs_state :=
      match rs with
      | mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 =>
          ( mk_regs (f r1) (f r2) (f r3) (f r4) (f r5) (f r6) (f r7) (f r8) (f r9) (f r10) (f r11) (f r12) (f r13) (f r14) (f r15))
      end.

  End Regs.

  Section Helpers.
    Import ZMod.

    Inductive extract_address bits: word -> int_mod bits -> Prop :=
    |ea_extract: forall val,
        extract_address bits val (ZMod.resize word_bits bits val).

    Definition extract_code_address: word -> code_address -> Prop := extract_address _.
    Definition extract_const_address: word -> const_address -> Prop := extract_address _.
    Definition extract_stack_address: word -> stack_address -> Prop
      := extract_address _.
  End Helpers.
End Memory.

Notation IntValue := (mk_pv false).
Notation PtrValue := (mk_pv true).
