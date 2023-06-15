From RecordUpdate Require Import RecordSet.
Require Ergs Memory Pages.

Import Bool ZMod Common Ergs Memory RecordSetNotations Pages ZMod.

Open Scope ZMod_scope.
(** ABIs are described here:
https://github.com/matter-labs/zkevm_opcode_defs/blob/v1.3.2/src/definitions/abi/far_call.rs
 *)

Record coder {ABIParams:Type} := {
    decode: u256 -> option ABIParams ;
    encode:  ABIParams -> u256 ;
    revertible1: forall params, decode (encode params) = Some params;
    revertible2: forall params encoded, decode encoded = Some params -> encode params = encoded;
  }.

(** * Fat Pointers *)
Module FatPointer.
  Record fat_ptr :=
    mk_fat_ptr {
        fp_page: page_id;
        fp_start: mem_address;
        fp_length: mem_address;
        fp_offset: mem_address;
      }.

  #[export] Instance etaFatPointer: Settable _
    := settable! mk_fat_ptr < fp_page; fp_start; fp_length; fp_offset>.

  Axiom ABI : @coder fat_ptr.

  Record validation_exception :=
    mk_ptr_validation_exception
      {
        ptr_expected_zero_offset : bool;
        ptr_deref_beyond_heap_range : bool;
        ptr_bad_slice: bool;
      }.

  Definition no_exceptions : validation_exception
    := mk_ptr_validation_exception false false false.

  Definition fat_ptr_empty :=
    {|
      fp_page := 0;
      fp_start := zero32;
      fp_length:= zero32;
      fp_offset:= zero32;
    |}.

  Definition is_overflowing {bits:nat} (res: int_mod bits* bool) := snd res.

  Definition validate (p:fat_ptr) (fresh:bool) : validation_exception :=
    {|
      ptr_expected_zero_offset    := fresh && negb (p.(fp_offset) == zero32);
      ptr_deref_beyond_heap_range := is_overflowing (p.(fp_start) + p.(fp_length));
      ptr_bad_slice := gt_unsigned _ p.(fp_offset) p.(fp_length);
    |}.

  Definition validate_fresh p := validate p true.
  Definition validate_non_fresh p := validate p false.

  Definition validate_in_bounds (p:fat_ptr) : bool := (lt_unsigned _ p.(fp_offset) p.(fp_length) ).

  Definition is_trivial (p:fat_ptr) := (p.(fp_length) == zero32) && (p.(fp_offset)
                                       == zero32).

  Inductive fat_ptr_shrink : fat_ptr -> fat_ptr -> Prop :=
  | fps_shrink : forall p start start' length length' ofs,
    validate (mk_fat_ptr p start length ofs) false = no_exceptions ->
    start + ofs = (start', false) ->
    length - ofs = (length', false) ->
    fat_ptr_shrink (mk_fat_ptr p start length ofs) (mk_fat_ptr p start' length' zero32).

  (** Used by [OpPtrShrink] instruction. *)
  Inductive fat_ptr_trim_length : fat_ptr -> u32 -> fat_ptr -> Prop :=
  | fptl_apply: forall p start diff length length' ofs,
    length - diff = (length', false) ->
    fat_ptr_trim_length (mk_fat_ptr p start length ofs) diff (mk_fat_ptr p start length' ofs).

  Definition growth (current_bound: mem_address) (query_bound: mem_address)
    : mem_address :=
    if le_unsigned _ query_bound current_bound then zero32 else
      fst (usub_overflow _ query_bound current_bound).

  Inductive fat_ptr_induced_growth: fat_ptr -> forall current_bound: mem_address, mem_address -> Prop :=
  | gb_bytes: forall fp_page fp_start fp_length fp_offset query_bound current_bound,
      fp_start + fp_length = (query_bound, false) ->
      let diff := growth current_bound query_bound in
      fat_ptr_induced_growth (mk_fat_ptr fp_page fp_start fp_length fp_offset) current_bound diff.

  Inductive ptr_inc : fat_ptr -> fat_ptr -> Prop :=
  |fpi_apply :
    forall page start len ofs ofs',
      ofs + (u32_of z_bytes_in_word) = (ofs', false) ->
      ptr_inc (mk_fat_ptr page start len ofs) (mk_fat_ptr page start len ofs').
  
  Inductive slice_from_ptr (m:data_page) : fat_ptr -> data_slice -> Prop :=
  | sfp_apply:
    forall page start length ofs upper_bound readonly_slice,
      start + length = (upper_bound, false) ->
      slice start upper_bound  m = readonly_slice ->
      slice_from_ptr m (mk_fat_ptr  page start length ofs) readonly_slice.
  
End FatPointer.


(** * Ret *)
Module Ret.
  Import FatPointer.
  (*Inductive forward_page_type := UseHeap | ForwardFatPointer | UseAuxHeap.*)
  Inductive forward_page_type := ForwardFatPointer | UseMemory (type: data_page_type).

  Record params := mk_params {
      memory_quasi_fat_ptr: fat_ptr;
      page_forwarding_mode: forward_page_type;
    }.

  Axiom ABI: @coder params.
  Axiom ABI_decode_zero: ABI.(decode) zero256 = Some (mk_params fat_ptr_empty (UseMemory Heap) ).
End Ret.

(** * Near call *)
Module NearCall.

  Record params: Type := mk_params {
      ergs_passed: u32;
    }.

  Axiom ABI: @coder params.

End NearCall.

(** * Far call *)
Module FarCall.
  Import FatPointer Ret.
  Record params := mk_params {
      memory_quasi_fat_ptr: fat_ptr;
      ergs_passed: ergs;
      shard_id: shard_id;
      forwarding_mode: forward_page_type;
      constructor_call: bool;
      to_system: bool;
    }.


  Axiom ABI: @coder params.

End FarCall.


Module MetaParameters.

  Record params :=
    mk_params {
        ergs_per_pubdata_byte: ergs;
        heap_size: mem_address;
        aux_heap_size: mem_address;
        this_shard_id: shard_id;
        caller_shard_id: shard_id;
        code_shard_id: shard_id;
      }.

  Axiom ABI: @coder params.

End MetaParameters.
