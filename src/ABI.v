Require Memory.

Import Bool ZMod Common Memory.

(** ABIs are described here:
https://github.com/matter-labs/zkevm_opcode_defs/blob/v1.3.2/src/definitions/abi/far_call.rs
 *)

Record coder (ABIParams:Type) := {
    decode: u256 -> ABIParams ;
    encode:  ABIParams -> u256 ;
    revertible1: forall params, decode (encode params) = params;
    revertible2: forall params encoded, decode encoded = params -> encode params = encoded;
  }.

(** * Fat Pointers *)
Module FatPointer.
  Axiom ABI : coder fat_ptr.

  Record validation_exception :=
    mk_ptr_validation_exception
      {
        ptr_expected_zero_offset : bool;
        ptr_deref_beyond_heap_range : bool;
      }.

  Definition fat_ptr_empty :=
    {|
      fp_mem_page := 0;
      fp_start := zero32;
      fp_length:= zero32;
      fp_offset:= zero32;
    |}.

  Definition is_overflowing {bits:nat} (res: int_mod bits* bool) := snd res.

  Definition validate (p:fat_ptr) (fresh:bool) : validation_exception :=
    {|
      ptr_expected_zero_offset    := fresh && (p.(fp_offset) == zero32);
      ptr_deref_beyond_heap_range := is_overflowing (p.(fp_start) + p.(fp_length))
    |}.

  (* FIXME the comment in Rust code mentions that the empty slice should be
  accepted. Maybe we should rewrite it as: "length == 0 OR ofs < length" rather
  than "offset <= length"? *)
  Definition validate_as_slice (p:fat_ptr) : bool
    := (le_unsigned _ p.(fp_offset) p.(fp_length) ).

  Definition validate_in_bounds (p:fat_ptr) : bool := (lt_unsigned _ p.(fp_offset) p.(fp_length) ).

  Definition is_trivial (p:fat_ptr) := (p.(fp_length) == zero32) && (p.(fp_offset)
                                       == zero32).

End FatPointer.


(** * Ret *)
Module Ret.
  Inductive forward_page_type := UseHeap | ForwardFatPointer | UseAuxHeap.
  Record params := {
      memory_quasi_fat_ptr: fat_ptr;
      page_forwarding_mode: forward_page_type;
    }.

  Axiom ABI: coder params.
End Ret.

(** * Near call *)
Module NearCall.

  Record params: Type := {
      nca_get_ergs_passed: u32;
    }.

  Axiom ABI: coder params.

End NearCall.

(** * Far call *)
Inductive far_call_forward_page_type := UseHeap | ForwardFatPointer | UseAuxHeap.

Record far_call := {
    fc_memory_quasi_fat_ptr: fat_ptr;
    fc_ergs_passed: u32;
    fc_shard_id: u8;
    fc_forwarding_mode: far_call_forward_page_type;
    fc_constructor_call: bool;
    fc_consider_new_tx: bool;
  }.


Axiom ABI_far_call: coder far_call.
