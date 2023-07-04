From RecordUpdate Require Import RecordSet.
Require Memory.

Import Bool Core ZMod Common MemoryBase Memory RecordSetNotations ZMod PMap_ext BinInt.

Section Definitions.

  Open Scope ZMod_scope.
  (** # Fat Pointers

A **fat pointer** defines an address inside a slice of a data memory page.

The slice begins on page with ID=[fp_page] starting at [fp_start] (inclusive) and ending at
[fp_start]+[fp_length] (exclusive).
*)
  Record fat_ptr :=
    mk_fat_ptr {
        fp_page: option page_id;
        fp_start: mem_address;
        fp_length: mem_address;
        fp_offset: mem_address;
      }.

  #[export] Instance etaFatPointer: Settable _
    := settable! mk_fat_ptr < fp_page; fp_start; fp_length; fp_offset>.
(** The absolute address encoded by a fat pointer is [fp_start + fp_offset].
In order to dereference it, the address should be in bounds, therefore,
**)
  Definition validate_in_bounds (p:fat_ptr) : bool := (lt_unsigned _ p.(fp_offset) p.(fp_length) ).

  (** Note: Valid heap/auxheap fat pointers always have [fp_start = 0], therefore
[fp_offset] is an absolute address in (aux_)heap.


## Usage

- Fat pointers are used to pass read-only slices of memory between contracts, either through [OpFarCall]/[OpMimicCall]/[OpDelegateCall] or through `ret`/`revert`.
- Fat pointers are used by instructions [OpLoad], [OpLoadInc], [OpStore], [OpStoreInc], [OpLoadPointer], [OpLoadPointerInc].
Additionally, they are used to forward data slices between external frames.
Pointers are created and managed by [OpPtrAdd], [OpPtrSub], [OpPtrPack] and [OpPtrShrink] instructions.
   *)

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
      fp_page := None;
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


  Definition is_trivial (p:fat_ptr) := (p.(fp_length) == zero32) && (p.(fp_offset)
                                                                     == zero32).

  Inductive fat_ptr_shrink : fat_ptr -> fat_ptr -> Prop :=
  | fps_shrink : forall p start start' length length' ofs,
      validate (mk_fat_ptr p start length ofs) false = no_exceptions ->
      start + ofs = (start', false) ->
      length - ofs = (length', false) ->
      fat_ptr_shrink (mk_fat_ptr p start length ofs) (mk_fat_ptr p start' length' zero32).

  (** Used by [OpPtrShrink] instruction. *)
  Inductive fat_ptr_trim_length : fat_ptr -> mem_address -> fat_ptr -> Prop :=
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


  (** ### Data slices


Accesses through fat pointers should be in bounds from [fp_start] (inclusive) to [fp_start]+[fp_length] (exclusive).

Accesses through [OpLoadPtr] and [OpLoadPtrInc] return 32-byte words starting at an address [fp_start + fp_offset], specified by  fat pointer.
However, the word might surpass the upper bound when [fp_length - fp_offset <= 32].
In this case, reads from out-of-bound bytes will return zero bytes.


Data slice is a virtual memory page holding a read-only fragment of some memory page.
   *)

  Definition data_page_slice_params := data_page_params <| writable := false |>.
  Definition data_slice := mem_parameterized data_page_slice_params.

  Definition slice  (from_incl to_excl: mem_address) (m:data_page) : data_slice :=
    let from_key := MemoryBase.addr_to_key _ from_incl in
    let to_key := MemoryBase.addr_to_key _ to_excl in
    let contents := pmap_slice m from_key to_key in
    mk_mem data_page_slice_params contents.


  (** Predicate [slice_from_ptr] describes a slice corresponding to a fat pointer pointer. *)
  Inductive slice_from_ptr (m:data_page) : fat_ptr -> data_slice -> Prop :=
  | sfp_apply:
    forall page start length ofs upper_bound readonly_slice,
      start + length = (upper_bound, false) ->
      slice start upper_bound  m = readonly_slice ->
      slice_from_ptr m (mk_fat_ptr  page start length ofs) readonly_slice.

End Definitions.
