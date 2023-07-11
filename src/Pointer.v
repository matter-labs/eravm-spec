From RecordUpdate Require Import RecordSet.
Require Memory.

Import Bool Core ZMod Common MemoryBase Memory RecordSetNotations PMap_ext BinInt.

Section Definitions.
  Context (bytes_in_word := u32_of z_bytes_in_word).
  
  Open Scope ZMod_scope.
  (** This file describes concepts related to [%data_page]s: spans, heap
  pointers, and fat pointers.

# Span

A **span** is a range of addresses from [%s_start] inclusive
to [%s_start + s_length] exclusive. It is not bound to a specific page. *)

  Record span :=
    mk_span {
        s_start: mem_address;
        s_length: mem_address;
      }.

  Definition span_empty := mk_span zero32 zero32.

  (** ## Usage

  Spans enable creating **fat pointers** by encoding spans in
[%ForwardNewHeapPointer] and passing the encoded value in register.
It requires encoding the parameters according to [%ABI.FarRet.ABI] or
[%ABI.FarCall.ABI].
See [%FarCall] and [%FarRet].


In EraVM, heap variants have a bound; if memory is accessed beyond it, the bound
is adjusted and the growth (difference between bounds) is paid in ergs.
Definition [%span_induced_growth]
   *)
  Inductive span_induced_growth: span -> mem_address -> mem_address -> Prop :=
  | gb_bytes: forall fp_start fp_length query_bound current_bound,
      fp_start + fp_length = (query_bound, false) ->
      let diff := growth current_bound query_bound in
      span_induced_growth (mk_span fp_start fp_length) current_bound diff.

  Section HeapPointer.
    (** # Heap pointer

A **heap pointer** is a pair of an absolute address [%hp_addr] on some data page
and a limit [%hp_limit]. They are used in UMA instructions: [%OpLoad]/[%OpLoadInc], [%OpStore]/[%OpStoreInc].
*)

    Record heap_ptr :=
      mk_hptr
        {
          hp_addr: mem_address;
          hp_limit: mem_address;
        }.
    Definition heap_ptr_empty := mk_hptr zero32 zero32.

    (** Heap pointer $(\mathit{addr}, \mathit{limit})$ resolves to
$[0,\mathit{limit})$, as described by [%hp_resolves_to]. *)

    Inductive hp_resolves_to : heap_ptr -> mem_address -> Prop :=
    | tpr_apply: forall addr limit,
        ( addr < limit ) = true ->
        hp_resolves_to (mk_hptr addr limit) addr.

    Definition hp_span (hp:heap_ptr) : span :=
      mk_span zero32 hp.(hp_limit).

    (**
 **Shrinking a heap pointer** a pointer with [%hp_shrink] subtracts a number from its length; it is guaranteed not to overflow.

Shrinking may result in a pointer with $\mathit{offset}>\mathit{length}$, but such pointer will not resolve to a memory location.
    *)
    Inductive hp_shrink (diff: mem_address) : heap_ptr -> heap_ptr -> Prop :=
    | tptl_apply: forall length length' ofs,
        length - diff = (length', false) ->
        hp_shrink diff (mk_hptr ofs length) (mk_hptr ofs length').

    (** Incrementing a heap pointer with [%hp_inc] increases its offset by 32, the size of a word in bytes.
This is used by instructions [%OpLoadInc] and [%OpStoreInc].
     *)
    Inductive hp_inc : heap_ptr -> heap_ptr -> Prop :=
    |fpi_apply :
      forall ofs ofs' lim,
        ofs + bytes_in_word  = (ofs', false) ->
        hp_inc (mk_hptr ofs lim) (mk_hptr ofs' lim).

  (** ## Usage

Heap pointers are used by some UMA instructions and pointer manipulation instructions:

- [%OpLoad]/[%OpLoadInc]
- [%OpStore]/[%OpStoreInc]
- [%OpPtrAdd], [%OpPtrSub], [%OpPtrShrink]

The layout of a heap pointer in a 256-bit word is described by [%ABI.FatPointer.decode_heap_ptr].

## Relation to fat pointers

Heap pointers are bearing a similarity to fat pointers.
They can be thought about as fat pointers where the slice starts at 0, an offset is the address, length is the limit, and the page ID is ignored.
   *)
  End HeapPointer.

  (** Definition [%free_ptr] is auxiliary and is only used to facilitate the definition of [%fat_ptr]. *)
  Record free_ptr :=
    mk_ptr {
        p_span :> span;
        p_offset: mem_address;
      }.

  Definition fresh_ptr (s:span) : free_ptr :=
    mk_ptr s zero32.

  Definition validate_in_bounds (p:free_ptr) : bool :=  p.(p_offset) < p.(s_length) .

  Inductive ptr_resolves_to : free_ptr -> mem_address -> Prop :=
  | upr_apply: forall addr start ofs length,
      (ofs < length)  = true ->
      (addr, false) = start + ofs ->
      ptr_resolves_to (mk_ptr (mk_span start length) ofs) addr.

  Definition heap_ptr_to_free (hp:heap_ptr) : free_ptr :=
    mk_ptr (hp_span hp) hp.(hp_addr).

  Section FatPointer.
    (** # Fat pointer

A **fat pointer** defines an address inside a [%span] of a specific data memory page [%fp_page].
These four components are enough to unambiguously identify a **slice** of a data memory page. See [%Slice].

     *)
    Record fat_ptr :=
      mk_fat_ptr {
          fp_page: option page_id;
          fp_ptr :> free_ptr;
        }.

    (* begin hide *)
    Inductive fp_lift (P: free_ptr -> free_ptr -> Prop) : fat_ptr -> fat_ptr -> Prop :=
    |fpl_apply: forall i p1 p2, P p1 p2 ->
                           fp_lift P (mk_fat_ptr i p1) (mk_fat_ptr i p2).

    #[export] Instance etaSpan : Settable _ := settable! mk_span < s_start; s_length >.
    #[export] Instance etaFreePointer: Settable _ := settable! mk_ptr < p_span; p_offset >.
    #[export] Instance etaFatPointer: Settable _ := settable! mk_fat_ptr < fp_page; fp_ptr >.
    (* end hide *)
    (** ## Usage

- Fat pointers are used to pass read-only spans of [%data_page]s between contracts.
- Fat pointers are created from spans by [%OpFarCall]/[%OpMimicCall]/[%OpDelegateCall] or through [%OpFarRet]/[%OpFarRevert].

   - Far calls accept a serialized instance of [%FarCall.params] in a register.
     If it contains a span in [%fwd_memory], then when the contract starts executing, [%r1] is assigned the fat pointer obtained from the slice.
   - Far returns accept a serialized instance of [%FarRet.fwd_memory] in a register.
     If it contains a span in [%fwd_memory], then after return [%r1] is assigned the fat pointer obtained from the slice.
- An existing fat pointer is passed by using [%ForwardFatPointer].


Pointers may be created only by far calls ([%OpFarCall], [%OpMimicCall], [%OpDelegateCall]) or far returns ([%OpFarRet], [%OpFarRevert]).

     **)

    Record validation_exception :=
      mk_ptr_validation_exception
        {
          ptr_deref_beyond_heap_range : bool;
          ptr_bad_span: bool;
        }.

    Definition no_exceptions : validation_exception
      := mk_ptr_validation_exception false false.

    Definition free_ptr_empty :=
      {|
        p_span := span_empty;
        p_offset:= zero32;
      |}.

    Definition fat_ptr_empty :=
      {|
        fp_page := None;
        fp_ptr := free_ptr_empty;
      |}.


    (** A fat pointer $(\mathit{page}, \mathit{start}, \mathit{length}, \mathit{offset})$ is **invalid** if:

- $\mathit{start}+\mathit{length} \geq 2^{256}$, or
- $\mathit{offset} > \mathit{length}$.
     *)
    Definition validate (p:free_ptr) : validation_exception :=
      match p with
      | mk_ptr (mk_span start len) ofs =>
          {|
            ptr_deref_beyond_heap_range := is_overflowing _ (start + len);
            ptr_bad_span := ofs > len;
          |}
      end.

    Definition is_trivial (p:free_ptr) := (p.(s_length) == zero32) && (p.(p_offset) == zero32).

    (** **Shrinking a fat pointer** moves its $\mathit{start}$ to where $\mathit{start} + \mathit{offset}$ was, and sets $\mathit{offset}$ to zero:

$(\mathit{start}, \mathit{length}, \mathit{offset}) \mapsto (\mathit{start}+\mathit{offset}, \mathit{length}-\mathit{offset}, 0)$

![](img/ptr-shrinking.svg)


A fat pointer is automatically shrunk in two situations:

- by far calls with forwarding mode [%ForwardFatPointer];
- by returns from far calls with forwarding mode [%ForwardFatPointer].

     *)
    Inductive free_ptr_shrink : free_ptr -> free_ptr -> Prop :=
    | tps_shrink : forall start start' length length' ofs,
        validate (mk_ptr (mk_span start length) ofs) = no_exceptions ->
        start + ofs = (start', false) ->
        length - ofs = (length', false) ->
        free_ptr_shrink (mk_ptr (mk_span start length) ofs) (mk_ptr (mk_span start' length') zero32).

    Definition fp_shrink := fp_lift free_ptr_shrink.


    (** Incrementing a fat pointer with [%fp_inc] increases its offset by 32, the size of a word in bytes. This is used by the instruction [%OpLoadPointerInc]. *)

    Inductive ptr_inc : free_ptr -> free_ptr -> Prop :=
    |fpf_apply :
      forall ofs ofs' s,
        ofs + bytes_in_word = (ofs', false) ->
        ptr_inc (mk_ptr s ofs) (mk_ptr s ofs').


    Definition fp_inc := fp_lift ptr_inc.
  End FatPointer.

End Definitions.

Module Coercions.

  Coercion heap_ptr_to_free : heap_ptr >-> free_ptr.

End Coercions .
