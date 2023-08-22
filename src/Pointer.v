From RecordUpdate Require Import RecordSet.
Require Memory.

Import Bool Core ZMod Common MemoryBase Memory RecordSetNotations PMap_ext BinInt.

Section Definitions.
  Context (bytes_in_word := u32_of z_bytes_in_word).

  Open Scope ZMod_scope.
  (** This library describes concepts related to [%data_page]s: spans, heap
  pointers, and fat pointers.

# Span

A **span** is a range of addresses from [%s_start] inclusive
to [%s_start + s_length] exclusive. It is not bound to a specific page. *)

  Record span :=
    mk_span {
        s_start : mem_address;
        s_length: mem_address;
      }.

  Definition span_empty := mk_span zero32 zero32.

  Inductive span_limit: span -> mem_address -> Prop :=
    | sl_apply:forall start length limit,
      (limit, false) = start + length ->
      span_limit (mk_span start length) limit.

  Inductive bound_of_span : span -> data_page_type -> page_bound -> Prop :=
    | qos_apply: forall s limit hv,
        span_limit s limit ->
        bound_of_span s hv (hv, limit).
  (** ## Usage

Passing a span in [%ForwardNewHeapPointer] as an argument to far calls or far
returns creates a **fat pointer**.
The required encoding is described by [%ABI.FarRet.ABI] or [%ABI.FarCall.ABI].
See [%FarCall] and [%FarRet].

See also: [%Slices].

In EraVM, heap variants have a bound, stored in call stack frames (see
[%ctx_heap_bound] of [%ecf_mem_ctx]).
If memory is accessed beyond this bound, the bound is adjusted and the growth
(difference between bounds) is paid in ergs. Definition [%span_induced_growth]
computes how many bytes should the user pay for. *)
  Inductive span_induced_growth: span -> mem_address -> mem_address -> Prop :=
  | gb_bytes: forall start length query_bound current_bound diff,
      start + length = (query_bound, false) ->
      diff = growth current_bound query_bound ->
      span_induced_growth (mk_span start length) current_bound diff.

  Section HeapPointer.
    (** # Heap pointer

A **heap pointer** is an absolute address [%hp_addr] on some data page.
Heap pointers are used in instructions:

 - [%OpLoad]/[%OpLoadInc]
 - [%OpStore]/[%OpStoreInc]
*)
    Record heap_ptr :=
      mk_hptr
        {
          hp_addr: mem_address;
          (*hp_limit: mem_address;*)
        }.
    Definition heap_ptr_empty : heap_ptr := mk_hptr zero32.

    Inductive hp_resolves_to : heap_ptr -> mem_address -> Prop :=
    | tpr_apply: forall addr,
        hp_resolves_to (mk_hptr addr) addr.

    (* Definition hp_span (hp:heap_ptr) : span := *)
    (*   mk_span zero32 hp.(hp_limit). *)

    (** Incrementing a heap pointer with [%hp_inc] increases its offset by 32,
the size of a word in bytes. This is used by instructions [%OpLoadInc] and
[%OpStoreInc]. *)
    Inductive hp_inc : heap_ptr -> heap_ptr -> Prop :=
    |fpi_apply :
      forall ofs ofs',
        ofs + bytes_in_word  = (ofs', false) ->
        hp_inc (mk_hptr ofs) (mk_hptr ofs' ).

    Definition hp_inc_OF (hp: heap_ptr) : option heap_ptr :=
      match hp with
      | mk_hptr ofs =>
          match ofs + bytes_in_word with
          | (ofs', false) => Some (mk_hptr ofs')
          | _ => None
          end
      end.
  (** ## Usage

Heap pointers are used by the following instructions:

- [%OpLoad]/[%OpLoadInc]
- [%OpStore]/[%OpStoreInc]

The layout of a heap pointer in a 256-bit word is described by [%ABI.FatPointer.decode_heap_ptr].

## Relation to fat pointers

Heap pointers are bearing a similarity to fat pointers.
They can be thought about as fat pointers where:

- the span starts at 0;
- an offset is the address;
- length is the limit, and
- page ID is ignored.

Heap pointers are not necessarily tagged and do not receive any special
treatment from the VM's side.
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

  (* Definition heap_ptr_to_free (hp:heap_ptr) : free_ptr := *)
  (*   mk_ptr (hp_span hp) hp.(hp_addr). *)

  Inductive word_upper_bound : heap_ptr -> mem_address -> Prop :=
  | qbu_apply : forall start upper_bound,
      let bytes_in_word := int_mod_of _ Core.z_bytes_in_word in
      start + bytes_in_word  = (upper_bound, false) ->
      word_upper_bound (mk_hptr start) upper_bound.

  Section FatPointer.
    (** # Fat pointer



A **fat pointer** defines an address inside a [%span] of a specific data memory page [%fp_page].
We may denote is as a 4-tuple: $(\mathit{page, start, length, offset})$.
These four components are enough to unambiguously identify a **[%slice]** of a data memory page.
     *)
    Record fat_ptr :=
      mk_fat_ptr {
          fp_page: option page_id;
          fp_ptr :> free_ptr;
        }.

    (* begin hide *)
    Inductive fat_ptr_liftP (P: free_ptr -> free_ptr -> Prop) : fat_ptr -> fat_ptr -> Prop :=
    |fpl_apply: forall i p1 p2, P p1 p2 ->
                           fat_ptr_liftP P (mk_fat_ptr i p1) (mk_fat_ptr i p2).

    Definition fat_ptr_opt_map (F: free_ptr -> option free_ptr) : fat_ptr -> option fat_ptr :=
      fun fp =>
        match fp with
        | mk_fat_ptr page ptr =>
            match F ptr with
              | Some res => Some (mk_fat_ptr page res)
              | None => None
            end
        end.

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

If $\mathit{offset} = \mathit{length}$, the span of the pointer is empty, but it is still valid.
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

    (** **Narrowing a fat pointer** moves its $\mathit{start}$ to where $\mathit{start} + \mathit{offset}$ was, and sets $\mathit{offset}$ to zero:

$(\mathit{page}, \mathit{start}, \mathit{length}, \mathit{offset}) \mapsto (\mathit{page}, \mathit{start}+\mathit{offset}, \mathit{length}-\mathit{offset}, 0)$

![](img/ptr-narrowing.svg)


A fat pointer is automatically narrowed in two situations:

- by far calls with forwarding mode [%ForwardFatPointer];
- by returns from far calls with forwarding mode [%ForwardFatPointer].

**Attention**: **shrinking** and **narrowing** far pointers are different. See [%fat_ptr_shrink] and [%fat_ptr_narrow].
     *)
    Inductive free_ptr_narrow: free_ptr -> free_ptr -> Prop :=
    | tps_narrow: forall start start' length length' ofs,
        validate (mk_ptr (mk_span start length) ofs) = no_exceptions ->
        start + ofs = (start', false) ->
        length - ofs = (length', false) ->
        free_ptr_narrow (mk_ptr (mk_span start length) ofs) (mk_ptr (mk_span start' length') zero32).

    Definition fat_ptr_narrow := fat_ptr_liftP free_ptr_narrow.


(** **Shrinking a fat pointer** with [%fat_ptr_shrink] subtracts a given number [%diff] from its length; it is guaranteed to not overflow.

Shrinking may result in a pointer with $\mathit{offset}>\mathit{length}$, but such pointer will not resolve to a memory location.

    *)
    Inductive free_ptr_shrink (diff: mem_address) : free_ptr -> free_ptr -> Prop :=
    | tptl_apply: forall start ofs length length',
        length - diff = (length', false) ->
        free_ptr_shrink diff (mk_ptr (mk_span start length) ofs) (mk_ptr (mk_span start length') ofs).

    Definition free_ptr_shrink_OF (diff: mem_address) : free_ptr -> option free_ptr :=
      fun fp => match fp with
              | mk_ptr (mk_span start length) p_offset =>
                  match length - diff with
                  | (length', false) => Some (mk_ptr (mk_span start length') p_offset)
                  | _ => None
                  end
              end.

    Definition fat_ptr_shrink diff := fat_ptr_liftP (free_ptr_shrink diff).
    Definition fat_ptr_shrink_OF diff := fat_ptr_opt_map (free_ptr_shrink_OF diff).
    (** Incrementing a fat pointer with [%fp_inc] increases its offset by 32, the size of a word in bytes. This is used by the instruction [%OpLoadPointerInc]. *)

    Definition ptr_inc_OF (p: free_ptr) : option free_ptr :=
      match p with
      | mk_ptr s ofs =>
        match ofs + bytes_in_word with
        | (ofs', false) => Some (mk_ptr s ofs')
        | _ => None
        end
      end.

    Inductive ptr_inc : free_ptr -> free_ptr -> Prop :=
    |fpf_apply :
      forall ofs ofs' s,
        ofs + bytes_in_word = (ofs', false) ->
        ptr_inc (mk_ptr s ofs) (mk_ptr s ofs').


    Definition fat_ptr_inc := fat_ptr_liftP ptr_inc.
    Definition fat_ptr_inc_OF := fat_ptr_opt_map ptr_inc_OF.
  End FatPointer.

End Definitions.
