From RecordUpdate Require Import RecordSet.

Require
ABI
Bool
CallStack
Coder
Common
Flags
GPR
MemoryContext
MemoryManagement
Pointer
PrimitiveValue
SemanticCommon
State.

Import
ABI
FatPointerABI
Bool
CallStack
Coder
Common
Flags
GPR
isa.CoreSet
MemoryContext
MemoryManagement
Pointer
PrimitiveValue
RecordSetNotations
SemanticCommon
State
StepPanic
.

Section FarRetDefinition.

  Let reserve regs :=
   regs    <| r2 := reserved |> <| r3 := reserved |> <| r4 := reserved |>.

  Inductive step_farret: instruction -> tsmallstep :=
(** # Far return (normal return, not panic/revert)

## Abstract Syntax

[%OpFarRet (args: in_reg)]

## Syntax

`ret in1`

  A normal return from a **far** call. Will pop up current callframe, return
  unspent ergs to the caller, and continue execution from the saved return
  address (from where the call had taken place). The register `args`
  describes a span of memory passed to the external caller.

  The assembler expands `ret` to `ret r1`; `r1` is ignored by returns from near calls.

## Semantic

1. Fetch the value from register `args` and decode the value of type [%fwd_memory]:

   ```
   Inductive fwd_memory :=
     ForwardFatPointer (p:fat_ptr)
   | ForwardNewFatPointer (heap_var: data_page_type) (s:span).
   ```

   The exact encoding is described by ABI.

2. Forward memory to the caller (see [%paid_forward]):
   - If `args` is [%ForwardFatPointer p], an existing [%fat_ptr] is forwarded:
      + ensure that the register containing `args` is tagged as a pointer.
      + ensure that the memory page of `p` does NOT refer to a page owned by an older frame.
      + [%fat_ptr_narrow p] so it starts at its current offset, and the offset is reset to zero.

     There is no payment because the existing fat pointer has already been paid for.

     **Attention**: **shrinking** and **narrowing** far pointers are different. See [%fat_ptr_shrink] and [%fat_ptr_narrow].

   - If `args` is [%ForwardNewFatPointer heap_variant [start; limit)], a new
     [%fat_ptr] is created:
      + let $B$ be the bound of the [%heap_variant] taken from
        [%ctx_heap_bound] field of [%ecf_mem_ctx] of the [%active_extframe].
      + let $I$ be the page id of the [%heap_variant] taken from
        [%ctx_heap_page_id] field of [%ecf_mem_ctx] of the [%active_extframe].
      + build a fat pointer $P$ from the span as described in
        [%paid_forward_heap_span].

         $$P := (I, (\mathit{start}, \mathit{limit}), 0)$$

      + if $\mathit{start} + \mathit{limit} >B$, pay for the growth difference
        ([%growth_cost] $(\mathit{start} + \mathit{limit} - B)$).

     Note: it is not useful to readjust the current heap/auxheap bounds after
     paying for growth. The bounds are part of [%mem_ctx] of the topmost frame, which is about to be discarded.

3. Return the remaining ergs from [%cf_ergs_remaining] of the destroyed frame to the caller.
4. Clear flags.
5. Encode $P$ and store it in register [%r1], setting its pointer tag.

   All other registers are zeroed. Registers [%r2], [%r3], and [%r4] are
   reserved and may gain a special meaning in newer versions of EraVM.
6. Clear context register.
*)
| step_RetExt_heapvar:
  forall pages cf caller_stack cs1 new_caller new_regs ___1 ___2 ___3 out_ptr heap_type hspan params s1 s2 status enc_ptr,
    let cs0 := ExternalCall cf (Some caller_stack) in

    paid_forward_new_fat_ptr heap_type hspan cs0 (out_ptr, cs1) ->
    ergs_return_caller_and_drop cs1 new_caller ->
    params = FarRetABI.mk_params (ForwardNewFatPointer heap_type hspan) ->
    Some enc_ptr = encode_fat_ptr_word zero128 (NotNullPtr out_ptr) ->
    new_regs = (reserve regs_state_zero)
                             <| r1 := PtrValue enc_ptr |> ->
    step_transient_only {|
                          gs_flags        := ___1 ;
                          gs_callstack    := cs0;
                          gs_regs         := ___2;
                          gs_context_u128 := ___3;


                          gs_pages        := pages;
                          gs_status       := status;
                        |}
                        {|
                          gs_flags        := flags_clear;
                          gs_callstack    := new_caller;
                          gs_regs         := new_regs;
                          gs_context_u128 := zero128;


                          gs_pages        := pages;
                          gs_status       := status;
                           |} s1 s2 ->
    step_farret (OpFarRet (Some (IntValue params))) s1 s2

  | step_RetExt_ForwardFatPointer:
  forall pages cf caller_stack cs1 new_caller new_regs ___1 ___2 ___3 in_ptr out_ptr page params s1 s2 status enc_ptr,
    let cs0 := ExternalCall cf (Some caller_stack) in

    in_ptr.(fp_page) = Some page ->

    page_older page (get_mem_ctx cs0) = false->

    validate in_ptr = no_exceptions ->

    fat_ptr_narrow in_ptr out_ptr ->

    ergs_return_caller_and_drop cs1 new_caller ->
    params = FarRetABI.mk_params (ForwardExistingFatPointer (NotNullPtr in_ptr)) ->
    Some enc_ptr = encode_fat_ptr_word zero128 (NotNullPtr out_ptr) ->
    new_regs = (reserve regs_state_zero)
                             <| r1 := PtrValue enc_ptr |> ->
    step_transient_only {|
                          gs_flags        := ___1 ;
                          gs_callstack    := cs0;
                          gs_regs         := ___2;
                          gs_context_u128 := ___3;


                          gs_pages        := pages;
                          gs_status       := status;
                        |}
                        {|
                          gs_flags        := flags_clear;
                          gs_callstack    := new_caller;
                          gs_regs         := new_regs;

                          gs_context_u128 := zero128;
                          gs_pages        := pages;
                          gs_status       := status;
                          |} s1 s2 ->
    step_farret (OpFarRet (Some (PtrValue params))) s1 s2
(** ## Affected parts of VM state

- Flags are cleared.
- Context register is zeroed (only returns from far calls).
- Registers are cleared (only returns from far calls).
- Execution stack:
  + Current frame is dropped.
  + Caller frame:
    * Unspent ergs are given back to caller (but memory growth is paid first).

## Usage

## Similar instructions

- `revert` executes the current frame's exception handler instead of returning
  to the caller.
- `panic` executes the current frame's exception handler instead of returning to
  the caller, and sets overflow flag.

## Panics

1. Attempt to forward an existing fat pointer, but the value holding [%RetABI] is not tagged as a pointer.
*)

  | step_RetExt_ForwardFatPointer_requires_ptrtag:
  forall cf caller_stack params ___1 ___2 (s1 s2:state),
    let cs0 := ExternalCall cf (Some caller_stack) in
    gs_callstack s1 = cs0 ->
    params = FarRetABI.mk_params (ForwardExistingFatPointer ___1) ->
    step_panic
      RetABIExistingFatPointerWithoutTag
      s1 s2 ->
    step_farret (OpFarRet (Some (IntValue ___2))) s1 s2

(** 2. Attempt to return a pointer created before the current callframe.
It is forbidden to pass a pointer to a contract in a far call and return it back.
Otherwise we could create a [%fat_ptr] $P$ to a heap page of contract $A$, pass it to a contract $B$, return it back to $A$, and then modify the contents on the heap page of $A$. This way we will also modify the memory [%slice] associated with $P$.

In other words, this is a situation where:

- caller makes far call to some contract;
- callee does return-forward @calldataptr;
- caller modifies calldata corresponding heap region, that leads to modification of returndata.

*)
  | step_RetExt_ForwardFatPointer_returning_older_pointer:
  forall cf caller_stack in_ptr page params (s1 s2:state) _tag,
    let cs0 := ExternalCall cf (Some caller_stack) in
    gs_callstack s1 = cs0 ->

    in_ptr.(fp_page) = Some page ->

    page_older page (get_mem_ctx cs0) = true ->
    params = FarRetABI.mk_params (ForwardExistingFatPointer (NotNullPtr in_ptr)) ->
    step_panic
      RetABIReturnsPointerCreatedByCaller
      s1 s2 ->
    step_farret (OpFarRet (Some (mk_pv _tag params))) s1 s2
(** 3. Attempt to return a malformed pointer. *)
  | step_RetExt_ForwardFatPointer_returning_malformed_pointer:
  forall cf caller_stack _tag (in_ptr: fat_ptr) params (s1 s2:state) ,
    let cs0 := ExternalCall cf (Some caller_stack) in
    gs_callstack s1 = cs0 ->

    validate in_ptr <> no_exceptions ->

    params = FarRetABI.mk_params (ForwardExistingFatPointer (NotNullPtr in_ptr)) ->
    step_panic
      FatPointerMalformed
      s1 s2 ->
    step_farret (OpFarRet (Some (mk_pv _tag params))) s1 s2
(** 4. Attempt to return a new pointer but unable to pay for memory growth. *)
| step_RetExt_heapvar_growth_unaffordable:
  forall cf caller_stack _tag heap_type hspan params (s1 s2:state),
    let cs0 := ExternalCall cf (Some caller_stack) in
    gs_callstack s1 = cs0 ->
    params = FarRetABI.mk_params (ForwardNewFatPointer heap_type hspan) ->
    growth_to_span_unaffordable cs0 heap_type hspan ->
    step_panic
      FatPointerCreationUnaffordable
      s1 s2 ->
    step_farret (OpFarRet (Some (mk_pv _tag params))) s1 s2
  .

End FarRetDefinition.
