Require SemanticCommon.

Import Common Core TransientMemory isa.CoreSet State
  Pointer PrimitiveValue SemanticCommon ZArith.

Section PtrShrinkDefinition.
  Open Scope ZMod_scope.

  Inductive step_ptrshrink: instruction -> smallstep :=
  (** {{{!
 describe(InstructionDoc(

ins=Instruction(
"OpPtrShrink",
"shrnk",
in1 = In.Reg,
in2 = In.Reg,
out1=Out.Reg,
modifiers=[Modifier.Swap],
kernelOnly = False,
notStatic = False),

legacy = ["`ptr.shrink in1, in2, out`", "`ptr.shrink.s in1, in2, out`, for setting the swap modifier."] ,
preamble = r"""
**Attention**: **shrinking** and **narrowing** far pointers are different. See
  [%fat_ptr_shrink] and [%fat_ptr_narrow].
""",

summary = r"""
**Shrink** the fat pointer, decreasing its length.
""",

semantic = r"""
1. Fetch input operands, swap them if `swap` modifier is set. Now operands are $\mathit{op_1}$ and $\mathit{op_2}$.
2. Ensure the $\mathit{op_1}$ is tagged as a pointer, and $\mathit{op_2}$ is not tagged as a pointer. Otherwise panic.
3. Decode fat pointer $\mathit{ptr_{in}}$ from $\mathit{op_1}$
4. Let $\mathit{diff}$ be $\mathit{op_2}$ truncated to 32 bits:

$$\mathit{diff} := \mathit{op}_2 \mod 2^{32}$$

5. Rewind pointer length of $\mathit{ptr_{in}}$ by $\mathit{diff}$:

$$\mathit{ptr_{out}} := \mathit{ptr_{in}} | _\mathit{length := length - diff}$$

6. Store the result, tagged as a pointer, to `out`:

$$result := \mathit{op_1}\{255\dots128\} \#\# \texttt{encode}(\mathit{ptr_{out}})$$
""",
affectedState = "",
usage = r"""
- Instead of copying a fragment of a memory region defined by a fat pointer to
  pass it to some other contract, we may shrink the pointer and cheaply pass a
  sub-fragment to another contract without copying.
""",
similar = f"See {PTR_MANIPULATION}."
))
}}} *)

  | step_PtrShrink :
    forall  s high128 ptr_in ptr_out delta ,

      let diff := low mem_address_bits delta in
      fat_ptr_shrink diff ptr_in ptr_out ->


      step_ptrshrink (OpPtrShrink
                        (Some (PtrValue (high128, NotNullPtr ptr_in)))
                        (IntValue delta)
                        (Some (PtrValue (high128, NotNullPtr ptr_out))))
        s s
(** ## Panics

1. First argument is not a pointer (after accounting for `swap`).
 *)
  | step_PtrShrink_in1_not_ptr:
    forall s1 s2 ___2 ___3 ___4,
      step_panic ExpectedFatPointer s1 s2 ->
      step_ptrshrink (OpPtrShrink (Some (IntValue ___2)) ___3 ___4) s1 s2
  (** 2. Second argument is a pointer (after accounting for `swap`). *)
  | step_PtrShrink_in2_ptr:
    forall s1 s2 ___1 ___3 ___4,
      step_panic ExpectedFatPointer s1 s2 ->
      step_ptrshrink (OpPtrShrink (Some ___1) (PtrValue ___3) ___4) s1 s2
  (** 3. Shrinking underflows. *)
  | step_PtrShrink_underflow:
    forall s1 s2 high128 ptr_in ptr_out delta ,
      let diff := low mem_address_bits delta in
      fat_ptr_shrink_OF diff ptr_in = None ->

      step_ptrshrink (OpPtrShrink
                         (Some (PtrValue (high128, NotNullPtr ptr_in)))
                        (IntValue delta)
                        (Some (PtrValue (high128, NotNullPtr ptr_out))))
        s1 s2
  .
End PtrShrinkDefinition.
