Require SemanticCommon.

Import Arith Core TransientMemory MemoryBase Pointer PrimitiveValue SemanticCommon State isa.CoreSet spec.

Section PtrAddDefinition.
  Open Scope ZMod_scope.

  (** {{{!
describe(InstructionDoc(

ins=Instruction(
"OpPtrAdd",
"addp",
in1 = In.Reg,
in2 = In.Reg,
out1=Out.Reg,
modifiers=[Modifier.Swap],
kernelOnly = False,
notStatic = False),

legacy = ["`ptr.add in1, in2, out`", "`ptr.add.s in1, in2, out`"] ,
preamble = None,

summary = r"""
Takes a fat pointer from `in1` and a 32-bit unsigned number from `in2`. Advances
the fat pointer's offset by that number, and writes (`in2`{128...255} ||
incremented pointer) to `out`.
""",

semantic = r"""
1. Fetch input operands, swap them if `swap` modifier is set. Now operands are
   $\mathit{op_1}$ and $\mathit{op_2}$.
2. Ensure the $\mathit{op_1}$ is tagged as a pointer, and $\mathit{op_2}$ is not
   tagged as a pointer. Otherwise panic.
3. Decode fat pointer $\mathit{ptr_{in}}$ from $\mathit{op_1}$
4. Let $\mathit{diff}$ be $\mathit{op_2}$ truncated to 32 bits:

   $$\mathit{diff} := \mathit{op}_2 \mod 2^{32}$$

   It is required that $\mathit{op}_2 < \texttt{MAX\_OFFSET\_FOR\_ADD\_SUB}$,
   otherwise VM panics.

5. Advance pointer offset of $\mathit{ptr_{in}}$ by $\mathit{diff}$:

$$\mathit{ptr_{out}} := \mathit{ptr_{in}} | _\mathit{offset := offset + diff}$$

6. Store the result, tagged as a pointer, to `out`. The most significant 128 bits of result are taken from `op1`, the least significant bits hold an encoded pointer:

$$result := \mathit{op_1}\{255\dots128\} \#\# \texttt{encode}(\mathit{ptr_{out}})$$
""",
affectedState = "",
usage = """
- Used as a substitute for an absent MOV instruction to copy fat pointers around.
- Manipulating fat pointers to pass slices of memory between functions.""",
similar = f"See {PTR_MANIPULATION}."
))
}}}
*)

  Inductive step_ptradd : instruction -> smallstep :=
  | step_PtrAdd:
    forall s ofs new_ofs pid high128 (arg_delta:word) (mem_delta: mem_address) span,

      arg_delta < MAX_OFFSET_FOR_ADD_SUB = true ->
      mem_delta = low mem_address_bits arg_delta ->
      (false, new_ofs) = ofs + mem_delta ->

      step_ptradd (OpPtrAdd
              (Some (PtrValue (high128, NotNullPtr (mk_fat_ptr pid (mk_ptr span ofs)))))
              (IntValue arg_delta)
              (Some (PtrValue (high128, NotNullPtr (mk_fat_ptr pid (mk_ptr span new_ofs))))))
        s s
(** ## Panics

1. First argument is not a pointer (after accounting for `swap`).
 *)
  | step_PtrAdd_in1_not_ptr:
    forall s1 s2 ___ ____ _____,
      step_panic ExpectedFatPointer s1 s2 ->
      step_ptradd (OpPtrAdd (Some (IntValue ___)) ____ _____) s1 s2
  (** 2. Second argument is a pointer (after accounting for `swap`). *)
  | step_PtrAdd_in2_ptr:
    forall s1 s2 ___ ____ _____,
      step_panic ExpectedInteger s1 s2 ->
      step_ptradd (OpPtrAdd (Some (PtrValue ___)) (PtrValue ____) _____) s1 s2

  (** 3. Second argument is larger than [%MAX_OFFSET_FOR_ADD_SUB] (after
  accounting for `swap`). *)
  | step_PtrAdd_diff_too_large:
    forall s1 s2 (arg_delta:word) (mem_delta: mem_address) ___ ____,

      arg_delta >= MAX_OFFSET_FOR_ADD_SUB = true ->
      step_panic FatPointerDeltaTooLarge s1 s2 ->
      step_ptradd (OpPtrAdd (Some (PtrValue ___)) (IntValue arg_delta) ____) s1 s2

  (** 4. Addition overflows. *)
  | step_PtrAdd_overflow:
    forall s1 s2 ofs new_ofs pid (arg_delta:word) (mem_delta: mem_address) span high128,

      arg_delta < MAX_OFFSET_FOR_ADD_SUB = true ->
      mem_delta = low mem_address_bits arg_delta ->
      (true, new_ofs) = ofs + mem_delta ->

      step_panic FatPointerOverflow s1 s2 ->
      step_ptradd (OpPtrAdd
              (Some (PtrValue (high128, NotNullPtr (mk_fat_ptr pid (mk_ptr span ofs)))))
              (IntValue arg_delta)
              (Some (PtrValue (high128, NotNullPtr (mk_fat_ptr pid (mk_ptr span new_ofs))))))
        s1 s2.
End PtrAddDefinition.
