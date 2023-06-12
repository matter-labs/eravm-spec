Require Addressing Common Condition Memory Ergs CodeStorage.

Import Addressing Common Condition Memory Ergs CodeStorage.

(** - This file describes the syntax of assembly instructions.
 - The instruction semantics is described in a different place; see [step]. 
 - This is a high-level instruction set, similar but not exactly matching machine instructions.

   For example, `xor`, `or`, and `and` bitwise operations are represented by
   three distinct instructions in this set; however, they are encoded to three
   instructions with the same opcode and different modifiers.

*)
Section Def.
(** # Instruction modifiers

Modifiers alter the meaning of instruction.

## Common modifiers
Two modifiers are commonly encountered:

  1. `swap`: if an instruction has two input operands, this modifier swaps
    them.
   *) 
  Inductive mod_swap := Swap | NoSwap.

  Definition apply_swap {T} (md: mod_swap) (a b:T) : T*T :=
    match md with
    | NoSwap => (a,b)
    | Swap => (b,a)
    end.

  (**
  For example, if `sub in1, in2, out` computes $\mathit{in_1 - in_2}$,
  `sub.s in1,in2,out` (where `.s` stands for "with `swap` modifier") computes $\mathit{in_2 - in_1}$.

  This is useful because `in1` usually has richer address modes: it can be e.g.
  fetched from stack, whereas `in2` can only be fetched from a GPR.


  2. `set_flags`: if set, instruction is allowed to change the flags. If
    cleared, the instruction will not touch the flags.
   *)
  Inductive mod_set_flags := SetFlags | PreserveFlags.

  Definition apply_set_flags (md: mod_set_flags) (f f':flags_state) : flags_state :=
    match md with
    | SetFlags => f'
    | PreserveFlags => f
    end.

  Inductive mod_inc32 := Inc32 | NoInc32.
  Inductive instruction: Set :=
  | OpInvalid
  | OpNoOp
  | OpModSP       (in1: in_any) (out1: out_any)
  | OpJump        (dest: in_any)
  | OpAnd         (in1: in_any) (in2: in_reg)  (out1: out_any)                 (swap:mod_swap) (flags:mod_set_flags)
  | OpOr          (in1: in_any) (in2: in_reg)  (out1: out_any)                 (swap:mod_swap) (flags:mod_set_flags)
  | OpXor         (in1: in_any) (in2: in_reg)  (out1: out_any)                 (swap:mod_swap) (flags:mod_set_flags)
  | OpAdd         (in1: in_any) (in2: in_reg)  (out1: out_any)                 (swap:mod_swap) (flags:mod_set_flags)
  | OpSub         (in1: in_any) (in2: in_reg)  (out1: out_any)                 (swap:mod_swap) (flags:mod_set_flags)

  | OpShl         (in1: in_any) (in2: in_reg)  (out1: out_any)                                 (flags:mod_set_flags)
  | OpShr         (in1: in_any) (in2: in_reg)  (out1: out_any)                                 (flags:mod_set_flags)
  | OpRol         (in1: in_any) (in2: in_reg)  (out1: out_any)                                 (flags:mod_set_flags)
  | OpRor         (in1: in_any) (in2: in_reg)  (out1: out_any)                                 (flags:mod_set_flags)

  | OpMul         (in1: in_any) (in2: in_reg)  (out1: out_any) (out2: out_reg) (swap:mod_swap) (flags:mod_set_flags)
  | OpDiv         (in1: in_any) (in2: in_reg)  (out1: out_any) (out2: out_reg) (swap:mod_swap) (flags:mod_set_flags)
  | OpNearCall    (in1: in_reg) (dest: imm_in) (handler: imm_in)
  | OpFarCall     (enc: in_reg) (dest: in_reg) (handler: imm_in) (is_static:bool)
  | OpMimicCall   (enc: in_reg) (dest: in_reg) (handler: imm_in) (is_static:bool)
  | OpDelegateCall(enc: in_reg) (dest: in_reg) (handler: imm_in) (is_static:bool)

  (*               quasi fat pointer + forwarding mode *)
  | OpRet         (args: in_reg) (label: option code_address)
  (*               quasi fat pointer + forwarding mode *)
  | OpRevert      (args: in_reg) (label: option code_address)
  | OpPanic       (label: option code_address)

  | OpPtrAdd      (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)
  | OpPtrSub      (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)
  | OpPtrShrink   (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)
  | OpPtrPack     (in1: in_any) (in2: in_reg)  (out: out_any) (swap:mod_swap)

                  
  | OpLoad        (ptr: in_regimm) (res: out_reg) (mem:data_page_type)
  | OpLoadInc     (ptr: in_regimm) (res: out_reg) (mem:data_page_type) (inc_ptr: out_reg)
  | OpStore       (ptr: in_regimm) (val: in_reg)  (mem:data_page_type) 
  | OpStoreInc    (ptr: in_regimm) (val: in_reg)  (mem:data_page_type) (inc_ptr: out_reg)
                  
                  
  | OpLoadPointer     (ptr: in_reg)  (res: out_reg)
  | OpLoadPointerInc  (ptr: in_reg)  (res: out_reg) (inc_ptr: out_reg)


  | OpContextThis                                (out: out_reg)
  | OpContextCaller                              (out: out_reg)
  | OpContextCodeAddress                         (out: out_reg)
  | OpContextMeta                                (out: out_reg)
  | OpContextErgsLeft                            (out: out_reg)
  | OpContextSp                                  (out: out_reg)
  | OpContextGetContextU128                      (out: out_reg)
  | OpContextSetContextU128        (in1: in_reg)
  | OpContextSetErgsPerPubdataByte (in1: in_reg)
  | OpContextIncrementTxNumber
  .

  (** ## Common definitions

An instruction type, including:

- opcode-specific part;
- execution conditions, describing under which conditions (flags) the instruction will be executed. *)
  Record instruction_predicated: Set :=
    Ins {
        ins_spec: instruction;
        ins_cond: cond;
      }.

  (** Invalid instruction. It is a default value on code memory pages. See
  [code_page]. It is parameterized by an instruction type for convenience of
  defining it. *)

  Definition instruction_invalid : instruction_predicated :=
    {|
      ins_spec := OpInvalid;
      ins_cond:= IfAlways
    |}.

End Def.

(** A helper definition to specialize a code page with a (just defined) instruction type. *)
Definition code_page : Type := code_page instruction_predicated instruction_invalid.
Definition code_storage_type: Type := code_storage instruction_predicated instruction_invalid.


Section Costs.
  Import ZMod ZArith.

(** # Costs

Basic costs of all instructions. They get deducted when the instruction starts executing; see [Semantics.step]. *)
  
  Definition base_cost (ins:instruction) :=
    (match ins with
     | OpInvalid => INVALID_OPCODE_ERGS
     | OpNoOp | OpModSP _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpJump _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpAnd _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpOr _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpXor _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpAdd _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpSub _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS

     | OpShl _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpShr _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpRol _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpRor _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS

     | OpMul _ _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpDiv _ _ _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     | OpNearCall _ _ _ => AVERAGE_OPCODE_ERGS + CALL_LIKE_ERGS_COST
     | OpFarCall _ _ _ _
     | OpDelegateCall _ _ _ _
     | OpMimicCall _ _ _ _ => 2 * VM_CYCLE_COST_IN_ERGS
                             + RAM_PERMUTATION_COST_IN_ERGS
                             + STORAGE_READ_IO_PRICE
                             + CALL_LIKE_ERGS_COST
                             + STORAGE_SORTER_COST_IN_ERGS
                             + CODE_DECOMMITMENT_SORTER_COST_IN_ERGS

     | OpRet _ _ | OpRevert _ _ | OpPanic _ => AVERAGE_OPCODE_ERGS
     | OpPtrAdd _ _ _ _
     | OpPtrSub _ _ _ _
     | OpPtrShrink _ _ _ _
     | OpPtrPack _ _ _ _ => RICH_ADDRESSING_OPCODE_ERGS
     |
       OpStore _ _ _
     | OpStoreInc _ _ _ _ 
       => 2 * VM_CYCLE_COST_IN_ERGS + 5 * RAM_PERMUTATION_COST_IN_ERGS

     | OpLoad _ _ _
     | OpLoadInc _ _ _ _
     | OpLoadPointer _ _
     | OpLoadPointerInc _ _ _
       => VM_CYCLE_COST_IN_ERGS + 3 * RAM_PERMUTATION_COST_IN_ERGS

     | OpContextThis _
     | OpContextCaller _
     | OpContextCodeAddress _
     | OpContextMeta _
     | OpContextErgsLeft _
     | OpContextSp _
     | OpContextGetContextU128 _
     | OpContextSetContextU128 _
     | OpContextSetErgsPerPubdataByte _
     | OpContextIncrementTxNumber => AVERAGE_OPCODE_ERGS
     end)%Z.
End Costs.

(** Function [allowed_static_ctx] returns [true] if instruction [ins] is allowed
in a static context. *)
Definition allowed_static_ctx (ins:instruction) : bool :=
  match ins with
  | OpContextSetContextU128 _
  | OpContextSetErgsPerPubdataByte _
  | OpContextIncrementTxNumber => false
  | _ => true
  end.

(** Function [check_allowed_static_ctx] returns [false] if:

- an instruction [ins] is not allowed in static context, and
- the current context is static, as indicated by [current_ctx_is_static].
*)
Definition check_allowed_static_ctx
  (ins: instruction)
  (current_ctx_is_static: bool) : bool :=
  if current_ctx_is_static
  then allowed_static_ctx ins
  else true.

(** Is instruction only allowed in kernel mode? *)
Definition requires_kernel (ins: instruction) : bool :=
  match ins with
  | OpMimicCall _ _ _ _
  | OpContextSetContextU128 _
  | OpContextSetErgsPerPubdataByte _
  | OpContextIncrementTxNumber => true

  | _ => false
  end.

(** Function [check_requires_kernel] returns [false] if:

- an instruction [ins] requires kernel mode, and 
- not in kernel mode, as indicated by [in_kernel].
*)
Definition check_requires_kernel
  (ins: instruction)
  (in_kernel: bool) : bool :=
  if negb in_kernel
  then negb (requires_kernel ins)
  else true.
