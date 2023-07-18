Require Addressing Common Memory Predication.

Import Addressing Common Memory Predication Flags.

(**
- This file describes the syntax of assembly instructions.
 - The instruction semantic is described in a different place; see all files in [%sem] module.
 - This is a high-level instruction set, not an encoding-aware low-level machine
   instruction set. The distinction between them is of convenience: while in encoded machine instructions some fields are only occasionally used, the instructions from this set only contain used fields.

   For example, `xor`, `or`, and `and` bitwise operations are represented by
   three distinct instructions in this set; however, they are encoded using the
   same opcode and different modifiers. *)
Section Instructions.
(** # Common instruction modifiers

Modifiers alter the meaning of instruction.

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
  For example, take an instruction

  [%OpSub $a$ $b$ $c$ NoSwap PreserveFlags]

  It computes $a - b$ and stores the result to $c$.

  Adding `swap` modifier will change the syntax as follows:

  [%OpSub $a$ $b$ $c$ Swap PreserveFlags]

  The new meaning with `swap` modifier is to compute $b-a$.

  In binary operations the first input operand usually supports more
  sophisticated address modes: it can be e.g. fetched from stack, whereas the
  second one can only be fetched from a GPR.

  2. `set_flags`: if set, an instruction is allowed to change [%gs_flags]. If
    cleared, the instruction will not alter the flags.
   *)
  Inductive mod_set_flags := SetFlags | PreserveFlags.

  Definition apply_set_flags (md: mod_set_flags) (f f':flags_state) : flags_state :=
    match md with
    | SetFlags => f'
    | PreserveFlags => f
    end.

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
  | OpFarCall     (enc: in_reg) (dest: in_reg) (handler: imm_in) (is_static:bool) (is_shard_provided: bool)
  | OpMimicCall   (enc: in_reg) (dest: in_reg) (handler: imm_in) (is_static:bool) (is_shard_provided: bool)
  | OpDelegateCall(enc: in_reg) (dest: in_reg) (handler: imm_in) (is_static:bool) (is_shard_provided: bool)

  (*               quasi fat pointer + forwarding mode *)
  | OpNearRet
  | OpNearRetTo      (label: code_address)
  | OpFarRet         (args: in_reg)
  (*               quasi fat pointer + forwarding mode *)
  | OpNearRevert
  | OpNearRevertTo(label: code_address)
  | OpFarRevert   (args: in_reg)
  | OpNearPanicTo (label: code_address)
  | OpPanic

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


  | OpSLoad          (in1: in_reg)               (out: out_reg)
  | OpSStore         (in1: in_reg) (in2: in_reg)
  | OpToL1Message    (in1: in_reg) (in2: in_reg)                (is_first: bool)
  | OpEvent          (in1: in_reg) (in2: in_reg)                (is_first: bool)
  | OpPrecompileCall (in1: in_reg)               (out: out_reg)
  .

  (** ## Predicated instruction

The type [%instruction_predicated] defines the predicated instruction.
These are the instructions stored on [%code_page]s.

Such instruction contains two parts:

- opcode-specific part;
- execution conditions, describing under which conditions (flags) the instruction will be executed. *)
  Record instruction_predicated: Set :=
    Ins {
        ins_spec: instruction;
        ins_cond: predicate;
      }.

  (** Invalid instruction. It is a default value on code memory pages. See
  [%code_page]. It is parameterized by an instruction type for convenience of
  defining it. *)

  Definition instruction_invalid : instruction_predicated :=
    {|
      ins_spec := OpInvalid;
      ins_cond:= IfAlways
    |}.

End Instructions.

(** A helper definition to specialize a code page with a (just defined) instruction type. *)
Definition code_page : Type := code_page instruction_invalid.
