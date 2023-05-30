From RecordUpdate Require Import RecordSet.
Require  sem.SemanticCommon.

Import Bool ZArith Common Condition Instruction ExecutionStack Memory MemoryOps State ZMod
  ZBits Arg Arg.Coercions RecordSetNotations SemanticCommon.
(** * Binary operations *)

(**
** Common binary operation semantic

The predicate [binop_effect] describes a scheme of operation shared by binary operations:

<<
- `add`
- `sub`
- `and`
- `or`
- `xor`

These instructions follow the format:

`<OPCODE> (in1: in_any) (in2:in_reg) (out: out_any) (swap_mod:bool) (set_flags_mod:bool)`:


The operation follows a similar scheme as described below. It is parameterized using a function `F` to calculate the resultant value and flags.

1. **Fetch `op1` from `in1`** ::  Fetch operand `op1` from `in1`. It uses full addressing mode, i.e. may be taken from registers, memory, in absolute or relative way.
2. **Adjust SP** :: If `in1` affects SP through an addressing mode `RelSpPop`, SP is adjusted.
3. **Fetch `op2` from `in2`** :: Fetch operand `op2` from `in2`. It may only use registers, therefore does not affect SP.
4. **Resolve `out`** :: Resolve location of `out`. It uses a full addressing mode, therefore the destination may be register, stack, it can be addressed relatively to GPR and so on.
5. **Adjust SP again** :: If `out` affects SP through an addressing mode `RelSpPush`, SP is adjusted.
6. **Account for `swap`** :: If `swap` modifier is set, operands are swapped, i.e. `op1` becomes `op2`, and `op2` becomes `op1`. This allows e.g. subtracting a stack memory value from register: `sub r1, stack[0], swap=true`
7. **Compute result and new flags** :: Apply `F(op1, op2)` to compute `result` value and new flags state `flags_candidate`.
8. **Commit or discard new flags** :: If `set_flags` modifier is set, flags are set according to `flags_candidate`; otherwise all flags are preserved and `flags_candidate` is discarded.
9. **Store result**:: Write `result` to a location resolved on step 4.

>>

See [RelSpPop], [RelSpPush], [step].
 *)
Inductive binop_effect: execution_stack -> regs_state -> pages -> flags_state ->
                        in_any -> in_reg -> out_any ->
                        mod_swap -> mod_set_flags ->
                        forall F: word_type -> word_type -> (word_type * flags_state),
                        (execution_stack * regs_state * pages * flags_state) -> Prop :=
| be_apply:
  forall f ef0 ef1 ef' regs regs' mm mm' (in1: in_any) (in2:regonly) (out: out_any) loc1 loc2
    op1 op2 op1' op2' swap set_flags out_loc result flags_candidate flags0 new_flags tag1 tag2,
    resolve ef0 regs in1 loc1 ->
    resolve_effect__in in1 ef0 ef1 ->
    resolve ef1 regs in2 loc2 ->
    resolve ef1 regs out out_loc ->
    resolve_effect__out out ef1 ef' ->
    fetch_loc regs ef' mm loc1 (FetchPV (mk_pv tag1 op1)) ->
    fetch_loc regs ef' mm loc2 (FetchPV (mk_pv tag2 op2)) ->
    apply_swap swap op1 op2 = (op1', op2') -> (* [op1', op2'] are [op1,op2] or [op2,op1] depending on swap modifier value. *)
    f op1' op2' = (result, flags_candidate) ->
    store_loc regs ef' mm (IntValue result) out_loc (regs', mm') ->
    new_flags = apply_set_flags set_flags flags0 flags_candidate ->
    binop_effect ef0 regs mm flags0 in1 in2 out swap set_flags f (ef', regs', mm', new_flags).

Inductive binop_state_effect: in_any -> in_any -> out_any -> mod_swap -> mod_set_flags ->
                      (word_type -> word_type -> (word_type * flags_state)) ->
                      smallstep :=
| be_apply_step:
  forall f xstack new_xstack context_u128 regs new_regs pages new_pages depot (in1: in_any) (in2: in_reg) (out: out_any) swap set_flags flags new_flags codes,
    let gs := {|
          gs_flags        := flags;
          gs_callstack    := xstack;
          gs_regs         := regs;
          gs_context_u128 := context_u128;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_contracts    := codes;
          |}  in
    binop_effect xstack regs pages flags in1 in2 out swap set_flags f (new_xstack, new_regs, new_pages, new_flags) ->
    binop_state_effect
      in1 in2 out swap set_flags f gs
      {|
        gs_flags        := new_flags;
        gs_callstack    := new_xstack;
        gs_regs         := new_regs;
        gs_context_u128 := context_u128;
        gs_pages        := new_pages;
        gs_depot        := depot;
        gs_contracts    := codes;
      |}
.

Inductive step: instruction -> smallstep :=
(**
<<
## Add

### Syntax

- `add in1, in2, out`
- `add.s in1, in2, out`, to set `swap` modifier.
- `add! in1, in2, out`, to set `set flags` modifier.
- `add.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Unsigned overflowing addition of two numbers modulo $2^{256}$.

### Semantic

>>
Follows the scheme described in [binop_effect].
<<
Its parameter $F(op_1, op_2)$ is a function that acts as follows:

- result is computed by unsigned addition of two numbers with overflow modulo $2^{256}$.

   $$result := op_1 + op_2 \mod 2^{256}$$

- flags are computed as follows:
   - `LT_OF` is set if overflow occurs, i.e. $op_1 + op_2 \geq 2^{256}$
   - `EQ` is set if $result = 0$.
   - `GT` is set if $op_1 \gt op_2$. An equivalent condition is: both `LT_OF` and `EQ` are cleared.

Reminder: flags are only set if `set_flags` modifier is set.

### Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.
- flags, if `set_flags` modifier is set.

### Usage

Arithmetic operations.

### Similar instructions

Flags are computed exactly as in `sub`, but the meaning of overflow is different for addition and subtraction.
>>
*)
| step_Add:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_state_effect in1 in2 out mod_swap mod_sf
      (fun x y =>
         let (result, NEW_OF) := x + y in
         let NEW_EQ := EQ_of_bool (result == zero256) in
         let NEW_GT := GT_of_bool (negb NEW_EQ && negb NEW_OF) in
         (result, mk_fs (OF_LT_of_bool NEW_OF) NEW_EQ NEW_GT))
      gs gs' ->

    step (OpAdd in1 in2 out mod_swap mod_sf) gs gs'
(**
<<
## Sub

### Syntax

- `sub in1, in2, out`
- `sub.s in1, in2, out`, to set `swap` modifier.
- `sub! in1, in2, out`, to set `set flags` modifier.
- `sub.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Unsigned overflowing subtraction of two numbers modulo $2^{256}$.

### Semantic

>>
Follows the scheme described in [binop_effect].
<<
Its parameter $F(op_1, op_2)$ is a function that acts as follows:

- result is computed by unsigned subtraction of two numbers with overflow modulo $2^{256}$.

   $$result := \begin{cases}op_1 - op_2 & , \text{if}\  op_1 \geq op_2\\ 2^{256} -  (op_2 - op_1) &, \text{if}\ op_1 \lt op_2\end{cases}$$

- flags are computed as follows:
   - `LT_OF` is set if overflow occurs, i.e. $op_1 \lt op_2$
   - `EQ` is set if $result = 0$.
   - `GT` is set if $op_1 \gt op_2$. An equivalent condition is: both `LT_OF` and `EQ` are cleared.

Reminder: flags are only set if `set_flags` modifier is set.

### Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.
- flags, if `set_flags` modifier is set.

### Usage

Arithmetic operations.

### Similar instructions

Flags are computed exactly as in `sub`, but the meaning of overflow is different for addition and subtraction.
>>
*)
| step_Sub:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_state_effect in1 in2 out mod_swap mod_sf
      (fun x y =>
         let (result, NEW_OF) := x - y in
         let NEW_EQ := EQ_of_bool (result == zero256) in
         let NEW_GT := GT_of_bool (negb NEW_EQ && negb NEW_OF) in
         (result, mk_fs (OF_LT_of_bool NEW_OF) NEW_EQ NEW_GT))
      gs gs' ->

    step (OpSub in1 in2 out mod_swap mod_sf) gs gs'

(**
<<
## And

### Syntax

- `and in1, in2, out`
- `and.s in1, in2, out`, to set `swap` modifier.
- `and! in1, in2, out`, to set `set flags` modifier.
- `and.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Bitwise AND of two 256-bit numbers.

### Semantic

>>
Follows the scheme described in [binop_effect].
<<
Its parameter $F(op_1, op_2)$ is a function that acts as follows:

- result is computed as a bitwise AND of two operands. 
- flags are computed as follows:
   - `EQ` is set if $result = 0$.
   - `OF_LT` and `GT` are cleared

Reminder: flags are only set if `set_flags` modifier is set.

### Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.
- flags, if `set_flags` modifier is set.

### Usage

- operations with bit masks

### Similar instructions

- `and`, `or` and `xor` are encoded as variants of the same instruction.
>>
*)

| step_And:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_state_effect in1 in2 out mod_swap mod_sf
      (fun x y => let result := bitwise_and _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
      gs gs' ->
    step (OpAnd in1 in2 out mod_swap mod_sf) gs gs'
 (**
<<
## OR

### Syntax

- `or in1, in2, out`
- `or.s in1, in2, out`, to set `swap` modifier.
- `or! in1, in2, out`, to set `set flags` modifier.
- `or.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Bitwise OR of two 256-bit numbers.

### Semantic

>>
Follows the scheme described in [binop_effect].
<<
Its parameter $F(op_1, op_2)$ is a function that acts as follows:

- result is computed as a bitwise OR of two operands. 
- flags are computed as follows:
   - `EQ` is set if $result = 0$.
   - `OF_LT` and `GT` are cleared

Reminder: flags are only set if `set_flags` modifier is set.

### Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.
- flags, if `set_flags` modifier is set.

### Usage

- operations with bit masks

### Similar instructions

- `and`, `or` and `xor` are encoded as variants of the same instruction.
>>
*)   
| step_Or:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_state_effect in1 in2 out mod_swap mod_sf
      (fun x y => let result := bitwise_or _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
      gs gs' ->

    step (OpOr in1 in2 out mod_swap mod_sf) gs gs'

(**
<<
## XOR

### Syntax

- `or in1, in2, out`
- `or.s in1, in2, out`, to set `swap` modifier.
- `or! in1, in2, out`, to set `set flags` modifier.
- `or.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Bitwise XOR of two 256-bit numbers.

### Semantic

>>
Follows the scheme described in [binop_effect].
<<
Its parameter $F(op_1, op_2)$ is a function that acts as follows:

- result is computed as a bitwise XOR of two operands. 
- flags are computed as follows:
   - `EQ` is set if $result = 0$.
   - `OF_LT` and `GT` are cleared

Reminder: flags are only set if `set_flags` modifier is set.

### Affected parts of VM state

- execution stack: PC, as by any instruction; SP, if `in1` uses `RelPop` addressing mode, or if `out` uses `RelPush` addressing mode.
- Current stack memory page, if `out` resolves to it.
- GPRs, if `out` resolves to a register.
- flags, if `set_flags` modifier is set.

### Usage

- operations with bit masks

### Similar instructions

- `and`, `or` and `xor` are encoded as variants of the same instruction.
>>
*)
         
| step_Xor:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs',

    binop_state_effect in1 in2 out mod_swap mod_sf
      (fun x y => let result := bitwise_xor _ x y in (result, (mk_fs Clear_OF_LT (EQ_of_bool (result == zero256)) Clear_GT)))
      gs gs' ->

    step (OpXor in1 in2 out mod_swap mod_sf) gs gs'
.
