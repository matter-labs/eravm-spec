From RecordUpdate Require Import RecordSet.
Require  sem.SemanticCommon.

Import Addressing Bool ZArith Common Condition Instruction CallStack Memory MemoryOps State ZMod
  ZBits Addressing.Coercions RecordSetNotations SemanticCommon.
(**
# Binary operations

##  Common binary operation semantic

The predicate [binop_effect] describes a scheme of operation shared by binary operations:

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


See [RelSpPop], [RelSpPush], [step].
 *)

Definition binop_eval := word -> word -> (word * flags_state).
Inductive binop_effect: (regs_state * callstack * pages * flags_state) ->
                        in_any -> in_reg -> out_any ->
                        mod_swap -> mod_set_flags ->
                        binop_eval ->
                        (regs_state * callstack * pages * flags_state) -> Prop :=
| be_apply:
  forall f xstack new_xstack regs new_regs pages new_pages (in1: in_any) (in2:in_reg) (out: out_any) 
    op1 op2 swap set_flags result flags_candidate flags0 new_flags tag1 tag2,

    fetch_apply2_swap swap (regs, xstack, pages) in1 in2 out (mk_pv tag1 op1) (mk_pv tag2 op2) (IntValue result) (new_regs, new_xstack, new_pages) ->
    f op1 op2 = (result, flags_candidate) ->
    new_flags = apply_set_flags set_flags flags0 flags_candidate ->
    binop_effect (regs, xstack, pages, flags0) in1 in2 out swap set_flags f (new_regs, new_xstack, new_pages, new_flags).


Definition binop_spec := primitive_value -> primitive_value -> primitive_value * flags_state.
Inductive binop_effect_spec: (regs_state * callstack * pages * flags_state) ->
                        in_any -> in_reg -> out_any ->
                        mod_swap -> mod_set_flags ->
                        primitive_value -> primitive_value -> primitive_value -> flags_state ->
                        (regs_state * callstack * pages * flags_state) -> Prop :=
| bes_apply:
  forall xstack new_xstack regs new_regs pages new_pages (in1: in_any) (in2:in_reg) (out: out_any) 
    op1 op2 swap set_flags result flags_candidate flags0 new_flags ,

    fetch_apply2_swap swap (regs, xstack, pages) in1 in2 out op1 op2 result (new_regs, new_xstack, new_pages) ->
    new_flags = apply_set_flags set_flags flags0 flags_candidate ->
    binop_effect_spec (regs, xstack, pages, flags0) in1 in2 out swap set_flags
                 op1 op2 result flags_candidate
      (new_regs, new_xstack, new_pages, new_flags).


Inductive binop_state_effect: in_any -> in_any -> out_any -> mod_swap -> mod_set_flags ->
                      binop_eval ->
                      smallstep :=
| be_apply_step:
  forall f xstack new_xstack context_u128 regs new_regs pages new_pages (in1: in_any) (in2: in_reg) (out: out_any) swap set_flags flags new_flags gs,
    let gs := {|
          gs_flags        := flags;
          gs_callstack    := xstack;
          gs_regs         := regs;
          gs_context_u128 := context_u128;
          gs_pages        := pages;
          
          gs_global       := gs;
          |}  in
    binop_effect (regs, xstack, pages, flags) in1 in2 out swap set_flags f (new_regs, new_xstack, new_pages, new_flags) ->
    binop_state_effect
      in1 in2 out swap set_flags f gs
      {|
        gs_flags        := new_flags;
        gs_callstack    := new_xstack;
        gs_regs         := new_regs;
        gs_context_u128 := context_u128;
        gs_pages        := new_pages;
        
        gs_global       := gs;
      |}
.
Inductive binop_state_effect_spec: in_any -> in_any -> out_any -> mod_swap -> mod_set_flags ->
                                   primitive_value -> primitive_value -> primitive_value -> flags_state ->
                      smallstep :=
| bes_apply_step:
  forall xstack new_xstack context_u128 regs new_regs pages new_pages (in1: in_any) (in2: in_reg) (out: out_any) swap set_flags new_flags gs op1 op2 result flags,
    let gs := {|
          gs_flags        := flags;
          gs_callstack    := xstack;
          gs_regs         := regs;
          gs_context_u128 := context_u128;
          gs_pages        := pages;
          
          gs_global       := gs;
          |}  in
    binop_effect_spec (regs, xstack, pages, flags) in1 in2 out swap set_flags
                      op1 op2 result flags 
      (new_regs, new_xstack, new_pages, new_flags) ->
    binop_state_effect_spec
      in1 in2 out swap set_flags op1 op2 result flags gs
      {|
        gs_flags        := new_flags;
        gs_callstack    := new_xstack;
        gs_regs         := new_regs;
        gs_context_u128 := context_u128;
        gs_pages        := new_pages;
        
        gs_global       := gs;
      |}
.

Inductive binop_state_bitwise_effect:
in_any -> in_any -> out_any -> mod_swap -> mod_set_flags ->
                      (word -> word -> word) ->
                      smallstep :=
| bsee_apply:
  forall (bitwise_op: word -> word -> word) (in1: in_any) (in2:in_reg) (out: out_any) swap set_flags
    old_state new_state,
    binop_state_effect  in1 in2 out swap set_flags 
      (fun x y =>
         let result := bitwise_op x y in
         (result, bflags false (result == zero256) false))
      old_state new_state ->
    
    binop_state_bitwise_effect in1 in2 out swap set_flags bitwise_op old_state new_state.

Inductive binop_state_bitwise_effect_spec:
in_any -> in_any -> out_any -> mod_swap -> mod_set_flags ->
primitive_value -> primitive_value -> primitive_value -> 
                      smallstep :=
| bseec_apply:
  forall  (in1: in_any) (in2:in_reg) (out: out_any) swap set_flags
    old_state new_state op1 op2 result flags_candidate,
    binop_state_effect_spec in1 in2 out swap set_flags
                            op1 op2 result flags_candidate
                            old_state new_state ->
    
    flags_candidate = bflags false (result.(value) == zero256) false ->
    binop_state_bitwise_effect_spec in1 in2 out swap set_flags op1 op2 result old_state new_state.

Inductive step: instruction -> smallstep :=
(**
## Add

### Abstract Syntax

```
| OpAdd         (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
```

### Syntax

- `add in1, in2, out`
- `add.s in1, in2, out`, to set `swap` modifier.
- `add! in1, in2, out`, to set `set flags` modifier.
- `add.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Unsigned overflowing addition of two numbers modulo $2^{256}$.

### Semantic

Follows the scheme described in [binop_effect].

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

*)
| step_Add:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs' _tag1 _tag2 op1 op2 result flags_candidate new_OF,

    binop_state_effect_spec in1 in2 out mod_swap mod_sf
      (mk_pv _tag1 op1)
      (mk_pv _tag2 op2)
      (IntValue result) flags_candidate
      gs gs' ->

    (result, new_OF) = op1 + op2 ->
    let new_EQ := result == zero256 in
    let new_GT := negb new_EQ && negb new_OF in
    flags_candidate = bflags new_OF new_EQ new_GT ->
    step (OpAdd in1 in2 out mod_swap mod_sf) gs gs'
(**

## Sub

### Abstract Syntax

```
 | OpSub         (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
```

### Syntax

- `sub in1, in2, out`
- `sub.s in1, in2, out`, to set `swap` modifier.
- `sub! in1, in2, out`, to set `set flags` modifier.
- `sub.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Unsigned overflowing subtraction of two numbers modulo $2^{256}$.

### Semantic

Follows the scheme described in [binop_effect].

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

*)
| step_Sub:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out gs gs' _tag1 _tag2 op1 op2 result flags_candidate new_OF,

    binop_state_effect_spec in1 in2 out mod_swap mod_sf
      (mk_pv _tag1 op1)
      (mk_pv _tag2 op2)
      (IntValue result) flags_candidate
      gs gs' ->

    (result, new_OF) = op1 - op2 ->
    let new_EQ := result == zero256 in
    let new_GT := negb new_EQ && negb new_OF in
    flags_candidate = bflags new_OF new_EQ new_GT ->
    step (OpSub in1 in2 out mod_swap mod_sf) gs gs'

(**
## And

### Abstract Syntax

```
 | OpAnd (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
```

### Syntax

- `and in1, in2, out`
- `and.s in1, in2, out`, to set `swap` modifier.
- `and! in1, in2, out`, to set `set flags` modifier.
- `and.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Bitwise AND of two 256-bit numbers.

### Semantic

Follows the scheme described in [binop_effect].

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

*)

| step_And:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out _tag1 _tag2 x y result gs gs',
    binop_state_bitwise_effect_spec in1 in2 out mod_swap mod_sf
      (mk_pv _tag1 x) (mk_pv _tag2 y) (IntValue result)  gs gs' ->
    result = bitwise_and _ x y ->
    step (OpAnd in1 in2 out mod_swap mod_sf) gs gs'
 (**

## OR

### Abstract Syntax

```
 | OpOr (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
```


### Syntax

- `or in1, in2, out`
- `or.s in1, in2, out`, to set `swap` modifier.
- `or! in1, in2, out`, to set `set flags` modifier.
- `or.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Bitwise OR of two 256-bit numbers.

### Semantic


Follows the scheme described in [binop_effect].

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

*)   
| step_Or:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out _tag1 _tag2 x y result gs gs',
    binop_state_bitwise_effect_spec in1 in2 out mod_swap mod_sf
      (mk_pv _tag1 x) (mk_pv _tag2 y) (IntValue result)  gs gs' ->
    result = bitwise_or _ x y ->
    step (OpOr in1 in2 out mod_swap mod_sf) gs gs'

(**

## XOR

### Abstract Syntax

```
 | OpXor (in1: in_any) (in2: in_reg)  (out1: out_any) (swap:mod_swap) (flags:mod_set_flags)
```

### Syntax

- `or in1, in2, out`
- `or.s in1, in2, out`, to set `swap` modifier.
- `or! in1, in2, out`, to set `set flags` modifier.
- `or.s! in1, in2, out`, to set both `swap` and `set flags` modifiers.

### Summary

Bitwise XOR of two 256-bit numbers.

### Semantic


Follows the scheme described in [binop_effect].

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

*)
         
| step_Xor:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out _tag1 _tag2 x y result gs gs',
    binop_state_bitwise_effect_spec in1 in2 out mod_swap mod_sf
      (mk_pv _tag1 x) (mk_pv _tag2 y) (IntValue result)  gs gs' ->
    result = bitwise_xor _ x y ->
    step (OpXor in1 in2 out mod_swap mod_sf) gs gs'
| step_Shl:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out _tag1 _tag2 x y result gs gs',
    binop_state_bitwise_effect_spec in1 in2 out mod_swap mod_sf
      (mk_pv _tag1 x) (mk_pv _tag2 y) (IntValue result)  gs gs' ->
    result = shiftl _ x y ->
    step (OpShl in1 in2 out mod_sf) gs gs'
| step_Shr:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out _tag1 _tag2 x y result gs gs',
    binop_state_bitwise_effect_spec in1 in2 out mod_swap mod_sf
      (mk_pv _tag1 x) (mk_pv _tag2 y) (IntValue result)  gs gs' ->
    result = shiftr _ x y ->
    step (OpShr in1 in2 out mod_sf) gs gs'
| step_Rol:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out _tag1 _tag2 x y result gs gs',
    binop_state_bitwise_effect_spec in1 in2 out mod_swap mod_sf
      (mk_pv _tag1 x) (mk_pv _tag2 y) (IntValue result)  gs gs' ->
    result = rol _ x y ->
    step (OpRol in1 in2 out mod_sf) gs gs'
| step_Ror:
  forall mod_swap mod_sf (in1:in_any) (in2:in_reg) out _tag1 _tag2 x y result gs gs',
    binop_state_bitwise_effect_spec in1 in2 out mod_swap mod_sf
      (mk_pv _tag1 x) (mk_pv _tag2 y) (IntValue result)  gs gs' ->
    result = ror _ x y ->
    step (OpRor in1 in2 out mod_sf) gs gs'.

