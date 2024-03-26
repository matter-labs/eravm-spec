From RecordUpdate Require Import RecordSet.

Require SemanticCommon Precompiles.

Import Addressing ABI Bool Common Coder Predication Ergs CallStack Event TransientMemory MemoryOps isa.CoreSet State
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations PrecompileParametersABI.

Section PrecompileCallDefinition.
  Open Scope ZMod_scope.
  Import ssreflect.tuple ssreflect.eqtype.
(** {{{!
describe(InstructionDoc(

ins=Instruction(
"",
"",
in1 = In.Reg,
in2 = In.Reg,
out1=Out.Reg,
kernelOnly = True,
notStatic = False),

legacy = " `log.precompile in1, in2, out1`",
preamble = None,

summary = """

A precompile call is a call to an extension of a virtual machine. The extension
operates differently depending on the currently executing contract's address.
Only system contracts may have precompiles.
""",

semantic = r"""
Attempt to pay the extra cost:

   $$\mathit{cost_{extra}} = \mathit{in}_2 \mod 2^{32}$$

- If the cost is affordable:
  + pay $\mathit{cost_{extra}}$
  + execute the precompile logic associated to the currently executing contract.
    This will emit a special event.
  + set ${out}_1$ to one.

- If the cost is unaffordable, do not pay anything beyound [%base_cost] of this
  instruciton. Set ${out}_1$ to zero.
""",
affectedState = "",
usage = """ """,
similar = ""
))
}}}
*)
  Inductive step_precompile: instruction -> smallstep :=
  | step_PrecompileCall_affordable:
    forall flags pages cs regs result new_cs extra_ergs gs new_gs ctx ___1 new_xs params,
      let heap_id := active_heap_id cs in


      let cost := low ergs_bits extra_ergs in

      pay cost cs new_cs ->
      result = one256 ->

      let xs := {|
                     gs_callstack    := new_cs;

                     gs_regs         := regs;
                     gs_pages        := pages;
                     gs_flags        := flags;
                     gs_context_u128 := ctx;
                     gs_status       := NoPanic;
                   |} in
      Precompiles.precompile_processor (current_contract cs) params xs new_xs ->

      emit_event (PrecompileQuery {|
                      q_contract_address := current_contract cs;
                      q_tx_number_in_block := gs_tx_number_in_block gs;
                      q_shard_id := current_shard cs;
                      q_key := params;
                    |}) gs new_gs ->
      step_precompile (OpPrecompileCall (Some (IntValue params)) (mk_pv ___1 extra_ergs) (IntValue result))
                      {|
                        gs_transient := {|
                                      gs_regs         := regs;
                                      gs_pages        := pages;
                                      gs_callstack    := cs;
                                      gs_flags        := flags;
                                      gs_context_u128 := ctx;
                                      gs_status       := NoPanic;
                                    |};
                        gs_global       := gs;

                      |}
                      {|
                        gs_transient    := new_xs;
                        gs_global       := new_gs;
                      |}
  | step_PrecompileCall_unaffordable:
    forall flags pages cs regs extra_ergs ___1 ___2 s1 s2 result ctx,
      let cost := low ergs_bits extra_ergs in
      affordable cs cost = false ->

      result = zero256 ->
      step_transient_only
        {|
          gs_callstack    := cs;

          gs_regs         := regs;
          gs_flags        := flags;
          gs_pages        := pages;
          gs_context_u128 := ctx;
          gs_status       := NoPanic;
        |}
        {|
          gs_callstack    := ergs_reset cs;

          gs_regs         := regs;
          gs_flags        := flags;
          gs_pages        := pages;
          gs_context_u128 := ctx;
          gs_status       := NoPanic;
        |} s1 s2 ->
      step_precompile (OpPrecompileCall ___2 (mk_pv ___1 extra_ergs) (IntValue result)) s1 s2
.

End PrecompileCallDefinition.
