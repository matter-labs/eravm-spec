From RecordUpdate Require Import RecordSet.

Require SemanticCommon Precompiles.

Import Addressing ABI Bool Common Coder Predication Ergs CallStack Event Memory MemoryOps isa.CoreSet State ZMod
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations MetaParameters.
Import ZArith List ListNotations.

Section Def.
  Open Scope ZMod_scope.
  Inductive step_precompile: instruction -> smallstep :=
  | step_PrecompileCall_unaffordable:
    forall flags pages cs regs extra_ergs __ ___ s1 s2 result ctx,
      let cost := resize _ ergs_bits extra_ergs in
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
      step_precompile (OpPrecompileCall __ (mk_pv ___ extra_ergs) (IntValue result)) s1 s2
  | step_PrecompileCall_affordable:
    forall flags pages cs regs result new_cs extra_ergs gs new_gs ctx __ ___ new_xs params,
      let heap_id := active_heap_id cs in


      let cost := resize _ ergs_bits extra_ergs in

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
      step_precompile (OpPrecompileCall (Some params, __) (mk_pv ___ extra_ergs) (IntValue result))
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
                        gs_transient       := new_xs;
                        gs_global       := new_gs;
                      |}
  .

End Def.
