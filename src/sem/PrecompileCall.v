From RecordUpdate Require Import RecordSet.

Require SemanticCommon Precompiles.

Import Addressing ABI Bool Common Coder Predication Ergs CallStack Event Memory MemoryOps Instruction State ZMod
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations MetaParameters.
Import ZArith List ListNotations.

Section Def.
  Open Scope ZMod_scope.
  Inductive step_precompile: instruction -> smallstep :=
  | step_PrecompileCall_unaffordable:
    forall flags pages cs regs (arg_params arg_extra_ergs: in_reg) (arg_dest: out_reg)
      new_regs params extra_ergs __ ___ s1 s2,

      load_regs regs [
          (arg_params, mk_pv __ params);
          (arg_extra_ergs, mk_pv ___ extra_ergs)
        ] ->

      let cost := resize _ ergs_bits extra_ergs in
      affordable cs cost = false ->

      store_reg regs arg_dest (IntValue zero256) new_regs ->
      step_xstate_only
        {|
          gs_regs         := regs;
          gs_callstack    := cs;

          gs_flags        := flags;
          gs_pages        := pages;
        |}
        {|
          gs_regs         := new_regs;
          gs_callstack    := ergs_reset cs;

          gs_flags        := flags;
          gs_pages        := pages;
        |} s1 s2 ->
      step_precompile (OpPrecompileCall arg_params arg_extra_ergs) s1 s2

  | step_PrecompileCall_affordable:
    forall flags pages cs regs (arg_params arg_extra_ergs: in_reg) (arg_dest: out_reg)
      regs1 new_cs ext_params enc_params extra_ergs gs new_gs context_u128 __ ___ new_xs,
      let heap_id := active_heap_id cs in

      load_regs regs [
          (arg_params, mk_pv __ enc_params);
          (arg_extra_ergs, mk_pv ___ extra_ergs)
        ] ->

      let cost := resize _ ergs_bits extra_ergs in

      pay cost cs new_cs ->
      store_reg regs arg_dest (IntValue one256) regs1 ->

      PrecompileParameters.pub_ABI.(decode) enc_params = Some ext_params ->
      let in_params := PrecompileParameters.to_inner heap_id heap_id ext_params in

      let xs := {|
                     gs_callstack    := new_cs;

                     gs_regs         := regs;
                     gs_pages        := pages;
                     gs_flags        := flags;
                   |} in
      Precompiles.precompile_processor (current_contract cs) in_params
        xs
        new_xs ->

      emit_event (PrecompileQuery {|
                      q_contract_address := current_contract cs;
                      q_tx_number_in_block := gs_tx_number_in_block gs;
                      q_shard_id := current_shard cs;
                      q_key := in_params;
                    |}) gs new_gs ->
      step_precompile (OpPrecompileCall arg_params arg_extra_ergs) {|
                        gs_xstate := {|
                                      gs_regs         := regs;
                                      gs_pages        := pages;
                                      gs_callstack    := cs;
                                      gs_flags        := flags;
                                    |};
                        gs_global       := gs;

                        gs_context_u128 := context_u128;
                      |}
                      {|
                        gs_xstate       := new_xs;
                        gs_global       := new_gs;

                        gs_context_u128 := context_u128;
                      |}
  .

End Def.
