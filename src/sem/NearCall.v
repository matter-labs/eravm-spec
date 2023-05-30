From RecordUpdate Require Import RecordSet.
Require SemanticCommon.

Import Common Condition ExecutionStack MemoryOps Instruction State ZMod
  ABI ABI.NearCall Arg Arg.Coercions SemanticCommon.

Inductive step_nearcall : instruction -> smallstep :=
(**
<<
## Near calls

Calls the code inside the current contract space.

>>
 *)
| step_NearCall_pass_some_ergs:
  forall codes flags depot pages xstack0 context_u128 regs (abi_params_op:in_reg) abi_params_value call_addr expt_handler ergs_left passed_ergs,

    resolve_fetch_word regs xstack0 pages abi_params_op abi_params_value ->

    Some passed_ergs = option_map NearCall.nca_get_ergs_passed (NearCall.ABI.(decode) abi_params_value) ->

    passed_ergs <> zero32 ->

    (ergs_left, false) = ergs_remaining xstack0 - passed_ergs  ->

    let new_frame := mk_cf expt_handler (sp_get xstack0) call_addr passed_ergs in
    step_nearcall (OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler))
                  {|
                    gs_flags        := flags;
                    gs_callstack    := xstack0;


                    gs_regs         := regs;
                    gs_pages    := pages;
                    gs_depot     := depot;
                    gs_context_u128 := context_u128;
                    gs_contracts    := codes;
                  |}
                  {|
                    gs_flags        := flags_clear;
                    gs_callstack    := InternalCall new_frame (ergs_set ergs_left xstack0);


                    gs_regs         := regs;
                    gs_pages    := pages;
                    gs_depot     := depot;
                    gs_context_u128 := context_u128;
                    gs_contracts    := codes;
                  |}

| step_NearCall_underflow_pass_all_ergs:
  forall codes flags depot pages xstack0 context_u128 regs (abi_params_op:in_reg) abi_params_value call_addr expt_handler ergs_underflown passed_ergs,
    resolve_fetch_word regs xstack0 pages abi_params_op abi_params_value ->
    Some passed_ergs = option_map NearCall.nca_get_ergs_passed (NearCall.ABI.(decode) abi_params_value) ->
    passed_ergs <> zero32 ->

    (ergs_underflown, true) = ergs_remaining xstack0 - passed_ergs  ->

    let new_frame := mk_cf expt_handler (sp_get xstack0) call_addr (ergs_remaining xstack0) in
    step_nearcall (OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler))
                  {|
                    gs_flags        := flags;
                    gs_callstack    := xstack0;


                    gs_regs         := regs;
                    gs_pages    := pages;
                    gs_depot     := depot;
                    gs_context_u128 := context_u128;
                    gs_contracts    := codes;
                  |}
                  {|
                    gs_flags        := flags_clear;
                    gs_callstack    := InternalCall new_frame (ergs_reset xstack0);


                    gs_regs         := regs;
                    gs_pages    := pages;
                    gs_depot     := depot;
                    gs_context_u128 := context_u128;
                    gs_contracts    := codes;
                  |}

| step_NearCall_pass_all_ergs:
  forall codes flags depot pages xstack0 xstack1 context_u128 regs (abi_params_op:in_reg) abi_params_value call_addr expt_handler,
    resolve_fetch_word regs xstack0 pages abi_params_op abi_params_value ->

    option_map NearCall.nca_get_ergs_passed  (NearCall.ABI.(decode) abi_params_value)= Some zero32 ->

    let new_frame := mk_cf expt_handler (sp_get xstack0) call_addr (ergs_remaining xstack0) in
    step_nearcall (OpNearCall abi_params_op (Imm call_addr) (Imm expt_handler))
                  {|
                    gs_flags        := flags;
                    gs_callstack    := xstack0;


                    gs_regs         := regs;
                    gs_pages    := pages;
                    gs_depot     := depot;
                    gs_context_u128 := context_u128;
                    gs_contracts    := codes;
                  |}

                  {|
                    gs_flags        := flags_clear;
                    gs_callstack    := InternalCall new_frame (ergs_reset xstack1);


                    gs_regs         := regs;
                    gs_pages        := pages;
                    gs_depot        := depot;
                    gs_context_u128 := context_u128;
                    gs_contracts    := codes;
                  |}
.
