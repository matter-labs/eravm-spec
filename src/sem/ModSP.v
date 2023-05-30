Require SemanticCommon.

Import MemoryOps Instruction State SemanticCommon.
(**
<<
## ModSP

>>
Performs no operations with memory, but may adjust SP using address modes
[RelSpPop] and [RelSPPush].
*)

Inductive step : instruction -> smallstep :=
| step_ModSP:
  forall codes flags depot pages xstack0 xstack1 new_xstack context_u128 in1 out1 regs,
    resolve_effect__in in1 xstack0 xstack1 ->
    resolve_effect__out out1 xstack1 new_xstack ->
    step (OpModSP in1 out1)
          {|
          gs_callstack    := xstack0;


          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
          |}
          {|
          gs_callstack    := new_xstack;


          gs_flags        := flags;
          gs_regs         := regs;
          gs_pages        := pages;
          gs_depot        := depot;
          gs_context_u128 := context_u128;
          gs_contracts    := codes;
          |}
.
