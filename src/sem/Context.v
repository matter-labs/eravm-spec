From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Coder Core Common Predication Ergs CallStack TransientMemory MemoryOps isa.CoreSet State
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations ABI.MetaParametersABI.

Section ContextDefinitions.

Inductive step_context: instruction -> smallstep :=
(** {{{!
describe(InstructionDoc(

ins=Instruction("OpGetCapturedContext", "ldvl", out1=Out.Reg),
legacy = """```
context.get_context_u128 out
```
""",

summary = """
Retrieves current captured context value from the active external frame.

Does not interact with the context register.
""",

semantic = r"""
- Fetch the current context value from the active external frame.
- Widen the context value from 128 bits to [%word_bits], zero-extended, and write to `out`.
""",

usage = """
- See [%gs_context_u128], [%ecf_context_u128_value].
""",

similar = """
- Farcalls capture context. See [%OpFarCall], [%OpMimicCall], [%OpDelegateCall].
- [%OpSetContextReg] to set context register, from where the value is captured by farcalls.
"""
))
}}}
 *)
| step_GetCapturedContext:
  forall wcontext (s1 s2: state),
    wcontext = widen word_bits (gs_context_u128 s1) ->
    step_context (OpGetCapturedContext (IntValue wcontext)) s1 s2
(** {{{!
describe(InstructionDoc(

ins=Instruction("OpSetContextReg", "stvl", in1=In.Reg, kernelOnly = True, notStatic = True),

legacy = """```
context.set_context_u128 in
```
""",

summary = """
Sets context register.

Does not interact with the captured context value in the active external frame.
""",

semantic = """
- Fetch the value from `out` and narrow it to 128 bits.
- Store the shrunk value in the context register [%gs_context_u128].
""",

usage = """
- See [%gs_context_u128], [%ecf_context_u128_value].
""",

similar = f"""
- Farcalls capture context. See {FARCALLS}.
- [%OpGetCapturedContext] to retrieve a captured context value.
"""
))
}}}

 *)
| step_SetContextReg:
  forall (new_context256 :word) any_tag (new_context_u128:u128) xs1 xs2 s1 s2,
    new_context_u128 = low 128 new_context256->
    xs2 = xs1 <| gs_context_u128 := new_context_u128 |> ->
    step_transient_only xs1 xs2 s1 s2 ->

    step_context (OpSetContextReg (mk_pv any_tag new_context256)) s1 s2.
End ContextDefinitions.
