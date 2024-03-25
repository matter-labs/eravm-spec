From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing ABI Bool Coder Core Common Predication Ergs CallStack TransientMemory MemoryOps isa.CoreSet State
  Addressing.Coercions PrimitiveValue SemanticCommon RecordSetNotations ABI.MetaParametersABI.

Section ContractDefinitions.
(** {{{!
describe(InstructionDoc(

ins=Instruction("OpContractThis", "this", out1=Out.Reg),

legacy = """```
context.this out
```
""",

summary = """
Retrieves the address of the currently executed contract.
""",

semantic = r"""
- Fetch the address of the currently executed contract
from the active external frame.
- Widen the address to [%word_bits], zero-extended, and write to register `out`.
""",

usage = """
- On [%OpDelegateCall] this address is preserved to be one of the caller.
See [%select_this_address].
""",

similar = """
- See [%OpContractCaller], [%OpContractCodeAddress].
"""
))
}}}
 *)
Inductive step_contract: instruction -> smallstep :=

| step_ContractThis:
  forall this_addr (this_addr_word:word) (s1 s2: state),

    this_addr = ecf_this_address (active_extframe (gs_callstack s1)) ->
    this_addr_word = widen word_bits this_addr ->


    step_contract (OpContractThis (IntValue this_addr_word)) s1 s2
(** {{{!
describe(InstructionDoc(

ins=Instruction("OpContractCaller", "par", out1=Out.Reg),

legacy = """```
context.caller out
```
""",
summary = """
Retrieves the address of the contract which has called the currently executed contract.
""",

semantic = """
- Fetch the address of the currently executed contract from the active external frame.
- Widen address is widened to [%word_bits], zero-extended, and written to register `out`.
""",

usage = """
On [%OpDelegateCall] this address is preserved to be the caller of the caller.
See [%select_sender].
""",

similar = """
- See [%OpContractThis], [%OpContractCodeAddress].
"""
))
}}} *)
| step_ContractCaller:
  forall sender_addr sender_addr_word (s1 s2:state),
    sender_addr = (active_extframe (gs_callstack s1)).(ecf_msg_sender) ->
    sender_addr_word = widen word_bits sender_addr ->

    step_contract (OpContractCaller (IntValue sender_addr_word)) s1 s2
(** {{{!
describe(InstructionDoc(

ins=Instruction("OpContractCodeAddress", "code", out1=Out.Reg),

legacy = """```
context.code_source out
```
""",
summary = """
Retrieves the address of the contract code that is actually being executed.
""",

semantic = r"""
- Fetch the contract address of the currently executed code from the active external frame.
- Widen the address to [%word_bits], zero-extended, and write to register `out`.
""",

usage = """
- In the execution frame created by [%OpDelegateCall] this will be the address of the contract that was called by [%OpDelegateCall].
- Necessary to implement Solidity’s `immutable` under [%OpDelegateCall].
""",

similar = """
- See [%OpContractThis], [%OpContractCaller].
"""
))
}}}
 *)
| step_ContractCodeAddress:
  forall code_addr code_addr_word (s1 s2:state),
    code_addr = ecf_code_address (active_extframe (gs_callstack s1)) ->
    code_addr_word = widen word_bits code_addr ->
    step_contract (OpContractCodeAddress (IntValue code_addr_word)) s1 s2.

End ContractDefinitions.
