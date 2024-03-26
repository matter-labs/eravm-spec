Require SemanticCommon.

Import ABI Bool Coder Core Common Predication Ergs CallStack TransientMemory MemoryOps isa.CoreSet State
  Addressing.Coercions PrimitiveValue SemanticCommon.

Section IncrementTxDefinition.

Inductive step_increment_tx: @instruction bound -> smallstep :=
  (** {{{!
describe(InstructionDoc(

ins=Instruction("OpIncrementTxNumber", "inctx", kernelOnly = True, notStatic = True ),
legacy = " `context.inc_tx_num`",

summary = """
- Reset all transient storage.
- Increment the tx number counter in [%gs_tx_number_in_block].
""",

semantic = r"""
TODO
""",

usage = """ Utility in system contracts. """,
affectedState = """
- Tx counter.
- Transient storages.
""",

))
}}}
 *)
(* FIXME: clear transient storage *)
| step_IncrementTx:
  forall transient gs new_gs,
    global_state_increment_tx tx_inc gs new_gs ->
    step_increment_tx OpIncrementTxNumber
         {|
           gs_transient    := transient;
           gs_global       := gs;
         |}
         {|
           gs_transient    := transient;
           gs_global       := new_gs;
         |}
.

End IncrementTxDefinition.
