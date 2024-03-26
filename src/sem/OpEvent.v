Require SemanticCommon.

Import CallStack Event isa.CoreSet State PrimitiveValue SemanticCommon.
Import ssreflect ssrfun ssrbool ssreflect.eqtype ssreflect.tuple.

Section EventDefinition.
  Inductive step_event: instruction -> smallstep :=
(** {{{!
describe(InstructionDoc(
ins=Instruction(
"OpEvent",
"log",
in1 = In.Reg,
in2 = In.Reg,
modifiers = [Modifier.IsFirst],
kernelOnly = True,
notStatic = True),

syntax_override = [],
legacy = [
"`log.event in1, in2` aliased as `event in1, in2`",
"`log.event.first in1, in2` aliased as `event.i in1, in2`",
],

summary = """
Emit an event with provided key and value. See [%event] for more details on
events system.
""",
usage = "",
semantic = r"""
1. Fetch key and value from `in1` and `in2`.
2. If `is_first` is `true`, mark the event as the first in a chain of events.
3. Emit event.
""",
affectedState = "- Event queue."
))
}}} *)
  | step_Event:
    forall xs is_first _tag1 _tag2
      key value gs new_gs,
      let regs := gs_regs xs in
      let pages := gs_pages xs in
      let xstack := gs_callstack xs in

      emit_event (EventQuery {|
                      ev_shard_id := current_shard xstack;
                      ev_is_first := is_first;
                      ev_tx_number_in_block := gs_tx_number_in_block gs;
                      ev_address := current_contract xstack;
                      ev_key := key;
                      ev_value := value;
                    |}) gs new_gs ->

      step_event (OpEvent (mk_pv _tag1 key) (mk_pv _tag2 value) is_first)
                 {|
                   gs_global       := gs;
                   gs_transient    := xs;
                 |}
                 {|
                   gs_global       := new_gs;
                   gs_transient    := xs;
                 |}.
End EventDefinition.
