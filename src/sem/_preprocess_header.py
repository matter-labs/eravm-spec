
RETS = ", ".join(map(lambda s: f"[%Op{s}]", ["Ret", "NearPanicTo", "NearRevertTo", "NearRetTo"]))
FARCALLS = ", ".join(map(lambda s: f"[%Op{s}Call]", ["Far", "Mimic", "Delegate"]))
BITWISE = ", ".join(map(lambda s: f"[%Op{s}]", ["Shr", "Shl", "Rol", "Ror", "And", "Or", "Xor"]))
CALLS = "[%OpNearCall], " + FARCALLS
INSNS_WORKING_WITH_HEAPS = "[%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc]"
PTR_MANIPULATION = ", ".join(["[%OpPtrAdd]", "[%OpPtrSub]", "[%OpPtrShrink]", "[%OpPtrPack]"])

INSNS_USE_REGIMM = "[%OpLoad], [%OpLoadInc], [%OpStore], [%OpStoreInc], [%OpLoadPointer], [%OpLoadPointerInc], [%OpStaticReadInc], [%OpStaticRead], [%OpStaticWrite], [%OpStaticWriteInc]"


USES_REGIMM = f"""
- One of few instructions that accept only reg or imm operand but do not have
  full addressing mode, therefore can't e.g. address stack. The full list is:
  {INSNS_USE_REGIMM}.
"""

RET_LEGACY= ["`ret in1`",
"`ret` is an alias for `ret r1`",
"`ret.ok in1` aliased as `ret in1`"
]


REVERT_LEGACY= [
   "`revert` is an alias for `revert r1`",
"`ret.revert in1`"
]

def heap_var_op_syntax(ins):
   return syntax(ins) + [
f"`{ins.mnemonic}.h` to access heap (default)",
f"`{ins.mnemonic}.ah` to access auxheap",
f"`{ins.mnemonic}.st` to access static memory page"
]

def NEAR_FAR_RET_LIKE_PREAMBLE(near_descr, near_section, far_descr, far_section):
   return f"""
The {near_descr} and {far_descr} share the same syntax, but their runtime
semantic is different:

- if the topmost frame in callstack is [%ExternalCall], the {far_descr} semantic is
  selected (see [%{far_section}]);
- if the topmost frame in callstack is [%InternalCall], the {near_descr} semantic is
  selected (see [%{near_section}]).
"""

def ins_arith(abstract_name: str, mnemonic:str, hasOut2 = False, commutes=False):
   return Instruction(
      mnemonic = mnemonic,
      abstract_name = abstract_name,
      modifiers = ([Modifier.Swap] if not commutes else []) + [Modifier.SetFlags],
      in1 = In.Any,
      in2 = In.Reg,
      out1 = Out.Any,
      out2 = Out.Reg if hasOut2 else None
   )

def ins_affected_args(in1:Optional[In], out1: Optional[Out],hasSetFlags = False)->str:
   result =  """"""
   if out1 == Out.Reg:
      result += """
- GPRs, because `out` resolves to a register. """
   elif out1:
      result += """
- GPRs, if `out` resolves to a register. """

   result += """
- Execution stack:
   - PC, as by any instruction """
   if in1 == In.Any or out1 == Out.Any:
      result += """
   - SP, if `in1` uses [%RelSpPop] addressing mode, or if `out1` uses
     [%RelSpPush] addressing mode. """
   if out1 == Out.Any:
      result += """
- Current stack memory page, if `out` resolves to it. """
   if hasSetFlags:
      result += """
- Flags, if `set_flags` modifier is set. """
   return result


def ins_affected(ins:Instruction):
   return ins_affected_args(ins.in1, ins.out1, ins.setFlags())


def descr_ins_generic_bitwise(abstract_name: str, mnemonic:str, commutes=False, summary: Optional[str] = None, semantic: Optional[str] = None, usage : Optional[str] = None):
   return InstructionDoc(
      ins=ins_arith(abstract_name, mnemonic, commutes=commutes),

      summary = f"""
Bitwise {mnemonic.upper()} of two 256-bit numbers.
      """,

      semantic = f"""
- $result$ is computed as a bitwise {mnemonic.upper()} of two operands.
- flags are computed as follows:
   - `EQ` is set if $result = 0$.
   - `OF_LT` and `GT` are cleared
      """ if not semantic else semantic,

      usage = "- Operations with bit masks." if not usage else usage,

      similar = f"- See {BITWISE}."
      )


def summary_header(ins:Instruction ):
   return ""

def summary_footer(ins: Instruction ):
   result = ""
   if ins.kernelOnly :
      result += "- Requires [%KernelMode]\n"
   if ins.notStatic:
      result += "- Forbidden in [%StaticMode]\n"
   return result

def semantic_header(ins: Instruction ):
   result = ""
   if ins.swap():
      result += """**Note**: In the following description the operands are bound after
taking [%mod_swap] modifier into account. \n"""
   return result

def semantic_footer(ins: Instruction):
  result = ""
  if ins.setFlags():
     result += """Reminder: flags are affected only if [%mod_set_flags] is set.\n"""
  return result

def sec_semantic(content: str, ins:Instruction ):
   return "## Semantic\n" + semantic_header(ins) + content + semantic_footer(ins)



def describe(descr:InstructionDoc):
   ins = descr.ins
   sec_abstract_syntax_content = f"[%{abstract_syntax(ins)}]" if not descr.abstract_syntax else descr.abstract_syntax
   sec_legacy_syntax = f"## Legacy syntax\n\n{bullets(descr.legacy)}\n" if descr.legacy else ""
   sec_similar = f"## Related instructions\n\n{descr.similar} " if descr.similar else ""
   sec_syntax_content = bullets(syntax(ins) if not descr.syntax_override else descr.syntax_override)
   preamble_content = descr.preamble if descr.preamble else ""
   return f"""
# {ins.abstract_name} {descr.add_to_title}

{preamble_content}
## Abstract Syntax

{sec_abstract_syntax_content}


## Syntax

{sec_syntax_content}

{sec_legacy_syntax}

## Summary

{summary_header(ins)}

{descr.summary}

{summary_footer(ins)}

## Semantic

{semantic_header(ins)}

{descr.semantic}

{semantic_footer(ins)}

## Affected parts of the state

{ins_affected(ins)}

{descr.affectedState}

## Usage

{descr.usage}

{sec_similar}
"""
