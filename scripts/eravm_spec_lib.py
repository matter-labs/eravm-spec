from typing import *
from enum import Enum, auto
from dataclasses import dataclass, field
from copy import copy

class In(Enum):
   Any = auto()
   RegImm = auto()
   Reg = auto()
   Imm = auto()
   def coq(self)-> str:
      match self:
         case In.Any: return "in_any"
         case In.RegImm: return "in_regimm"
         case In.Reg: return "in_reg"
         case In.Imm: return "imm_in"

class Out(Enum):
   Any = auto()
   Reg = auto()
   def coq(self)-> str:
      match self:
         case Out.Any: return "out_any"
         case Out.Reg: return "out_reg"

@dataclass
class Modifier(Enum):
   DataPageType = auto()
   Swap = auto()
   SetFlags = auto()

   def coq(self)-> str:
      match self:
         case Modifier.DataPageType: return "data_page_type"
         case Modifier.Swap: return "mod_swap"
         case Modifier.SetFlags: return "mod_set_flags"

@dataclass
class Instruction():
   abstract_name:str = ""
   mnemonic: str = ""
   modifiers : list[Modifier] = field(default_factory = lambda : [])
   in1: Optional[In] = None
   in2: Optional[In] = None
   out1: Optional[Out] = None
   out2: Optional[Out] = None
   kernelOnly: bool = False
   notStatic: bool = False

   def setFlags(self) -> bool:
      return Modifier.SetFlags in self.modifiers

   def swap(self) -> bool:
      return Modifier.Swap in self.modifiers

ARITH = Instruction(
   modifiers = [Modifier.Swap, Modifier.SetFlags],
   in1 = In.Any,
   in2 = In.Reg,
   out1 = Out.Any,
   out2 = None
)

def abstract_syntax(ins:Instruction):
   result = ins.abstract_name
   if ins.in1:
      result += f" (in1: {ins.in1.coq()})"
   if ins.in2:
      result += f" (in2: {ins.in2.coq()})"
   if ins.out1:
      result += f" (out1: {ins.out1.coq()})"
   if ins.out2:
      result += f" (out2: {ins.out2.coq()})"
   for modifier in ins.modifiers:
        result += f" (_: {modifier.coq()})"
   return result

def syntax(ins:Instruction):
   args = []
   if ins.in1:
      args.append("in1")

   if ins.in2:
      args.append("in2")

   if ins.out1:
      args.append("out1")

   if ins.out2:
      args.append("out2")

   args_str = ", ".join(args)

   result = f"""\n- `{ins.mnemonic} {args_str}`\n"""

   if ins.setFlags():
      result += f"- `{ins.mnemonic}! {args_str}`\n     - to set [%mod_set_flags] modifier\n"

   if ins.swap():
      result += f"- `{ins.mnemonic}.s {args_str}`\n    - to set [%mod_swap] modifier\n"

   if ins.setFlags() and ins.swap():
      result += f"- `{ins.mnemonic}.s! {args_str}`\n   - to set both [%mod_set_flags] and [%mod_swap] modifier\n"

   return result

def ins_arith(abstract_name: str, mnemonic:str, hasOut2 = False):
   result = copy(ARITH)
   result.mnemonic = mnemonic
   result.abstract_name = abstract_name
   if hasOut2:
      result.out2 = Out.Reg
   return result

def ins_affected_args(in1:Optional[In], out1: Optional[Out],hasSetFlags = False)->str:
   result =  """"""
   if out1 == Out.Reg:
      result += """
- GPRs, because `out` resolves to a register. """
   elif out1:
      result += """
- GPRs, if `out` resolves to a register. """

   result += """
- execution stack:
   - PC, as by any instruction """
   if in1 == In.Any or out1 == Out.Any:
      result += """
   - SP, if `in1` uses [%RelSPPop] addressing mode, or if `out1` uses
     [%RelSPPush] addressing mode. """
   if out1 == Out.Any:
      result += """
- Current stack memory page, if `out` resolves to it. """
   if hasSetFlags:
      result += """
- Flags, if `set_flags` modifier is set. """
   return result


def ins_affected(ins:Instruction):
   return ins_affected_args(ins.in1, ins.out1, ins.setFlags())
@dataclass
class InstructionDoc():
   ins: Instruction
   summary: str
   semantic: str
   usage: str
   abstract_syntax: Optional[str] = None
   syntax_override: Optional[list[str]] = None
   affectedState: str = ""
   legacy: Optional[str] = None
   similar: Optional[str] = None

def bullets(ls):
   if isinstance(ls, str):
      return ls
   if len(ls) == 0:
      return ""
   if len(ls) == 1:
      return ls[0]
   return "\n".join(map(lambda x: f"- {x}", ls))
