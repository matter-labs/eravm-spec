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

class Modifier(Enum):
   DataPageType = auto()
   Swap = auto()
   SetFlags = auto()
   IsFirst = auto()

   def name(self)-> str:
      match self:
         case Modifier.DataPageType: return "page_type"
         case Modifier.Swap: return "swap"
         case Modifier.SetFlags: return "sf"
         case Modifier.IsFirst: return "is_first"
   def coq(self)-> str:
      match self:
         case Modifier.DataPageType: return "data_page_type"
         case Modifier.Swap: return "mod_swap"
         case Modifier.SetFlags: return "mod_set_flags"
         case Modifier.IsFirst: return "bool"

@dataclass
class Instruction():
   abstract_name:str = ""
   mnemonic: str = ""
   modifiers : list[Modifier] = field(default_factory = lambda : [])
   in1: Optional[In] = None
   in2: Optional[In] = None
   out1: Optional[Out] = None
   out2: Optional[Out] = None
   imm1: Optional[str] = None
   imm2: Optional[str] = None
   kernelOnly: bool = False
   notStatic: bool = False

   def setFlags(self) -> bool:
      return Modifier.SetFlags in self.modifiers

   def swap(self) -> bool:
      return Modifier.Swap in self.modifiers
def abstract_syntax(ins:Instruction):
   result = ins.abstract_name
   if ins.in1:
      result += f" (in1: {ins.in1.coq()})"
   if ins.in2:
      result += f" (in2: {ins.in2.coq()})"
   if ins.imm1:
      result += f" ({ins.imm1}: imm_in)"
   if ins.imm2:
      result += f" ({ins.imm2}: imm_in)"
   if ins.out1:
      result += f" (out1: {ins.out1.coq()})"
   if ins.out2:
      result += f" (out2: {ins.out2.coq()})"
   for modifier in ins.modifiers:
        result += f" ({modifier.name()}: {modifier.coq()})"
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

   if ins.imm1:
      args.append(ins.imm1)

   if ins.imm2:
      args.append(ins.imm2)

   args_str = ", ".join(args)

   result = [f"`{ins.mnemonic} {args_str}`\n"]

   if ins.setFlags():
      result.append(f"`{ins.mnemonic}! {args_str}`\t to set [%mod_set_flags] modifier\n")

   if ins.swap():
      result.append(f"`{ins.mnemonic}.s {args_str}`\t to set [%mod_swap] modifier\n")

   if ins.setFlags() and ins.swap():
      result.append(f"`{ins.mnemonic}.s! {args_str}`\t to set both [%mod_set_flags] and [%mod_swap] modifier\n")

   return result
@dataclass
class InstructionDoc():
   ins: Instruction
   summary: str
   semantic: str
   usage: str
   add_to_title: str = ""
   preamble :str = ""
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
   ls[0] = f"- {ls[0]}"
   return "\n- ".join(ls)
