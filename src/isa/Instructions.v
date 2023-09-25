Section InstructionSets.
(** # EraVM instruction sets

*Note* If you are interested in the instruction set exposed to the assembly
 programmer, skim this section quickly and then proceed to
 [%AssemblyInstructionSet], [%CoreInstructionSet] and [%to_core].

The spec introduces the following layers of abstraction for the instruction set,
from lowest level to the highest level:

1. Binary encoding (as [BITS 64] type instances).
   Binary encoded instructions, each instruction is 64-bit wide.

   The exact type for such instructions is [%BITS 64].

   The definition [%encode_mach_instruction] formalizes the encoding algorithm.
   It depends on [%encode_predicate] and [%encode_opcode].

   The encoding is an injection, because most instructions ignore the values of
   some instruction fields such as [%op_dst1].

2. Low-level machine instructions [%mach_instruction].

   - Fixed format with two input operands, two output operands, two immediate
     values.
   - Restricted sources/destinations (e.g. second input can only be fetched from
     registers), instructions may ignore some instruction fields.

3. Assembly instructions (see section [%AssemblyInstructionSet]).

   An assembly instruction is an instance of [%predicated asm_instruction].
   The type [%asm_instruction] defines instruction format with the exact operand
   types and all their supported modifiers.

   The instruction semantic is defined for these instructions; see [%step] in
   section [%SmallStep].

   The following abstraction levels simplify the definition of instruction
   semantic but are invisible for assembly programmer.

-----

4. Core instructions (see the type [%instruction] in section
   [%CoreInstructionSet]).
   The exact type for such instructions is [%predicated (instruction decoded)].

   A simplified instruction set where the [%mod_swap] modifier is applied and
   there are no restrictions on the operand sources or destinations, such as
   "the second input operand may only be fetched from register". Because of
   fewer restrictions, the definitions are more uniform. The translation from
   [%asm_instruction] to [%instruction] is implemented in section
   [%AssemblyToCore].

   Additionally, the type [%instruction] describes the meaningful operand types
   for instructions after decoding, e.g. [%OpFarRet] loads an operand from a
   register, but then deserializes it into a compound value. The types of
   such compound values are explicitly provided by [%bound] definition.

   The type [%instruction] describes a schema of core instructions; this schema
   can be specialized to describe:

   - fetched and decoded instruction [%instruction decoded];
   - an instruction where input and output operands are bound to the memory
     locations [%instruction bound]. This abstracts loading and storing
     operands, and their serialization/deserialization in case of ABI encoded
     instruction parameters.


   Adding a layer of [%instruction bound] allows describing instruction
   semantics as if instructions were accepting structural values directly,
   omitting fetching values, binary encoding and decoding.
   - See [%step_add] for an example of how instruction-specific semantic is
     defined omitting loading and storing details.
   - See [%step_ContextMeta] for an example of how instruction-specific semantic
     is defined omitting not only loading and storing, but also
     serialization/deserialization details.
   - See [%OperandBinding] for the details of binding, e.g.
     [%bind_farret_params] describes how [%OpFarRet]'s ABI parameters are
     deserialized.
*)
End InstructionSets.
