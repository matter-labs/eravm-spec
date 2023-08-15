(**
# EraVM instruction sets

The spec introduces the following layers of abstraction for the instruction set,
from lowest level to the highest level:

1. Binary encoding (not formalized).
   Binary encoded instructions, each instruction is 64-bit wide.

   The exact type for such instructions is [%int_mod 64].

2. Low-level machine instructions (not formalized).
   - Fixed format with two input, two output operands, two immediate values
   - restricted sources/destinations (e.g. second input can only be fetched from
     registers), instructions do not use all the supported instruction fields.

   The map from the low-level machine instructions to their binary encodings is
   an injection, because if a specific instruction does not use some parts
   fields, the values some fields in a bijection.

3. Assembly instructions (see section [%AssemblyInstructionSet]).
   The type [%asm_instruction] defines instruction format with the exact types
   of their operands, and all their supported modifiers.

   The exact type for such instructions is [%predicated asm_instruction].

   The instruction semantic is defined for these instructions; see [%step] in section [%SmallStep].

   The later abstraction levels are used for a simpler definition of instruction semantic.

-----

4. Core instructions (see the type [%instruction] in section [%CoreInstructionSet]).

   A simplified instruction set where the [%mod_swap] modifier is applied and
   there are no restrictions on the operand sources or destinations, such as
   "this operand may only be fetched from register". The translation from
   [%asm_instruction] to [%instruction] is implemented by [%to_core].

   Additionally, the type gives an idea of the "actual" operand types for
   instructions after decoding, e.g. [%OpFarRet] loads an operand from a
   register, but then deserializes a compound value from its value. The types of
   such compound values are explicitly provided by [%bound] definition.

   The exact type for such instructions is [%predicated (instruction decoded)].

   The type [%instruction] describes a schema of core instructions; this schema can be specialized to describe:

   - fetched and decoded instruction [%instruction decoded];
   - an instruction where input and output operands are bound to the memory locations [%instruction bound].
     This abstracts loading and storing operands, and their serialization/deserialization in case of ABI encoded instruction parameters.


   Adding a layer of [%instruction bound] allows describing instruction
   semantics as if instructions were accepting structural values directly,
   omitting details of binary encoding and decoding.
   - See [%step_add] for an example of how instruction-specific semantic is defined omitting loading and storing details.
   - See [%step_ContextMeta] for an example of how instruction-specific semantic is defined omitting not only loading and storing, but also serialization/deserialization details.
   - See [%OperandBinding] for the details of binding, e.g. [%bind_farret_params] describes how [%OpFarRet]'s ABI parameters are deserialized.
*)
