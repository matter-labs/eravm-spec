(** This is the specification of the instruction set of EraVM 1.4.1, a language
virtual machine for zkSync Era. It describes the virtual machine's architecture,
instruction syntax and semantics, and some elements of system protocol.

# Table of contents

- **Overview**

  + [%Glossary] : a list of all important recurring terms and notations defined in this document.
  + [%ArchOverview] : a bird's eye overview of EraVM architecture with links to more detailed descriptions of its parts.
  + [%PrimitiveValue] : defines a tagged 256-bit word datatype; can be an integer or a pointer.

- **EraVM Structure**

  [%StateDefinitions] collects all system state, persistent and transient.

  + [%Registers] : a group of isolated read/write memory cells available to all instructions.
  + [%Flags] : special registers showing the status of the latest computations.
  + [%Predication] : how setting flags makes EraVM skip of execute instructions.
  + [%Memory] : transient memory (heap, stack) for supporting computations and persistent storages of contracts.
  + [%PointerDefinitions] : definition of pointers to transient memory and operations on them.
  + [%Slices] : how individual pointers are restricted to selected subranges of memory addresses.
  + [%Callstack] : states of running functions and contracts.
  + [%MemoryContext] : how new transient memory is allocated when a contract is called.

- **Instruction Set**

  + [%Addressing] : how instructions can refer to their arguments.
  + [%Resolution] : how instruction arguments are resolved to the operand values.
  + [%InstructionSets] : overview of all layers of instruction set and their relations.

    * [%Modifiers] : recurring modifiers supported by many instructions: [%mod_set_flags] and [%mod_swap].
    * [%AssemblyInstructionSet] : **instruction set exposed to assembly programmers**.
    * [%CoreInstructionSet] : simplified instruction set used to define instruction semantic.
    * [%MachInstructionDefinition] : layout of encoded assembly instructions.
    * Conversions between instruction sets: [%asm_to_core] and [%asm_to_mach].

- **EraVM operation**

   + [%Ergs] : resource/gas system and basic operation costs.
   + [%MemoryOps] : precise formalization of memory writes and reads.
   + [%MemoryForwarding] : a mechanism to pass memory slices between contracts.
   + [%Events] : different types of events emitted when EraVM is operating.

   + [%KernelMode] : privileged mode of execution for system contracts allowing a restricted part of the instructions set.
   + [%StaticMode] : mode of execution with limited effects on persistent state.
   + [%SmallStep] : formal semantics of instruction execution cycle, in small-step operational style
   + [%Panics] : a mechanism of signaling irrecoverable errors and a list of situations where they occur.


- **Instruction set semantic**

   + Stack manipulation
      * **`SpAdd`** : [%SpAddDefinition] : forward stack pointer.
      * **`SpSub`** : [%SpSubDefinition] : rewind stack pointer.

   + Arithmetic
      * **`Add`** : [%AddDefinition] :
      * **`Sub`** : [%SubDefinition] :
      * **`Mul`** : [%MulDefinition] :
      * **`Div`** : [%DivDefinition] :

   + Bitwise logical
      * **`And`** : [%AndDefinition] :
      * **`Or`** : [%OrDefinition] :
      * **`Xor`** : [%XorDefinition] :

   + Bitwise shifts
      * **`Shl`** : [%ShlDefinition] : left logical shift.
      * **`Shr`** : [%ShrDefinition] :  right logical shift.
      * **`Rol`** : [%RolDefinition] : left circular shift.
      * **`Ror`** : [%RorDefinition] : right circular shift.

   + Control flow
      * **`Nop`** : [%NopDefinition] : do nothing.
      * **`Jump`** : [%JumpDefinition] : jump to code (conditional jumps are implemented through [%Predication]).
      * **`NearCall`** : [%NearCallDefinition] : call a function in the same contract.
      * **`NearRet`** : [%NearRetDefinition] : normal return from near call to the call site, return unspend ergs.
      * **`NearRevert`** : [%NearRevertDefinition] : return from near call due to a recoverable error, return unspend ergs, roll back storage/events, execute exception handler.

      * **`NearRetTo`** : [%NearRetToDefinition] : Like `NearRet` but returns to explicit label.
      * **`NearRevertTo`** : [%NearRevertToDefinition] : like `NearRevert` but executes code at label instead of exception handler.

      * **`Panic`** : [%PanicDefinition] : trigger panic.
      * **`NearPanicTo`** : [%NearPanicToDefinition] : trigger panic and return to label.
      * **`Farcall`** : [%FarcallDefinition] : call a contract
      * **`FarRet`** : [%FarRetDefinition] : return from farcall.
      * **`FarRevert`** : [%FarRevertDefinition] : like `FarRet` but roll back storage/events and execute exception handler.

   + Operations with heaps

      * **`LoadPtr`** : [%LoadPtrDefinition] : load word by a fat pointer.
      * **`LoadPtrInc`** : [%LoadPtrIncDefinition] : like `LoadPtr`, additionally return an incremented pointer.
      * **`Load`** : [%LoadDefinition] : load word from heap by a fat pointer.
      * **`LoadInc`** : [%LoadIncDefinition] : like `Load`, additionally return offset+32.
      * **`Store`** : [%StoreDefinition] : store word to heap by an offset.
      * **`StoreInc`** : [%StoreIncDefinition] : like `Store`, additionally return offset+32.

   + Operations with static memory page (unique "heap"-like unbound page, kernel-only)

      * **`StaticRead`** : [%StaticReadDefinition] : load word from heap by a fat pointer.
      * **`StaticReadInc`** : [%StaticReadIncDefinition] : like `Load`, additionally return offset+32.
      * **`StaticWrite`** : [%StaticWriteDefinition] : store word to heap by an offset.
      * **`StaticWriteInc`** : [%StaticWriteIncDefinition] : like `Store`, additionally return offset+32.

   + Operations with pointers

      * **`PtrAdd`** : [%PtrAddDefinition] : increment pointer.
      * **`PtrSub`** : [%PtrSubDefinition] : decrement pointer.
      * **`PtrShrink`** : [%PtrShrinkDefinition] : restrict the range of addresses that a pointer can reference.
      * **`PtrPack`** : [%PtrPackDefinition] : put data in the unused high 128 bits of a pointer.

   + Operations with storage
      * **`SStore`** : [%SStoreDefinition] : store value at a key in storage of the current contract.
      * **`SLoad`** : [%SLoadDefinition] : load value by key from storage of the current contract.

   + Operations with transient storage (resets after each transaction)
      * **`TransientStore`** : [%TransientStoreDefinition] : store value at a key in transient storage of the current contract.
      * **`TransientLoad`** : [%TransientLoadDefinition] : load value by key from transient storage of the current contract.

   + Events and precompiles
      * **`OpEvent`** : [%OpEventDefinition] : emit an event.
      * **`ToL1`** : [%ToL1Definition] : emit a message to L1.
      * **`PrecompileCall`** : [%PrecompileCallDefinition] : call an extension of VM specific to currently executing system contract.
      * **`Context`** : [%ContextDefinition] : access the context register and context captured value (used to emulate `msg.value`).
      * **`Contract`** : [%ContractDefinition] : access associated contract addresses (current, caller, or code)
      * **`VM`** : [%VMDefinition] : access some parts of VM execution state such as stack pointer.

- **ABI**  (memory layouts of compound data structures serialized to 256-bit words.)

   + [%Coder] : general definitions of encoding, decoding, composition and required properties.
   + [%NearCallABI]
   + [%FatPointerABI]
   + [%FarCallABI]
   + [%FarRetABI]
   + [%MetaParametersABI] : layout of result of [%ContextMeta].
   + [%PrecompileParametersABI] : layout of result of [%ContextMeta].

- **Instruction encoding**

   + [%EncodingTools] : binary encoding of different parts of instruction layout.
   + [%encode_opcode] : encoding source/destination, addressing modes, and all modifiers as a single 11-bit opcode value.
   + [%MachEncoder] : the main assembly instruction encoder definition.

- **Elements of protocol**

  + [%Bootloader] : a system contract in charge of block construction.
  + [%Precompiles] : extensions of virtual machine.
  + [%VersionedHash] : used to fetch the contract code.
  + [%Decommitter] : fetches the contract code.
 *)
