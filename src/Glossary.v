(** # Notations

- Definitional equality is denoted with $A:=B$. Its meaning is: $A$ can be substituted with $B$.
- Ranges of numbers are denoted as follows:

  $$\mathit{[start, limit) := \{n | start \leq n \lt limit\}}$$

  In other words, start is included, and limit is excluded.

- Accessing subranges of a binary representation of a number is denoted with $\{\}$.
  For example, this denotes a binary number obtained by taking bits from 128-th
  to 255-th, both inclusive, of the value $\mathit{op}$:

  $$\mathit{op}\{255, 128\}$$

- Concatenation of sequences of binary numbers is denoted with $||$

  For example, this denotes concatenating bit representations of the numbers $a$ and $b$:
  $$a || b$$
*)

(**

# Glossary

- **ABI** --  application binary interface. See [%ABI].
- **Active external frame** --  the closest external frame to the top of call stack. For example, in a callstack [%(InternalCall _ (InternalCall _ (ExternalCall _ (InternalCall _ ...))))] the active external frame will be the third frame in stack. See [%active_extframe].
- **Auxheap** --  one of two heap variants (heap and auxheap), mostly used by system contracts. Executing one of far call instructions creates a new external frame and allocates pages for code, constants, data stack, heap and aux heap.
- **Batch** -- ??
- **Burning ergs** --  setting ergs to zero in topmost call stack frame, external or internal. See [%Ergs].
- **Callstack** --  a stack of context information. Executing one of near call instructions pushes a frame of type [%InternalCall] to the callstack, executing one of far call instructions pushes a frame of type [%ExternalCall]. See [%CallStack].
- **Checkpoint** -- see [%state_checkpoint]. Not to confuse with EraVM snapshot.
- **Code page** --  a read only page filled with [%instruction_predicated]. Created by far calls, filled with code obtained from [%Decommitter]. See [%code_page].
- **Const page** --  a read only page filled with constant data. Created by far calls, filled with constants obtained from [%Decommitter]. Can be implemented by putting constants to code pages instead. See [%const_page].
- **Context instructions** --  instructions implemented as variants of `context` machine instruction:
  + [%OpContextCaller]
  + [%OpContextCodeAddress]
  + [%OpContextErgsLeft]
  + [%OpContextGetContextU128]
  + [%OpContextIncrementTxNumber]
  + [%OpContextMeta]
  + [%OpContextSetContextU128]
  + [%OpContextSetErgsPerPubdataByte]
  + [%OpContextSp]
  + [%OpContextThis]

- **Running instance of a contract, or a function** -- a set of memory pages, call stack frames, and other resources associated with a running contract or function. They are distinct per function/contract call.
- **Current contract** --  contract currently being executed. See [%ecf_this_address] and [%active_extframe].
- **Current function** --  the most recent of functions currently being executed.
- **Data page** -- one of types of memory pages. See [%data_page].
- **Data stack** -- a stack implicitly operated upon by instructions using address modes like [%RelSpPop] or [%RelSP]. Located on pages of type [%stack_page]. Every contract instance has its own stack; functions invoked by [%OpNearCall] share the stack with their caller.
- **Decommitter** -- a module responsible for storing contract code and providing it upon query.
- **Exception handler** -- a [%code_address] of a piece of code associated to a call stack frame. This code will be executed if the corresponding function reverts or panics.
- **External/internal frame, function/contract frame** --
- **Far call** -- execution of one of the following instructions: [%OpFarCall], [%OpMimicCall], [%OpDelegateCall].
- **Fat pointer** --  a full 128-bit [%data_page] pointer encoding page id, a span of addresses from some starting address and with a specified length, and an offset inside this span. See [%fat_ptr].
- **GPR, general purpose register** --  one of 16 registers [%r0]--[%r15] containing primitive values. Register [%r0] is a constant register, can not be written to and is read-only.
- **Heap** --  one of two heap variants (heap and auxheap), mostly used by system contracts. Executing one of far call instructions creates a new external frame and allocates pages for code, constants, data stack, heap and aux heap.
- **Heap pointer** --  a pair of address in heap and a limit; it is associated with a span $[0; limit)$. See [%heap_ptr].
- **Heap variant** -- either Heap or Auxheap, depending on the context.
- **Integer value** -- a [%primitive_value] with a reset pointer tag. See [%IntValue].
- **L1** -- level-1, refers to the main Ethereum blockchain, also known as the Ethereum Mainnet. Used to distinguish from scaling solutions or Layer 2 solutions that aim to improve the scalability and throughput of the Ethereum blockchain.
- **Log instructions** -- variations of `log` machine instruction: [%OpSLoad], [%OpSStore], [%OpEvent], [%OpToL1Message], [%OpPrecompileCall].
- **Memory forwarding** -- a mechanism of sharing a read-only fragment ofmemory between contracts. The memory fragment is created from [%span] and described by [%fat_ptr]. This fragment can be narrowed or shrunk as a result of far call or executing [%OpPtrShrink].
- **Machine instruction** -- a low-level machine instruction with a fixed format. The high-level [%instruction_predicated] is encoded to machine instructions.
- **Memory growth** -- a process, where an access to a heap variant beyond its bound leads to increasing the bound and payment.
- **Message** --  TODO
- **Narrowing a fat pointer** -- subtract a given number from its length and add it to its start; it is guaranteed to not overflow. See [%fat_ptr_narrow]. Used when passing a fat pointer to a far call, or returning it from a contract.
- **Near call** -- calling a function that belongs to the same contract.
- **Operand** --  data or the address that is operated upon by the instruction. It represents the input or output values used by the instruction to perform a specific operation or computation. See [%InstructionArguments].
- **Page** -- see [%page].
- **Pointer value** -- a [%primitive_value] with a set pointer tag. May contain a fat pointer. See [%PtrValue].
- **Precompile call** -- an invokation of [%OpPrecompileCall]. Precompiles are
extensions of EraVM bound to one of the system contracts. When this contract
executes an instruction [%OpPrecompileCall], EraVM executes an
algorithm specific to this contract. See [%Precompiles].
- **Precompile processor** -- a module responsible for encoding the algorithms of precompile calls and executing them.
- **Primitive value** -- a tagged word. See [%primitive_value].
- **Shrinking a fat pointer** -- subtract a given number from its length; it is guaranteed to not overflow. See [%fat_ptr_shrink]. Triggered by [%OpPtrShrink] instruction.
- **Slice** -- see [%slice].
- **Span** -- see [%span].
- **Stack page** -- a type of pages. See [%stack_page].
- **System contracts** -- contracts with addresses from 0 to [%KERNEL_MODE_MAXADDR_LIMIT]. They are executed in [%KernelMode].
- **Topmost callstack frame** -- the last frame pushed to call stack.
- **Word** -- 256-bit unsigned untagged integer value.
- **address resolution** -- a matching between instruction operands and locations using the supported address modes. See [%resolve].
- **base cost** -- the fixed cost of executing instruction, in ergs. Some instructions imply additional costs, e.g. far calls may require paying for code decommitment.
- **bootloader** -- a system contract written in YUL in charge of block construction.
- **cell** -- alias to "word". Often used to distinguish between values themselves and the memory locations holding them.
- **depot** -- all storages in all shards. See [%depot].
- **ergs** -- resource spent on actions such as executing instructions. See [%Ergs].
- **instruction predicate** -- see [%Predication].
- **flag** -- see [%flag_state].
- **fully qualified address** -- see [%fqa_key].
- **instruction** -- low-level command or operation that is executed by a virtual machine to perform a specific task. Instructions supported by EraVm are described by the type [%instruction_predicated].
- **kernel mode** -- a mode of execution for system contracts opening access to full instruction set, containing instructions potentially harmful to the global state e.g. [%OpContextIncrementTxNumber]. See [%KernelMode].
- **key** -- a 256-bit address of a cell in storage.
- **location** -- see [%loc].
- **panic** -- irrecoverable error. Handled by formally executing [%OpPanic].
- **revert** -- execution of [%OpRevert], usually as a consequence of recoverable error.
- **malformed transaction** -- a transaction rejected by the bootloader. Handling it is the responsibility of the server that controls EraVM.
- **predicate** -- see [%Predication].
- **predication** -- see [%Predication].
- **program counter** -- the [%code_address] of the next instruction to be executed. See [%cf_pc].
- **rollback** -- restoration of the [%gs_revertable] portion of [%state] as a result of revert or panic. The state is saved at every near or far call. See also [%state_checkpoint].
- **shard** -- a collection of [%storage]s. See [%shard].
- **snapshot** -- a copy of the full state of EraVM. Server makes a snapshot of VM state every time a transaction is successfully completed. When the bootloader encounters a malformed transaction, it fails, and the server restarts EraVM from the most recent snapshot, skipping this transaction.
- **server** -- a program that launches EraVM and controls it. Feeds the transactions to the bootloader, provides decommitter and other external modules, restarts EraVM from the latest snapshot in case of malformed transactions.
- **stack pointer** -- the [%stack_address] where the next element will be pushed. It is the address of the (top of the stack + 1).
- **static mode** -- see [%StaticMode].
- **storage** -- see [%storage].
- **total cost** -- a sum of [%base_cost] of an instruction and all its additional costs.
- **versioned hash** -- a key used to retrieve the contract code from decommitter. See [%versioned_hash] and [%Decommitter].
- **VM** -- the same as EraVM, the abstract virtual machine that this document specifies.
 *)
