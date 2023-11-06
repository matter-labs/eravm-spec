Require List Core MemoryBase.
Import Common Core MemoryBase List.

Section Memory.

  (** ### Data pages

A **data page** contains individually addressable bytes. Each data page holds
$2^{32}$ bytes. *)

  Definition data_page_params := {|
                                  addressable_block := u8;
                                  address_bits := 32;
                                  default_value := zero8;
                                  writable := true
                                |}.
  Definition mem_address := address data_page_params.
  Definition mem_address_zero: mem_address := zero32.
  Definition mem_address_bits := data_page_params.(address_bits).

  Definition data_page := mem_parameterized data_page_params.

  (** There are currently two types of data pages:

- [%Heap]
- [%AuxHeap].

  We call both of them **heap variants** for brevity, as in almost all cases
  they are handled in a similar way. *)
  Inductive data_page_type := Heap | AuxHeap.
  Definition page_bound := prod data_page_type mem_address.

  Local Open Scope ZMod_scope.
  Definition growth (current_bound: mem_address) (query_bound: mem_address)
    : mem_address :=
    if query_bound < current_bound then zero32 else
      snd (query_bound - current_bound)
     .
  (**

Note: only selected few instructions can access data pages:

- [%OpLoad]/[%OpLoadInc]
- [%OpStore]/[%OpStoreInc]
- [%OpLoadPointer]/[%OpLoadPointerInc]

Every byte on data pages has an address, but these instructions read or store 32-byte words.

-----

Fat pointers [%fat_ptr] define slices of data pages and allow passing them
between contracts.

### Stack pages

A **stack page** contains $2^{16}$ primitive values (see [%primitive_value]).
Reminder: primitive values are tagged words.

   *)
  Context {primitive_value: Type} (pv0: primitive_value).
  Definition stack_page_params := {|
                                   addressable_block := primitive_value;
                                   address_bits := 16;
                                   default_value := pv0;
                                   writable := true
                                 |}.

  Definition stack_address := address stack_page_params.
  Definition stack_address_bits := stack_page_params.(address_bits).
  Definition stack_address_zero: stack_address := zero16.

  Definition stack_page := mem_parameterized stack_page_params.

  (** #### Data stack in EraVM

There are two stacks in EraVM: call stack to support the execution of functions
and contracts, and data stack to facilitate computations. This section details
the data stack.

At each moment of execution, one stack page is active; it is associated with the
topmost of external frames, which belongs to the contract currently being
executed. See [%active_extframe], its field [%ecf_mem_ctx] and subfield
[%ctx_stack_page_id].

Each contract instance has an independent stack on a separate page.
Instead of zero, stack pointer on new stack pages start with a value
[%INITIAL_SP_ON_FAR_CALL]. Stack addresses in range [0; [%INITIAL_SP_ON_FAR_CALL]) can be used as a scratch space.

Topmost frame of the callstack, whether internal or external, contains the stack
pointer (SP) value [%cf_sp]; which points to the address after the topmost element of
the stack. That means that the topmost element of the stack is located in word
number $(\mathit{SP}-1)$ on the associated stack page.

Data stack grows towards greater addresses.
In other words, pushing to stack increases stack pointer value, and popping
elements decreases stack pointer.

### Const pages

A **const page** contains $2^{16}$ non tagged [%word]s.
They are not writable.

Implementation may put constants and code on the same pages.
In this case, the bytes on the same virtual page can be addressed in two ways:

- For instructions [%OpJump] and [%OpNearCall], the code addressing will be
  used: consecutive addresses correspond to 8-bytes instructions.
- For instructions like [%OpAdd] with [%CodeAddr] addressing mode, the const
  data addressing will be used: consecutive addresses correspond to 32-bytes
  words.

For example, [%OpJump 0], [%OpJump 1], [%OpJump 2], [%OpJump 3] will refer to
the first four instructions on the page; their binary representations, put
together, can be fetched by addressing the const page's 0-th word e.g.
[%OpAdd (CodeAddr R0 zero_16 ) (Reg R0) (Reg R1)].
   *)
  Definition const_address_bits := 16.

  Definition const_page_params := {|
                                   addressable_block := word;
                                   address_bits := const_address_bits;
                                   default_value := word0;
                                   writable := false
                                 |}.
  Definition const_address :=  address const_page_params.
  Definition const_page := mem_parameterized const_page_params.

  (** ### Code pages

A **code page** contains $2^{16}$ instructions.
They are not writable.

On genesis, code pages are filled as follows:

- The contract code is places starting from the address 0.
- The rest is filled with a value guaranteed to decode as [%invalid] instruction.

Const pages can coincide with code pages. *)

  Context {ins_type: Type} (invalid_ins: ins_type).

  (* Implementation note: [%code_address] should be [%address code_page_params] but we don't want to introduce
      dependency between code_address and instruction type *)
  Definition code_address_bits := 16.
  Definition code_address := BITS code_address_bits.
  Definition code_address_zero: stack_address := zero16.

  Definition code_page_params := {|
                                  addressable_block := ins_type;
                                  address_bits := code_address_bits;
                                  default_value := invalid_ins;
                                  writable := false
                                |}.
  Record code_page := mk_code_page {
                          cp_insns:> mem_parameterized code_page_params;
                        }.
  Definition code_length := code_address.

End Memory.
