Require Coder Ergs Pointer GPR.
Import Core Common Coder Bool ZMod GPR Ergs Memory Pointer.

(** # ABI

ABIs are described here:
https://github.com/matter-labs/zkevm_opcode_defs/blob/v1.3.2/src/definitions/abi/far_call.rs
 *)


Local Definition coder := @coder word.


(** ## Fat pointers *)
Module FatPointer.
  Axiom ABI  : @coder fat_ptr.
End FatPointer.

(** ## Ret *)
Module Ret.
  Inductive forward_page_type := ForwardFatPointer | UseMemory (type: data_page_type).

  Record params :=
    mk_params {
        memory_quasi_fat_ptr: fat_ptr;
        page_forwarding_mode: forward_page_type;
      }.

  Axiom ABI: @coder params.
  Axiom ABI_decode_zero: ABI.(decode) word0 = Some (mk_params fat_ptr_empty (UseMemory Heap) ).
End Ret.

(** ## Near call *)
Module NearCall.

  Record params: Type :=
    mk_params {
        ergs_passed: u32;
      }.

  Axiom ABI: @coder params.

End NearCall.

(** ## Far call *)
Module FarCall.
  Import FatPointer Ret.
  Record params :=
    mk_params {
        memory_quasi_fat_ptr: fat_ptr;
        ergs_passed: ergs;
        shard_id: shard_id;
        forwarding_mode: forward_page_type;
        constructor_call: bool;
        to_system: bool;
      }.


  Axiom ABI: @coder params.

End FarCall.


Module MetaParameters.

  Record params :=
    mk_params {
        ergs_per_pubdata_byte: ergs;
        heap_size: mem_address;
        aux_heap_size: mem_address;
        this_shard_id: shard_id;
        caller_shard_id: shard_id;
        code_shard_id: shard_id;
      }.

  Axiom ABI: @coder params.

End MetaParameters.

Module PrecompileParameters.

  Record params :=
    mk_params
      {
        input_memory_offset: mem_address;
        input_memory_length: mem_address;
        output_memory_offset: mem_address;
        output_memory_length: mem_address;
        per_precompile_interpreted: u64;
      }.

  Record inner_params :=
    mk_priv_params
      {
        priv_input_memory_offset: mem_address;
        priv_input_memory_length: mem_address;
        priv_output_memory_offset: mem_address;
        priv_output_memory_length: mem_address;
        priv_memory_page_to_read: page_id;
        priv_memory_page_to_write: page_id;
        priv_precompile_interpreted_data: u64;
      }.

  Definition to_inner read_page write_page (pub: params) : inner_params :=
    match pub with
    | mk_params
        input_memory_offset
        input_memory_length
        output_memory_offset
        output_memory_length
        per_precompile_interpreted =>
        {|
          priv_input_memory_offset := input_memory_offset;
          priv_input_memory_length := input_memory_length;
          priv_output_memory_offset := output_memory_offset;
          priv_output_memory_length := output_memory_length;
          priv_memory_page_to_read := read_page;
          priv_memory_page_to_write := write_page;
          priv_precompile_interpreted_data := per_precompile_interpreted;
        |}
    end.

  Axiom pub_ABI: @coder params.
  Axiom priv_ABI: @coder inner_params.

End PrecompileParameters.
