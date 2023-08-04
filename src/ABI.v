Require Coder Ergs Pointer GPR.
Import Core Common Coder Bool ZMod GPR Ergs Memory Pointer.

(** # ABI

ABIs are described here:
https://github.com/matter-labs/zkevm_opcode_defs/blob/v1.3.2/src/definitions/abi/far_call.as
 *)


Local Definition coder := @coder word.


(** ## Fat pointers *)
Module FatPointer.
  Axiom ABI  : @coder fat_ptr.

  Definition decode_fat_ptr (w:word) : option fat_ptr := ABI.(decode) w.

  Definition decode_heap_ptr (w:word) : option heap_ptr :=
    match decode_fat_ptr w with
    | Some (mk_fat_ptr _ (mk_ptr (mk_span _ length) offset)) =>
        Some (mk_hptr offset length)
    | None => None
   end.

  Definition decode_span (w:word) : option span :=
    match decode_fat_ptr w with
    | Some (mk_fat_ptr _ (mk_ptr s _ ))=> Some s
    | None => None
   end.

  Definition encode_fat_ptr (fp: fat_ptr) : word := ABI.(encode) fp.

  Definition encode_heap_ptr (hp:heap_ptr) : word :=
    encode_fat_ptr (mk_fat_ptr None (heap_ptr_to_free hp)).

End FatPointer.


(** ## Near call *)
Module NearCall.

  Record params: Type :=
    mk_params {
        ergs_passed: u32;
      }.

  Axiom ABI: @coder params.

End NearCall.

(* TODO find better place*)
Inductive fwd_memory :=
  ForwardFatPointer (p:fat_ptr)
| ForwardNewHeapPointer (heap_var: data_page_type) (s:span).


(** ## Ret *)
Module FarRet.
  Record params := mk_params {
                           forwarded_memory :> fwd_memory
                          }.
  Axiom ABI: @coder params.
  Axiom ABI_decode_zero: ABI.(decode) word0 = Some (mk_params (ForwardNewHeapPointer Heap span_empty)).
End FarRet.

(** ## Far call *)
Module FarCall.
  Import FatPointer.

  Record params :=
    mk_params {
        fwd_memory: fwd_memory;
        ergs_passed: ergs;
        shard_id: shard_id;
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
        memory_page_to_read: page_id;
        memory_page_to_write: page_id;
        precompile_interpreted_data: u64;
      }.

  (* Record inner_params := *)
  (*   mk_priv_params *)
  (*     { *)
  (*       priv_input_memory_offset: mem_address; *)
  (*       priv_input_memory_length: mem_address; *)
  (*       priv_output_memory_offset: mem_address; *)
  (*       priv_output_memory_length: mem_address; *)
  (*       priv_memory_page_to_read: page_id; *)
  (*       priv_memory_page_to_write: page_id; *)
  (*       priv_precompile_interpreted_data: u64; *)
  (*     }. *)

  (* Definition to_inner read_page write_page (pub: params) : inner_params := *)
  (*   match pub with *)
  (*   | mk_params *)
  (*       input_memory_offset *)
  (*       input_memory_length *)
  (*       output_memory_offset *)
  (*       output_memory_length *)
  (*       per_precompile_interpreted => *)
  (*       {| *)
  (*         priv_input_memory_offset := input_memory_offset; *)
  (*         priv_input_memory_length := input_memory_length; *)
  (*         priv_output_memory_offset := output_memory_offset; *)
  (*         priv_output_memory_length := output_memory_length; *)
  (*         priv_memory_page_to_read := read_page; *)
  (*         priv_memory_page_to_write := write_page; *)
  (*         priv_precompile_interpreted_data := per_precompile_interpreted; *)
  (*       |} *)
  (*   end. *)

  Axiom ABI: @coder params.

End PrecompileParameters.
