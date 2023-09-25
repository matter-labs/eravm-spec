Require Coder Ergs MemoryManagement Pointer lib.BitsExt.

Import ssreflect ssreflect.ssrfun ssreflect.eqtype ssreflect.tuple.
Import Arith Core Common Coder Ergs Memory MemoryManagement Pointer lib.BitsExt.

Section MetaParametersABI.
Record params :=
  mk_params {
      ergs_per_pubdata_byte: ergs;
      heap_size: mem_address;
      aux_heap_size: mem_address;
      this_shard_id: shard_id;
      caller_shard_id: shard_id;
      code_shard_id: shard_id;
    }.

Record params_layout :=
  mk_params_layout {
      (* reserved: u8 *)
      l_code_shard_id : u8;
      l_caller_shard_id : u8;
      l_this_shard_id : u8;
     (* reserved: u96 *)
      l_aux_heap_size : u32;
      l_heap_size : u32;
      (* reserved: u32 *)
      l_ergs_per_pubdata_byte: u32;
  }.

Section BinaryCoder.
  #[local] Open Scope ZMod_scope.
  Context (zero96 : BITS 96 := # 0).

  Definition encode_bin : @encoder word params_layout :=
    fun layout =>
      match layout with
      | mk_params_layout
          l_code_shard_id8
          l_caller_shard_id8
          l_this_shard_id8
          l_aux_heap_size32
          l_heap_size32
          l_ergs_per_pubdata_byte32
        => Some (
              zero8 ## l_code_shard_id8 ## l_caller_shard_id8 ## l_this_shard_id8 ## zero96 ## l_aux_heap_size32 ## l_heap_size32 ## zero32 ## l_ergs_per_pubdata_byte32)
      end.

  Definition decode_bin: @decoder word params_layout :=
    fun w =>
      Some {|
          (* reserved: u8 *)
          l_code_shard_id := w { 256 - 2*8 , 256 - 8} ;
          l_caller_shard_id := w {256 - 3 * 8, 256 - 2 * 8};
          l_this_shard_id := w {256 - 4 * 8, 256 - 3 * 8};
          (* reserved: u96 *)
          l_aux_heap_size := w { 3 * 32, 4 * 32 };
          l_heap_size := w { 2 * 32, 3 * 32 };
          (* reserved: u32 *)
          l_ergs_per_pubdata_byte:= w { 0, 32 };
        |}.


  Theorem binary_coder_revertible: revertible decode_bin encode_bin.
  Proof.
     unfold revertible, decode_bin, encode_bin.
     destruct obj.
     inversion 1.
     subst.
     move :
       (bits_size l_code_shard_id0)
         (bits_size l_caller_shard_id0)
         (bits_size l_this_shard_id0)
         (bits_size l_aux_heap_size0)
         (bits_size l_heap_size0)
         (bits_size l_ergs_per_pubdata_byte0)
         (bits_size zero96)
         (bits_size zero8)
         (bits_size zero32)
     .
     move =>bits_size bits_size0 bits_size1 bits_size2 bits_size3 bits_size4 bits_size5 bits_size6 bits_size7.
     repeat f_equal; try by bits_solve_subranges.
     {
       unfold subrange, subrange_len; apply /eqP; rewrite -val_eqE.
       repeat rewrite high_val; repeat rewrite low_val.
       rewrite drop0.
       repeat (rewrite take_cat; bits_solve_size; simpl).
       by rewrite take_size_cat.
     }
  Qed.

  Definition binary_coder := mk_coder decode_bin encode_bin binary_coder_revertible.
End BinaryCoder.


Section LayoutCoder.

Definition decode_layout : @decoder params_layout params :=
  fun layout =>
    match layout with
    | mk_params_layout l_code_shard_id l_caller_shard_id l_this_shard_id l_aux_heap_size l_heap_size
        l_ergs_per_pubdata_byte => Some
                                    {|
                                      ergs_per_pubdata_byte := l_ergs_per_pubdata_byte;
                                      heap_size := l_heap_size;
                                      aux_heap_size := l_aux_heap_size;
                                      this_shard_id := l_this_shard_id;
                                      caller_shard_id := l_caller_shard_id;
                                      code_shard_id := l_code_shard_id;
                                    |}
    end.


Definition encode_layout : @encoder params_layout params :=
  fun params =>
    match params with
    | mk_params ergs_per_pubdata_byte heap_size aux_heap_size this_shard_id caller_shard_id code_shard_id => Some
                                    {|
                                      l_ergs_per_pubdata_byte := ergs_per_pubdata_byte;
                                      l_heap_size := heap_size;
                                      l_aux_heap_size := aux_heap_size;
                                      l_this_shard_id := this_shard_id;
                                      l_caller_shard_id := caller_shard_id;
                                      l_code_shard_id := code_shard_id;
                                    |}
    end.

Theorem layout_coder_revertible: revertible decode_layout encode_layout.
Proof.
  unfold revertible, encode_layout, decode_layout.
  move => [ergs_per_pubdata_byte0 heap_size0 aux_heap_size0 this_shard_id0 caller_shard_id0 code_shard_id0].
  by inversion_clear 1.
Qed.

  Definition layout_coder := mk_coder decode_layout encode_layout layout_coder_revertible.
End LayoutCoder.

Definition coder := coder_compose binary_coder layout_coder.
End MetaParametersABI.
