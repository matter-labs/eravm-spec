Require Coder Ergs memory.Depot MemoryManagement Pointer lib.BitsExt ABI.FatPointerABI ABI.ForwardPageTypesABI.

Import ssreflect ssreflect.ssrfun ssreflect.eqtype ssreflect.tuple.
Import Arith Core Common Coder Ergs memory.Depot MemoryManagement Pointer TransientMemory lib.BitsExt FatPointerABI ForwardPageTypesABI.

Section FarCallABI.
  (** This record describes all the parameters that [%FarCalls] can use. *)
Record params :=
  mk_params {
      fwd_memory: fwd_memory;
      ergs_passed: ergs;
      shard_id: shard_id;
      constructor_call: bool;
      to_system: bool;
    }.

(** This record describes the layout of 256-bit word that encodes these parameters. *)
Record params_layout :=
  mk_params_layout {
      raw_to_system_bool: u8;
      raw_constructor_call_bool: u8;
      raw_shard_id: u8;
      raw_memory_forwarding_type_enum : u8;
      raw_ergs_passed: u32;
      (*raw_reserved: u64; *)
      raw_fat_ptr_layout: fat_ptr_layout;
    }.

Section BinaryCoder.
  Open Scope ZMod_scope.
  Definition encode_bin : @encoder word params_layout :=
    fun params =>
      match params with
       | mk_params_layout to_system8 constructor_call8 shard_id8 memory_forwarding_type8 ergs_passed32 (* reserved64 *) fat_ptr_layout128 =>
          match FatPointerABI.encode_bin fat_ptr_layout128 with
          | Some ptr_encoded128 => Some (
                                      to_system8 ## constructor_call8 ## shard_id8 ## memory_forwarding_type8 ##
                                        ergs_passed32 ##
                                        zero64 ##
                                        ptr_encoded128)
          | None => None
          end
      end
  .


  Definition decode_bin : @decoder word params_layout :=
    fun w =>
      let to_system : u8 := w { 256-8, 256 } in
      let constructor_call : u8 := w { 256 - 2*8, 256 - 8 }  in
      let shard_id : u8 := w { 256 - 3*8, 256 - 2*8 }  in
      let memory_forwarding_type : u8 := w { 256 - 4*8, 256 - 3*8 }  in
      let ergs_passed : u32 := w { 256 - 2*32, 256 - 32 }  in
      let ptr : option fat_ptr_layout := FatPointerABI.decode_bin (low 128 w) in
      match ptr with
      | Some ptr => Some (mk_params_layout to_system constructor_call shard_id memory_forwarding_type ergs_passed ptr )
      | None => None
      end.


  Theorem binary_coder_revertible: revertible decode_bin encode_bin.
  Proof.
    unfold revertible, encode_bin, decode_bin.
    move => [s c sh mf es fpe] encoded.
    move: (bits_size s) (bits_size c) (bits_size sh) (bits_size mf) (bits_size es) (bits_size encoded).
    move => bits_size0 bits_size1 bits_size2 bits_size3 bits_size4 bits_size5.
    case_eq (FatPointerABI.encode_bin fpe); last by discriminate.
    {
      inversion 2.
      replace (low 128 _) with u.
      {
        move: (bits_size u) => bits_size6.
        move: H => /FatPointerABI.fat_ptr_bin_revertible ->.
        do 2 f_equal; by bits_solve_subranges.
      }
      {
        unfold subrange, subrange_len; apply /eqP; rewrite -val_eqE.
        move : (bits_size u) => bits_size6.
        by rewrite low_val !take_cat; bits_solve_size; rewrite cats0.
      }
    }
  Qed.


  Definition coder_binary : @coder word params_layout :=
    mk_coder decode_bin encode_bin binary_coder_revertible.

End BinaryCoder.

Section LayoutCoder.

  Definition encode_layout: @encoder params_layout params :=
fun params =>
  match params with
  | mk_params (ForwardExistingFatPointer fptr) ergs_passed shard_id constructor_call to_system =>
      match FatPointerABI.encode_layout fptr with
        | Some ptr_layout =>
            Some
              {|
                raw_to_system_bool:= if to_system then # 1 else # 0;
                raw_constructor_call_bool := if constructor_call then # 1 else # 0;
                raw_shard_id := shard_id;
                raw_memory_forwarding_type_enum := FarCallForwardPageType.ForwardFatPointer;
                raw_ergs_passed:= ergs_passed;
                (*raw_reserved: u64; *)
                raw_fat_ptr_layout:= ptr_layout;
              |}
      | None => None
      end
  | mk_params (ForwardNewFatPointer heap_variant span) ergs_passed shard_id constructor_call to_system =>
      Some
        {|
          raw_to_system_bool:= if to_system then # 1 else # 0;
          raw_constructor_call_bool := if constructor_call then # 1 else # 0;
          raw_shard_id := shard_id;
          raw_memory_forwarding_type_enum := data_page_type_to_u8 heap_variant;
          raw_ergs_passed := ergs_passed;
          (*raw_reserved: u64; *)
          raw_fat_ptr_layout:= {|
                                start := span.(s_start);
                                length := span.(s_length);
                                page := zero32;
                                offset := zero32;
                              |};
        |}
  end.

  Definition decode_layout: @decoder params_layout params :=
    fun layout =>
      match layout with
      | mk_params_layout raw_to_system_bool raw_constructor_call_bool raw_shard_id raw_memory_forwarding_type_enum raw_ergs_passed raw_fat_ptr_layout =>
          match fwd_memory_adapter raw_memory_forwarding_type_enum raw_fat_ptr_layout with
          | Some fwd_memory_value => Some (
                                        {|
                                          fwd_memory := fwd_memory_value;
                                          ergs_passed := raw_ergs_passed;
                                          shard_id := raw_shard_id;
                                          constructor_call := raw_constructor_call_bool != zero8;
                                          to_system := raw_to_system_bool != zero8;
                                        |})
          | None => None
          end
      end
  .

  Theorem layout_coding_revertible: revertible decode_layout encode_layout.
    unfold revertible.
    unfold revertible, decode_layout, encode_layout, fwd_memory_adapter.
    move => [fwd_memory ergs_passed shard_id constructor_call to_system encoded].
    case_eq fwd_memory.
    { (* Existing fatptr *)
      move => p H. subst.
      case_eq (FatPointerABI.encode_layout p); last by [].
      {
        intros f.
        move /FatPointerABI.layout_coding_revertible.
        intros Hptr.
        inversion_clear 1.
        rewrite Hptr.
        by destruct constructor_call, to_system.
      }
    }
    {
      intros heap_var s H.
      inversion 1.
      subst encoded.
     simpl.
     repeat f_equal =>//=; try by destruct constructor_call, to_system.
     clear H0.
     {
       unfold span_of. destruct heap_var;
       repeat f_equal =>//=; try by destruct constructor_call, to_system, s.
     }
    }
  Qed.

  Definition coder_layout := mk_coder decode_layout encode_layout layout_coding_revertible.

End LayoutCoder.

Definition coder := coder_compose coder_binary coder_layout.
End FarCallABI.
