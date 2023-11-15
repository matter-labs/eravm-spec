Require Coder Ergs MemoryManagement Pointer lib.BitsExt ABI.FatPointerABI ABI.ForwardPageTypesABI.

Import ssreflect ssreflect.ssrfun ssreflect.eqtype ssreflect.tuple.
Import Arith Core Common Coder Ergs MemoryManagement Pointer TransientMemory lib.BitsExt FatPointerABI ForwardPageTypesABI.


  (** This record describes all the parameters that far returns can use. *)
Section FarRetABI.
  Record params :=
  mk_params {
      fwd_memory: fwd_memory;
    }.


(** This record describes the layout of 256-bit word that encodes these parameters. *)
Record params_layout :=
  mk_params_layout {
      (* reserved 3 bytes *)
      raw_memory_forwarding_type_enum : u8;
      (* last 16 bytes contain the pointer *)
      raw_fat_ptr_layout: fat_ptr_layout;
    }.

Section BinaryCoder.
  Open Scope ZMod_scope.
  Definition encode_bin : @encoder word params_layout :=
    fun params =>
      match params with
       | mk_params_layout memory_forwarding_type8 fat_ptr_layout128 =>
          match FatPointerABI.encode_bin fat_ptr_layout128 with
          | Some ptr_encoded128 => Some (zero8 ## zero8 ## zero8 ## memory_forwarding_type8 ##
                                        zero32 ##
                                        zero64 ##
                                        ptr_encoded128)
          | None => None
          end
      end
  .


  Definition decode_bin : @decoder word params_layout :=
    fun w =>
      let memory_forwarding_type : u8 := w { 256 - 4*8, 256 - 3*8 }  in
      let ptr : option fat_ptr_layout := FatPointerABI.decode_bin (low 128 w) in
      match ptr with
      | Some ptr => Some (mk_params_layout memory_forwarding_type ptr)
      | None => None
      end.


  Theorem binary_coder_revertible: revertible decode_bin encode_bin.
  Proof.
    unfold revertible, encode_bin, decode_bin.
    move => [mf fpe] encoded.
    move: (bits_size mf) (bits_size encoded).
    move => bits_size0 bits_size1.
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
  | mk_params (ForwardExistingFatPointer fptr) =>
      match FatPointerABI.encode_layout fptr with
        | Some ptr_layout =>
            Some
              {|
                raw_memory_forwarding_type_enum := FarCallForwardPageType.ForwardFatPointer;
                raw_fat_ptr_layout:= ptr_layout;
              |}
      | None => None
      end
  | mk_params (ForwardNewFatPointer heap_variant span) =>
      Some
        {|
          raw_memory_forwarding_type_enum := data_page_type_to_u8 heap_variant;
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
      | mk_params_layout raw_memory_forwarding_type_enum raw_fat_ptr_layout =>
          match fwd_memory_adapter raw_memory_forwarding_type_enum raw_fat_ptr_layout with
          | Some fwd_memory_value => Some (mk_params fwd_memory_value)
          | None => None
          end
      end
  .

  Theorem layout_coding_revertible: revertible decode_layout encode_layout.
    unfold revertible.
    unfold revertible, decode_layout, encode_layout, fwd_memory_adapter.
    move => [fwd_memory encoded].
    case_eq fwd_memory.
    { (* Existing fatptr *)
      move => p H. subst.
      case_eq (FatPointerABI.encode_layout p); last by [].
      {
        intros f.
        move /FatPointerABI.layout_coding_revertible.
        intros Hptr.
        inversion_clear 1.
        by rewrite Hptr.
      }
    }
    {
      intros heap_var s H.
      inversion 1.
      subst encoded.
     simpl.
     repeat f_equal =>//=.
     clear H0.
     {
       unfold span_of. destruct heap_var;
       repeat f_equal =>//=; by destruct s.
     }
    }
  Qed.

  Definition coder_layout := mk_coder decode_layout encode_layout layout_coding_revertible.

End LayoutCoder.

Definition coder := coder_compose coder_binary coder_layout.
End FarRetABI.
