Require Coder Pointer lib.BitsExt.

Import ssreflect ssreflect.ssrfun ssreflect.eqtype ssreflect.tuple.
Import Core Common Coder Pointer lib.BitsExt.

(** Record [%fat_ptr_layout] displays the memory layout of a 128-bit fat pointer.*)
Record fat_ptr_layout := mk_fat_ptr_layout {
                              length: u32;
                              start: u32;
                              page: u32;
                              offset: u32;
                            }.
Definition null_fat_ptr_layout := mk_fat_ptr_layout zero32 zero32 zero32 zero32.

Section LayoutCoder.
  (** Functions [%encode_layout] and [%decode_layout] formalize the encoding of
  a [%fat_ptr_nullable] to [%fat_ptr_layout]. *)
  Definition encode_layout : @encoder fat_ptr_layout fat_ptr_nullable :=
    fun fp : fat_ptr_nullable =>
      match fp with
      | NullPtr => Some null_fat_ptr_layout
      | NotNullPtr (mk_fat_ptr p (mk_ptr (mk_span s l) ofs)) =>
          if (p == 0)  || (p >= 2^32) then None else
            Some (mk_fat_ptr_layout l s (# p) ofs)
      end.

  Definition decode_layout : @decoder fat_ptr_layout fat_ptr_nullable :=
    fun w: fat_ptr_layout =>
      match w with
      | mk_fat_ptr_layout length start page offset =>
          if page == zero32 then Some NullPtr else
            Some (NotNullPtr {|
                      fp_page := toNat page;
                      fp_ptr := {|
                                 p_span := mk_span start length;
                                 p_offset := offset;
                               |}
                    |})
      end.

  Theorem layout_coding_revertible: revertible decode_layout encode_layout.
  Proof.
    move => [|[page [[start length] ofs]]]; first by inversion 1.
    move => [length' start' page' ofs'] //=.
    case_eq (page == 0) => Hva2 ; first by inversion_clear 1.
    simpl.
    case_eq (2^32 <= page); first by inversion 1.
    inversion 2.
    subst.
    have Hpagelt: page < 2^32.
    rewrite ltnNge.
    by move: H ; case (2^32 <= page).
    have Hpage: # ( page) == zero32 = false.
    {
      symmetry; rewrite -Hva2.
      by apply properties.fromNatBounded_eq.
    }
    {
      rewrite Hpage.
      repeat f_equal.
      by apply properties.toNat_fromNatBounded.
    }
  Qed.

  Definition fat_ptr_layout_coder : @Coder.coder fat_ptr_layout fat_ptr_nullable
    := mk_coder decode_layout encode_layout layout_coding_revertible.

End LayoutCoder.

Section BinaryCoder.
  #[local] Open Scope ZMod_scope.

  Definition encode_bin: @encoder u128 fat_ptr_layout :=
    fun fp: fat_ptr_layout =>
      match fp with
      | mk_fat_ptr_layout length start page offset =>
          Some (length ## start ## page ## offset)
      end.

  Definition decode_bin : @decoder u128 fat_ptr_layout :=
    fun w: u128 =>
      let length := w { 3*32, 4*32 } in
      let start  := w { 2*32, 3*32 } in
      let page   := w { 32, 2*32} in
      let offset := w { 0, 32 } in
      Some (mk_fat_ptr_layout length start page offset).

  Lemma fat_ptr_bin_revertible: revertible decode_bin encode_bin.
  Proof.
    move => [a b p d] w.
    have: (size a = 32) by apply /eqP; case a.
    have: (size b = 32) by apply /eqP; case b.
    have: (size p = 32) by apply /eqP; case p.
    have: (size d = 32) by apply /eqP; case d.
    move => Hd Hp Hb Ha.
    inversion_clear 1.
    unfold encode_bin, decode_bin.
    f_equal.
    unfold subrange, subrange_len.
    f_equal; apply /eqP.
    {
      rewrite -val_eqE high_val low_val.
      simpl.
      have H1: (size (((d ++ p) ++ b) ++ a) = 128) by rewrite! size_cat Hd Hp Hb Ha.
      have H2: (size ((d ++ p) ++ b) = 96) by rewrite! size_cat Hd Hp Hb.
      replace (3 * 32 + 32)%nat with (size (((d ++ p) ++ b) ++ a)).
      by rewrite take_size drop_size_cat.
    }
    {
      by rewrite properties.low_catB properties.high_catB.
    }
    {
      replace (a ## b ## p ## d) with ((a ## b) ## (p ## d));
        first by rewrite properties.low_catB properties.high_catB.
      apply /eqP; unfold eq_op =>//=.
      by rewrite catA.
    }
    {
      replace (a ## b ## p ## d) with ((a ## b ## p) ## d);
        first by rewrite properties.low_catB.
      apply /eqP; unfold eq_op =>//=.
      by rewrite! catA.
    }
  Qed.

  Definition binary_coder: @Coder.coder u128 fat_ptr_layout :=
    mk_coder decode_bin encode_bin fat_ptr_bin_revertible.
End BinaryCoder.

Section ComposedCoder.
  Definition ABI : @Coder.coder u128 fat_ptr_nullable :=
    coder_compose binary_coder fat_ptr_layout_coder.


  Definition decode_fat_ptr (w:u128) : option fat_ptr_nullable := ABI.(decode) w.

  Definition decode_fat_ptr_word (w:word) : option (u128 * fat_ptr_nullable) :=
    let (high128, low128) := split2 128 128 w in
    match decode_fat_ptr low128 with
    | Some fpn => Some (high128, fpn)
    | _ => None
    end
  .

  Definition decode_heap_ptr (w:word) : option (u224 * heap_ptr) :=
    let (msbs, ofs) := split2 _ 32 w in
    Some (msbs, mk_hptr ofs).

  Definition encode_heap_ptr (h:heap_ptr) : option u32 :=
    Some (hp_addr h)
  .

  Definition encode_heap_ptr_word (high224: u224) (h:heap_ptr) : option word :=
    match encode_heap_ptr h with
    | Some hpenc => Some (high224 ## hpenc)
    | _ => None
    end
  .
  Definition encode_fat_ptr (fp: fat_ptr_nullable) : option u128 := ABI.(encode) fp.
  Definition encode_fat_ptr_word (high_bytes: u128) (fp: fat_ptr_nullable) : option word :=
    match encode_fat_ptr fp with
    | Some enc => Some (high_bytes ## enc)
    | _ => None
    end.
End ComposedCoder.
