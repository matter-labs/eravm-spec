Require BinNums FMapPositive ZArith.
Require Common.

Section Mem.
  (* FIXME we probably could operate on pairs of integers/bits rather than
  dependent types. Remember that dependent types are an antipattern in Coq
  (sic!) *)
  Import lib.ZMod.
  Import BinNums ZArith FMapPositive.

  Record mem_descr := {
      addressable_block: Type;
      default_value: addressable_block;
      address_bits: nat;
      writable: bool;
    }.

  Variable mem_params: mem_descr.

  Let default_value := mem_params.(default_value).
  Let address_bits := mem_params.(address_bits).
  Let addressable_block := mem_params.(addressable_block).

  Definition address : Set := int_mod address_bits.

  Record mem_parameterized : Type := mk_mem {
                                  contents :> PositiveMap.t addressable_block
                                }.

  Definition addr_to_key (addr: address): positive :=
    Z.to_pos ((int_val address_bits addr) + 1).

  (** [load] assumes mem is initialized with a known default_value value. *)
  Definition load (addr : address) (m : mem_parameterized) : addressable_block :=
    match PositiveMap.find (addr_to_key addr) m.(contents) with
    | None => default_value
    | Some v => v
    end.

  Definition store (val:addressable_block) (addr : address) (m : mem_parameterized)
    : mem_parameterized :=
    mk_mem (PositiveMap.add (addr_to_key addr) val m).

  Definition empty := mk_mem (PositiveMap.empty addressable_block).

  Inductive load_result (addr: address) (m: mem_parameterized) (v:addressable_block) : Prop :=
    | LoadResultOK: load addr m = v -> load_result addr m v.

  Inductive store_result (addr: address) (m : mem_parameterized) (v:addressable_block) (m'
      : mem_parameterized) : Prop :=
    | StoreResultOK:
      mem_params.(writable) = true ->
      store v addr m = m' -> store_result addr m v m'.

  Fixpoint load_multicell (a:address) (len:nat) (m:mem_parameterized)
    : option (list addressable_block) :=
    match len with
    | O => Some nil
    | S lft => let value := load a m in
               let (nextaddr,overflow) := uinc_overflow _ a in
               if overflow then None else
               match load_multicell nextaddr lft m with
                 | Some tail => Some (cons value tail)
               | None => None
               end
    end.

  Inductive load_multicell_result:
    address -> forall len: nat, mem_parameterized -> list addressable_block -> Prop :=
  | lmr_end : forall a m,
      load_multicell_result a 0%nat m nil

  | lmr_progress: forall addr nextaddr mem value n tail,
      (nextaddr, false) = uinc_overflow _  addr ->
      load_result addr mem value ->
      load_multicell_result nextaddr n mem tail ->
      load_multicell_result addr (S n) mem (cons value tail)

.

Theorem load_multicell_spec:
  forall a len m ls,
  load_multicell a len m = Some ls ->
  load_multicell_result a len m ls.
Proof.
  intros a len. revert a.
  induction len.
  intros a m ls H.
  - inversion H. subst. constructor.
  - intros a m ls H.
    simpl in *.
    destruct (carry address_bits _) eqn: Heq.
    + congruence.
    + destruct (load_multicell _ _ _) eqn: Hload.
      * inversion H.
        subst.
        econstructor; simpl; eauto ; [|constructor; auto].
        unfold mk_int_mod_truncated.
        unfold uinc_overflow.
        unfold uadd_overflow.
        f_equal; symmetry; assumption.
      * congruence.
Qed.


Theorem load_multicell_result_len:
  forall tl a m v,
  load_multicell_result a tl m v ->
  length v = tl.
Proof.
  {
    induction tl.
    intros a m v H.
    - inversion_clear H; reflexivity.
    - intros a m []; inversion 1.
      + simpl; f_equal.
      eapply IHtl; eauto.
  }
Qed.

End Mem.
Import BinInt Z List ZMod.

Section Util.
Import BinInt ZArith Z List ZMod.
Variable bits: nat.

Definition concat_z z1 z2 : Z:=
  (z1* (2^ of_nat bits) +z2)%Z.

Definition concat_bytes_Z (ls: list Z)  : Z :=
  @fold_left Z Z concat_z ls 0%Z.
End Util.


Definition merge_bytes bits resbits (ls: list (int_mod bits)) : int_mod resbits
  :=
  let only_zs := List.map (int_val bits) ls in
  mk_int_mod_truncated resbits
    (concat_bytes_Z bits only_zs).



