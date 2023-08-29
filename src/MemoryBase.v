From RecordUpdate Require Import RecordSet.
From Bits Require spec.

Require BinNums FMapPositive ZArith.
Require Common.

Section MemoryBase.
  Import ssreflect.
  Set Warnings "-notation-overridden,-ambiguous-paths".
  Import BinNums ZArith spec FMapPositive.
  Set Warnings "notation-overridden,ambiguous-paths".

  (** Memory is modeled as a mapping from addresses (integers of [%address_bits]
  bits) to values of type [%addressable_block]. Unmapped addresses are mapped to
  the [%default_value]. *)
  Record mem_descr := mk_mem_descr {
                          addressable_block: Type;
                          default_value: addressable_block;
                          address_bits: nat;
                          writable: bool;
                        }.

  (* begin hide *)
  #[export] Instance etaMD: Settable _ := settable! mk_mem_descr< addressable_block; default_value; address_bits; writable>.
  (* end hide *)

  Context (mem_params: mem_descr)
    (default_value := mem_params.(default_value))
    (address_bits := mem_params.(address_bits))
    (addressable_block := mem_params.(addressable_block)).

  Axiom AX_ADDRESS_BITS_GT_0: address_bits <> 0.

  Definition address := BITS address_bits.

  Record mem_parameterized : Type := mk_mem {
                                         contents :> PositiveMap.t addressable_block
                                       }.

  (** We use a map from positive numbers implemented as a tree to store values in memory. However, address space starts at zero. Therefore, having an address $A$ we map it to the key $K(A)$ as follows:

$$K(A):= A + 1$$

   *)
  Program Definition addr_to_key (addr: address): positive :=
    match address_bits with
    | 0 => fun _ => _
    | S bts => fun Heq => Z.to_pos ((@toZ bts addr) + 1)
    end (@eq_refl Z).
  Next Obligation. exfalso. by apply AX_ADDRESS_BITS_GT_0. Qed.

  (** All memory addresses are initialized to the default value at memory
  genesis. *)
  Definition load (addr : address) (m : mem_parameterized) : addressable_block :=
    match PositiveMap.find (addr_to_key addr) m.(contents) with
    | None => default_value
    | Some v => v
    end.

  Definition store (val:addressable_block) (addr : address) (m : mem_parameterized) : mem_parameterized :=
    mk_mem (PositiveMap.add (addr_to_key addr) val m).

  (** An empty memory. *)
  Definition empty := mk_mem (PositiveMap.empty addressable_block).

  Inductive load_result (addr: address) (m: mem_parameterized) (v:addressable_block) : Prop :=
  | LoadResultOK: load addr m = v -> load_result addr m v.

  Inductive store_result (addr: address) (m : mem_parameterized) (v:addressable_block) (m'
      : mem_parameterized) : Prop :=
  | StoreResultOK:
    writable mem_params = true ->
    store v addr m = m' -> store_result addr m v m'.

  (** Heap variants are byte-addressable, but reads and words operate on 256-bit
  [%word]s. Multicell loads return [%len] consecutive bytes from memory [%m] at
  an address [%a]. *)
  Import Arith.
  Open Scope bits_scope.
  Fixpoint load_multicell (a:address) (len:nat) (m:mem_parameterized)
    : option (list addressable_block) :=
    match len with
    | O => Some nil
    | S lft => let value := load a m in
              let (overflow, nextaddr) := uadd_of a (fromZ 1) in
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
      (false, nextaddr) = uinc_of addr ->
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
      destruct (uadd_of a (fromPosZ 1)) eqn:Heq.
      destruct b =>//.
      destruct (load_multicell _ _ _) eqn: Hload =>//.
      inversion H.
      subst.
      econstructor 2 with (nextaddr := b0) =>//.
      by apply IHlen.
  Qed.


  Theorem load_multicell_result_size:
    forall tl a m v,
      load_multicell_result a tl m v ->
      seq.size v = tl.
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

  (** Similarly, [%store_multicell] accepts a list of values and puts them in memory starting from the address [%a]. *)
  Import seq.
  Fixpoint store_multicell (a:address) (vals: list addressable_block) (m:mem_parameterized)
    : option mem_parameterized  :=
    if writable mem_params then
      match vals with
      | [::] =>  Some m
      | v :: tail =>
          let stored := store v a m in
          let (overflow, nextaddr) := uinc_of a in
          if overflow then None else
            store_multicell nextaddr tail stored
      end
    else None.

  Inductive store_multicell_result:
    address -> list addressable_block -> mem_parameterized -> mem_parameterized -> Prop :=
  | smr_end : forall a m,
      writable mem_params = true ->
      store_multicell_result a [::] m m

  | smr_progress: forall addr nextaddr mem mem' mem'' value tail,
      writable mem_params = true ->
      (false, nextaddr) = uinc_of addr ->
      store_result addr mem value mem' ->
      store_multicell_result nextaddr tail mem' mem'' ->
      store_multicell_result addr (value::tail)  mem mem''
  .

  Theorem store_multicell_spec:
    forall ls a m m',
      store_multicell a ls m = Some m'  ->
      store_multicell_result a ls m m'.
  Proof.
    induction ls.
    - move => a m m' []. inversion 1.
      destruct (writable _) eqn: Hw;[|discriminate]. inversion H0 =>//. by constructor.
    - move => a0 m m'.
      inversion 1.
      destruct (writable _) eqn: Hw =>//.
      destruct (uinc_of _) eqn: Hinc =>//.
      destruct b =>//.
      econstructor 2  with (nextaddr := b0) =>//.
      by eauto.
  Qed.

End MemoryBase.
