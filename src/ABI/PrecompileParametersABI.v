Require Coder TransientMemory lib.BitsExt.

Import ssreflect ssreflect.ssrfun ssreflect.eqtype ssreflect.tuple.
Import Core Common Coder TransientMemory lib.BitsExt.

Section PrecompileParametersABI.

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

(* begin details: equality *)

Definition params_eqn (x y: params) : bool :=
  (x.(input_memory_offset) == y.(input_memory_offset)) &&
    (x.(input_memory_length) == y.(input_memory_length)) &&
    (x.(output_memory_offset) == y.(output_memory_offset)) &&
    (x.(output_memory_length) == y.(output_memory_length)) &&
    (x.(per_precompile_interpreted) == y.(per_precompile_interpreted)) &&
    (x.(memory_page_to_read) == y.(memory_page_to_read)) &&
    (x.(memory_page_to_write) == y.(memory_page_to_write)) &&
    (x.(precompile_interpreted_data) == y.(precompile_interpreted_data)).

Lemma params_eqnP : Equality.axiom params_eqn.
Proof.
  move => x y.
  unfold params_eqn.
  destruct x,y =>//=.
  repeat match goal with
           [ |- context [(?x == ?y)] ] =>
             let Hf := fresh "H" in
             destruct (x == y) eqn: Hf; try rewrite Hf
         end =>//=; constructor; auto;
    repeat match goal with [ H: (?x == ?y) = true |- _] => move: H => /eqP -> end;
    try injection; intros; subst;
    repeat match goal with [ H: (?x == ?x) = false |- _] => rewrite eq_refl in H end =>//=.
  - constructor.
Qed.

Canonical params_eqMixin := EqMixin params_eqnP.
Canonical params_eqType := Eval hnf in EqType _ params_eqMixin.
(* end details *)


Axiom ABI: @coder word params.
End PrecompileParametersABI.
