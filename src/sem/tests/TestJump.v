(*
From RecordUpdate Require Import RecordSet.
From mathcomp Require Import ssreflect eqtype.
From Bits Require Import bits spec tuple spec.properties.
Require SemanticCommon Semantics sem.Jump.

Import Addressing Bool Core Common Predication GPR CallStack MemoryOps isa.CoreSet State
  PrimitiveValue SemanticCommon Semantics RecordSetNotations TransientMemory.
Import Addressing.Coercions.
Import ssreflect.tuple.
Import BitsExt.
Import Pointer.

Section JumpTests.
  Generalizable All Variables.
  Theorem jump_correct1 :
    forall tail,
      let ins := Assembly.OpJump R0 in
      `(

          let topframe0 := InternalCall (mk_cf eh sp ( # 2) (# 10) cp) tail in
          let topframe1 := InternalCall (mk_cf eh sp ( # 0) (# 4) cp) tail in
          execute_action Execute
            (AssemblyToCore.to_core ins)
            (mk_state
               (mk_transient_state flags regs pges topframe0 context_u128 st)
               gs)

            (mk_state
               (mk_transient_state flags regs pges topframe1 context_u128 st)
               gs)
        )
  .
  Proof.
    move=> tail ins eh sp cp flags regs pges context_u128 st gs topframe new_topframe.
    {
      econstructor; first by reflexivity.
      {
        econstructor; reflexivity.
      }
      {
        constructor.
        unfold ergs_remaining, usub_uf, cf_ergs_remaining, cfc, gs_callstack, pc_map.
        instantiate (1:= # 4).
        by apply /eqP /andP.
      }
      {
        repeat econstructor.
      }
      {
        simpl.
        econstructor.
        {
          do  10 (constructor 2).
          by constructor 1.
        }
        {

          econstructor.
          simpl.
          subst topframe.
          subst new_topframe.

          econstructor; last by constructor.
          econstructor; [|reflexivity|reflexivity].
          econstructor.
          unfold pc_set, pc_map.
          unfold code_address_bits.
          simpl.
          by f_equal.
        }
      }
    }
  Qed.

  Remark helper:
    # 6 = (@low 240 code_address_bits
             (@catB 128 128 (@fromNat 128 0)
                (@catB 32 (addn (addn 32 32) 32)
                   (@subrange 0 (muln 3 32) (muln 4 32)
                      (@catB 32 (addn (addn 32 32) 32) (@fromNat 32 1)
                         (@catB 32 (addn 32 32) (@fromNat 32 777)
                            (@catB 32 32 (@fromNat 32 666) (@fromNat 32 6)))))
                   (@catB 32 (addn 32 32)
                      (@subrange 32 (muln 2 32) (muln 3 32)
                         (@catB 32 (addn (addn 32 32) 32) (@fromNat 32 1)
                            (@catB 32 (addn 32 32) (@fromNat 32 777)
                               (@catB 32 32 (@fromNat 32 666) (@fromNat 32 6)))))
                      (@catB 32 32
                         (@fromNat 32
                            (@toNat 32
                               (@subrange 64 32 (muln 2 32)
                                  (@catB 32 (addn (addn 32 32) 32) (@fromNat 32 1)
                                     (@catB 32 (addn 32 32) (@fromNat 32 777)
                                        (@catB 32 32 (@fromNat 32 666) (@fromNat 32 6)))))))
                         (@subrange 96 0 32
                            (@catB 32 (addn (addn 32 32) 32) (@fromNat 32 1)
                               (@catB 32 (addn 32 32) (@fromNat 32 777)
                                  (@catB 32 32 (@fromNat 32 666) (@fromNat 32 6)))))))))).
  Proof.
    clear.
    unfold code_address_bits.
    apply /eqP.
    unfold subrange, subrange_len.
    rewrite -val_eqE.
    simpl (val # (6)).
    by rewrite! low_catB low_val.
  Qed.

  Lemma jump_correct_aux2_2:
    forall (tail : CallStack.callstack) (encoded_ptr : u128) (regs0 : regs_state) (eh : CallStack.exception_handler) (sp : stack_address) (cp : state_checkpoint)
      (flags : Flags.flags_state) (pges : State.memory) (ctx : u128) (st : status) (gs : global_state),
      Some encoded_ptr = FatPointerABI.encode_fat_ptr (NotNullPtr {| fp_page := 666; fp_ptr := {| p_span := {| s_start := # (777); s_length := # (1) |}; p_offset := # (6) |} |}) ->
      Jump.step_jump (OpJump (IntValue (# (0) ## encoded_ptr)))
                     {|
                       gs_transient :=
                         {|
                           gs_flags := flags;
                           gs_regs := regs0 <| r1 := PtrValue (# (0) ## encoded_ptr) |>;
                                                       gs_pages := pges;
                           gs_callstack :=
                             ergs_set # (0)
                               (update_pc_regular (InternalCall {| cf_exception_handler_location := eh; cf_sp := sp; cf_pc := # (2); cf_ergs_remaining := # (6); cf_saved_checkpoint := cp |} tail));
                           gs_context_u128 := ctx;
                           gs_status := st
                         |};
                       gs_global := gs
                     |}
                     {|
                       gs_transient :=
                         {|
                           gs_flags := flags;
                           gs_regs := regs0 <| r1 := PtrValue (# (0) ## encoded_ptr) |>;
                                                       gs_pages := pges;
                           gs_callstack := InternalCall {| cf_exception_handler_location := eh; cf_sp := sp; cf_pc := # (6); cf_ergs_remaining := # (0); cf_saved_checkpoint := cp |} tail;
                           gs_context_u128 := ctx;
                           gs_status := st
                         |};
                       gs_global := gs
                     |}.
  Proof.
    move=> tail encoded_ptr regs0 eh sp cp flags pges ctx st gs H.
    constructor.
    eapply sc_apply with (xs1 := mk_transient_state flags _ pges _ ctx st)
                         (xs2 := mk_transient_state flags _ pges _ ctx st); last by constructor.
    eapply (scs_apply _ flags _ _ ctx _ _ _ _ st); try reflexivity.
    constructor.
    inversion H.
    simpl.
    f_equal.
  Qed.

  Lemma helper2:
    @eq word (@catB 128 128 (@fromNat 128 0) (@catB 32 (addn (addn 32 32) 32) (@fromNat 32 1) (@catB 32 (addn 32 32) (@fromNat 32 777) (@catB 32 32 (@fromNat 32 666) (@fromNat 32 6)))))
      (@catB 128 128 (@fromNat 128 0)
         (@catB 32 (addn (addn 32 32) 32)
            (@subrange 0 (muln 3 32) (muln 4 32) (@catB 32 (addn (addn 32 32) 32) (@fromNat 32 1) (@catB 32 (addn 32 32) (@fromNat 32 777) (@catB 32 32 (@fromNat 32 666) (@fromNat 32 6)))))
            (@catB 32 (addn 32 32)
               (@subrange 32 (muln 2 32) (muln 3 32)
                  (@catB 32 (addn (addn 32 32) 32) (@fromNat 32 1) (@catB 32 (addn 32 32) (@fromNat 32 777) (@catB 32 32 (@fromNat 32 666) (@fromNat 32 6)))))
               (@catB 32 32
                  (@fromNat 32
                     (@toNat 32
                        (@subrange 64 32 (muln 2 32)
                           (@catB 32 (addn (addn 32 32) 32) (@fromNat 32 1) (@catB 32 (addn 32 32) (@fromNat 32 777) (@catB 32 32 (@fromNat 32 666) (@fromNat 32 6)))))))
                  (@subrange 96 0 32 (@catB 32 (addn (addn 32 32) 32) (@fromNat 32 1) (@catB 32 (addn 32 32) (@fromNat 32 777) (@catB 32 32 (@fromNat 32 666) (@fromNat 32 6))))))))).
  Proof.
    apply /eqP.
    rewrite -val_eqE.
    by compute.
  Qed.


  Theorem jump_correct2 :
    forall tail,
      let ins := Assembly.OpJump R1 in
      `(
          Some encoded_ptr = FatPointerABI.encode_fat_ptr (NotNullPtr
                                                             (mk_fat_ptr #666
                                                                         {|
                                                                           p_span := {|
                                                                                      s_start := # 777;
                                                                                      s_length := # 1
                                                                                    |};
                                                                           p_offset := # 6;
                                                                         |})
                               ) ->
          let r1_value := #0 ## encoded_ptr in
          let regs := regs0 <| r1 := PtrValue r1_value |> in
          let topframe0 := InternalCall (mk_cf eh sp #2 #6 cp) tail in
          (* pay ergs & update PC *)
          let topframe1 := InternalCall (mk_cf eh sp #6 #0 cp) tail in
          let ts0 := mk_transient_state flags regs pges topframe0 ctx st in
          let ts1 := mk_transient_state flags regs pges topframe1 ctx st in
          in_kernel_mode topframe0 = true ->
          execute_action Execute
            (AssemblyToCore.to_core ins)
            (mk_state ts0 gs)
            (mk_state ts1 gs)
        )
  .
  Proof.
    move=> tail ins encoded_ptr regs0 eh sp cp flags pges ctx st gs H r1_value regs topframe0 topframe1 ts0 ts1 Hkernel.
    apply ea_execute with (cs0:=topframe0) (cs1 := update_pc_regular topframe0) (cs2 := ergs_set #0 (update_pc_regular topframe0) )
                          (instr_bound := OpJump (IntValue r1_value))
                          (xs0 := ts0) (xs1 := mk_transient_state flags regs pges (ergs_set #0 (update_pc_regular topframe0) ) ctx st )
                          (new_s := mk_state ts1 gs); [done|constructor | constructor; by apply /eqP /andP| | ].
    { (* bind_operands *)
      inversion H. subst encoded_ptr.
      econstructor.

      constructor; simpl.
      econstructor 2 with (high128:=#0).
      {
        repeat constructor.
        econstructor; repeat constructor.
      }
      {
        unfold FatPointerABI.decode_fat_ptr_word.
        rewrite split2app.
        simpl. f_equal.
      }
      {
        reflexivity.
      }
      {
        reflexivity.
      }
      {
        subst r1_value.
        by rewrite helper2.
      }
    }
    {
      econstructor.
      {
        do  10 (constructor 2).
        by constructor 1.
      }
      {
        by apply jump_correct_aux2_2.
      }
    }
  (* Qed. *)
  (* FIXME: Qed hangs here; the reason is probably that the
      kernel expands the dependently typed terms with huge proofs under the hood
      in order to check them. This bug may fix itself with a future version of
      Coq so we leave it for now. *)
  Admitted.

End JumpTests.
*)
