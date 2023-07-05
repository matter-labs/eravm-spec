From RecordUpdate Require Import RecordSet.
Require Core List PrimitiveValue.

Import Core PrimitiveValue .

Section Regs.

  Context (pv := @primitive_value word).

  (** # General purpose registers

EraVM has 15 mutable general purpose registers R1, R2, ..., R15.
They hold [primitive_value word], so they are tagged 256-bit words.
The tag is set when the register contains a fat pointer.
   *)
  Inductive reg_name : Set :=
    R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13
  | R14 | R15.

  Record regs_state :=  mk_regs {
                            r1  : pv;
                            r2  : pv;
                            r3  : pv;
                            r4  : pv;
                            r5  : pv;
                            r6  : pv;
                            r7  : pv;
                            r8  : pv;
                            r9  : pv;
                            r10  : pv;
                            r11  : pv;
                            r12  : pv;
                            r13  : pv;
                            r14  : pv;
                            r15  : pv;
                          }.

  Definition reg_zero := IntValue word0.
  Definition reserved := reg_zero.
  Definition regs_state_zero := let z := reg_zero in
                                mk_regs z z z z z z z z z z z z z z z.


  (** Additionally, it has one reserved read-only register R0 which evaluates to [IntValue 0], that is, an untagged integer 0. Function [fetch_gpr] loads a value from register. *)
  Definition fetch_gpr (rs:regs_state) (r:reg_name) : pv :=
    match r with
    | R0 => IntValue word0
    | R1 => r1 rs
    | R2 => r2 rs
    | R3 => r3 rs
    | R4 => r4 rs
    | R5 => r5 rs
    | R6 => r6 rs
    | R7 => r7 rs
    | R8 => r8 rs
    | R9 => r9 rs
    | R10 => r10 rs
    | R11 => r11 rs
    | R12 => r12 rs
    | R13 => r13 rs
    | R14 => r14 rs
    | R15 => r15 rs
    end.

  (** Predicate [store_gpr] stores value to a general purpose register. It is not defined for [R0] *)
  Inductive store_gpr : regs_state -> reg_name -> pv -> regs_state -> Prop :=
  | fr_store1 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R1 pv
        (mk_regs pv r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
  | fr_store2 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R2 pv
        (mk_regs r1 pv r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
  | fr_store3 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R3 pv
        (mk_regs r1 r2 pv r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
  | fr_store4 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R4 pv
        (mk_regs r1 r2 r3 pv r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
  | fr_store5 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R5 pv
        (mk_regs r1 r2 r3 r4 pv r6 r7 r8 r9 r10 r11 r12 r13 r14 r15)
  | fr_store6 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R6 pv
        (mk_regs r1 r2 r3 r4 r5 pv r7 r8 r9 r10 r11 r12 r13 r14 r15)
  | fr_store7 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R7 pv
        (mk_regs r1 r2 r3 r4 r5 r6 pv r8 r9 r10 r11 r12 r13 r14 r15)
  | fr_store8 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R8 pv
        (mk_regs r1 r2 r3 r4 r5 r6 r7 pv r9 r10 r11 r12 r13 r14 r15)
  | fr_store9 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R9 pv
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 pv r10 r11 r12 r13 r14 r15)
  | fr_store10 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R10 pv
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 pv r11 r12 r13 r14 r15)
  | fr_store11 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R11 pv
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 pv r12 r13 r14 r15)
  | fr_store12 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R12 pv
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 pv r13 r14 r15)
  | fr_store13 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R13 pv
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 pv r14 r15)
  | fr_store14 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R14 pv
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 pv r15)
  | fr_store15 :
    forall r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 pv,
      store_gpr
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) R15 pv
        (mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 pv)
  .

  #[export] Instance etaGPRs : Settable _ := settable! mk_regs < r1; r2; r3; r4; r5; r6; r7; r8; r9; r10; r11; r12; r13; r14; r15 >.

  Definition reg_map f (rs:regs_state) : regs_state :=
    match rs with
    | mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 =>
        ( mk_regs (f r1) (f r2) (f r3) (f r4) (f r5) (f r6) (f r7) (f r8) (f r9) (f r10) (f r11) (f r12) (f r13) (f r14) (f r15))
    end.
End Regs.
