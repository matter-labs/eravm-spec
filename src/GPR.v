From RecordUpdate Require Import RecordSet.
Require Core List PrimitiveValue.

Import Core PrimitiveValue .

Section Registers.
  Import RecordSetNotations.
  Context (pv := @primitive_value word).

  (** # GPR (General Purpose Registers)

EraVM has 15 mutable general purpose registers R1, R2, ..., R15.
They hold [%primitive_value word], so they are tagged 256-bit words.
The tag is set when the register contains a fat pointer in its 128 least significant bits (it may contain other useful data in topmost 128-bits; this is used e.g. for encoding parameters of [%FarCall]).

Additionally, EraVM has one read-only, **constant register** R0 which
evaluates to [%IntValue 0], that is, an untagged integer 0.
   *)
  Inductive reg_name : Set :=
    R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13
  | R14 | R15.

  Record regs_state :=  mk_regs {
                            r1   : pv;
                            r2   : pv;
                            r3   : pv;
                            r4   : pv;
                            r5   : pv;
                            r6   : pv;
                            r7   : pv;
                            r8   : pv;
                            r9   : pv;
                            r10  : pv;
                            r11  : pv;
                            r12  : pv;
                            r13  : pv;
                            r14  : pv;
                            r15  : pv;
                          }.

  (* begin hide *)
  Definition reg_zero := IntValue word0.
  Definition reserved := reg_zero.
  Definition regs_state_zero := let z := reg_zero in
                                mk_regs z z z z z z z z z z z z z z z.

  Definition reg_idx (name: reg_name) : nat :=
    match name with
    | R0 => 0
    | R1 => 1
    | R2 => 2
    | R3 => 3
    | R4 => 4
    | R5 => 5
    | R6 => 6
    | R7 => 7
    | R8 => 8
    | R9 => 9
    | R10 => 10
    | R11 => 11
    | R12 => 12
    | R13 => 13
    | R14 => 14
    | R15 => 15
    end
  .
  (* end hide *)

  (** Function [%fetch_gpr] loads a value from register. *)
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

(* begin details: helpers *)

  #[export] Instance etaGPRs : Settable _ := settable! mk_regs < r1; r2; r3; r4; r5; r6; r7; r8; r9; r10; r11; r12; r13; r14; r15 >.
  (** Predicate [%store_gpr] stores value to a general purpose register. Storing to [%R0] is ignored. *)
  Definition store_gpr (rs: regs_state) (name: reg_name) (pv: primitive_value) : regs_state :=
    match name with
    | R0 => rs
    | R1 => rs <| r1 := pv|>
    | R2 => rs <| r2 := pv|>
    | R3 => rs <| r3 := pv|>
    | R4 => rs <| r4 := pv|>
    | R5 => rs <| r5 := pv|>
    | R6 => rs <| r6 := pv|>
    | R7 => rs <| r7 := pv|>
    | R8 => rs <| r8 := pv|>
    | R9 => rs <| r9 := pv|>
    | R10 =>rs <| r10 := pv|>
    | R11 =>rs <| r11 := pv|>
    | R12 =>rs <| r12 := pv|>
    | R13 =>rs <| r13 := pv|>
    | R14 =>rs <| r14 := pv|>
    | R15 =>rs <| r15 := pv|>
    end.

  Definition reg_map f (rs:regs_state) : regs_state :=
    match rs with
    | mk_regs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 =>
        ( mk_regs (f r1) (f r2) (f r3) (f r4) (f r5) (f r6) (f r7) (f r8) (f r9) (f r10) (f r11) (f r12) (f r13) (f r14) (f r15))
    end.
  (* end details *)
End Registers.
