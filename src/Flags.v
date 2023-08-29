Require Bool.
Import Bool.

Section Flags.

(** # Flags

Flags are boolean values, which reflect certain characteristics of the result of
the last instruction.

It is commonly said that a flag is **set** if its value is [%true], and a flag
is **cleared** if its value is false.


In EraVM there are three flags:

1. [%OF_LT] : overflow or less than; *)
  Inductive OF_LT := Set_OF_LT | Clear_OF_LT.

  (** 2. [%EQ] : equals;  *)
  Inductive EQ := Set_EQ | Clear_EQ.
  (** 3. [%GT] : greater than.  *)
  Inductive GT := Set_GT | Clear_GT.

  (** More specifically:

1. [%OF_LT] is set in the following cases:
   - Overflow
   - Underflow
   - Division by zero
   - Panic, then when the exception handler starts execution, [%OF_LT] is set.

2. [%EQ] is set when the result of a binary operation is zero.
3. [%GT] is set when the first operand of a binary operation was greater than
   the second.
   *)

  (* begin details: Helpers *)
  Definition OF_LT_to_bool (f:OF_LT) := if f then true else false.
  Definition EQ_to_bool (f:EQ) := if f then true else false.
  Definition GT_to_bool (f:GT) := if f then true else false.

  #[reversible]
    Coercion OF_LT_to_bool : OF_LT >-> bool.
  #[reversible]
    Coercion EQ_to_bool : EQ >-> bool.
  #[reversible]
    Coercion GT_to_bool : GT >-> bool.

  Definition EQ_of_bool (f:bool) := if f then Set_EQ else Clear_EQ.
  Definition OF_LT_of_bool (f:bool) := if f then Set_OF_LT else Clear_OF_LT.
  Definition GT_of_bool (f:bool) := if f then Set_GT else Clear_GT.

  (* end details *)

  (** State of three flags [%flags_state] is stored in the global [%state] in
  the field [%gs_xstate] in the field [%gs_flags]. *)
  Record flags_state := mk_fs {
                            fs_OF_LT: OF_LT;
                            fs_EQ: EQ;
                            fs_GT: GT;
                          }.

  (**

## Usage
Flags are used to control the execution flow. See [%Predication].

   *)
  (* begin details: Helpers *)
  Definition set_overflow fs := match fs with
                              | mk_fs _ EQ GT => mk_fs Set_OF_LT EQ GT
                              end.

  Definition bflags (OF EQ GT: bool) : flags_state :=
    {|
      fs_OF_LT := OF_LT_of_bool OF;
      fs_EQ := EQ_of_bool EQ;
      fs_GT := GT_of_bool GT
    |}.

  (* end details *)
  Definition flags_clear : flags_state := mk_fs Clear_OF_LT Clear_EQ Clear_GT.
End Flags.
