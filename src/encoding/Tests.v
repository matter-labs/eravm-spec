Require Import Encoder.
Require Import lib.BitsExt lib.Show.
Require Import Coq.Strings.String.
Import Addressing AssemblyToMach Core GeneratedMachISA Modifiers Predication GPR Types.
Import Addressing.Coercions.
(** Test cases:
	sub r0, r1, r2
00 00 00 00 02 10 00 49
	sub.s r0, r1, r2
00 00 00 00 02 10 00 4a
	sub! r0, r1, r2
00 00 00 00 02 10 00 4b
	sub 10, r1, r2
00 00 00 0a 02 10 00 89
*)
Import Assembly.
Notation equals := eq_refl.
Open Scope string.
Definition sub in1 in2 out1 := (Ins _ (OpSub in1 in2 out1 NoSwap PreserveFlags) IfAlways).
Check (equals: "000000000210004B" = Show.to_string (encode_asm (Ins _ (OpSub R0 R1 R2 NoSwap SetFlags) IfAlways))).
Check (equals: "000000000210004A" = Show.to_string (encode_asm (Ins _ (OpSub R0 R1 R2 Swap PreserveFlags) IfAlways))).
Check (equals: "0000000002100049" = Show.to_string (encode_asm (sub R0 R1 R2))).
Check (equals: "0000000A02100089" = Show.to_string (encode_asm (sub (Imm (# 10)) R1 R2))).
Check (equals: "0000000A02100079" = (Show.to_string (encode_asm (Ins _ (OpSub (Absolute R0 (# 10)) R1 R2 NoSwap PreserveFlags) IfAlways)))).

(* Require Import Extraction. *)

(* Require Import ExtrOcamlBasic. *)
(* Require Import ExtrOcamlString. *)
(* Extract Inlined Constant Datatypes.fst => "fst". *)
(* Extract Inlined Constant Datatypes.snd => "snd". *)

(* Extraction Blacklist List String Int. *)

(* Recursive Extraction encode_asm. *)


(* Definition ins_encode (i:predicated asm_instruction) : string := *)
(*   Show.to_string (encode_asm i). *)

(* Recursive Extraction sub ins_encode. *)
