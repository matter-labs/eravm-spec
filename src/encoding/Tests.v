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
Definition sub in1 in2 out1 := OpSub in1 in2 out1 NoSwap PreserveFlags.
Notation str := Show.to_string.
Notation encoded  := (fun ins => str (encode_asm (Ins _ ins IfAlways))).

Check (equals: "000000000210004B" = encoded (OpSub R0 R1 R2 NoSwap SetFlags)).
Check (equals: "000000000210004B" = encoded (OpSub R0 R1 R2 NoSwap SetFlags)).
Check (equals: "000000000210004A" = encoded (OpSub R0 R1 R2 Swap PreserveFlags)).
Check (equals: "0000000002100049" = encoded (sub R0 R1 R2)).
Check (equals: "0000000A02100089" = encoded (sub (Imm (# 10)) R1 R2)).
Check (equals: "0000000A02100079" = encoded (OpSub (Absolute R0 (# 10)) R1 R2 NoSwap PreserveFlags)).

Import PageTypes.
Check (equals: "0000000002010433" = encoded (OpLoad (RegImmR R1) R2 Heap)).
Check (equals: "0000000002010437" = encoded (OpLoad (RegImmR R1) R2 AuxHeap)).
Check (equals: "0000FFFF0200043D" = encoded (OpLoad (RegImmI (Imm # 65535)) R2 Heap)).
Check (equals: "0000FFFF02000441" = encoded (OpLoad (RegImmI (Imm # 65535)) R2 AuxHeap)).
Check (equals: "0000000000000001" = encoded OpNoOp).
Check (equals: "0000000000000000" = encoded OpInvalid).
Check (equals: "0000000000000431" = encoded OpPanic).
Check (equals: "0000000000000448" = encoded (OpStaticRead (RegImmR R0) R0)).
Check (equals: "000000000000044C" = encoded (OpStaticWrite (RegImmR R0) R0)).
Check (equals: "0000000000000449" = encoded (OpStaticReadInc (RegImmR R0) R0 R0)).
Check (equals: "000000000000044D" = encoded (OpStaticWriteInc (RegImmR R0) R0 R0)).

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
