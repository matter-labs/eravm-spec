(* Require Import Coq.Program.Equality. *)

(* Require MemoryBase. *)

(* Import MemoryBase ZMod ZArith List ListNotations. *)

(* Definition data_page_params := {| *)
(*                                 addressable_block := Common.u8; *)
(*                                 address_bits := 24; *)
(*                                 default_value := Common.zero8; *)
(*                                 writable := true *)
(*                               |}. *)
(*   Definition m := let m0 := empty data_page_params in *)
(*                 let a0 := int_mod_of 24 3%Z in *)
(*                 let (a1,_) := uinc_overflow _ a0 in *)
(*                 let (a2,_) := uinc_overflow _ a1 in *)
(*                 let v0 := int_mod_of 8 1%Z in *)
(*                 let (v1,_) := uinc_overflow _ v0 in *)
(*                 let (v2,_) := uinc_overflow _ v1 in *)
(*                 store data_page_params v0 a0 ( *)
(*                     store data_page_params v1 a1 ( *)
(*                         store data_page_params v2 a2 m0)). *)
(* Program Definition mtestcase : *)
(*   option_map (List.map (fun i => int_val 8 i)) *)
(*     (load_multicell data_page_params (int_mod_of 24 3%Z) 3 m) = Some [ 1%Z; 2%Z; 3%Z]. *)
(* reflexivity. *)
(* Qed. *)

(* (* Compute option_map (merge_bytes 8 (8*3)) (load_multicell data_page_params (mk_int_mod_truncated 24 3%Z) 3 m). *) *)