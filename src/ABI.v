Require Memory.

Import Common Memory.

(** ABIs are described here:
https://github.com/matter-labs/zkevm_opcode_defs/blob/v1.3.2/src/definitions/abi/far_call.rs
 *)

Record coder (ABIParams:Type) := {
    decode: u256 -> ABIParams ;
    encode:  ABIParams -> u256 ;
    revertible1: forall params, decode (encode params) = params;
    revertible2: forall params encoded, decode encoded = params -> encode params = encoded;
  }.

(** * Fat Pointers *)
Module FatPointer.
  Axiom ABI : coder fat_ptr.


End FatPointer.


(** * Ret *)
Module Ret.
  Inductive forward_page_type := UseHeap | ForwardFatPointer | UseAuxHeap.
  Record params := {
      memory_quasi_fat_ptr: fat_ptr;
      page_forwarding_mode: forward_page_type;
    }.

  Axiom ABI: coder params.
End Ret.

(** * Near call *)
Module NearCall.

  Record params: Type := {
      nca_get_ergs_passed: u32;
    }.

  Axiom ABI: coder params.

End NearCall.

(** * Far call *)
Inductive far_call_forward_page_type := UseHeap | ForwardFatPointer | UseAuxHeap.

Record far_call := {
    fc_memory_quasi_fat_ptr: fat_ptr;
    fc_ergs_passed: u32;
    fc_shard_id: u8;
    fc_forwarding_mode: far_call_forward_page_type;
    fc_constructor_call: bool;
    fc_consider_new_tx: bool;
  }.


Axiom ABI_far_call: coder far_call.
