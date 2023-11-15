Require Coder Ergs MemoryManagement Pointer TransientMemory lib.BitsExt ABI.FatPointerABI.

Import ssreflect ssreflect.ssrfun ssreflect.eqtype ssreflect.tuple.
Import Arith Core Common Coder Ergs MemoryManagement Pointer TransientMemory lib.BitsExt FatPointerABI.

Module FarCallForwardPageType.
  Definition UseHeap : u8 := # 0.
  Definition ForwardFatPointer : u8 := # 1.
  Definition UseAuxHeap : u8 := # 2.
  (* other u8 values are mapped to UseHeap. *)
End FarCallForwardPageType.

Definition data_page_type_to_u8 (t:data_page_type) : u8 :=
  match t with
  | Heap => FarCallForwardPageType.UseHeap
  | AuxHeap =>FarCallForwardPageType.UseAuxHeap
  end.

Definition span_of (fp: fat_ptr_layout) : span :=
  mk_span fp.(start) fp.(length).

Definition fwd_memory_adapter (fwd_type: u8) (raw_fat_ptr_layout: fat_ptr_layout) : option MemoryManagement.fwd_memory:=
  if fwd_type == FarCallForwardPageType.ForwardFatPointer then
    option_map ForwardExistingFatPointer
      (FatPointerABI.decode_layout raw_fat_ptr_layout)
  else
    let span := span_of raw_fat_ptr_layout in
    Some (
        if fwd_type == FarCallForwardPageType.UseAuxHeap then
          ForwardNewFatPointer AuxHeap span
        else (* Heap or a default option *)
          ForwardNewFatPointer Heap span
      )
.
