From RecordUpdate Require Import RecordSet.

Require Pointer.

Section Slices.
Import Bool Core ZMod Common MemoryBase Memory RecordSetNotations Pointer PMap_ext ZMod.
Open Scope ZMod_scope.
(** ### Slices

Accesses through fat pointers should be in bounds of its span.

Suppose $P:=(\mathit{page, start, length, offset})$ is a fat pointer.
Accesses through [%OpLoadPtr] and [%OpLoadPtrInc] return 32-byte words starting
at an address $\mathit{start + offset}$.

However, the 256-bit [%word] spans across addresses in range
$[\mathit{start + offset, start + offset + 32})$
and therefore might surpass the upper bound when $\mathit{length-offset} \leq 32$.

In this case, reads from out-of-bound bytes in range $[\mathit{start+length,
start+offset+32})$ will return zero bytes.

Data slice is a virtual memory page holding a read-only fragment of some memory
page.
 *)

Definition data_page_slice_params := data_page_params <| writable := false |>.
Definition data_slice := mem_parameterized data_page_slice_params.

Definition do_slice_page (from_incl to_excl: mem_address) (m:data_page) : data_slice :=
  let from_key := MemoryBase.addr_to_key _ from_incl in
  let to_key := MemoryBase.addr_to_key _ to_excl in
  let contents := pmap_slice m from_key to_key in
  mk_mem data_page_slice_params contents.


(** Predicate [%slice_page] describes a slice visible to a fat pointer. *)
Inductive slice_page (m:data_page) : span -> data_slice -> Prop :=
| sfp_apply:
  forall start length upper_bound readonly_slice,
    start + length = (upper_bound, false) ->
    do_slice_page start upper_bound  m = readonly_slice ->
    slice_page m (mk_span start length) readonly_slice.

End Slices.
