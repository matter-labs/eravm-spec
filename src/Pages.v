From RecordUpdate Require Import RecordSet.
Require Common Memory lib.PMap_ext.
Import Common Memory BinInt List PMap_ext.
Import ListNotations.
Import RecordSetNotations.

Definition page_id := nat.

Section Pages.
  
  Context {ins_type: Type} (inv: ins_type).
  Inductive page :=
  (** Heap or auxheap *)
  | DataPage : data_page -> page
  | StackPage : stack_page -> page
  | ConstPage : const_page -> page
  | CodePage : code_page inv -> page.

  Inductive data_page_type := Heap | AuxHeap.

  Definition pages := list (prod nat page).

  Inductive page_has_id : pages -> page_id -> page -> Prop :=
  | mpid_select : forall mm id page,
      List.In (id, page) mm ->
      page_has_id mm id page.

  Inductive page_replace:  page_id -> page -> pages -> pages -> Prop :=
  | mm_replace_base: forall oldpage id newpage tail,
      page_replace id newpage ((id, oldpage)::tail) ((id,newpage)::tail)
  | mm_replace_ind: forall oldpage id not_id newpage tail tail',
      page_replace id newpage tail tail' ->
      id <> not_id ->
      page_replace id newpage ((not_id,oldpage)::tail) ((not_id,oldpage)::tail').


  Definition page_alloc (p:page) (m: pages) : pages :=
    cons (length m, p) m.


End Pages.
