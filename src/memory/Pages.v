Require Common MemoryBase.
Import Common MemoryBase.

Section Pages.
  (** # Main memory (transient)
## Memory structure

Contract execution routinely uses **main memory** to hold instructions, stack,
heaps, and constants.

When the execution of a contract starts, new pages are allocated for:

- contract code: [%code_page], fetched by decommitter; see [%Decommitter] and
  [%FarCallDefinitions]);
- data stack: [%stack_page];
- heap: [%data_page];
- aux_heap: [%data_page];
- constants: [%const_page], implementation may chose to allocate code and
  constants on the same page.

Therefore, the types of pages are: data pages, stack pages, constant data pages,
and code pages. **)

  Context {code_page const_page data_page stack_page: Type}.

  Inductive page_type :=
  | DataPage : data_page -> page_type
  | StackPage : stack_page -> page_type
  | ConstPage : const_page -> page_type
  | CodePage : code_page -> page_type
  .

  Record page := mk_page {
                     type:> page_type
                   }.
  (** **Memory** is a collection of pages [%memory], each page is attributed a
    unique identifier [%page_id]. Pages persist for as long as they can be read
    by some code; in presence of [%FatPointer] the page lifetime may exceed the
    lifetime of the frame that created it. *)

  Definition page_id := nat.
  Definition pages := list (page_id * page).
  Record memory := mk_pages {
                       mem_pages:> pages;
                     }.

  Inductive page_has_id : memory -> page_id -> page -> Prop :=
  | mpid_select : forall mm id page,
      List.In (id, page) mm ->
      page_has_id (mk_pages mm) id page.

  (** The set of identifiers has a complete linear order, ordering the pages
    by the time of creation. The ability to distinguish older pages from newer
    is necessary to prevent returning fat pointers to pages from older frames.
    See e.g. [% step_RetExt_ForwardFatPointer]. *)
  Section Order.
    Definition page_ordering := Nat.leb.
    Definition page_eq x y := page_ordering x y && page_ordering y x.
    Definition page_neq x y := negb (page_eq x y).
    Definition page_older (id1 id2: page_id) : bool :=
      page_ordering id1 id2.
  End Order.

  (** Predicate [%page_replace] describes a relation between two memories
    [%m1] and [%m2], where [%m2] is a copy of [%m1] but a page with it [%id] is
    replaced
    by another page [%p].*)
  Inductive page_replace_list (id:page_id) (p:page): pages -> pages -> Prop :=
  | mm_replace_base: forall oldpage newpage tail,
      page_replace_list id p ((id, oldpage)::tail) ((id,newpage)::tail)
  | mm_replace_ind: forall oldpage not_id tail tail',
      page_replace_list id p tail tail' ->
      id <> not_id ->
      page_replace_list id p ((not_id,oldpage)::tail) ((not_id,oldpage)::tail').

  Inductive page_replace (id:page_id) (p:page): memory -> memory -> Prop :=
  | prl_apply: forall ls ls',
      page_replace_list id p ls ls' ->
      page_replace id p (mk_pages ls) (mk_pages ls').

  (** Function [%page_alloc] creates a new page in memory. *)
  Definition page_alloc (p:page) (m: memory) : memory :=
    let new_id := length (mem_pages m) in
    match m with
    | mk_pages mem_pages => mk_pages (cons (new_id, p) mem_pages)
    end.

End Pages.
