(**
 # Primitive values

**Primitive value** is a tagged word. The tag shows that the word contains a
  valid fat pointer (see [%fat_ptr]) and can be used in instructions that
  require pointer argument, for example [%OpPtrShrink].

Only registers and stack hold primitive values; other types of memory, including storage, holds non-tagged words.
 *)

Section PrimitiveValue.
Context {word:Type}.
Inductive primitive_value :=
  mk_pv {
      is_ptr: bool;
      value: word;
    }.

(** Function [%clear_pointer_tag] clears the pointer tag of a primitive value. *)
Definition clear_pointer_tag (pv:primitive_value): primitive_value :=
  match pv with | mk_pv _ value => mk_pv false value end.

End PrimitiveValue.

(** For brevity, we will call a primitive value **a pointer value** if its tag
is set, and **integer value** otherwise. *)
Notation IntValue := (mk_pv false).
Notation PtrValue := (mk_pv true).
