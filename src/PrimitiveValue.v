Require Types.

Section PrimitiveValue.
(**
# Primitive values

**Primitive value** is a tagged word.
The tag [%is_ptr] is a boolean.

- If [%is_ptr] is set, it is guaranteed that the lowest 128-bits of the word contain a serialized [%fat_ptr].
Such values can be used as operands in instructions that require pointer arguments, for example, [%OpPtrAdd]. The other half (128 most significant bits) may hold meaningful data, e.g. when forming a value according to FarCall ABI using [%Assembly.OpPtrPack] instruction.
- If [%is_ptr] is cleared, there are no guarantees to its value. It may contain an integer, a representation of a [%heap_ptr], a representation of a [%span] of addresses, etc.

*)

Context {word:Type}.
Inductive primitive_value :=
  mk_pv {
      is_ptr: bool;
      value: word;
    }.

(**
Only [%Registers] and [%stack_page]s hold primitive values; other types of memory, including storage and heap pages, contain non-tagged data.

Function [%clear_pointer_tag] clears the pointer tag of a primitive value. *)
Definition clear_pointer_tag (pv:primitive_value): primitive_value :=
  match pv with | mk_pv _ value => mk_pv false value end.

End PrimitiveValue.

(** For brevity, a primitive value is called **a pointer value** if its tag
is set, and **integer value** otherwise. *)
Notation IntValue := (mk_pv false).
Notation PtrValue := (mk_pv true).

Definition pv0 := IntValue Types.zero256.
