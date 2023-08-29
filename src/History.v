Require Common.

Section History.
  Import ssreflect ssrfun ssrbool eqtype ssreflect.tuple seq.
  (** # History
**History** is a data structure supporting appending elements of type [%T] to it.
   *)
  Context (T:eqType).

  Definition history := seq T.

  Context (l:history).

  (** [%history] supports checking if an element is contained in it. *)
  Definition contains (elem:T): bool := if has (fun e => e == elem) l then true else false.

End History.
