Require FMapPositive.

Import FMapPositive.PositiveMap BinPos.

Definition pmap_slice {V} (m:t V) (from_incl to_excl:positive ) : t V :=
  let leb x y := negb (Pos.ltb y x) in
  let in_range k := andb (leb from_incl k) (Pos.ltb k to_excl) in
  let f k cell accmap :=
    if in_range k 
    then
      add k cell accmap
    else
      accmap
    in
  fold f m (empty _).
