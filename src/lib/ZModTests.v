Require ZMod.

Import ZMod ZArith List ListNotations.

Let test_rols seed := List.map (fun i => int_val _ (rol _ (int_mod_of 4 seed) (int_mod_of _ i) ) ).
Open Scope Z.
Check eq_refl: test_rols 1 [1;2;3;4;5] = [2; 4; 8; 1; 2].
Check eq_refl: test_rols 3 [1;2;3;4;5] = [6; 12; 9; 3; 6].

Compute rol _ (int_mod_of 4 4%Z) (int_mod_of 4 1%Z).
Compute rol _ (int_mod_of 4 4%Z) (int_mod_of 4 3%Z).

Check eq_refl: (1027%Z = int_val _ ( mix_lower _ (int_mod_of _ 1025) (int_mod_of 8 3))).
