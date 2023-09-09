From ExtLib Require Import ExtLib Show.
From Bits Require Import spec.
Require Pointer.

Import Coq.Strings.String Bool Ascii Show.
Import ShowNotation.
Import Pointer Types.

Section ShowInstances.

  Open Scope show_scope.
  Global Instance bits_Show : forall n, Show (BITS n):=
    { show b := toHex b }.

  Compute to_string zero32.
  #[local]
    Open Scope string.
  #[global]
    Instance span_Show : Show span :=
    { show s :=
        match s with
        | mk_span s l => ("[" ++ to_string s ++ ", " ++ to_string s ++ " + " ++ to_string l ++ ")")%string
        end
    }.

  #[global]
    Instance free_ptr_Show : Show free_ptr :=
    { show p :=
        match p with
        | mk_ptr s ofs => "offset " ++ to_string ofs ++ " in " ++ to_string s
        end
    }.

  #[global]
    Instance fat_ptr_Show : Show fat_ptr :=
    { show p :=
        match p with
        | mk_fat_ptr page fp => "fat ptr to page " ++ to_string page ++ ", " ++ to_string fp
        end
    }.

  #[global]
    Instance fat_ptr_nullable_Show : Show fat_ptr_nullable :=
    { show p :=
        match p with
        | NullPtr => "NullPtr"
        | NotNullPtr ptr => to_string ptr
        end
    }.


  #[global]
    Instance option_Show {T} `{Show T}: Show (option T) :=
    { show o :=
        match o with
        | Some e=> show e
        | None => "None"
        end
    }.
(* Examples:

```
Compute (to_string (FatPointerABI.ABI.(decode) (zero32 ## zero32 ## @fromNat 32 1  ## zero32))).
Compute to_string (NotNullPtr (mk_fat_ptr #(1) (mk_ptr (mk_span zero32 #(92)) zero32))).
```
 *)
End ShowInstances.
