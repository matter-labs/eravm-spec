Require ZArith lib.ZMod.

Section Types.
  Import ZArith lib.ZMod.
  Let mk n := int_mod_of n.

  Definition u8 := int_mod 8.
  Definition u8_of := mk 8.

  Definition u16 := int_mod 16.
  Definition u16_of := mk 16.

  Definition u24 := int_mod 24.
  Definition u24_of := mk 24.

  Definition u32 := int_mod 32.
  Definition u32_of := mk 32.

  Definition u64 := int_mod 64.
  Definition u64_of := mk 64.

  Definition u128 := int_mod 128.
  Definition u128_of := mk 128.

  Definition u160 := int_mod 160.
  Definition u160_of := mk 160.

  Definition u256 := int_mod 256.
  Definition u256_of := mk 256.


  Definition zero8   := u8_of 0.
  Definition zero16  := u16_of 0.
  Definition zero24  := u24_of 0.
  Definition zero32  := u32_of 0.
  Definition zero64  := u64_of 0.
  Definition zero128 := u128_of 0.
  Definition zero160 := u160_of 0.
  Definition zero256 := u256_of 0.
End Types.
