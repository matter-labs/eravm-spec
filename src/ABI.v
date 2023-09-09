Require Coder Ergs Pointer GPR MemoryManagement lib.BitsExt.

Import ssreflect ssreflect.ssrfun ssreflect.ssrbool ssreflect.eqtype ssreflect.tuple zmodp.
Import Core Common Coder Bool GPR Ergs Memory MemoryManagement Pointer.


(** # Application binary interface (ABI)

This section details the serialization and deserialization formats for compound
instruction arguments.


Currently, they are not described in details, but introduced axiomatically.

The description from Rust VM implementation is described here:
https://github.com/matter-labs/zkevm_opcode_defs/blob/v1.4.1/src/definitions/abi

## Fat pointers *)
Require Export
  ABI.FatPointerABI
  ABI.MetaParametersABI
  ABI.PrecompileParametersABI
  ABI.NearCallABI
  ABI.FarRetABI
  ABI.FarCallABI
.
