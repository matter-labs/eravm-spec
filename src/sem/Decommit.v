From RecordUpdate Require Import RecordSet.

Require SemanticCommon.

Import Addressing Bool Core Common Predication GPR CallStack TransientMemory MemoryOps isa.CoreSet State
  PrimitiveValue SemanticCommon RecordSetNotations.

Section DecommitDefinition.


  Inductive step_decommit: @instruction decoded -> smallstep :=
(** # Decommit

## Summary

Decommit code into memory.

TODO

## Abstract Syntax

[%OpDecommit (in1: in_reg) (in2: in_reg) (out1: out_reg)]

## Syntax

`dcmt in1, in2, out1`

## Legacy Syntax

`decommit in1, in2, out1`


## Semantic

FIXME

 *)
    (* FIXME: no semantic yet *)
| step_decommit_apply:
  forall src0 src1 dst0 (s: state),

    step_decommit (OpDecommit src0 src1 dst0) s s.

(** ## Affected parts of VM state

- execution stack: PC is overwritten with a new value.

## Usage

- Load the contract code

## Similar instructions

- Instructions [%OpSStore], [%OpSLoad], [%OpTransientStore], [%OpTransientLoad],
  [%OpToL1Msg], [%OpEvent] have the same opcode.

*)

End DecommitDefinition.
