Require memory.Depot ABI State.

Import ABI memory.Depot State.

Section Precompiles.
  (** # Precompiles

Precompiles are extensions of VM bound to one of the system contracts.
When this contract executes an instruction [%OpPrecompileCall], VM executes an
algorithm specific to this contract.

This requires preparing data for the precompiled algorithm in a special,
algorithm-dependent way.

Precompiles are able to change [%data_page]s.

Precompiles may fail.

Precompiles are not revertable; their functioning is not affected by rollbacks.

Currently we formalize precompiles as a black box.
   *)
  Parameter precompile_processor : contract_address -> PrecompileParametersABI.params -> transient_state -> transient_state -> Prop.
End Precompiles.
