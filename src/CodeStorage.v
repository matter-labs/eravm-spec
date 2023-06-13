Require Common Memory ABI lib.Decidability Log VersionedHash.

Import Log VersionedHash Common Decidability Ergs Memory MemoryBase ZArith ZMod ABI.
(** A separate code storage. It is an abstraction, because in the current *)
(** implementation it is a part of a decommitter. *)

Definition DEPLOYER_SYSTEM_CONTRACT_ADDRESS : contract_address
  := (ZMod.int_mod_of _ (2^15))%Z.

Section Defs.
  Variable ins_type: Type.
  Variable invalid_ins: ins_type.

  Let code_page := code_page ins_type invalid_ins.

  Definition code_storage_params := {|
                                     addressable_block := code_page;
                                     address_bits := 256;
                                     default_value := empty _;
                                     writable := false;
                                   |}.

  Definition code_storage: Type := mem_parameterized code_storage_params.

  Record code_manager :=
    mk_code_mgr {
        cm_storage: code_storage;
        cm_fresh: log versioned_hash;
      }.


  Definition is_fresh cm vh := negb (contains _ VersionedHash.eq_dec (cm_fresh cm) vh).

  Inductive code_fetch_no_masking: shard -> code_storage
                        -> contract_address -> (versioned_hash * code_page * code_length) -> Prop :=
  | cfnm_load : forall (contracts:shard) (called_address:contract_address) deployer_storage hash_enc (code_storage:code_storage) code_length_in_words extra_marker partial_hash page_init,
      load_result _ DEPLOYER_SYSTEM_CONTRACT_ADDRESS contracts deployer_storage ->
      load_result storage_params (@resize _ 256 called_address) deployer_storage hash_enc ->
      hash_enc <> zero256 ->
      hash_coder.(decode) hash_enc = Some (mk_vhash code_length_in_words extra_marker partial_hash) ->
      marker_valid extra_marker = true ->
      load_result (code_storage_params) (@resize _ 256 partial_hash) code_storage page_init ->
      code_fetch_no_masking contracts code_storage called_address ((mk_vhash code_length_in_words extra_marker partial_hash), page_init,code_length_in_words).

  Inductive code_fetch_shard: bool -> shard -> code_storage -> contract_address -> (versioned_hash * code_page * code_length) -> Prop :=
  | cfh_load is_masking_allowed: forall (contracts:shard) (called_address:contract_address) (code_storage:code_storage) code_length_in_words extra_marker partial_hash page_init,
      code_fetch_no_masking contracts code_storage called_address ((mk_vhash code_length_in_words extra_marker partial_hash), page_init,code_length_in_words) ->
      code_fetch_shard is_masking_allowed contracts code_storage called_address ((mk_vhash code_length_in_words extra_marker partial_hash), page_init,code_length_in_words)

  | cfh_load_aa_default : forall (contracts:shard) (called_address:contract_address) deployer_storage (code_storage:code_storage),
      load_result _ DEPLOYER_SYSTEM_CONTRACT_ADDRESS contracts deployer_storage ->
      load_result storage_params (@resize _ 256 called_address) deployer_storage zero256->
      code_fetch_shard true contracts code_storage called_address (DEFAULT_AA_VHASH, DEFAULT_AA_CODE _ invalid_ins,code_length_in_words DEFAULT_AA_VHASH).

  Inductive code_fetch (depot:depot) (sid: shard_id): bool -> code_storage -> contract_address ->
                                                      (versioned_hash * code_page * code_length) -> Prop :=
| cfs_fetch: forall masking_allowed sh codes addr vh,
    load_result _ sid depot sh ->
    code_fetch_shard masking_allowed sh codes addr vh ->
    code_fetch depot sid masking_allowed codes addr vh .
  
    
End Defs.
