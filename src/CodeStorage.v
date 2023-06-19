Require Common ABI lib.Decidability Log MemoryOps VersionedHash.

Import Log VersionedHash Common Decidability Ergs MemoryOps Memory MemoryBase ZArith ZMod ABI.
(** A separate code storage. It is an abstraction, because in the current *)
(** implementation it is a part of a decommitter. *)

Definition DEPLOYER_SYSTEM_CONTRACT_ADDRESS : contract_address
  := (ZMod.int_mod_of _ (2^15))%Z.

Section Defs.
  Context {ins_type: Type} (invalid_ins: ins_type).

  Let code_page := code_page invalid_ins.

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

  Definition code_hash_location (for_contract: contract_address) (sid:shard_id): fqa_key :=
      mk_fqa_key (mk_fqa_storage sid DEPLOYER_SYSTEM_CONTRACT_ADDRESS) (resize _ 256 for_contract).
  
  Inductive code_fetch_hash (d:depot) (cs: code_storage) (sid: shard_id) (contract_addr: contract_address) :
   option (versioned_hash * code_length) -> Prop :=
 |cfh_found: forall hash_enc code_length_in_words extra_marker partial_hash,
      storage_read d (code_hash_location contract_addr sid) hash_enc ->
      hash_enc <> zero256 ->
      marker_valid extra_marker = true ->
      hash_coder.(decode) hash_enc = Some (mk_vhash code_length_in_words extra_marker partial_hash) ->
      code_fetch_hash d cs sid contract_addr (Some (mk_vhash code_length_in_words extra_marker partial_hash, code_length_in_words))

  | cfh_not_found:
      storage_read d (code_hash_location contract_addr sid) zero256 ->
      code_fetch_hash d cs sid contract_addr None.
                        
  
  Inductive code_fetch  (d:depot) (cs: code_storage) (sid: shard_id) (contract_addr: contract_address) :
    bool -> (versioned_hash * code_page * code_length) -> Prop :=
  | cfnm_no_masking: forall vhash (code_storage:code_storage) code_length_in_words page_init masking,
      code_fetch_hash d cs sid contract_addr (Some (vhash, code_length_in_words)) ->
      load_result code_storage_params (resize _ 256 (partial_hash vhash)) code_storage page_init ->
      
      code_fetch d cs sid contract_addr masking (vhash, page_init, code_length_in_words) 
  | cfnm_masking: forall (code_storage:code_storage) code_length_in_words,
      code_fetch_hash d cs sid contract_addr None ->
      code_fetch d cs sid contract_addr true (DEFAULT_AA_VHASH, DEFAULT_AA_CODE _ invalid_ins,code_length_in_words).

  
    
End Defs.

        
