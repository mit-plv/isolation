Require Import koikaExamples.KoikaConversion.
Require Koika.Syntax.
Require Koika.Frontend.

Require Import rv_cache_isolation.Common.
Require Import rv_cache_isolation.Machine.
Require Import rv_cache_isolation.rv32.
Require Import rv_cache_isolation.SecurityMonitor.
Require Import Koika.Types.
Require Import koika.Frontend.
Require Koika.Vect.
Require Import koikaExamples.EnclaveWithCache.Common.

Module KEnclaveParams (EnclaveParams: EnclaveParams_sig) <: rv_cache_isolation.Common.EnclaveParams_sig.
  Import EnclaveParams.
  Definition enclave_base : enclave_id -> bits_t 32 :=
    fun eid => eq_rect _ _ (vect_of_list (enclave_sig.(_enclave_base) eid))  _ (wf_sig.(wf_enclave_base _) eid).

  Definition enclave_size : enclave_id -> bits_t 32 :=
    fun eid => eq_rect _ _ (vect_of_list (enclave_sig.(_enclave_size) eid))  _ (wf_sig.(wf_enclave_size _) eid).

  Definition enclave_bootloader_addr : enclave_id -> bits_t 32 :=
    fun eid => eq_rect _ _ (vect_of_list (enclave_sig.(_enclave_bootloader_addr) eid))  _ (wf_sig.(wf_bootloader_addr _) eid).

  Definition shared_region_base : shared_id -> bits_t 32 :=
    fun sid => eq_rect _ _ (vect_of_list (enclave_sig.(_shared_region_base) sid))  _ (wf_sig.(wf_shared_base _) sid).

  Definition shared_region_size : type_denote (bits_t 32) :=
    eq_rect _ _ (vect_of_list (enclave_sig.(_shared_region_size) ))  _ (wf_sig.(wf_shared_size _) ).

  Definition core_init0 : rv_cache_isolation.Common.core_init_params_t :=
    {| rv_cache_isolation.Common.machine_pc :=
        eq_rect _ _ (vect_of_list (enclave_sig.(_core_init0).(machine_pc)))  _ (wf_sig.(wf_core_init0 _));
      rv_cache_isolation.Common.machine_config := enclave_sig.(_core_init0).(machine_config)
    |}.
  Definition core_init1 : rv_cache_isolation.Common.core_init_params_t :=
    {| rv_cache_isolation.Common.machine_pc :=
        eq_rect _ _ (vect_of_list (enclave_sig.(_core_init1).(machine_pc)))  _ (wf_sig.(wf_core_init1 _));
      rv_cache_isolation.Common.machine_config := enclave_sig.(_core_init1).(machine_config)
    |}.

  Definition enclave_params: rv_cache_isolation.Common.enclave_params_sig :=
  {| rv_cache_isolation.Common._enclave_base := enclave_base;
     rv_cache_isolation.Common._enclave_size := enclave_size;
     rv_cache_isolation.Common._enclave_bootloader_addr := enclave_bootloader_addr;
     rv_cache_isolation.Common._shared_region_base := shared_region_base;
     rv_cache_isolation.Common._shared_region_size := shared_region_size;
     rv_cache_isolation.Common._core_init0 := core_init0;
     rv_cache_isolation.Common._core_init1 := core_init1
  |}.
End KEnclaveParams.

Module DummyEnclaveParams <: rv_cache_isolation.Common.EnclaveParams_sig.
  Definition enclave_params :=
    {| rv_cache_isolation.Common._enclave_base := fun _ => @Bits.zero 32;
       rv_cache_isolation.Common._enclave_size := fun _ => @Bits.zero 32;
       rv_cache_isolation.Common._enclave_bootloader_addr := fun _ => @Bits.zero 32;
       rv_cache_isolation.Common._shared_region_base := fun _ => @Bits.zero 32;
       rv_cache_isolation.Common._shared_region_size := @Bits.zero 32;
       rv_cache_isolation.Common._core_init0 :=
        {| rv_cache_isolation.Common.machine_pc := @Bits.zero 32;
          rv_cache_isolation.Common.machine_config := None
        |};
       rv_cache_isolation.Common._core_init1 :=
        {| rv_cache_isolation.Common.machine_pc := @Bits.zero 32;
          rv_cache_isolation.Common.machine_config := None
        |};
    |}.
End DummyEnclaveParams.


Definition reg_t := SecurityMonitor.reg_t.
Definition ext_fn_t := rv_cache_isolation.Common.ext_fn_t.
Existing Instance SecurityMonitor.Show_reg_t.
Existing Instance SecurityMonitor.Show_ext_fn_t.
Existing Instance SecurityMonitor.FiniteType_reg_t.
Existing Instance FiniteType_ext_fn_t.
Instance Show_rule' : Koika.Show.Show rule_name_t := _.
Instance Show_rule : Show rule_name_t :=
  { show := Show_rule'.(Koika.Show.show) }.

Definition reg_to_debug_id (r: reg_t) : debug_id_ty :=
    (Show.show r, N.of_nat (FiniteType.finite_index r)).
Definition ext_fn_to_debug_id (extfn: ext_fn_t) : debug_id_ty :=
    (Show.show extfn, N.of_nat (FiniteType.finite_index extfn)).
Module DummyMachine := Machine DummyEnclaveParams.
Definition struct_sigs :=
  Eval vm_compute in (get_scheduler_structs DummyMachine.R Sigma DummyMachine.rules DummyMachine.schedule).
Definition struct_defs := Eval vm_compute in
    ltac:(_extract_success (struct_sig_to_struct_env struct_sigs)).
Instance EqDec_rule_name_t : EqDec rule_name_t := _.
Definition id_struct_defs := (id_transform_struct_env _id struct_defs).
Definition R := DummyMachine.R.
Definition reg_types : reg_types_t :=
  Eval vm_compute in
    (map (fun r => ((reg_to_debug_id r), Types.type_sz (R r))) (@FiniteType.finite_elements _ FiniteType_reg_t)).
Definition _reg_types : reg_types_t :=
  Eval vm_compute in (id_transform_reg_types _id reg_types).
Definition ext_fn_tys : ext_fn_types_t :=
  Eval vm_compute in
    (map (fun ext => ((ext_fn_to_debug_id ext),(type_sz (Sigma ext).(arg1Sig), type_sz ((Sigma ext).(retSig)))))
        (@FiniteType.finite_elements _ FiniteType_ext_fn_t)).
Definition _ext_fn_tys := Eval vm_compute in id_transform_ext_fn_types _id ext_fn_tys.
Definition int_fns : @int_fn_env_t debug_id_ty (@action debug_id_ty):= [].
Definition id_int_fns : @int_fn_env_t N (@action N):= id_transform_int_fn_env _id int_fns.
Definition reg_list := Eval vm_compute in (map reg_to_debug_id (@FiniteType.finite_elements _ FiniteType_reg_t)).
Definition _reg_list := Eval vm_compute in (map _id reg_list).
Definition lookup_reg := nth_error reg_list.



Definition lookup_struct (s: string) : result struct_t unit :=
  match find (fun s' => beq_dec (fst s'.(dstruct_name)) s ) struct_defs with
  | Some v => Success v
  | None => Failure tt
  end.

Definition _lookup_struct (s: struct_sig) : result struct_t unit :=
  lookup_struct (s.(Types.struct_name)).

Definition struct_sz (s: struct_sig) : result nat unit :=
  match _lookup_struct s with
  | Success s => Success (struct_sz s)
  | _ => Failure tt
  end.


Definition _unsafe_struct_sz (s: struct_sig) : nat :=
  success_or_default (struct_sz s) 0.


Definition struct_sig_to_id (s: string) : result debug_id_ty unit :=
  let/res s := lookup_struct s in
  Success s.(dstruct_name).
Definition _struct_sig_to_id (s: struct_sig) : result debug_id_ty unit :=
  let/res s := _lookup_struct s in
  Success s.(dstruct_name).

Definition lookup_field_idx (s: @struct_t debug_id_ty) (fld: string) : result debug_id_ty unit :=
  match find (fun '(f, _) => beq_dec (fst f) fld) s.(dstruct_fields) with
  | Some (f, _) => Success f
  | None => Failure tt
  end.
Definition _sid s := (success_or_default (_struct_sig_to_id s) ("ERROR", 0%N)).

Definition unsafe_lookup_field_idx (s: @struct_t debug_id_ty) (fld: string) : debug_id_ty :=
  success_or_default (lookup_field_idx s fld) ("ERROR", 0%N).


Definition unsafe_field_map
  {X} (s: @struct_t debug_id_ty) (flds: list (string * X)) : list (debug_id_ty * X) :=
  map (fun '(f, v) => (unsafe_lookup_field_idx s f, v)) flds.

Definition struct_init (s: string) (flds: list (string * vect_t)) : result vect_t unit :=
  let/res s := lookup_struct s in
  Semantics.struct_init s (unsafe_field_map s flds).

Definition _struct_init (s: struct_sig) (flds: list (string * vect_t))
                        : result vect_t unit :=
  struct_init s.(Types.struct_name) flds.

Definition get_field (s: string) (fld: string) (v: vect_t) : result vect_t unit :=
  let/res s := lookup_struct s in
  get_field s.(dstruct_fields) (unsafe_lookup_field_idx s fld) v.

(* Arguments get_field : simpl _ _ _. *)
(* Lemma foo: *)
(*   get_field "mem_output" "get_valid" [] = Success []. *)
(* Proof. *)
(*   intros.  *)
(*   match goal with *)
(*   | |- context C[get_field ?X ?Y ?Z] => *)
(*       let T := constr:(get_field X Y Z) in *)
(*       let T' := eval cbn in T in *)
(*       let G := context C[T'] in *)
(*       change G *)
(*       (* change T with T' *) *)
(*       (* cbn [get_field] *) *)
(*   end. *)

Definition _get_field (s: struct_sig) (fld: string) (v: vect_t) : result vect_t unit :=
  get_field s.(Types.struct_name) fld v.

Definition _unsafe_get_field (s: struct_sig) (fld: string) (v: vect_t) : vect_t :=
  success_or_default (_get_field s fld v) [].

Definition _ext fn := (_id (ext_fn_to_debug_id fn)).
Definition _extid fn := (ext_fn_to_debug_id fn).


Definition _unsafe_get_ext_call_from_log (log: ext_log_t) (fn: ext_fn_t) : vect_t :=
  unsafe_get_ext_call_from_log _ext_fn_tys log (_ext fn).

Definition lookup_enum (s: Types.enum_sig) (fld: string) : result (list bool) unit :=
  match vect_index fld s.(enum_members) with
  | Some idx => Success (vect_to_list (vect_nth s.(enum_bitpatterns) idx))
  | None => Failure tt
  end.

Definition _enum (s: Types.enum_sig) (fld: string) : (list bool)  :=
  success_or_default (lookup_enum s fld) [].

Definition _rid reg := (_id (reg_to_debug_id reg)).
Definition _fld (s: Types.struct_sig) (fld: string) :=
    success_or_default (let/res sid := _lookup_struct s in lookup_dstruct_field sid fld) ("ERROR", 0%N).


Definition core0_schedule := Eval vm_compute in ltac:(_extract_success (convert_scheduler DummyMachine.lifted_core0_schedule)).
Definition core1_schedule := Eval vm_compute in
      ltac:(_extract_success (convert_scheduler DummyMachine.lifted_core1_schedule)).
Definition mem_schedule := Eval vm_compute in ltac:(_extract_success (convert_scheduler DummyMachine.lifted_mem_schedule)).
Definition sm_schedule := Eval vm_compute in ltac:(_extract_success (convert_scheduler DummyMachine.lifted_sm_schedule)).
Definition schedule := Eval vm_compute in ltac:(_extract_success (convert_scheduler DummyMachine.schedule)).
  Definition modular_schedule : list (@scheduler rule_name_t) :=
    [core0_schedule; core1_schedule; mem_schedule; sm_schedule ].

Lemma _reg_types_sorted : sorted (map fst _reg_types) = true. Proof. constructor. Qed.
Definition reg_type_env := SortedRegEnv.from_list _reg_types _reg_types_sorted.

Module Type Impl (EnclaveParams: EnclaveParams_sig).
  Module EnclaveParams' <: rv_cache_isolation.Common.EnclaveParams_sig := KEnclaveParams EnclaveParams.
  Module Machine := Machine EnclaveParams'.
  Import Machine.SM. Import Machine.

  (* Existing Instance Machine.FiniteType_reg_t. *)
  (* Existing Instance Machine.Show_reg_t. *)
  (* Existing Instance Machine.Show_ext_fn_t. *)
  (* Definition struct_sigs' := Eval vm_compute in (get_scheduler_structs R Sigma Machine.rules schedule). *)
  Lemma struct_sigs_eq:  struct_sigs = (get_scheduler_structs R Sigma Machine.rules schedule).
  Proof. vm_reflect. Qed.

  (* Definition struct_defs := Eval vm_compute in ltac:(_extract_success (struct_sig_to_struct_env struct_sigs)). *)
  Definition rules_list : (list (rule_name_t * (@action debug_id_ty))) :=
    Eval vm_compute in
ltac:(_extract_success (convert_schedule R Sigma reg_to_debug_id ext_fn_to_debug_id struct_sigs Machine.rules schedule)).

  Definition rules (rl: rule_name_t) : @action debug_id_ty :=
    match find (fun '(rl', _) => beq_dec rl' rl) rules_list with
    | Some (_, rl) => rl
    | _ => Fail 0
    end.
  Definition id_rules (rl: rule_name_t) : @action N:=
    id_transform_action snd (rules rl).

End Impl.

Module ExternalMemory.
  Record mem_resp_t :=
    { mem_resp_byte_en : vect_t;
      mem_resp_addr : vect_t;
      mem_resp_data : vect_t
    }.

  Record external_cache_t :=
    { ext_cache_resp: option vect_t; (* cache_req_sig *)
      ext_cache: cache_sram_t
    }.

  Record external_metadata_t :=
    { ext_metadata_resp: option vect_t; (* metadata_req_sig *)
      ext_metadata: metadata_sram_t
    }.

  Record external_mainmem_t :=
    { ext_resp: option mem_resp_t; (* previous req *)
      ext_mem: dram_t
    }.

  Record external_cache_pair_t :=
    { ext_pair_cache : external_cache_t;
      ext_pair_meta  : external_metadata_t
    }.

  Record external_mem_t :=
    { ext_main_mem: external_mainmem_t;
      ext_l1_caches: mem_type -> ind_core_id -> external_cache_pair_t;
    }.

  Definition initial_cache : external_cache_t :=
    {| ext_cache_resp := None; ext_cache := fun _ => Some (zeroes 32)|}.
  Definition initial_metadata : external_metadata_t :=
    {| ext_metadata_resp := None; ext_metadata := fun _ => Some (zeroes (_unsafe_struct_sz metadata_sig)) |}.
  Definition initial_cache_pair: external_cache_pair_t :=
    {| ext_pair_cache := initial_cache;
       ext_pair_meta := initial_metadata
    |}.

  Definition initial_mem (dram: dram_t) : external_mem_t :=
    {| ext_main_mem := {| ext_resp := None; ext_mem := dram |};
       ext_l1_caches := fun _ _ => initial_cache_pair
    |}.

  Definition mem_get_response__koika (mem: external_mainmem_t) : result vect_t unit :=
    match mem.(ext_resp) with
    | Some resp =>
        let/res resp_vect := _struct_init mem_resp
                                         [("byte_en", resp.(mem_resp_byte_en))
                                         ;("addr", resp.(mem_resp_addr))
                                         ;("data", resp.(mem_resp_data))] in
        _struct_init mem_output
                      [("get_valid", [true])
                      ;("put_ready", [true] (* don't care? *) )
                      ;("get_response", resp_vect)]
    | None => Success (zeroes (_unsafe_struct_sz mem_output))
    end.

  Definition update_dram (req:vect_t) (dram: dram_t) : result external_mainmem_t unit :=
    let/res addr := _get_field mem_req "addr" req in
    let/res data := _get_field mem_req "data" req in
    let/res byte_en := _get_field mem_req "byte_en" req in
    let address_n := to_N addr in
    if beq_dec (byte_en) Ob~0~0~0~0 then
      Success {| ext_resp := Some {| mem_resp_byte_en := byte_en;
                                     mem_resp_addr := addr;
                                     mem_resp_data := match dram (to_N addr) with
                                                      | Some data => data
                                                      | _ => zeroes 32
                                                      end
                                  |};
                 ext_mem := dram
              |}
    else Success {| ext_resp := None;
                    ext_mem := (fun r => if beq_dec address_n r then Some data else dram r)
                 |}.

  Definition mainmem__ext (obs_mainmem: vect_t) (mem: external_mainmem_t): result external_mainmem_t unit :=
    let/res put_valid := _get_field mem_input "put_valid" obs_mainmem in
    let/res put_request := _get_field mem_input "put_request" obs_mainmem in
    match put_valid with
    | [true] => update_dram put_request mem.(ext_mem)
    | [false] => Success {| ext_resp := None; ext_mem := mem.(ext_mem) |}
    | _ => Failure tt
    end.

  Definition cache_get_response__koika (input: vect_t) (cache: external_cache_t) : result vect_t unit :=
    let/res get_ready := _get_field cache_input_sig "get_ready" input in
    let/res put_request := _get_field cache_input_sig "put_request" input in
    let/res put_valid := _get_field cache_input_sig "put_valid" input in
    match cache.(ext_cache_resp), get_ready with
    | Some resp, [true] =>
        _struct_init cache_output_sig
                     [("get_valid", Ob~1)
                     ;("put_ready", put_valid)
                     ;("get_response", resp)
                     ]
    | Some resp, [false] => Success (zeroes (_unsafe_struct_sz cache_output_sig))
    | None, _ =>
         _struct_init cache_output_sig
                      [("get_valid", Ob~0)
                      ;("put_ready", put_valid)
                      ;("get_response", zeroes 32)
                      ]
    | _, _ => Failure tt
    end.

  (* Arbitrary function *)
  Definition compute_with_byte_en (byte_en new_value: vect_t) (old_value: option vect_t) : vect_t.
  Admitted.

  Axiom compute_with_byte_en_ok:
    forall byte_en new_value old_value,
    Datatypes.length (compute_with_byte_en byte_en new_value old_value) = 32.

  Axiom compute_with_byte_en_store:
    forall new_value old_value,
      compute_with_byte_en Ob~1~1~1~1 new_value old_value = new_value.

  Definition update_cache (req: vect_t) (cache: cache_sram_t) : result external_cache_t unit :=
    let/res addr := _get_field cache_req_sig "addr" req in
    let/res data := _get_field cache_req_sig "data" req in
    let/res byte_en := _get_field cache_req_sig "byte_en" req in
    let address_n := to_N addr in
    if beq_dec (byte_en) Ob~0~0~0~0 then
      let new_data := match cache address_n with
                      | Some data => data
                      | None => zeroes 32
                      end in
      Success {| ext_cache_resp := Some new_data;
                 ext_cache := cache
              |}
    else Success {| ext_cache_resp := None;
                    ext_cache := (fun r => if beq_dec address_n r
                                        then Some (compute_with_byte_en byte_en data (cache r))
                                        else cache r)
                 |}.

  Definition cache__ext (obs_cache: vect_t) (cache: external_cache_t) : result external_cache_t unit :=
    let/res put_valid := _get_field cache_input_sig "put_valid" obs_cache in
    let/res put_request := _get_field cache_input_sig "put_request" obs_cache in
    let/res get_ready := _get_field cache_input_sig "get_ready" obs_cache in
    match get_ready, put_valid with
    | [true], [true] => update_cache put_request cache.(ext_cache)
    | [true], [false] => Success {| ext_cache_resp := None; ext_cache := cache.(ext_cache)|}
    | [false], [true] =>
        match cache.(ext_cache_resp) with
        | Some resp => Success cache
        | None => update_cache put_request cache.(ext_cache)
        end
    | [false], [false] => Success cache
    | _, _ => Failure tt
    end.

  Definition metadata_get_response__koika (input: vect_t) (metadata: external_metadata_t) : result vect_t unit :=
    let/res get_ready := _get_field metadata_input_sig "get_ready" input in
    let/res put_request := _get_field metadata_input_sig "put_request" input in
    let/res put_valid := _get_field metadata_input_sig "put_valid" input in
    match metadata.(ext_metadata_resp), get_ready with
    | Some resp, [true] =>
        _struct_init metadata_output_sig
                     [("get_valid", Ob~1)
                     ;("put_ready", put_valid)
                     ;("get_response", resp)
                     ]
    | Some resp, [false] => Success (zeroes (_unsafe_struct_sz metadata_output_sig))
    | None, _ =>
         _struct_init metadata_output_sig
                      [("get_valid", Ob~0)
                      ;("put_ready", put_valid)
                      ;("get_response", zeroes (_unsafe_struct_sz metadata_sig))
                      ]
    | _, _ => Failure tt
    end.

  Definition update_metadata (req: vect_t) (metadata: metadata_sram_t) : result external_metadata_t unit :=
    let/res is_write := _get_field metadata_req_sig "is_write" req in
    let/res data := _get_field metadata_req_sig "data" req in
    let/res addr := _get_field metadata_req_sig "addr" req in
    let address_n := to_N addr in
    if beq_dec (is_write) Ob~0 then
      let new_data := match metadata address_n with
                      | Some data => data
                      | None => zeroes (_unsafe_struct_sz metadata_sig)
                      end in
      Success {| ext_metadata_resp := Some new_data;
                 ext_metadata := metadata
              |}
    else Success {| ext_metadata_resp := None;
                    ext_metadata := (fun r => if beq_dec address_n r then Some data else metadata r)
                 |}.

  Definition metadata__ext (obs_metadata: vect_t) (metadata: external_metadata_t) : result external_metadata_t unit :=
    let/res put_valid := _get_field metadata_input_sig "put_valid" obs_metadata in
    let/res put_request := _get_field metadata_input_sig "put_request" obs_metadata in
    let/res get_ready := _get_field metadata_input_sig "get_ready" obs_metadata in
    match get_ready, put_valid with
    | [true], [true] => update_metadata put_request metadata.(ext_metadata)
    | [true], [false] => Success {| ext_metadata_resp := None; ext_metadata := metadata.(ext_metadata)|}
    | [false], [true] =>
        match metadata.(ext_metadata_resp) with
        | Some resp => Success metadata
        | None => update_metadata put_request metadata.(ext_metadata)
        end
    | [false], [false] => Success metadata
    | _, _ => Failure tt
    end.

  Definition cachepair__ext (obs_metadata: vect_t) (obs_cache: vect_t)
                          (cachepair: external_cache_pair_t) : result external_cache_pair_t unit :=
    let/res cache' := cache__ext obs_cache cachepair.(ext_pair_cache) in
    let/res meta' := metadata__ext obs_metadata cachepair.(ext_pair_meta) in
    Success {| ext_pair_cache := cache';
               ext_pair_meta := meta'
            |}.

  Definition update_memory (mem_obs: mem_observations_t)
                           (mem: external_mem_t)
                           : result external_mem_t unit :=
    let/res mainmem := mainmem__ext mem_obs.(obs_mainmem) mem.(ext_main_mem) in
    let res_cache_pair mem_type core := cachepair__ext (mem_obs.(obs_meta) mem_type core)
                                                         (mem_obs.(obs_cache) mem_type core)
                                                         (mem.(ext_l1_caches) mem_type core) in
    let/res ext_cache_imem0 := res_cache_pair imem CoreId0 in
    let/res ext_cache_dmem0 := res_cache_pair dmem CoreId0 in
    let/res ext_cache_imem1 := res_cache_pair imem CoreId1 in
    let/res ext_cache_dmem1 := res_cache_pair dmem CoreId1 in
    Success {| ext_main_mem := mainmem;
               ext_l1_caches := fun mem_ty core =>
                                  match mem_ty, core with
                                  | imem, CoreId0 => ext_cache_imem0
                                  | dmem, CoreId0 => ext_cache_dmem0
                                  | imem, CoreId1 => ext_cache_imem1
                                  | dmem, CoreId1 => ext_cache_dmem1
                                  end |}.
End ExternalMemory.

Module TopLevelModuleHelpers.
  Definition get_ext_observations (ext_log: ext_log_t): external_observations_t :=
    {| obs_uart_write := _unsafe_get_ext_call_from_log ext_log ext_uart_write;
       obs_uart_read:= _unsafe_get_ext_call_from_log ext_log ext_uart_read;
       obs_led := _unsafe_get_ext_call_from_log ext_log ext_led;
       obs_finish := _unsafe_get_ext_call_from_log ext_log ext_finish
    |}.
  Definition enclave_config_to_enclave_request (config: enclave_config) : vect_t :=
    success_or_default (_struct_init enclave_req
                                     [("eid", enclave_id_to_vect config.(config_eid));
                                      ("shared_regions", shared_regions_to_vect config.(config_shared_regions));
                                      ("ext_uart", [config.(config_ext_uart)]);
                                      ("ext_led", [config.(config_ext_led)]);
                                      ("ext_finish", [config.(config_ext_finish)])]) [].
    Definition enclave_config_to_valid_enclave_data (config: enclave_config) : vect_t :=
      success_or_default (_struct_init enclave_data
                                       [("data", enclave_config_to_enclave_request config);
                                        ("valid", [true])]) [].

    Definition opt_enclave_config_to_enclave_data (opt_config: option enclave_config) : vect_t :=
      match opt_config with
      | Some config => enclave_config_to_valid_enclave_data config
      | None => zeroes (_unsafe_struct_sz enclave_data)
      end.
    Definition _reg_t (r: reg_t) : nat :=
      match find (fun '(r', _) => beq_dec (_rid r) r') _reg_types with
      | Some (_, t) => t
      | None => 0
      end.

    Definition r (params0: core_init_params_t) (params1: core_init_params_t)
                 (mem_turn: vect_t) (sm_clk: vect_t)
                 (reg: reg_t) : list bool :=
      match reg with
      | Core0 RVCore.Core.init_pc => params0.(machine_pc)
      | Core1 RVCore.Core.init_pc => params1.(machine_pc)
      | Core0 RVCore.Core.core_id => Ob~0
      | Core1 RVCore.Core.core_id => Ob~1
      | Core0 (RVCore.Core.rf (RVCore.Core.Rf.rData r)) =>
          match params0.(machine_rf) (Vect.index_to_nat r) with
          | Some v => slice 0 32 v
          | None => zeroes 32
          end
      | Core1 (RVCore.Core.rf (RVCore.Core.Rf.rData r)) =>
          match params1.(machine_rf) (Vect.index_to_nat r) with
          | Some v => slice 0 32 v
          | None => zeroes 32
          end
      | SM (enc_data CoreId0) => opt_enclave_config_to_enclave_data params0.(machine_config)
      | SM (enc_data CoreId1) => opt_enclave_config_to_enclave_data params1.(machine_config)
      | SM clk => sm_clk
      | Memory Memory.Memory.turn => mem_turn
      | _ => zeroes (_reg_t reg)
      end.

  Definition eid_vect_to_enclave_id (eid: vect_t): result enclave_id unit :=
    let id := to_nat eid in
    match id with
    | 0 => Success Enclave0
    | 1 => Success Enclave1
    | 2 => Success Enclave2
    | 3 => Success Enclave3
    | _ => Failure tt
    end.

  Definition shared_vect_to_shared_regions (sid: vect_t): shared_id -> bool :=
    fun id =>
    match id with
    | Shared01 => nth 0 sid false
    | Shared02 => nth 1 sid false
    | Shared03 => nth 2 sid false
    | Shared12 => nth 3 sid false
    | Shared13 => nth 4 sid false
    | Shared23 => nth 5 sid false
    end.
  Definition unsafe_enclave_req_to_config (req: vect_t) : enclave_config :=
    let eid := _unsafe_get_field enclave_req "eid" req in
    let shared := _unsafe_get_field enclave_req "shared_regions" req in
    let uart := _unsafe_get_field enclave_req "ext_uart" req in
    let led := _unsafe_get_field enclave_req "ext_led" req in
    let finish := _unsafe_get_field enclave_req "ext_finish" req in
    {| config_eid := success_or_default (eid_vect_to_enclave_id eid) Enclave0;
       config_shared_regions := shared_vect_to_shared_regions shared;
       config_ext_uart := beq_dec uart [true];
       config_ext_led := beq_dec led [true];
       config_ext_finish:= beq_dec finish [true];
   |}.
  Definition unsafe_enclave_data_to_config (data: vect_t) : enclave_config :=
    let req := _unsafe_get_field enclave_data "data" data in
    unsafe_enclave_req_to_config req.
  Definition observe_enclave_exit_from_enc_data (enc_data enc_data': vect_t)
                                                (enc_req': vect_t) : option enclave_config :=
      let enc_data_valid := _unsafe_get_field enclave_data "valid" enc_data in
      let enc_data_valid' := _unsafe_get_field enclave_data "valid" enc_data' in
      let enc_req'_valid := _unsafe_get_field enclave_data "valid" enc_req' in
      let enc_req'_data := _unsafe_get_field enclave_data "data" enc_req' in
      if beq_dec enc_data_valid [true] && beq_dec enc_data_valid' [false] then
        Some (unsafe_enclave_req_to_config enc_req'_data)
      else None.

  Definition observe_enclave_exit (core: ind_core_id) (st st': state_t) : (option enclave_config) :=
    observe_enclave_exit_from_enc_data
      st.[_rid (SM (enc_data core))]
      st'.[_rid (SM (enc_data core))]
      st'.[_rid (SM (enc_req core))].
  Lemma sorted_map_snd_reg_list:
    forall {B} (f: reg_t -> B),
      sorted (map fst (map (fun reg => (_id (reg_to_debug_id reg), f reg))
                         (@FiniteType.finite_elements _ SecurityMonitor.FiniteType_reg_t))) = true.
  Proof. constructor. Qed.

   Definition initial_koika_state (params0: core_init_params_t) (params1: core_init_params_t)
                                  (mem_turn sm_clk: list bool) : koika_state_t :=
    SortedRegEnv.from_list
      (map (fun reg => (_id (reg_to_debug_id reg), r params0 params1 mem_turn sm_clk reg))
            (@FiniteType.finite_elements _ SecurityMonitor.FiniteType_reg_t))
      (@sorted_map_snd_reg_list (list bool) (r params0 params1 mem_turn sm_clk)).

   Definition get_mem_observations (ext_log: ext_log_t): mem_observations_t :=
     {| obs_mainmem := _unsafe_get_ext_call_from_log ext_log ext_mainmem;
        obs_cache := fun mem core =>
                       _unsafe_get_ext_call_from_log ext_log
                         (match mem with
                         | imem => ext_cache_imem core
                         | dmem => ext_cache_dmem core
                         end);
        obs_meta := fun mem core =>
                       _unsafe_get_ext_call_from_log ext_log
                         (match mem with
                         | imem => ext_metadata_imem core
                         | dmem => ext_metadata_dmem core
                         end)
     |}.


  Definition get_observations (st st': state_t) (ext_log: ext_log_t): local_observations_t :=
      {| obs_mem:= get_mem_observations ext_log;
         obs_exit_enclave := fun core_id => observe_enclave_exit core_id st st';
         obs_ext := get_ext_observations ext_log
      |}.
  Definition mk_sigma_fn : ExternalMemory.external_mem_t -> input_t -> ext_sigma_t :=
      fun mem input (fn: @Syntax.ext_fn_t N) v =>
        if beq_dec fn (_ext ext_mainmem) then
          ExternalMemory.mem_get_response__koika mem.(ExternalMemory.ext_main_mem)
        else if beq_dec fn (_ext (ext_cache_imem CoreId0)) then
          ExternalMemory.cache_get_response__koika v (ExternalMemory.ext_pair_cache (mem.(ExternalMemory.ext_l1_caches) imem CoreId0))
        else if beq_dec fn (_ext (ext_cache_dmem CoreId0)) then
          ExternalMemory.cache_get_response__koika v (ExternalMemory.ext_pair_cache (mem.(ExternalMemory.ext_l1_caches) dmem CoreId0))
        else if beq_dec fn (_ext (ext_cache_imem CoreId1)) then
          ExternalMemory.cache_get_response__koika v (ExternalMemory.ext_pair_cache (mem.(ExternalMemory.ext_l1_caches) imem CoreId1))
        else if beq_dec fn (_ext (ext_cache_dmem CoreId1)) then
          ExternalMemory.cache_get_response__koika v (ExternalMemory.ext_pair_cache (mem.(ExternalMemory.ext_l1_caches) dmem CoreId1))
        else if beq_dec fn (_ext (ext_metadata_imem CoreId0)) then
          ExternalMemory.metadata_get_response__koika v (ExternalMemory.ext_pair_meta (mem.(ExternalMemory.ext_l1_caches) imem CoreId0))
        else if beq_dec fn (_ext (ext_metadata_dmem CoreId0)) then
          ExternalMemory.metadata_get_response__koika v (ExternalMemory.ext_pair_meta (mem.(ExternalMemory.ext_l1_caches) dmem CoreId0))
        else if beq_dec fn (_ext (ext_metadata_imem CoreId1)) then
          ExternalMemory.metadata_get_response__koika v (ExternalMemory.ext_pair_meta (mem.(ExternalMemory.ext_l1_caches) imem CoreId1))
        else if beq_dec fn (_ext (ext_metadata_dmem CoreId1)) then
          ExternalMemory.metadata_get_response__koika v (ExternalMemory.ext_pair_meta (mem.(ExternalMemory.ext_l1_caches) dmem CoreId1))
        else if beq_dec fn (_ext ext_uart_write) then
          Success (slice 0 (ext_fn_ret_type ext_uart_write) (input.(input_ext_uart_write) v))
        else if beq_dec fn (_ext ext_uart_read) then
          Success (slice 0 (ext_fn_ret_type ext_uart_read) (input.(input_ext_uart_read) v))
        else if beq_dec fn (_ext ext_led) then
          Success (slice 0 (ext_fn_ret_type ext_led) (input.(input_ext_led) v))
        else if beq_dec fn (_ext ext_finish) then
          Success (slice 0 (ext_fn_ret_type ext_finish) (input.(input_ext_finish) v))
        else
          Failure tt.
 (* TODO *)
   Definition wf_sigma (mk_sigma_fn:  @ext_sigma_t debug_id_ty) : Prop := True.
    Record machine_state_t :=
      { machine_koika_st: koika_state_t;
        machine_mem_st: ExternalMemory.external_mem_t
      }.

  Import ExternalMemory.
      Definition initial_machine_state (params0: core_init_params_t) (params1: core_init_params_t)
                                       (mem_turn sm_clk: vect_t) (dram: dram_t) : machine_state_t :=
        {| machine_koika_st := initial_koika_state params0 params1 mem_turn sm_clk;
           machine_mem_st := initial_mem dram
        |}.

End TopLevelModuleHelpers.

Instance EqDec_reg_t : EqDec.EqDec SecurityMonitor.reg_t :=
  EqDec_FiniteType.
Instance EqDec_reg_t' : EqDec SecurityMonitor.reg_t :=
  { eq_dec := EqDec_reg_t.(EqDec.eq_dec) }.

Module Type TopLevelModule (EnclaveParams: EnclaveParams_sig) (Impl: Impl EnclaveParams).
  Import ExternalMemory.
  Import Impl.
  Import TopLevelModuleHelpers.

  Import Machine.SM. Import Machine.
    Section WithSchedule.
      Context (schedule: @scheduler rule_name_t).
      Definition koika_step'
        (sigma: ext_sigma_t) (st: state_t) : result (koika_state_t * ext_log_t) unit :=
        interp_cycle' sigma id_int_fns id_struct_defs st id_rules schedule.

      Definition koika_step (sigma: ext_sigma_t) (st: koika_state_t)
                            : result (koika_state_t * local_observations_t) unit :=
        let/res2 st', ext_log := koika_step' sigma st in
        let output := get_observations st st' ext_log in
        Success (st', output).

      Definition machine_step_local_obs (sigma: input_t -> ext_sigma_t) (st: machine_state_t) (input: input_t)
                              : result (machine_state_t * local_observations_t) unit :=
        let/res2 koika_st', obs := koika_step (sigma input) st.(machine_koika_st) in
        let/res mem' := update_memory obs.(obs_mem) st.(machine_mem_st) in
        Success ({| machine_koika_st := koika_st';
                    machine_mem_st := mem'
                 |}, obs).

      Definition unsafe_machine_step_local_obs
        (sigma: input_t -> ext_sigma_t) (st: machine_state_t) (input: input_t)
        : machine_state_t * local_observations_t :=
        match machine_step_local_obs sigma st input with
        | Success ret => ret
        | Failure _ => (st, get_observations st.(machine_koika_st) st.(machine_koika_st) SortedExtFnEnv.empty)
        end.

      Definition machine_step_external (st: machine_state_t) (input: input_t)
                              : result (machine_state_t * external_observations_t) unit :=
        let/res2 koika_st', obs :=
          koika_step (mk_sigma_fn st.(machine_mem_st) input) st.(machine_koika_st) in
        let/res mem' := update_memory obs.(obs_mem) st.(machine_mem_st) in
        Success ({| machine_koika_st := koika_st';
                    machine_mem_st := mem'
                 |}, obs.(obs_ext)).

      Section WithExternalWorld.
        Context (mk_sigma_fn: external_mem_t -> input_t -> @ext_sigma_t N).
        Context {external_world_state_t : Type}.
        Context (input_machine: @i_machine_t external_world_state_t external_observations_t input_t).

        Definition step (st: machine_state_t) (input_st: external_world_state_t)
                        : result (machine_state_t * external_world_state_t * external_observations_t) unit :=
          step (machine_step_external) input_machine st input_st.

        Definition step_n' (n: nat) (st: machine_state_t) (input_st: external_world_state_t)
                   : result (machine_state_t * external_world_state_t * list external_observations_t) unit :=
          step_n' (machine_step_external) input_machine n st input_st.

        Section WithInitial.
          Context (params0 params1: core_init_params_t).
          Context (init_mem_turn init_sm_clk: vect_t).
          Context (init_dram: dram_t).

          Definition initial_state := initial_machine_state params0 params1
                                                            init_mem_turn init_sm_clk init_dram.

          Definition step_n (n: nat) : result (list external_observations_t) unit :=
            step_n initial_state
                   (machine_step_external)
                   input_machine n.
        End WithInitial.
      End WithExternalWorld.
    End WithSchedule.
  (* Lemma oraat_ok_core0_schedule: *)
  (*   oraat_ok id_int_fns id_rules (SemanticUtils.list_of_schedule core0_schedule) = true. *)
  (*  Proof. vm_reflect. Qed. *)
  (* Lemma oraat_ok_core1_schedule: *)
  (*   oraat_ok id_int_fns id_rules (SemanticUtils.list_of_schedule core1_schedule) = true. *)
  (*  Proof. vm_reflect. Qed. *)
  (* Lemma oraat_ok_sm_schedule: *)
  (*   oraat_ok id_int_fns id_rules (SemanticUtils.list_of_schedule sm_schedule) = true. *)
  (*  Proof. vm_reflect. Qed. *)
  (* Lemma oraat_ok_mem_schedule: *)
  (*   oraat_ok id_int_fns id_rules (SemanticUtils.list_of_schedule mem_schedule) = true. *)
  (*  Proof. vm_reflect. Qed. *)
  Notation typecheck_schedule := (typecheck_schedule _reg_types _ext_fn_tys id_int_fns id_struct_defs).
  Notation typecheck_int_fns := (fun int_fn_env => typecheck_int_fns' _reg_types _ext_fn_tys id_int_fns id_struct_defs).
  Module FullMachine.
    Section Typecheck.

      Definition schedule : @scheduler rule_name_t := Impl.schedule.
      Lemma typecheck_schedule_Success : typecheck_schedule schedule id_rules = Success tt.
      Proof. vm_reflect. Qed.
      Lemma typecheck_int_fns_Success : is_success (typecheck_int_fns id_int_fns) = true.
      Proof. vm_reflect. Qed.

      Definition modular_schedule : list (@scheduler rule_name_t) :=
        [core0_schedule; core1_schedule; mem_schedule; sm_schedule ].

      Lemma modular_schedule_does_not_conflict :
         modular_schedule_does_not_conflict id_int_fns id_rules modular_schedule = true.
      Proof. vm_reflect. Qed.

    End Typecheck.


    Section WithExt.
      Context (init_dram: dram_t).
      Context {external_world_state_t : Type}.
      Context (input_machine: @i_machine_t external_world_state_t external_observations_t input_t).

      Definition init_mem_turn : vect_t :=  Ob~0~0.
      Definition init_sm_turn : vect_t:=  Ob~0.

      Definition step (st: machine_state_t) (input_st: external_world_state_t)
                      : result (machine_state_t * external_world_state_t * external_observations_t) unit :=
        step schedule input_machine st input_st.

      Definition step_n' (n: nat) (st: machine_state_t) (input_st: external_world_state_t)
                   : result (machine_state_t * external_world_state_t * list external_observations_t) unit :=
        step_n' schedule input_machine n st input_st.

      Definition step_n (n: nat) : result (list external_observations_t) unit :=
        step_n schedule input_machine
                                (EnclaveParams.enclave_sig.(_core_init0))
                                (EnclaveParams.enclave_sig.(_core_init1))
                                init_mem_turn init_sm_turn init_dram n.
    End WithExt.
  End FullMachine.

  Section Schedules.
    Import SecurityMonitor.
    Import Memory.
    Import RVCore.
    Definition sm_schedule core : @scheduler SecurityMonitor.sm_rules_t :=
        mk_schedule [
            Rl_FilterReqs core
          ; Rl_DoMMIO (* TODO: move elsewhere? *)
          ; Rl_ForwardResps core
          ; Rl_UpdateEnclave core
          ; Rl_EnterEnclave core
          ; Rl_ExitEnclave core
          ; Rl_DoClk].


    Definition mem_schedule core : @scheduler mem_rules_t :=
      Rl_doCacheReq imem core |>
      Rl_doCacheReq dmem core |>
      Rl_doMemReq core
      |> Rl_doPurge core
      |> Rl_doExternalMetadata imem core
      |> Rl_doExternalMetadata dmem core
      |> Rl_doExternalCache imem core
      |> Rl_doExternalCache dmem core
      |> Rl_doExternalMem
      |> Rl_doMemResp core
      |> Rl_doInit core
      |> Rl_doFreeze core
      |> Rl_tick |> done.

    Definition core_schedule core :=
      match core with
      | CoreId0 => core0_schedule
      | CoreId1 => core1_schedule
      end.
    Definition spec_schedule (core: ind_core_id) : @scheduler rule_name_t :=
        schedule_app (core_schedule core)
       (schedule_app (map_scheduler RlMem (mem_schedule core))
                     (map_scheduler RlSm (sm_schedule core))).

  End Schedules.

  Module Core0Machine.
    Import Machine.
    Section Typecheck.

      Definition schedule : @scheduler rule_name_t :=
        spec_schedule CoreId0.

      Lemma typecheck_schedule_Success : typecheck_schedule schedule id_rules = Success tt.
      Proof. reflexivity. Qed.

      Lemma typecheck_int_fns_Success : is_success (typecheck_int_fns id_int_fns) = true.
      Proof. vm_compute. reflexivity. Qed.
    End Typecheck.


    Section WithExt.
      Context (init_dram: dram_t).
      Context {external_world_state_t : Type}.
      Context (input_machine: @i_machine_t external_world_state_t external_observations_t input_t).

      Definition step (st: machine_state_t) (input: input_t) : machine_state_t * local_observations_t :=
        unsafe_machine_step_local_obs schedule (mk_sigma_fn st.(machine_mem_st)) st input.
    End WithExt.
  End Core0Machine.

  Module Core1Machine.
    Import Machine.
    Section Typecheck.

      Definition schedule : @scheduler rule_name_t :=
        spec_schedule CoreId1.

      Lemma typecheck_schedule_Success : typecheck_schedule schedule id_rules = Success tt.
      Proof. vm_compute. reflexivity. Qed.

      Lemma typecheck_int_fns_Success : is_success (typecheck_int_fns int_fns) = true.
      Proof. vm_compute. reflexivity. Qed.

    End Typecheck.

    Section WithExt.
      Context (init_dram: dram_t).
      Context {external_world_state_t : Type}.
      Context (input_machine: @i_machine_t external_world_state_t external_observations_t input_t).

      Definition step (st: machine_state_t) (input: input_t) : machine_state_t * local_observations_t :=
        unsafe_machine_step_local_obs schedule (mk_sigma_fn st.(machine_mem_st)) st input.
    End WithExt.
  End Core1Machine.

End TopLevelModule.
