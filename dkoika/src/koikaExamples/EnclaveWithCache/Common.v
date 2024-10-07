Require Import PeanoNat.
Require Import rv_cache_isolation.Common.
Require Import Koika.Types.
Require Koika.Vect.

Require Import koika.Frontend.
Require Export koikaExamples.Shared.

  Definition ext_fn_ret_type (fn: ext_fn_t) : nat :=
    type_sz (Sigma fn).(retSig).
  Definition ext_fn_arg_type (fn: ext_fn_t) : nat :=
    type_sz (Sigma fn).(arg1Sig).

  Definition addr_sz := 32.
  Definition data_sz := 32.

  Record input_t : Type :=
  { input_ext_uart_write: vect_t -> vect_t;
    input_ext_uart_read: vect_t -> vect_t;
    input_ext_led: vect_t -> vect_t;
    input_ext_finish: vect_t -> vect_t
  }.

  Definition data_t := list bool.
  Definition dram_t : Type := N -> option data_t.
  Definition metadata_t := list bool.

  Definition cache_sram_t : Type := N -> option data_t.
  Definition metadata_sram_t : Type := N -> option metadata_t.


  Record external_observations_t : Type :=
    { obs_uart_write: vect_t;
      obs_uart_read: vect_t;
      obs_led: vect_t;
      obs_finish: vect_t
    }.

  Definition output_t : Type := external_observations_t.
  Definition EID_SIZE : nat := 2.

  Definition enclave_id_to_nat (eid: enclave_id) : nat :=
    match eid with
    | Enclave0 => 0
    | Enclave1 => 1
    | Enclave2 => 2
    | Enclave3 => 3
    end.

  Definition enclave_id_to_vect (eid: enclave_id) : vect_t :=
    Bits.of_nat EID_SIZE (enclave_id_to_nat eid).

  Definition shared_regions_to_vect (regions: shared_id -> bool) : vect_t :=
    [regions Shared01
     ;regions Shared02
     ;regions Shared03
     ;regions Shared12
     ;regions Shared13
     ;regions Shared23
    ].

  Inductive mem_region :=
  | MemRegion_Enclave (eid: enclave_id)
  | MemRegion_Shared (id: shared_id)
  | MemRegion_Other.
  Definition addr_t := list bool.

  Definition reg_file_t := nat -> option vect_t.

  Record core_init_params_t : Type :=
    { machine_pc: vect_t;
      machine_rf: reg_file_t;
      machine_config: option enclave_config
    }.

  Record enclave_params_sig :=
    { _enclave_base : enclave_id -> addr_t
    ; _enclave_size : enclave_id -> vect_t
    ; _enclave_bootloader_addr : enclave_id -> addr_t
    ; _shared_region_base : shared_id -> addr_t
    ; _shared_region_size : vect_t
    ; _core_init0 : core_init_params_t
    ; _core_init1: core_init_params_t
    }.

  Definition enclave_config_to_core_init_params
    (enclave_params: enclave_params_sig) (config: enclave_config) (rf: nat -> option vect_t) : core_init_params_t :=
    {| machine_pc := _enclave_bootloader_addr enclave_params config.(config_eid);
       machine_rf:= rf;
       machine_config := Some config
    |}.
   Definition shared_id_index (id: shared_id) : vect_t :=
     match id with
     | Shared01 => Bits.of_N_sz 3 0
     | Shared02 => Bits.of_N_sz 3 1
     | Shared03 => Bits.of_N_sz 3 2
     | Shared12 => Bits.of_N_sz 3 3
     | Shared13 => Bits.of_N_sz 3 4
     | Shared23 => Bits.of_N_sz 3 5
     end.


  Definition dummy_core_init_params : core_init_params_t :=
                  {| machine_pc := @zeroes addr_sz;
                     machine_rf := fun _ => None;
                     machine_config := None |}.

    Definition shared_regions_conflict (r1 r2: shared_id -> bool) : bool :=
      (r1 Shared01 && r2 Shared01) ||
      (r1 Shared02 && r2 Shared02) ||
      (r1 Shared03 && r2 Shared03) ||
      (r1 Shared12 && r2 Shared12) ||
      (r1 Shared13 && r2 Shared13) ||
      (r1 Shared23 && r2 Shared23).

    Definition configs_conflict (config: enclave_config) (other_config: option enclave_config) : bool :=
      match other_config with
      | Some other_config =>
          (enclave_id_beq config.(config_eid) other_config.(config_eid)) ||
          (shared_regions_conflict config.(config_shared_regions) other_config.(config_shared_regions)) ||
          (config.(config_ext_uart) && other_config.(config_ext_uart)) ||
          (config.(config_ext_led) && other_config.(config_ext_led)) ||
          (config.(config_ext_finish) && other_config.(config_ext_finish))
      | None => false
      end.

    Record disjoint_configs (config1 config2: enclave_config) : Prop :=
      { disjoint_eid: config_eid config1 <> config_eid config2
      ; disjoint_shared_regions: forall region, config_shared_regions config1 region = true /\ config_shared_regions config2 region = true -> False;
        disjoint_ext_uart: config_ext_uart config1 = true /\ config_ext_uart config2 = true -> False;
        disjoint_ext_led: config_ext_led config1 = true /\ config_ext_led config2 = true -> False;
        disjoint_ext_finish: config_ext_finish config1 = true /\ config_ext_finish config2 = true -> False;

      }.

    Definition wf_opt_disjoint_configs (config1 config2: option enclave_config) : Prop :=
      match config1, config2 with
      | Some config1, Some config2 => disjoint_configs config1 config2
      | _, _ => True
      end.


  Record wf_enclave_params (params: enclave_params_sig) : Prop :=
  { wf_bootloader_addr: forall eid,
      Datatypes.length (_enclave_bootloader_addr params eid) = 32
  ; wf_enclave_base: forall eid, Datatypes.length (_enclave_base params eid) = 32
  ; wf_enclave_size : forall eid, Datatypes.length (_enclave_size params eid) = 32
  ; wf_shared_base: forall sid, Datatypes.length (_shared_region_base params sid) = 32
  ; wf_shared_size : Datatypes.length (_shared_region_size params ) = 32
  ; wf_core_init0: Datatypes.length params.(_core_init0).(machine_pc) = 32
  ; wf_core_init1: Datatypes.length params.(_core_init1).(machine_pc) = 32
  ; wf_config0 : is_some params.(_core_init0).(machine_config)
  ; wf_config1 : is_some params.(_core_init1).(machine_config)
  ; wf_init_configs: wf_opt_disjoint_configs
                       params.(_core_init0).(machine_config)
                       params.(_core_init1).(machine_config)
  ; wf_rf0 : params.(_core_init0).(machine_rf) = fun _ => Some (Bits.zeroes 32)
  ; wf_rf1 : params.(_core_init1).(machine_rf) = fun _ => Some (Bits.zeroes 32)

  }.


  Section EnclaveUtils.
    Context (params: enclave_params_sig).
    Definition enclave_base_N enc_id := Bits.to_N (_enclave_base params enc_id).

    Definition enclave_max_N enc_id : N :=
      match (Bits.plus (_enclave_base params enc_id) (_enclave_size params enc_id)) with
      | Success v => Bits.to_N v
      | Failure _ => 0
      end.

    Definition shared_base_N (id: shared_id) := Bits.to_N (_shared_region_base params id).
    Definition shared_max_N (id: shared_id) :=
      match (Bits.plus (_shared_region_base params id) (_shared_region_size params )) with
      | Success v => Bits.to_N v
      | Failure _ => 0%N
      end.

    Definition addr_in_region (region: mem_region) (addr: N): bool :=
      match region with
      | MemRegion_Enclave eid =>
          (enclave_base_N eid <=? addr)%N && (addr <? (enclave_max_N eid))%N
      | MemRegion_Shared id =>
          ((shared_base_N id <=? addr) && (addr <? shared_max_N id))%N
      | MemRegion_Other => false
      end.


    Definition filter_dram : dram_t -> mem_region -> dram_t :=
      fun dram region addr =>
        if addr_in_region region addr then
          dram addr
        else None.

    Definition memory_map_t : Type := mem_region -> dram_t.
    Definition update_regions (config: enclave_config) (dram: dram_t)
                            (regions: memory_map_t)
                            : memory_map_t :=
      fun region =>
        match region with
        | MemRegion_Enclave _eid =>
            if enclave_id_beq _eid config.(config_eid) then
              filter_dram dram region
            else regions region
        | MemRegion_Shared id =>
            if config.(config_shared_regions) id then
              filter_dram dram region
            else regions region
        | MemRegion_Other => regions region
        end.

    Definition get_enclave_dram : memory_map_t -> enclave_config -> dram_t :=
       fun mem_map enclave_config addr =>
        let enclave_region := MemRegion_Enclave enclave_config.(config_eid) in
        let shared := enclave_config.(config_shared_regions) in
        if addr_in_region enclave_region addr then
          (mem_map enclave_region) addr
        else if shared Shared01 && addr_in_region (MemRegion_Shared Shared01) addr then
          (mem_map (MemRegion_Shared Shared01)) addr
        else if shared Shared02 && addr_in_region (MemRegion_Shared Shared02) addr then
          (mem_map (MemRegion_Shared Shared02)) addr
        else if shared Shared03 && addr_in_region (MemRegion_Shared Shared03) addr then
          (mem_map (MemRegion_Shared Shared03)) addr
        else if shared Shared12 && addr_in_region (MemRegion_Shared Shared12) addr then
          (mem_map (MemRegion_Shared Shared12)) addr
        else if shared Shared13 && addr_in_region (MemRegion_Shared Shared13) addr then
          (mem_map (MemRegion_Shared Shared13)) addr
        else if shared Shared23 && addr_in_region (MemRegion_Shared Shared23) addr then
          (mem_map (MemRegion_Shared Shared23)) addr
        else None.
    Definition opt_get_enclave_dram : memory_map_t -> option enclave_config -> dram_t :=
      fun mem opt_config dram =>
        match opt_config with
        | None => None
        | Some config => get_enclave_dram mem config dram
        end.


    Definition dram_to_mem_map (dram: dram_t) : memory_map_t :=
      fun region => filter_dram dram region.

    Definition wf_disjoint_configs :=
      forall region1 region2 addr,
        addr_in_region region1 addr = true ->
        addr_in_region region2 addr = true ->
        region1 = region2.
  End EnclaveUtils.
  Record mem_observations_t : Type :=
    { obs_mainmem: vect_t;
      obs_cache: mem_type -> ind_core_id -> vect_t ;
      obs_meta: mem_type -> ind_core_id -> vect_t
    }.

   Record local_observations_t : Type :=
    { obs_mem: mem_observations_t;
      obs_exit_enclave: ind_core_id -> option enclave_config;
      obs_ext : external_observations_t
     }.

  Definition empty_mem_observations : mem_observations_t :=
    {| obs_mainmem := Bits.zeroes (ext_fn_arg_type ext_mainmem);
       obs_cache := fun mem core =>
                      Bits.zeroes (ext_fn_arg_type (match mem with
                                                    | imem => ext_cache_imem
                                                    | dmem => ext_cache_dmem
                                                    end core));
       obs_meta := fun mem core =>
                      Bits.zeroes (ext_fn_arg_type (match mem with
                                                    | imem => ext_metadata_imem
                                                    | dmem => ext_metadata_dmem
                                                    end core))
    |}.


  Definition empty_external_obs: external_observations_t :=
    {| obs_uart_write := Bits.zeroes (ext_fn_arg_type ext_uart_write);
       obs_uart_read := Bits.zeroes (ext_fn_arg_type ext_uart_read);
       obs_led := Bits.zeroes (ext_fn_arg_type ext_led);
       obs_finish := Bits.zeroes (ext_fn_arg_type ext_finish);
    |}.

  Definition empty_local_observations: local_observations_t :=
    {| obs_mem:= empty_mem_observations;
       obs_exit_enclave := fun _ => None;
       obs_ext := empty_external_obs
    |}.


  Record context_switch_data_t :=
  { context_switch_config: enclave_config;
    context_switch_dram: dram_t;
    context_switch_rf: reg_file_t;
  }.

  (* Record wf_enclave_params (params: enclave_params_sig) : Prop := *)
  (* { wf_bootloader_addr: forall eid, *)
  (*     Datatypes.length (_enclave_bootloader_addr params eid) = 32 *)
  (* ; wf_enclave_base: forall eid, Datatypes.length (_enclave_base params eid) = 32 *)
  (* ; wf_enclave_size : forall eid, Datatypes.length (_enclave_size params eid) = 32 *)
  (* ; wf_shared_base: forall sid, Datatypes.length (_shared_region_base params sid) = 32 *)
  (* ; wf_shared_size : Datatypes.length (_shared_region_size params ) = 32 *)
  (* ; wf_core_init0: Datatypes.length params.(_core_init0).(machine_pc) = 32 *)
  (* ; wf_core_init1: Datatypes.length params.(_core_init1).(machine_pc) = 32 *)
  (* }. *)

  Module Type EnclaveParams_sig.
    Parameter enclave_sig: enclave_params_sig.
    Parameter pf_disjoint_configs: wf_disjoint_configs enclave_sig.
    Parameter wf_sig : wf_enclave_params enclave_sig.
  End EnclaveParams_sig.

  Definition owns_uart (config: option enclave_config) : bool :=
    match  config with
    | Some config => config_ext_uart config
    | None => false
    end.

  Definition owns_led (config: option enclave_config) : bool :=
    match  config with
    | Some config => config_ext_led config
    | None => false
    end.
  Definition owns_finish (config: option enclave_config) : bool :=
    match  config with
    | Some config => config_ext_finish config
    | None => false
    end.


  Definition lookup_dstruct_field (s: @struct_t debug_id_ty) (fld: string)
    : result (@dstruct_field_t debug_id_ty) unit:=
    match find (fun '(f, _) => beq_dec (fst f) fld) s.(dstruct_fields) with
    | Some (f, _) => Success f
    | None => Failure tt
    end.

Definition list_of_value {tau: type} (v: tau) : list bool :=
  vect_to_list(bits_of_value v).

Definition WF_dram (dram: dram_t) : Prop :=
  forall addr data, dram addr = Some data -> Datatypes.length data = data_sz.
