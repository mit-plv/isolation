Require Import rv_cache_isolation.Common.
Require Import rv_cache_isolation.RVCore.
Require Import rv_cache_isolation.Memory.
Require Import rv_cache_isolation.SecurityMonitor.
Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.EnclaveWithCache.ExtractionUtils.
Require Import koikaExamples.EnclaveWithCache.ProofUtils.
Require Import koikaExamples.EnclaveWithCache.PfDefs.
Require Import koikaExamples.EnclaveWithCache.SymbSpec.

Module SpecParams.
  Definition can_start_fn: ind_core_id -> nat -> nat -> enclave_config -> option enclave_config -> bool :=
    fun core_id t_exit cur_cycles new_config other_core_config =>
      match core_id with
      | CoreId0 => Nat.even cur_cycles
      | CoreId1 => Nat.odd cur_cycles
      end.
End SpecParams.
Import TopLevelModuleHelpers.
  Definition spec_post_obs_exit
    (core: ind_core_id) (machine_st: machine_state_t)
    (machine_st': machine_state_t) (local_output: local_observations_t) :=
    match obs_exit_enclave local_output core with
    | Some new =>
      (machine_koika_st machine_st').[_smrid (state core )] = (_enum enum_core_state "Waiting") /\
      (unsafe_enclave_data_to_config (machine_koika_st machine_st').[_smrid (enc_req core)]) = new
    | None =>
      (machine_koika_st machine_st').[_smrid (state core )] <> (_enum enum_core_state "Waiting") /\
      (machine_koika_st machine_st').[_smrid (enc_data core )] =
      (machine_koika_st machine_st).[_smrid (enc_data core )]
    end.
  Record SpecCorePost (core: ind_core_id) (machine_st: machine_state_t) (config: enclave_config)
                          (machine_st': machine_state_t) (local_output: local_observations_t)
                          : Prop :=
  { SpecPost__wf_ext_obs: wf_external_observations (obs_ext local_output)
  ; SpecPost__wf_spec_output_config: wf_spec_output_config (obs_ext local_output) (Some config)
  ; SpecPost__obs_exit: spec_post_obs_exit core machine_st machine_st' local_output
  ; SpecPost__wf_state: strong_WF_state reg_type_env (machine_koika_st machine_st')
  ; SpecPost__wf_ext_mem: WF_ext_mem (machine_mem_st machine_st')
  ; SpecPost__still_running: forall input, (machine_koika_st machine_st').[_smrid (state core)] <> (_enum enum_core_state "Waiting") ->
                             SymbSpecDefs.Pre core (machine_koika_st machine_st') (mk_sigma_fn (machine_mem_st machine_st') input)
  }.

Import SpecDefs.

Module Type PfSpecDefs (EnclaveParams: EnclaveParams_sig)
                   (SecurityParams: SecurityParams_sig EnclaveParams)
                   (Spec: Spec_sig EnclaveParams).
  Import SecurityParams.Impl.
  Import SecurityParams.Machine.
  Import SecurityParams.
  (* Import Machine.SM.Memory. *)
  Import PfHelpers.
  Import Spec.
  Import ExternalMemory.
  Import TopLevelModuleHelpers.
  Notation spec_state_t := (@Spec.state_t machine_state_t).

  Definition get_spec_configs (st: spec_state_t) : ind_core_id -> option enclave_config :=
    fun core_id => Spec.get_core_config (st.(Spec.machine_state) core_id).

  Definition disjoint_option_configs' (spec_st: spec_state_t) : Prop :=
      disjoint_option_configs
        (get_core_config (machine_state spec_st CoreId0))
        (get_core_config (machine_state spec_st CoreId1)).

  Record SpecCoreInvariant__Running (core: ind_core_id) (st: machine_state_t) (config: enclave_config): Prop :=
   { SpecInv_WF_state: strong_WF_state reg_type_env st.(machine_koika_st);
     SpecInv_not_waiting: (machine_koika_st st).[_smrid (state core)] <> (_enum enum_core_state "Waiting");
     SpecInv_config: machine_st_to_ghost_core (machine_koika_st st) core SecurityParams.extract_rf = GhostCoreState_Enclave config;
     SpecInv_state: forall input, SymbSpecDefs.Pre core (machine_koika_st st) (mk_sigma_fn (machine_mem_st st) input);
     SpecInv_ExtMem: WF_ext_mem st.(machine_mem_st)
    }.


  Definition spec_machine_invariant (core: ind_core_id) (st: @core_state_t machine_state_t) (cycles: nat): Prop :=
  match st with
  | CoreState_Enclave st config => SpecCoreInvariant__Running core st config
  | CoreState_Waiting config rf exit_cycles => True (* exit_cycles < cycles *)
  end.

  Record wf_mem_regions (regions: memory_map_t) : Prop :=
  { WF_mem_regions : forall region, WF_dram (regions region)
  }.

  Record SpecInvariant (st: spec_state_t) : Prop :=
    { spec_machine_inv: forall core, spec_machine_invariant core (st.(machine_state) core) (cycles st)
    ; spec_disjoint_configs: disjoint_option_configs' st
    ; spec_wf_mem_regions: wf_mem_regions st.(mem_regions)
   }.

    Definition case_core_state core (step_function: machine_state_t -> machine_state_t * local_observations_t)
                               (state1 state2: @core_state_t machine_state_t) output cycles
                               memory0 memory1
                               (other_config: option enclave_config)
      :=
      match state1, state2 with
      | CoreState_Enclave machine_state1 config1,
        CoreState_Enclave machine_state2 config2 =>
          let '(machine_state', obs) := (step_function machine_state1) in
          machine_state2 = machine_state' /\ config1 = config2 /\
          obs.(obs_exit_enclave) core = None /\
          output = (snd (step_function machine_state1)).(obs_ext) /\
          memory1 = memory0
      | CoreState_Enclave machine_state1 config1,
        CoreState_Waiting config2 rf2 cycles2 =>
          let '(machine_state', obs) := (step_function machine_state1) in
          obs.(obs_exit_enclave) core = Some config2 /\
          output = (snd (step_function machine_state1)).(obs_ext) /\
          cycles2 = cycles /\
          memory1 = update_regions EnclaveParams.enclave_sig config1 (SecurityParams.extract_dram machine_state') memory0 /\
          rf2 = SecurityParams.extract_rf machine_state' core
      | CoreState_Waiting config1 rf1 cycles1,
        CoreState_Enclave machine_state2 config2 =>
        config2 = config1 /\
        (can_enter_enclave config1 ((other_config )) = true) /\
        (match core with
         | CoreId0 => Nat.even cycles = true
         | CoreId1 => Nat.even cycles = false
         end) /\ output = empty_external_obs /\ memory1 = memory0 /\
          machine_state2 = SecurityParams.spin_up_machine core (cycles + 1)
                               {| machine_pc := _enclave_bootloader_addr EnclaveParams.enclave_sig (config_eid config1);

                                  machine_rf := rf1;
                                  machine_config := Some config1
                               |}
                              (get_enclave_dram EnclaveParams.enclave_sig memory1 config1)
      | CoreState_Waiting config1 rf1 cycles1,
        CoreState_Waiting config2 rf2 cycles2 =>
        (can_enter_enclave config1 other_config = false \/
          (match core with
          | CoreId0 => Nat.even cycles = false
          | CoreId1 => Nat.even cycles = true
          end))  /\
          config1 = config2 /\ cycles2 = cycles1 /\ output = empty_external_obs/\ memory1 = memory0 /\ rf1 = rf2
      end.


    Definition spec_step_core core (core_state: @core_state_t machine_state_t) input :=
      match core with
      | CoreId0 => fun machine => SecurityParams.local_step_fn0 machine (filter_input (get_core_config core_state) input)
      | CoreId1 => fun machine => SecurityParams.local_step_fn1 machine (filter_input (get_core_config core_state) input)
      end.


End PfSpecDefs.
