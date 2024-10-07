Require Import rv_isolation.Common.
Require Import rv_isolation.RVCore.
Require Import rv_isolation.Memory.
Require Import rv_isolation.SecurityMonitor.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.TypeDefs.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.Enclaves.ExtractionUtils.
(* Require Import koikaExamples.Enclaves.ProofUtils. *)
Require Import koikaExamples.Enclaves.PfDefs.
Require Import koikaExamples.Enclaves.ProofCore_symb.
(* Require Import koikaExamples.Enclaves.SmDefs. *)
Require Import koikaExamples.Enclaves.SmProofs.
(* Require Import koikaExamples.Enclaves.MemoryDefs. *)
Require Import koikaExamples.Enclaves.MemoryProofs.
Require Import koikaExamples.Enclaves.PfSim_sig.
(* Require Import koikaExamples.Enclaves.SymbSpec. *)

Import TopLevelModuleHelpers.
Notation impl_state_t := machine_state_t.
Import Utils.PfHelpers.

Module Type PfImplDefs (EnclaveParams: EnclaveParams_sig)
                   (SecurityParams: SecurityParams_sig EnclaveParams).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.

  Import SecurityParams.
  Import ExternalMemory.
  Import Spec.
  (* Module SM := Machine.SM. *)
  Import PfHelpers.

  Record ImplInvariant (impl_st: impl_state_t) : Prop :=
    { ImplInv_WF_state : strong_WF_state reg_type_env impl_st.(machine_koika_st)
    ; ImplInv_WF_ext_mem : WF_ext_mem (machine_mem_st impl_st)
    ; ImplInv_Core0Invariant: CoreSymbDefs.CorePre CoreId0 (machine_koika_st impl_st)
    ; ImplInv_Core1Invariant: CoreSymbDefs.CorePre CoreId1 (machine_koika_st impl_st)
    ; ImplInv_MemInvariant: forall input, MemSymbDefs.MemPre (machine_koika_st impl_st) (mk_sigma_fn (machine_mem_st impl_st) input)
    ; ImplInv_SMInvariant : forall input, SMSymbDefs.SMPre EnclaveParams.enclave_sig (machine_koika_st impl_st) (mk_sigma_fn (machine_mem_st impl_st) input)
    }.
  #[global] Hint Resolve ImplInv_WF_state : solve_invariants.
  #[global] Hint Resolve ImplInv_WF_ext_mem: solve_invariants.
  #[global] Hint Resolve WF_mk_sigma_fn: solve_invariants.

  Definition impl_still_waiting (impl_st impl_st': impl_state_t) : Prop :=
    forall new rf core, machine_st_to_ghost_core (machine_koika_st impl_st) core SecurityParams.extract_rf = GhostCoreState_Waiting new rf ->
                can_enter_enclave new (get_impl_config impl_st.(machine_koika_st) (other_core core) SecurityParams.extract_rf ) = false \/
                  is_sm_turn core (machine_koika_st impl_st) = false ->
                machine_st_to_ghost_core (machine_koika_st impl_st') core SecurityParams.extract_rf = GhostCoreState_Waiting new rf.

  Record PostImplEnter (core: ind_core_id) (new: enclave_config)
                       (impl_st': impl_state_t ) (rf: reg_file_t): Prop :=
  { PostImplEnter_state: machine_st_to_ghost_core (machine_koika_st impl_st') core SecurityParams.extract_rf = GhostCoreState_Enclave new;
    PostImplEnter_sim: (* TODO with spec_mem *)
                       forall input spec_mem,
                       SymbSimDefs.SimPre EnclaveParams.enclave_sig core (machine_koika_st impl_st')
                                   (init_spec_koika_st core
                                                       {| machine_pc := _enclave_bootloader_addr EnclaveParams.enclave_sig new.(config_eid);
                                                          machine_config := Some new;
                                                          machine_rf := extract_rf impl_st' core
                                                       |}
                                                       (machine_koika_st impl_st').[_mrid Memory.turn]
                                                       (machine_koika_st impl_st').[_smrid clk]
                                   )
                         (mk_sigma_fn impl_st'.(machine_mem_st) input)
                         (mk_sigma_fn (initial_mem (get_enclave_dram EnclaveParams.enclave_sig spec_mem new))
                           (filter_input (Some new) input));
    PostImplEnter_rf: SecurityParams.extract_rf impl_st' core = rf

   }.

  Definition impl_enter (impl_st impl_st': impl_state_t) : Prop :=
    forall new core rf, machine_st_to_ghost_core (machine_koika_st impl_st) core SecurityParams.extract_rf = GhostCoreState_Waiting new rf ->
                can_enter_enclave new (get_impl_config impl_st.(machine_koika_st) (other_core core) SecurityParams.extract_rf) = true  ->
                is_sm_turn core (machine_koika_st impl_st) = true ->
                PostImplEnter core new impl_st' rf.

  Record step_WF_ext_obs (init_st: impl_state_t) (obs: external_observations_t) : Prop :=
    { wf_observations: wf_external_observations obs;
      wf_uart_unowned: owns_uart (get_impl_config (machine_koika_st init_st) CoreId0 SecurityParams.extract_rf) || owns_uart (get_impl_config (machine_koika_st init_st) CoreId1 SecurityParams.extract_rf) = false ->
                       obs_uart_write obs = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_uart_write))
                       /\ obs_uart_read obs = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_uart_read));
      wf_led_unowned: owns_led (get_impl_config (machine_koika_st init_st) CoreId0 SecurityParams.extract_rf) || owns_led (get_impl_config (machine_koika_st init_st) CoreId1 SecurityParams.extract_rf) = false ->
                       obs_led obs = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_led));
      wf_finish_unowned: owns_finish (get_impl_config (machine_koika_st init_st) CoreId0 SecurityParams.extract_rf) || owns_finish (get_impl_config (machine_koika_st init_st) CoreId1 SecurityParams.extract_rf) = false ->
                       obs_finish obs = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_finish))

   }.
  Definition mem_addr_in_option_config := PfHelpers.mem_addr_in_option_config EnclaveParams.enclave_sig.
  Definition mem_push_in_config (init_st: koika_state_t ) (push_req: vect_t) : Prop :=
    if PfHelpers.is_mem_core0_push_turn init_st then
      match get_valid_addr_from_push_req push_req with
      | Some addr => mem_addr_in_option_config addr
                      (get_ghost_running_config (machine_st_to_ghost_core init_st CoreId0 SecurityParams.extract_rf))
      | None => True
      end
    else if PfHelpers.is_mem_core1_push_turn init_st then
      match PfHelpers.get_valid_addr_from_push_req push_req with
      | Some addr => mem_addr_in_option_config addr
                      (get_ghost_running_config (machine_st_to_ghost_core init_st CoreId1 SecurityParams.extract_rf))
      | None => True
      end
    else
      _get_field mem_input  "put_valid" push_req = Success [false].

  Record step_WF_ext_log (init_st : impl_state_t) (ext_log: ext_log_t) : Prop :=
    { wf_ext: step_WF_ext_obs init_st (get_ext_observations ext_log) ;
      wf_mem_push: mem_push_in_config (machine_koika_st init_st)
                     (unsafe_get_ext_call_from_log (ext_log) (_ext ext_mainmem))
    }.

  Record ImplPost (impl_st impl_st': impl_state_t) (log: ext_log_t) : Prop :=
    { impl_invariant_post: ImplInvariant impl_st'
    ; impl_increment_mem_cycles:
          Bits.plus ((machine_koika_st impl_st).[_mrid Memory.turn]) (Bits.of_nat 2 1) =
            Success (machine_koika_st impl_st').[_mrid Memory.turn]
    ; impl_increment_sm_cycles:
          Bits.plus ((machine_koika_st impl_st).[_smrid clk]) (Bits.of_nat 1 1) =
            Success (machine_koika_st impl_st').[_smrid clk]
    ; impl_w2w: impl_still_waiting impl_st impl_st'
    ; impl_w2e: impl_enter impl_st impl_st'
    ; impl_wf_log: step_WF_ext_log impl_st log
    ; impl_mem_update:
      mainmem__ext
        (unsafe_get_ext_call_from_log (log) (_ext ext_mainmem)) (machine_mem_st impl_st) =
        Success impl_st'.(machine_mem_st)
    }.
End PfImplDefs.
