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
Require Import koikaExamples.EnclaveWithCache.PfDefs.
Require Import koikaExamples.EnclaveWithCache.ProofCore_symb.
Require Import koikaExamples.EnclaveWithCache.SmProofs.
(* Require Import koikaExamples.EnclaveWithCache.MemoryDefs. *)
Require Import koikaExamples.EnclaveWithCache.MemoryProofs.
Require Import koikaExamples.EnclaveWithCache.PfSim_sig.
(* Require Import koikaExamples.EnclaveWithCache.SymbSpec. *)

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

  (* Cache Inv:
     - if waiting: metadata is reset; cache resp is None

     - if flushing...
       + lines up to ??? are flushed
     *)
  Definition derive_addr (tag index: vect_t) : vect_t := tag ++ index ++ Ob~0~0.

  Definition get_cache_reg (st: koika_state_t) cache core (cache_reg: CacheState.reg_t) : vect_t :=
    st.[_id (_mid (Memory.cache_reg cache core cache_reg))].

  Record cache_resp_invariant (cache_st: CacheState.reg_t -> vect_t) (v: vect_t): Prop :=
    { CacheRespInv_fromCache_invalid : cache_st (CacheState.SH_cache_resp CacheResp.valid0) = Ob~0;
      CacheRespInv_fsm : cache_st (CacheState.cache_fsm) = _enum (cache_fsm_sig) "ProcessRequest" \/
                         cache_st (CacheState.cache_fsm) = _enum (cache_fsm_sig) "FlushLineProcess"

    }.

  Record meta_resp_invariant (cache_st: CacheState.reg_t -> vect_t) (v: vect_t) : Prop :=
    { MetaRespInv_fromMeta_invalid : cache_st (CacheState.SH_metadata_resp MetadataResp.valid0) = Ob~0;
      MetaRespInv_fsm : cache_st (CacheState.cache_fsm) = _enum (cache_fsm_sig) "ProcessRequest" \/
                         cache_st (CacheState.cache_fsm) = _enum (cache_fsm_sig) "FlushLineProcess"
    }.

  Definition dummy_interp_spred_at_st (st: koika_state_t) (spred: fancy_spred):=
    forall st' st'' sigma mid_log final_log ,
    interp_fancy_spred (dummy_pkg st st' st'' sigma mid_log final_log)
                       spred.
      (* (MemSymbDefs.meta_resp_in_range EnclaveParams.enclave_sig resp cache core impl_init impl_get_field)) *)

  Definition cache_flush_line (cache: mem_type) (core: ind_core_id)
                             (st: koika_state_t) (cache0: external_cache_t)
                             : Prop :=
        forall n line,
        (line < 2 ^ N.of_nat log_nlines)%N ->
        dummy_interp_spred_at_st st (MemSymbDefs.is_in_flush_state cache core impl_init impl_get_field) ->
        dummy_interp_spred_at_st st (MemSymbDefs.flushing_line_eq (of_N_sz log_nlines line) cache core impl_init impl_get_field) ->
        N.le n line ->
        ext_cache cache0 n = Some (Bits.zeroes 32).
  Definition meta_flush_line (cache: mem_type) (core: ind_core_id)
                             (st: koika_state_t) (meta:  external_metadata_t)
                             : Prop :=
        forall n line,
        (line < 2 ^ N.of_nat log_nlines)%N ->
        dummy_interp_spred_at_st st (MemSymbDefs.is_in_flush_state cache core impl_init impl_get_field) ->
        dummy_interp_spred_at_st st (MemSymbDefs.flushing_line_eq (of_N_sz log_nlines line) cache core impl_init impl_get_field) ->
        N.le n line ->
        ext_metadata meta n = Some (Bits.zeroes (_unsafe_struct_sz metadata_sig)).

  Record wf_cache_pair (cache: mem_type) (core: ind_core_id)
                       (st: koika_state_t)
                       (cachepair: external_cache_pair_t)
    : Prop :=
    { WF_cache_outside_range :
        forall n, N.ge n (N.pow 2%N (N.of_nat log_nlines)) ->
             cachepair.(ext_pair_cache).(ext_cache) n = Some (Bits.zeroes 32)
    ; WF_meta_outside_range :
        forall n, N.ge n (N.pow 2%N (N.of_nat log_nlines)) ->
             cachepair.(ext_pair_meta).(ext_metadata) n = Some (Bits.zeroes (_unsafe_struct_sz metadata_sig))
    ; WF_cache_flushed:
      cache_flush_line cache core st (cachepair.(ext_pair_cache))
    ; WF_meta_flushed:
      meta_flush_line cache core st (cachepair.(ext_pair_meta))
    ; WF_meta_addrs: (* TODO *)
        forall line v, cachepair.(ext_pair_meta).(ext_metadata) (to_N line) = Some v ->
                 Datatypes.length line = log_nlines ->
                   (* If data is valid, then addr in range *)
                   (dummy_interp_spred_at_st st
                     (MemSymbDefs.meta_resp_in_range_with_line EnclaveParams.enclave_sig
                        line v cache core impl_init impl_get_field))
    ; WF_valid_meta_resp:
        forall v , cachepair.(ext_pair_meta).(ext_metadata_resp) = Some v ->
        dummy_interp_spred_at_st st
            (MemSymbDefs.meta_resp_in_range EnclaveParams.enclave_sig v cache core impl_init impl_get_field)
    ; WF_meta_state_inv:
        forall v, cachepair.(ext_pair_meta).(ext_metadata_resp) = Some v ->
             meta_resp_invariant (get_cache_reg st cache core ) v
    ; WF_cache_state_inv:
        forall v, cachepair.(ext_pair_cache).(ext_cache_resp) = Some v ->
             cache_resp_invariant (get_cache_reg st cache core ) v
    }.


  Record ImplInvariant (impl_st: impl_state_t) : Prop :=
    { ImplInv_WF_state : strong_WF_state reg_type_env impl_st.(machine_koika_st)
    ; ImplInv_WF_ext_mem : WF_ext_mem (machine_mem_st impl_st)
    ; ImplInv_Core0Invariant: CoreSymbDefs.CorePre CoreId0 (machine_koika_st impl_st)
    ; ImplInv_Core1Invariant: CoreSymbDefs.CorePre CoreId1 (machine_koika_st impl_st)
    ; ImplInv_MemInvariant: forall input, MemSymbDefs.MemPre EnclaveParams.enclave_sig (machine_koika_st impl_st) (mk_sigma_fn (machine_mem_st impl_st) input)
    ; ImplInv_SMInvariant : forall input, SMSymbDefs.SMPre EnclaveParams.enclave_sig (machine_koika_st impl_st) (mk_sigma_fn (machine_mem_st impl_st) input)
    ; ImplInv_metapair : forall cache core, wf_cache_pair cache core (machine_koika_st impl_st)
                                         ((machine_mem_st impl_st).(ext_l1_caches) cache core)
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
    PostImplEnter_rf: SecurityParams.extract_rf impl_st' core = rf;
    PostImplEnter_cache: forall cache , impl_st'.(machine_mem_st).(ext_l1_caches) cache core = initial_cache_pair
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
        (unsafe_get_ext_call_from_log (log) (_ext ext_mainmem)) (ext_main_mem (machine_mem_st impl_st)) =
        Success impl_st'.(machine_mem_st).(ext_main_mem)
    ; impl_cache_update: forall cache core,
        cachepair__ext (unsafe_get_ext_call_from_log log (_ext (Memory.ext_metadata cache core)))
                     (unsafe_get_ext_call_from_log log (_ext (Memory.ext_cache cache core)))
                     (ext_l1_caches (machine_mem_st impl_st) cache core)  =
          Success (impl_st'.(machine_mem_st).(ext_l1_caches) cache core)
    }.
End PfImplDefs.
