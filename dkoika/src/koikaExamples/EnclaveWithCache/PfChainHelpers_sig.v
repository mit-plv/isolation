Require Import rv_cache_isolation.Common.
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
Require Import koikaExamples.EnclaveWithCache.ProofCore_symb.
Require Import koikaExamples.EnclaveWithCache.SmProofs.
Require Import koikaExamples.EnclaveWithCache.MemoryProofs.
Require Import koikaExamples.EnclaveWithCache.SymbSpec.
Require Import koikaExamples.EnclaveWithCache.PfImplDefs.
Require Import koikaExamples.EnclaveWithCache.PfImplLemmas_sig.
Require Import koikaExamples.EnclaveWithCache.PfChain.
Require Import koikaExamples.EnclaveWithCache.PfSim_sig.
Require Import koikaExamples.EnclaveWithCache.PfImplHelpers.

Module Type PfChainHelpers_sig (EnclaveParams: EnclaveParams_sig)
                   (SecurityParams: SecurityParams_sig EnclaveParams)
                   (ImplDefs: PfImplDefs EnclaveParams SecurityParams).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.

  Import SecurityParams.
  Import ExternalMemory.
  Import ImplDefs.
  Import PfChain.
  Import Utils.PfHelpers.
  Import TopLevelModuleHelpers.
Import PfHelpers.
Import CoreSymbDefs.
Import SymbSimDefs.

Import SymbPfChain.
Import SMSymbDefs.
Parameter CorePost_implies_post_conds':
  forall core sigma1 sigma2 final_st init_st mid_st post_log final_log,
  CorePost core init_st mid_st sigma2 post_log ->
  dummy_interp init_st mid_st final_st
    sigma1 (Some post_log) final_log (post_conds' core impl_init impl_mid impl_mid_ext).

  (* Parameter ImplInvariant_destruct: *)
  (*   forall st, *)
  (*     strong_WF_state reg_type_env st.(machine_koika_st) -> *)
  (*     WF_ext_mem (machine_mem_st st) -> *)
  (*     ImplInvariant_spreds EnclaveParams.enclave_sig (st) -> *)
  (*     ImplInvariant st. *)

  Parameter ImplInvariant_implies_spreds:
    forall st,
      ImplInvariant st ->
      ImplInvariant_spreds EnclaveParams.enclave_sig st.
  Parameter ImplInvariant_implies_sm_inv:
    forall init_st mid_st final_st ext_log1 ext_log2 sigma input,
    ImplInvariant init_st ->
    sigma = mk_sigma_fn (machine_mem_st init_st) input ->
    dummy_interp (machine_koika_st init_st) mid_st final_st sigma ext_log1 ext_log2
      (map_fst CustomSM (sm_invariant EnclaveParams.enclave_sig impl_init impl_get_field)).

  Parameter mem_push_in_config_implied:
    forall init_st mid_st st mid_log final_log mem sigma,
    WF_ext_log _ext_fn_tys mid_log ->
    WF_ext_log _ext_fn_tys final_log ->
    ImplInvariant {| machine_koika_st := init_st;
                     machine_mem_st := mem
                  |} ->
    dummy_interp init_st mid_st st sigma (Some mid_log) final_log
                     (post_sm_exprs EnclaveParams.enclave_sig impl_init impl_final
                        impl_mid_ext impl_committed_ext
                        impl_get_field) ->
    mem_push_in_config init_st (unsafe_get_ext_call_from_log (ext_log_app final_log mid_log) (_ext ext_mainmem)).

  Parameter core0_step_preserve_invariant:
    forall impl_st koika_log ext_log input,
    WF_ext_log _ext_fn_tys ext_log ->
    WF_ext_mem (machine_mem_st impl_st) ->
    ImplInvariant impl_st ->
    strong_WF_state reg_type_env (commit_update (machine_koika_st impl_st) koika_log) ->
    CoreSymbDefs.CorePost CoreId0 (machine_koika_st impl_st)
                   (commit_update (machine_koika_st impl_st) koika_log)
                   (mk_sigma_fn (machine_mem_st impl_st) input) ext_log ->
    ImplInvariant {| machine_koika_st := (commit_update (machine_koika_st impl_st) koika_log);
                     machine_mem_st := impl_st.(machine_mem_st) |}.
  Parameter core1_step_preserve_invariant:
    forall init_st impl_st__koika impl_st__mem koika_log ext_log mid_ext_log sigma1 sigma2 input,
    strong_WF_state reg_type_env init_st ->
    WF_ext_mem impl_st__mem  ->
    WF_ext_log _ext_fn_tys mid_ext_log ->
    WF_ext_log _ext_fn_tys ext_log ->
    ImplInvariant {| machine_koika_st := init_st;
                     machine_mem_st := impl_st__mem
                  |} ->
    ImplInvariant {| machine_koika_st := impl_st__koika;
                     machine_mem_st := impl_st__mem
                  |} ->
    strong_WF_state reg_type_env (commit_update impl_st__koika  koika_log) ->
    CoreSymbDefs.CorePost CoreId1 impl_st__koika (commit_update impl_st__koika koika_log)
                 (mk_sigma_fn (impl_st__mem) input)
                   ext_log ->
    dummy_interp init_st impl_st__koika (commit_update impl_st__koika koika_log)
                 sigma1
                 (Some mid_ext_log) ext_log
      (CoreSymbDefs.post_conds' CoreId0 impl_init impl_mid impl_mid_ext) ->
    ImplInvariant {| machine_koika_st := (commit_update impl_st__koika koika_log);
                     machine_mem_st := impl_st__mem |} /\
    dummy_interp init_st impl_st__koika
                         (commit_update impl_st__koika koika_log)
                         sigma2
                         (Some mid_ext_log) ext_log
                         (SymbPfChain.post_core1_exprs impl_init impl_final impl_committed_ext).

  Parameter mem_step_implies:
  forall init_st impl_st__koika impl_st__mem koika_log ext_log mid_ext_log input,
  strong_WF_state reg_type_env init_st ->
  WF_ext_mem impl_st__mem ->
  WF_ext_log _ext_fn_tys mid_ext_log ->
  WF_ext_log _ext_fn_tys ext_log ->
  ImplInvariant {| machine_koika_st := init_st;
                   machine_mem_st := impl_st__mem
                |} ->
  ImplInvariant {| machine_koika_st := impl_st__koika;
                   machine_mem_st := impl_st__mem
                |} ->
  strong_WF_state reg_type_env (commit_update (impl_st__koika) koika_log) ->
  MemSymbDefs.MemPost EnclaveParams.enclave_sig (impl_st__koika) (commit_update (impl_st__koika) koika_log) (mk_sigma_fn impl_st__mem input) ext_log ->
  dummy_interp init_st (impl_st__koika) (commit_update (impl_st__koika) koika_log)
               (mk_sigma_fn impl_st__mem input)
               (Some mid_ext_log) ext_log
               (SymbPfChain.post_core1_exprs impl_init impl_mid impl_mid_ext) ->
  exists mem,
  update_memory
    (get_mem_observations (ext_log_app ext_log mid_ext_log))
                        impl_st__mem  = Success mem /\
    ImplInvariant {| machine_koika_st := (commit_update (impl_st__koika) koika_log);
                     machine_mem_st := mem |} /\
          dummy_interp init_st (impl_st__koika) (commit_update (impl_st__koika) koika_log)
                       (mk_sigma_fn mem input)
                         (Some mid_ext_log) ext_log
                         (SymbPfChain.post_mem_exprs EnclaveParams.enclave_sig impl_init impl_final impl_committed_ext impl_get_field).
  Parameter sm_step_implies:
    forall init_st impl_st__koika impl_st__mem  impl_mem__init koika_log ext_log mid_ext_log input,
    strong_WF_state reg_type_env init_st ->
    WF_ext_log _ext_fn_tys mid_ext_log ->
    WF_ext_log _ext_fn_tys ext_log ->
    WF_ext_mem impl_st__mem  ->
    ImplInvariant {| machine_koika_st := init_st;
                     machine_mem_st := impl_mem__init
                  |} ->
    ImplInvariant {| machine_koika_st := impl_st__koika;
                     machine_mem_st := impl_st__mem
                  |} ->
    strong_WF_state reg_type_env (commit_update (impl_st__koika) koika_log) ->
    SMPost EnclaveParams.enclave_sig (impl_st__koika) (commit_update (impl_st__koika) koika_log)
      (mk_sigma_fn impl_mem__init input) ext_log ->
    dummy_interp init_st (impl_st__koika) (commit_update (impl_st__koika) koika_log)
                 (mk_sigma_fn impl_st__mem input)
                 (Some mid_ext_log) ext_log
                 (post_mem_exprs EnclaveParams.enclave_sig impl_init impl_mid impl_mid_ext impl_get_field) ->
    ImplInvariant {| machine_koika_st := (commit_update (impl_st__koika) koika_log);
                     machine_mem_st := impl_st__mem |} /\
    dummy_interp init_st (impl_st__koika)
                     (commit_update (impl_st__koika) koika_log)
                     (mk_sigma_fn impl_st__mem input)
                     (Some mid_ext_log) ext_log
                     (post_sm_exprs EnclaveParams.enclave_sig impl_init impl_final
                                    impl_mid_ext impl_committed_ext impl_get_field).


End PfChainHelpers_sig.
