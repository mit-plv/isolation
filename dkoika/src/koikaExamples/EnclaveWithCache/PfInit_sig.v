Require Import rv_cache_isolation.Common.
Require Import rv_cache_isolation.RVCore.
Require Import rv_cache_isolation.Memory.
Require Import rv_cache_isolation.SecurityMonitor.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Utils.
Require Import koikaExamples.EnclaveWithCache.PfImplDefs.
Require Import koikaExamples.EnclaveWithCache.ExtractionUtils.


Module Type PfInit_sig (EnclaveParams: EnclaveParams_sig)
          (SecurityParams: SecurityParams_sig EnclaveParams)
          (* (SimDefs: PfSimDefs EnclaveParams SecurityParams Symbspec) *)
          (ImplDefs: PfImplDefs EnclaveParams SecurityParams).

  Definition impl_initial_state (dram: dram_t) : impl_state_t :=
    (Machine.initial_state (_core_init0 EnclaveParams.enclave_sig)
                      (_core_init1 EnclaveParams.enclave_sig) Impl.init_mem_turn Impl.init_sm_turn dram).
  Parameter ImplInvariant_initial: forall dram,  WF_dram dram -> ImplDefs.ImplInvariant (impl_initial_state dram).
End PfInit_sig.
