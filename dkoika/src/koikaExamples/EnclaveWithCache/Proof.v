Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.EnclaveWithCache.ProofCore_symb.
Require Import koikaExamples.EnclaveWithCache.ExtractionUtils.
Require Import koikaExamples.EnclaveWithCache.ProofUtils.
Require Import koikaExamples.EnclaveWithCache.PfDefs.
Require Import koikaExamples.EnclaveWithCache.SmProofs.
Require Import koikaExamples.EnclaveWithCache.MemoryDefs.
Require Import koikaExamples.EnclaveWithCache.MemoryProofs.
Require Import koikaExamples.EnclaveWithCache.PfChain.
Require Import koikaExamples.EnclaveWithCache.PfImplDefs.
Require Import koikaExamples.EnclaveWithCache.PfImplLemmas_sig.
Require Import koikaExamples.EnclaveWithCache.PfSpecLemmas_sig.
Require Import koikaExamples.EnclaveWithCache.PfSpecDefs.
Require Import koikaExamples.EnclaveWithCache.PfSim.

(* Require Import koikaExamples.EnclaveWithCache.PfImplLemmas. *)
(* Require Import koikaExamples.EnclaveWithCache.PfSim. *)
(* Require Import koikaExamples.EnclaveWithCache.PfSpecLemmas. *)
(* Require Import koikaExamples.EnclaveWithCache.PfChainHelpers. *)


(* Require Import koikaExamples.EnclaveWithCache.Monolithic_PfSim. *)

(* Require Import koikaExamples.EnclaveWithCache.Modular_PfSim. *)
Require Import koikaExamples.EnclaveWithCache.PfInit_sig.

Module Secure (EnclaveParams: EnclaveParams_sig)
              (SecurityParams: SecurityParams_sig EnclaveParams)
              (Symbspec: SymbSpec.SymbSpec EnclaveParams SecurityParams)
              (ImplDefs: PfImplDefs.PfImplDefs EnclaveParams SecurityParams)
              (PfImplLemmas: PfImplLemmas_sig EnclaveParams SecurityParams ImplDefs)
              (Spec: Spec_sig EnclaveParams)
              (SpecDefs: PfSpecDefs EnclaveParams SecurityParams Spec)
              (PfSpecLemmas: PfSpecLemmas_sig EnclaveParams SecurityParams Spec SpecDefs)
              (PfSimProofs: PfSim_sig.PfSimProofs_sig EnclaveParams SecurityParams Symbspec)
              (PfInit: PfInit_sig EnclaveParams SecurityParams ImplDefs)
              : Secure_t EnclaveParams SecurityParams.
  Module MPf := PfSim.Pf EnclaveParams SecurityParams Symbspec ImplDefs
                         PfImplLemmas Spec SpecDefs PfSpecLemmas PfSimProofs PfInit.
  Module Impl := SecurityParams.Machine.FullMachine.
  Module Spec := Empty <+ Spec_sig EnclaveParams.

  Theorem secure :
    forall (initial_dram: dram_t),
      exists (can_start_fn: Common.ind_core_id -> nat -> nat -> Common.enclave_config -> option Common.enclave_config -> bool),
      forall (external_world_state_t: Type)
        (input_machine: @i_machine_t external_world_state_t output_t input_t)
        (n: nat),
        WF_dram initial_dram ->
        Impl.step_n initial_dram input_machine n =
          Success (Spec.step_n SecurityParams.local_step_fn0
                               SecurityParams.local_step_fn1
                               can_start_fn
                               SecurityParams.spin_up_machine
                               SecurityParams.extract_dram
                               SecurityParams.extract_rf
                               (dram_to_mem_map EnclaveParams.enclave_sig initial_dram) input_machine n).
  Proof.
    eauto using MPf.simulation.
  Qed.
End Secure.

(*! Concrete proof for particular EnclaveParams *)
Require Import koikaExamples.EnclaveWithCache.ConcreteDefs.
Require Import koikaExamples.EnclaveWithCache.PfImplLemmas.
Require Import koikaExamples.EnclaveWithCache.PfChainHelpers.
Require Import koikaExamples.EnclaveWithCache.Modular_PfSim.
Require Import koikaExamples.EnclaveWithCache.PfInit.
Require Import koikaExamples.EnclaveWithCache.PfSpecLemmas.
Require Import koikaExamples.EnclaveWithCache.SymbSpec.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Modular_PfSim.

Module MkConcreteSecure
  (SMT_ok_core0: SMT_Core0_sig External.EnclaveParams SecurityParams Core0_Defs)
  (SMT_ok_core1: SMT_Core1_sig External.EnclaveParams SecurityParams Core1_Defs)
  (SMT_ok_sm: SMT_SM_sig External.EnclaveParams SecurityParams SmDefs)
  (SMT_ok_mem: SMT_Mem_sig External.EnclaveParams SecurityParams MemDefs)
  (SMT_ok_chain: SMT_Chain_sig External.EnclaveParams )
  (SMT_ok_spec : SMT_Spec_sig External.EnclaveParams SecurityParams Symbspec)
  (SMT_ok_init: SMT_ImplInit_sig External.EnclaveParams)
  (SMT_ok_SimCore: SMT_SimCore_sig External.EnclaveParams SecurityParams SimCoreDefs)
  (SMT_ok_SimMem : SMT_SimMem_sig External.EnclaveParams SecurityParams SimMemDefs)
  (SMT_ok_SimSM : SMT_SimSM_sig External.EnclaveParams SecurityParams SimSMDefs)
  (SMT_ok_SimChain: SMT_AbstractSteps_sig External.EnclaveParams SecurityParams SimCoreDefs
                                          SimMemDefs SimSMDefs AbstractStepsDefs)
  : Secure_t External.EnclaveParams SecurityParams.
  Module PfChain := Empty <+ PfChain.PfChain External.EnclaveParams SecurityParams SMT_ok_chain.
  Module PfChainHelpers := PfChainHelpers External.EnclaveParams SecurityParams
                                          ImplDefs SMT_ok_chain PfChain.
  Module PfImplLemmas := PfImplLemmas External.EnclaveParams SecurityParams Core0_Defs Core1_Defs
                                      MemDefs SmDefs ImplDefs
                                      SMT_ok_core0 SMT_ok_core1 SMT_ok_sm SMT_ok_mem
                                      SMT_ok_chain PfChain PfChainHelpers.
  Module PfSpecLemmas := PfSpecLemmas External.EnclaveParams SecurityParams Spec Symbspec
                                      PfSpecDefs SMT_ok_spec.
  Module PfSimProofs := ModularProof External.EnclaveParams SecurityParams Symbspec ImplDefs
                                     SimCoreDefs SimMemDefs SimSMDefs AbstractStepsDefs
                                     SMT_ok_SimCore SMT_ok_SimMem SMT_ok_SimSM SMT_ok_SimChain.
  Module PfInit := PfInit External.EnclaveParams SecurityParams ImplDefs SMT_ok_init.

  Module MPf := PfSim.Pf External.EnclaveParams SecurityParams Symbspec ImplDefs
                         PfImplLemmas Spec PfSpecDefs PfSpecLemmas PfSimProofs PfInit.

  Module CSecure := Secure External.EnclaveParams SecurityParams Symbspec ImplDefs
                           PfImplLemmas Spec PfSpecDefs PfSpecLemmas PfSimProofs PfInit.
  Module Impl := SecurityParams.Machine.FullMachine.
  Module Spec := Spec.

  Definition secure := CSecure.secure.
End MkConcreteSecure.

Require Import koikaExamples.EnclaveWithCache.SMT_ok_init.
Require Import koikaExamples.EnclaveWithCache.SMT_ok_core.
Require Import koikaExamples.EnclaveWithCache.SMT_ok_sm.
Require Import koikaExamples.EnclaveWithCache.SMT_ok_mem.
Require Import koikaExamples.EnclaveWithCache.SMT_ok_spec.
Require Import koikaExamples.EnclaveWithCache.SMT_ok_chain.


Module ConcreteSecure : Secure_t External.EnclaveParams SecurityParams :=
  MkConcreteSecure Smt_ok_core0 Smt_ok_core1 Smt_ok_sm Smt_ok_mem Smt_ok_chain
                   Smt_ok_spec Smt_ok_init
                   Smt_ok_SimCore Smt_ok_SimMem Smt_ok_SimSM Smt_ok_SimChain.

Print Assumptions ConcreteSecure.secure.
