Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.TypeDefs.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.Enclaves.ProofCore_symb.
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koikaExamples.Enclaves.ScheduleEquiv.
Require Import koikaExamples.Enclaves.ProofUtils.
Require Import koikaExamples.Enclaves.PfDefs.
Require Import koikaExamples.Enclaves.SmDefs.
Require Import koikaExamples.Enclaves.SmProofs.
Require Import koikaExamples.Enclaves.MemoryDefs.
Require Import koikaExamples.Enclaves.MemoryProofs.
Require Import koikaExamples.Enclaves.PfChain.
Require Import koikaExamples.Enclaves.PfImplDefs.
Require Import koikaExamples.Enclaves.PfImplLemmas_sig.
Require Import koikaExamples.Enclaves.PfSpecLemmas_sig.
Require Import koikaExamples.Enclaves.PfSpecDefs.
Require Import koikaExamples.Enclaves.PfSim.


Require Import koikaExamples.Enclaves.PfInit_sig.

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
Require Import koikaExamples.Enclaves.ConcreteDefs.
Require Import koikaExamples.Enclaves.PfImplLemmas.
Require Import koikaExamples.Enclaves.PfChainHelpers.
Require Import koikaExamples.Enclaves.Modular_PfSim.
Require Import koikaExamples.Enclaves.PfInit.
Require Import koikaExamples.Enclaves.PfSpecLemmas.
Require Import koikaExamples.Enclaves.SymbSpec.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Modular_PfSim.

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
  Module PfSimProofs := ModularProof External.EnclaveParams SecurityParams Symbspec
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

Require Import koikaExamples.Enclaves.SMT_ok_init.
Require Import koikaExamples.Enclaves.SMT_ok_core.
Require Import koikaExamples.Enclaves.SMT_ok_sm.
Require Import koikaExamples.Enclaves.SMT_ok_mem.
Require Import koikaExamples.Enclaves.SMT_ok_spec.
Require Import koikaExamples.Enclaves.SMT_ok_chain.


Module ConcreteSecure : Secure_t External.EnclaveParams SecurityParams :=
  MkConcreteSecure Smt_ok_core0 Smt_ok_core1 Smt_ok_sm Smt_ok_mem Smt_ok_chain
                   Smt_ok_spec Smt_ok_init
                   Smt_ok_SimCore Smt_ok_SimMem Smt_ok_SimSM Smt_ok_SimChain.

Print Assumptions ConcreteSecure.secure.

(* Expected outpet:
Axioms:
SymbolicInterp.symbolic_evaluate_file_success
  : forall (_ext_fn_tys : list (Syntax.ext_fn_t * (nat * nat)))
      (unsafe_lookup_dstruct_fields : struct_env_t -> ProofCore_symb.reg_t -> list (dstruct_field_t * nat))
      (file : file_t),
    match file_machines file with
    | Single machine schedule =>
        SymbolicInterp.WF_single_file file = true ->
        SymbolicInterp.symbolic_evaluate_file_success_single machine schedule (file_assumptions file)
          (file_assertions file)
    | Product impl spec impl_sched spec_sched =>
        SymbolicInterp.WF_product_file file = true ->
        SymbolicInterp.symbolic_evaluate_file_success_product impl spec impl_sched spec_sched
          (file_assumptions file) (file_assertions file)
    | AbstractSingle machine =>
        SymbolicInterp.WF_single_file file = true ->
        SymbolicInterp.symbolic_evaluate_file_success_abstract_single machine (file_assumptions file)
          (file_assertions file)
    | AbstractProduct impl spec =>
        SymbolicInterp.WF_product_file file = true ->
        SymbolicInterp.symbolic_evaluate_file_success_abstract_product impl spec (file_assumptions file)
          (file_assertions file)
    end
functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g
SymbolicInterp.WF_single_file : file_t -> bool
SymbolicInterp.WF_product_file : file_t -> bool
Smt_ok_chain.SMT_sm_ok
  : SymbolicInterp.WF_single_file (SymbPfChain.impl_sm_step_file External.EnclaveParams.enclave_sig) = true
Smt_ok_chain.SMT_mem_ok
  : SymbolicInterp.WF_single_file (SymbPfChain.impl_mem_step_file External.EnclaveParams.enclave_sig) = true
Smt_ok_sm.SMT_file_ok : SymbolicInterp.WF_single_file SmDefs.ImplStep.file = true
Smt_ok_mem.SMT_file_ok : SymbolicInterp.WF_single_file MemDefs.ImplStep.file = true
Smt_ok_core1.SMT_file_ok : SymbolicInterp.WF_single_file Core1_Defs.file = true
Smt_ok_core0.SMT_file_ok : SymbolicInterp.WF_single_file Core0_Defs.file = true
Smt_ok_spec.SMT_file1_ok : SymbolicInterp.WF_single_file Symbspec.Spec1Machine.file = true
Smt_ok_SimSM.SMT_file1 : SymbolicInterp.WF_product_file (SimSMDefs.sim_sm_file Common.CoreId1) = true
Smt_ok_SimMem.SMT_file1 : SymbolicInterp.WF_product_file (SimMemDefs.sim_mem_file Common.CoreId1) = true
Smt_ok_SimCore.SMT_file1 : SymbolicInterp.WF_product_file (SimCoreDefs.sim_core_file Common.CoreId1) = true
Smt_ok_spec.SMT_file0_ok : SymbolicInterp.WF_single_file Symbspec.Spec0Machine.file = true
Smt_ok_SimSM.SMT_file0 : SymbolicInterp.WF_product_file (SimSMDefs.sim_sm_file Common.CoreId0) = true
Smt_ok_SimMem.SMT_file0 : SymbolicInterp.WF_product_file (SimMemDefs.sim_mem_file Common.CoreId0) = true
Smt_ok_SimCore.SMT_file0 : SymbolicInterp.WF_product_file (SimCoreDefs.sim_core_file Common.CoreId0) = true
Smt_ok_chain.SMT_core1_ok
  : SymbolicInterp.WF_single_file (SymbPfChain.impl_core1_step_file External.EnclaveParams.enclave_sig) = true
Smt_ok_chain.SMT_core0_ok
  : SymbolicInterp.WF_single_file (SymbPfChain.impl_core0_step_file External.EnclaveParams.enclave_sig) = true
Smt_ok_SimChain.SMT_SMStep1
  : SymbolicInterp.WF_product_file (AbstractStepsDefs.AbstractSmStep.sim_sm_step_file Common.CoreId1) = true
Smt_ok_SimChain.SMT_SMStep0
  : SymbolicInterp.WF_product_file (AbstractStepsDefs.AbstractSmStep.sim_sm_step_file Common.CoreId0) = true
Smt_ok_SimChain.SMT_MemStep1
  : SymbolicInterp.WF_product_file (AbstractStepsDefs.AbstractMemStep.sim_mem_step_file Common.CoreId1) = true
Smt_ok_SimChain.SMT_MemStep0
  : SymbolicInterp.WF_product_file (AbstractStepsDefs.AbstractMemStep.sim_mem_step_file Common.CoreId0) = true
Smt_ok_init.SMT_ImplInvariant__Init : SymbolicInterp.WF_single_file Smt_ok_init.file = true
*)
