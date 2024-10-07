Require Import koikaExamples.EnclaveWithCache.ConcreteDefs.

Module Smt_ok_chain <: PfChain.SMT_Chain_sig External.EnclaveParams.
  Axiom SMT_core0_ok: SymbolicInterp.WF_single_file (PfChain.SymbPfChain.impl_core0_step_file External.EnclaveParams.enclave_sig)= true.
  Module Core0.
    Definition file := Eval vm_compute in (PfChain.SymbPfChain.impl_core0_step_file External.EnclaveParams.enclave_sig).
  End Core0.

  Axiom SMT_core1_ok: SymbolicInterp.WF_single_file (PfChain.SymbPfChain.impl_core1_step_file External.EnclaveParams.enclave_sig)= true.
  Module Core1.
    Definition file := Eval vm_compute in (PfChain.SymbPfChain.impl_core1_step_file External.EnclaveParams.enclave_sig).
  End Core1.

  Axiom SMT_mem_ok: SymbolicInterp.WF_single_file (PfChain.SymbPfChain.impl_mem_step_file External.EnclaveParams.enclave_sig)= true.
  Module Mem.
    Definition file := Eval vm_compute in (PfChain.SymbPfChain.impl_mem_step_file External.EnclaveParams.enclave_sig).
  End Mem.

  Axiom SMT_sm_ok: SymbolicInterp.WF_single_file (PfChain.SymbPfChain.impl_sm_step_file External.EnclaveParams.enclave_sig)= true.
  Module SM.
    Definition file := Eval vm_compute in (PfChain.SymbPfChain.impl_sm_step_file External.EnclaveParams.enclave_sig).
  End SM.

End Smt_ok_chain.
Extraction "out_EnclaveWithCache/Smt_ok_chain.Core0.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_chain.Core0.file.
Extraction "out_EnclaveWithCache/Smt_ok_chain.Mem.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_chain.Mem.file.
Extraction "out_EnclaveWithCache/Smt_ok_chain.Core1.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_chain.Core1.file.
Extraction "out_EnclaveWithCache/Smt_ok_chain.SM.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_chain.SM.file.

Module Smt_ok_SimChain <:
  Modular_PfSim.SMT_AbstractSteps_sig External.EnclaveParams SecurityParams SimCoreDefs
                                          SimMemDefs SimSMDefs AbstractStepsDefs.
  Import AbstractStepsDefs.
  Axiom SMT_MemStep0: SymbolicInterp.WF_product_file (AbstractMemStep.sim_mem_step_file Common.CoreId0) = true.

  Module Mem0.
    Definition file := Eval vm_compute in (AbstractMemStep.sim_mem_step_file Common.CoreId0).
  End Mem0.
  Axiom SMT_MemStep1: SymbolicInterp.WF_product_file (AbstractMemStep.sim_mem_step_file Common.CoreId1) = true.

  Module Mem1.
    Definition file := Eval vm_compute in (AbstractMemStep.sim_mem_step_file Common.CoreId1).
  End Mem1.
  Definition SMT_MemStep: forall core, SymbolicInterp.WF_product_file (AbstractMemStep.sim_mem_step_file core) = true.
  Proof. destruct core; [apply SMT_MemStep0 | apply SMT_MemStep1]. Qed.

  Axiom SMT_SMStep0: SymbolicInterp.WF_product_file (AbstractSmStep.sim_sm_step_file Common.CoreId0) = true.
  Module SM0.
    Definition file := Eval vm_compute in (AbstractSmStep.sim_sm_step_file Common.CoreId0).
  End SM0.

  Axiom SMT_SMStep1: SymbolicInterp.WF_product_file (AbstractSmStep.sim_sm_step_file Common.CoreId1) = true.
  Module SM1.
    Definition file := Eval vm_compute in (AbstractSmStep.sim_sm_step_file Common.CoreId1).
  End SM1.
  Definition SMT_SMStep: forall core, SymbolicInterp.WF_product_file (AbstractSmStep.sim_sm_step_file core) = true.
  Proof. destruct core; [apply SMT_SMStep0 | apply SMT_SMStep1]. Qed.
End Smt_ok_SimChain.
Extraction "out_EnclaveWithCache/Smt_ok_SimChain.Mem0.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_SimChain.Mem0.file.
Extraction "out_EnclaveWithCache/Smt_ok_SimChain.Mem1.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_SimChain.Mem1.file.
Extraction "out_EnclaveWithCache/Smt_ok_SimChain.SM0.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_SimChain.SM0.file.
Extraction "out_EnclaveWithCache/Smt_ok_SimChain.SM1.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_SimChain.SM1.file.
