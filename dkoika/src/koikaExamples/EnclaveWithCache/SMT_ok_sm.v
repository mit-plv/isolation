Require Import koikaExamples.EnclaveWithCache.ConcreteDefs.

Module Smt_ok_sm <: SmProofs.SMT_SM_sig External.EnclaveParams SecurityParams SmDefs.
  Axiom SMT_file_ok: SymbolicInterp.WF_single_file SmDefs.ImplStep.file = true.
  Definition file := Eval vm_compute in (SmDefs.ImplStep.file).
End Smt_ok_sm.
Extraction "out_EnclaveWithCache/Smt_ok_sm.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_sm.file.

Module Smt_ok_SimSM <: Modular_PfSim.SMT_SimSM_sig External.EnclaveParams SecurityParams SimSMDefs.
  Axiom SMT_file0: SymbolicInterp.WF_product_file (SimSMDefs.sim_sm_file Common.CoreId0) = true.
  Axiom SMT_file1: SymbolicInterp.WF_product_file (SimSMDefs.sim_sm_file Common.CoreId1) = true.

  Definition SMT_file: forall core, SymbolicInterp.WF_product_file (SimSMDefs.sim_sm_file core) = true.
  Proof. destruct core; [apply SMT_file0 | apply SMT_file1]; auto. Qed.

  Module Core0.
    Definition file := Eval vm_compute in (SimSMDefs.sim_sm_file Common.CoreId0).
  End Core0.

  Module Core1.
    Definition file := Eval vm_compute in (SimSMDefs.sim_sm_file Common.CoreId1).
  End Core1.

End Smt_ok_SimSM.

Extraction "out_EnclaveWithCache/Smt_ok_SimSM.Core0.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_SimSM.Core0.file.
Extraction "out_EnclaveWithCache/Smt_ok_SimSM.Core1.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_SimSM.Core1.file.
