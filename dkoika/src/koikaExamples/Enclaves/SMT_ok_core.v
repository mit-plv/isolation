Require Import koikaExamples.Enclaves.ConcreteDefs.


Module Smt_ok_core0<: ProofCore_symb.SMT_Core0_sig External.EnclaveParams SecurityParams Core0_Defs.
  Axiom SMT_file_ok: SymbolicInterp.WF_single_file Core0_Defs.file = true.
  Definition file := Eval vm_compute in (Core0_Defs.file).
End Smt_ok_core0.
Extraction "out_Enclaves/Smt_ok_core0.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_core0.file.

Module Smt_ok_core1<: ProofCore_symb.SMT_Core1_sig External.EnclaveParams SecurityParams Core1_Defs.
  Axiom SMT_file_ok: SymbolicInterp.WF_single_file Core1_Defs.file = true.
  Definition file := Eval vm_compute in (Core1_Defs.file).
End Smt_ok_core1.
Extraction "out_Enclaves/Smt_ok_core1.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_core1.file.

Module Smt_ok_SimCore<: Modular_PfSim.SMT_SimCore_sig External.EnclaveParams SecurityParams SimCoreDefs.
  Axiom SMT_file0 : SymbolicInterp.WF_product_file (SimCoreDefs.sim_core_file Common.CoreId0) = true.
  Axiom SMT_file1 : SymbolicInterp.WF_product_file (SimCoreDefs.sim_core_file Common.CoreId1) = true.
  Definition SMT_file: forall core, SymbolicInterp.WF_product_file (SimCoreDefs.sim_core_file core) = true.
  Proof. destruct core; [apply SMT_file0 | apply SMT_file1]. Qed.

  Module Core0.
    Definition file := Eval vm_compute in (SimCoreDefs.sim_core_file Common.CoreId0).
  End Core0.

  Module Core1.
    Definition file := Eval vm_compute in (SimCoreDefs.sim_core_file Common.CoreId1).
  End Core1.
End Smt_ok_SimCore.
Extraction "out_Enclaves/Smt_ok_SimCore.Core0.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_SimCore.Core0.file.
Extraction "out_Enclaves/Smt_ok_SimCore.Core1.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_SimCore.Core1.file.
