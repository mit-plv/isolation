Require Import koikaExamples.EnclaveWithCache.ConcreteDefs.

Module Smt_ok_mem<: MemoryProofs.SMT_Mem_sig External.EnclaveParams SecurityParams MemDefs.
  Axiom SMT_file_ok: SymbolicInterp.WF_single_file MemDefs.ImplStep.file = true.
  Definition file := Eval vm_compute in (MemDefs.ImplStep.file).
End Smt_ok_mem.
Extraction "out_EnclaveWithCache/Smt_ok_mem.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_mem.file.

Module Smt_ok_SimMem <: Modular_PfSim.SMT_SimMem_sig External.EnclaveParams SecurityParams SimMemDefs.
  Axiom SMT_file0: SymbolicInterp.WF_product_file (SimMemDefs.sim_mem_file Common.CoreId0) = true.
  Axiom SMT_file1: SymbolicInterp.WF_product_file (SimMemDefs.sim_mem_file Common.CoreId1) = true.

  Definition SMT_file: forall core, SymbolicInterp.WF_product_file (SimMemDefs.sim_mem_file core) = true.
  Proof. destruct core; [apply SMT_file0 | apply SMT_file1]; auto. Qed.

  Module Core0.
    Definition file := Eval vm_compute in (SimMemDefs.sim_mem_file Common.CoreId0).
  End Core0.

  Module Core1.
    Definition file := Eval vm_compute in (SimMemDefs.sim_mem_file Common.CoreId1).
  End Core1.

End Smt_ok_SimMem.
Extraction "out_EnclaveWithCache/Smt_ok_SimMem.Core0.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_SimMem.Core0.file.
Extraction "out_EnclaveWithCache/Smt_ok_SimMem.Core1.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_SimMem.Core1.file.
