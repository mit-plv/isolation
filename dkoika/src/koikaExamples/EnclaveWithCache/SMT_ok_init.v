Require Import koikaExamples.EnclaveWithCache.ConcreteDefs.
Require Import koikaExamples.EnclaveWithCache.PfInit.

Module Smt_ok_init : SMT_ImplInit_sig External.EnclaveParams.
  Definition file := SymbPfInit.impl_init_file' External.EnclaveParams.enclave_sig.
  Axiom SMT_ImplInvariant__Init : SymbolicInterp.WF_single_file file = true.
End Smt_ok_init.

Module SMT_ok_init.
  Definition file := Eval vm_compute in (Smt_ok_init.file).
End SMT_ok_init.
Extraction "out_EnclaveWithCache/SMT_ok_init.ml" SyntaxMacros.struct_sz Bits.vect_t SMT_ok_init.file.
