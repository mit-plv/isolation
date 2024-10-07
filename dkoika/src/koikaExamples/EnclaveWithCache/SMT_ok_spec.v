Require Import koikaExamples.EnclaveWithCache.ConcreteDefs.

Module Smt_ok_spec<: SymbSpec.SMT_Spec_sig External.EnclaveParams SecurityParams Symbspec.
  Axiom SMT_file0_ok: SymbolicInterp.WF_single_file Symbspec.Spec0Machine.file = true.
  Axiom SMT_file1_ok: SymbolicInterp.WF_single_file Symbspec.Spec1Machine.file = true.

  Module Core0.
    Definition file := Eval vm_compute in (Symbspec.Spec0Machine.file).
  End Core0.

  Module Core1.
    Definition file := Eval vm_compute in (Symbspec.Spec1Machine.file).
  End Core1.
End Smt_ok_spec.
Extraction "out_EnclaveWithCache/Smt_ok_spec.Core0.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_spec.Core0.file.
Extraction "out_EnclaveWithCache/Smt_ok_spec.Core1.ml" SyntaxMacros.struct_sz Bits.vect_t Smt_ok_spec.Core1.file.
