Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.PfImplLemmas.
Require Import koikaExamples.EnclaveWithCache.PfChainHelpers.
Require Import koikaExamples.EnclaveWithCache.Modular_PfSim.
Require Import koikaExamples.EnclaveWithCache.PfInit.
Require Import koikaExamples.EnclaveWithCache.PfSpecLemmas.
Require Import koikaExamples.EnclaveWithCache.SymbSpec.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Modular_PfSim.

Module SecurityParams := Empty <+ SecurityParams_sig External.EnclaveParams.
Module Symbspec := Empty <+ SymbSpec.SymbSpec External.EnclaveParams SecurityParams.
Module ImplDefs := Empty <+ PfImplDefs.PfImplDefs External.EnclaveParams SecurityParams.
Module Core0_Defs := Empty <+ ProofCore_symb.Core0_Defs External.EnclaveParams SecurityParams.
Module Core1_Defs := Empty <+ ProofCore_symb.Core1_Defs External.EnclaveParams SecurityParams.
Module MemDefs := Empty <+ MemoryProofs.MemoryProofDefs External.EnclaveParams SecurityParams.
Module SmDefs := Empty <+ SmProofs.SmProofDefs External.EnclaveParams SecurityParams.
Module Spec := Empty <+ Spec_sig External.EnclaveParams.
Module PfSpecDefs  := Empty <+ PfSpecDefs.PfSpecDefs External.EnclaveParams SecurityParams Spec.
Module SimCoreDefs := Empty <+ SimCoreDefs External.EnclaveParams SecurityParams.
Module SimMemDefs := Empty <+ SimMemDefs External.EnclaveParams SecurityParams.
Module SimSMDefs := Empty <+ SimSMDefs External.EnclaveParams SecurityParams.
Module AbstractStepsDefs := Empty <+ AbstractStepsDefs External.EnclaveParams SecurityParams
                                     SimCoreDefs SimMemDefs SimSMDefs.
