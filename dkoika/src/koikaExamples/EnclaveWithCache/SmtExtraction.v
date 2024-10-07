(* Require Import koika.Frontend. *)
(* Require Import koikaExamples.EnclaveWithCache.Theorem. *)
(* Require Import koikaExamples.EnclaveWithCache.External. *)
(* Require Import koikaExamples.EnclaveWithCache.Impl. *)

(* Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)

(* Require Import koikaExamples.EnclaveWithCache.SymbSpec. *)
(* Module SmtSpec. *)
(*   Module SymbSpec := Empty <+ SymbSpec.SymbSpec EnclaveParams SecurityParams. *)
(*   Import SymbSpec. *)
(*   Module Spec0. *)
(*     Definition file := Eval vm_compute in Spec0Machine.file. *)
(*     Extraction "SmtSpec.Spec0.ml" struct_sz vect_t file. *)
(*   End Spec0. *)

(*   Module Spec1. *)
(*     Definition file := Eval vm_compute in Spec1Machine.file. *)
(*     Extraction "SmtSpec.Spec1.ml" struct_sz vect_t file. *)
(*   End Spec1. *)
(* End SmtSpec. *)
(* Require Import koikaExamples.EnclaveWithCache.ProofCore_symb. *)
(* Module SmtCore. *)
(*   Module Core0Defs := Empty <+ Core0_Defs EnclaveParams SecurityParams. *)
(*   Module Core1Defs := Empty <+ Core1_Defs EnclaveParams SecurityParams. *)

(*   Module Core0. *)
(*     Definition file := Eval vm_compute in Core0Defs.file. *)
(*     Extraction "SmtCore.Core0.ml" struct_sz vect_t file. *)
(*   End Core0. *)
(*   Module Core1. *)
(*     Definition file := Eval vm_compute in Core1Defs.file. *)
(*     Extraction "SmtCore.Core1.ml" struct_sz vect_t file. *)
(*   End Core1. *)
(* End SmtCore. *)

(* Require Import koikaExamples.EnclaveWithCache.SmProofs. *)
(* Module SmtSM. *)
(*   Module Smdefs := Empty <+ SmProofDefs EnclaveParams SecurityParams. *)
(*   Module SmProof := SmProofs EnclaveParams SecurityParams Smdefs. *)
(*   Import SmProof. *)
(*   Import Smdefs. *)

(*   Definition file := Eval vm_compute in ImplStep.file. *)
(*   Extraction "SmtSM.ml" struct_sz vect_t file. *)

(* End SmtSM. *)

(* Require Import koikaExamples.EnclaveWithCache.MemoryProofs. *)
(* Module SmtMemory. *)
(*   Module Memdefs := Empty <+ MemoryProofDefs EnclaveParams SecurityParams. *)
(*   Import Memdefs. *)

(*   Definition file := Eval vm_compute in ImplStep.file. *)
(*   Extraction "SmtMemory.ml" struct_sz vect_t file. *)

(* End SmtMemory. *)

(* Require Import koikaExamples.EnclaveWithCache.PfChain. *)
(* Module SmtPfChain. *)
(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module Pfchain := Empty <+ PfChain.PfChain EnclaveParams SecurityParams. *)
(*   Import Pfchain. *)
(*   Module Core0. *)
(*     Definition file := Eval vm_compute in impl_core0_step_file. *)
(*     Extraction "SmtPfChain.Core0.ml" struct_sz vect_t file. *)
(*   End Core0. *)
(*   Module Core1. *)
(*     Definition file := Eval vm_compute in impl_core1_step_file. *)
(*     Extraction "SmtPfChain.Core1.ml" struct_sz vect_t file. *)

(*   End Core1. *)

(*   Module Mem. *)
(*     Definition file := Eval vm_compute in impl_mem_step_file. *)
(*     Extraction "SmtPfChain.Mem.ml" struct_sz vect_t file. *)

(*   End Mem. *)

(*   Module SM. *)
(*     Definition file := Eval vm_compute in impl_sm_step_file. *)
(*     Extraction "SmtPfChain.SM.ml" struct_sz vect_t file. *)
(*   End SM. *)
(* End SmtPfChain. *)
(* Require Import koikaExamples.EnclaveWithCache.Modular_PfSim. *)

(* Module SmtPfSim_Modular. *)
(*   Module SimCore. *)
(*     Module Files := SimCore EnclaveParams SecurityParams . *)

(*     Module Core0. *)
(*       Definition file := Eval vm_compute in (Files.sim_core_file Common.CoreId0). *)
(*       Extraction "SmtPfSim_Modular.SimCore.Core0.ml" struct_sz vect_t file. *)
(*     End Core0. *)
(*     Module Core1. *)
(*       Definition file := Eval vm_compute in (Files.sim_core_file Common.CoreId1). *)
(*       Extraction "SmtPfSim_Modular.SimCore.Core1.ml" struct_sz vect_t file. *)
(*     End Core1. *)
(*   End SimCore. *)
(*   Module SimSm. *)
(*     Module Files := SimSM EnclaveParams SecurityParams . *)

(*     Module Core0. *)
(*       Definition file := Eval vm_compute in (Files.sim_sm_file Common.CoreId0). *)
(*       Extraction "SmtPfSim_Modular.SimSm.Core0.ml" struct_sz vect_t file. *)
(*     End Core0. *)

(*     Module Core1. *)
(*       Definition file := Eval vm_compute in (Files.sim_sm_file Common.CoreId1). *)
(*       Extraction "SmtPfSim_Modular.SimSm.Core1.ml" struct_sz vect_t file. *)
(*     End Core1. *)

(*   End SimSm. *)

(*   Module SimMem. *)
(*     Module Files := SimMem EnclaveParams SecurityParams . *)

(*     Module Core0. *)
(*       Definition file := Eval vm_compute in (Files.sim_mem_file Common.CoreId0). *)
(*       Extraction "SmtPfSim_Modular.SimMem.Core0.ml" struct_sz vect_t file. *)
(*     End Core0. *)

(*     Module Core1. *)
(*       Definition file := Eval vm_compute in (Files.sim_mem_file Common.CoreId1). *)
(*       Extraction "SmtPfSim_Modular.SimMem.Core1.ml" struct_sz vect_t file. *)
(*     End Core1. *)

(*   End SimMem. *)

(*   Module AbstractSteps := AbstractSteps EnclaveParams SecurityParams. *)
(*   Module AbstractMemStep. *)
(*     Module Files := AbstractSteps.AbstractMemStep. *)

(*     Module File0. *)
(*       Definition file := Eval vm_compute in (Files.sim_mem_step_file Common.CoreId0). *)
(*       Extraction "SmtPfSim_Modular.AbstractMemStep.File0.ml" struct_sz vect_t file. *)
(*     End File0. *)

(*     Module File1. *)
(*       Definition file := Eval vm_compute in (Files.sim_mem_step_file Common.CoreId1). *)
(*       Extraction "SmtPfSim_Modular.AbstractMemStep.File1.ml" struct_sz vect_t file. *)
(*     End File1. *)

(*   End AbstractMemStep. *)

(*   Module AbstractSmStep. *)

(*     Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*     Module Files := AbstractSteps.AbstractSmStep. *)
(*     Module File0. *)
(*       Definition file := Eval vm_compute in (Files.sim_sm_step_file Common.CoreId0). *)
(*       Extraction "SmtPfSim_Modular.AbstractSmStep.File0.ml" struct_sz vect_t file. *)
(*     End File0. *)
(*     Module File1. *)
(*       Definition file := Eval vm_compute in (Files.sim_sm_step_file Common.CoreId1). *)
(*       Extraction "SmtPfSim_Modular.AbstractSmStep.File1.ml" struct_sz vect_t file. *)

(*       (* Extraction "PfSim_Modular_AbstractSim1_Sm.ml" struct_sz vect_t file. *) *)
(*     End File1. *)

(*   End AbstractSmStep. *)
(* End SmtPfSim_Modular. *)


(* (* Extraction "Spec0.ml" struct_sz vect_t SmtSpec.Spec0.file. *) *)
(* (* Extraction "Spec1.ml" struct_sz vect_t SmtSpec.Spec1.file. *) *)
(* (* Extraction "Core0.ml" struct_sz vect_t SmtCore.Core0.file. *) *)
(* (* Extraction "Core1.ml" struct_sz vect_t SmtCore.Core1.file. *) *)
(* (* Extraction "SM.ml" struct_sz vect_t SmtSM.file. *) *)
(* (* Extraction "Mem.ml" struct_sz vect_t SmtMemory.file. *) *)
(* (*            SmtPfChain.Core0.file *) *)
(* (*            SmtPfChain.Core1.file *) *)
(* (*            SmtPfChain.Mem.file *) *)
(* (*            SmtPfChain.SM.file *) *)
(* (*            SmtPfSim_Modular.SimCore.Core0.file *) *)
(* (*            SmtPfSim_Modular.SimCore.Core1.file *) *)
(* (*            SmtPfSim_Modular.SimSm.Core0.file *) *)
(* (*            SmtPfSim_Modular.SimSm.Core1.file *) *)
(* (*            SmtPfSim_Modular.SimMem.Core0.file *) *)
(* (*            SmtPfSim_Modular.SimMem.Core1.file *) *)
(* (*            SmtPfSim_Modular.AbstractMemStep.File0.file *) *)
(* (*            SmtPfSim_Modular.AbstractMemStep.File1.file *) *)
(* (*            SmtPfSim_Modular.AbstractSmStep.File0.file *) *)
(* (*            SmtPfSim_Modular.AbstractSmStep.File1.file. *) *)




(* (* Require Import koikaExamples.EnclaveWithCache.Monolithic_PfSim. *) *)
(* (* Module SmtPfSim_Monolithic. *) *)
(* (*   Module SymbSpec := Empty <+ SymbSpec.SymbSpec EnclaveParams SecurityParams. *) *)
(* (*   Module PfDefs := Empty <+ MonolithicDefs EnclaveParams SecurityParams SymbSpec. (* fix typo *) *) *)

(* (*   Module File0. *) *)
(* (*     Definition file := Eval vm_compute in PfDefs.sim0_file. *) *)
(* (*     Extraction "PfSim_Monolithic_Sim0.ml" struct_sz vect_t file. *) *)
(* (*   End File0. *) *)

(* (*   Module File1. *) *)
(* (*     Definition file := Eval vm_compute in PfDefs.sim1_file. *) *)
(* (*     Extraction "PfSim_Monolithic_Sim1.ml" struct_sz vect_t file. *) *)
(* (*   End File1. *) *)

(* (* End SmtPfSim_Monolithic. *) *)
