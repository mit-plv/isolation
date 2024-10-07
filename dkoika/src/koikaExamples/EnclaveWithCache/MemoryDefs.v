(* Require Import rv_isolation.Common. *)
(* Require Import koika.Frontend. *)
(* Require Import koikaExamples.EnclaveWithCache.Common. *)
(* (* Require Import koikaExamples.EnclaveWithCache.TypeDefs. *) *)
(* Require Import koikaExamples.EnclaveWithCache.Impl. *)
(* Require Import koikaExamples.EnclaveWithCache.Spec. *)
(* Require Import koikaExamples.EnclaveWithCache.Theorem. *)
(* Require Import koikaExamples.EnclaveWithCache.Utils. *)
(* (* Require Import koikaExamples.EnclaveWithCache.ProofCore. *) *)
(* (* Require Import koikaExamples.EnclaveWithCache.ProofMemory. *) *)
(* (* Require Import koikaExamples.EnclaveWithCache.ProofSm. *) *)
(* Require Import FunctionalExtensionality. *)
(* Require Import koikaExamples.EnclaveWithCache.ExtractionUtils. *)
(* Require Import koikaExamples.EnclaveWithCache.ProofUtils. *)
(* Require Import koikaExamples.EnclaveWithCache.PfDefs. *)
(* Require Import koika.AnnotatedSyntax. *)

(* Module Type MemoryDefs (EnclaveParams: EnclaveParams_sig) *)
(*                        (SecurityParams: SecurityParams_sig EnclaveParams). *)
(*   Import Memory. *)
(*   Import SecurityParams.Machine. *)
(*   Import PfHelpers. *)
(*   Import SecurityParams.Impl. *)
(*   Section ImplMachine. *)
(*     Notation reg_t := (@reg_t debug_id_ty). *)
(*     Definition impl_schedule_list : list (Machine.rule_name_t * string) := *)
(*       map (fun rl => (rl, show rl)) (list_of_schedule (Impl.mem_schedule)). *)
(*     Definition impl_typecheck_fn rl : result (aaction * nat) unit := *)
(*       typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl). *)
(*     Definition impl_schedule := *)
(*       preprocess_schedule impl_typecheck_fn rules impl_schedule_list. *)

(*     (* Goal preprocess_schedule_success impl_typecheck_fn SM.rules impl_schedule_list = true. *) *)
(*     (* Proof. vm_compute; reflexivity. Qed. *) *)
(*     Definition impl_machine : machine_t := *)
(*       {| file_registers := reg_types; *)
(*          file_ext_sigma := ext_fn_tys; *)
(*          file_struct_defs := struct_defs; *)
(*       |}. *)
(*     Lemma impl_schedule_oraat_ok: *)
(*     oraat_ok id_int_fns id_rules (list_of_schedule Impl.mem_schedule) = true. *)
(*     Proof. *)
(*       vm_compute. reflexivity. *)
(*     Qed. *)

(*   End ImplMachine. *)
(*   Section SpecMachine0. *)

(*     Definition spec0_schedule_list : list (Machine.rule_name_t * string) := *)
(*       map (fun rl => (Machine.RlMem rl, show (Machine.RlMem rl))) (list_of_schedule (mem_schedule CoreId0)). *)
(*     Definition spec0_typecheck_fn rl : result (aaction * nat) unit := *)
(*       typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl). *)
(*     Definition spec0_schedule := *)
(*       preprocess_schedule spec0_typecheck_fn rules spec0_schedule_list. *)

(*     (* Goal preprocess_schedule_success impl_typecheck_fn Memory.rules spec0_schedule_list = true. *) *)
(*     (* Proof. vm_compute; reflexivity. Qed. *) *)

(*     Definition spec0_machine : machine_t := *)
(*       {| file_registers := reg_types; *)
(*          file_ext_sigma := ext_fn_tys; *)
(*          file_struct_defs := struct_defs; *)
(*       |}. *)
(*   End SpecMachine0. *)


(*   Section SpecMachine1. *)

(*     Definition spec1_schedule_list : list (Machine.rule_name_t * string) := *)
(*       map (fun rl => (Machine.RlMem rl, show (Machine.RlMem rl))) (list_of_schedule (mem_schedule CoreId1)). *)
(*     Definition spec1_typecheck_fn rl : result (aaction * nat) unit := *)
(*       typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl). *)
(*     Definition spec1_schedule := *)
(*       preprocess_schedule spec1_typecheck_fn rules spec1_schedule_list. *)

(*     (* Goal preprocess_schedule_success impl_typecheck_fn Memory.rules spec1_schedule_list = true. *) *)
(*     (* Proof. vm_compute; reflexivity. Qed. *) *)

(*     Definition spec1_machine : machine_t := *)
(*       {| file_registers := reg_types; *)
(*          file_ext_sigma := ext_fn_tys; *)
(*          file_struct_defs := struct_defs; *)
(*       |}. *)
(*   End SpecMachine1. *)


(* End MemoryDefs. *)
