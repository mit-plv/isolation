Require Import rv_isolation.Common.
Require Import rv_isolation.RVCore.
Require Import rv_isolation.Memory.
Require Import rv_isolation.SecurityMonitor.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.Impl.
(* Require Import koikaExamples.Enclaves.Spec. *)
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.Enclaves.ExtractionUtils.
(* Require Import koikaExamples.Enclaves.ProofUtils. *)
(* Require Import koikaExamples.Enclaves.PfDefs. *)
(* Require Import koikaExamples.Enclaves.ProofCore_symb. *)
(* Require Import koikaExamples.Enclaves.SmProofs. *)
(* Require Import koikaExamples.Enclaves.MemoryProofs. *)
Require Import koikaExamples.Enclaves.SymbSpec.
Require Import koikaExamples.Enclaves.PfSim_sig.
Require Import koika.AnnotatedSyntax.

Module Type MonolithicDefs (EnclaveParams: EnclaveParams_sig)
                 (SecurityParams: SecurityParams_sig EnclaveParams)
                 (SymbSpec: SymbSpec EnclaveParams SecurityParams).
                  (* : PfSimProofs_sig EnclaveParams SecurityParams SymbSpec. *)

  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.
  (* Definition spec_schedule core := *)
  (*   match core with *)
  (*   | CoreId0 => Core0Machine.schedule *)
  (*   | CoreId1 => Core1Machine.schedule *)
  (*   end. *)

  Definition impl_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (rl, show rl)) (list_of_schedule (FullMachine.schedule)).
  Definition impl_typecheck_fn rl : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl).

  Definition impl_schedule :=
      preprocess_schedule impl_typecheck_fn rules impl_schedule_list.

  Definition sim0_file : file_t :=
    {| file_machines := Product impl_machine SymbSpecDefs.spec_machine
                                impl_schedule SymbSpec.Spec0Machine.spec0_schedule;
       file_assumptions := preprocess_fancy_spreds
                             (sim_pre_conds EnclaveParams.enclave_sig CoreId0 impl_init spec_init impl_get_field spec_get_field);
       file_assertions := preprocess_fancy_spreds
                             (sim_post_conds EnclaveParams.enclave_sig CoreId0 impl_init spec_init impl_final spec_final
                                            impl_get_field spec_get_field impl_final_ext spec_final_ext)
    |}.
  (* Definition sim0_file: file_t := Eval vm_compute in sim0_file'. *)

  Definition sim1_file : file_t :=
    {| file_machines := Product impl_machine SymbSpecDefs.spec_machine
                                impl_schedule SymbSpec.Spec1Machine.spec1_schedule;
       file_assumptions := preprocess_fancy_spreds
                             (sim_pre_conds EnclaveParams.enclave_sig CoreId1 impl_init spec_init impl_get_field spec_get_field);
       file_assertions := preprocess_fancy_spreds
                             (sim_post_conds EnclaveParams.enclave_sig CoreId1 impl_init spec_init impl_final spec_final
                                            impl_get_field spec_get_field impl_final_ext spec_final_ext)
    |}.

  Definition spec_schedule' core :=
    match core with
    | CoreId0 => SymbSpec.Spec0Machine.spec0_schedule
    | CoreId1 => SymbSpec.Spec1Machine.spec1_schedule
    end.
End MonolithicDefs.

Module Type SMT_Monolithic_sig
  (EnclaveParams: EnclaveParams_sig)
  (SecurityParams: SecurityParams_sig EnclaveParams)
  (SymbSpec: SymbSpec EnclaveParams SecurityParams)
  (MonolithicDefs: MonolithicDefs EnclaveParams SecurityParams SymbSpec).
  Parameter SMT_file0: SymbolicInterp.WF_product_file MonolithicDefs.sim0_file = true.
  Parameter SMT_file1: SymbolicInterp.WF_product_file MonolithicDefs.sim1_file = true.

End SMT_Monolithic_sig.

(* Module Test_Sim. *)
(*   Require Import koikaExamples.Enclaves.External. *)

(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module SymbSpec := Empty <+ SymbSpec.SymbSpec EnclaveParams SecurityParams. *)
(*   Module PfDefs := Empty <+ MonolithicDefs EnclaveParams SecurityParams SymbSpec. *)

(*   Module File0. *)
(*     Definition file := Eval vm_compute in PfDefs.sim0_file. *)
(*     Extraction "Test_Sim.File0.ml" struct_sz vect_t file. *)
(*   End File0. *)

(*   Module File1. *)
(*     Definition file := Eval vm_compute in PfDefs.sim1_file. *)
(*     Extraction "Test_Sim.File1.ml" struct_sz vect_t file. *)
(*   End File1. *)

(* End Test_Sim. *)


Module MonolithicProof (EnclaveParams: EnclaveParams_sig)
                       (SecurityParams: SecurityParams_sig EnclaveParams)
                       (SymbSpec: SymbSpec EnclaveParams SecurityParams)
                       (MonolithicDef: MonolithicDefs EnclaveParams SecurityParams SymbSpec)
                       (SmtOk: SMT_Monolithic_sig EnclaveParams SecurityParams SymbSpec MonolithicDef).
  Import MonolithicDef.
  (* Module Import MonolithicDef := MonolithicDefs EnclaveParams SecurityParams SymbSpec. *)
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.

  Theorem sim_step_correct: forall core,
    symbolic_evaluate_file_success_product
      impl_machine SymbSpecDefs.spec_machine impl_schedule (spec_schedule' core)
        (preprocess_fancy_spreds (sim_pre_conds EnclaveParams.enclave_sig core impl_init spec_init impl_get_field spec_get_field))
        (preprocess_fancy_spreds (sim_post_conds EnclaveParams.enclave_sig core impl_init spec_init impl_final spec_final
                                                 impl_get_field spec_get_field
                                                 impl_final_ext spec_final_ext)).
  Proof.
    destruct core.
    - pose proof SmtOk.SMT_file0.
      specialize symbolic_evaluate_file_success with (file := sim0_file) .
      unfold sim0_file. unfold file_machines, file_assertions, file_assumptions.
      intro foo. specialize (foo H). auto.
    - pose proof SmtOk.SMT_file1.
      specialize symbolic_evaluate_file_success with (file := sim1_file) .
      unfold sim1_file. unfold file_machines, file_assertions, file_assumptions.
      intro foo. specialize (foo H). auto.
  Qed.


  (* Lemma impl_schedule_oraat_ok: *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule FullMachine.schedule) = true. *)
  (* Proof. *)
  (*   vm_compute. reflexivity. *)
  (* Qed. *)

  (* Lemma spec_schedule_oraat_ok: *)
  (*   forall core, *)
  (*    oraat_ok id_int_fns id_rules (list_of_schedule (spec_schedule core)) = true. *)
  (* Proof. *)
  (*   destruct core; vm_reflect. *)
  (* Qed. *)

  Theorem step_sim_sched_correct:
    forall core,
     sim_interp_scheduler_satisfies_spec
        reg_type_env _ext_fn_tys
        id_int_fns id_int_fns
        id_struct_defs id_struct_defs
        id_rules id_rules FullMachine.schedule (spec_schedule core) unit
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           SimPre EnclaveParams.enclave_sig core impl_st spec_st impl_sigma spec_sigma)
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           SimPost EnclaveParams.enclave_sig core impl_st spec_st impl_st' spec_st' impl_sigma spec_sigma impl_ext spec_ext).
  Proof.
    unfold sim_interp_scheduler_satisfies_spec.
    intros * ? hwf_impl hwf_spec hwf_impl_sigma hwf_spec_sigma hwf_impl_fns hwf_spec_fns
             himpl_step hspec_step hpre.
    specialize typecheck_scheduler_correct'' with (5 := himpl_step) (2 := hwf_impl) (3 := hwf_impl_sigma) (4 := hwf_impl_fns) (1 := eq_refl); intros (hwf_impl' & wf_impl_ext').

    assert (strong_WF_state reg_type_env (commit_update spec_st (Log__koika spec_log)) /\
            WF_ext_log _ext_fn_tys (Log__ext spec_log)) as (hwf_spec' & wf_spec_ext').
    { destruct core;  eapply typecheck_scheduler_correct'' with (5 := hspec_step) (2 := hwf_spec) (3 := hwf_spec_sigma) (4 := hwf_spec_fns) (1 := eq_refl); auto.
    }

    split_ands_in_goal; auto.
    unfold SimPost.
    unfold SimPre in *. propositional.
    (* specialize @oraat_interp_scheduler__conflicts_correct with *)
    (*   (1 := strong_WF_state_weaken _ _ hwf_impl) (2 := hwf_impl_sigma) (3 := hwf_impl_fns) (* (4 := eq_refl) *) *)
    (*   (5 := impl_schedule_oraat_ok) (6 := himpl_step); eauto; intros Horaat_impl. *)
    (* specialize Horaat_impl with (1 := eq_refl). *)
    (* assert (oraat_interp_scheduler spec_sigma id_int_fns id_struct_defs id_rules spec_st *)
    (*                                (spec_schedule core) = *)
    (*           (true, commit_update spec_st (Log__koika spec_log), Log__ext spec_log)) as Horaat_spec. *)
    (* { eapply @oraat_interp_scheduler__conflicts_correct with *)
    (*   (1 := strong_WF_state_weaken _ _ hwf_spec) (2 := hwf_spec_sigma) (3 := hwf_spec_fns) *)
    (*   (5 := @spec_schedule_oraat_ok core) (6 := hspec_step); eauto. *)
    (*   destruct core; reflexivity. *)
    (* } *)

    specialize sim_step_correct with (core := core); intros hsuccess.
    unfold symbolic_evaluate_file_success_product in *.
    rewrite<-forall_preprocess_fancy_spreds_correct2.
    apply hsuccess.
    - clear hsuccess.
      rewrite<-forall_preprocess_fancy_spreds_correct2 in hpre.
      revert hpre.
      destruct core;
        eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
    - unfold machine_to_prop; split_ands_in_goal.
      + auto.
      + apply strong_WF_state_weaken in hwf_impl; auto.
      +  set (strip_dbg_sched_list _ ) as l in *.
         assert (l = (map (fun rl => id_transform_action _id (rules rl)) (list_of_schedule FullMachine.schedule))) as Hl.
         { vm_reflect. }
         rewrite Hl. apply interp_scheduler_list_equiv. assumption.
    - unfold machine_to_prop; split_ands_in_goal.
      + auto.
      + apply strong_WF_state_weaken in hwf_spec; auto.
      + set (strip_dbg_sched_list _ ) as l in *.
        destruct core.
        { assert (l = (map (fun rl => id_transform_action _id (rules rl))
                         (list_of_schedule Core0Machine.schedule))) as Hl.
          { vm_reflect. }
          rewrite Hl. apply interp_scheduler_list_equiv. assumption.
        }
        { assert (l = (map (fun rl => id_transform_action _id (rules rl))
                         (list_of_schedule Core1Machine.schedule))) as Hl.
          { vm_reflect. }
          rewrite Hl. apply interp_scheduler_list_equiv. assumption.
        }
  Qed.

End MonolithicProof.
