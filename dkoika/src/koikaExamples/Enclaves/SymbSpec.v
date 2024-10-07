Require Import rv_isolation.Common.
Require Import rv_isolation.RVCore.
Require Import rv_isolation.Memory.
Require Import rv_isolation.SecurityMonitor.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.TypeDefs.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
(* Require Import koikaExamples.Enclaves.ProofCore. *)
(* Require Import koikaExamples.Enclaves.ProofMemory. *)
(* Require Import koikaExamples.Enclaves.ProofSm. *)
Require Import FunctionalExtensionality.
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koikaExamples.Enclaves.ProofUtils.
Require Import koikaExamples.Enclaves.PfDefs.
(* Require Import koikaExamples.Enclaves.SmDefs. *)
Require Import koikaExamples.Enclaves.SmProofs.
Require Import koika.AnnotatedSyntax.
  Inductive custom_debug_t :=
  | Custom_uart_read_zero
  | Custom_uart_write_zero
  | Custom_led_zero
  | Custom_finish_zero
  | Custom_other_core_reset
  | Custom_stay_in_enclave
  | Custom_exit_enclave
  | Custom_pre_not_waiting
  | Custom_sm (sm: sm_custom_t)
  | Custom_base (st: string).

Import Utils.PfHelpers.
Module SymbSpecDefs.
  Definition other_core_reset (core: ind_core_id) (reg_fn: reg_t -> sval) : fancy_spred :=
    let to_mmio_regs core :=
      map _smid (match core with
               | CoreId0 => map toMMIO0 FiniteType.finite_elements
               | CoreId1 => map toMMIO1 FiniteType.finite_elements
               end) in
    {{{ forall x in (to_mmio_regs (other_core core)),
        `reg_fn x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
    }}}.

  Definition invariants (core: ind_core_id) (reg_fn: reg_t -> sval)
                        (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                        : list (custom_debug_t * fancy_spred) :=
    [(Custom_sm (SM_mmio_req_in_range core), SMSymbDefs.fs_mmio_req_in_range core reg_fn get_field)
    ;(Custom_sm (SM_enc_data_valid core), SMSymbDefs.fs_sm_inv_enc_data_valid core reg_fn get_field)
    ;(Custom_sm (SM_enc_req core), SMSymbDefs.fs_enc_req core reg_fn get_field)
    ;(Custom_sm (SM_inv_reset core), SMSymbDefs.fs_sm_inv_reset_correct core reg_fn get_field)
    ;(Custom_other_core_reset, other_core_reset core reg_fn)
    ].
  Definition pre_conds' (core: ind_core_id) (reg_fn: reg_t -> sval)
                       (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                       : list (custom_debug_t * fancy_spred) :=
    [(Custom_pre_not_waiting, {{{  `reg_fn ((_smid (state core)))` <> #(_enum enum_core_state "Waiting") }}})].

  Definition pre_conds (core: ind_core_id) (reg_fn: reg_t -> sval)
                       (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                       : list (custom_debug_t * fancy_spred) :=
    invariants core reg_fn get_field ++ pre_conds' core reg_fn get_field.

  Definition ext_fn_zero core fld fn reg_init ext_log get_field: fancy_spred :=
    let enc_data := senc_data core reg_init get_field in
    {{{ `get_field (_sid enclave_req) fld (enc_data)` <> Ob~1 ->
        `ext_log fn` = #(zeroes (unsafe_get_ext_fn_arg_type (_id fn)))
    }}}.

  Definition fs_exit_enclave (core: ind_core_id)
                                 (reg_init reg_final: reg_t -> sval)
                                 (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                 : fancy_spred :=
    {{{ `senc_data_valid core reg_init get_field` = Ob~1 ->
        `senc_data_valid core reg_final get_field` = Ob~0 ->
        { `reg_final ((_smid (state core)))` = #(_enum enum_core_state "Waiting")
        }
    }}}.

  Definition fs_stay_in_enclave (core: ind_core_id)
                                 (reg_init reg_final: reg_t -> sval)
                                 (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                 : fancy_spred :=
    {{{ {`senc_data_valid core reg_init get_field` <> Ob~1 \/
         `senc_data_valid core reg_final get_field` <> Ob~0} ->
        { `reg_final ((_smid (state core)))` <> #(_enum enum_core_state "Waiting") /\
          `reg_final ((_smid (enc_data core)))` = `reg_init ((_smid (enc_data core)))`
        }
    }}}.

  Definition post_conds' (core: ind_core_id) (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval)
                         (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    : list (custom_debug_t * fancy_spred) :=
    [(Custom_uart_write_zero, ext_fn_zero core (_fld enclave_req "ext_uart") (_extid ext_uart_write)
                               reg_init ext_log get_field)
    ;(Custom_uart_read_zero, ext_fn_zero core (_fld enclave_req "ext_uart") (_extid ext_uart_read)
                               reg_init ext_log get_field)
    ;(Custom_led_zero, ext_fn_zero core (_fld enclave_req "ext_led") (_extid ext_led)
                               reg_init ext_log get_field)
    ;(Custom_finish_zero, ext_fn_zero core (_fld enclave_req "ext_finish") (_extid ext_finish)
                               reg_init ext_log get_field)
    ;(Custom_exit_enclave, fs_exit_enclave core reg_init reg_final get_field)
    ;(Custom_stay_in_enclave, fs_stay_in_enclave core reg_init reg_final get_field)
    ].
  Definition post_conds (core: ind_core_id) (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval) get_field: list (custom_debug_t * fancy_spred) :=
    invariants core reg_final get_field ++ post_conds' core reg_init reg_final ext_log get_field.
  Definition spec_machine : machine_t :=
      {| file_registers := reg_types;
         file_ext_sigma := ext_fn_tys;
         file_struct_defs := struct_defs;
      |}.

  Definition Pre core (st: Environments.state_t) (sigma: @ext_sigma_t N) : Prop :=
          Forall (fun '(_, p) => interp_fancy_spred
                      {| pkg_machine := spec_machine;
                         pkg_init_st := st; pkg_mid_st := None; pkg_final_st := st; (* don't care *)
                         pkg_sigma := sigma; pkg_mid_ext_log := None;
                         pkg_ext_log' := SortedExtFnEnv.empty; (* don't care *)
                      |} p) (pre_conds core impl_init impl_get_field).
    Definition Post core (st st': Environments.state_t) (sigma: @ext_sigma_t N) (ext_log: ext_log_t): Prop :=
        Forall (fun '(_, p) => interp_fancy_spred
                    {| pkg_machine := spec_machine;
                       pkg_init_st := st; pkg_mid_st := None; pkg_final_st := st';
                       pkg_sigma := sigma; pkg_mid_ext_log := None; pkg_ext_log' := ext_log
                    |} p) (post_conds core impl_init impl_final impl_final_ext impl_get_field).


End SymbSpecDefs.

Module Type SymbSpec (EnclaveParams: EnclaveParams_sig)
                     (SecurityParams: SecurityParams_sig EnclaveParams).
  Import SecurityParams.Machine.
  Import PfHelpers.
  Import SecurityParams.Impl.
  Import SymbSpecDefs.


  Module Spec0Machine.
    Definition spec0_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (rl, show rl)) (list_of_schedule (Core0Machine.schedule)).
    Definition spec0_typecheck_fn rl : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs
              (inline_rule int_fns rl).
    Definition spec0_schedule :=
      preprocess_schedule spec0_typecheck_fn rules spec0_schedule_list.
    (* Goal preprocess_schedule_success impl_typecheck_fn Machine.rules impl_schedule_list = true. *)
    (* Proof. vm_compute; reflexivity. Qed. *)

    (* Lemma spec0_schedule_oraat_ok: *)
    (*   oraat_ok id_int_fns id_rules (list_of_schedule Core0Machine.schedule) = true. *)
    (* Proof. *)
    (*   vm_compute. reflexivity. *)
    (* Qed. *)

     Definition file: file_t :=
      {| file_machines := Single spec_machine spec0_schedule;
         file_assumptions := preprocess_fancy_spreds (pre_conds CoreId0 impl_init impl_get_field);
         file_assertions := preprocess_fancy_spreds (post_conds CoreId0 impl_init impl_final impl_final_ext impl_get_field);
      |}.
  End Spec0Machine.

  Module Spec1Machine.
    Definition spec1_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (rl, show rl)) (list_of_schedule (Core1Machine.schedule)).
    Definition spec1_typecheck_fn rl : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs
              (inline_rule int_fns rl).
    Definition spec1_schedule :=
      preprocess_schedule spec1_typecheck_fn rules spec1_schedule_list.
    (* Goal preprocess_schedule_success impl_typecheck_fn Machine.rules impl_schedule_list = true. *)
    (* Proof. vm_compute; reflexivity. Qed. *)

    (* Lemma spec1_schedule_oraat_ok: *)
    (*   oraat_ok id_int_fns id_rules (list_of_schedule Core1Machine.schedule) = true. *)
    (* Proof. *)
    (*   vm_compute. reflexivity. *)
    (* Qed. *)

     Definition file: file_t :=
      {| file_machines := Single spec_machine spec1_schedule;
         file_assumptions := preprocess_fancy_spreds (pre_conds CoreId1 impl_init impl_get_field);
         file_assertions := preprocess_fancy_spreds (post_conds CoreId1 impl_init impl_final impl_final_ext impl_get_field);
      |}.
  End Spec1Machine.
End SymbSpec.

Module Type SMT_Spec_sig (EnclaveParams: EnclaveParams_sig)
                          (SecurityParams: SecurityParams_sig EnclaveParams)
                          (SpecDefs: SymbSpec EnclaveParams SecurityParams).
  Parameter SMT_file0_ok: SymbolicInterp.WF_single_file SpecDefs.Spec0Machine.file = true.
  Parameter SMT_file1_ok: SymbolicInterp.WF_single_file SpecDefs.Spec1Machine.file = true.
End SMT_Spec_sig.

Module SymbSpecProofs (EnclaveParams: EnclaveParams_sig)
                      (SecurityParams: SecurityParams_sig EnclaveParams)
                      (SpecDefs: SymbSpec EnclaveParams SecurityParams)
                      (SmtOk: SMT_Spec_sig EnclaveParams SecurityParams SpecDefs).

  Import SecurityParams.Impl.
  Import SecurityParams.Machine.
  Import SpecDefs.
  Import SymbSpecDefs.
  Module Pf0.
    Import Spec0Machine.
    Theorem spec0_step_correct:
      symbolic_evaluate_file_success_single
        spec_machine spec0_schedule
          (preprocess_fancy_spreds (pre_conds CoreId0 impl_init impl_get_field))
          (preprocess_fancy_spreds (post_conds CoreId0 impl_init impl_final impl_final_ext impl_get_field)).
    Proof.
      pose proof SmtOk.SMT_file0_ok.
      specialize symbolic_evaluate_file_success with (file := file).
      propositional.
    Qed.

    Theorem spec0_step_sched_correct:
        interp_scheduler_satisfies_spec reg_type_env _ext_fn_tys id_int_fns
          id_struct_defs
          id_rules Core0Machine.schedule unit
          (fun st sigma _ => Pre CoreId0 st sigma)
          (fun st sigma st' ext_log _ => Post CoreId0 st st' sigma ext_log).
    Proof.
        unfold interp_scheduler_satisfies_spec.
        intros * _ hwf_st hwf_sigma hwf_fns hinterp hpre.
        specialize typecheck_scheduler_correct'' with
          (5 := hinterp) (2 := hwf_st) (3 := hwf_sigma) (4 := hwf_fns) (1 := eq_refl).
        intros (hwf_impl' & wf_impl_ext').
        (* specialize @oraat_interp_scheduler__conflicts_correct with *)
        (*      (1 := strong_WF_state_weaken _ _ hwf_st) (2 := hwf_sigma) (3 := hwf_fns) (6 := hinterp) (4 := eq_refl) (5 := Spec0Machine.spec0_schedule_oraat_ok). intros Horaat_impl. *)
        split_ands_in_goal; auto.
        consider Post.
        specialize spec0_step_correct. unfold symbolic_evaluate_file_success_single.
        intros.
        rewrite<-forall_preprocess_fancy_spreds_correct.
        apply H.
        + consider Pre . revert hpre.
          repeat rewrite<-forall_preprocess_fancy_spreds_correct.
          apply forall_interp_spred_package_equiv; solve_package_equiv.
        + unfold machine_to_prop. split_ands_in_goal.
          * auto.
          * apply strong_WF_state_weaken in hwf_st.
            eapply WF_state_subset with (2 := hwf_st). vm_compute; reflexivity.
          * unfold spec0_schedule. consider spec0_schedule_list.
             move hinterp at bottom.
             set (strip_dbg_sched_list _ ) as l in *.
             assert (l = (map (fun rl => id_transform_action _id (rules rl)) (list_of_schedule Core0Machine.schedule))) as Hl.
             { vm_reflect. }
             rewrite Hl.
             consider id_rules.
             apply interp_scheduler_list_equiv.
             apply hinterp.
    Qed.
  End Pf0.

  Module Pf1.
    Import Spec1Machine.

    Theorem spec1_step_correct:
      symbolic_evaluate_file_success_single
        spec_machine spec1_schedule
          (preprocess_fancy_spreds (pre_conds CoreId1 impl_init impl_get_field))
          (preprocess_fancy_spreds (post_conds CoreId1 impl_init impl_final impl_final_ext impl_get_field)).
    Proof.
      pose proof SmtOk.SMT_file1_ok.
      specialize symbolic_evaluate_file_success with (file := file).
      propositional.
    Qed.

    Theorem spec1_step_sched_correct:
        interp_scheduler_satisfies_spec reg_type_env _ext_fn_tys id_int_fns
          id_struct_defs
          id_rules Core1Machine.schedule unit
          (fun st sigma _ => Pre CoreId1 st sigma)
          (fun st sigma st' ext_log _ => Post CoreId1 st st' sigma ext_log).
    Proof.
        unfold interp_scheduler_satisfies_spec.
        intros * _ hwf_st hwf_sigma hwf_fns hinterp hpre.
        specialize typecheck_scheduler_correct'' with
          (5 := hinterp) (2 := hwf_st) (3 := hwf_sigma) (4 := hwf_fns) (1 := eq_refl).
        intros (hwf_impl' & wf_impl_ext').
        (* specialize @oraat_interp_scheduler__conflicts_correct with *)
        (*      (1 := strong_WF_state_weaken _ _ hwf_st) (2 := hwf_sigma) (3 := hwf_fns) (6 := hinterp) (4 := eq_refl) (5 := Spec1Machine.spec1_schedule_oraat_ok). intros Horaat_impl. *)
        split_ands_in_goal; auto.
        consider Post.
        specialize spec1_step_correct. unfold symbolic_evaluate_file_success_single.
        intros.
        rewrite<-forall_preprocess_fancy_spreds_correct.
        apply H.
        + consider Pre . revert hpre.
          repeat rewrite<-forall_preprocess_fancy_spreds_correct.
          apply forall_interp_spred_package_equiv; solve_package_equiv.
        + unfold machine_to_prop. split_ands_in_goal.
          * auto.
          * apply strong_WF_state_weaken in hwf_st.
            eapply WF_state_subset with (2 := hwf_st). vm_compute; reflexivity.
          * unfold spec1_schedule. consider spec1_schedule_list.
             move hinterp at bottom.
             set (strip_dbg_sched_list _ ) as l in *.
             assert (l = (map (fun rl => id_transform_action _id (rules rl)) (list_of_schedule Core1Machine.schedule))) as Hl.
             { vm_reflect. }
             rewrite Hl.
             consider id_rules.
             apply interp_scheduler_list_equiv.
             apply hinterp.
    Qed.

  End Pf1.

End SymbSpecProofs.


(* Module Test_SymbSpec. *)
(*   Require Import koikaExamples.Enclaves.External. *)
(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module SymbSpec := Empty <+ SymbSpec EnclaveParams SecurityParams. *)
(*   Module Foo. *)
(*     Import SymbSpec. *)
(*     Definition file := Eval vm_compute in Spec0Machine.file. *)
(*     Extraction "../../../../Spec0.ml" struct_sz vect_t file. *)
(*   End Foo. *)
(*   Module Bar. *)
(*     Import SymbSpec. *)
(*     Definition file := Eval vm_compute in Spec1Machine.file. *)
(*     Extraction "../../../../Spec1.ml" struct_sz vect_t file. *)
(*   End Bar. *)

(* End Test_SymbSpec. *)
