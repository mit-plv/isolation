Require Import rv_cache_isolation.Common.
Require Import rv_cache_isolation.SecurityMonitor.
Require Import rv_cache_isolation.RVCore.
Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.Utils.
Require Import FunctionalExtensionality.
Require Import koika.Symbolic.
Require Import koikaExamples.EnclaveWithCache.ExtractionUtils.
Require Import koika.AnnotatedSyntax.
Require Import koikaExamples.EnclaveWithCache.ProofUtils.


Import ListNotations.

Instance Show_core_rule' : Koika.Show.Show rv_rules_t := _.
Instance Show_core_rule : Show rv_rules_t :=
  { show := Show_core_rule'.(Koika.Show.show)}.

Inductive core_custom_prop_names :=
| PurgeReset
| CoreIdSame
| CoreTaint
| CoreExt (id: N)
| CorePurgedPreserve
| CorePurgedMachine
| CorePurgedWait
.

Module Type Core_sig.
  Parameter core_id : ind_core_id.
End Core_sig.

  Import Core.
  Import PfHelpers.
  Existing Instance SecurityMonitor.FiniteType_reg_t.
  Notation finite_elements := FiniteType.finite_elements.

  Definition regs_to_reset core : list debug_id_ty :=
      map reg_to_debug_id
          (Utils.PfHelpers.core_regs_to_reset core).
            (* ((map f2d finite_elements) ++ *)
            (* (map f2dprim finite_elements) ++ *)
            (* (map d2e finite_elements) ++ *)
            (* (map e2w finite_elements) ++ *)
            (* (* (map rf finite_elements) ++ *) *)
            (* (map mulState finite_elements) ++ *)
            (* (map scoreboard finite_elements) ++ *)
            (* (map fromIMem finite_elements) ++ *)
            (* (map fromDMem finite_elements) ++ *)
            (* (map fromMMIO finite_elements) ++ *)
            (* [cycle_count; instr_count; epoch; freeze_fetch; pc] *)
  Notation reg_t := debug_id_ty.

Module CoreSymbDefs.
  Definition invariant (core: ind_core_id) (reg_fn: reg_t -> sval) : list (core_custom_prop_names * fancy_spred) :=
    [(PurgeReset, {{{ `reg_fn (_crid core purge)` = #(_enum purge_state "Purged") ->
                      {forall x in (regs_to_reset core),
                       `reg_fn x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
                      }
                  }}}
     );
     (CoreIdSame, {{{ `reg_fn (_crid core core_id)` = #(cid_to_bits core)}}})
    ].
  Definition pre_conds (core: ind_core_id) (reg_init : reg_t -> sval) : list (core_custom_prop_names * fancy_spred) :=
    [] ++ (invariant core reg_init).
  Definition ext_empty (extfn: debug_id_ty -> sval): list (core_custom_prop_names * fancy_spred) :=
    map (fun fn => (CoreExt (_id fn), {{{ `extfn fn` = #(zeroes (unsafe_get_ext_fn_arg_type (_id fn))) }}}))
      (map fst ext_fn_tys).
  Definition post_conds' (core: ind_core_id) (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval): list (core_custom_prop_names * fancy_spred) :=
    [(CoreTaint, {{{ forall x in (remove_regs (reg_list) (map reg_to_debug_id (core_regs core))),
                     `reg_final x` = `reg_init x`
                 }}})
    ;(CorePurgedPreserve, {{{ {`reg_init (_crid core purge)` = #(_enum purge_state "Ready") \/
                               `reg_init (_crid core purge)` = #(_enum purge_state "Purged")} ->
                               `reg_final (_crid core purge)` = `reg_init (_crid core purge)`
                              }}})
    ;(CorePurgedMachine, {{{ `reg_init (_crid core purge)` = #(_enum purge_state "Init") ->
                             {`reg_final (_crid core purge)` = #(_enum purge_state "Ready") \/
                              `reg_final (_crid core purge)` = #(_enum purge_state "Init")}
                         }}})
    ;(CorePurgedWait, {{{ `reg_init (_crid core purge)` = #(_enum purge_state "Purged")->
                          {forall x in (map reg_to_debug_id (core_regs core)),
                           `reg_final x` = `reg_init x`
                          }
                      }}})
    ] ++ (ext_empty ext_log).

  Definition post_conds (core: ind_core_id) (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval): list (core_custom_prop_names * fancy_spred) :=
    post_conds' core reg_init reg_final ext_log ++ (invariant core reg_final).

    Definition impl_machine : machine_t :=
      {| file_registers := reg_types;
         file_ext_sigma := ext_fn_tys;
         file_struct_defs := struct_defs;
      |}.
  Definition CorePre core (st: Environments.state_t) : Prop :=
    Forall (fun '(_, p) =>
              interp_fancy_spred
                {|
                  pkg_machine := impl_machine;

                  pkg_init_st := st;
                  pkg_sigma := fun _ _ => Failure tt;
                  pkg_mid_st := None;
                  pkg_mid_ext_log := None;
                  pkg_final_st := st; (* don't care *)
                  pkg_ext_log' := SortedExtFnEnv.empty
                |} p) (pre_conds core impl_init).

  Definition CorePost core (st st': Environments.state_t) (sigma: @ext_sigma_t N) (ext_log: ext_log_t): Prop :=
      Forall (fun '(_, p) =>
                             interp_fancy_spred
                               {|
                                 pkg_machine := impl_machine;
                                 pkg_init_st := st;
                                 pkg_sigma := sigma;
                                 pkg_mid_st := None;
                                 pkg_final_st := st';
                                 pkg_mid_ext_log := None;
                                 pkg_ext_log' := ext_log
                               |} p) (post_conds core impl_init impl_final impl_final_ext).

End CoreSymbDefs.

Require Import koikaExamples.EnclaveWithCache.External.
Existing Instance Show_rule'.
Existing Instance Show_rule.

Module Type Core0_Defs (EnclaveParams: EnclaveParams_sig)
                       (SecurityParams: SecurityParams_sig EnclaveParams).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  (* Module Machine := Implementation.Machine. *)
  Module Core0Params <: Core_sig.
    Definition core_id := CoreId0.
  End Core0Params.

  Import CoreSymbDefs.

  Section ImplMachine.
    Notation reg_t := (@reg_t debug_id_ty).

    Definition impl_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (rl, show rl)) (list_of_schedule (core0_schedule)).

    Definition impl_typecheck_fn (rl: action) : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs
              (inline_rule int_fns rl).

    Definition impl_schedule :=
      preprocess_schedule impl_typecheck_fn rules impl_schedule_list.
    (* Goal preprocess_schedule_success impl_typecheck_fn Core.rules impl_schedule_list = true. *)
    (* Proof. vm_compute; reflexivity. Qed. *)

  End ImplMachine.
  Definition file: file_t :=
    {| file_machines := Single impl_machine impl_schedule;
       file_assumptions := preprocess_fancy_spreds (pre_conds CoreId0 impl_init );
       file_assertions := preprocess_fancy_spreds (post_conds CoreId0 impl_init impl_final impl_final_ext);
    |}.
End Core0_Defs.
Module Type Core1_Defs (EnclaveParams: EnclaveParams_sig)
                       (SecurityParams: SecurityParams_sig EnclaveParams).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  (* Module Machine := Implementation.Machine. *)
  Module Core1Params <: Core_sig.
    Definition core_id := CoreId1.
  End Core1Params.

  Import CoreSymbDefs.

  Section ImplMachine.
    Notation reg_t := (@reg_t debug_id_ty).

    Definition impl_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (rl, show rl)) (list_of_schedule (core1_schedule)).

    Definition impl_typecheck_fn (rl: action) : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs
              (inline_rule int_fns rl).

    Definition impl_schedule :=
      preprocess_schedule impl_typecheck_fn rules impl_schedule_list.
    (* Goal preprocess_schedule_success impl_typecheck_fn Core.rules impl_schedule_list = true. *)
    (* Proof. vm_compute; reflexivity. Qed. *)
    Definition impl_machine : machine_t :=
      {| file_registers := reg_types;
         file_ext_sigma := ext_fn_tys;
         file_struct_defs := struct_defs;
      |}.

  End ImplMachine.
  Definition file: file_t :=
    {| file_machines := Single impl_machine impl_schedule;
       file_assumptions := preprocess_fancy_spreds (pre_conds CoreId1 impl_init );
       file_assertions := preprocess_fancy_spreds (post_conds CoreId1 impl_init impl_final impl_final_ext);
    |}.
End Core1_Defs.

Module Type SMT_Core0_sig
  (EnclaveParams: EnclaveParams_sig)
  (SecurityParams: SecurityParams_sig EnclaveParams)
  (Core0Defs: Core0_Defs EnclaveParams SecurityParams).

  Parameter SMT_file_ok: SymbolicInterp.WF_single_file Core0Defs.file = true.

End SMT_Core0_sig.
Module Type SMT_Core1_sig
  (EnclaveParams: EnclaveParams_sig)
  (SecurityParams: SecurityParams_sig EnclaveParams)
  (Core1Defs: Core1_Defs EnclaveParams SecurityParams).

  Parameter SMT_file_ok: SymbolicInterp.WF_single_file Core1Defs.file = true.

End SMT_Core1_sig.



Module Core0Proofs (EnclaveParams: EnclaveParams_sig)
                   (SecurityParams: SecurityParams_sig EnclaveParams)
                   (Core0Defs: Core0_Defs EnclaveParams SecurityParams)
                   (SMT_ok: SMT_Core0_sig EnclaveParams SecurityParams Core0Defs).
  Import CoreSymbDefs.
  Import Core0Defs.
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SMT_ok.

  Theorem smt_core_correct:
    symbolic_evaluate_file_success_single
      impl_machine impl_schedule (preprocess_fancy_spreds (pre_conds CoreId0 impl_init)) (preprocess_fancy_spreds (post_conds CoreId0 impl_init impl_final impl_final_ext)).
  Proof.
    specialize symbolic_evaluate_file_success with (file := file).
    replace (file_machines file) with (Single impl_machine impl_schedule) by vm_reflect.
    replace (file_assumptions file) with (preprocess_fancy_spreds (pre_conds CoreId0 impl_init)) by vm_reflect.
    replace (file_assertions file) with (preprocess_fancy_spreds (post_conds CoreId0 impl_init impl_final impl_final_ext)) by vm_reflect.
    pose proof SMT_file_ok.
    auto.
  Qed.
  Lemma ext_fn_taint_schedule_empty':
    match (ext_fn_taint_schedule id_int_fns id_rules SortedExtFnEnv.empty core0_schedule) with
    | Success (Some log) => beq_dec (SortedExtFnEnv.to_list log) []
    | _ => false
    end = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  Lemma ext_fn_taint_schedule_empty:
    ext_fn_taint_schedule id_int_fns id_rules SortedExtFnEnv.empty core0_schedule = Success (Some (SortedExtFnEnv.empty)).
  Proof.
    pose proof ext_fn_taint_schedule_empty'. bash_destruct H. rewrite beq_dec_iff in H.
    f_equal. f_equal.
    apply SortedExtFnEnv.env_ext. intros.
    apply SortedExtFnEnv.to_list_ext. rewrite H. reflexivity.
  Qed.
  (* Lemma oraat_schedule_ok: *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule core0_schedule) = true. *)
  (* Proof. *)
  (*   vm_compute. reflexivity. *)
  (* Qed. *)
  Theorem sched_correct:
    interp_scheduler_satisfies_spec reg_type_env _ext_fn_tys id_int_fns id_struct_defs
      id_rules core0_schedule unit
      (fun st sigma _ => CorePre CoreId0 st )
      (fun st sigma st' ext_log _ => CorePost CoreId0 st st' sigma ext_log).
  Proof.
    unfold interp_scheduler_satisfies_spec.
    intros * _ hwf_st hwf_sigma hwf_fns hinterp hpre.
    specialize typecheck_scheduler_correct'' with
      (5 := hinterp) (2 := hwf_st) (3 := hwf_sigma) (4 := hwf_fns) (1 := eq_refl);
      intros (hwf_impl' & wf_impl_ext').
    split_ands_in_goal; auto.
    consider CorePost.
    specialize smt_core_correct. unfold symbolic_evaluate_file_success_single.
    intros.
    rewrite<-forall_preprocess_fancy_spreds_correct.
    consider CorePre.
    apply H.
    + revert hpre.
      repeat rewrite forall_preprocess_fancy_spreds_correct.
      repeat rewrite Forall_map_snd.
      apply forall_interp_fancy_spred_package_equiv'; solve_package_equiv.
    + unfold machine_to_prop. split_ands_in_goal.
      * auto.
      * apply strong_WF_state_weaken in hwf_st.
        eapply WF_state_subset with (2 := hwf_st). vm_compute; reflexivity.
      * unfold impl_schedule. consider impl_schedule_list.
        move hinterp at bottom. consider impl_typecheck_fn.
        set (strip_dbg_sched_list _ ) as l in *.
        assert (l = (map (fun rl => id_transform_action _id (rules rl)) (list_of_schedule core0_schedule))) as Hl.
        { vm_reflect. }
        rewrite Hl.
        consider id_rules.
        apply interp_scheduler_list_equiv.
        apply hinterp.
  Qed.

End Core0Proofs.

Module Core1Proofs (EnclaveParams: EnclaveParams_sig)
                        (SecurityParams: SecurityParams_sig EnclaveParams)
                        (Core1Defs: Core1_Defs EnclaveParams SecurityParams)
                        (SMT_ok: SMT_Core1_sig EnclaveParams SecurityParams Core1Defs).

  Import CoreSymbDefs.
  Import Core1Defs.
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SMT_ok.

  Theorem smt_core_correct:
    symbolic_evaluate_file_success_single
      impl_machine impl_schedule (preprocess_fancy_spreds (pre_conds CoreId1 impl_init)) (preprocess_fancy_spreds (post_conds CoreId1 impl_init impl_final impl_final_ext)).
  Proof.
    specialize symbolic_evaluate_file_success with (file := file).
    replace (file_machines file) with (Single impl_machine impl_schedule) by vm_reflect.
    replace (file_assumptions file) with (preprocess_fancy_spreds (pre_conds CoreId1 impl_init)) by vm_reflect.
    replace (file_assertions file) with (preprocess_fancy_spreds (post_conds CoreId1 impl_init impl_final impl_final_ext)) by vm_reflect.
    pose proof SMT_file_ok.
    auto.
  Qed.
  Lemma ext_fn_taint_schedule_empty':
    match (ext_fn_taint_schedule id_int_fns id_rules SortedExtFnEnv.empty core1_schedule) with
    | Success (Some log) => beq_dec (SortedExtFnEnv.to_list log) []
    | _ => false
    end = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  Lemma ext_fn_taint_schedule_empty:
    ext_fn_taint_schedule id_int_fns id_rules SortedExtFnEnv.empty core1_schedule = Success (Some (SortedExtFnEnv.empty)).
  Proof.
    pose proof ext_fn_taint_schedule_empty'. bash_destruct H. rewrite beq_dec_iff in H.
    f_equal. f_equal.
    apply SortedExtFnEnv.env_ext. intros.
    apply SortedExtFnEnv.to_list_ext. rewrite H. reflexivity.
  Qed.
  (* Lemma oraat_schedule_ok: *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule core1_schedule) = true. *)
  (* Proof. *)
  (*   vm_compute. reflexivity. *)
  (* Qed. *)
  Theorem sched_correct:
    interp_scheduler_satisfies_spec reg_type_env _ext_fn_tys id_int_fns id_struct_defs
      id_rules core1_schedule unit
      (fun st sigma _ => CorePre CoreId1 st )
      (fun st sigma st' ext_log _ => CorePost CoreId1 st st' sigma ext_log).
  Proof.
    unfold interp_scheduler_satisfies_spec.
    intros * _ hwf_st hwf_sigma hwf_fns hinterp hpre.
    specialize typecheck_scheduler_correct'' with
      (5 := hinterp) (2 := hwf_st) (3 := hwf_sigma) (4 := hwf_fns) (1 := eq_refl);
      intros (hwf_impl' & wf_impl_ext').
    split_ands_in_goal; auto.
    consider CorePost.
    specialize smt_core_correct. unfold symbolic_evaluate_file_success_single.
    intros.
    rewrite<-forall_preprocess_fancy_spreds_correct.
    consider CorePre.
    apply H.
    + revert hpre.
      repeat rewrite forall_preprocess_fancy_spreds_correct.
      repeat rewrite Forall_map_snd.
      apply forall_interp_fancy_spred_package_equiv'; solve_package_equiv.
    + unfold machine_to_prop. split_ands_in_goal.
      * auto.
      * apply strong_WF_state_weaken in hwf_st.
        eapply WF_state_subset with (2 := hwf_st). vm_compute; reflexivity.
      * unfold impl_schedule. consider impl_schedule_list.
        move hinterp at bottom. consider impl_typecheck_fn.
        set (strip_dbg_sched_list _ ) as l in *.
        assert (l = (map (fun rl => id_transform_action _id (rules rl)) (list_of_schedule core1_schedule))) as Hl.
        { vm_reflect. }
        rewrite Hl.
        consider id_rules.
        apply interp_scheduler_list_equiv.
        apply hinterp.
  Qed.


End Core1Proofs.
