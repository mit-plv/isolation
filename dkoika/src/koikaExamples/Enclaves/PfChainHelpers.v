Require Import rv_isolation.Common.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koikaExamples.Enclaves.ProofUtils.
Require Import koikaExamples.Enclaves.PfDefs.
Require Import koikaExamples.Enclaves.ProofCore_symb.
Require Import koikaExamples.Enclaves.SmProofs.
Require Import koikaExamples.Enclaves.MemoryProofs.
Require Import koikaExamples.Enclaves.SymbSpec.
Require Import koikaExamples.Enclaves.PfImplDefs.
Require Import koikaExamples.Enclaves.PfImplLemmas_sig.
Require Import koikaExamples.Enclaves.PfChain.
Require Import koikaExamples.Enclaves.PfSim_sig.
Require Import koikaExamples.Enclaves.PfImplHelpers.
Require Import koikaExamples.Enclaves.PfChainHelpers_sig.
Import TopLevelModuleHelpers.

Module PfChainHelpers (EnclaveParams: EnclaveParams_sig)
                   (SecurityParams: SecurityParams_sig EnclaveParams)
                   (* (Core0Defs : Core0_Defs EnclaveParams SecurityParams) *)
                   (* (Core1Defs : Core1_Defs EnclaveParams SecurityParams) *)
                   (* (MemDefs : MemoryProofDefs EnclaveParams SecurityParams) *)
                   (* (SmDefs :  SmProofDefs EnclaveParams SecurityParams) *)
                   (ImplDefs: PfImplDefs EnclaveParams SecurityParams)
                   (SmtOk: SMT_Chain_sig EnclaveParams)
                   (PfChain: PfChain.PfChain EnclaveParams SecurityParams SmtOk)
                   : PfChainHelpers_sig EnclaveParams SecurityParams ImplDefs.

(* Module Core0Proofs := Core0Proofs EnclaveParams SecurityParams Core0Defs. *)
(* Module Core1Proofs := Core1Proofs EnclaveParams SecurityParams Core1Defs. *)
(* Module MemProof := MemProofs EnclaveParams SecurityParams MemDefs. *)
(* Module SmProof := SmProofs EnclaveParams SecurityParams SmDefs. *)
Module Import ImplHelpers := ImplHelpers EnclaveParams SecurityParams ImplDefs.
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.

  Import SecurityParams.
  Import ExternalMemory.
  Import ImplDefs.
  Import PfChain.
  Import Utils.PfHelpers.
  Import TopLevelModuleHelpers.
  Module Import PfLemmas := PfLemmas EnclaveParams SecurityParams .

  Lemma ImplInvariant_destruct:
    forall st,
      strong_WF_state reg_type_env st.(machine_koika_st) ->
      WF_ext_mem (machine_mem_st st) ->
      ImplInvariant_spreds EnclaveParams.enclave_sig (st) ->
      ImplInvariant st.
  Proof.
    intros * hwf_st hwf_mem pres. consider ImplInvariant_spreds.
    propositional; constructor; auto.
  Qed.

  Lemma ImplInvariant_implies_spreds:
    forall st,
      ImplInvariant st ->
      ImplInvariant_spreds EnclaveParams.enclave_sig st.
  Proof.
    intros * H; destruct H; propositional.
    constructor; auto.
  Qed.

Import PfHelpers.
Import CoreSymbDefs.
Import SymbSimDefs.

Import SymbPfChain.
Import SMSymbDefs.

Ltac init_interp ::=
  repeat
   match goal with
   | |- dummy_interp _ _ _ _ _ _ => unfold dummy_interp, dummy_pkg
   | |- Forall (fun '(_, p) => interp_fancy_spred _ _) _ => rewrite <- forall_preprocess_fancy_spreds_correct
   | |- Forall (fun '(_, p) => interp_fancy_spred2 _ _ _) _ => rewrite <- forall_preprocess_fancy_spreds_correct2
   end.
  Lemma ImplInvariant_implies_sm_inv:
    forall init_st mid_st final_st ext_log1 ext_log2 sigma input,
    ImplInvariant init_st ->
    sigma = mk_sigma_fn (machine_mem_st init_st) input ->
    dummy_interp (machine_koika_st init_st) mid_st final_st sigma ext_log1 ext_log2
      (map_fst CustomSM (sm_invariant EnclaveParams.enclave_sig impl_init impl_get_field)).
  Proof.
    intros * hinv sigma. subst.
    specialize ImplInv_SMInvariant with (1 := hinv) (input := dummy_input_t).
    consider SMPre. consider sm_pre_conds. rewrite Forall_app. unfold dummy_interp. propositional.
    apply Forall_ignore_map_fst. revert H1.
    repeat rewrite<-forall_preprocess_fancy_spreds_correct.
    apply forall_interp_spred_package_equiv; solve_package_equiv.
  Qed.
Hint Resolve WF_mk_sigma_fn: modularity.
#[global] Hint Resolve @WF_ext_log__empty: modularity.
#[global] Hint Resolve strong_WF_state_weaken : modularity.
#[global] Hint Resolve @ImplInv_Core0Invariant: modularity.
#[global] Hint Resolve @ImplInv_Core1Invariant: modularity.
#[global] Hint Resolve @ImplInv_WF_ext_mem : modularity.
#[global] Hint Resolve @ImplInv_WF_state : modularity.
#[global] Hint Resolve @ImplInv_WF_state : solve_invariants.
#[global] Hint Resolve @WF_mk_sigma_fn: solve_invariants.
(* #[global] Hint Resolve @WF_mk_sigma_fn': solve_invariants. *)
#[global] Hint Resolve @ImplInv_WF_ext_mem: solve_invariants.
#[global] Hint Rewrite ext_log_app_empty_r: solve_invariants.
#[global] Hint Resolve WF_ext_log_app : modularity.

Ltac solve_package_equiv ::=
  constructor; unfold package_equiv_taint'; split_ands_in_goal;
   (solve [ left; trivial ]) || (right; vm_compute; reflexivity).
Lemma mem_step_put_valid_implied:
  forall ext_log mem mem' arg input,
  WF_ext_log _ext_fn_tys ext_log ->
  mainmem__ext (unsafe_get_ext_call_from_log ext_log (_ext ext_mainmem)) mem  = Success mem' ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid Memory.Memory.mem_output))
        (_fld Memory.Memory.mem_output "get_valid")
        (unsafe_call_ext (mk_sigma_fn mem' input) (_id (_extid ext_mainmem)) arg) = Ob~1 ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid Memory.Memory.mem_input))
    (_fld Memory.Memory.mem_input "put_valid") (unsafe_get_ext_call_from_log ext_log (_id (_extid ext_mainmem))) =
  Ob~1.
Proof.
  intros * hwf. intros. consider mainmem__ext. simplify.
  bash_destruct H.
  { consider update_dram. simplify. destruct_matches_in_hyp H; simplify.
    - eapply _get_field_implies_unsafe_get_field with (1 := Heqr0); auto.
    - cbv in H0. discriminate.
  }
  { simplify. cbv in H0. discriminate. }
Qed.
Lemma or_zeroes:
  forall v,
  or v (zeroes (Datatypes.length v)) = Success v.
Proof.
  unfold or. induction v; auto.
  simpl. setoid_rewrite IHv. rewrite orb_false_r. auto.
Qed.

Lemma unsafe_get_ext_call_from_log_app_empty_r:
  forall log1 log2 fn,
  WF_ext_log _ext_fn_tys log1 ->
  unsafe_get_ext_call_from_log log2 fn = zeroes (unsafe_get_ext_fn_arg_type fn) ->
  unsafe_get_ext_call_from_log (ext_log_app log1 log2) fn =
  unsafe_get_ext_call_from_log log1 fn.
Proof.
  consider ext_log_app. consider unsafe_get_ext_call_from_log.
  consider SemanticUtils.unsafe_get_ext_call_from_log.
  intros. rewrite SortedExtFnEnv.opt_get_mapV.
  rewrite SortedExtFnEnv.opt_get_zip_default.
  consider unsafe_get_ext_fn_arg_type.
  destruct_all_matches; auto.
  consider WF_ext_log. specialize H with (1 := Heqo). propositional.
  consider SemanticUtils.unsafe_get_ext_fn_arg_type.
  setoid_rewrite H0.
  rewrite or_zeroes. auto.
Qed.

  Lemma mem_step_implies:
  forall init_st impl_st__koika impl_st__mem koika_log ext_log mid_ext_log input,
  strong_WF_state reg_type_env init_st ->
  WF_ext_mem impl_st__mem ->
  WF_ext_log _ext_fn_tys mid_ext_log ->
  WF_ext_log _ext_fn_tys ext_log ->
  ImplInvariant {| machine_koika_st := init_st;
                   machine_mem_st := impl_st__mem
                |} ->
  ImplInvariant {| machine_koika_st := impl_st__koika;
                   machine_mem_st := impl_st__mem
                |} ->
  strong_WF_state reg_type_env (commit_update (impl_st__koika) koika_log) ->
  MemSymbDefs.MemPost (impl_st__koika) (commit_update (impl_st__koika) koika_log) (mk_sigma_fn impl_st__mem input) ext_log ->
  dummy_interp init_st (impl_st__koika) (commit_update (impl_st__koika) koika_log)
               (mk_sigma_fn impl_st__mem input)
               (Some mid_ext_log) ext_log
               (SymbPfChain.post_core1_exprs impl_init impl_mid impl_mid_ext) ->
  exists mem,
  update_memory
    (unsafe_get_ext_call_from_log (ext_log_app ext_log mid_ext_log) (_ext ext_mainmem))
                        impl_st__mem  = Success mem /\
    ImplInvariant {| machine_koika_st := (commit_update (impl_st__koika) koika_log);
                     machine_mem_st := mem |} /\
          dummy_interp init_st (impl_st__koika) (commit_update (impl_st__koika) koika_log)
                       (mk_sigma_fn mem input)
                         (Some mid_ext_log) ext_log
                         (SymbPfChain.post_mem_exprs impl_init impl_final impl_committed_ext impl_get_field).
  Proof.
    intros * hwf_init hwf_sigma hwf_mid_ext_log hwf_ext_log hinv_init hinv hwf' hpost hcore1.
    set {| machine_koika_st := init_st; machine_mem_st := impl_st__mem |} as st_init in *.
    set {| machine_koika_st := impl_st__koika; machine_mem_st := impl_st__mem |} as st_mid in *.
    set (commit_update impl_st__koika koika_log) as final_koika_st.
    specialize ImplInvariant_implies_spreds with (1 := hinv); intros hpres.
    specialize ImplInvariant_implies_spreds with (1 := hinv_init); intros hpres_init.

    assert (WF_ext_log _ext_fn_tys (ext_log_app ext_log mid_ext_log)) as hwf_log_app.
    { eauto with modularity. }
    specialize symbolic_evaluate_file_success with (file := impl_mem_step_file EnclaveParams.enclave_sig).
    set (mk_sigma_fn impl_st__mem input) as sigma in *.

    assert (SymbolicInterp.WF_single_file (impl_mem_step_file EnclaveParams.enclave_sig) = true) as Hwf_file.
    { apply WF_impl_mem_step_file. }

    assert (WF_abstract_state_set dummy_machine sigma init_st
              impl_st__koika final_koika_st  mid_ext_log ext_log) as Hwf_step.
    { unfold WF_abstract_state_set; repeat unsafe_weaken_strong_WF; split_ands_in_goal; eauto with modularity.
      eapply ImplInv_WF_state with (1 := hinv); eauto.
    }
    intros Hok.
    cbn [file_machines impl_mem_step_file] in Hok. propositional.
    unfold symbolic_evaluate_file_success_abstract_single in *.
    specialize Hok with (sigma := sigma) (st := init_st)
                        (st' := final_koika_st) (mid_ext_log := mid_ext_log)
                        (ext_log' := ext_log) (2 := Hwf_step).
    assert_pre_as Hassumes Hok; [clear Hok| specialize Hok with (1 := Hassumes)].
    {
      unfold impl_mem_step_file. unfold file_assumptions.
      do 3 rewrite Forall_app. split_ands_in_goal.
      - unfold sigma. replace init_st with (machine_koika_st st_init) by auto.
        replace impl_st__mem with (machine_mem_st st_init) by auto.
        apply ImplInvariant_spreds_implies_invariant_spreds'_init; auto.
      - unfold sigma. replace impl_st__koika with (machine_koika_st st_mid) by auto.
        replace impl_st__mem with (machine_mem_st st_mid) by auto.
        apply ImplInvariant_spreds_implies_invariant_spreds'_mid.  auto.
      - consider dummy_interp. consider dummy_pkg. init_interp_in hcore1.
        revert hcore1.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      - consider MemSymbDefs.MemPost. init_interp_in hpost.
        replace_mid_st_in hpost (Some impl_st__koika); [ | solve_package_equiv ].
        rewrite Lift_Forall with (g := replace_spred_init_reg_with_mid) in hpost;
          [ | solve[ intro q; apply replace_fancy_spred_init_reg_with_mid_correct with (p := PBase q); auto] ].
        change_Forall_lists1 hpost.
        revert hpost.
        apply forall_interp_spred_package_equiv. solve_package_equiv.
    }
    unfold file_assertions, impl_mem_step_file in Hok.
    rewrite Forall_app in Hok. destruct Hok as (Hok & hpost1).

    consider update_memory.
    specialize mem_push_request__success with (log := ext_log_app ext_log mid_ext_log) (2 := hwf_sigma); intros hsuccess.
    propositional. simplify. exists s; split; auto.
    split.
    - apply ImplInvariant_destruct; eauto with modularity.
      eapply ImplInvariant_spreds_implied with (mid_st:= impl_st__koika) (final_st := final_koika_st)
                                               (ext_log1 := Some mid_ext_log) (ext_log2 := ext_log) (input := input) (1 := eq_refl).
      + replace impl_st__koika with (machine_koika_st {| machine_koika_st := impl_st__koika;
                                                      machine_mem_st := impl_st__mem
                                                    |}) by reflexivity.
        replace final_koika_st with (machine_koika_st {| machine_koika_st := final_koika_st;
                                                         machine_mem_st := s
                                                      |}) by reflexivity.
        eapply ImplInvariant_spreds_implies_invariant_spreds'_init'. unfold machine_koika_st.
        eapply Hok.
      + unfold file_assumptions, impl_mem_step_file in Hassumes.
        unfold MemSymbDefs.mem_pre_conds'.
        do 3 rewrite Forall_app in Hassumes. destruct Hassumes as (_hinv_init & _hinv_mid  & _hpost_core1 & _hpost_mem).
        rewrite forall_preprocess_fancy_spreds_correct in _hpost_mem.
        rewrite forall_preprocess_fancy_spreds_correct in _hpost_core1.
        prop_pose_with_custom hmem (PfChain.CustomExtFn ((_ext ext_mainmem))) _hpost_core1.

        cbn - [_id _sid _fld].
        repeat constructor.
        { cbn - [_id _sid _fld mk_sigma_fn].
          prop_pose_with_custom  hfoo
            ((MemoryProofs.MemImplExtCorrectCore CoreId0)) _hpost_mem.
          cbn - [_id _sid _fld mk_sigma_fn] in hfoo.
          intros. apply hfoo; auto.
          rewrite unsafe_get_ext_call_from_log_app_empty_r in Heqr0; auto.
          eapply mem_step_put_valid_implied; eauto.
        }
        { cbn - [_id _sid _fld mk_sigma_fn].
          prop_pose_with_custom  hfoo
            ((MemoryProofs.MemImplExtCorrectCore CoreId1)) _hpost_mem.
          cbn - [_id _sid _fld mk_sigma_fn] in hfoo.
          intros. apply hfoo; auto.
          rewrite unsafe_get_ext_call_from_log_app_empty_r in Heqr0; auto.
          eapply mem_step_put_valid_implied; eauto.
        }
    - clear - hpost1. unfold dummy_interp.
      init_interp. revert hpost1.
      apply forall_interp_spred_package_equiv. solve_package_equiv.
  Qed.

  Lemma sm_step_implies:
    forall init_st impl_st__koika impl_st__mem  impl_mem__init koika_log ext_log mid_ext_log input,
    strong_WF_state reg_type_env init_st ->
    WF_ext_log _ext_fn_tys mid_ext_log ->
    WF_ext_log _ext_fn_tys ext_log ->
    WF_ext_mem impl_st__mem  ->
    ImplInvariant {| machine_koika_st := init_st;
                     machine_mem_st := impl_mem__init
                  |} ->
    ImplInvariant {| machine_koika_st := impl_st__koika;
                     machine_mem_st := impl_st__mem
                  |} ->
    strong_WF_state reg_type_env (commit_update (impl_st__koika) koika_log) ->
    SMPost EnclaveParams.enclave_sig (impl_st__koika) (commit_update (impl_st__koika) koika_log)
      (mk_sigma_fn impl_mem__init input) ext_log ->
    dummy_interp init_st (impl_st__koika) (commit_update (impl_st__koika) koika_log)
                 (mk_sigma_fn impl_st__mem input)
                 (Some mid_ext_log) ext_log
                 (post_mem_exprs impl_init impl_mid impl_mid_ext impl_get_field) ->
    ImplInvariant {| machine_koika_st := (commit_update (impl_st__koika) koika_log);
                     machine_mem_st := impl_st__mem |} /\
    dummy_interp init_st (impl_st__koika)
                     (commit_update (impl_st__koika) koika_log)
                     (mk_sigma_fn impl_st__mem input)
                     (Some mid_ext_log) ext_log
                     (post_sm_exprs EnclaveParams.enclave_sig impl_init impl_final
                                    impl_mid_ext impl_committed_ext impl_get_field).
  Proof.
    intros * hwf_init hwf_mid_ext_log hwf_ext_log hwf_mem hinv_init hinv hwf' hpost hmem.
    set {| machine_koika_st := init_st; machine_mem_st := impl_mem__init |} as st_init in *.
    set {| machine_koika_st := impl_st__koika; machine_mem_st := impl_st__mem |} as st_mid in *.
    set (commit_update impl_st__koika koika_log) as final_koika_st.
    set {| machine_koika_st := final_koika_st;
           machine_mem_st := impl_st__mem
        |} as final_st in *.

    specialize ImplInvariant_implies_spreds with (1 := hinv); intros hpres.
    specialize ImplInvariant_implies_spreds with (1 := hinv_init); intros hpres_init.

    assert (WF_ext_log _ext_fn_tys (ext_log_app ext_log mid_ext_log)) as hwf_log_app.
    { eauto with modularity. }
    specialize symbolic_evaluate_file_success with (file := (impl_sm_step_file EnclaveParams.enclave_sig)).
    set (mk_sigma_fn impl_st__mem input) as sigma in *.

    assert (SymbolicInterp.WF_single_file (impl_sm_step_file EnclaveParams.enclave_sig) = true) as Hwf_file.
    { apply WF_impl_sm_step_file. }

    assert (WF_abstract_state_set dummy_machine sigma init_st
              impl_st__koika final_koika_st  mid_ext_log ext_log) as Hwf_step.
    { unfold WF_abstract_state_set; repeat unsafe_weaken_strong_WF; split_ands_in_goal; eauto with modularity.
      eapply ImplInv_WF_state with (1 := hinv); eauto.
    }
    intros Hok.
    cbn [file_machines impl_sm_step_file] in Hok. propositional.
    unfold symbolic_evaluate_file_success_abstract_single in *.
    specialize Hok with (sigma := sigma) (st := init_st)
                        (st' := final_koika_st) (mid_ext_log := mid_ext_log)
                        (ext_log' := ext_log) (2 := Hwf_step).
    assert_pre_as Hassumes Hok; [clear Hok| specialize Hok with (1 := Hassumes)].
    {
      unfold impl_sm_step_file. unfold file_assumptions.
      do 3 rewrite Forall_app. split_ands_in_goal.
      - replace init_st with (machine_koika_st st_init) by auto.
        replace impl_st__koika with (machine_koika_st st_mid) by reflexivity.
        replace final_koika_st with (machine_koika_st final_st) by reflexivity.
        apply ImplInvariant_spreds_implies_invariant_spreds'_init.
        auto.
      - unfold sigma. replace impl_st__koika with (machine_koika_st st_mid) by auto.
        replace impl_st__mem with (machine_mem_st st_mid) by auto.
        apply ImplInvariant_spreds_implies_invariant_spreds'_mid.  auto.
      - consider dummy_interp. consider dummy_pkg. init_interp_in hmem.
        revert hmem.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      - consider SMPost. init_interp_in hpost.
        replace_mid_st_in hpost (Some impl_st__koika); [ | solve_package_equiv ].
        rewrite Lift_Forall with (g := replace_spred_init_reg_with_mid) in hpost;
          [ | solve[ intro q; apply replace_fancy_spred_init_reg_with_mid_correct with (p := PBase q); auto] ].
        change_Forall_lists1 hpost.
        revert hpost.
        apply forall_interp_spred_package_equiv. solve_package_equiv.
    }
    unfold file_assertions, impl_sm_step_file in Hok.
    rewrite Forall_app in Hok. destruct Hok as (Hok & hpost1).
    split.
    - apply ImplInvariant_destruct; eauto with modularity.
      eapply ImplInvariant_spreds_implied with (mid_st:= impl_st__koika) (final_st := final_koika_st)
                                               (ext_log1 := Some mid_ext_log) (ext_log2 := ext_log) (input := input) (1 := eq_refl).
      + replace impl_st__koika with (machine_koika_st {| machine_koika_st := impl_st__koika;
                                                      machine_mem_st := impl_st__mem
                                                    |}) by reflexivity.
        replace final_koika_st with (machine_koika_st {| machine_koika_st := final_koika_st;
                                                         machine_mem_st := impl_st__mem
                                                      |}) by reflexivity.
        eapply ImplInvariant_spreds_implies_invariant_spreds'_init'.
        eapply Hok.
      + replace impl_st__koika with (machine_koika_st {| machine_koika_st := impl_st__koika;
                                                      machine_mem_st := impl_st__mem
                                                    |}) by reflexivity.
        replace final_koika_st with (machine_koika_st {| machine_koika_st := final_koika_st;
                                                         machine_mem_st := impl_st__mem
                                                      |}) by reflexivity.
        unfold file_assumptions, impl_sm_step_file in Hassumes.
        do 3 rewrite Forall_app in Hassumes. destruct Hassumes as (hinv_init' & hinv_mid & hpost_mem & hpost_sm).
        rewrite forall_preprocess_fancy_spreds_correct in hpost_sm.
        prop_pose_with_custom hfoo (SM_taint) hpost_sm.
        set (remove_regs reg_list (map reg_to_debug_id (sm_regs CoreId0 ++ sm_regs CoreId1))) in hfoo.
        vm_compute in l.
        consider dummy_interp.
        rewrite Forall_ignore_map_fst. erewrite<-Forall_ignore_map_fst with (g := PfChain.CustomMem).
        eapply mem_pre_conds_implied with(enclave_sig := EnclaveParams.enclave_sig); auto; unfold machine_koika_st.
        { apply hfoo. solve_In_to_find. }
        { apply hfoo. solve_In_to_find. }
    - clear - hpost1. unfold dummy_interp.
      init_interp. revert hpost1.
      apply forall_interp_spred_package_equiv. solve_package_equiv.
  Qed.



  Lemma core0_step_preserve_invariant':
    forall st st' ext_log input,
    strong_WF_state reg_type_env (machine_koika_st st) ->
    strong_WF_state reg_type_env (machine_koika_st st') ->
    WF_ext_mem (machine_mem_st st) ->
    WF_ext_log _ext_fn_tys ext_log ->
    (machine_mem_st st')  = machine_mem_st st ->
    ImplInvariant_spreds EnclaveParams.enclave_sig st ->
    CoreSymbDefs.CorePost CoreId0 (machine_koika_st st) (machine_koika_st st')
      (mk_sigma_fn (machine_mem_st st) input ) ext_log ->
    ImplInvariant_spreds EnclaveParams.enclave_sig st'.
  Proof.
    intros * hwf hwf' hwf_mem hwf_ext_log hmemeq hinv Core0_post.
    specialize symbolic_evaluate_file_success with (file := (impl_core0_step_file EnclaveParams.enclave_sig)).
    set (mk_sigma_fn (machine_mem_st st) input) as sigma in *.
    assert (SymbolicInterp.WF_single_file (impl_core0_step_file EnclaveParams.enclave_sig) = true) as Hwf_file.
    { apply WF_impl_core0_step_file. }
    assert (WF_abstract_state_set dummy_machine sigma (machine_koika_st st) (machine_koika_st st) (machine_koika_st st') SortedExtFnEnv.empty ext_log) as Hwf_step.
    { unfold WF_abstract_state_set; repeat unsafe_weaken_strong_WF; split_ands_in_goal;
        eauto with modularity.
    }
    intros Hok.
    cbn [file_machines impl_core0_step_file] in Hok. propositional.
    unfold symbolic_evaluate_file_success_abstract_single in *.
    specialize Hok with (sigma := sigma) (st := machine_koika_st st) (mid_st := machine_koika_st st) (st' := machine_koika_st st') (mid_ext_log := SortedExtFnEnv.empty) (ext_log' := ext_log) (2 := Hwf_step).
    assert_pre_as Hassumes Hok; [clear Hok| specialize Hok with (1 := Hassumes)].
    { unfold impl_core0_step_file. unfold file_assumptions.
      rewrite forall_interp_spred_preprocess_app_iff.
      rewrite Forall_app; split_ands_in_goal.
      - apply  ImplInvariant_spreds_implies_invariant_spreds'_init; auto.
      - consider CoreSymbDefs.CorePost .
        rewrite<-forall_preprocess_fancy_spreds_correct in Core0_post.
        rewrite preprocess_fancy_spreds_map_fst_equiv.
        revert Core0_post.
        eapply forall_interp_spred_package_equiv; solve_package_equiv.
    }
    unfold file_assertions, impl_core0_step_file in Hok.
    eapply ImplInvariant_spreds_implied with (mid_st:= (machine_koika_st st)) (final_st := machine_koika_st st') (ext_log1 := Some SortedExtFnEnv.empty) (ext_log2 := ext_log) (input := input) (1 := eq_refl).
    - eapply ImplInvariant_spreds_implies_invariant_spreds'_init' with (1 := Hok).
    - unfold file_assumptions, impl_core0_step_file in Hassumes.
      rewrite forall_preprocess_fancy_spreds_correct in Hassumes.
      prop_pose_with_custom htaint (CustomCore0 CoreTaint) Hassumes.
      set (remove_regs reg_list  (map reg_to_debug_id (core_regs CoreId0))) in htaint. vm_compute in l.
      unfold dummy_interp.
      rewrite Forall_ignore_map_fst. erewrite<-Forall_ignore_map_fst with (g := PfChain.CustomMem).

      eapply mem_pre_conds_implied with(enclave_sig := EnclaveParams.enclave_sig); auto.
      + apply htaint. solve_In_to_find.
      + apply htaint. solve_In_to_find.
  Qed.

  Lemma core0_step_preserve_invariant:
    forall impl_st koika_log ext_log input,
    WF_ext_log _ext_fn_tys ext_log ->
    WF_ext_mem (machine_mem_st impl_st) ->
    ImplInvariant impl_st ->
    strong_WF_state reg_type_env (commit_update (machine_koika_st impl_st) koika_log) ->
    CoreSymbDefs.CorePost CoreId0 (machine_koika_st impl_st)
                   (commit_update (machine_koika_st impl_st) koika_log)
                   (mk_sigma_fn (machine_mem_st impl_st) input) ext_log ->
    ImplInvariant {| machine_koika_st := (commit_update (machine_koika_st impl_st) koika_log);
                     machine_mem_st := impl_st.(machine_mem_st) |}.
  Proof.
    intros * hwf_ext_log hwf_mem hinv hwf' hpost.
    apply ImplInvariant_destruct; simpl; eauto with modularity.
    specialize ImplInvariant_implies_spreds with (1 := hinv); intros hpres.
    eapply core0_step_preserve_invariant' with (st := impl_st); eauto with modularity.
  Qed.

Lemma CorePost_implies_post_conds':
  forall core sigma1 sigma2 final_st init_st mid_st post_log final_log,
  CorePost core init_st mid_st sigma2 post_log ->
  dummy_interp init_st mid_st final_st
    sigma1 (Some post_log) final_log (post_conds' core impl_init impl_mid impl_mid_ext).
Proof.
  intros * HPostCore.
  unfold dummy_interp, dummy_pkg.
  init_interp.
  consider CorePost. consider post_conds.
  rewrite Forall_app in HPostCore.
  destruct HPostCore as (HPostCore & HPostCore').
  init_interp_in HPostCore.
  destruct core.
  - replace_final_st_with_mid.
    replace_final_ext_with_mid.
    change_Forall_lists1 HPostCore.
    revert HPostCore.
    apply forall_interp_spred_package_equiv; try solve_package_equiv.
  - replace_final_st_with_mid.
    replace_final_ext_with_mid.
    change_Forall_lists1 HPostCore.
    revert HPostCore.
    apply forall_interp_spred_package_equiv; try solve_package_equiv.
Qed.
Lemma CorePost_implies_post_conds:
  forall core sigma1 sigma2 final_st init_st mid_st post_log final_log,
  CorePost core init_st mid_st sigma2 post_log ->
  dummy_interp init_st mid_st final_st
    sigma1 (Some post_log) final_log (post_conds core impl_init impl_mid impl_mid_ext).
Proof.
  intros * HPostCore.
  unfold dummy_interp, dummy_pkg.
  init_interp.
  consider CorePost. init_interp_in HPostCore.
  destruct core.
  - replace_final_st_with_mid.
    replace_final_ext_with_mid.
    change_Forall_lists1 HPostCore.
    revert HPostCore.
    apply forall_interp_spred_package_equiv; try solve_package_equiv.
  - replace_final_st_with_mid.
    replace_final_ext_with_mid.
    change_Forall_lists1 HPostCore.
    revert HPostCore.
    apply forall_interp_spred_package_equiv; try solve_package_equiv.
Qed.

  Lemma core1_step_implies':
    forall init_st mid_st final_st mid_ext_log ext_log sigma1 sigma2 input,
    strong_WF_state reg_type_env (machine_koika_st init_st) ->
    strong_WF_state reg_type_env mid_st.(machine_koika_st) ->
    strong_WF_state reg_type_env final_st.(machine_koika_st) ->
    WF_ext_mem (machine_mem_st mid_st) ->
    WF_ext_log _ext_fn_tys mid_ext_log ->
    WF_ext_log _ext_fn_tys ext_log ->
    ImplInvariant_spreds EnclaveParams.enclave_sig init_st ->
    ImplInvariant_spreds EnclaveParams.enclave_sig mid_st ->
    (machine_mem_st mid_st) = machine_mem_st final_st ->
    (machine_mem_st init_st) = machine_mem_st final_st ->
    dummy_interp (machine_koika_st init_st) mid_st.(machine_koika_st) final_st.(machine_koika_st)
                 sigma1
                 (Some mid_ext_log) ext_log
        (CoreSymbDefs.post_conds' CoreId0 impl_init impl_mid
                                            impl_mid_ext
        ) ->
    CoreSymbDefs.CorePost CoreId1 mid_st.(machine_koika_st) final_st.(machine_koika_st) (mk_sigma_fn (machine_mem_st mid_st) input) ext_log ->
    ImplInvariant_spreds EnclaveParams.enclave_sig final_st /\
      dummy_interp (machine_koika_st init_st) mid_st.(machine_koika_st) final_st.(machine_koika_st) sigma2
                   (Some mid_ext_log) ext_log
        (SymbPfChain.post_core1_exprs impl_init impl_final impl_committed_ext).
  Proof.
    intros * hwf_init hwf_mid hwf_final hwf_sigma hwf_mid_ext_log hwf_ext_log
             hinv_init hinv hmem0 hmem1 hcore0 hcore1.
    specialize symbolic_evaluate_file_success with (file := (impl_core1_step_file EnclaveParams.enclave_sig)).
    set (mk_sigma_fn (machine_mem_st mid_st) input) as sigma in *.

    assert (SymbolicInterp.WF_single_file (impl_core1_step_file EnclaveParams.enclave_sig) = true) as Hwf_file.
    { apply WF_impl_core1_step_file. }

    assert (WF_abstract_state_set dummy_machine sigma (machine_koika_st init_st)
              mid_st.(machine_koika_st) final_st.(machine_koika_st) mid_ext_log ext_log) as Hwf_step.
    { unfold WF_abstract_state_set; repeat unsafe_weaken_strong_WF; split_ands_in_goal; eauto with modularity.
    }
    intros Hok.
    cbn [file_machines impl_core1_step_file] in Hok. propositional.
    unfold symbolic_evaluate_file_success_abstract_single in *.
    specialize Hok with (sigma := sigma) (st := machine_koika_st init_st)
                        (st' := machine_koika_st final_st) (mid_ext_log := mid_ext_log)
                        (ext_log' := ext_log) (2 := Hwf_step).
    assert_pre_as Hassumes Hok; [clear Hok| specialize Hok with (1 := Hassumes)].
    { unfold impl_core1_step_file. unfold file_assumptions.
      rewrite forall_preprocess_fancy_spreds_correct.
      repeat rewrite Forall_app. split_ands_in_goal.
      - rewrite<-forall_preprocess_fancy_spreds_correct.
        unfold sigma. rewrite hmem0. rewrite<-hmem1.
        apply ImplInvariant_spreds_implies_invariant_spreds'_init; auto.
      - rewrite<-forall_preprocess_fancy_spreds_correct.
        apply ImplInvariant_spreds_implies_invariant_spreds'_mid.  auto.
      - rewrite Forall_ignore_map_fst. init_interp.
        consider dummy_interp. consider dummy_pkg. init_interp_in hcore0.
        revert hcore0.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      - consider CorePost. init_interp_in hcore1.
        init_interp.
        replace_mid_st_in hcore1 (Some (machine_koika_st mid_st)); [ | solve_package_equiv ].
        rewrite Lift_Forall with (g := replace_spred_init_reg_with_mid) in hcore1;
          [ | solve[ intro q; apply replace_fancy_spred_init_reg_with_mid_correct with (p := PBase q); auto] ].
        change_Forall_lists1 hcore1.
        revert hcore1.
        apply forall_interp_spred_package_equiv. solve_package_equiv.
    }
    unfold file_assertions, impl_core1_step_file in Hok.
    rewrite Forall_app in Hok. destruct Hok as (Hok & hpost1).
    split.
    - eapply ImplInvariant_spreds_implied with (mid_st:= (machine_koika_st mid_st)) (final_st := machine_koika_st final_st) (ext_log1 := Some mid_ext_log) (ext_log2 := ext_log) (input := input) (1 := eq_refl).
      + eapply ImplInvariant_spreds_implies_invariant_spreds'_init' with (sigma := sigma) (mid_st := Some( machine_koika_st mid_st)).
        eapply Hok.
      + unfold file_assumptions, impl_core1_step_file in Hassumes.
        rewrite forall_preprocess_fancy_spreds_correct in Hassumes.
        prop_pose_with_custom htaint (CustomCore1 CoreTaint) Hassumes.
        set (remove_regs reg_list  (map reg_to_debug_id (core_regs CoreId1))) in htaint. vm_compute in l.
        consider dummy_interp.
        rewrite Forall_ignore_map_fst. erewrite<-Forall_ignore_map_fst with (g := PfChain.CustomMem).
        eapply mem_pre_conds_implied with(enclave_sig := EnclaveParams.enclave_sig); auto.
        * apply htaint. solve_In_to_find.
        * apply htaint. solve_In_to_find.
    - clear - hpost1. unfold dummy_interp.
      init_interp. revert hpost1.
      apply forall_interp_spred_package_equiv. solve_package_equiv.
  Qed.

  Lemma core1_step_preserve_invariant:
    forall init_st impl_st__koika impl_st__mem koika_log ext_log mid_ext_log sigma1 sigma2 input,
    strong_WF_state reg_type_env init_st ->
    WF_ext_mem impl_st__mem  ->
    WF_ext_log _ext_fn_tys mid_ext_log ->
    WF_ext_log _ext_fn_tys ext_log ->
    ImplInvariant {| machine_koika_st := init_st;
                     machine_mem_st := impl_st__mem
                  |} ->
    ImplInvariant {| machine_koika_st := impl_st__koika;
                     machine_mem_st := impl_st__mem
                  |} ->
    strong_WF_state reg_type_env (commit_update impl_st__koika  koika_log) ->
    CoreSymbDefs.CorePost CoreId1 impl_st__koika (commit_update impl_st__koika koika_log)
                 (mk_sigma_fn (impl_st__mem) input)
                   ext_log ->
    dummy_interp init_st impl_st__koika (commit_update impl_st__koika koika_log)
                 sigma1
                 (Some mid_ext_log) ext_log
      (CoreSymbDefs.post_conds' CoreId0 impl_init impl_mid impl_mid_ext) ->
    ImplInvariant {| machine_koika_st := (commit_update impl_st__koika koika_log);
                     machine_mem_st := impl_st__mem |} /\
    dummy_interp init_st impl_st__koika
                         (commit_update impl_st__koika koika_log)
                         sigma2
                         (Some mid_ext_log) ext_log
                         (SymbPfChain.post_core1_exprs impl_init impl_final impl_committed_ext).
  Proof.
    intros * hwf_init hwf_sigma hwf_mid_ext_log hwf_ext_log hinv_init hinv hwf' hpost hcore0.
    set {| machine_koika_st := (commit_update impl_st__koika koika_log);
           machine_mem_st := impl_st__mem |} as final_st.
    specialize ImplInvariant_implies_spreds with (1 := hinv); intros hpres.
    specialize ImplInvariant_implies_spreds with (1 := hinv_init); intros hpres_init.
    specialize core1_step_implies' with
      (init_st := {| machine_koika_st := init_st;
                     machine_mem_st := impl_st__mem |}) (mid_ext_log := mid_ext_log) (final_st := final_st)
      (sigma2 := sigma2) (sigma1 := sigma1)
      (8 := hpres) (12 := hpost);simpl; intros hcore1.
    assert_conclusion_of hcore1 Hnew; [ | clear hcore1].
    { eapply hcore1; auto with modularity.
      eapply ImplInv_WF_state with (1 := hinv); eauto.
    }
    destruct Hnew as (hinv_final & hpost_core1).
    split_ands_in_goal.
    - apply ImplInvariant_destruct; eauto with modularity.
    - assumption.
  Qed.

  Lemma mem_addr_in_config_implied:
    forall core st mid_st final_st mid_log final_log s0 s1 sigma (* st' *),
    WF_state (SortedRegEnv.to_list reg_type_env) st ->
    WF_ext_log _ext_fn_tys (ext_log_app final_log mid_log) ->
    dummy_interp st mid_st final_st sigma (Some mid_log) final_log
                     (post_sm_exprs EnclaveParams.enclave_sig impl_init impl_final
                        impl_mid_ext impl_committed_ext
                        impl_get_field) ->
    st.[_rid (SecurityMonitor.SM (SecurityMonitor.state core))] <> _enum enum_core_state "Waiting" ->
    _get_field mem_input "put_valid"
             (unsafe_get_ext_call_from_log (ext_log_app final_log mid_log) (_ext ext_mainmem)) =
           Success Ob~1 ->
    _get_field mem_input "put_request"
              (unsafe_get_ext_call_from_log (ext_log_app final_log mid_log) (_ext ext_mainmem)) = Success s0 ->
    _get_field (mem_req) ("addr") s0 = Success s1 ->
    st.[_rid (SecurityMonitor.Memory Memory.Memory.turn)] = mem_core_write_turn core ->
    addr_in_config EnclaveParams.enclave_sig (to_N s1) (unsafe_enclave_data_to_config (st.[_rid (SecurityMonitor.SM (SecurityMonitor.enc_data core))])).
  Proof.
    intros * hwf_st hwf_log hpost hnot_waiting hpush_valid hpush_request hreq_addr hturn.
    prop_pose_with_custom hreq0 (Custom_PushReq0) hpost.
    prop_pose_with_custom hreq1 (Custom_PushReq1) hpost.
    assert (Datatypes.length s1 = addr_sz) as haddr_sz.
    { repeat unsafe_auto_simplify_structs. }

    destruct core.
    - cbn - [_id interp_bits2 fs_req_addrs_in_config] in hreq0.
      assert_pre_and_specialize hreq0.
      { rewrite _get_field_implies_unsafe_get_field with (1 := hpush_valid); auto. }
      assert_pre_and_specialize hreq0; auto.
      eapply addr_in_config_implied; eauto.
      unsafe_auto_simplify_structs.
    - cbn - [_id interp_bits2 fs_req_addrs_in_config] in hreq1.
      assert_pre_and_specialize hreq1.
      { rewrite _get_field_implies_unsafe_get_field with (1 := hpush_valid); auto. }
      assert_pre_and_specialize hreq1; auto.
      eapply addr_in_config_implied; eauto.
      unsafe_auto_simplify_structs.
  Qed.

  Lemma mem_push_in_config_implied:
    forall init_st mid_st st mid_log final_log mem sigma,
    WF_ext_log _ext_fn_tys mid_log ->
    WF_ext_log _ext_fn_tys final_log ->
    ImplInvariant {| machine_koika_st := init_st;
                     machine_mem_st := mem
                  |} ->
    dummy_interp init_st mid_st st sigma (Some mid_log) final_log
                     (post_sm_exprs EnclaveParams.enclave_sig impl_init impl_final
                        impl_mid_ext impl_committed_ext
                        impl_get_field) ->
    mem_push_in_config init_st (unsafe_get_ext_call_from_log (ext_log_app final_log mid_log) (_ext ext_mainmem)).
  Proof.
    intros * hwf_mid_log hwf_final_log hinv hpost.
    specialize ImplInv_WF_state with (1 := hinv); intros hwf; simpl in hwf.
    unfold mem_push_in_config, is_mem_core0_push_turn, is_mem_core1_push_turn.
    specialize ImplInvariant_implies_sm_inv with
      (1 := hinv) (mid_st := mid_st) (final_st := st) (ext_log1 := Some mid_log) (ext_log2 := final_log).
    intros hsm_inv.
    evar (sigma': @ext_sigma_t N).
    evar (input': @input_t).
    specialize (hsm_inv sigma' input'). specialize hsm_inv with (1 := eq_refl).
    consider dummy_interp.
    unfold get_ghost_running_config, machine_st_to_ghost_core, mem_addr_in_option_config, ImplDefs.mem_addr_in_option_config, get_valid_addr_from_push_req.
    intros. destruct_all_matches; simplify.
    - prop_pose_with_custom hmem_zero (PfChain.CustomMem Mem_push_zero0) hpost.
      prop_pose_with_custom hsm_waiting (PfChain.CustomSM (SM_inv_waiting CoreId0)) hsm_inv.
      cbn - [_id In core_to_sm_fifos memory_to_sm_fifos sm_to_core_fifos sm_to_memory_fifos] in hsm_waiting, Heqb1, hmem_zero.
      consider @mem_core0_write_turn. propositional.
      cbn - [_id In] in hmem_zero.
      assert_conclusion_of hmem_zero hfalse.
      { apply hmem_zero; auto.
        - apply hsm_waiting4. solve_In_to_find.
        - apply hsm_waiting4. solve_In_to_find.
      }
      unfold unsafe_get_field in hfalse. setoid_rewrite Heqr0 in hfalse. discriminate.
    - consider mem_addr_in_option_config.
      consider addr_in_config.
      eapply mem_addr_in_config_implied with (3 := hpost);eauto with modularity.
    - prop_pose_with_custom hmem_zero (PfChain.CustomMem Mem_push_zero1) hpost.
      prop_pose_with_custom hsm_waiting (PfChain.CustomSM (SM_inv_waiting CoreId1)) hsm_inv.
      cbn - [_id In ] in hsm_waiting, Heqb2, hmem_zero.
      consider @mem_core1_write_turn. propositional.
      cbn - [_id In] in hmem_zero.
      assert_conclusion_of hmem_zero hfalse.
      { apply hmem_zero; auto.
        - apply hsm_waiting4. solve_In_to_find.
        - apply hsm_waiting4. solve_In_to_find.
      }
      unfold unsafe_get_field in hfalse. setoid_rewrite Heqr0 in hfalse. discriminate.
    - consider mem_addr_in_option_config.
      consider addr_in_config.
      eapply mem_addr_in_config_implied with (3 := hpost);eauto with modularity.
    - prop_pose_with_custom hmem_zero (PfChain.CustomMem Mem_push_zero_both) hpost.
      cbn - [_id] in hmem_zero.
      propositional. setoid_rewrite hmem_zero.
      unfold MemSymbDefs.almost_zeroed_mainmem_call.
      auto.
      Unshelve.
      exact dummy_input_t.
  Qed.

End PfChainHelpers.
