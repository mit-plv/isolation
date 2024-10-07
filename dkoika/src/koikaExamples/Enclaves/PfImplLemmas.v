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



Module PfImplLemmas (EnclaveParams: EnclaveParams_sig)
                   (SecurityParams: SecurityParams_sig EnclaveParams)
                   (Core0Defs : Core0_Defs EnclaveParams SecurityParams)
                   (Core1Defs : Core1_Defs EnclaveParams SecurityParams)
                   (MemDefs : MemoryProofDefs EnclaveParams SecurityParams)
                   (SmDefs :  SmProofDefs EnclaveParams SecurityParams)
                   (ImplDefs: PfImplDefs EnclaveParams SecurityParams)
                   (SMT_ok_core0: SMT_Core0_sig EnclaveParams SecurityParams Core0Defs)
                   (SMT_ok_core1: SMT_Core1_sig EnclaveParams SecurityParams Core1Defs)
                   (SMT_ok_sm: SMT_SM_sig EnclaveParams SecurityParams SmDefs)
                   (SMT_ok_mem: SMT_Mem_sig EnclaveParams SecurityParams MemDefs)
                   (SmtOk: SMT_Chain_sig EnclaveParams )
                   (PfChain: PfChain.PfChain EnclaveParams SecurityParams SmtOk)
                   (PfChainHelpers: PfChainHelpers_sig EnclaveParams SecurityParams ImplDefs)
                   : PfImplLemmas_sig EnclaveParams SecurityParams ImplDefs.

Module Core0Proofs := Core0Proofs EnclaveParams SecurityParams Core0Defs SMT_ok_core0.
Module Core1Proofs := Core1Proofs EnclaveParams SecurityParams Core1Defs SMT_ok_core1.
Module MemProof := MemProofs EnclaveParams SecurityParams MemDefs SMT_ok_mem.
Module SmProof := SmProofs EnclaveParams SecurityParams SmDefs SMT_ok_sm.
Import PfChainHelpers.
Module Import ImplHelpers := PfImplHelpers.ImplHelpers EnclaveParams SecurityParams ImplDefs.
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.

  Import SecurityParams.
  Import ExternalMemory.
  Import ImplDefs.
  Import PfChain.
  Import Utils.PfHelpers.
  Import TopLevelModuleHelpers.
  Module PfLemmas := PfLemmas EnclaveParams SecurityParams.
  Import PfLemmas.
  Lemma impl_interp_cycle_correct':
    forall impl_st input ,
      ImplInvariant impl_st ->
      match
        interp_scheduler (mk_sigma_fn impl_st.(machine_mem_st) input)
                         id_int_fns id_struct_defs
              impl_st.(machine_koika_st)
             id_rules
             Impl.schedule with
      | Success log => strong_WF_state reg_type_env (commit_update impl_st.(machine_koika_st) log.(Log__koika)) /\
                        WF_ext_log _ext_fn_tys log.(Log__ext)
      | _ => False
      end.
  Proof.
    intros * Hinv. eapply impl_interp_cycle_correct; eauto with solve_invariants.
  Qed.
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
Import PfHelpers.
Import CoreSymbDefs.
Import SymbSimDefs.

Import SymbPfChain.
Import SMSymbDefs.

Ltac change_get_field_in H :=
  match type of H with
  | context C[unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid ?req) (_fld ?req ?fld)) ?v] =>
      let T := constr:(unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid ?req) (_fld ?req ?fld)) ?v) in
      let T' := constr:(_unsafe_get_field req fld v) in
      change T with T' in H
  end.
Ltac change_get_field :=
  match goal with
  | |- context C[unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid ?req)) (_fld ?req ?fld) ?v] =>
      let T := constr:(unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid req)) (_fld req fld) v) in
      let T' := constr:(_unsafe_get_field req fld v) in
      let G := context C[T'] in
      change G
  end.
Ltac init_interp ::=
  repeat
   match goal with
   | |- dummy_interp _ _ _ _ _ _ => unfold dummy_interp, dummy_pkg
   | |- Forall (fun '(_, p) => interp_fancy_spred _ _) _ => rewrite <- forall_preprocess_fancy_spreds_correct
   | |- Forall (fun '(_, p) => interp_fancy_spred2 _ _ _) _ => rewrite <- forall_preprocess_fancy_spreds_correct2
   end.



Ltac basic_cbn :=
  cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat filter_input].
Import SecurityMonitor.
Import RVCore.
Import Memory.
Instance EqDec_mem_custom_t : EqDec mem_custom_t := _.
Instance EqDec_custom_chaining_asserts : EqDec custom_chaining_asserts := _.
Instance EqDec_sm_custom_t : EqDec sm_custom_t := _.

  Lemma impl_enter_implied:
  forall st mid_st st' mid_log final_log sigma input,
    WF_state (SortedRegEnv.to_list reg_type_env) (machine_koika_st st) ->
    WF_state (SortedRegEnv.to_list reg_type_env) (machine_koika_st st') ->
    WF_ext_log _ext_fn_tys mid_log ->
    ImplInvariant st ->
    ImplInvariant st' ->
    sigma = mk_sigma_fn (machine_mem_st st') input ->
    dummy_interp (machine_koika_st st) mid_st (machine_koika_st st') sigma (Some mid_log) final_log
                   (post_sm_exprs EnclaveParams.enclave_sig impl_init impl_final impl_mid_ext impl_committed_ext
                      impl_get_field) ->
    update_memory (unsafe_get_ext_call_from_log mid_log (_ext ext_mainmem))
                  (machine_mem_st st) = Success (machine_mem_st st') ->
    impl_enter st st'.
  Proof.
    unfold impl_enter. unfold can_enter_enclave.
    unfold configs_conflict, get_impl_config, machine_st_to_ghost_core, get_ghost_running_config,
      is_sm_turn, is_sm_core0_turn, is_sm_core1_turn.
    intros * hwf hwf' hwf_mid_log hinv hinv' hsigma hpost hmem.
    intros * hwaiting henter hturn.
    simplify.
    bash_destruct hwaiting. inversions hwaiting. simplify.
    simplify.
    prop_pose_with_custom hreset0 (Custom_Reset0) hpost.
    prop_pose_with_custom hreset1 (Custom_Reset1) hpost.
    prop_pose_with_custom henter0 (PfChain.CustomSM SM_Enter0) hpost.
    prop_pose_with_custom henter1 (PfChain.CustomSM SM_Enter1) hpost.

    cbn - [_id core_regs_to_reset core_to_sm_fifos memory_to_sm_fifos sm_to_memory_fifos to_mmio_regs from_mmio_regs sm_reset_regs] in hreset0.
    cbn - [_id core_regs_to_reset core_to_sm_fifos memory_to_sm_fifos sm_to_memory_fifos to_mmio_regs from_mmio_regs sm_reset_regs] in hreset1.
    pose proof hinv' as hinv''.
    destruct hinv'.
    assert (interp_fancy_spred
             (dummy_pkg (machine_koika_st st) mid_st (machine_koika_st st')
                (mk_sigma_fn (machine_mem_st st') input)
                (Some mid_log) final_log)
             (fs_sm_enter_enclave__conclusion EnclaveParams.enclave_sig core impl_init impl_final
                                         impl_get_field)) as henter_post.
    {
      destruct core.
      - apply henter0;
          cbn - [_smid _sid of_nat _fld reg_to_debug_id]; simplify; auto.
        destruct_matches_in_hyp henter; simplify; auto. right.
        repeat rewrite orb_false_iff in henter. propositional. split_ors_in H.
        + apply enclave_id_beq_false_iff in henter4. apply henter4.
          apply unsafe_enclave_eid_eq.
          3: { setoid_rewrite H. reflexivity. }
          all: unsafe_auto_simplify_structs.
        + revert H. repeat change_get_field. intros H.
          rewrite shared_region_conflict_false in H; auto; unsafe_auto_simplify_structs.
        + revert H. repeat change_get_field. intros H.
          setoid_rewrite uart_disjoint in H; auto; try unsafe_auto_simplify_structs; discriminate.
        + revert H. repeat change_get_field. intros H.
          setoid_rewrite led_disjoint in H; auto; try unsafe_auto_simplify_structs; discriminate.
        + revert H. repeat change_get_field. intros H.
          setoid_rewrite finish_disjoint in H; auto; try unsafe_auto_simplify_structs; discriminate.
      - apply henter1;
          cbn - [_smid _sid of_nat _fld reg_to_debug_id]; simplify; auto.
        destruct_matches_in_hyp henter; simplify; auto. right.
        repeat rewrite orb_false_iff in henter. propositional. split_ors_in H.
        + apply enclave_id_beq_false_iff in henter4. apply henter4.
          apply unsafe_enclave_eid_eq.
          3: { setoid_rewrite H. reflexivity. }
          all: unsafe_auto_simplify_structs.
        + revert H. repeat change_get_field. intros H.
          rewrite shared_region_conflict_false in H; auto; unsafe_auto_simplify_structs.
        + revert H. repeat change_get_field. intros H.
          setoid_rewrite uart_disjoint in H; auto; try unsafe_auto_simplify_structs; discriminate.
        + revert H. repeat change_get_field. intros H.
          setoid_rewrite led_disjoint in H; auto; try unsafe_auto_simplify_structs; discriminate.
        + revert H. repeat change_get_field. intros H.
          setoid_rewrite finish_disjoint in H; auto; try unsafe_auto_simplify_structs; discriminate.
    }
    cbn - [ map _sid of_nat _fld reg_to_debug_id In _id core_to_sm_fifos memory_to_sm_fifos
            sm_to_core_fifos sm_to_memory_fifos] in henter_post.
    destruct henter_post as (henter_running & henter_config & (henter_pc0 & henter_pc1 & henter_pc2 & henter_pc3) & henter_reset & hfifos_unchanged).

    assert ((machine_koika_st st').[_id (_crid core RVCore.Core.init_pc)] =
              _enclave_bootloader_addr EnclaveParams.enclave_sig
    (config_eid
       (unsafe_enclave_data_to_config
          (machine_koika_st st).[_rid (SecurityMonitor.SM (SecurityMonitor.enc_req core))]))) as hinit_pc.
    { set (config_eid _ ) as eid.
      assert (eid = eid) by auto.
      unfold eid at 2 in H.
      rewrite<-enclave_eid with (eid := eid) in H. 2: { destruct core; unsafe_auto_simplify_structs. }
      clearbody eid.
      clear - henter_pc0 henter_pc2 henter_pc1 henter_pc3 H.
      destruct eid; propositional.
    }
    constructor.
    - setoid_rewrite<-henter_config. unfold machine_st_to_ghost_core. setoid_rewrite henter_running. reflexivity.
    - intros. apply SimPre__init_spec; auto.
      + setoid_rewrite henter_config. auto.
      + destruct core; [apply hreset0 | apply hreset1]; auto.
      + destruct core;
          [ prop_apply_with_custom CoreIdSame ImplInv_Core0Invariant0 |
            prop_apply_with_custom CoreIdSame ImplInv_Core1Invariant0 ].
      + setoid_rewrite henter_config.
        destruct core;
          [ prop_apply_with_custom ((SM_enc_req CoreId0)) (ImplInv_SMInvariant  _ hinv input)
          | prop_apply_with_custom ((SM_enc_req CoreId1)) (ImplInv_SMInvariant  _ hinv input)
          ]; basic_cbn; setoid_rewrite Heqb; auto.
      + prop_pose_with_custom hlog_eq (PfChain.CustomExtFn (_id (_extid ext_mainmem))) hpost.
        assert (
            (machine_koika_st st').[_id (_mid Memory.Memory.turn)] = (mem_core_read_turn  core) ->
            (machine_mem_st st').(ext_resp) = None) as hresp_none.
        { consider update_memory.
          intros turn. eapply update_memory_none; eauto.
          destruct core.
          - prop_pose_with_custom hfoo' (Custom_MemPushZero0) hpost.
            cbn - [_id _sid _fld mk_sigma_fn] in hfoo'.
            rewrite<-hlog_eq in hfoo'. apply hfoo'; auto.
          - prop_pose_with_custom hfoo' (Custom_MemPushZero1) hpost.
            cbn - [_id _sid _fld mk_sigma_fn] in hfoo'.
            rewrite<-hlog_eq in hfoo'. apply hfoo'; auto.
        }
        apply hresp_none.
     + intros.
       prop_pose_with_custom hlog_eq (PfChain.CustomExtFn (_id (_extid ext_mainmem))) hpost.
       prop_pose_with_custom hfoo' (Custom_MemPushZeroBoth) hpost.
       eapply update_memory_none; eauto.
       cbn - [_id mk_sigma_fn] in hfoo'. rewrite<-hlog_eq in hfoo'.
       setoid_rewrite hfoo'; auto.
    - prop_pose_with_custom hrf0 (PfChain.Custom_Rf0) hpost.
      prop_pose_with_custom hrf1 (PfChain.Custom_Rf1) hpost.
      cbn - [_id FiniteType.finite_elements] in hrf0.
      cbn - [_id FiniteType.finite_elements] in hrf1.
      assert ((machine_koika_st st).[_id (_crid core RVCore.RV32Core.purge)] = Ob~1~1) as hcore_purge.
      { destruct hinv.
        destruct core.
        -  prop_pose_with_custom hwaiting0 ((SM_inv_waiting CoreId0)) (ImplInv_SMInvariant1 dummy_input_t).
           cbn - [_id core_to_sm_fifos memory_to_sm_fifos sm_to_core_fifos sm_to_memory_fifos ]in hwaiting0.
           clear - hwaiting0 Heqb.
           propositional.
        -  prop_pose_with_custom hwaiting1 ((SM_inv_waiting CoreId1)) (ImplInv_SMInvariant1 dummy_input_t).
           cbn - [_id core_to_sm_fifos memory_to_sm_fifos sm_to_core_fifos sm_to_memory_fifos ]in hwaiting1.
           clear - hwaiting1 Heqb.
           propositional.
      }

      eapply extract_rf_eq; intros; symmetry; destruct core; eauto.
      { symmetry. eapply hrf0; auto.  clear - H.
        apply in_map. apply in_map. auto.
      }
      { symmetry. eapply hrf1; auto.
        apply in_map. apply in_map. auto.
      }
Qed.

  Lemma impl_still_waiting_implied':
    forall st mid_st st' mid_log final_log input sigma,
    WF_state (SortedRegEnv.to_list reg_type_env) (machine_koika_st st) ->
    WF_state (SortedRegEnv.to_list reg_type_env) (machine_koika_st st') ->
    sigma = mk_sigma_fn (machine_mem_st st') input ->
    dummy_interp (machine_koika_st st) mid_st (machine_koika_st st') sigma mid_log final_log
                   (post_sm_exprs EnclaveParams.enclave_sig impl_init impl_final impl_mid_ext impl_committed_ext
                      impl_get_field) ->
    impl_still_waiting st st'.
  Proof.
    intros * hwf hwf' hsigma hpost.
    unfold impl_still_waiting, machine_st_to_ghost_core.
    intros. bash_destruct H; simplify. inversions H.
    consider get_impl_config. consider machine_st_to_ghost_core. consider get_ghost_running_config.
    consider can_enter_enclave. consider is_sm_turn; unfold is_sm_core0_turn, is_sm_core1_turn in *.
    assert (forall x, In x ([(SecurityMonitor.SM (SecurityMonitor.state core));
                        (SecurityMonitor.SM (SecurityMonitor.enc_req core));
                        (SecurityMonitor.SM (SecurityMonitor.enc_data core))] ++
                       (map (SecurityMonitor.core_reg core) (map RVCore.RV32Core.rf FiniteType.finite_elements))) ->
            (machine_koika_st st').[_id (reg_to_debug_id x)] = (machine_koika_st st).[_id (reg_to_debug_id x)]) as Hst_eq.
    { intros * Hin. rewrite in_app_iff in Hin.
      destruct core.
      + prop_pose_with_custom hwaiting0 (CustomSM SM_Waiting0) hpost.
        cbn - [_id FiniteType.finite_elements _sid _fld fs_enc_reqs_conflict In] in hwaiting0.
        assert_conclusion_of hwaiting0 hnew.
        { apply hwaiting0; auto.
          split_ors_in H0; simplify; auto.
          cbn - [_smid _sid of_nat _fld reg_to_debug_id].
          destruct_matches_in_hyp H0; simplify.
          + simpl in H0. discriminate.
          + right. split; [auto | ].
            consider configs_conflict. repeat rewrite orb_true_iff in H0.
            split_ors_in H0.
            * left. consider enclave_id_beq.
              bash_destruct H0; auto;
              repeat match goal with
              | H: config_eid _ = _ |- _ =>
                  symmetry in H; eapply enclave_eid in H; [ setoid_rewrite H | unsafe_auto_simplify_structs ]
              end; auto.
            * right. left.
              apply shared_region_conflict; auto; unsafe_auto_simplify_structs.
            * right. right. left.
              consider unsafe_enclave_data_to_config. cbn - [_id] in H0. rewrite andb_true_iff in H0.
              propositional; simplify. setoid_rewrite H1. setoid_rewrite H2. auto.
            * do 3 right.
              consider unsafe_enclave_data_to_config. cbn - [_id] in H0. rewrite andb_true_iff in H0.
              propositional; simplify. setoid_rewrite H1. setoid_rewrite H2. auto.
            * do 4 right.
              consider unsafe_enclave_data_to_config. cbn - [_id _sid of_nat _fld reg_to_debug_id] in H0.
              rewrite andb_true_iff in H0.
              propositional; simplify. setoid_rewrite H1. setoid_rewrite H2. auto.
        }
        { destruct hnew as (hsm & hrf).
          destruct Hin.
          - apply hsm; auto. apply in_map with (f := reg_to_debug_id) in H. auto.
          - apply hrf; auto.
            apply in_map with (f := reg_to_debug_id) in H.
            auto.
        }
      + prop_pose_with_custom hwaiting1 (CustomSM SM_Waiting1) hpost.
        cbn - [_id FiniteType.finite_elements _sid _fld fs_enc_reqs_conflict In] in hwaiting1.
        assert_conclusion_of hwaiting1 hnew.
        { apply hwaiting1; auto.
          split_ors_in H0; simplify; auto.
          cbn - [_smid _sid of_nat _fld reg_to_debug_id].
          destruct_matches_in_hyp H0; simplify.
          + simpl in H0. discriminate.
          + right. split; [auto | ].
            consider configs_conflict. repeat rewrite orb_true_iff in H0.
            split_ors_in H0.
            * left. consider enclave_id_beq.
              bash_destruct H0; auto;
              repeat match goal with
              | H: config_eid _ = _ |- _ =>
                  symmetry in H; eapply enclave_eid in H; [ setoid_rewrite H | unsafe_auto_simplify_structs ]
              end; auto.
            * right. left.
              apply shared_region_conflict; auto; unsafe_auto_simplify_structs.
            * right. right. left.
              consider unsafe_enclave_data_to_config. cbn - [_id] in H0. rewrite andb_true_iff in H0.
              propositional; simplify. setoid_rewrite H1. setoid_rewrite H2. auto.
            * do 3 right.
              consider unsafe_enclave_data_to_config. cbn - [_id] in H0. rewrite andb_true_iff in H0.
              propositional; simplify. setoid_rewrite H1. setoid_rewrite H2. auto.
            * do 4 right.
              consider unsafe_enclave_data_to_config. cbn - [_id _sid of_nat _fld reg_to_debug_id] in H0.
              rewrite andb_true_iff in H0.
              propositional; simplify. setoid_rewrite H1. setoid_rewrite H2. auto.
        }
        { destruct hnew as (hsm & hrf).
          destruct Hin.
          - apply hsm; auto. apply in_map with (f := reg_to_debug_id) in H. auto.
          - apply hrf; auto.
            apply in_map with (f := reg_to_debug_id) in H.
            auto.
        }
    }
    unfold _rid.
    repeat rewrite Hst_eq. setoid_rewrite Heqb. auto. rewrite beq_dec_refl.
    f_equal; try solve_In_to_find.
    apply extract_rf_eq; intros; auto.
    { apply Hst_eq. right. right. right. rewrite app_nil_l. rewrite in_map_iff. exists reg; split; auto. }
    all: destruct core; solve_In_to_find.
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

Hint Resolve WF_mk_sigma_fn: modularity.
Ltac solve_package_equiv ::=
  constructor; unfold package_equiv_taint'; split_ands_in_goal;
   (solve [ left; trivial ]) || (right; vm_compute; reflexivity).

    Theorem impl_step_preserves_impl_inv':
     forall impl_st input ,
         ImplInvariant impl_st ->
         exists res mem_st' ,
         interp_scheduler (mk_sigma_fn (machine_mem_st impl_st) input)
                          id_int_fns
                          id_struct_defs
                          (machine_koika_st impl_st)
                          id_rules
                          Impl.schedule = Success res /\
           ImplPost impl_st
                    {| machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika res);
                      machine_mem_st := mem_st' |} (Log__ext res).
    Proof.
      intros * hinv.
      specialize impl_interp_cycle_correct' with (1 := hinv) (input := input); intros hsched.
      simplify. destruct hsched as (hwf_st & hwf_log).
      exists s.
      specialize mem_push_request__success with (1 := hwf_log) (2 := ImplInv_WF_ext_mem _ hinv).
      intros hwf_mem'; simplify. exists s0. split; auto.
      rename Heqr0 into himpl_step.
      apply impl_interp_modular_schedule in himpl_step.
      consider interp_modular_schedule. consider modular_schedule.
      step_modular_schedule himpl_step impl_step_core0 impl_st_core0 impl_log_core0.
      step_modular_schedule himpl_step impl_step_core1 impl_st_core1 impl_log_core1.
      step_modular_schedule himpl_step impl_step_mem impl_st_mem impl_log_mem.
      step_modular_schedule himpl_step impl_step_sm impl_st_sm impl_log_sm.
      simpl in himpl_step.

      set (ext_log_app (Log__ext impl_log_core0) _) as post_log_core0 in *.
      set (ext_log_app (Log__ext impl_log_core1) _) as post_log_core1 in *.
      set (ext_log_app (Log__ext impl_log_mem) _) as post_log_mem in *.
      set (ext_log_app (Log__ext impl_log_sm) _) as post_log_sm in *.

      specialize_spec Core0Proofs.sched_correct HPreCore0 HPostCore0
                      impl_step_core0 tt wf_impl_core0 wf_iext_core0.
      { apply ImplInv_Core0Invariant; auto. }

      assert (ImplInvariant {| machine_koika_st := impl_st_core0;
                               machine_mem_st := impl_st.(machine_mem_st) |}) as HInv__Core0.
      { eapply core0_step_preserve_invariant; eauto; eauto with solve_invariants. }

      specialize_spec Core1Proofs.sched_correct HPreCore1 HPostCore1
                      impl_step_core1 tt wf_impl_core1 wf_iext_core1.
      { apply ImplInv_Core1Invariant with (1 := HInv__Core0). }

      assert (ImplInvariant {| machine_koika_st := impl_st_core1;
                               machine_mem_st := impl_st.(machine_mem_st) |} /\
                dummy_interp (machine_koika_st impl_st) impl_st_core0 impl_st_core1
                             (mk_sigma_fn (machine_mem_st impl_st) input)
                           (Some post_log_core0) (Log__ext impl_log_core1)
                           (post_core1_exprs impl_init impl_final impl_committed_ext)) as (HInv__Core1 & HBigPost__Core1).
      { eapply core1_step_preserve_invariant with (8 := HPostCore1); eauto with modularity;
        eauto with solve_invariants.
        - destruct impl_st; auto.
        - eapply CorePost_implies_post_conds'.  unfold post_log_core0. rewrite ext_log_app_empty_r.
          eapply HPostCore0.
      }
      specialize_spec MemProof.impl_step_mem_sched_correct HPreMem HPostMem
                      impl_step_mem tt wf_impl_mem wf_iext_mem.
      { apply ImplInv_MemInvariant with (1 := HInv__Core1). }

      assert (exists mem, update_memory
                      (unsafe_get_ext_call_from_log post_log_mem (_ext ext_mainmem))
                    (machine_mem_st impl_st) = Success mem /\
                ImplInvariant {| machine_koika_st := impl_st_mem;
                                 machine_mem_st := mem |} /\
                  dummy_interp (machine_koika_st impl_st) impl_st_core1 impl_st_mem
                     (mk_sigma_fn mem input)
                    (Some post_log_core1) (Log__ext impl_log_mem)
                    (post_mem_exprs impl_init impl_final impl_committed_ext impl_get_field)) as (mem' & Hmem_update & HInv__Mem & HBigPost__Mem).
    { eapply mem_step_implies with (8 := HPostMem); eauto with modularity; eauto with solve_invariants.
      - destruct impl_st; auto.
      - unfold dummy_interp, dummy_pkg. init_interp.
        replace_final_st_with_mid.
        replace_final_ext_with_mid.
        replace_mid_ext (None: option ext_log_t); [solve_package_equiv | ].
        replace_final_ext_with_committed.
        unfold dummy_interp, dummy_pkg in HBigPost__Core1. init_interp_in HBigPost__Core1.
        change_Forall_lists1 HBigPost__Core1.
        revert HBigPost__Core1.
        apply forall_interp_spred_package_equiv.
        clear.
        constructor; unfold package_equiv_taint'; split_ands_in_goal;
          try ((solve [ left; repeat rewrite ext_log_app_empty_r; auto ]) || (right; vm_compute; reflexivity)).
    }
    specialize_spec SmProof.impl_step_sm_sched_correct HPreSM HPostSM
                    impl_step_sm tt wf_impl_sm wf_iext_sm.
    { eapply SMPre_ignores_mem.
      eapply ImplInv_SMInvariant with (1 := HInv__Mem).
    }
    assert (ImplInvariant {| machine_koika_st := impl_st_sm;
                             machine_mem_st := mem' |} /\
              dummy_interp (machine_koika_st impl_st) impl_st_mem impl_st_sm
                     (mk_sigma_fn mem' input)
                     (Some post_log_mem) (Log__ext impl_log_sm)
                     (post_sm_exprs EnclaveParams.enclave_sig impl_init impl_final impl_mid_ext impl_committed_ext impl_get_field)) as (HInv__SM & HBigPost__SM).
    { eapply sm_step_implies with (impl_mem__init := machine_mem_st impl_st) (8 := HPostSM); eauto with modularity; eauto with solve_invariants.
      - apply ImplInv_WF_ext_mem with (1 := HInv__Mem).
      - destruct impl_st; auto.
      - unfold dummy_interp, dummy_pkg. init_interp.
        replace_final_st_with_mid.
        replace_final_ext_with_mid.
        replace_mid_ext (None: option ext_log_t); [solve_package_equiv | ].
        replace_final_ext_with_committed.
        unfold dummy_interp, dummy_pkg in HBigPost__Mem. init_interp_in HBigPost__Mem.
        replace_mid_ext (None: option ext_log_t); [solve_package_equiv | ].
        change_Forall_lists1 HBigPost__Mem.
        init_interp_in HBigPost__Mem.
        revert HBigPost__Mem.
        apply forall_interp_spred_package_equiv.
        clear.
        constructor; unfold package_equiv_taint'; split_ands_in_goal;
          try ((solve [ left; repeat rewrite ext_log_app_empty_r; auto ]) || (right; vm_compute; reflexivity)).
    }
    replace (commit_update (machine_koika_st impl_st) (Log__koika s)) with impl_st_sm in *.
    2: { apply Success_inj in himpl_step. simplify. auto. }
    specialize ImplInv_WF_state with (1 := hinv); intros hwf_impl_st. apply strong_WF_state_weaken in hwf_impl_st.
    assert (s0 = mem'); subst.
    { unfold update_memory in Hmem_update. simplify.
      replace (unsafe_get_ext_call_from_log (Log__ext s) (_ext ext_mainmem)) with
              (unsafe_get_ext_call_from_log post_log_mem (_ext ext_mainmem)) in *.
      { rewrite Hmem_update in Heqr1. simplify. auto. }
      { prop_rewrite_with_custom (PfChain.CustomExtFn ((_ext ext_mainmem))) HBigPost__SM.
          rewrite<-H0. reflexivity.
        }
    }
      simplify; subst; rewrite<-H0 in *.
      constructor; cbn - [_id].
      - auto.
      - prop_pose_with_custom hfoo (PfChain.CustomMem Mem_Tick) HBigPost__SM.
        cbn - [_id] in hfoo.
        apply plus_success' with (2 := hfoo). unsafe_auto_simplify_structs.
      - prop_pose_with_custom hfoo (PfChain.CustomSM SM_Tick) HBigPost__SM.
        cbn - [_id] in hfoo.
        apply plus_success' with (2 := hfoo). unsafe_auto_simplify_structs.
      - eapply impl_still_waiting_implied'; eauto with solve_invariants; eauto with modularity.
      - eapply impl_enter_implied.
        7: eapply HBigPost__SM.
        all: eauto with modularity.
      - constructor.
        + constructor; eauto with modularity.
          * rewrite orb_false_iff. unfold get_ext_observations; simpl.
            intros (owns0 & owns1).
            apply not_owns_uart_implies in owns0; eauto with modularity.
            apply not_owns_uart_implies in owns1; eauto with modularity.
            split.
            { prop_apply_with_custom (PfChain.CustomSM SM_uart_write_zeroes)  HBigPost__SM; auto. }
            { prop_apply_with_custom (PfChain.CustomSM SM_uart_read_zeroes)  HBigPost__SM; auto. }
          * rewrite orb_false_iff. unfold get_ext_observations; simpl.
            intros (owns0 & owns1).
            apply not_owns_led_implies in owns0; eauto with modularity.
            apply not_owns_led_implies in owns1; eauto with modularity.
            prop_apply_with_custom (PfChain.CustomSM SM_led_zeroes)  HBigPost__SM; auto.
          * rewrite orb_false_iff. unfold get_ext_observations; simpl.
            intros (owns0 & owns1).


            apply not_owns_finish_implies in owns0; eauto with modularity.
            apply not_owns_finish_implies in owns1; eauto with modularity.
            prop_apply_with_custom (PfChain.CustomSM SM_finish_zeroes)  HBigPost__SM; auto.
        + destruct impl_st.

          eapply mem_push_in_config_implied; eauto.
          unfold post_log_mem. eauto with modularity.
      - auto.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
        Unshelve.
        exact ((fun _ _ => Failure tt): ext_sigma_t).
    Qed.

End PfImplLemmas.
