Require Import rv_cache_isolation.Common.
Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.Utils.
Require Import koikaExamples.EnclaveWithCache.ExtractionUtils.
Require Import koikaExamples.EnclaveWithCache.ProofUtils.
Require Import koikaExamples.EnclaveWithCache.PfDefs.
Require Import koikaExamples.EnclaveWithCache.SymbSpec.
Require Import koikaExamples.EnclaveWithCache.PfSpecDefs.
Require Import koikaExamples.EnclaveWithCache.PfSpecLemmas_sig.
Require Import koikaExamples.EnclaveWithCache.PfHelpers.

Require Import FunctionalExtensionality.


Module PfSpecLemmas (EnclaveParams: EnclaveParams_sig)
                   (SecurityParams: SecurityParams_sig EnclaveParams)
                   (Spec: Spec_sig EnclaveParams)
                   (Symbspec: SymbSpec EnclaveParams SecurityParams )
                   (SpecDefs: PfSpecDefs EnclaveParams SecurityParams Spec)
                   (SmtOk: SMT_Spec_sig EnclaveParams SecurityParams Symbspec)
                   : PfSpecLemmas_sig EnclaveParams SecurityParams Spec SpecDefs.
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SecurityParams.
  Import ExternalMemory.
  Notation impl_state_t := machine_state_t.
  Import Spec.
  Import SpecDefs.
  Import Utils.PfHelpers.
  Import TopLevelModuleHelpers.

  Module Import PfLemmas := PfLemmas EnclaveParams SecurityParams.
  Module SymbSpecProofs := SymbSpecProofs EnclaveParams SecurityParams Symbspec SmtOk.

      Definition memory_post0 (step_function: machine_state_t -> machine_state_t * local_observations_t)
                              (state state': @core_state_t machine_state_t) memory : memory_map_t :=
      match state, state' with
      | CoreState_Enclave machine_state1 config1,
        CoreState_Enclave machine_state2 config2 =>
          memory
      | CoreState_Enclave machine_state1 config1,
        CoreState_Waiting config2 rf2 cycles2 =>
          let '(machine_state', _) := (step_function machine_state1) in
          update_regions EnclaveParams.enclave_sig config1 (SecurityParams.extract_dram machine_state') memory
      | CoreState_Waiting config1 rf1 cycles1,
        CoreState_Enclave machine_state2 config2 =>
          memory
      | CoreState_Waiting config1 rf1 cycles1,
        CoreState_Waiting config2 rf2 cycles2 =>
          memory
      end.
    Ltac simplify_spec :=
      repeat match goal with
      | H: CoreState_Waiting _ _ _ = CoreState_Waiting _ _ _
        |- _ =>
          inversions H
      | H: CoreState_Enclave _ _ = CoreState_Enclave _ _
        |- _ =>
          inversions H
      | H: Transition_Core _ _ = Transition_Core _ _
        |- _ =>
          inversions H
      | H: Transition_Exit _ _ _ = Transition_Exit _ _ _
        |- _ =>
          inversions H
      end.
    Lemma can_start0_even:
      forall cycles0 cycles1 config0 config1,
      SpecParams.can_start_fn CoreId0 cycles0 cycles1 config0 config1 = true ->
      Nat.even cycles1 = true. (* /\ cycles0 <> cycles1. *)
    Proof.
      unfold SpecParams.can_start_fn; simpl; intros. auto.
    Qed.
    Lemma can_start1_neven:
      forall cycles0 cycles1 config0 config1,
      SpecParams.can_start_fn CoreId1 cycles0 cycles1 config0 config1 = true ->
      Nat.even cycles1 = false (* /\ cycles0 <> cycles1 *).
    Proof.
      unfold SpecParams.can_start_fn; simpl; intros.
      rewrite <- PeanoNat.Nat.negb_even in H. rewrite negb_true_iff in H; auto.
    Qed.
  Theorem spec_step_case_core_state:
      forall spec_st input spec_st' output,
      SpecInvariant spec_st ->
      spec_step SecurityParams.local_step_fn0 SecurityParams.local_step_fn1
        SpecParams.can_start_fn SecurityParams.spin_up_machine
        SecurityParams.extract_dram SecurityParams.extract_rf spec_st input = (spec_st', output) ->
      exists output0 output1 memory',
      (case_core_state CoreId0 (spec_step_core CoreId0 (machine_state spec_st CoreId0) input)
         (machine_state spec_st CoreId0) (machine_state spec_st' CoreId0) output0
                       (cycles spec_st) (mem_regions spec_st) memory') (get_spec_configs spec_st CoreId1) /\
      (case_core_state CoreId1 (spec_step_core CoreId1 (machine_state spec_st CoreId1) input)
         (machine_state spec_st CoreId1) (machine_state spec_st' CoreId1) output1
                       (cycles spec_st) memory' (mem_regions spec_st'))
        (get_spec_configs spec_st CoreId0)  /\
      (output = merge_external_observations output0 output1).
  Proof.
      intros * HInv hstep. intros. unfold get_spec_configs.
      consider @spec_step. simplify. simpl.
      rename Heqp into step0.
      rename Heqp1 into step1.
      eexists (obs_ext l); eexists (obs_ext l0).
      eexists (memory_post0 (spec_step_core CoreId0 (machine_state spec_st CoreId0) input)
                            (machine_state spec_st CoreId0) c
                            (mem_regions spec_st)).
      unfold spec_step_core.
      unfold SecurityParams.machine_state_t in *.
      assert_left_as h0.
      { destruct (machine_state spec_st CoreId0) eqn:hMachine0;
        destruct c eqn:hMachine0'; hnf;
        unfold memory_post0;
        safe_unfold @do_enter_step step0;
          bash_destruct step0; simplify_spec;
          rename Heqt into exit0;
          revert exit0;
          unfold local_core_step; unfold do_exit_step; intros exit0;
          bash_destruct exit0;
          repeat (match goal with
          | H: SecurityParams.local_step_fn0 _ _ = _ |- context[SecurityParams.local_step_fn0] =>
              try setoid_rewrite H
          | H: _ && _ = true |- _ =>
              rewrite andb_true_iff in H
          | H: _ && _ = false |- _ =>
              rewrite andb_false_iff in H
          | H: SpecParams.can_start_fn CoreId0 ?cycles ?cycles ?config0 ?config1 = true |- _ =>
              apply can_start_cycles_eq in H
          | H1: ?x = _, H2: ?x = _ |- _ =>
              rewrite H1 in H2; clear H1
          | |- _ => progress (simplify_spec; propositional)
          end; simplify_spec; auto);
        try apply can_start0_even in Heqb1; propositional;
        split_ands_in_goal; auto.
      }
      split_ands_in_goal.
       - clear h0.
         destruct (machine_state spec_st CoreId1) eqn:hMachine1;
         destruct c0 eqn:hMachine1'; unfold case_core_state; unfold memory_post0;
             revert step1; unfold do_enter_step; intros enter1;
          bash_destruct enter1; simplify_spec;
           rename Heqt into exit1; revert exit1; unfold local_core_step, do_exit_step; intros exit1;
          bash_destruct exit1;
          repeat match goal with
          | H: SecurityParams.local_step_fn1 _ _ = _ |- context[SecurityParams.local_step_fn1] =>
              try rewrite H
          | H: _ && _ = true |- _ =>
              rewrite andb_true_iff in H
          | H: SpecParams.can_start_fn CoreId1 ?cycles ?cycles ?config0 ?config1 = true |- _ =>
              apply can_start_cycles_eq in H
          | |- _ => progress (simplify_spec; propositional)
          end; simplify_spec; auto.
         all: split_ands_in_goal; try reflexivity; try assumption.
         3 : { apply can_start1_neven in Heqb1; auto. }
         all: unfold do_exit_step in *; unfold do_enter_step in *;
           unfold local_core_step in *; unfold SpecParams.can_start_fn in *;
           bash_destruct  step0.
         (* 5 : { unfold spin_up_machine. f_equal. simpl in Heqb0. *)
         (*       unfold can_enter_enclave *)
          all: repeat (match goal with
          | H: local_step_fn0 _ _ = _ |- context[local_step_fn0] =>
              try setoid_rewrite H
          | H: _ && _ = true |- _ =>
              rewrite andb_true_iff in H
          | H: SpecParams.can_start_fn CoreId0 ?cycles ?cycles ?config0 ?config1 = true |- _ =>
              apply can_start_cycles_eq in H
          | H: negb _ = true |- _ => rewrite negb_true_iff in H
          | H: context[negb _ = false]|- _ => rewrite negb_false_iff in H
          | H : context[_ && _ = false] |- _ => rewrite andb_false_iff in H
          | H : context[Nat.eqb _ _  = true] |- _ => rewrite PeanoNat.Nat.eqb_eq in H
          | H : PeanoNat.Nat.odd ?n = true |- PeanoNat.Nat.even ?n = false =>
              rewrite<-PeanoNat.Nat.negb_odd; rewrite_solve
          | |- _ => progress (simplify_spec; simplify; try reflexivity; try assumption)
          end; simplify_spec ).
          * unfold spin_up_machine. f_equal.
            simpl in Heqb0.  unfold can_enter_enclave in *.
            apply get_enclave_dram_update_regions_eq. rewrite negb_true_iff in *. auto.
          * rewrite<-PeanoNat.Nat.negb_odd.  rewrite negb_true_iff. auto.
          * rewrite<-PeanoNat.Nat.negb_odd.  rewrite negb_true_iff. auto.
          * rewrite<-PeanoNat.Nat.negb_odd.  rewrite negb_true_iff. auto.
          * rewrite<-PeanoNat.Nat.negb_odd.  rewrite negb_true_iff. auto.
      - reflexivity.
    Qed.

  Hint Resolve @SpecInv_WF_state : solve_invariants.
  Lemma spec_interp_cycle_correct0:
      forall sigma koika_st,
        strong_WF_state reg_type_env koika_st ->
        WF_ext_sigma _ext_fn_tys sigma ->
        match interp_scheduler sigma id_int_fns id_struct_defs koika_st
                                     id_rules
               Core0Machine.schedule with
        | Success log => strong_WF_state reg_type_env (commit_update koika_st log.(Log__koika)) /\
                          WF_ext_log _ext_fn_tys log.(Log__ext)
        | _ => False
        end.
    Proof.
      intros * Hwf_state Hwf_ext.
      eapply typecheck_schedule_correct' with (ext_fn_types := _ext_fn_tys); try assumption.
      - apply Core0Machine.typecheck_schedule_Success.
      - auto with WF_auto.
      - auto with WF_auto.
      - unfold WF_int_fn_env. reflexivity.
  Qed.
  Lemma spec_interp_cycle_correct1:
      forall sigma koika_st,
        strong_WF_state reg_type_env koika_st ->
        WF_ext_sigma _ext_fn_tys sigma ->
        match interp_scheduler sigma id_int_fns id_struct_defs koika_st id_rules
               Core1Machine.schedule with
        | Success log => strong_WF_state reg_type_env (commit_update koika_st log.(Log__koika)) /\
                          WF_ext_log _ext_fn_tys log.(Log__ext)
        | _ => False
        end.
    Proof.
      intros * Hwf_state Hwf_ext.
      eapply typecheck_schedule_correct' with (ext_fn_types := _ext_fn_tys); try assumption.
      - apply Core1Machine.typecheck_schedule_Success.
      - auto with WF_auto.
      - auto with WF_auto.
      - unfold WF_int_fn_env. reflexivity.
  Qed.

  Lemma spec_interp_cycle_correct':
    forall schedule core impl_st config input,
      SpecCoreInvariant__Running core impl_st config ->
      match core with
      | CoreId0 => schedule = Core0Machine.schedule
      | CoreId1 => schedule = Core1Machine.schedule
      end ->
      match
        interp_scheduler (mk_sigma_fn impl_st.(machine_mem_st) input)
                         id_int_fns id_struct_defs
                         impl_st.(machine_koika_st) id_rules
                         schedule with
      | Success log => strong_WF_state reg_type_env (commit_update impl_st.(machine_koika_st) log.(Log__koika)) /\
                        WF_ext_log _ext_fn_tys log.(Log__ext)
      | _ => False
      end.
  Proof.
    intros * Hinv hsched.
    destruct core; subst.
    - eapply spec_interp_cycle_correct0; eauto with solve_invariants.
      eapply WF_mk_sigma_fn. eapply SpecInv_ExtMem; eauto.
    - eapply spec_interp_cycle_correct1; eauto with solve_invariants.
      eapply WF_mk_sigma_fn. eapply SpecInv_ExtMem; eauto.
  Qed.
Hint Resolve SpecInv_ExtMem : modularity.
Hint Resolve SpecInv_WF_state : solve_invariants.
Hint Resolve WF_mk_sigma_fn : solve_invariants.
(* Lemma unsafe_enclave_req_to_config_equiv: *)
(*   forall data, *)
(*   Datatypes.length data = struct_sz enclave_data -> *)
(*   Machine.unsafe_enclave_data_to_config data = *)
(*   Machine.unsafe_enclave_req_to_config  *)
(*     (unsafe_get_field (dstruct_fields enclave_data) FLD_enclave_data__data data). *)
(* Proof. *)
(*   intros * hlen. *)
(*   pose proof (eta_expand_list_correct false data) as hdata. rewrite hlen in hdata. *)
(*   cbn in hdata. rewrite hdata. cbn. *)
(*   unfold unsafe_enclave_data_to_config, unsafe_enclave_req_to_config, eid_vect_to_enclave_id, enclave_req_to_config, eid_vect_to_enclave_id. cbn. *)
(*   destruct_with_eqn (nth 0 data false); destruct_with_eqn (nth 1 data false); cbn; reflexivity. *)
(* Qed. *)
Definition get_mem_observations (log: ext_log_t) : mem_observations_t :=
  {| obs_mainmem := unsafe_get_ext_call_from_log log (_ext ext_mainmem);
     obs_cache := fun mem_ty core => unsafe_get_ext_call_from_log log (_ext (Memory.Memory.ext_cache mem_ty core));
     obs_meta := fun mem_ty core => unsafe_get_ext_call_from_log log (_ext (Memory.Memory.ext_metadata mem_ty core))
  |}.

Lemma post_implies_post_obs_exit:
  forall core machine_st koika_log ext_log sigma mem_st',
  WF_state (SortedRegEnv.to_list reg_type_env)
           (commit_update (machine_koika_st machine_st) koika_log) ->
  SymbSpecDefs.Post core (machine_koika_st machine_st)
                (commit_update (machine_koika_st machine_st) koika_log) sigma ext_log ->
  (* machine_st_to_ghost_core (machine_koika_st machine_st) core = GhostCoreState_Enclave config -> *)
  spec_post_obs_exit core machine_st
    {|
      machine_koika_st := commit_update (machine_koika_st machine_st) koika_log;
      machine_mem_st := mem_st'
    |}
    {| obs_mem := get_mem_observations ext_log;
      obs_exit_enclave :=
        fun core_id : ind_core_id =>
        observe_enclave_exit core_id (machine_koika_st machine_st)
          (commit_update (machine_koika_st machine_st) koika_log);
      obs_ext := get_ext_observations ext_log
    |}.
Proof.
  intros * hwf hpost. unfold spec_post_obs_exit.
  prop_pose_with_custom hstay Custom_stay_in_enclave hpost.
  prop_pose_with_custom hexit Custom_exit_enclave hpost.
  cbn - [_id] in hstay, hexit.
  destruct core.
  - cbn - [_id]. unfold observe_enclave_exit. unfold observe_enclave_exit_from_enc_data.
    destruct_match; propositional; simplify.
    + rewrite andb_true_iff in Heqb. propositional; simplify.
      propositional.
    + rewrite andb_false_iff in Heqb. apply hstay.
      split_ors_in Heqb; simplify; auto.
  - cbn - [_id]. unfold observe_enclave_exit. unfold observe_enclave_exit_from_enc_data.
    destruct_match; propositional; simplify.
    + rewrite andb_true_iff in Heqb. propositional; simplify.
      propositional.
    + rewrite andb_false_iff in Heqb. apply hstay.
      split_ors_in Heqb; simplify; auto.
Qed.
Hint Resolve strong_WF_state_weaken : modularity.
Lemma post_implies_pre:
  forall core st st' sigma sigma' ext_log,
  SymbSpecDefs.Post core st st' sigma ext_log ->
  st'.[_smrid (SecurityMonitor.state core)] <> (_enum enum_core_state "Waiting") ->
  SymbSpecDefs.Pre core st' sigma'.
Proof.
  intros * hpost hwaiting.
  consider SymbSpecDefs.Pre. consider SymbSpecDefs.Post.
  consider SymbSpecDefs.post_conds. consider SymbSpecDefs.pre_conds.
  repeat rewrite Forall_app in *.
  repeat rewrite<-forall_preprocess_fancy_spreds_correct in *.
  propositional. split_ands_in_goal.
  - rewrite Lift_Forall with (g := replace_spred_init_reg_with_final).
    2: { intros. apply replace_fancy_spred_init_reg_with_final_correct with (p := PBase p); auto. }
    destruct core; change_Forall_lists1 hpost0; revert hpost0;
      apply forall_interp_spred_package_equiv; solve_package_equiv.
  - destruct core; cbn - [_id]; auto.
Qed.


Lemma post_config_false_implies_ext_zeroed:
  forall core koika_st config koika_log ext_log sigma,
  SymbSpecDefs.Post core koika_st
                (commit_update koika_st koika_log) sigma ext_log ->
  machine_st_to_ghost_core koika_st core SecurityParams.extract_rf = GhostCoreState_Enclave config ->
  (config_ext_uart config = false ->
   unsafe_get_ext_call_from_log ext_log (_ext ext_uart_write) = Ob~0~0~0~0~0~0~0~0~0 /\
   unsafe_get_ext_call_from_log ext_log (_ext ext_uart_read) = Ob~0) /\
  (config_ext_led config = false ->
   unsafe_get_ext_call_from_log ext_log (_ext ext_led) = Ob~0~0) /\
  (config_ext_finish config = false ->
   unsafe_get_ext_call_from_log ext_log (_ext ext_finish) = Ob~0~0~0~0~0~0~0~0~0).
Proof.
  intros * hpost hconfig.
  consider machine_st_to_ghost_core. bash_destruct hconfig; simplify.
  prop_pose_with_custom huart_read Custom_uart_read_zero hpost.
  prop_pose_with_custom huart_write Custom_uart_write_zero hpost.
  prop_pose_with_custom hled Custom_led_zero hpost.
  prop_pose_with_custom hfinish Custom_finish_zero hpost.
  cbn - [_smid _sid of_nat _fld reg_to_debug_id] in huart_read, huart_write, hled, hfinish.
  inversions hconfig. unfold unsafe_enclave_data_to_config; simpl.
  split_ands_in_goal.
  - intros huart; split; simplify; auto.
  - intros hled'; simplify; auto.
  - intros finish'; simplify; auto.
Qed.

Lemma spec_step_core_invariant:
  forall core machine_st config machine_st' local_output input,
  SpecCoreInvariant__Running core machine_st config ->
  spec_step_core core (CoreState_Enclave machine_st config) input
                      machine_st = (machine_st', local_output) ->
  SpecCorePost core machine_st config machine_st' local_output.
Proof.
  intros * hrunning hstep.
  consider spec_step_core.
  assert (WF_ext_mem (machine_mem_st machine_st)) as hwf_mem by eauto with modularity.
  destruct core; unfold local_step_fn0, local_step_fn1, Core0Machine.step, Core1Machine.step in *;
    unfold Machine.unsafe_machine_step_local_obs,
           Machine.machine_step_local_obs, Machine.koika_step, Machine.koika_step', interp_cycle' in *;
    specialize spec_interp_cycle_correct' with (1 := hrunning) (2 := eq_refl)
                (input := (filter_input (get_core_config (CoreState_Enclave machine_st config)) input));
    intros hsched; simplify; consider update_memory;
    unfold get_observations in hstep; simpl in hstep;
    specialize mem_push_request__success with (log := (Log__ext s)) (mem := ext_main_mem (machine_mem_st machine_st)); intros hpush;
    specialize cache_pair_push_request__success with (log := (Log__ext s))
                                                   (metacache:= ext_l1_caches (machine_mem_st machine_st) imem CoreId0) (mem_type := imem) (core := CoreId0); intros hpair_imem0;
    specialize cache_pair_push_request__success with (log := (Log__ext s))
                                                   (metacache:= ext_l1_caches (machine_mem_st machine_st) imem CoreId1) (mem_type := imem) (core := CoreId1); intros hpair_imem1;
    specialize cache_pair_push_request__success with (log := (Log__ext s))
                                                   (metacache:= ext_l1_caches (machine_mem_st machine_st) dmem CoreId1) (mem_type := dmem) (core := CoreId1); intros hpair_dmem1;
    specialize cache_pair_push_request__success with (log := (Log__ext s))
                                                   (metacache:= ext_l1_caches (machine_mem_st machine_st) dmem CoreId0) (mem_type := dmem) (core := CoreId0); intros hpair_dmem0;
    propositional; simplify; consider unsafe_get_ext_call_from_log; consider _unsafe_get_ext_call_from_log;
      consider Memory.Memory.ext_metadata;
      consider Memory.Memory.ext_cache;
      assert_pre_and_specialize hpush; auto with solve_invariants;
      assert_pre_and_specialize hpair_imem0; auto with solve_invariants;
      assert_pre_and_specialize hpair_imem1; auto with solve_invariants;
      assert_pre_and_specialize hpair_dmem0; auto with solve_invariants;
      assert_pre_and_specialize hpair_dmem1; auto with solve_invariants; simplify;
    rename Heqr0 into hstep.
    (* setoid_rewrite Heqr1 in hstep; simplify; *)
    (* rename Heqr0 into hstep; rename Heqr1 into hmem'. *)
  - specialize_spec SymbSpecProofs.Pf0.spec0_step_sched_correct HPreSpec HPostSpec
                    hstep tt wf_spec' wf_iext_spec'.
    { eapply SpecInv_state; eauto. }
    constructor; cbn - [_id]; eauto with modularity.
    + eapply post_config_false_implies_ext_zeroed; eauto.
      eapply SpecInv_config; eauto.
    + eapply post_implies_post_obs_exit with (2 := HPostSpec). eauto with modularity.
    + constructor; auto; intros; simpl. destruct mem_ty; destruct core; auto.
    + intros. eapply post_implies_pre; eauto.
    + reflexivity.
  - specialize_spec SymbSpecProofs.Pf1.spec1_step_sched_correct HPreSpec HPostSpec
                    hstep tt wf_spec' wf_iext_spec'.
    { eapply SpecInv_state; eauto. }
    constructor; cbn - [_id]; eauto with modularity.
    + eapply post_config_false_implies_ext_zeroed; eauto.
      eapply SpecInv_config; eauto.
    + eapply post_implies_post_obs_exit; eauto with modularity.
    + constructor; auto; intros; simpl. destruct mem_ty; destruct core; auto.
    + intros. eapply post_implies_pre; eauto.
    + reflexivity.
Qed.
Lemma wf_dram_update:
  forall memory region config dram,
  WF_dram dram ->
  WF_dram (memory region) ->
  WF_dram (update_regions EnclaveParams.enclave_sig config dram memory region).
Proof.
  intros * hdram hregion.
  consider WF_dram.
  consider update_regions. intros.
  consider filter_dram.
  bash_destruct H; eauto.
Qed.
    Lemma case_core_state_preserves_wf_mem:
      forall spec_st core output memory' mem_regions' other_config input res,
      SpecInvariant spec_st ->
      wf_mem_regions memory' ->
      case_core_state core
                (spec_step_core core (machine_state spec_st core)
                   input) (machine_state spec_st core)
                res
                output (cycles spec_st) memory'
                mem_regions' other_config ->
        wf_mem_regions mem_regions'.
    Proof.
      intros *  hinv hwf hcase.
      consider case_core_state. bash_destruct hcase; propositional.
      pose proof (spec_machine_inv _ hinv) as hmachine. specialize hmachine with (core := core).
      rewrite Heqc in hmachine. simpl in hmachine.
      specialize spec_step_core_invariant with (1 := hmachine) (2 := Heqp); intros Hspec_post.
      constructor. inversions hwf. intros region. specialize (WF_mem_regions0 region).
      eapply wf_dram_update; auto.
      eapply WF_ext_mem__dram. eapply SpecPost__wf_ext_mem; eauto.
    Qed.
Ltac solve_wf_state_update:=
  try match goal with
  | |- context[Datatypes.length (of_nat _ _) ] => rewrite length_of_nat
  | |- context[Datatypes.length (opt_enclave_config_to_enclave_data _) ] =>
      rewrite opt_enclave_config_to_enclave_data_length
  | |- context [Datatypes.length (machine_pc (enclave_config_to_core_init_params EnclaveParams.enclave_sig _ ))] =>
    unfold enclave_config_to_core_init_params; unfold machine_pc;
    rewrite EnclaveParams.wf_sig.(wf_bootloader_addr _)
  end; vm_compute; reflexivity.
Ltac normalize_rid :=
  repeat match goal with
  | |- context[(_id (reg_to_debug_id ?x))] =>
    change (_id (reg_to_debug_id x)) with (_rid x)
  | |- context[(_id (_smid ?x))] =>
    change (_id (_smid x)) with (_rid (SecurityMonitor.SM x))
  | |- context[(_id (_smid ?x))] =>
    change (_id (_smid x)) with (_rid (SecurityMonitor.SM x))
  end.

Lemma wf_mem_regions_impl_wf_dram:
  forall memory new,
  wf_mem_regions memory ->
  WF_dram (get_enclave_dram EnclaveParams.enclave_sig memory new).
Proof.
  intros * hwf. unfold WF_dram.
  consider get_enclave_dram.
  destruct hwf. consider WF_dram.
  intros.
  bash_destruct H; eauto.
Qed.


Lemma spec_running_new_machine:
  forall core new memory cycles rf pc,
  wf_mem_regions memory ->
  Datatypes.length pc = 32 ->
  SpecCoreInvariant__Running core
        (spin_up_machine core cycles
                         {| machine_pc := pc;
                            machine_rf := rf;
                            machine_config := Some new
                         |}
                         (get_enclave_dram EnclaveParams.enclave_sig memory new)) new.
Proof.
  intros * hmem hpc; unfold spin_up_machine, Machine.initial_state, initial_machine_state.
  destruct core.
  - constructor; unfold machine_koika_st.
    + unfold strong_WF_state.  split.
      * reflexivity.
      * apply WF_initial_koika_state; auto.
        { rewrite length_of_nat; auto. }
    + setoid_rewrite initial_koika_state_lookup'. simpl.
      set (_reg_t _). vm_compute in n. subst n. discriminate.
    + unfold machine_st_to_ghost_core. destruct_match; simplify.
      * exfalso.
        setoid_rewrite initial_koika_state_lookup' in Heqb.
        simpl in Heqb. vm_compute in Heqb. discriminate.
      * setoid_rewrite initial_koika_state_lookup'. simpl.
        f_equal. apply enclave_data_to_config_involutive.
    + unfold machine_mem_st.
      unfold SymbSpecDefs.Pre. unfold SymbSpecDefs.pre_conds. intros.
      rewrite Forall_app. split.
      * unfold SymbSpecDefs.invariants.
        repeat apply Forall_cons;
          cbn - [_smid _sid of_nat _fld reg_to_debug_id]; normalize_rid;
          repeat rewrite initial_koika_state_lookup'; simpl.
        { intros. exfalso. clear - H0.
          vm_compute in H0. discriminate.
        }
        { intros; exfalso. simpl in H.
          rewrite enclave_config_to_valid_enclave_data_valid in H.
          discriminate.
        }
        { intros; split_ors_in H; vm_compute in H; exfalso; discriminate. }
        { split_ands_in_goal.
          + intros. vm_compute in H. discriminate.
          + intros. vm_compute in H. discriminate.
          + auto.
        }
        { intros; split_ors_in H; subst; normalize_rid;
          repeat rewrite initial_koika_state_lookup'; simpl; auto.
        }
        constructor.
      * unfold SymbSpecDefs.pre_conds'. repeat constructor.
          cbn - [_smid _sid of_nat _fld reg_to_debug_id]; normalize_rid;
          repeat rewrite initial_koika_state_lookup'; simpl.
        vm_compute. discriminate.
    + simpl. constructor.
      * constructor; simpl; propositional; try discriminate.
        apply wf_mem_regions_impl_wf_dram; auto.
      * intros. simpl.
        repeat constructor; simpl; propositional; simplify; auto; try discriminate.
  - constructor; unfold machine_koika_st.
    + unfold strong_WF_state.  split.
      * reflexivity.
      * apply WF_initial_koika_state; auto.
        { rewrite length_of_nat; auto. }
    + setoid_rewrite initial_koika_state_lookup'. simpl.
      set (_reg_t _). vm_compute in n. subst n. discriminate.
    + unfold machine_st_to_ghost_core. destruct_match; simplify.
      * exfalso.
        setoid_rewrite initial_koika_state_lookup' in Heqb.
        simpl in Heqb. vm_compute in Heqb. discriminate.
      * setoid_rewrite initial_koika_state_lookup'. simpl.
        f_equal. apply enclave_data_to_config_involutive.
    + unfold machine_mem_st.
      unfold SymbSpecDefs.Pre. unfold SymbSpecDefs.pre_conds. intros.
      rewrite Forall_app. split.
      * unfold SymbSpecDefs.invariants.
        repeat apply Forall_cons;
          cbn - [_smid _sid of_nat _fld reg_to_debug_id]; normalize_rid;
          repeat rewrite initial_koika_state_lookup'; simpl.
        { intros. exfalso. clear - H0.
          vm_compute in H0. discriminate.
        }
        { intros; exfalso. simpl in H.
          rewrite enclave_config_to_valid_enclave_data_valid in H.
          discriminate.
        }
        { intros; split_ors_in H; vm_compute in H; exfalso; discriminate. }
        { split_ands_in_goal.
          + intros. vm_compute in H. discriminate.
          + intros. vm_compute in H. discriminate.
          + auto.
        }
        { intros; split_ors_in H; subst; normalize_rid;
          repeat rewrite initial_koika_state_lookup'; simpl; auto.
        }
        constructor.
      * unfold SymbSpecDefs.pre_conds'. repeat constructor.
          cbn - [_smid _sid of_nat _fld reg_to_debug_id]; normalize_rid;
          repeat rewrite initial_koika_state_lookup'; simpl.
        vm_compute. discriminate.
    + simpl. constructor.
      * constructor; simpl; propositional; try discriminate.
        apply wf_mem_regions_impl_wf_dram; auto.
      * intros. simpl.
        repeat constructor; simpl; propositional; simplify; auto; try discriminate.
  Qed.

    Lemma case_core_state_preserves_invariant:
      forall spec_st core machine_state' config' output memory' mem_regions' other_config input,
      SpecInvariant spec_st ->
      wf_mem_regions memory' ->
      case_core_state core
                (spec_step_core core (machine_state spec_st core)
                   input) (machine_state spec_st core)
                (CoreState_Enclave machine_state' config')
                output (cycles spec_st) memory'
                mem_regions' other_config ->
      SpecCoreInvariant__Running core machine_state' config'.
    Proof.
      intros * hinv hmem hcase.
      consider case_core_state.
      destruct_matches_in_hyp hcase; simplify; propositional.
      - specialize spec_step_core_invariant with (2 := Heqp); intros hspec_post.
        specialize spec_machine_inv with (1 := hinv) (core := core). rewrite Heqc. simpl.  intros hrunning.
        propositional.
        constructor; inversions hspec_post; auto.
        + consider spec_post_obs_exit.
          simpl_match. propositional.
        + consider spec_post_obs_exit. simpl_match. propositional.
          unfold machine_st_to_ghost_core.
          setoid_rewrite SpecPost__obs_exit1.
          destruct_match; simplify; try congruence.
          * setoid_rewrite Heqb in SpecPost__obs_exit0.
            congruence.
          * (* setoid_rewrite<-SpecPost__obs_exit2. *)
            (* setoid_rewrite Heqb. *)
            specialize SpecInv_config with (1 := hrunning). unfold machine_st_to_ghost_core.
            intros hst0. bash_destruct hst0. simplify.
            auto.
        + consider spec_post_obs_exit. simpl_match. propositional.
      - eapply spec_running_new_machine; eauto.
        rewrite EnclaveParams.wf_sig.(wf_bootloader_addr _). reflexivity.
    Qed.


  Theorem spec_step_preserves_spec_inv:
        forall spec_st
        (external_world_state_t: Type)
        (input_machine: @i_machine_t external_world_state_t output_t input_t)
        ext_st spec_st' ext_st'__spec output__spec,
        SpecInvariant spec_st ->
        Spec.step
            SecurityParams.local_step_fn0
            SecurityParams.local_step_fn1
            SpecParams.can_start_fn
            SecurityParams.spin_up_machine
            SecurityParams.extract_dram
            SecurityParams.extract_rf
            input_machine spec_st ext_st = (spec_st', ext_st'__spec, output__spec) ->
        SpecInvariant spec_st'.
  Proof.
        unfold Spec.step, safe_step.
        intros * hinv hstep. simplify. rename Heqp into hstep.
        specialize spec_step_case_core_state with (1 := hinv) (2 := hstep).
        intros (output0 & output1 & memory' & case0 & case1 & merge). subst.
        constructor.
        - intros core. consider spec_machine_invariant.
          destruct_match.
          + specialize case_core_state_preserves_wf_mem with
              (1 := hinv) (2 := spec_wf_mem_regions _ hinv) (3 := case0); intros wf.
            destruct core; [ setoid_rewrite Heqc in case0; eapply case_core_state_preserves_invariant with (2 := spec_wf_mem_regions _ hinv) (3 := case0) | setoid_rewrite Heqc in case1; eapply case_core_state_preserves_invariant with (3 := case1) ]; eauto.
          + auto.
        - specialize spec_disjoint_configs with (1 := hinv); intros hdisjoint.
          consider disjoint_option_configs'.
          consider disjoint_option_configs. destruct_goal_matches; auto.
          consider case_core_state. consider @get_core_config.
          destruct_matches_in_hyp case0.
          + destruct_matches_in_hyp case0. propositional.
            * simpl in Heqo. simplify.
              destruct_matches_in_hyp case1.
              { destruct_matches_in_hyp case1; propositional.
                - simpl in Heqo0. simplify.  propositional.
                - simpl in Heqo0. discriminate.
              }
              { destruct_matches_in_hyp case1; propositional.
                - simpl in Heqo0. simplify.
                  consider get_spec_configs. setoid_rewrite Heqc in case1.
                  simpl in case1.
                  apply disjoint_configs_sym.
                  eapply can_enter_enclave_implies_disjoint; eauto.
                - simpl in Heqo0. discriminate.
              }
            * simpl in Heqo. discriminate.
          + bash_destruct Heqo. bash_destruct Heqo0. simplify. propositional.
            destruct_matches_in_hyp case1; propositional.
            * consider get_spec_configs.  simplify. propositional.
              setoid_rewrite Heqc2 in case0.
              simpl in case0.
              eapply can_enter_enclave_implies_disjoint; eauto.
            * congruence.
        - eapply case_core_state_preserves_wf_mem; eauto.
          eapply case_core_state_preserves_wf_mem; eauto.
          inversions hinv; auto.
  Qed.
End PfSpecLemmas.
