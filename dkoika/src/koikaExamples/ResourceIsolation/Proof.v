Require Import koika.Frontend.

Require Import koika.examples.ResourceIsolation.Util.
Require Import koika.examples.ResourceIsolation.Impl.
Require Import koika.examples.ResourceIsolation.Spec.
Require Import koika.examples.ResourceIsolation.Theorem.
Require Import koika.examples.ResourceIsolation.ProofImpl.
Require Import koika.examples.ResourceIsolation.ProofSpec.
Require Import koika.examples.ResourceIsolation.ProofSim.

Require Import koika.Magic.

Import Common.

Module Pf.
  Section pf.

    Lemma impl_boxes_reset_initial:
      forall tag,
      impl_boxes_reset tag Impl.initial_state.
    Proof.
      intros. consider impl_boxes_reset.
      intros. solve_reg_in_taint. unfold Impl.initial_state.
      unfold unsafe_get_reg, r_get_reg.
      inversions H1; auto.
      inversions H; simpl; auto.
      inversions H0; simpl; auto.
      inversions H; simpl; auto.
    Qed.
    (* Should know that any simulation relation that holds still holds, cause no writes *)

    Lemma InitialSim: Sim Impl.initial_state (Spec.initial_state SpecParams.init_turn SpecParams.init_hist_ready).
    Proof.
      constructor.
      - apply initial_invariant.
      - reflexivity.
      - intros. destruct tag.
        + simpl. constructor; auto.
          * intros; subst. reflexivity.
          * apply impl_boxes_reset_initial.
        + simpl. constructor; auto.
          * intros; subst. reflexivity.
          * apply impl_boxes_reset_initial.
    Qed.

    Lemma ext_ready_for_job__sim:
      forall (impl_st: state_t) (spec_st: @Spec.state_t SpecParams.local_st_t) ,
        Sim impl_st spec_st ->
        impl_st.[Impl.REG_ext_ready_for_job] =
        Spec.ready_for_job_to_maybe
          (SpecParams.update_ready_for_job (Spec.hist_ready_for_job spec_st) (Spec.turn spec_st)
               (Spec.get_busy
                  (Spec.local_update_after_observations SpecParams.local_observe_output_reg
                                                        SpecParams.output_get_valid
                                                        (Spec.state0 spec_st))
                  (Spec.local_update_after_observations SpecParams.local_observe_output_reg
                                                        SpecParams.output_get_valid
                                                        (Spec.state1 spec_st)))).
    Proof.
      intros * HSim.
      unfold Spec.ready_for_job_to_maybe, SpecParams.update_ready_for_job; simpl.
      unfold Spec.local_update_after_observations, SpecParams.local_observe_output_reg;simpl.
      destruct_with_eqn (Spec.state0 spec_st); simpl.
      - pose proof (Sim_local _ _ HSim Tag0) as Hsim0; simpl in Hsim0; rewrite Heql in *; simpl in Hsim0; simplify.
        erewrite (impl_ext_ready_for_job _); try ri_solve.
        erewrite pf_taint_sim with (reg := Impl.REG_job0); eauto; [ | eapply pf_reg_sim; eauto | reflexivity].
        destruct (SpecParams.output_get_valid s.[Impl.REG_ext_output_reg]) eqn:H_output; simpl.
        + rewrite<-pf_job_NONE in H_output; eauto; [ | eapply spec_invariant; eauto |  reflexivity ].
          setoid_rewrite H_output. reflexivity.
        + destruct_match.
          * apply bits_eq_iff in Heqb. rewrite pf_job_NONE in Heqb; eauto; [ | eapply spec_invariant; eauto | reflexivity]. congruence.
          * pose proof (Sim_local _ _ HSim Tag1) as Hsim1; simpl in Hsim1.
            destruct_with_eqn (Spec.state1 spec_st); simpl in *; simplify; simpl.
            { erewrite pf_taint_sim with (reg := Impl.REG_job1); eauto; [ | eapply pf_reg_sim; eauto | reflexivity].
              destruct (SpecParams.output_get_valid s0.[Impl.REG_ext_output_reg]) eqn:H_output1; simpl.
              { rewrite<-pf_job_NONE in H_output1; eauto; [ | eapply spec_invariant; eauto | reflexivity ]. setoid_rewrite H_output1.
                reflexivity.
              }
              { destruct_match; auto.
                apply bits_eq_iff in Heqb0. rewrite pf_job_NONE in Heqb0; eauto; [ | eapply spec_invariant; eauto | reflexivity]. congruence.
              }
            }
            { erewrite pf_waiting_job_stage_None; eauto. }
      - erewrite (impl_ext_ready_for_job _); try ri_solve.
        pose proof (Sim_local _ _ HSim Tag0) as Hsim0; simpl in Hsim0.
        rewrite Heql in *; simpl in *.
        erewrite pf_waiting_job_stage_None; eauto.
    Qed.

    Lemma ext_output_reg__sim:
      forall (impl_st: state_t) (spec_st: @Spec.state_t SpecParams.local_st_t) ,
        Sim impl_st spec_st ->
        impl_st.[Impl.REG_ext_output_reg] =
        SpecParams.local_observe_output (Spec.turn spec_st)
                                        (fun tag : Tag =>
                                           match tag with
                                           | Tag0 => Spec.do_local_observations SpecParams.local_observe_output_reg (Spec.state0 spec_st)
                                           | Tag1 => Spec.do_local_observations SpecParams.local_observe_output_reg (Spec.state1 spec_st)
                                           end).
    Proof.
      intros * HSim.
      unfold Spec.do_local_observations, SpecParams.local_observe_output_reg,
             SpecParams.local_observe_output.
      destruct_match.
      - destruct_match.
        + pose proof (Sim_local _ _ HSim Tag0) as Hsim0; simpl in Hsim0.
          rewrite Heql in *. simpl in *. simplify.
          eapply pf_ext_output_reg_sim; eauto; simpl.
          erewrite Sim_clk; eauto. rewrite_solve.
        + pose proof (Sim_local _ _ HSim Tag0) as Hsim0; simpl in Hsim0.
          rewrite Heql in *. simpl in *.
          eapply pf_waiting_output_reg_None; eauto; simpl.
          erewrite Sim_clk; eauto. rewrite_solve.
      - destruct_match.
        + pose proof (Sim_local _ _ HSim Tag1) as Hsim1; simpl in Hsim1. rewrite Heql in *; simpl in *.
          simplify.
          eapply pf_ext_output_reg_sim; eauto; simpl.
          erewrite Sim_clk; eauto. rewrite_solve.
        + pose proof (Sim_local _ _ HSim Tag1) as Hsim1; simpl in Hsim1.
          rewrite Heql in *. simpl in *.
          eapply pf_waiting_output_reg_None; eauto; simpl.
          erewrite Sim_clk; eauto. rewrite_solve.
    Qed.

    Lemma get_job_accepted__sim:
      forall impl_st (spec_st: @Spec.state_t SpecParams.local_st_t) input ,
        Sim impl_st spec_st ->
        Impl.get_job_accepted impl_st input =
        Spec.get_job_accepted input
             (SpecParams.update_ready_for_job (Spec.hist_ready_for_job spec_st) (Spec.turn spec_st)
                 (Spec.get_busy
                    (Spec.local_update_after_observations SpecParams.local_observe_output_reg
                                                          SpecParams.output_get_valid
                                                          (Spec.state0 spec_st))
                    (Spec.local_update_after_observations SpecParams.local_observe_output_reg
                                                          SpecParams.output_get_valid
                                                          (Spec.state1 spec_st)))).
    Proof.
      intros * HSim.
      unfold Impl.get_job_accepted, Spec.get_job_accepted, SpecParams.update_ready_for_job,
             Spec.local_update_after_observations.
      destruct_match; auto.
      (* ri_step. *)
      (* apply unsafe_get_reg_safe in Heqo. subst. *)
      erewrite impl_ext_ready_for_job in *.

      destruct_with_eqn (Spec.state0 spec_st).
      - pose proof (Sim_local _ _ HSim Tag0) as Hsim0; simpl in Hsim0. rewrite Heql0 in *. simpl in *.
        simplify; simpl.
        erewrite pf_taint_sim with (1 := pf_reg_sim _ _ _ Hsim0) (reg := Impl.REG_job0); eauto; [| reflexivity].
        destruct_with_eqn (SpecParams.output_get_valid (s.[Impl.REG_ext_output_reg])); simpl.
        + erewrite<-pf_job_NONE in Heqb; eauto; [ erewrite Heqb | eapply spec_invariant; eauto | reflexivity]; simpl. reflexivity.
        + destruct_match.
          * apply bits_eq_iff in Heqb0.  rewrite pf_job_NONE in Heqb0; eauto; [ | eapply spec_invariant; eauto | reflexivity]. congruence.
          * destruct_with_eqn (Spec.state1 spec_st); simpl.
            { pose proof (Sim_local _ _ HSim Tag1) as Hsim1; simpl in Hsim1; rewrite Heql1 in Hsim1; simpl in Hsim1; simplify.
              erewrite pf_taint_sim with (1 := pf_reg_sim _ _ _ Hsim1) (reg := Impl.REG_job1); eauto; [| reflexivity]. simpl.
              destruct_with_eqn (SpecParams.output_get_valid (s0.[Impl.REG_ext_output_reg])); simpl.
              { erewrite<-pf_job_NONE in Heqb1; eauto; [ erewrite Heqb1 | eapply spec_invariant; eauto | reflexivity ]. simpl.
                reflexivity.
              }
              { destruct_match.
                - apply bool_list_beq_iff in Heqb2.
                  rewrite pf_job_NONE in Heqb2; eauto; [ | eapply spec_invariant; eauto | reflexivity]. congruence.
                - reflexivity.
              }
            }
            { pose proof (Sim_local _ _ HSim Tag1) as Hsim1; simpl in Hsim1.
              rewrite Heql1 in *; simpl in *.
              erewrite pf_waiting_job_stage_None; eauto; simpl.
            }
      - simpl.
        pose proof (Sim_local _ _ HSim Tag0) as Hsim0; simpl in Hsim0. rewrite Heql0 in *; simpl in *.
        erewrite pf_waiting_job_stage_None; eauto; simpl.
      - eapply Sim_impl_invariant; eauto.
    Qed.

    Lemma step_sim__output:
      forall (impl_st impl_st': state_t) (spec_st spec_st': @Spec.state_t SpecParams.local_st_t)
        (sigma: input_t -> ext_sigma_t)
        (external_world_state_t: Type)
        (input_machine: @i_machine_t external_world_state_t output_t input_t)
        (ext_st ext_st'__impl ext_st'__spec: external_world_state_t)
        (output__impl output__spec: output_t),
      Impl.wf_sigma sigma ->
      Sim impl_st spec_st ->
      Spec.step (SpecParams.local_init_state sigma)
                (SpecParams.local_observe_output_reg)
                SpecParams.local_observe_output
                SpecParams.update_ready_for_job
                SpecParams.output_get_valid
                (SpecParams.local_step_fn sigma None)
                input_machine spec_st ext_st = (spec_st', ext_st'__spec, output__spec) ->
      Impl.step sigma input_machine impl_st ext_st = Success (impl_st', ext_st'__impl, output__impl) ->
      output__impl = output__spec.
    Proof.
      intros * Hwf_sigma HSim Hstep__spec Hstep__impl.
      unfold Impl.step, Spec.step, step, safe_step, Spec.spec_step in *.
      unfold Impl.koika_step, Impl.koika_step' in *.
      simplify.
      f_equal.
      - unfold Impl.get_observations. f_equal.
        + apply ext_ready_for_job__sim; assumption.
        + erewrite<-ext_output_reg__sim; eauto.
      - apply get_job_accepted__sim; assumption.
    Qed.

    Lemma step_Waiting_impl_job_stage_NONE:
       forall tag (impl_st : state_t) (spec_st : @Spec.state_t SpecParams.local_st_t) sigma input,
      Sim impl_st spec_st ->
      Spec.do_local_step (SpecParams.local_init_state sigma) (SpecParams.local_step_fn sigma None) tag
           (Spec.turn spec_st)
           (Spec.local_update_after_observations SpecParams.local_observe_output_reg
                                                 SpecParams.output_get_valid
                                                 (get_spec_st tag spec_st)) input
           (SpecParams.update_ready_for_job (Spec.hist_ready_for_job spec_st) (Spec.turn spec_st)
              (Spec.get_busy
                 (Spec.local_update_after_observations SpecParams.local_observe_output_reg
                                                       SpecParams.output_get_valid (Spec.state0 spec_st))
                 (Spec.local_update_after_observations SpecParams.local_observe_output_reg
                                                       SpecParams.output_get_valid (Spec.state1 spec_st)))) =
         Spec.Waiting ->
      unsafe_get_job_stage (impl_st.[job_reg tag]) = Impl.ENUM_stage__None /\
      ((impl_st.[Impl.REG_ext_ready_for_job] <> Spec.ready_for_job_to_maybe (Some tag)) \/
       input = None).
    Proof.
      intros * Hsim Hstep.
      consider @Spec.do_local_step.
      destruct_matches_in_hyp Hstep; [ discriminate | ].
      consider @Spec.local_update_after_observations.
      destruct_matches_in_hyp Heql.
      - bash_destruct Heql.
        pose proof (Sim_local _ _ Hsim tag) as Hsimtag. rewrite Heql0 in Hsimtag. simpl in Hsimtag.
        simplify.
        erewrite pf_taint_sim; eauto with solve_taint; [ | eapply pf_reg_sim; eauto].
        erewrite pf_job_NONE; eauto with solve_taint; [ | eapply spec_invariant; eauto].
        simpl in Heqb. split; auto.
        rewrite impl_ext_ready_for_job; try ri_solve.
        pose proof (Sim_local _ _ Hsim Tag0) as Hsim0; simpl in Hsim0.
        pose proof (Sim_local _ _ Hsim Tag1) as Hsim1; simpl in Hsim1.

        destruct_matches_in_hyp Hstep; simpl in Hstep.
        + simpl in Hsim0; simplify; simpl in *.
          erewrite pf_taint_sim with (tag := Tag0) (spec_st := s0); eauto with solve_taint; try ri_solve; [ | reflexivity].

          destruct_matches_in_hyp Hstep; simpl in Hstep.
          * simpl in Hsim0; simplify; simpl in *.
            erewrite<-pf_job_NONE with (reg_job := Impl.REG_job0) (tag := Tag0) in Heqb0; eauto; try ri_solve; [ | reflexivity]. rewrite Heqb0. simpl.
            destruct tag; simpl in *; bash_destruct Hstep; auto; left; discriminate.
          * simpl in Hsim0; simplify.
            destruct_matches_in_hyp Hstep.
            { simpl in *. simplify. simpl in Hstep.
              destruct_matches_in_hyp Hstep; simpl in Hstep.
              { bash_destruct Hstep; destruct tag; simpl in *; auto; try discriminate. left.
                rewrite Heql0 in Heql1. inversions Heql1.
                congruence.
              }
              { destruct tag; simpl in *; left.
                { rewrite Heql0 in *. inversions Heql1. congruence. }
                { rewrite Heql0 in *. inversions Heql2. congruence. }
              }
            }
            { simpl in Hstep. bash_destruct Hstep; destruct tag; simpl in *; try discriminate; auto.
              left. repeat destruct_match; try discriminate.
              apply bits_eq_iff in Heqb2.
              rewrite pf_job_NONE with (tag := Tag0) (reg_job := Impl.REG_job0) in Heqb2; try ri_solve; [ | reflexivity].
              congruence.
            }
        + simpl in Hsim0.
          erewrite pf_waiting_job_stage_None with (tag := Tag0); simpl; auto.
          destruct tag; simpl in *; try congruence. left; discriminate.
      - erewrite pf_waiting_job_stage_None; eauto.
        2 : { pose proof (Sim_local _ _ Hsim tag). rewrite Heql0 in *. assumption. }
        consider get_spec_st.
        destruct tag; simpl in Heql0; rewrite Heql0 in *; simpl in Hstep.
        + bash_destruct Hstep; auto.
        + split; auto.
          bash_destruct Hstep; simpl in *; unfold Spec.get_busy, SpecParams.update_ready_for_job in *; simpl in *; simplify; auto; left; rewrite impl_ext_ready_for_job; try ri_solve.
          all: pose proof (Sim_local _ _ Hsim Tag0) as Hsim0; simpl in Hsim0; rewrite Heql1 in Hsim0; simpl in Hsim0; simplify; simpl in *.
          all: pose proof (Sim_local _ _ Hsim Tag1) as Hsim1; simpl in Hsim1; rewrite Heql0 in Hsim1; simpl in Hsim1; simplify; simpl in *.
          *  erewrite pf_taint_sim with (tag := Tag0) (spec_st := s); eauto with solve_taint; try ri_solve; [ | reflexivity].
            rewrite<-pf_job_NONE with (reg_job := Impl.REG_job0) (tag := Tag0) in Heqb; eauto; try ri_solve; [ | reflexivity].
            rewrite Heqb. simpl. discriminate.
         * discriminate.
         * erewrite pf_waiting_job_stage_None with (tag := Tag0); auto.
           erewrite pf_waiting_job_stage_None with (tag := Tag1); auto.
           simpl. congruence.
    Qed.

    Lemma LocalStateSim_Waiting_NoInput :
      forall tag (impl_st : state_t) sigma log input,
        Impl.wf_sigma sigma ->
        ImplInvariant impl_st ->
        unsafe_get_job_stage (impl_st.[job_reg tag]) = Impl.ENUM_stage__None ->
        input = None \/ (impl_st.[Impl.REG_ext_ready_for_job] <> Spec.ready_for_job_to_maybe (Some tag)) ->
        interp_scheduler (sigma input) Impl.int_fn_env Impl.struct_env
                         impl_st Impl.rules Impl.schedule = Success log ->
        WF_log Impl.reg_types log.(Log__koika) ->
        impl_boxes_reset tag impl_st ->
        LocalStateSim tag (commit_update impl_st log.(Log__koika)) Spec.Waiting.
    Proof.
      intros * Hwf_sigma HInv Hjob_NONE Hinput Hsched Hwf_log Hreset.
      epose proof (Invariant_step_preserved _ _ _ _ Hwf_sigma HInv Hsched) as HInv'.
      specialize IP__waiting with (2 := Hjob_NONE) (st' := commit_update impl_st log.(Log__koika)) (sigma := sigma input).
      intros Hwaiting.
      assert_pre_and_specialize Hwaiting.
      { eapply impl_step_implies_post; eauto. }
      specialize Hwaiting with (reg := job_reg tag).
      assert_pre_and_specialize Hwaiting.
      { ri_solve. }
      assert_pre_and_specialize Hwaiting.
      { destruct Hinput; subst.
        - left. eapply Impl.wf_GetJob. auto.
        - right. destruct tag; auto.
      }
      destruct Hwaiting as [Hwaiting__job Hwaiting__output].

      constructor.
      - intros Hclk. auto.
      - intros; subst; auto.
      - unfold impl_boxes_reset; intros reg Hreg; simpl.
        destruct tag; simpl in *.
        + repeat rewrite orb_true_iff in Hreg.
          erewrite impl_pf__NONE_OR_INIT with (tag := Tag0); eauto; simpl.
          split_cases; auto; simplify; reflexivity.
        + repeat rewrite orb_true_iff in Hreg.
          erewrite impl_pf__NONE_OR_INIT with (tag := Tag1); eauto; simpl.
          split_cases; auto; simplify; reflexivity.
    Qed.


    Lemma WF_spec_create_initial:
      forall turn tag,
      WF_state Impl.reg_types
        (SortedRegEnv.map (SpecParams.create_initial_state_fn turn tag) Impl.reg_tys).
    Proof.
      intros. unfold WF_state.
      unfold get_reg. intros. destruct_match; auto.
      unfold Impl.reg_types in *.
      rewrite SortedRegEnv.opt_get_map in *. simpl_match.
      unfold SpecParams.create_initial_state_fn.
      destruct_match; simplify; subst; [ cbn in Heqo | ]; simplify.
      - destruct_match; auto.
      - destruct_match; simplify; subst; [ cbn in Heqo | ]; simplify.
        + destruct_match; auto.
        + destruct_match; simplify; subst; [cbn in Heqo | ]; simplify.
          * reflexivity.
          * rewrite zeroes_length. reflexivity.
    Qed.

    Lemma SpecInvariant__initial:
      forall turn tag,
        SpecInvariant tag (SortedRegEnv.map (SpecParams.create_initial_state_fn turn tag) Impl.reg_tys).
    Proof.
      intros.
      constructor.
      - apply WF_spec_create_initial.
      - destruct tag; unfold is_job_reg; intros; subst; auto.
      - intros; simpl. destruct tag; unfold is_job_reg in *; subst; auto; cbn; split; auto.
      - intros Hext_ready_for_job. cbn in Hext_ready_for_job.
        intros; simpl. destruct tag; unfold is_job_reg in *; subst; auto; cbn; split; auto.
    Qed.

    Lemma LocalRegSim__initial:
      forall tag impl_st (turn: bool),
      ImplInvariant impl_st ->
      unsafe_get_job_stage impl_st.[job_reg tag] = Impl.ENUM_stage__None ->
      impl_st.[Impl.REG_clk] = (if turn then Ob~1 else Ob~0) ->
      LocalRegSim tag impl_st
        (SortedRegEnv.map (SpecParams.create_initial_state_fn turn tag) Impl.reg_tys).
    Proof.
      intros * Hinv Hstage Hturn.
      constructor.
      - intros * Htaint; destruct tag; simpl in Htaint; repeat rewrite orb_true_iff in Htaint.
        + repeat destruct Htaint as [? | Htaint]; simplify; auto.
          * rewrite impl_pf_job_NONE_zeroed; eauto; reflexivity.
          * rewrite impl_pf__NONE_OR_INIT; eauto; reflexivity.
          * rewrite impl_pf__NONE_OR_INIT; eauto; reflexivity.
         + repeat destruct Htaint as [? | Htaint]; simplify; auto.
          * rewrite impl_pf_job_NONE_zeroed; eauto; reflexivity.
          * rewrite impl_pf__NONE_OR_INIT; eauto; reflexivity.
          * rewrite impl_pf__NONE_OR_INIT; eauto; reflexivity.
      - rewrite Hturn; destruct turn; auto.
      - intros Hvalid reg Htaint. destruct tag; simpl in Hvalid; rewrite Forall_single in Hvalid.
        + rewrite impl_pf__NONE_OR_INIT in Hvalid; eauto; [discriminate | reflexivity].
        + rewrite impl_pf__NONE_OR_INIT in Hvalid; eauto; [discriminate | reflexivity].
      - intros Hvalid reg Htaint. destruct tag; simpl in Hvalid; rewrite Forall_single in Hvalid.
        + rewrite impl_pf__NONE_OR_INIT in Hvalid; eauto; [discriminate | reflexivity].
        + rewrite impl_pf__NONE_OR_INIT in Hvalid; eauto; [discriminate | reflexivity].
    Qed.



    Lemma LocalStateSim_preserved:
      forall tag (impl_st : state_t) (spec_st: @Spec.state_t SpecParams.local_st_t) sigma input log,
        Impl.wf_sigma sigma ->
        Sim impl_st spec_st ->
        interp_scheduler (sigma input) Impl.int_fn_env Impl.struct_env
                         impl_st Impl.rules Impl.schedule = Success log ->
        WF_log Impl.reg_types log.(Log__koika) ->
        LocalStateSim tag (commit_update impl_st log.(Log__koika))
           (Spec.do_local_step (SpecParams.local_init_state sigma)
                               (SpecParams.local_step_fn sigma None) tag
               (Spec.turn spec_st)
               (Spec.local_update_after_observations SpecParams.local_observe_output_reg
                                                     SpecParams.output_get_valid
                                                     (get_spec_st tag spec_st))
               input
               (SpecParams.update_ready_for_job
                  (Spec.hist_ready_for_job spec_st) (Spec.turn spec_st)
                  (Spec.get_busy
                     (Spec.local_update_after_observations SpecParams.local_observe_output_reg
                                                           SpecParams.output_get_valid (Spec.state0 spec_st))
                     (Spec.local_update_after_observations SpecParams.local_observe_output_reg
                                                           SpecParams.output_get_valid (Spec.state1 spec_st))))).
    Proof.
      intros * Hwf_sigma HSim Hsched Hwf_log.

      remember (Spec.do_local_step _ _ _ _ _ _ _) as spec_st' eqn:Hspec_st'.
      pose proof (Sim_local _ _ HSim) as HLocal.

      destruct_with_eqn spec_st'.
      - unfold Spec.do_local_step in *. simpl.
        destruct_matches_in_hyp Hspec_st'.
        + inversions Hspec_st'.
          unfold SpecParams.local_step_fn, Impl.koika_step'.
          unfold Spec.local_update_after_observations in *.
          bash_destruct Heql0. inversions Heql0.
          specialize (HLocal tag). rewrite Heql in HLocal. simpl in HLocal. simplify.
          specialize @typecheck_schedule_correct with
            (1 := Impl.typecheck_schedule_Success) (st := s) (ext_sigma := sigma None); simpl.
          intros Htype.
          assert_pre_and_specialize Htype. { eapply pf_wf_spec; eauto. eapply spec_invariant; eauto. }
          assert_pre_and_specialize Htype. { ri_solve. }
          assert_pre_and_specialize Htype. { ri_solve. }
          simplify. simpl in Heqb.

          eapply Sim_step with (impl_st := impl_st) (impl_input := input); eauto; try ri_solve.
          * unfold Impl.koika_step', interp_cycle. simpl_match. reflexivity.
          * rewrite impl_ext_ready_for_job; try ri_solve.
            left.
            destruct tag.
            { destruct_match; auto.
              - apply bits_eq_iff in Heqb0.
                erewrite pf_taint_sim in Heqb0; [ | eapply pf_reg_sim; eauto | reflexivity ].
                erewrite pf_job_NONE with (tag := Tag0) in Heqb0; eauto with solve_taint; try ri_solve; [ | reflexivity].
                congruence.
              - split_ands_in_goal; auto.
                + repeat destruct_match; discriminate.
                + unfold not. intros Hext_ready_for_job.
                  eapply pf_job_stage_implied with (tag := Tag0) (reg_job := Impl.REG_job0) in Hext_ready_for_job; eauto with solve_taint; try ri_solve; [ | reflexivity].
                  apply bits_neq_iff in Heqb0.
                  erewrite pf_taint_sim with (tag := Tag0) in Heqb0; eauto; [ | reflexivity].
                  ri_solve.
            }
            { split_ands_in_goal; auto.
              - destruct_match; auto; [ discriminate | ].
                destruct_match; auto; [ | discriminate].
                apply bits_eq_iff in Heqb1.
                erewrite pf_taint_sim in Heqb1; [ | eapply pf_reg_sim; eauto | reflexivity ].
                erewrite pf_job_NONE with (tag := Tag1) in Heqb1; eauto with solve_taint; try ri_solve; [ | reflexivity].
                congruence.
              - unfold not in *; intros Hext_ready_for_job.
                eapply pf_job_stage_implied with (tag := Tag1) (reg_job := Impl.REG_job1) in Hext_ready_for_job; eauto with solve_taint; try ri_solve; [ | reflexivity].
                erewrite pf_job_NONE with (tag := Tag1) in Hext_ready_for_job; eauto; try ri_solve; [ | reflexivity].
                congruence.
            }
          * intros. destruct tag; simpl in *.
            { erewrite pf_job_NONE with (tag := Tag0) in H; eauto; try ri_solve; [ | reflexivity].
              congruence.
            }
            { erewrite pf_job_NONE with (tag := Tag1) in H; eauto; try ri_solve; [ | reflexivity].
              congruence.
            }
        + bash_destruct Hspec_st'. inversions Hspec_st'.
          unfold SpecParams.local_init_state; simpl.
          specialize @typecheck_schedule_correct with
              (1 := Impl.typecheck_schedule_Success)
              (st := (SortedRegEnv.map (SpecParams.create_initial_state_fn (Spec.turn spec_st) tag) Impl.reg_tys))
              (ext_sigma := sigma (Some l)); simpl; intros Htype.
          assert_pre_and_specialize Htype. { eapply WF_spec_create_initial. }
          assert_pre_and_specialize Htype. { ri_solve. }
          assert_pre_and_specialize Htype. { ri_solve. }
          simplify. unfold Impl.koika_step'.
          rewrite Heqr.
          specialize (HLocal tag).
          assert (unsafe_get_job_stage impl_st.[job_reg tag] = Impl.ENUM_stage__None) as Himpl_job.
          { unfold Spec.local_update_after_observations in *.
            destruct (get_spec_st tag spec_st) eqn:Hspec_st; simpl in HLocal; simplify.
            - bash_destruct Heql0. simpl in Heqb.
              rewrite<-pf_job_NONE with (1 := spec_invariant _ _ _ HLocal) (reg_job := job_reg tag) in Heqb0; eauto with solve_taint.
              rewrite pf_taint_sim with (spec_st := s0) (tag := tag); eauto with solve_taint; ri_solve.
            - eapply pf_waiting_job_stage_None; eauto.
          }
          eapply Sim_step with (impl_st := impl_st) (impl_input := Some l); eauto; try ri_solve.
          * eapply SpecInvariant__initial.
          * eapply LocalRegSim__initial with (turn := Spec.turn spec_st); eauto; try ri_solve.
            erewrite Sim_clk; eauto. destruct_match; auto.
          * unfold Impl.koika_step'. unfold interp_cycle. simpl_match. reflexivity.
          * apply Spec.internal_Tag_dec_bl in Heqb. subst.
            right. exists l; split_ands_in_goal; auto.
            { rewrite impl_ext_ready_for_job; try ri_solve. simpl.
              destruct t; simpl in Himpl_job; rewrite Himpl_job; simpl; auto.
              simpl in Heql0. rewrite Heql0 in Heqo. unfold SpecParams.update_ready_for_job in Heqo.
              simpl in Heqo.
              destruct_match; auto. apply bits_eq_iff in Heqb.
              destruct_with_eqn (Spec.state0 spec_st).
              { simpl in Heqo. bash_destruct Heqo; simpl in *; try discriminate.
                pose proof (Sim_local _ _ HSim Tag0) as Hsim0; simpl in Hsim0; rewrite Heql1 in *; simpl in Hsim0; simplify. simpl in Heqb0.
                erewrite pf_taint_sim with (tag := Tag0) (spec_st := s0) in Heqb; try ri_solve; [ | reflexivity].
                erewrite pf_job_NONE with (tag := Tag0) in Heqb; eauto; try ri_solve; [ | reflexivity].
                congruence.
              }
              { simpl in Heqo. discriminate. }
            }
            { destruct t; reflexivity. }
          * destruct tag; auto.

      - specialize step_Waiting_impl_job_stage_NONE with (1 := HSim) (2 := eq_sym Hspec_st').
        intros[Hjob__None ?]; propositional.
        eapply LocalStateSim_Waiting_NoInput with (sigma := sigma) (input := input); auto; try ri_solve.
        + destruct H; auto.
        + unfold impl_boxes_reset. intros.
          eapply impl_pf__NONE_OR_INIT; try ri_solve; eauto.
    Qed.

    Lemma step_sim:
      forall (impl_st: state_t) (spec_st spec_st': @Spec.state_t SpecParams.local_st_t)
        (sigma: input_t -> ext_sigma_t)
        (external_world_state_t: Type)
        (input_machine: @i_machine_t external_world_state_t output_t input_t)
        (ext_st ext_st'__spec: external_world_state_t)
        (output__spec: output_t),
      Impl.wf_sigma sigma ->
      Sim impl_st spec_st ->
      Spec.step (SpecParams.local_init_state sigma)
                (SpecParams.local_observe_output_reg)
                SpecParams.local_observe_output
                SpecParams.update_ready_for_job
                SpecParams.output_get_valid
                (SpecParams.local_step_fn sigma None)
                input_machine spec_st ext_st = (spec_st', ext_st'__spec, output__spec) ->
      match Impl.step sigma input_machine impl_st ext_st with
      | Success (impl_st', ext_st'__impl, output__impl) =>
        Sim impl_st' spec_st' /\ ext_st'__impl = ext_st'__spec /\ output__impl = output__spec
      | Failure _ => False
      end.
    Proof.
      intros * pf_wf_sigma HSim Hstep__spec.
      specialize Proofs.ImplInvariant_implies_step_Success with
          (1 := pf_wf_sigma) (2 := Sim_impl_invariant _ _ HSim)
          (ext_st := ext_st) (input_machine := input_machine) (impl_st := impl_st).
      intros; simplify_result. destruct_match_pairs; propositional.
      rename o into output__impl. rename e into ext_st'__impl. rename s0 into impl_st'.

      assert (output__impl = output__spec); subst.
      { eapply step_sim__output; eauto. }

      unfold Impl.step, step, Impl.koika_step, Impl.koika_step', interp_cycle in *. simplify.
      assert (WF_log Impl.reg_types s.(Log__koika)) as Hwf_log.
      { eapply typecheck_schedule_correct'_WF_log with (6 := Heqr0).
        - erewrite Impl.typecheck_schedule_Success. auto.
        - apply_sim.
        - eauto with WF_auto.
        - apply_wf_sigma.
        - unfold WF_int_fn_env.
          apply Impl.typecheck_int_fns_Success.
      }

      assert (ImplInvariant (commit_update impl_st s.(Log__koika))) as HInv'.
      { eapply Invariant_step_preserved; eauto. ri_solve. }

      assert (forall tag, LocalStateSim tag (commit_update impl_st s.(Log__koika)) (get_spec_st tag spec_st')) as HLocalSim'.
      { unfold Spec.step, safe_step, Spec.spec_step in *; simplify_tupless; simpl.
        intros; destruct tag; simpl; eapply LocalStateSim_preserved; eauto.
      }

      split_ands_in_goal; auto.
      { constructor; auto.
        - unfold Spec.step, safe_step, Spec.spec_step in *; simplify_tupless; simpl.
          erewrite IP__clk with (st := impl_st); eauto.
          2 : { eapply impl_step_implies_post; eauto; try ri_solve. }
          erewrite Sim_clk; eauto. reflexivity.
      }

      unfold Impl.step, Spec.step, step, safe_step in *.
      simplify. reflexivity.
    Qed.


    Lemma step_n'_sim (sigma: input_t -> ext_sigma_t)
          (pf_wf_sigma: Impl.wf_sigma sigma):
      forall (external_world_state_t: Type)
        (input_machine: @i_machine_t external_world_state_t output_t input_t)
        (n: nat)
        (ext_st ext_st'__spec: external_world_state_t)
        (impl_st: state_t) (spec_st spec_st': @Spec.state_t SpecParams.local_st_t)
        (output__spec: list output_t),
        Sim impl_st spec_st ->
        Spec.step_n'
          (SpecParams.local_init_state sigma)
          (SpecParams.local_observe_output_reg)
          SpecParams.local_observe_output
          SpecParams.update_ready_for_job
          SpecParams.output_get_valid
          (SpecParams.local_step_fn sigma None)
          input_machine n
          spec_st ext_st = (spec_st', ext_st'__spec, output__spec) ->
        match Impl.step_n' sigma input_machine n impl_st ext_st with
        | Success (impl_st', ext_st'__impl, output__impl) =>
          Sim impl_st' spec_st' /\ ext_st'__impl = ext_st'__spec /\ output__impl = output__spec
        | Failure _ => False
        end.
    Proof.
      induction n.
      - simpl; propositional; simplify_tupless; auto.
      - intros * HSim Hstep__spec.
        specialize IHn with (1 := HSim).
        unfold Impl.step_n' in *.
        unfold Spec.step_n' in *.
        rewrite rewrite_step_succ_n'.
        rewrite rewrite_safe_step_succ_n' in Hstep__spec.
        destruct_match_pairs. simplify_tupless.
        specialize IHn with (1 := Heqp); propositional.
        bash_destruct IHn; propositional.
        specialize step_sim with (1 := pf_wf_sigma) (2 := IHn0) (3 := Heqp1).
        intros Hstep_sim.
        consider Impl.step. bash_destruct Hstep_sim. propositional.
    Qed.


  End pf.


  Theorem simulation (sigma: input_t -> ext_sigma_t)
                     (pf_wf_sigma: Impl.wf_sigma sigma) :
    forall (external_world_state_t: Type)
      (input_machine: @i_machine_t external_world_state_t output_t input_t)
      (n: nat),
      Impl.step_n sigma input_machine n =
      Success (Spec.step_n SpecParams.init_turn SpecParams.init_hist_ready
                           (SpecParams.local_init_state sigma)
                           (SpecParams.local_observe_output_reg)
                           SpecParams.local_observe_output
                           SpecParams.update_ready_for_job
                           SpecParams.output_get_valid
                           (SpecParams.local_step_fn sigma None)
                           input_machine n).
  Proof.
    intros.
    unfold Impl.step_n, Spec.step_n.
    unfold step_n, safe_step_n. destruct_match_pairs; simplify_tupless.
    specialize step_n'_sim with (1 := pf_wf_sigma) (2 := InitialSim) (3 := Heqp).
    unfold Impl.step_n'.
    destruct_match; destruct_match_pairs; simplify_tupless; propositional.
  Qed.

End Pf.

Module Secure : Secure_t.

  Corollary secure :
    forall (sigma: input_t -> ext_sigma_t) (pf_WF_ext_sigma: Impl.wf_sigma sigma),
    exists (local_st_t: Type)
      (init_turn: Spec.turn_t)
      (init_hist_ready: option Tag)
      (local_init_state: input_t -> Tag -> Spec.turn_t -> local_st_t)
      (local_observe_output_reg: local_st_t -> Spec.obs_output_reg_t)
      (local_observe_output: Spec.turn_t -> (Tag -> option Spec.local_output_t) -> Spec.obs_output_reg_t)
      (update_ready_for_job: option Tag -> Spec.turn_t -> (Tag -> bool) -> option Tag)
      (output_get_valid: Spec.obs_output_reg_t -> bool)
      (local_step_fn: local_st_t -> local_st_t),
    forall (external_world_state_t: Type)
      (input_machine: @i_machine_t external_world_state_t output_t input_t)
      (n: nat),
      Impl.step_n sigma input_machine n =
        Success (Spec.step_n init_turn init_hist_ready local_init_state
                  local_observe_output_reg  local_observe_output
                  update_ready_for_job output_get_valid local_step_fn
                  input_machine n).
  Proof.
    intros. repeat eexists. eapply Pf.simulation; auto.
  Qed.
End Secure.
