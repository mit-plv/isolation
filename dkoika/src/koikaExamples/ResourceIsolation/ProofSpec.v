Require Import koika.Frontend.

Require Import koika.examples.ResourceIsolation.Util.
Require Import koika.examples.ResourceIsolation.Impl.
Require Import koika.examples.ResourceIsolation.Spec.
Require Import koika.examples.ResourceIsolation.Theorem.
Require Import koika.examples.ResourceIsolation.ProofImpl.

Require Import koika.Magic.

(* - spec says once a job continues, it's no longer affected by external inputs *)

Import Common.

Module Type SpecParams_sig.
  Parameter local_st_t: Type.
  Parameter init_turn : Spec.turn_t.
  Parameter (init_hist_ready: option Tag).
  Parameter (local_init_state: (input_t -> ext_sigma_t) -> input_t -> Common.Tag -> Spec.turn_t -> local_st_t).
  Parameter (local_observe_output_reg: local_st_t -> Spec.obs_output_reg_t).
  Parameter (local_observe_output: Spec.turn_t -> (Tag -> option Spec.local_output_t) -> Spec.obs_output_reg_t).
  Parameter (update_ready_for_job : option Tag -> Spec.turn_t -> (Tag -> bool) -> option Tag).
  Parameter (output_get_valid: Spec.obs_output_reg_t -> bool).
  Parameter (local_step_fn: (input_t -> ext_sigma_t) -> input_t -> local_st_t -> local_st_t).
End SpecParams_sig.


Module SpecParams <: SpecParams_sig.
  Definition local_st_t : Type := result state_t unit.

  Definition init_turn : bool := false.
  Definition init_hist_ready : option Tag := Some Tag0.

  Definition local_step_fn (sigma: input_t -> ext_sigma_t)
                           (dummy_input: input_t)
                           : local_st_t -> local_st_t :=
    fun res_st =>
      let/res st := res_st in
      Impl.koika_step' sigma st dummy_input.

  Definition create_initial_state_fn (spec_turn: Spec.turn_t) (ready_tag: Tag) : reg_t -> nat -> list bool :=
    (fun r sz => if beq_dec r Impl.REG_clk then
                (if spec_turn then [true] else [false])
              else if beq_dec r Impl.REG_ext_ready_for_job then
                   (match ready_tag with
                    | Tag0 => [true; false]
                    | Tag1 => [true; true]
                    end)
              else if beq_dec r Impl.REG_ext_output_reg then (* for convenience in spec invariant; doesn't matter b/c we run for one cycle *)
                   option_to_maybe' Impl.sz (Some (zeroes Impl.sz))
              else Bits.zeroes sz).


  (* Create new machine, run one cycle, return the output *)
  Definition local_init_state (sigma: input_t -> ext_sigma_t)
                              (input: input_t) (tag: Tag) (turn: Spec.turn_t)
                              : local_st_t :=
      let fresh_state := SortedRegEnv.map (create_initial_state_fn turn tag) Impl.reg_tys in
    local_step_fn sigma input (Success fresh_state).

  Definition local_observe_output_reg: local_st_t -> Spec.obs_output_reg_t :=
    fun res_st => match res_st with
               | Success st => st.[Impl.REG_ext_output_reg]
               | Failure _ => []
               end.

  Definition local_observe_output: Spec.turn_t -> (Tag -> option Spec.local_output_t) -> Spec.obs_output_reg_t :=
    fun turn local_outputs =>
    match turn with
    | true => match local_outputs Tag0 with
             | Some v => v
             | None => Bits.zeroes (struct_sz Impl.S_maybe_sz)
             end
    | false => match local_outputs Tag1 with
              | Some v => v
              | None => Bits.zeroes (struct_sz Impl.S_maybe_sz)
              end
    end.

  Definition update_ready_for_job : option Tag -> Spec.turn_t -> (Tag -> bool) -> option Tag :=
    fun hist_ready_for_job turn local_busy =>
      if negb (local_busy Tag0) then Some Tag0
      else if negb (local_busy Tag1) then Some Tag1
      else None.

  Definition output_get_valid: Spec.obs_output_reg_t -> bool :=
    fun bs => match bs with
           | b::_ => b
           | _ => false
           end.
End SpecParams.

Section SpecInvariants.

    Definition mk_ready_tag (tag: Tag) :=
      option_to_maybe' 1 (Some (match tag with | Tag0 => Ob~0 | Tag1 => Ob~1 end)).

    Record SpecInvariant (tag: Tag) (spec_st: state_t) : Prop :=
       { pf_wf_spec: WF_state Impl.reg_types spec_st
       ; pf_other_job_NONE: forall reg_job,
                            is_job_reg (invert_tag tag) reg_job ->
                            (unsafe_get_job_stage (spec_st.[reg_job])) = Impl.ENUM_stage__None
       ; pf_job_NONE: forall reg_job, is_job_reg tag reg_job ->
                      (unsafe_get_job_stage (spec_st.[reg_job]) = Impl.ENUM_stage__None <->
                       SpecParams.output_get_valid (spec_st.[Impl.REG_ext_output_reg]) = true)
       ; pf_job_stage_implied: spec_st.[Impl.REG_ext_ready_for_job] = mk_ready_tag tag ->
                               forall reg_job, is_job_reg tag reg_job ->
                                          unsafe_get_job_stage (spec_st.[reg_job]) = Impl.ENUM_stage__None
       }.

End SpecInvariants.

Module SpecProofs' (ImplProofs: ImplementationProofs_Sig).
  Include ImplProofs.

  Section Specs.
    Definition Spec__InteractWithWorld : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.InteractWithWorld;
         RuleSpec_spec := RlSpec__InteractWithWorld;
         RuleSpec_pf := RlSatisfiesSpec__InteractWithWorld
      |}.

    Definition Spec__DoInput : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.DoInput;
         RuleSpec_spec := RlSpec__DoInput;
         RuleSpec_pf := RlSatisfiesSpec__DoInput
      |}.

    Definition Spec__StepBoxes : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.StepBoxes;
         RuleSpec_spec := RlSpec__StepBoxes;
         RuleSpec_pf := RlSatisfiesSpec__StepBoxes
      |}.


     Definition Spec__Step0 : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.DoStep0;
         RuleSpec_spec := RlSpec__DoStep0;
         RuleSpec_pf := RlSatisfiesSpec__DoStep0
      |}.

    Definition Spec__Step1 : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.DoStep1;
         RuleSpec_spec := RlSpec__DoStep1;
         RuleSpec_pf := RlSatisfiesSpec__DoStep1
      |}.

    Definition Spec__UpdateReady : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.UpdateReady;
         RuleSpec_spec := RlSpec__UpdateReady;
         RuleSpec_pf := RlSatisfiesSpec__UpdateReady
      |}.

  End Specs.

  Ltac ri_solve :=
    match goal with
    | H: Impl.wf_sigma ?sigma
      |- WF_ext_sigma Impl.ext_fn_types (?sigma ?input) =>
        solve[apply (Impl.wf); assumption]
    | H: ImplInvariant ?impl_st
      |- WF_state Impl.reg_types ?impl_st =>
        solve[apply (impl_wf_state _ H)]
    | |- WF_int_fn_env Impl.reg_types Impl.ext_fn_types Impl.int_fn_env Impl.struct_env=>
        solve[apply Impl.typecheck_int_fns_Success]
    | H: SpecInvariant ?tag ?spec_st
      |- WF_state Impl.reg_types ?spec_st =>
        apply (pf_wf_spec _ _ H)
    | |- _ => solve[auto with WF_auto solve_taint]
    end.

  Ltac step_oraat_scheduler Hsched RlSpec NewSt NewPostCond NewSched NewWfSt :=
    eapply oraat_interp_scheduler'_cons__spec with
      (rl_spec := RlSpec.(RuleSpec_spec)) (reg_types := Impl.reg_types) (ext_fn_types := Impl.ext_fn_types)
    in Hsched; [ | | | | |  apply RlSpec.(RuleSpec_pf) | ]; eauto;
    [ destruct Hsched as (NewSt & NewPostCond & NewSched & NewWfSt)
                      | simpl; try ri_solve ..].

  Ltac rewrite_with_custom name postcond :=
    rewrite (postcond_to_custom_lookup_name _ _ _ _ _ name postcond eq_refl).
  Ltac rewrite_with_custom_in H name postcond :=
    rewrite (postcond_to_custom_lookup_name _ _ _ _ _ name postcond eq_refl) in H.


  Ltac rewrite_with_reg_spec reg postcond :=
    rewrite (postcond_to_Prop_lookup_reg _ _ _ _ reg _ postcond eq_refl).
  Ltac rewrite_with_reg_spec_in H reg postcond :=
    rewrite (postcond_to_Prop_lookup_reg _ _ _ _ reg _ postcond eq_refl) in H.

  Ltac rewrite_no_write reg postcond :=
    rewrite (taint_set_to_prop_no_write' _ _ _ reg
                                         (postcond_to_Prop_implies_taint_set_to_Prop _ _ _ _  postcond) eq_refl).

  Ltac rewrite_no_write_in H reg postcond :=
    rewrite (taint_set_to_prop_no_write' _ _ _ reg
                                         (postcond_to_Prop_implies_taint_set_to_Prop _ _ _ _  postcond) eq_refl) in H.

  Ltac rewrite_no_write_forall reg postcond :=
    match goal with
    | H: reg_in_taint_list' reg _ |- _ =>
      rewrite (taint_set_to_prop_no_write_forall_in_list
               _ _ _ _ reg
              (postcond_to_Prop_implies_taint_set_to_Prop _ _ _ _  postcond) H eq_refl)
    end.

Arguments Impl.mk_GetJob: simpl never.
(* TODO: move *)
Lemma unsafe_get_field_maybe_valid:
  forall sz v,
  Datatypes.length v = sz ->
  unsafe_get_field (STRUCT_maybe_fields sz) FIELD_maybe_valid
                   (option_to_maybe' sz (Some v)) = Ob~1.
Proof.
  intros. unfold unsafe_get_field, option_to_maybe'.
  simpl. unfold get_field. simpl. rewrite H. rewrite PeanoNat.Nat.eqb_refl. auto.
Qed.
Lemma unsafe_get_valid_relates_output_get_valid:
  forall v,
  unsafe_get_field (dstruct_fields Impl.S_maybe_sz) FIELD_maybe_valid v = Ob~1 ->
  SpecParams.output_get_valid v = true.
Proof.
  unfold unsafe_get_field, success_or_default; simpl; intros.
  bash_destruct H. unfold SpecParams.output_get_valid.
  destruct_match; simpl in *; try discriminate.
  destruct b; simpl in *; auto. cbn in Heqr. simplify.
Qed.

  Lemma spec_invariant_preserved:
    forall tag spec_st spec_input spec_st' sigma,
      Impl.wf_sigma sigma ->
      SpecInvariant tag spec_st ->
      Impl.koika_step' sigma spec_st spec_input = Success spec_st' ->
      WF_state Impl.reg_types spec_st' ->
      (spec_st.[Impl.REG_ext_ready_for_job] = mk_ready_tag tag  <->
       is_some spec_input) ->
      (unsafe_get_job_stage (spec_st.[job_reg tag]) = Impl.ENUM_stage__None ->
       spec_st.[Impl.REG_ext_ready_for_job] = mk_ready_tag tag)  ->
      SpecInvariant tag spec_st'.
  Proof.
    intros * pf_wf_sigma HInv Hsched Hwf_st' Hext_ready_for_job Hjob_stage.
    unfold Impl.koika_step' in *.
    consider interp_cycle. destruct_matches_in_hyp Hsched; simplify.
    unfold interp_scheduler in *.
    specialize schedule_does_not_conflict_implies with
          (1 := Impl.oraat_schedule_does_not_conflict); intros (taint & Htaint).

    eapply oraat_interp_schedule'_correct with (reg_types := Impl.reg_types) (ext_fn_types := Impl.ext_fn_types) (taint := SortedRegEnv.empty) (taint' := taint) in Heqr; eauto; try ri_solve.
    2: eapply taint_env_approximates_log_empty.
    rename Heqr into Horaat.
    clear Htaint.

    rewrite commit_update_empty in Horaat.
    consider Impl.schedule. consider interp_scheduler.

    step_oraat_scheduler Horaat Spec__InteractWithWorld St__World Post__World Sched__World WF__World.
    step_oraat_scheduler Sched__World Spec__DoInput St__Input Post__Input Sched__Input WF__Input.
    step_oraat_scheduler Sched__Input Spec__StepBoxes St__Boxes Post__Boxes Sched__Boxes WF__Boxes.
    step_oraat_scheduler Sched__Boxes Spec__Step0 St__Step0 Post__Step0 Sched__Step0 WF__Step0.
    step_oraat_scheduler Sched__Step0 Spec__Step1 St__Step1 Post__Step1 Sched__Step1 WF__Step1.
    step_oraat_scheduler Sched__Step1 Spec__UpdateReady St__UpdateReady Post__UpdateReady Sched__UpdateReady WF__UpdateReady.
    simpl in Sched__UpdateReady. simplify_tupless.

    constructor; auto.
    - intros * Hjob_reg; destruct tag; unfold is_job_reg, invert_tag in *; simpl in Hjob_reg; subst.
      + rewrite_no_write Impl.REG_job1 Post__UpdateReady.
        rewrite_with_reg_spec Impl.REG_job1 Post__Step1.
        rewrite_no_write Impl.REG_job1 Post__Step0.
        rewrite_no_write Impl.REG_job1 Post__Boxes.
        rewrite_with_reg_spec Impl.REG_job1 Post__Input.
        rewrite_no_write Impl.REG_ext_ready_for_job Post__World.
        rewrite_no_write Impl.REG_job1 Post__World.
        destruct_match.
        * apply andb_true_iff in Heqb. propositional. apply bits_eq_iff in Heqb0.
          apply bits_eq_iff in Heqb1.
          rewrite Impl.wf_GetJob in Heqb1; try ri_solve.
          destruct spec_input; simpl in *.
          { rewrite Hext_ready_for_job1 in Heqb0; [discriminate | eexists; eauto]. }
          { discriminate. }
        * erewrite pf_other_job_NONE; eauto; [ | reflexivity].
          simpl.
          eapply pf_other_job_NONE; eauto; reflexivity.
      + rewrite_no_write Impl.REG_job0 Post__UpdateReady.
        rewrite_no_write Impl.REG_job0 Post__Step1.
        rewrite_with_reg_spec Impl.REG_job0 Post__Step0.
        rewrite_no_write Impl.REG_job0 Post__Boxes.
        rewrite_with_reg_spec Impl.REG_job0 Post__Input.
        rewrite_no_write Impl.REG_ext_ready_for_job Post__World.
        rewrite_no_write Impl.REG_job0 Post__World.
        destruct_match.
        * apply andb_true_iff in Heqb. propositional. apply bits_eq_iff in Heqb0.
          apply bits_eq_iff in Heqb1.
          rewrite Impl.wf_GetJob in Heqb1; try ri_solve.
          destruct spec_input; simpl in *.
          { rewrite Hext_ready_for_job1 in Heqb0; [ discriminate | eexists; eauto]. }
          { discriminate. }
        * erewrite pf_other_job_NONE; eauto; [ | reflexivity].
          simpl.
          eapply pf_other_job_NONE; eauto; reflexivity.
    - intros * Hjob_reg; destruct tag; unfold is_job_reg, invert_tag in *; simpl in Hjob_reg; subst.
      + rewrite_no_write Impl.REG_job0 Post__UpdateReady.
        rewrite_with_reg_spec Impl.REG_ext_output_reg Post__UpdateReady.
        rewrite_no_write Impl.REG_job0 Post__Step1.
        rewrite_no_write Impl.REG_ext_output_reg0 Post__Step1.
        split; intros X.
        { destruct_with_eqn (bits_eq (unsafe_get_job_stage St__Step0.[Impl.REG_job0]) (unsafe_get_job_stage St__Boxes.[Impl.REG_job0])).
          { apply bits_eq_iff in Heqb. simpl in *.
            exfalso.
            rewrite_no_write_in Heqb Impl.REG_job0 Post__Boxes.
            rewrite_with_reg_spec_in Heqb Impl.REG_job0 Post__Input.
            rewrite_no_write_in Heqb Impl.REG_ext_ready_for_job Post__World.
            rewrite_no_write_in Heqb Impl.REG_job0 Post__World.
            destruct_matches_in_hyp Heqb.
            { apply andb_true_iff in Heqb0. propositional. apply bits_eq_iff in Heqb1.
              apply bits_eq_iff in Heqb2.
              rewrite_with_custom_in Heqb DoInput__Job0__Stage Post__Input.
              { rewrite X in Heqb. discriminate. }
              { simpl in Heqb1. propositional. unfold is_some in *. propositional.
                rewrite_no_write Impl.REG_ext_ready_for_job Post__World.
                auto.
              }
            }
            { rewrite X in Heqb.
              symmetry in Heqb. propositional. rewrite Hjob_stage in Heqb0.
              unfold is_some in *; propositional; simpl in Heqb0.
              rewrite Impl.wf_GetJob in Heqb0; auto. simpl in Heqb0.
              unfold Impl.mk_GetJob in Heqb0.
              rewrite unsafe_get_field_maybe_valid in Heqb0; [ | rewrite firstn_fill_length]; auto.
              apply bits_neq_iff in Heqb0. contradiction.
            }
          }
          { destruct_match.
            - apply bits_eq_iff in Heqb0.
              apply bits_neq_iff in Heqb.
              assert (unsafe_get_field (dstruct_fields Impl.S_maybe_sz) FIELD_maybe_valid
                      St__Step0.[Impl.REG_ext_output_reg0] = [true]).
              { rewrite_with_custom DoStep0__ext_output_reg Post__Step0; auto.
                rewrite X in Heqb. auto.
              }
              { apply unsafe_get_valid_relates_output_get_valid; auto. }
            - apply bits_neq_iff in Heqb0. apply bits_neq_iff in Heqb.
              rewrite_no_write_in Heqb0 Impl.REG_clk Post__Step1.
              rewrite_no_write_in Heqb0 Impl.REG_clk Post__Step0.
              rewrite_with_custom_in Heqb0 DoStep0__finish_clk_inversion Post__Step0; auto.
              rewrite X in Heqb. auto.
          }
        }
        { destruct_with_eqn (bits_eq (unsafe_get_job_stage St__Step0.[Impl.REG_job0]) Impl.ENUM_stage__None); try solve_bits.
          apply bits_neq_iff in Heqb.
          rewrite_with_reg_spec_in X Impl.REG_ext_output_reg0 Post__Step0; auto.
          destruct_matches_in_hyp X; [ discriminate | ].
          destruct_with_eqn (bits_eq (unsafe_get_job_stage St__Step0.[Impl.REG_job1]) Impl.ENUM_stage__None).
          { apply  bits_eq_iff in Heqb1. rewrite_with_reg_spec_in X Impl.REG_ext_output_reg1 Post__Step1; auto.
            discriminate.
          }
          { apply bits_neq_iff in Heqb1.
            rewrite_no_write_in Heqb1 Impl.REG_job1 Post__Step0.
            rewrite_no_write_in Heqb1 Impl.REG_job1 Post__Boxes.
            rewrite_with_reg_spec_in Heqb1 Impl.REG_job1 Post__Input.
            rewrite_no_write_in Heqb1 Impl.REG_ext_ready_for_job Post__World.
            rewrite_no_write_in Heqb1 Impl.REG_job1 Post__World.
            destruct_matches_in_hyp Heqb1.
            { apply andb_true_iff in Heqb2; propositional. apply bits_eq_iff in Heqb3.
              apply bits_eq_iff in Heqb4. destruct spec_input; simpl in Heqb4.
              { rewrite Hext_ready_for_job1 in Heqb3; [ | eexists; eauto]. discriminate. }
              { rewrite Impl.wf_GetJob in Heqb4 by auto. discriminate. }
            }
            { erewrite pf_other_job_NONE with (tag := Tag0) in Heqb1; try ri_solve; auto; reflexivity. }
          }
        }
      + rewrite_no_write Impl.REG_job1 Post__UpdateReady.
        rewrite_with_reg_spec Impl.REG_ext_output_reg Post__UpdateReady.
        rewrite_no_write Impl.REG_ext_output_reg0 Post__Step1.
        split; intros X.
        { destruct_with_eqn (bits_eq (unsafe_get_job_stage St__Step1.[Impl.REG_job1]) (unsafe_get_job_stage St__Step0.[Impl.REG_job1])).
          { apply bits_eq_iff in Heqb. simpl in *.
            exfalso.
            rewrite_no_write_in Heqb Impl.REG_job1 Post__Step0.
            rewrite_no_write_in Heqb Impl.REG_job1 Post__Boxes.
            rewrite_with_reg_spec_in Heqb Impl.REG_job1 Post__Input.
            rewrite_no_write_in Heqb Impl.REG_ext_ready_for_job Post__World.
            rewrite_no_write_in Heqb Impl.REG_job1 Post__World.
            destruct_matches_in_hyp Heqb.
            { apply andb_true_iff in Heqb0. propositional. apply bits_eq_iff in Heqb1.
              apply bits_eq_iff in Heqb2.
              rewrite_with_custom_in Heqb DoInput__Job1__Stage Post__Input.
              { rewrite X in Heqb. discriminate. }
              { simpl in Heqb1. propositional. unfold is_some in *. propositional.
                rewrite_no_write Impl.REG_ext_ready_for_job Post__World.
                auto.
              }
            }
            { rewrite X in Heqb.
              symmetry in Heqb. propositional. rewrite Hjob_stage in Heqb0.
              unfold is_some in *; propositional; simpl in Heqb0.
              rewrite Impl.wf_GetJob in Heqb0; auto. simpl in Heqb0.
              unfold Impl.mk_GetJob in Heqb0.
              rewrite unsafe_get_field_maybe_valid in Heqb0; [ | rewrite firstn_fill_length]; auto.
              apply bits_neq_iff in Heqb0. contradiction.
            }
          }
          { destruct_match.
            - apply bits_eq_iff in Heqb0. apply bits_neq_iff in Heqb.
              rewrite_no_write_in Heqb0 Impl.REG_clk Post__Step1.
              rewrite_with_custom_in Heqb0 DoStep1__finish_clk_inversion Post__Step1; auto; try discriminate.
              rewrite X in Heqb. auto.
            - apply bits_neq_iff in Heqb0.
              apply bits_neq_iff in Heqb.
              assert (unsafe_get_field (dstruct_fields Impl.S_maybe_sz) FIELD_maybe_valid
                      St__Step1.[Impl.REG_ext_output_reg1] = [true]).
              { rewrite_with_custom DoStep1__ext_output_reg Post__Step1; auto.
                rewrite X in Heqb. auto.
              }
              { apply unsafe_get_valid_relates_output_get_valid; auto. }
          }
        }
        { destruct_with_eqn (bits_eq (unsafe_get_job_stage St__Step1.[Impl.REG_job1]) Impl.ENUM_stage__None); try solve_bits.
          apply bits_neq_iff in Heqb.
          rewrite_with_reg_spec_in X Impl.REG_ext_output_reg1 Post__Step1; auto.
          destruct_matches_in_hyp X; [ | discriminate ].
          destruct_with_eqn (bits_eq (unsafe_get_job_stage St__Step0.[Impl.REG_job0]) Impl.ENUM_stage__None).
          { apply bits_eq_iff in Heqb1.
            destruct_with_eqn (bits_eq (unsafe_get_job_stage St__Boxes.[Impl.REG_job0]) Impl.ENUM_stage__None ).
            { apply bits_eq_iff in Heqb2.
              rewrite_with_reg_spec_in X Impl.REG_ext_output_reg0 Post__Step0; auto. discriminate.
            }
            { apply bits_neq_iff in Heqb2.
              rewrite_no_write_in Heqb2 Impl.REG_job0 Post__Boxes.
              rewrite_with_reg_spec_in Heqb2 Impl.REG_job0 Post__Input.
              rewrite_no_write_in Heqb2 Impl.REG_job0 Post__World.
              rewrite_no_write_in Heqb2 Impl.REG_ext_ready_for_job Post__World.
              destruct_matches_in_hyp Heqb2.
              { apply andb_true_iff in Heqb3; propositional.
                apply bits_eq_iff in Heqb5. apply bits_eq_iff in Heqb4.
                rewrite Impl.wf_GetJob in Heqb5 by auto.  simpl in Heqb5.
                destruct spec_input; propositional.
                { rewrite Hext_ready_for_job1 in Heqb4; [ discriminate | eexists; eauto]. }
                { discriminate. }
              }
              { rewrite pf_other_job_NONE with (tag := Tag1) in Heqb2; auto. reflexivity. }
            }
          }
          { apply bits_neq_iff in Heqb1.
            rewrite_with_reg_spec_in X Impl.REG_ext_output_reg0 Post__Step0; auto.
            discriminate.
          }
        }
    - intros * Hjob_reg; destruct tag; unfold is_job_reg, invert_tag in *; simpl in Hjob_reg; subst.
      + intros; subst; simpl.
        rewrite_with_reg_spec_in Hjob_reg Impl.REG_ext_ready_for_job Post__UpdateReady.
        rewrite_no_write Impl.REG_job0 Post__UpdateReady.
        rewrite_no_write Impl.REG_job0 Post__Step1.
        rewrite_no_write_in Hjob_reg Impl.REG_job0' Post__Step1.
        bash_destruct Hjob_reg; try discriminate.
        rewrite_with_reg_spec_in Heqb Impl.REG_job0' Post__Step0. solve_bits.
      + intros; subst; simpl.
        rewrite_with_reg_spec_in Hjob_reg Impl.REG_ext_ready_for_job Post__UpdateReady.
        rewrite_no_write Impl.REG_job1 Post__UpdateReady.
        rewrite_with_reg_spec_in Hjob_reg Impl.REG_job1' Post__Step1.
        bash_destruct Hjob_reg; try discriminate. solve_bits.
  Qed.


End SpecProofs'.

Module SpecProofs := SpecProofs' (ImplementationProofs).
