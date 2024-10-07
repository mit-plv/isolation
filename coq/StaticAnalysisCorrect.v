Require Import Koika.Common.
Require Import Koika.Utils.
Require Import Koika.Syntax.
Require Import Koika.Semantics.
Require Import Koika.Environments.
Require Import Koika.Typechecking.
Require Import Koika.Tactics.
Require Import Koika.StaticAnalysis.
Require Import Koika.TypecheckingCorrectness.
Require Import FunctionalExtensionality.

Section TODO_MOVE_TaintLemmas.

  (* TODO: MOVE *)
  Lemma merge_taint_env_empty_l:
    forall env,
      merge_taint_env SortedRegEnv.empty env = env.
  Proof.
    unfold merge_taint_env. intros. apply SortedRegEnv.env_ext.
    intros. rewrite SortedRegEnv.opt_get_mapV.
    rewrite SortedRegEnv.opt_get_zip_default.
    rewrite SortedRegEnv.opt_get_empty.
    destruct_match; auto.
    rewrite merge_taints_empty_l.
    reflexivity.
  Qed.
  Lemma merge_taint_env_empty_r:
    forall env,
      merge_taint_env env SortedRegEnv.empty = env.
  Proof.
    unfold merge_taint_env. intros. apply SortedRegEnv.env_ext.
    intros. rewrite SortedRegEnv.opt_get_mapV.
    rewrite SortedRegEnv.opt_get_zip_default.
    rewrite SortedRegEnv.opt_get_empty.
    destruct_match; auto.
    rewrite merge_taints_empty_r.
    reflexivity.
  Qed.

  Lemma merge_taints_assoc:
    forall t1 t2 t3,
      merge_taints (merge_taints t1 t2) t3 = merge_taints t1 (merge_taints t2 t3).
  Proof.
    unfold merge_taints; simpl. intros. repeat rewrite<-orb_assoc. reflexivity.
  Qed.

  Lemma merge_taints_comm:
    forall t1 t2 ,
      merge_taints t1 t2 = merge_taints t2 t1.
  Proof.
    unfold merge_taints; simpl. intros.
    f_equal; rewrite orb_comm; reflexivity.
  Qed.

  Lemma merge_taint_env_assoc:
    forall env1 env2 env3,
    merge_taint_env (merge_taint_env env1 env2) env3 = merge_taint_env env1 (merge_taint_env env2 env3).
  Proof.
    unfold merge_taint_env. intros. apply SortedRegEnv.env_ext. intros.
    rewrite SortedRegEnv.opt_get_mapV.
    rewrite SortedRegEnv.opt_get_zip_default.
    repeat rewrite SortedRegEnv.opt_get_mapV.
    repeat rewrite SortedRegEnv.opt_get_zip_default.
    repeat rewrite SortedRegEnv.opt_get_mapV.
    repeat rewrite SortedRegEnv.opt_get_zip_default.
    repeat destruct_match; try rewrite merge_taints_assoc; auto.
  Qed.

  Lemma merge_taint_env_comm:
    forall env1 env2,
    merge_taint_env env1 env2 = merge_taint_env env2 env1.
  Proof.
    unfold merge_taint_env. intros.  apply SortedRegEnv.env_ext. intros.
    repeat rewrite SortedRegEnv.opt_get_mapV.
    repeat rewrite SortedRegEnv.opt_get_zip_default.
    repeat destruct_match; try rewrite merge_taints_comm; auto.
  Qed.

  Lemma taint_set_to_prop_no_write:
    forall st1 st2 res_taint_set reg,
    taint_set_to_prop st1 st2 res_taint_set ->
    no_writes_in_taint_set res_taint_set reg  = true ->
    get_reg st2 reg = get_reg st1 reg.
  Proof.
    intros * Hset Hwrites.
    consider taint_set_to_prop.
    consider no_writes_in_taint_set.
    consider get_reg. simplify.
    specialize (Hset reg).
    bash_destruct Hset; discriminate.
  Qed.


    Lemma taint_set_to_prop_no_write':
      forall st1 st2 res_taint_set reg,
      taint_set_to_prop st1 st2 res_taint_set ->
      no_writes_in_taint_set res_taint_set reg  = true ->
      st2.[reg] = st1.[reg].
    Proof.
      intros. apply unsafe_get_reg_ext. eapply taint_set_to_prop_no_write; eauto.
    Qed.



End TODO_MOVE_TaintLemmas.

Section FailSafety.
  Context (ext_sigma: ext_sigma_t).
  Context (int_fns: int_fn_env_t).
  Context (struct_defs: struct_env_t).
  Ltac solve_action_fail_safety IH :=
      match goal with
      | H: _ || _ = false |- _ =>
          rewrite orb_false_iff in H
      | H: _ && _ = true |- _ =>
          rewrite andb_true_iff in H
      | H: oraat_interp_action _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
          match b with
          | true => fail
          | _ => let H' := fresh in
                assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
                rewrite H' in H; subst
          end
      | H: oraat_interp_action ?sigma ?int_fns ?struct_defs ?fuel ?r ?r_acc true ?gamma ?_action = (true, None),
        H1: action_contains_fail ?int_fns ?_fuel2 ?action = Success false
        |- _ =>
          apply IH with (fuel2 := _fuel2) in H; auto
      | |- _ => progress (repeat simpl_match; simpl in *;simplify;propositional; auto)
      end.


  Lemma action_fail_safety:
    forall fuel1 fuel2 r r_acc b gamma action,
    oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc b gamma action = (true, None) ->
    action_contains_fail int_fns fuel2 action = Success false ->
    False.
  Proof.
    induction fuel1; intros fuel2 r r_acc b gamma action Horaat Haction;
      simpl in *; simplify; [discriminate | ].
    destruct fuel2; simpl in *; [discriminate | ].
    destruct action; cbn in *; simplify; simpl in *;
      destruct_all_matches; unfold get_fn_arg_and_body'', __debug__ in *;
      repeat solve_action_fail_safety IHfuel1; propositional.
  Qed.

End FailSafety.

Section TaintSafety.
  Context (ext_sigma: ext_sigma_t).
  Context (int_fns: int_fn_env_t).
  Context (struct_defs: struct_env_t).

  Definition taint_env_corresponds_to_state_update (st1 st2: state_t) (env: taint_env_t) : Prop :=
    forall reg,
      match SortedRegEnv.opt_get env reg with
      | Some t =>
          if taint_write0 t || taint_write1 t then True
          else get_reg st1 reg = get_reg st2 reg
      | None => get_reg st1 reg = get_reg st2 reg
      end.
  Lemma taint_env_corresponds_to_state_update__empty:
    forall st,
      taint_env_corresponds_to_state_update st st SortedRegEnv.empty.
  Proof.
    unfold taint_env_corresponds_to_state_update; intros.
    rewrite SortedRegEnv.opt_get_empty. reflexivity.
  Qed.

  Lemma taint_env_corresponds_to_state_update__unchanged:
    forall st env,
      taint_env_corresponds_to_state_update st st env.
  Proof.
    unfold taint_env_corresponds_to_state_update; intros.
    repeat destruct_match; auto.
  Qed.

  Lemma taint_env_corresponds_taint_le:
    forall r r' env env',
      taint_env_corresponds_to_state_update r r' env ->
      taint_env_le env env' ->
      taint_env_corresponds_to_state_update r r' env'.
  Proof.
    unfold taint_env_corresponds_to_state_update, taint_env_le.
    intros * Hstate Hle reg. specialize (Hstate reg). specialize (Hle reg).
    consider get_reg_taint_default. destruct_all_matches.
    - rewrite orb_true_iff in Heqb0. rewrite orb_false_iff in Heqb.
      destruct Hle. split_cases; congruence.
    - rewrite orb_true_iff in Heqb.
      destruct Hle. simpl in *. split_cases; congruence.
  Qed.

  Lemma taint_env_corresponds_merge_l:
    forall r r' env env',
      taint_env_corresponds_to_state_update r r' env ->
      taint_env_corresponds_to_state_update r r' (merge_taint_env env env').
  Proof.
    intros.
    eapply taint_env_corresponds_taint_le; eauto.
    eapply taint_env_le_merge_refl_l.
  Qed.
  Lemma taint_env_corresponds_merge_r:
    forall r r' env env',
      taint_env_corresponds_to_state_update r r' env ->
      taint_env_corresponds_to_state_update r r' (merge_taint_env env' env).
  Proof.
    intros.
    eapply taint_env_corresponds_taint_le; eauto.
    eapply taint_env_le_merge_refl_r.
  Qed.

  Lemma taint_env_corresponds_set_read0:
    forall r r' taint_env idx,
      taint_env_corresponds_to_state_update r r' taint_env ->
      taint_env_corresponds_to_state_update r r' (set_reg_taint taint_env idx set_taint_read0).
  Proof.
    unfold taint_env_corresponds_to_state_update, set_reg_taint. intros * Htaint reg.
    specialize (Htaint reg).
    destruct_with_eqn (Nat.eqb idx reg); simplify.
    - rewrite SortedRegEnv.update_correct_eq; auto.
      bash_destruct Htaint; simpl; simpl_match; auto.
    - rewrite SortedRegEnv.update_correct_neq; auto.
  Qed.

  Lemma taint_env_corresponds_set_read1:
    forall r r' taint_env idx,
      taint_env_corresponds_to_state_update r r' taint_env ->
      taint_env_corresponds_to_state_update r r' (set_reg_taint taint_env idx set_taint_read1).
  Proof.
    unfold taint_env_corresponds_to_state_update, set_reg_taint. intros * Htaint reg.
    specialize (Htaint reg).
    destruct_with_eqn (Nat.eqb idx reg); simplify.
    - rewrite SortedRegEnv.update_correct_eq; auto.
      bash_destruct Htaint; simpl; simpl_match; auto.
    - rewrite SortedRegEnv.update_correct_neq; auto.
  Qed.

  Lemma taint_env_corresponds_set_write0:
    forall r r' taint_env idx v,
      taint_env_corresponds_to_state_update r r' taint_env ->
      taint_env_corresponds_to_state_update r (state_set r' idx v) (set_reg_taint taint_env idx set_taint_write0).
  Proof.
    unfold taint_env_corresponds_to_state_update, set_reg_taint. intros * Htaint reg.
    specialize (Htaint reg).
    destruct_with_eqn (Nat.eqb idx reg); simplify.
    - rewrite SortedRegEnv.update_correct_eq; auto.
      destruct_all_matches; simpl in *; try discriminate.
    - rewrite SortedRegEnv.update_correct_neq; auto.
      destruct_all_matches; simpl in *; try discriminate.
      + rewrite get_set_reg_neq by auto. auto.
      + rewrite get_set_reg_neq by auto. auto.
  Qed.

  Lemma taint_env_corresponds_set_write1:
    forall r r' taint_env idx v,
      taint_env_corresponds_to_state_update r r' taint_env ->
      taint_env_corresponds_to_state_update r (state_set r' idx v) (set_reg_taint taint_env idx set_taint_write1).
  Proof.
    unfold taint_env_corresponds_to_state_update, set_reg_taint. intros * Htaint reg.
    specialize (Htaint reg).
    destruct_with_eqn (Nat.eqb idx reg); simplify.
    - rewrite SortedRegEnv.update_correct_eq; auto.
      destruct_all_matches; simpl in *; try discriminate.
      * rewrite orb_true_r in Heqb. discriminate.
      * rewrite orb_true_r in Heqb. discriminate.
    - rewrite SortedRegEnv.update_correct_neq; auto.
      destruct_all_matches; simpl in *; try discriminate.
      + rewrite get_set_reg_neq by auto. auto.
      + rewrite get_set_reg_neq by auto. auto.
  Qed.

  Create HintDb solve_taint.

  Hint Immediate taint_env_corresponds_set_read0 : solve_taint.
  Hint Immediate taint_env_corresponds_set_read1 : solve_taint.
  Hint Immediate taint_env_corresponds_set_write0 : solve_taint.
  Hint Immediate taint_env_corresponds_set_write1 : solve_taint.
  Hint Immediate taint_env_corresponds_merge_l : solve_taint.
  Hint Immediate taint_env_corresponds_merge_r : solve_taint.
  Hint Immediate taint_env_le_refl : solve_taint.

  Ltac solve_taint_safety_action IH :=
    match goal with
    | |- taint_env_corresponds_to_state_update ?r ?r _ =>
      apply taint_env_corresponds_to_state_update__unchanged
    | H: _ && _ = true |- _ => rewrite andb_true_iff in H; propositional
    | H: true = _ && _ |- _ => symmetry in H
    | H: oraat_interp_action _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
        match b with
        | true => fail
        | _ => let H' := fresh in
              assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
              rewrite H' in H; subst
        end
    | H: oraat_interp_action ?sigma ?int_fns ?struct_defs ?fuel ?r ?r_acc true ?gamma ?_action = (true, Some (_, ?_r', _)),
      Htaint : taint_env_corresponds_to_state_update ?r ?r_acc ?_taint_env,
      Hsuccess : taint_action ?int_fns ?_fuel2 ?_taint_env ?_action = Success (Some ?_env)
      |- _ =>
        eapply IH with (taint_env := _taint_env) (env := _env) (fuel2 := _fuel2) in H ; auto
    | H: oraat_interp_action ?sigma ?int_fns ?struct_defs ?fuel ?r ?r_acc true ?gamma ?_action = (true, None),
      Htaint : taint_env_corresponds_to_state_update ?r ?r_acc ?_taint_env,
      Hsuccess : taint_action ?int_fns ?_fuel2 ?_taint_env ?_action = Success (Some ?_env)
      |- _ =>
        eapply IH with (taint_env := _taint_env) (env := _env) (fuel2 := _fuel2) in H ; auto
    | H1: taint_env_le ?t ?env,
      H2: taint_env_le ?env ?t' |- _ =>
        lazymatch goal with
        | H : taint_env_le t t' |- _ => fail
        | |- _ => (pose proof (taint_env_le_trans _ _ _ H1 H2))
        end
    | H: taint_action _ _ ?taint_env _ = Success (Some ?taint_env') |- _ =>
        lazymatch goal with
        | H': taint_env_le taint_env taint_env' |- _ => fail
        | _ => (pose proof (taint_action_generalizes_taint _ _ _ _ _ H))
        end
    | |- _ /\ _ => split
    | |- _ => progress (simpl in *;simplify;propositional; auto with solve_taint)
    end.

  Lemma taint_safety_action:
    forall fuel1 fuel2 r r_acc gamma taint_env action env gamma' st' res,
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc true
         gamma action = (true, Some (gamma', st', res)) ->
      taint_env_corresponds_to_state_update r r_acc taint_env ->
      taint_action int_fns fuel2 taint_env action = Success (Some env) ->
      taint_env_corresponds_to_state_update r st' env.
  Proof.
    induction fuel1;
      intros fuel2 r r_acc gamma taint_env action env gamma' st' res
             Horaat Htaint Hsuccess; simpl in *; simplify; subst.
    destruct fuel2; [simpl in *; discriminate | ].
    destruct action; cbn in *; simplify_tupless; propositional;
      destruct_match_pairs; unfold res_opt_bind, get_fn_arg_and_body'', __debug__ in *; repeat solve_taint_safety_action IHfuel1; destruct_all_matches; simplify; repeat solve_taint_safety_action IHfuel1.
  Qed.

  Ltac solve_taint_safety_function' IH :=
    match goal with
    | H: oraat_interp_action _ _ _ _ _ ?r_acc true _ ?action = (true, Some _),
      H1: taint_env_corresponds_to_state_update ?r_base ?r_acc ?env,
      H2: taint_action _ ?fuel2 ?env ?action = Success (Some _) |- _ =>
        eapply IH with (2 := H1) (3 := H2) in H
    | |- taint_env_corresponds_to_state_update ?r ?r _ =>
      apply taint_env_corresponds_to_state_update__unchanged
    | H: _ && _ = true |- _ => rewrite andb_true_iff in H; propositional
    | H: true = _ && _ |- _ => symmetry in H
    | H: oraat_interp_action _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
        match b with
        | true => fail
        | _ => let H' := fresh in
              assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
              rewrite H' in H; subst
        end
    | |- _ => progress (simpl in *;simplify;propositional; auto with solve_taint)
    end.


  Lemma taint_safety_function':
    forall fuel1 fuel2 r r_acc gamma action gamma' st' res env env' r_base,
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc true
         gamma action = (true, Some (gamma', st', res)) ->
      taint_env_corresponds_to_state_update r_base r_acc env ->
      taint_action int_fns fuel2 env action = Success (Some env') ->
      taint_env_corresponds_to_state_update r_base st' env'.
  Proof.
    induction fuel1;
      intros fuel2 r r_acc gamma action gamma' st' res env env' r_base
             Horaat Htaint Hsuccess; simpl in *; simplify; subst.
    destruct fuel2; [simpl in *; discriminate | ].
    destruct action; cbn in *; simplify_tupless; propositional;
      destruct_match_pairs; unfold res_opt_bind, get_fn_arg_and_body'', __debug__ in *;
      destruct_all_matches; repeat solve_taint_safety_function' IHfuel1.
  Qed.


  Lemma taint_safety_function:
    forall fuel1 fuel2 r r_acc gamma action gamma' st' res,
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc true
         gamma action = (true, Some (gamma', st', res)) ->
      is_success_some (taint_action int_fns fuel2 SortedRegEnv.empty action) = true ->
      taint_set_to_prop r_acc st' (taint_action int_fns fuel2 SortedRegEnv.empty action).
  Proof.
    intros * Horaat Hsuccess.
    unfold is_success_some in *. bash_destruct Hsuccess.
    eapply taint_safety_function' with (r_base := r_acc) (env := SortedRegEnv.empty) (fuel2 := fuel2) in Horaat; eauto.
    apply taint_env_corresponds_to_state_update__empty; auto.
  Qed.

  Lemma taint_safety_rule:
    forall st1 st2 rule,
    oraat_interp_rule ext_sigma int_fns struct_defs st1 rule = (true, st2) ->
    is_success_some (taint_rule_from_empty int_fns rule) = true ->
    taint_set_to_prop st1 st2 (taint_rule_from_empty int_fns rule).
  Proof.
    unfold oraat_interp_rule, taint_rule_from_empty, taint_rule.
    unfold taint_set_to_prop.
    intros.
    destruct_match_pairs.
    destruct_matches_in_hyp H; destruct_match_pairs; simplify_tupless; unfold is_success_some in *; simplify.
    - bash_destruct H0.
      eapply taint_safety_action; eauto.
      apply taint_env_corresponds_to_state_update__empty.
    - bash_destruct H0.
      intros; repeat destruct_match; auto.
  Qed.

  Section ReadOnly.
    Definition read_only_taint (env: taint_env_t) :=
      forall reg,
        match SortedRegEnv.opt_get env reg with
        | Some t => if taint_write0 t || taint_write1 t then False else True
        | None => True
        end.

    Lemma empty_taint_read_only: read_only_taint SortedRegEnv.empty.
    Proof.
      unfold read_only_taint; intros.
      rewrite SortedRegEnv.opt_get_empty. auto.
    Qed.

    Lemma read_only_taint_le:
      forall env env',
      read_only_taint env' ->
      taint_env_le env env' ->
      read_only_taint env.
    Proof.
      intros * Hread Htaint. unfold read_only_taint, taint_env_le in *.
      intros reg.
      specialize (Htaint reg). specialize (Hread reg). unfold get_reg_taint_default in *.
      destruct Htaint.
      destruct_all_matches; auto.
      - rewrite orb_false_iff in Heqb0. rewrite orb_true_iff in Heqb. propositional.
        split_cases; congruence.
      - rewrite orb_true_iff in Heqb. simpl in *. split_cases; congruence.
    Qed.

    Lemma read_only_taint_merge_l_invert:
      forall t1 t2,
      read_only_taint (merge_taint_env t1 t2) ->
      read_only_taint t1.
    Proof.
      intros; eapply read_only_taint_le; eauto.
      eapply taint_env_le_merge_refl_l.
    Qed.

    Lemma read_only_taint_merge_r_invert:
      forall t1 t2,
      read_only_taint (merge_taint_env t1 t2) ->
      read_only_taint t2.
    Proof.
      intros; eapply read_only_taint_le; eauto.
      eapply taint_env_le_merge_refl_r.
    Qed.
    Ltac progress_pose_as Name Value :=
      lazymatch goal with
      | H' : Value |- _ => fail
      | _ => pose proof Value as Name
      end.
     Lemma not_read_only_set_write0:
      forall taint idx,
      read_only_taint (set_reg_taint taint idx set_taint_write0) -> False.
    Proof.
      intros * Htaint. consider read_only_taint.
      specialize (Htaint idx). consider set_reg_taint.
      rewrite SortedRegEnv.update_correct_eq in Htaint; simpl in *.
      destruct_matches_in_hyp Htaint; simpl in *; auto.
    Qed.

    Lemma not_read_only_set_write1:
      forall taint idx,
      read_only_taint (set_reg_taint taint idx set_taint_write1) -> False.
    Proof.
      intros * Htaint. consider read_only_taint.
      specialize (Htaint idx). consider set_reg_taint.
      rewrite SortedRegEnv.update_correct_eq in Htaint; simpl in *.
      destruct_matches_in_hyp Htaint; simpl in *; auto.
      rewrite orb_true_r in Htaint; simpl in *; auto.
    Qed.

    Ltac solve_taint_safety_read_only_action IH :=
      match goal with
      | H: _ && _ = true |- _ => rewrite andb_true_iff in H; propositional
      | H: true = _ && _ |- _ => symmetry in H
      | H: oraat_interp_action _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
          match b with
          | true => fail
          | _ => let H' := fresh in
                assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
                rewrite H' in H; subst
          end
      | H: oraat_interp_action ?sigma ?int_fns ?struct_defs ?fuel ?r ?r_acc true ?gamma ?_action = (true, Some (_, ?_r', _)),
        Htaint0 : read_only_taint ?_taint_env,
        Htaint1 : read_only_taint ?_env,
        Hsuccess : taint_action ?int_fns ?_fuel2 ?_taint_env ?_action = Success (Some ?_env)
        |- _ =>
          eapply IH with (env := _taint_env) (env' := _env) (fuel2 := _fuel2) in H ; auto
      | H1: taint_env_le ?t ?env,
        H2: taint_env_le ?env ?t' |- _ =>
          lazymatch goal with
          | H : taint_env_le t t' |- _ => fail
          | |- _ => (pose proof (taint_env_le_trans _ _ _ H1 H2))
          end
      | H: taint_action _ _ ?taint_env _ = Success (Some ?taint_env') |- _ =>
          lazymatch goal with
          | H': taint_env_le taint_env taint_env' |- _ => fail
          | _ => (pose proof (taint_action_generalizes_taint _ _ _ _ _ H))
          end
      | H : taint_env_le ?env ?env',
        H1: read_only_taint ?env' |- _ =>
          lazymatch goal with
          | H2: read_only_taint env |- _ => fail
          | |- _ => pose proof (read_only_taint_le _ _ H1 H)
          end
      | H : read_only_taint (merge_taint_env ?env1 ?env2) |- _ =>
          lazymatch goal with
          | H2: read_only_taint env1 |- _ => fail
          | |- _ => pose proof (read_only_taint_merge_l_invert _ _ H)
          end
      | H : read_only_taint (merge_taint_env ?env1 ?env2) |- _ =>
          lazymatch goal with
          | H2: read_only_taint env2 |- _ => fail
          | |- _ => pose (read_only_taint_merge_r_invert _ _ H)
          end
      | H: read_only_taint (set_reg_taint _ _ set_taint_write1) |- _ =>
          apply not_read_only_set_write1 in H; contradiction
      | H: read_only_taint (set_reg_taint _ _ set_taint_write0) |- _ =>
          apply not_read_only_set_write0 in H; contradiction
      | |- _ /\ _ => split
      | |- _ => progress (simpl in *;simplify;propositional; auto with solve_taint)
      end.


    Lemma taint_safety_read_only_function':
      forall fuel1 fuel2 r r_acc gamma gamma' action st' env env' v,
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc true gamma action = (true, Some (gamma', st', v)) ->
      read_only_taint env ->
      taint_action int_fns fuel2 env action = Success (Some env') ->
      read_only_taint env' ->
      st' = r_acc.
    Proof.
      induction fuel1;
        intros fuel2 r r_acc gamma gamma' action st' env env' v
               Horaat Htaint Hsuccess; simpl in *; simplify; subst.
      destruct fuel2; [simpl in *; discriminate | ].
      destruct action; cbn in *; simplify_tupless; propositional;
        destruct_match_pairs; unfold res_opt_bind, get_fn_arg_and_body'', __debug__ in *; repeat solve_taint_safety_action IHfuel1; destruct_all_matches; simplify; repeat solve_taint_safety_read_only_action IHfuel1.
    Qed.


    Lemma taint_safety_read_only_function:
      forall fuel1 fuel2 r r_acc gamma gamma' action st' env v,
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc true gamma action = (true, Some (gamma', st', v)) ->
      taint_action int_fns fuel2 SortedRegEnv.empty action = Success (Some env) ->
      read_only_taint env ->
      st' = r_acc.
    Proof.
      intros. eapply taint_safety_read_only_function' with (env := SortedRegEnv.empty) in H; eauto.
      apply empty_taint_read_only.
    Qed.
  End ReadOnly.
End TaintSafety.

Section ReadOnlyFunction.
  Context (ext_sigma: ext_sigma_t).
  Context (int_fns: int_fn_env_t).
  Context (struct_defs: struct_env_t).

  Definition read_only_taintb (env: taint_env_t) : bool :=
    forallb (fun '(_, v) => negb (taint_write0 v|| taint_write1 v)) (SortedRegEnv.to_list env).

  Lemma read_only_taintb_iff:
    forall env,
    read_only_taintb env = true <->
    read_only_taint env.
  Proof.
    unfold read_only_taintb, read_only_taint. intros.
    rewrite forallb_forall.
    split.
    - intros. repeat destruct_match; subst; auto.
      rewrite<-SortedRegEnv.In_to_list in Heqo.
      specialize H with (1 := Heqo). destruct_match_pairs; simplify.
      rewrite Heqb in H. discriminate.
    - intros. destruct x. rewrite SortedRegEnv.In_to_list in H0.
      specialize (H r). simpl_match. destruct_matches_in_hyp H; auto.
  Qed.

  Lemma read_only_function_safety:
    forall fuel1 fuel2 fuel3 r r_acc gamma action env opt_res,
    oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc true gamma action = (true, opt_res) ->
    taint_action int_fns fuel2 SortedRegEnv.empty action = Success (Some env) ->
    read_only_taintb env = true ->
    action_contains_fail int_fns fuel3 action = Success false ->
    match opt_res with
    | Some (_, st', _) => st' = r_acc
    | None => False
    end.
  Proof.
    intros * Horaat Htaint Hread Hfail.
    repeat destruct_match; subst.
    - eapply taint_safety_read_only_function; eauto.
      apply read_only_taintb_iff. assumption.
    - eapply action_fail_safety; eauto.
  Qed.

  Lemma read_only_function_safety':
    forall fuel1 r r_acc gamma action env opt_res,
    oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc true gamma action = (true, opt_res) ->
    taint_action int_fns (safe_fuel int_fns (Datatypes.length int_fns) action)
                         SortedRegEnv.empty action = Success (Some env) ->
    read_only_taintb env = true ->
    action_contains_fail int_fns (safe_fuel int_fns (Datatypes.length int_fns) action)  action = Success false ->
    match opt_res with
    | Some (_, st', _) => st' = r_acc
    | None => False
    end.
  Proof.
    intros; eapply read_only_function_safety; eauto.
  Qed.

End ReadOnlyFunction.

Section TaintRec.
  Context (ext_sigma: ext_sigma_t).
  Context (int_fns: int_fn_env_t).
  Context (struct_defs: struct_env_t).

  Ltac solve_taint_action_rec_equiv' IH :=
    match goal with
    | |- exists env', Success (Some ?env) = Success (Some env') /\ _ =>
        exists env
    | |- _ /\ _ => split
    | |- ?env = merge_taint_env ?env taint_empty =>
        rewrite merge_taint_env_empty_r
    | H: taint_action _ _ _ _ = Success (Some _) |- _=>
        apply IH in H
    | H: ?f = Success (Some ?env) |- exists env', ?f = Success (Some env') /\ _ =>
        exists env; split; [assumption | ]
    | H1: taint_action_rec ?int_fns ?fuel ?action = _,
      H2: taint_action_rec ?int_fns ?fuel ?action = _ |- _ =>
        rewrite H1 in H2; clear H1; try discriminate
    | _ => progress (try autorewrite with rewrite_taints; repeat simpl_match; simplify; propositional)
    end.
  Create HintDb rewrite_taints.
  Hint Rewrite merge_taint_env_assoc : rewrite_taints.

  Lemma set_reg_taint_merge_read0:
    forall env idx ,
    set_reg_taint env idx set_taint_read0 = merge_taint_env env (set_reg_taint taint_empty idx set_taint_read0).
  Proof.
    unfold merge_taint_env, set_reg_taint; intros. unfold taint_empty in *.
    apply SortedRegEnv.env_ext. intros.
    rewrite SortedRegEnv.opt_get_mapV.
    rewrite SortedRegEnv.opt_get_zip_default.
    destruct_with_eqn (Nat.eqb idx reg); simplify; subst.
    - repeat rewrite SortedRegEnv.update_correct_eq.
      destruct_match; repeat rewrite SortedRegEnv.opt_get_empty; simpl;
      unfold set_taint_read0, merge_taints; simpl; repeat rewrite orb_false_r; repeat rewrite orb_true_r; auto.
    - repeat rewrite SortedRegEnv.update_correct_neq; auto.
      repeat rewrite SortedRegEnv.opt_get_empty; simpl.
      destruct_match; auto. rewrite merge_taints_empty_r. reflexivity.
  Qed.

  Lemma set_reg_taint_merge_read1:
    forall env idx ,
    set_reg_taint env idx set_taint_read1 = merge_taint_env env (set_reg_taint taint_empty idx set_taint_read1).
  Proof.
    unfold merge_taint_env, set_reg_taint; intros. unfold taint_empty in *.
    apply SortedRegEnv.env_ext. intros.
    rewrite SortedRegEnv.opt_get_mapV.
    rewrite SortedRegEnv.opt_get_zip_default.
    destruct_with_eqn (Nat.eqb idx reg); simplify; subst.
    - repeat rewrite SortedRegEnv.update_correct_eq.
      destruct_match; repeat rewrite SortedRegEnv.opt_get_empty; simpl;
      unfold set_taint_read1, merge_taints; simpl; repeat rewrite orb_false_r; repeat rewrite orb_true_r; auto.
    - repeat rewrite SortedRegEnv.update_correct_neq; auto.
      repeat rewrite SortedRegEnv.opt_get_empty; simpl.
      destruct_match; auto. rewrite merge_taints_empty_r. reflexivity.
  Qed.

  Lemma set_reg_taint_merge_write0:
    forall env1 env2 idx,
    set_reg_taint (merge_taint_env env1 env2) idx set_taint_write0 =
    merge_taint_env env1 (set_reg_taint env2 idx set_taint_write0).
  Proof.
    unfold set_reg_taint, merge_taint_env, set_taint_write0; intros.
    apply SortedRegEnv.env_ext; intros.
    destruct_with_eqn (Nat.eqb idx reg); simplify; subst;
      repeat rewrite SortedRegEnv.update_correct_eq; repeat rewrite SortedRegEnv.update_correct_neq by auto;
      repeat rewrite SortedRegEnv.opt_get_mapV;
      repeat rewrite SortedRegEnv.opt_get_zip_default;
      repeat rewrite SortedRegEnv.update_correct_eq; repeat rewrite SortedRegEnv.update_correct_neq by auto.
    - repeat destruct_match; unfold merge_taints; simpl; repeat rewrite orb_true_r; auto.
    - repeat destruct_match; unfold merge_taints; simpl; repeat rewrite orb_true_r; auto.
  Qed.

  Lemma set_reg_taint_merge_write1:
    forall env1 env2 idx,
    set_reg_taint (merge_taint_env env1 env2) idx set_taint_write1 =
    merge_taint_env env1 (set_reg_taint env2 idx set_taint_write1).
  Proof.
    unfold set_reg_taint, merge_taint_env, set_taint_write0; intros.
    apply SortedRegEnv.env_ext; intros.
    destruct_with_eqn (Nat.eqb idx reg); simplify; subst;
      repeat rewrite SortedRegEnv.update_correct_eq; repeat rewrite SortedRegEnv.update_correct_neq by auto;
      repeat rewrite SortedRegEnv.opt_get_mapV;
      repeat rewrite SortedRegEnv.opt_get_zip_default;
      repeat rewrite SortedRegEnv.update_correct_eq; repeat rewrite SortedRegEnv.update_correct_neq by auto.
    - repeat destruct_match; unfold merge_taints; simpl; repeat rewrite orb_true_r; auto.
    - repeat destruct_match; unfold merge_taints; simpl; repeat rewrite orb_true_r; auto.
  Qed.

  Lemma merge_taint_idem:
    forall env1 env2,
      merge_taint_env env1 (merge_taint_env env1 env2) = merge_taint_env env1 env2.
  Proof.
    unfold taint_env_le, merge_taint_env, get_reg_taint_default; intros.
    apply SortedRegEnv.env_ext; intros.
    repeat rewrite SortedRegEnv.opt_get_mapV;
    repeat rewrite SortedRegEnv.opt_get_zip_default.
    repeat rewrite SortedRegEnv.opt_get_mapV;
    repeat rewrite SortedRegEnv.opt_get_zip_default.
    unfold merge_taints in *.
    repeat destruct_match; simpl; auto.
    - f_equal. f_equal; rewrite orb_assoc; rewrite orb_diag; auto.
    - repeat rewrite orb_false_r. repeat rewrite orb_diag. auto.
  Qed.

  Lemma taint_action_rec_equiv':
    forall fuel action env1 env1',
    taint_action int_fns fuel env1 action = Success (Some env1') ->
    exists env2', taint_action_rec int_fns fuel action = Success (Some env2') /\
             env1' = merge_taint_env env1 env2'.
  Proof.
    induction fuel; intros action env1 env1'; simpl; [discriminate | ].
    destruct action; simpl in *; intros Htaint; unfold res_opt_bind, __debug__ in *;
      destruct_all_matches; repeat solve_taint_action_rec_equiv' IHfuel.
    - rewrite merge_taint_env_comm with (env1 := t0).
      rewrite merge_taint_env_comm with (env1 := t).
      repeat rewrite merge_taint_env_assoc.
      rewrite merge_taint_idem.
      rewrite merge_taint_env_comm with (env1 := t1).
      rewrite merge_taint_env_comm with (env1 := t0).
      repeat rewrite merge_taint_env_assoc.
      rewrite merge_taint_idem.
      reflexivity.
    - apply set_reg_taint_merge_read0.
    - apply set_reg_taint_merge_read1.
    - apply set_reg_taint_merge_write0.
    - apply set_reg_taint_merge_write1.
  Qed.

  Lemma taint_action_rec_equiv:
    forall fuel action env1',
    taint_action int_fns fuel SortedRegEnv.empty action = Success (Some env1') ->
    taint_action_rec int_fns fuel action = Success (Some env1').
  Proof.
    intros * Htaint1. apply taint_action_rec_equiv' in Htaint1. propositional.
    rewrite merge_taint_env_empty_l. assumption.
  Qed.

   Create HintDb solve_taint.

  Hint Immediate taint_env_corresponds_set_read0 : solve_taint.
  Hint Immediate taint_env_corresponds_set_read1 : solve_taint.
  Hint Immediate taint_env_corresponds_set_write0 : solve_taint.
  Hint Immediate taint_env_corresponds_set_write1 : solve_taint.
  Hint Immediate taint_env_corresponds_merge_l : solve_taint.
  Hint Immediate taint_env_corresponds_merge_r : solve_taint.
  Hint Immediate taint_env_le_refl : solve_taint.

  Hint Immediate taint_env_corresponds_to_state_update__empty: solve_taint.
  Hint Immediate taint_env_corresponds_to_state_update__unchanged: solve_taint.

  Lemma taint_env_corresponds_to_state_update_chain:
    forall r1 r2 r3 t1 t2,
    taint_env_corresponds_to_state_update r1 r2 t1 ->
    taint_env_corresponds_to_state_update r2 r3 t2 ->
    taint_env_corresponds_to_state_update r1 r3 (merge_taint_env t1 t2).
  Proof.
    unfold taint_env_corresponds_to_state_update, merge_taint_env.
    intros. specialize (H reg). specialize (H0 reg).
    rewrite SortedRegEnv.opt_get_mapV.
    rewrite SortedRegEnv.opt_get_zip_default.
    destruct_all_matches; simpl in *; destruct_with_eqn (taint_write0 t); destruct_with_eqn (taint_write1 t); simpl in *; repeat rewrite orb_true_r in *; try discriminate.
    congruence.
  Qed.

  Ltac solve_taint_safety_rec IH :=
    match goal with
    | H: oraat_interp_action _ _ _ _ _ _ true _ ?action = (true, _),
      H1: taint_action_rec _ _ ?action = _ |- _ =>
        apply IH with (2 := H1) in H; auto
    | H: oraat_interp_action _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
        match b with
        | true => fail
        | _ => let H' := fresh in
              assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
              rewrite H' in H; subst
        end
    | H1: taint_env_corresponds_to_state_update ?r1 ?r2 ?t1,
      H2: taint_env_corresponds_to_state_update ?r2 ?r3 ?t2 |- _ =>
        pose_fresh (taint_env_corresponds_to_state_update_chain  _ _ _ _ _ H1 H2)
    | H: _ && _ = true |- _ => rewrite andb_true_iff in H
    | |- _ => progress (simpl in *;simplify;propositional; auto with solve_taint)
    end.

  Lemma taint_safety_rec:
    forall fuel1 fuel2 r r_acc gamma action gamma' st' res env' ,
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc true
         gamma action = (true, Some (gamma', st', res)) ->
      taint_action_rec int_fns fuel2 action = Success (Some env') ->
      taint_env_corresponds_to_state_update r_acc st' env'.
  Proof.
    induction fuel1;
      intros fuel2 r r_acc gamma action gamma' st' res env'
             Horaat Htaint; simpl in *; simplify; subst.
    destruct fuel2; [simpl in *; discriminate | ].
    destruct action; cbn in *; simplify_tupless; propositional;
      destruct_match_pairs; unfold res_opt_bind, get_fn_arg_and_body'', __debug__, get_reg in *;
      destruct_all_matches; repeat solve_taint_safety_rec IHfuel1.
    + rewrite<-merge_taint_env_assoc. rewrite merge_taint_env_comm.
      apply taint_env_corresponds_merge_r. auto.
    + rewrite merge_taint_env_comm with (env1 := t0).
      rewrite<-merge_taint_env_assoc.
      apply taint_env_corresponds_merge_l. auto.
  Qed.

End TaintRec.

Section TaintEquivalence.
  Context (ext_sigma: ext_sigma_t).
  Context (int_fns: int_fn_env_t).
  Context (struct_defs: struct_env_t).

  Notation "st .[ idx ]" := (unsafe_get_reg st idx) (at level 1, format "st .[ idx ]").

  Definition taint_equiv_read0_state (st1 st2: state_t) (env: taint_env_t) : Prop :=
    forall reg,
    match SortedRegEnv.opt_get env reg with
    | Some t =>
        if taint_read0 t then
          st1.[reg] = st2.[reg]
        else True
    | None => True
    end.

  Lemma taint_equiv_read0_refl:
    forall st env,
      taint_equiv_read0_state st st env.
  Proof.
    unfold taint_equiv_read0_state.
    intros; destruct_all_matches.
  Qed.

  (* Definition taint_equiv_read1_state (st1 st2: state_t) (env: taint_env_t) : Prop := *)
  (*   forall reg, *)
  (*   match SortedRegEnv.opt_get env reg with *)
  (*   | Some t => *)
  (*       if taint_read1 t then *)
  (*         get_reg st1 reg = get_reg st2 reg *)
  (*       else True *)
  (*   | None => True *)
  (*   end. *)


  (* Definition taint_equiv_read_state (st1 st2: state_t) (env: taint_env_t) : Prop := *)
  (*   forall reg, *)
  (*   match SortedRegEnv.opt_get env reg with *)
  (*   | Some t => *)
  (*       if taint_read0 t || taint_read1 t then *)
  (*         get_reg st1 reg = get_reg st2 reg *)
  (*         (* match SortedRegEnv.opt_get st1 reg, SortedRegEnv.opt_get st2 reg with *) *)
  (*         (* | Some v1, Some v2 => v1 = v2 *) *)
  (*         (* | _, _ => False *) *)
  (*         (* end *) *)
  (*       else True *)
  (*   | None => True *)
  (*   end. *)

  Definition taint_equiv_acc_state (st1 st2: state_t) (env: taint_env_t) : Prop :=
    forall reg,
    match SortedRegEnv.opt_get env reg with
    | Some t =>
        if taint_read1 t || taint_write0 t || taint_write1 t then
          st1.[reg] = st2.[reg]
        else True
    | None => True
    end.

  (* Lemma taint_equiv_read1_state_merge_l: *)
  (*   forall r1 r2 env1 env2, *)
  (*   taint_equiv_read1_state r1 r2 (merge_taint_env env1 env2) -> *)
  (*   taint_equiv_read1_state r1 r2 env1. *)
  (* Proof. *)
  (*   unfold taint_equiv_read1_state, merge_taint_env. *)
  (*   intros. specialize (H reg). rewrite SortedRegEnv.opt_get_mapV in H. *)
  (*   rewrite SortedRegEnv.opt_get_zip_default in H. *)
  (*   destruct_all_matches; simpl in *; destruct_with_eqn (taint_read0 t); *)
  (*     destruct_with_eqn (taint_read1 t); simpl in *; try rewrite orb_true_r in *; discriminate. *)
  (* Qed. *)
  Lemma taint_equiv_read0_state_merge_l:
    forall r1 r2 env1 env2,
    taint_equiv_read0_state r1 r2 (merge_taint_env env1 env2) ->
    taint_equiv_read0_state r1 r2 env1.
  Proof.
    unfold taint_equiv_read0_state, merge_taint_env.
    intros. specialize (H reg). rewrite SortedRegEnv.opt_get_mapV in H.
    rewrite SortedRegEnv.opt_get_zip_default in H.
    destruct_all_matches; simpl in *; destruct_with_eqn (taint_read0 t);
      destruct_with_eqn (taint_read1 t); simpl in *; try rewrite orb_true_r in *; discriminate.
  Qed.

  Lemma taint_equiv_read0_state_merge_r:
    forall r1 r2 env1 env2,
    taint_equiv_read0_state r1 r2 (merge_taint_env env1 env2) ->
    taint_equiv_read0_state r1 r2 env2.
  Proof.
    unfold taint_equiv_read0_state, merge_taint_env.
    intros. specialize (H reg). rewrite SortedRegEnv.opt_get_mapV in H.
    rewrite SortedRegEnv.opt_get_zip_default in H.
    destruct_all_matches; simpl in *; destruct_with_eqn (taint_read0 t);
      destruct_with_eqn (taint_read1 t); simpl in *; repeat rewrite orb_true_r in *; simpl in *; try discriminate.
  Qed.
  (* Lemma taint_equiv_read1_state_merge_r: *)
  (*   forall r1 r2 env1 env2, *)
  (*   taint_equiv_read1_state r1 r2 (merge_taint_env env1 env2) -> *)
  (*   taint_equiv_read1_state r1 r2 env2. *)
  (* Proof. *)
  (*   unfold taint_equiv_read1_state, merge_taint_env. *)
  (*   intros. specialize (H reg). rewrite SortedRegEnv.opt_get_mapV in H. *)
  (*   rewrite SortedRegEnv.opt_get_zip_default in H. *)
  (*   destruct_all_matches; simpl in *; destruct_with_eqn (taint_read0 t); *)
  (*     destruct_with_eqn (taint_read1 t); simpl in *; repeat rewrite orb_true_r in *; simpl in *; try discriminate. *)
  (* Qed. *)


  Lemma taint_equiv_acc_state_merge_r:
    forall r1 r2 env1 env2,
    taint_equiv_acc_state r1 r2 (merge_taint_env env1 env2) ->
    taint_equiv_acc_state r1 r2 env2.
  Proof.
    unfold taint_equiv_acc_state, merge_taint_env.
    intros. specialize (H reg). rewrite SortedRegEnv.opt_get_mapV in H.
    rewrite SortedRegEnv.opt_get_zip_default in H.
    destruct_all_matches; simpl in *; destruct_with_eqn (taint_read0 t);
      destruct_with_eqn (taint_read1 t); simpl in *; repeat rewrite orb_true_r in *; simpl in *; repeat rewrite orb_false_iff in *; destruct t; try destruct t0; simpl in *; propositional; try discriminate.
  Qed.

  Lemma taint_equiv_acc_state_merge_l:
    forall r1 r2 env1 env2,
    taint_equiv_acc_state r1 r2 (merge_taint_env env1 env2) ->
    taint_equiv_acc_state r1 r2 env1.
  Proof.
    unfold taint_equiv_acc_state, merge_taint_env.
    intros. specialize (H reg). rewrite SortedRegEnv.opt_get_mapV in H.
    rewrite SortedRegEnv.opt_get_zip_default in H.
    destruct_all_matches; simpl in *; destruct_with_eqn (taint_read0 t);
      destruct_with_eqn (taint_read1 t); simpl in *; repeat rewrite orb_true_r in *; simpl in *; repeat rewrite orb_false_iff in *; destruct t; try destruct t0; simpl in *; propositional; try discriminate.
  Qed.


(* Lemma taint_equiv_acc_state_implies_read1_equiv: *)
(*   forall s1 s2 t, *)
(*   taint_equiv_acc_state s1 s2 t -> *)
(*   taint_equiv_read1_state s1 s2 t. *)
(* Proof. *)
(*   unfold taint_equiv_acc_state, taint_equiv_read1_state. intros. specialize (H reg). *)
(*   unfold get_reg. *)
(*   destruct_all_matches. *)
(*   rewrite Heqb in *. discriminate. *)
(* Qed. *)
Lemma taint_equiv_set_read0:
  forall st1 st2 reg,
  taint_equiv_acc_state st1 st2 (set_reg_taint taint_empty reg set_taint_read0).
Proof.
  unfold taint_equiv_acc_state. unfold set_reg_taint. intros. unfold taint_empty.
  destruct_with_eqn (Nat.eqb reg reg0); simplify.
  - rewrite SortedRegEnv.update_correct_eq; repeat rewrite SortedRegEnv.opt_get_empty; simpl; auto.
  - rewrite SortedRegEnv.update_correct_neq by auto.
    repeat rewrite SortedRegEnv.opt_get_empty; simpl; auto.
Qed.
  Lemma taint_equiv_set_read0':
    forall r1 r2 idx,
    taint_equiv_read0_state r1 r2 (set_reg_taint taint_empty idx set_taint_read0) ->
    success_or_default (r_get_reg r1 idx) [] = success_or_default (r_get_reg r2 idx) [].
  Proof.
    unfold taint_equiv_read0_state, set_reg_taint, unsafe_get_reg, r_get_reg, get_reg, taint_empty.
    intros. specialize (H idx). rewrite SortedRegEnv.update_correct_eq in H.
    rewrite SortedRegEnv.opt_get_empty in H. simpl in H.
    rewrite H. destruct_match; auto.
  Qed.
  (* Lemma taint_equiv_set_read1: *)
  (*   forall st1 st2 reg, *)
  (*   taint_equiv_read1_state st1 st2 (set_reg_taint taint_empty reg set_taint_read1) -> *)
  (*   taint_equiv_acc_state st1 st2 (set_reg_taint taint_empty reg set_taint_read1). *)
  (* Proof. *)
  (*   unfold taint_equiv_acc_state, taint_equiv_read1_state. unfold set_reg_taint, taint_empty. intros. *)
  (*   specialize (H reg). rewrite SortedRegEnv.update_correct_eq in H. rewrite SortedRegEnv.opt_get_empty in H. simpl in *. *)
  (*   destruct_with_eqn (Nat.eqb reg reg0); simplify. *)
  (*   - rewrite SortedRegEnv.update_correct_eq; repeat rewrite SortedRegEnv.opt_get_empty; simpl; auto. *)
  (*   - rewrite SortedRegEnv.update_correct_neq by auto. *)
  (*     repeat rewrite SortedRegEnv.opt_get_empty; simpl; auto. *)
  (* Qed. *)

  Lemma taint_equiv_set_read1':
    forall r1 r2 idx,
    taint_equiv_acc_state r1 r2 (set_reg_taint taint_empty idx set_taint_read1) ->
    success_or_default (r_get_reg r1 idx) [] = success_or_default (r_get_reg r2 idx) [].
  Proof.
    unfold taint_equiv_acc_state, set_reg_taint, unsafe_get_reg, r_get_reg, get_reg, taint_empty.
    intros. specialize (H idx). rewrite SortedRegEnv.update_correct_eq in H.
    rewrite SortedRegEnv.opt_get_empty in H. simpl in H.
    rewrite H. destruct_match; auto.
  Qed.
Lemma taint_equiv_acc_state_set_write0:
  forall st1 st2 v env idx,
  taint_equiv_acc_state st1 st2 env ->
  taint_equiv_acc_state (state_set st1 idx v) (state_set st2 idx v) (set_reg_taint env idx set_taint_write0).
Proof.
  unfold taint_equiv_acc_state, state_set, unsafe_get_reg, set_reg_taint, get_reg, r_get_reg.
  intros. specialize (H reg).
  destruct_with_eqn (Nat.eqb reg idx); simplify.
  - repeat rewrite SortedRegEnv.update_correct_eq.
    repeat destruct_match; simpl; repeat rewrite orb_true_r in *; simpl in *; auto.
  - repeat rewrite SortedRegEnv.update_correct_neq by auto.
    repeat destruct_match; auto.
Qed.
Lemma taint_equiv_acc_state_set_write1:
  forall st1 st2 v env idx,
  taint_equiv_acc_state st1 st2 env ->
  taint_equiv_acc_state (state_set st1 idx v) (state_set st2 idx v) (set_reg_taint env idx set_taint_write1).
Proof.
  unfold taint_equiv_acc_state, state_set, unsafe_get_reg, set_reg_taint, get_reg, r_get_reg.
  intros. specialize (H reg).
  destruct_with_eqn (Nat.eqb reg idx); simplify.
  - repeat rewrite SortedRegEnv.update_correct_eq.
    repeat destruct_match; simpl; repeat rewrite orb_true_r in *; simpl in *; auto.
  - repeat rewrite SortedRegEnv.update_correct_neq by auto.
    repeat destruct_match; auto.
Qed.

  Create HintDb solve_taint.

  Hint Immediate taint_env_corresponds_set_read0 : solve_taint.
  Hint Immediate taint_env_corresponds_set_read1 : solve_taint.
  Hint Immediate taint_env_corresponds_set_write0 : solve_taint.
  Hint Immediate taint_env_corresponds_set_write1 : solve_taint.
  Hint Immediate taint_env_corresponds_merge_l : solve_taint.
  Hint Immediate taint_env_corresponds_merge_r : solve_taint.
  Hint Immediate taint_env_le_refl : solve_taint.

  Hint Immediate taint_env_corresponds_to_state_update__empty: solve_taint.
  Hint Immediate taint_env_corresponds_to_state_update__unchanged: solve_taint.
  Hint Immediate taint_equiv_set_read0: solve_taint.
  Hint Immediate taint_equiv_set_read0': solve_taint.
  (* Hint Immediate taint_equiv_set_read1: solve_taint. *)
  Hint Immediate taint_equiv_set_read1': solve_taint.
  Hint Immediate taint_equiv_acc_state_set_write0 : solve_taint.
  Hint Immediate taint_equiv_acc_state_set_write1 : solve_taint.

(* Lemma step_taint_read1_preserved: *)
(*   forall r_acc1 r_acc2 st1 st2 env1 env2, *)
(*   taint_equiv_read1_state r_acc1 r_acc2 (merge_taint_env env1 env2) -> (* All read values are equal *) *)
(*   taint_env_corresponds_to_state_update r_acc1 st1 env1 -> (* st1 is only updated if env1 writes *) *)
(*   taint_env_corresponds_to_state_update r_acc2 st2 env1 -> (* st2 is only updated if env2 writes *) *)
(*   taint_equiv_acc_state st1 st2 env1 -> (* st1=st2 at everything read/written by env1 *) *)
(*   taint_equiv_read1_state st1 st2 env2. *)
(* Proof. *)
(*   unfold taint_equiv_read1_state, taint_env_corresponds_to_state_update, taint_equiv_acc_state. *)
(*   intros * Hequiv Hupdate1 Hupdate2  Hequiv' reg. *)
(*   specialize (Hequiv reg). specialize (Hupdate1 reg). specialize (Hupdate2 reg). specialize (Hequiv' reg). *)
(*   unfold merge_taint_env, get_reg in *. *)
(*   rewrite SortedRegEnv.opt_get_mapV in Hequiv. *)
(*   rewrite SortedRegEnv.opt_get_zip_default in Hequiv. *)
(*   destruct_match; auto. *)
(*   destruct_match; auto. *)
(*   destruct_all_matches; simpl in *; try congruence. *)
(*   - rewrite Heqb in *. rewrite orb_true_r in *. *)
(*     rewrite<-orb_assoc in Heqb0. rewrite Heqb1 in *. rewrite orb_true_r in *. discriminate. *)
(*   - rewrite Heqb in *. rewrite orb_true_r in *. discriminate. *)
(*   - rewrite Heqb in *. rewrite orb_true_r in *. discriminate. *)
(* Qed. *)

Lemma taint_equiv_merge:
  forall st1 st2 st1' st2' env1 env2,
  taint_equiv_acc_state st1 st2 env1 ->
  taint_equiv_acc_state st1' st2' env2 ->
  taint_env_corresponds_to_state_update st1 st1' env2 ->
  taint_env_corresponds_to_state_update st2 st2' env2 ->
  taint_equiv_acc_state st1' st2' (merge_taint_env env1 env2).
Proof.
  unfold taint_equiv_acc_state, taint_env_corresponds_to_state_update, merge_taint_env, merge_taints, unsafe_get_reg, get_reg, r_get_reg.
  intros. specialize (H reg). specialize (H0 reg). specialize (H1 reg). specialize (H2 reg).
  rewrite SortedRegEnv.opt_get_mapV.
  rewrite SortedRegEnv.opt_get_zip_default.
  destruct_all_matches; simpl in *; destruct t; try destruct t0; simpl in *.
  all: repeat match goal with
       | H: _ || _ = false |- _ =>
           rewrite orb_false_iff in H
       | _ => progress (simpl in *; propositional; try discriminate)
       end.
Qed.

Lemma taint_equiv_read0_set_write0:
 forall r1 r2 env idx,
 taint_equiv_read0_state r1 r2 (set_reg_taint env idx set_taint_write0) ->
 taint_equiv_read0_state r1 r2 env.
Proof.
  unfold taint_equiv_read0_state, set_reg_taint. intros.
  specialize (H reg).
  destruct_with_eqn (Nat.eqb reg idx); simplify.
  - rewrite SortedRegEnv.update_correct_eq in H. destruct_match; propositional.
  - rewrite SortedRegEnv.update_correct_neq in H by auto. destruct_match; propositional.
Qed.
Lemma taint_equiv_read0_set_write1:
 forall r1 r2 env idx,
 taint_equiv_read0_state r1 r2 (set_reg_taint env idx set_taint_write1) ->
 taint_equiv_read0_state r1 r2 env.
Proof.
  unfold taint_equiv_read0_state, set_reg_taint. intros.
  specialize (H reg).
  destruct_with_eqn (Nat.eqb reg idx); simplify.
  - rewrite SortedRegEnv.update_correct_eq in H. destruct_match; propositional.
  - rewrite SortedRegEnv.update_correct_neq in H by auto. destruct_match; propositional.
Qed.

Lemma taint_equiv_acc_set_write0:
 forall r1 r2 env idx,
 taint_equiv_acc_state r1 r2 (set_reg_taint env idx set_taint_write0) ->
 taint_equiv_acc_state r1 r2 env.
Proof.
  unfold taint_equiv_acc_state, set_reg_taint. intros.
  specialize (H reg).
  destruct_with_eqn (Nat.eqb reg idx); simplify.
  - rewrite SortedRegEnv.update_correct_eq in H. destruct_match; propositional; simpl in *.
    rewrite orb_true_r in *. simpl in *. destruct_match; auto.
  - rewrite SortedRegEnv.update_correct_neq in H by auto. destruct_match; propositional.
Qed.
Lemma taint_equiv_acc_set_write1:
 forall r1 r2 env idx,
 taint_equiv_acc_state r1 r2 (set_reg_taint env idx set_taint_write1) ->
 taint_equiv_acc_state r1 r2 env.
Proof.
  unfold taint_equiv_acc_state, set_reg_taint. intros.
  specialize (H reg).
  destruct_with_eqn (Nat.eqb reg idx); simplify.
  - rewrite SortedRegEnv.update_correct_eq in H. destruct_match; propositional; simpl in *.
    repeat rewrite orb_true_r in *. destruct_match ;auto.
  - rewrite SortedRegEnv.update_correct_neq in H by auto. destruct_match; propositional.
Qed.

Ltac solve_oraat_interp_action_taint_eq IH :=
  match goal with
  | H : oraat_interp_action _ _ _ _ _ _ true _ ?action = (true, Some(_, ?st', _)),
    H1: taint_action_rec _ _ ?action = Success (Some _) |- _ =>
      pose_fresh (taint_safety_rec _ _ _ _ _ _ _ _ _ _ _ _ _ H H1)
  | H: oraat_interp_action _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
      match b with
      | true => fail
      | _ => let H' := fresh in
            assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
            rewrite H' in H; subst
      end
  | H: taint_equiv_acc_state ?r1 ?r2 (merge_taint_env ?env1 ?env2) |- _ =>
      pose_fresh (taint_equiv_acc_state_merge_l _ _ _ _ H)
  | H: taint_equiv_acc_state ?r1 ?r2 (merge_taint_env ?env1 ?env2) |- _ =>
      pose_fresh (taint_equiv_acc_state_merge_r _ _ _ _ H)
  | H: taint_equiv_read0_state ?r1 ?r2 (merge_taint_env ?env1 ?env2) |- _ =>
      pose_fresh (taint_equiv_read0_state_merge_l _ _ _ _ H)
  | H: taint_equiv_read0_state ?r1 ?r2 (merge_taint_env ?env1 ?env2) |- _ =>
      pose_fresh (taint_equiv_read0_state_merge_r _ _ _ _ H)
  | H: _ && _ = true |- _ => rewrite andb_true_iff in H
  | H1: taint_equiv_acc_state ?st1 ?st2 ?env1,
    H2: taint_equiv_acc_state ?st1' ?st2' ?env2,
    H3: taint_env_corresponds_to_state_update ?st1 ?st1' ?env2,
    H4: taint_env_corresponds_to_state_update ?st2 ?st2' ?env2 |- _ =>
       pose_fresh (taint_equiv_merge _ _ _ _ _ _ H1 H2 H3 H4)
  | H : taint_equiv_acc_state ?r1 ?r2 (set_reg_taint ?env ?idx set_taint_write1) |- _ =>
      pose_fresh (taint_equiv_acc_set_write1 _ _ _ _ H)
  | H : taint_equiv_acc_state ?r1 ?r2 (set_reg_taint ?env ?idx set_taint_write0) |- _ =>
      pose_fresh (taint_equiv_acc_set_write0 _ _ _ _ H)
  | H : taint_equiv_read0_state ?r1 ?r2 (set_reg_taint ?env ?idx set_taint_write1) |- _ =>
      pose_fresh (taint_equiv_read0_set_write1 _ _ _ _ H)
  | H : taint_equiv_read0_state ?r1 ?r2 (set_reg_taint ?env ?idx set_taint_write0) |- _ =>
      pose_fresh (taint_equiv_read0_set_write0 _ _ _ _ H)
  | H1: oraat_interp_action _ _ _ _ ?r1 ?r_acc1 _ ?gamma ?action = (true, _),
    H2: oraat_interp_action _ _ _ _ ?r2 ?r_acc2 _ ?gamma ?action = (true, _),
    H3: taint_action_rec _ _ ?action = Success (Some ?taint_env),
    H4: taint_equiv_read0_state ?r1 ?r2 ?taint_env,
    H5: taint_equiv_acc_state ?r_acc1 ?r_acc2 ?taint_env
    |- _ =>
      eapply IH with (2 := H2) (3 := H3) (4 := H4) (5 := H5) in H1; clear H2
  | H1: oraat_interp_action _ _ _ _ ?r1 ?r_acc1 _ ?gamma ?action = (true, _),
    H3: taint_action_rec _ _ ?action = Success (Some ?taint_env),
    H4: taint_equiv_read0_state ?r1 ?r2 ?taint_env,
    H5: taint_equiv_acc_state ?r_acc1 ?r_acc2 ?taint_env,
    H2: oraat_interp_action _ _ _ _ ?r2 ?r_acc2 _ ?gamma ?action = (_, _)
    |- _ =>
      eapply IH with (5 := H2) (2 := H3) (3 := H4) (4 := H5) in H1
   | H: success_or_default (Success _) _ = _ |- _ => simpl in H
   | H: Datatypes.length _ = 1 |- _ => progress (rewrite H in *; simpl in *)
  | |- _ => progress (simpl; simplify; propositional; auto with solve_taint)
  end.

  Lemma oraat_interp_action_taint_eq':
    forall fuel1 fuel2 fuel3 r1 r2 r_acc1 r_acc2 safe1 safe2 gamma action opt_res1 opt_res2 taint_env,
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r1 r_acc1 safe1 gamma action = (true, opt_res1) ->
      oraat_interp_action ext_sigma int_fns struct_defs fuel2 r2 r_acc2 safe2 gamma action = (true, opt_res2) ->
      taint_action_rec int_fns fuel3 action = Success (Some taint_env) ->
      taint_equiv_read0_state r1 r2 taint_env ->
      taint_equiv_acc_state r_acc1 r_acc2 taint_env -> (* taint_equiv_read1 not enough for if branch *)
      match opt_res1, opt_res2 with
      | Some (gamma1', st1', v1), Some (gamma2', st2', v2) =>
          gamma1' = gamma2' /\ taint_equiv_acc_state st1' st2' taint_env /\ v1 = v2
      | None, None => True
      | _, _ => False
      end.
  Proof.
    induction fuel1; simpl in *; [discriminate | ].
    destruct fuel2; simpl in *; [discriminate | ].
    destruct fuel3; simpl in *; [discriminate | ].
    intros * Horaat1 Horaat2 Htaint Htaint_equiv_r Htaint_equiv_racc.
    destruct action; cbn; unfold res_opt_bind, get_fn_arg_and_body'', __debug__ in *; repeat solve_oraat_interp_action_taint_eq IHfuel1;
      destruct_all_matches; repeat solve_oraat_interp_action_taint_eq IHfuel1; congruence.
  Qed.

  Lemma oraat_interp_action_taint_eq:
    forall fuel1 fuel2 fuel3 r1 r2 r_acc1 r_acc2 safe1 safe2 gamma action opt_res1 opt_res2 taint_env,
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r1 r_acc1 safe1 gamma action = (true, opt_res1) ->
      oraat_interp_action ext_sigma int_fns struct_defs fuel2 r2 r_acc2 safe2 gamma action = (true, opt_res2) ->
      taint_action int_fns fuel3 SortedRegEnv.empty action = Success (Some taint_env) ->
      taint_equiv_read0_state r1 r2 taint_env ->
      taint_equiv_acc_state r_acc1 r_acc2 taint_env ->
      match opt_res1, opt_res2 with
      | Some (_, st1', v1), Some (_, st2', v2) =>
          taint_equiv_acc_state st1' st2' taint_env /\ v1 = v2
      | None, None => True
      | _, _ => False
      end.
  Proof.
    intros * Horaat1 Horaat2 Htaint Htaint_equivr Htaint_equiv_racc.
    eapply taint_action_rec_equiv in Htaint.
    eapply oraat_interp_action_taint_eq' with (2 := Horaat2) in Horaat1; eauto.
    destruct_all_matches; propositional.
  Qed.


End TaintEquivalence.
Ltac simplify_oraat_interp_action_safety :=
  match goal with
  | H: oraat_interp_action _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
      match b with
      | true => fail
      | _ => let H' := fresh in
            assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
            rewrite H' in H; subst
      end
  end.

Section TODO_ORAAT_MOVE.
  Context (ext_fns: ext_sigma_t).
  Context (int_fns: int_fn_env_t).
  Context (struct_defs: struct_env_t).

  Create HintDb solve_gamma.

  Definition gamma_vars_eq {A} {B} (gamma1: @varenv_t A) (gamma2: @varenv_t B) : Prop :=
    Forall2 (fun '(v1, _) '(v2, _) => v1 = v2) gamma1 gamma2.

  Lemma gamma_vars_eq_refl:
    forall {A} (gamma: @varenv_t A), gamma_vars_eq gamma gamma.
  Proof.
    consider @gamma_vars_eq. induction gamma.
    - constructor.
    - constructor; auto. destruct_match_pairs; propositional.
  Qed.
  Hint Immediate gamma_vars_eq_refl : solve_gamma.

  Lemma gamma_vars_eq_update:
    forall {A} (gamma: @varenv_t A) var v,
      is_success (varenv_lookup_var gamma var tt) = true ->
      gamma_vars_eq gamma (varenv_update gamma var v).
  Proof.
    consider @gamma_vars_eq. consider @varenv_update.
    induction gamma; simpl; intros * Hlookup.
    - discriminate.
    - destruct_match_pairs; subst. consider @varenv_lookup_var. simpl in *.
      destruct_match.
      + apply String.eqb_eq in Heqb. subst.
        constructor; auto. apply gamma_vars_eq_refl.
      + constructor; auto.
  Qed.

  Hint Immediate gamma_vars_eq_update : solve_gamma.

  Lemma gamma_vars_eq_trans:
    forall {A} {B} {C} (gamma1: @varenv_t A) (gamma2: @varenv_t B) (gamma3: @varenv_t C),
      gamma_vars_eq gamma1 gamma2 ->
      gamma_vars_eq gamma2 gamma3 ->
      gamma_vars_eq gamma1 gamma3.
  Proof.
    consider @gamma_vars_eq. induction gamma1; intros * Hgamma0 Hgamma1.
    - destruct gamma2; [ | inversions Hgamma0].
      destruct gamma3; [ | inversions Hgamma1].
      auto.
    - destruct gamma2; [inversions Hgamma0 | ].
      destruct gamma3; [inversions Hgamma1 | ].
      inversions Hgamma0. inversions Hgamma1.
      destruct_match_pairs; propositional.
      constructor; eauto.
  Qed.
  Hint Immediate gamma_vars_eq_trans: solve_gamma.
Lemma gamma_vars_eq_tl:
  forall {A} {B} {C} (gamma: @varenv_t A) (gamma': @varenv_t B) (gamma'': @varenv_t C) var v,
  gamma_vars_eq gamma gamma' ->
  gamma_vars_eq (varenv_bind gamma' var v) gamma'' ->
  gamma_vars_eq gamma (tl gamma'').
Proof.
  intros * Hsim0 Hsim1.
  consider @gamma_vars_eq. consider @varenv_bind.
  destruct gamma''; [ inversions Hsim1 | ]. simpl.
  inversions Hsim1. simpl. eapply gamma_vars_eq_trans; eauto.
Qed.
  Hint Immediate gamma_vars_eq_tl: solve_gamma.

  Lemma oraat_interp_action_gamma_vars_eq:
    forall fuel r r_acc is_safe gamma action gamma' st' v,
    oraat_interp_action ext_fns int_fns struct_defs fuel r r_acc is_safe gamma action = (true, Some (gamma', st', v)) ->
    gamma_vars_eq gamma gamma'.
  Proof.
    induction fuel; [ discriminate | ].
    intros * Horaat.
    destruct action; cbn in *; destruct_all_matches;
      repeat match goal with
             | |- _ => simplify_oraat_interp_action_safety
             | H: oraat_interp_action _ _ _ _ _ _ _ _ _ = (true, _) |- _ =>
                 apply IHfuel in H
             | H: _ && _ = true |- _ => rewrite andb_true_iff in H
             | |- _ => progress (propositional; simplify; eauto with solve_gamma)
             end.
    - eapply gamma_vars_eq_trans; eauto with solve_gamma.
  Qed.

End TODO_ORAAT_MOVE.

Module BoxSimCorrect.

  Import BoxSimAnalysis.

  Include BoxSimPreserved.

  Section BoxSimAnalysis.
    Context (int_fns: int_fn_env_t).
    Context (struct_defs: struct_env_t).
    Context (box_t: Type).
    Context {box_t_eq_dec: EqDec box_t}.
    Context (box_defs: list (box_t * box_def)).
    (* Context (box_fns: list (fn_name_t * (box_t * list ext_fn_t))). *)

    Notation RegsNotInBoxes := (@RegsNotInBoxes box_t).
    Notation BoxRegsUnique := (@BoxRegsUnique box_t).
    Notation BoxRegsDisjoint := (@BoxRegsDisjoint box_t).

    (* For all registers in the environment, there is no box that contains the register *)
    Lemma computable_RegsNotInBoxes_correct:
      forall env boxes,
      computable_RegsNotInBoxes env boxes = true ->
      RegsNotInBoxes env boxes.
    Proof.
      unfold computable_RegsNotInBoxes. unfold RegsNotInBoxes.
      intros * Hcompute * Hreg Hin_box Hin_def. rewrite forallb_forall in *. unfold RegsNotInBoxes.
      rewrite<-SortedRegEnv.In_to_list in Hreg.
      specialize (Hcompute _ Hreg). simpl in Hcompute. rewrite forallb_forall in *.
      specialize (Hcompute _ Hin_box). simpl in *. rewrite negb_true_iff in Hcompute.
      apply existsb_false_forall in Hcompute. rewrite forallb_forall in *. specialize (Hcompute _ Hin_def).
      unfold reg_t_beq in *. rewrite PeanoNat.Nat.eqb_refl in Hcompute. discriminate.
    Qed.

    Lemma computable_BoxRegsUnique_correct:
      forall boxes,
      computable_BoxRegsUnique boxes = true ->
      BoxRegsUnique boxes.
    Proof.
      unfold computable_BoxRegsUnique.
      intros * Hunique. unfold BoxRegsUnique. intros.
      eapply unique_correct in Hunique; eauto.
    Qed.

    Lemma computable_BoxRegsDisjoint_correct:
      forall boxes,
      computable_BoxRegsDisjoint boxes = true ->
      BoxRegsDisjoint boxes.
    Proof.
      unfold BoxRegsDisjoint. induction boxes; auto.
      simpl. intros. destruct_match_pairs; simplify.
      destruct_all_matches; auto.
      + split_cases. simplify. auto.
      + rewrite andb_true_iff in *. propositional. rewrite forallb_forall in *.
        split_cases; simplify; auto.
        * specialize H4 with (1 := H3). rewrite negb_true_iff in *.
          apply existsb_false_forall in H4. rewrite forallb_forall in *.
          specialize H4 with (1 := H0). rewrite negb_true_iff in *.
          apply existsb_false_forall in H4. rewrite forallb_forall in H4.
          consider reg_t_beq. specialize H4 with (1 := H2). rewrite PeanoNat.Nat.eqb_refl in *. discriminate.
        * specialize H4 with (1 := H2). rewrite negb_true_iff in *.
          apply existsb_false_forall in H4. rewrite forallb_forall in *.
          specialize H4 with (1 := H). rewrite negb_true_iff in *.
          apply existsb_false_forall in H4. rewrite forallb_forall in H4.
          consider reg_t_beq. specialize H4 with (1 := H3). rewrite PeanoNat.Nat.eqb_refl in *. discriminate.
    Qed.

  Lemma computable_WF_boxes_correct:
    forall boxes,
    computable_WF_boxes boxes  = true ->
    WF_boxes boxes.
  Proof.
    unfold computable_WF_boxes. intros. rewrite andb_true_iff in *. propositional.
    constructor.
    - apply computable_BoxRegsUnique_correct. auto.
    - apply computable_BoxRegsDisjoint_correct. auto.
  Qed.
Create HintDb solve_box_sim.
Lemma merge_sim_regs_comm:
  forall sim1 sim2,
  merge_sim_regs sim1 sim2 = merge_sim_regs sim2 sim1.
Proof.
  unfold merge_sim_regs.
  intros. apply SortedRegEnv.env_ext.
  intros. repeat rewrite SortedRegEnv.opt_get_mapV, SortedRegEnv.opt_get_zip_default.
  destruct_all_matches; rewrite andb_comm; auto.
Qed.

Lemma RegsNotInBoxes_merge_l:
  forall sim1 sim2 box_defs,
  RegsNotInBoxes sim1 box_defs ->
  RegsNotInBoxes (merge_sim_regs sim1 sim2) box_defs.
Proof.
  unfold RegsNotInBoxes, merge_sim_regs.
  intros * Hsim1 * Hget Hin_box Hreg.
  rewrite SortedRegEnv.opt_get_mapV in Hget.
  rewrite SortedRegEnv.opt_get_zip_default in Hget.
  destruct_all_matches; simplify; rewrite andb_true_iff in *; propositional; try discriminate.
  specialize Hsim1 with (1 := Heqo).
  eauto.
Qed.

Lemma RegsNotInBoxes_merge_r:
  forall sim1 sim2 box_defs,
  RegsNotInBoxes sim2 box_defs ->
  RegsNotInBoxes (merge_sim_regs sim1 sim2) box_defs.
Proof.
  intros. rewrite merge_sim_regs_comm. apply RegsNotInBoxes_merge_l. auto.
Qed.

Lemma RegsNotInBoxes_update:
  forall defs sim idx b,
  RegsNotInBoxes sim defs ->
  reg_in_box_defs defs idx = false ->
  RegsNotInBoxes (update_sim_reg' sim idx b) defs.
Proof.
  unfold RegsNotInBoxes.
  intros * Hsim Hreg * Hupdate HIn_box HIn_reg.
  consider @reg_in_box_defs.
  consider @update_sim_reg'.
  apply existsb_false_forall in Hreg.
  rewrite forallb_forall in Hreg.
  consider @update_sim_reg.
  consider reg_t_beq.
  destruct_with_eqn (Nat.eqb idx reg); simplify.
  - rewrite SortedRegEnv.update_correct_eq in Hupdate.
    specialize (Hreg def). rewrite negb_true_iff in Hreg.
    assert_pre_and_specialize Hreg.
    { apply in_map with (f := snd) in HIn_box. assumption. }
    apply existsb_false_forall in Hreg.
    rewrite forallb_forall in Hreg.
    specialize (Hreg _ HIn_reg). rewrite negb_true_iff in Hreg. simplify. auto.
  - rewrite SortedRegEnv.update_correct_neq in Hupdate by auto. eauto.
Qed.

Definition reg_sim_le sim1 sim2 : Prop :=
  (forall idx, SortedRegEnv.opt_get sim1 idx = Some true -> SortedRegEnv.opt_get sim2 idx = Some true).

Definition box_sim_le (sim1 sim2: list box_t) : Prop :=
  forall box, In box sim1 -> In box sim2.

Definition sim_state_le (sim1 sim2: sim_state_t) :=
  reg_sim_le sim1.(sim_regs) sim2.(sim_regs) /\
  box_sim_le sim1.(sim_boxes) sim2.(sim_boxes).

Lemma RegNotInBoxes_decreases_preserve:
  forall box_defs sim sim',
  RegsNotInBoxes sim box_defs ->
  reg_sim_le sim' sim ->
  RegsNotInBoxes sim' box_defs.
Proof.
  unfold RegsNotInBoxes in *. consider reg_sim_le.
  intros * Hsim Hdecrease.
  intros. apply Hdecrease in H. eauto.
Qed.
Lemma reg_sim_le_refl:
  forall st, reg_sim_le st st.
Proof.
  consider reg_sim_le; auto.
Qed.

Lemma box_sim_le_refl:
  forall st, box_sim_le st st.
Proof.
  consider box_sim_le. auto.
Qed.

Hint Immediate box_sim_le_refl: solve_box_sim.
Lemma sim_state_le_refl:
  forall st, sim_state_le st st.
Proof.
  consider sim_state_le.
  intros; split.
  - apply reg_sim_le_refl.
  - apply box_sim_le_refl.
Qed.
Lemma reg_sim_le_trans:
  forall sim1 sim2 sim3,
  reg_sim_le sim1 sim2 ->
  reg_sim_le sim2 sim3 ->
  reg_sim_le sim1 sim3.
Proof.
  consider reg_sim_le. intros.
  apply H0. apply H. auto.
Qed.

Lemma box_sim_le_trans:
  forall sim1 sim2 sim3,
  box_sim_le sim1 sim2 ->
  box_sim_le sim2 sim3 ->
  box_sim_le sim1 sim3.
Proof.
  consider box_sim_le. intros.
  apply H0. apply H. auto.
Qed.

Lemma sim_state_le_trans:
  forall sim1 sim2 sim3,
  sim_state_le sim1 sim2 ->
  sim_state_le sim2 sim3 ->
  sim_state_le sim1 sim3.
Proof.
  intros * Hsim0 Hsim1.
  consider sim_state_le. propositional. split.
  - eapply reg_sim_le_trans; eauto.
  - eapply box_sim_le_trans; eauto.
Qed.

Lemma sim_state_le_update_sim_reg_false:
  forall st idx,
  sim_state_le (update_sim_reg st idx false) st.
Proof.
  unfold sim_state_le, update_sim_reg. simpl. intros; split; eauto with solve_box_sim.
  - consider update_sim_reg'. consider reg_sim_le.
    intros. destruct_with_eqn (Nat.eqb idx idx0); simplify.
    + rewrite SortedRegEnv.update_correct_eq in H. bash_destruct H; auto.
    + rewrite SortedRegEnv.update_correct_neq in H by auto. auto.
Qed.

Hint Immediate sim_state_le_update_sim_reg_false : solve_box_sim.
Hint Immediate sim_state_le_trans: solve_box_sim.
Lemma sim_state_le_remove_box:
  forall st box,
  sim_state_le (remove_box st box) st.
Proof.
  consider sim_state_le. consider @remove_box. simpl. intros; split.
  - apply reg_sim_le_refl.
  - unfold box_sim_le. intros. rewrite filter_In in H. propositional.
Qed.


Hint Immediate RegsNotInBoxes_merge_l : solve_box_sim.
Hint Immediate RegsNotInBoxes_merge_r : solve_box_sim.
Hint Immediate RegsNotInBoxes_update: solve_box_sim.
Hint Immediate sim_state_le_refl: solve_box_sim.
Hint Immediate sim_state_le_remove_box : solve_box_sim.

Definition gamma_state_le (gamma1 gamma2: sim_gamma_t) : Prop :=
  Forall2 (fun '(var1,v1) '(var2,v2) =>
             var1 = var2 /\ (v1 = true -> v2 = true)
          ) gamma1 gamma2.

Lemma gamma_state_le_refl: forall gamma, gamma_state_le gamma gamma.
Proof.
  intros; consider gamma_state_le; induction gamma; eauto.
  constructor; auto. destruct_match_pairs; propositional.
Qed.

Lemma gamma_state_le_trans :
  forall (gamma1 gamma2 gamma3: sim_gamma_t),
  gamma_state_le gamma1 gamma2 ->
  gamma_state_le gamma2 gamma3 ->
  gamma_state_le gamma1 gamma3.
Proof.
  consider gamma_state_le.
  induction gamma1; intros * Hsim0 Hsim1.
  - destruct gamma2; [ | inversions Hsim0].
    destruct gamma3; [ | inversions Hsim1].
    constructor.
  - destruct gamma2; [ inversions Hsim0 | ].
    destruct gamma3; [ inversions Hsim1 | ].
    inversions Hsim0. inversions Hsim1.
    destruct_match_pairs; propositional.
    constructor; eauto.
Qed.

Hint Immediate gamma_state_le_trans: solve_box_sim.

Lemma gamma_state_le_update:
  forall st var v,
  varenv_lookup_var st var tt = Success v ->
  gamma_state_le (varenv_update st var false) st.
Proof.
  consider @varenv_lookup_var. consider @varenv_update. consider gamma_state_le.
  induction st; simpl; [ discriminate | ].
  intros *. destruct_match; subst. destruct_match; propositional; simplify.
  - apply String.eqb_eq in Heqb0. subst. constructor; [split_ands_in_goal; propositional; discriminate | ].
    apply gamma_state_le_refl.
  - constructor; propositional.
    eapply IHst; simpl_match; eauto.
Qed.

Hint Immediate gamma_state_le_refl: solve_box_sim.
Hint Immediate gamma_state_le_update: solve_box_sim.
Lemma gamma_state_le_tl:
  forall sim1 sim2 sim3 v b,
  gamma_state_le sim1 sim3 ->
  gamma_state_le sim2 (varenv_bind sim1 v b) ->
  gamma_state_le (tl sim2) sim3.
Proof.
  consider gamma_state_le. consider @varenv_bind.
  induction sim1; intros * Hsim0 Hsim1.
  - destruct sim3; [ | inversions Hsim0].
    destruct sim2; [ inversions Hsim1| ]. simpl.
    inversions Hsim1; auto.
  - destruct sim3; [ inversions Hsim0 | ].
    destruct sim2; [inversions Hsim1 | ].
    simpl.
    inversions Hsim1.
    inversions Hsim0.
    destruct sim2; [inversions H4 | ].
    inversions H4. destruct_match_pairs. propositional.
    constructor.
    + destruct_match_pairs; propositional.
    + eapply gamma_state_le_trans; eauto.
Qed.

Hint Immediate gamma_state_le_tl: solve_box_sim.

Lemma remove_tainted_action_decreases_sim':
  forall fuel int_fns box_defs box_fns sim_st sim_gamma action sim_gamma' sim_st',
  remove_tainted_action' int_fns box_defs box_fns fuel sim_st sim_gamma action = Success (Some(sim_gamma', sim_st')) ->
  gamma_state_le sim_gamma' sim_gamma /\
  sim_state_le sim_st' sim_st.
Proof.
  induction fuel; [discriminate | ].
  intros * Hremove. destruct action; cbn in *; unfold res_opt_bind, __debug__ in *; destruct_all_matches;
    repeat match goal with
    | H1: gamma_state_le ?g1 ?g2,
      H2: gamma_state_le ?g2 ?g3 |- _ =>
        pose_fresh (gamma_state_le_trans _ _ _ H1 H2)
    | H1: sim_state_le ?s1 ?s2,
      H2: sim_state_le ?s2 ?s3 |- _ =>
        pose_fresh (sim_state_le_trans _ _ _ H1 H2)
    | H: remove_tainted_action' _ _ _ _ _ _ ?action = Success (Some (_, _)) |- _ =>
        apply IHfuel in H
    | _ => progress (propositional; simplify; eauto with solve_box_sim)
    end.
  - split_ands_in_goal; eauto with solve_box_sim.
    eapply gamma_state_le_trans; eauto with solve_box_sim.
  - split_ands_in_goal; eauto with solve_box_sim.
    eapply sim_state_le_trans with (2 := Heqr1); eauto with solve_box_sim.
  - split_ands_in_goal; eauto with solve_box_sim.
    eapply sim_state_le_trans; eauto with solve_box_sim.
Qed.

Theorem remove_tainted_action_decreases_sim:
  forall fuel int_fns box_defs box_fns sim_st sim_gamma action sim_gamma' sim_st',
  remove_tainted_action int_fns box_defs box_fns fuel sim_st sim_gamma action = Success (sim_gamma', sim_st') ->
  gamma_state_le sim_gamma' sim_gamma /\
  sim_state_le sim_st' sim_st.
Proof.
  intros * Haction. consider remove_tainted_action. bash_destruct Haction; simplify.
  - eapply remove_tainted_action_decreases_sim'; eauto.
  - eauto with solve_box_sim.
Qed.

    Theorem analyze_preserves_RegsNotInBoxes:
      forall fuel1 box_defs box_fns ext_fn_sims init_reg_sims acc_reg_sims gamma_sims action
        int_fns gamma' sim' b,
      RegsNotInBoxes acc_reg_sims.(sim_regs) box_defs ->
      analyze_action int_fns box_defs box_fns ext_fn_sims init_reg_sims (* box_sims *) fuel1
          acc_reg_sims gamma_sims action = Success (Some (gamma', sim', b)) ->
      RegsNotInBoxes sim'.(sim_regs) box_defs.
    Proof.
      induction fuel1; [discriminate | ].
      intros * Hbox Hanalyze.

      destruct action; cbn in *; simplify; unfold res_opt_bind, opt_bind_to_res in *; unfold __debug__ in *; destruct_all_matches;
        repeat match goal with
        | H: RegsNotInBoxes (sim_regs ?sim) _,
          H1: analyze_action _ _ _ _ _ _ ?sim _ ?action = Success (Some (_, _, _)) |- _ =>
            apply IHfuel1 with (1 := H) in H1
        | |- _ => progress (simpl in *; simplify; propositional; eauto with solve_box_sim)
        end.
      - apply remove_tainted_action_decreases_sim in Heqr1.
        apply remove_tainted_action_decreases_sim in Heqr0.
        propositional.
        eapply RegNotInBoxes_decreases_preserve; eauto.
        destruct Heqr4. destruct Heqr3.
        eapply reg_sim_le_trans; eauto with solve_box_sim.
    Qed.

Hint Immediate analyze_preserves_RegsNotInBoxes: solve_box_sim.

    Theorem analyze_none_implies_fail:
      forall fuel1 box_defs box_fns ext_fn_sims init_reg_sims acc_reg_sims gamma_sims action
        sigma int_fns fuel2 r r_acc is_safe gamma res ,
      analyze_action int_fns box_defs box_fns ext_fn_sims init_reg_sims fuel1
          acc_reg_sims gamma_sims action = Success None ->
      oraat_interp_action sigma int_fns struct_defs fuel2 r r_acc is_safe gamma action = (true, Some res) ->
      False.
    Proof.
      induction fuel1; [discriminate | ].
      intros *. destruct fuel2; [ discriminate | ].
      intros Hanalyze Horaat.
      destruct action; cbn in *; simplify; unfold res_opt_bind, opt_bind_to_res in *; unfold __debug__ in *;
        destruct_all_matches;
        repeat match goal with
        | H: analyze_action _ _ _ _ _ _ _ _ ?action = Success None,
          H1: oraat_interp_action _ _ _ _ _ _ _ _ ?action = (true, Some _) |- _ =>
            apply IHfuel1 with (1 := H) in H1
        | H: oraat_interp_action _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
            match b with
            | true => fail
            | _ => let H' := fresh in
                  assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
                  rewrite H' in H; subst
            end
        | H: _ && _ = true |- _ => rewrite andb_true_iff in H
        | |- _ => progress (simpl in *; simplify; propositional)
        end.
    Qed.

    Definition reg_sim_state_prop (sims: SortedRegEnv.EnvT bool) (st1 st2: state_t) : Prop :=
      forall reg, SortedRegEnv.opt_get sims reg = Some true ->
             st1.[reg] = st2.[reg].

    Definition box_sim_state_prop (sims: list box_t) (st1 st2: state_t) : Prop :=
      Forall (fun b => match find (fun '(b2, _) => beq_dec b b2) box_defs with
                    | Some (_, def) => box_sim def st1 st2
                    | None => False
                    end) sims.

    Definition action_writes_regs_only (int_fns: int_fn_env_t) (action: action) (regs: list reg_t) : Prop :=
        exists fuel, match taint_action int_fns fuel taint_empty action with
                | Success (Some taint_env) =>
                    forall reg taint,
                    not (In reg regs) ->
                    SortedRegEnv.opt_get taint_env reg = Some taint ->
                    taint.(taint_write0) = false /\
                    taint.(taint_write1) = false
                | _ => False
                end.

  Definition compute_action_writes_regs_only (int_fns: int_fn_env_t) (a: action) (regs: list reg_t) :=
    match taint_action int_fns (safe_fuel' int_fns a) taint_empty a with
    | Success (Some taint_env) =>
        forallb (fun '(r, taint) =>
                   existsb (reg_t_beq r) regs ||
                   (negb (taint_write0 taint || taint_write1 taint))
                ) (SortedRegEnv.to_list taint_env)
    | _ => false
    end.

  Lemma compute_action_writes_regs_only_correct:
    forall a int_fns regs,
    compute_action_writes_regs_only int_fns a regs = true ->
    action_writes_regs_only int_fns a regs.
  Proof.
    consider compute_action_writes_regs_only.
    consider action_writes_regs_only.
    intros * Hcompute.
    exists (safe_fuel' int_fns0 a).
    bash_destruct Hcompute.
    intros * Hregs Htaint.
    unfold not in *.
    rewrite forallb_forall in Hcompute.
    rewrite SortedRegEnv.opt_get_find in Htaint.
    simplify. apply find_some in Heqo. consider reg_t_beq. propositional; simplify.
    specialize (Hcompute _ Heqo0). simpl in Hcompute.
    rewrite orb_true_iff in *. rewrite negb_true_iff in Hcompute. rewrite orb_false_iff in Hcompute.
    destruct Hcompute; auto.
    rewrite existsb_exists in H. propositional; simplify. contradiction.
  Qed.

    Definition function_preserves_box_sim
      (int_fns: int_fn_env_t) (struct_defs: struct_env_t)
      (* (valid_regs: list (reg_t * list bool)) (regs: list reg_t)  *)
      (box: box_def) (fn_spec: int_fn_spec_t)
      (sigmas : list ext_fn_t):=
      forall arg sigma1 sigma2 fuel1 fuel2  r1 r2 r_acc1 r_acc2 gamma1' gamma2' st1' st2' v1 v2,
      Forall (fun fn => forall v, sigma1 fn v = sigma2 fn v) sigmas ->
      oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 r_acc1 true
        (fn_gamma (fn_arg_name fn_spec) arg)
        (fn_body fn_spec) = (true, Some (gamma1', st1', v1)) ->
      oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 r_acc2 true
        (fn_gamma (fn_arg_name fn_spec) arg) (fn_body fn_spec) = (true, Some (gamma2', st2', v2)) ->
      box_sim box r1 r2 ->
      box_sim box r_acc1 r_acc2 ->
      v1 = v2 /\ box_sim box st1' st2'.


    Definition box_fn_preserves_prop
      (box_fns: list (fn_name_t * (box_t * list ext_fn_t))) : Prop :=
      Forall (fun '(fn, (box, ext_fns)) =>
                match lookup_int_fn int_fns fn tt with
                | Success (_, fn_spec) =>
                    match find (fun '(b2,_) => beq_dec box b2) box_defs with
                    | Some (_, def) => function_preserves_box_sim int_fns struct_defs def fn_spec ext_fns /\
                                      action_writes_regs_only int_fns fn_spec.(fn_body) (get_box_regs def)
                    | _ => False
                    end
                | _ => False
                end) box_fns.
    Section Forall3.
      Context {A B C: Type}.
      Inductive Forall3 (R: A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
        | Forall3_nil : Forall3 R [] [] []
        | Forall3_cons: forall (x: A) (y: B) (z: C) (xs: list A) (ys: list B) (zs: list C),
                        R x y z  -> Forall3 R xs ys zs -> Forall3 R (x::xs) (y:: ys) (z:: zs).
    End Forall3.

    Definition gamma_sim_correct (gamma1 gamma2: gamma_t) (sim: sim_gamma_t) : Prop :=
      Forall3 (fun '(var1,v1) '(var2, v2) '(var3, b) =>
                 var1 = var2 /\ var2 = var3 /\ (b = true -> v1 = v2)) gamma1 gamma2 sim.

    Lemma gamma_sim_correct_empty : gamma_sim_correct [] [] [] .
    Proof.
      constructor.
    Qed.

Lemma gamma_sim_correct_lookup:
  forall gamma1 gamma2 gamma_sim var,
    gamma_sim_correct gamma1 gamma2 gamma_sim ->
    varenv_lookup_var gamma_sim var tt = Success true ->
    varenv_lookup_var gamma1 var tt = varenv_lookup_var gamma2 var tt.
Proof.
  unfold gamma_sim_correct, varenv_lookup_var.
  induction gamma1; intros gamma2 gamma_sim var Hsim Hlookup.
  - destruct gamma2; [ | inversions Hsim]. destruct gamma_sim; [ | inversions Hsim].
    simpl in *. discriminate.
  - destruct gamma2; [ inversions Hsim | ].
    destruct gamma_sim; [ inversions Hsim | ].
    inversions Hsim. destruct_match_pairs; propositional. simpl in *.
    destruct_match; simplify.
    + apply String.eqb_eq in Heqb0. propositional.
    + eapply IHgamma1; eauto. simpl_match. auto.
Qed.
Lemma gamma_sim_correct_lookup':
  forall gamma1 gamma2 gamma_sim var,
    gamma_sim_correct gamma1 gamma2 gamma_sim ->
    varenv_lookup_var gamma_sim var tt = Success true ->
    success_or_default (varenv_lookup_var gamma1 var tt) [] = success_or_default (varenv_lookup_var gamma2 var tt) [].
Proof.
  intros. eapply gamma_sim_correct_lookup in H; eauto. rewrite_solve.
Qed.
Lemma gamma_sim_correct_varenv_update:
  forall gamma1 gamma2 sim v1 v2 var b,
  gamma_sim_correct gamma1 gamma2 sim ->
  match b with
  | true => v1 = v2
  | false => True
  end ->
  gamma_sim_correct (varenv_update gamma1 var v1) (varenv_update gamma2 var v2) (varenv_update sim var b).
Proof.
  unfold gamma_sim_correct, varenv_update.
  induction gamma1; intros * Hsim Hb.
  - destruct gamma2; [ | inversions Hsim]. destruct sim; [ | inversions Hsim].
    simpl in *. constructor; destruct b; split_ands_in_goal; propositional. discriminate.
  - destruct gamma2; [ inversions Hsim | ].
    destruct sim; [ inversions Hsim | ]. simpl.
    inversions Hsim.
    destruct_match_pairs. propositional.
    destruct_match.
    + apply String.eqb_eq in Heqb1. subst. constructor; auto. split_ands_in_goal; propositional.
    + constructor; auto.
Qed.
Lemma gamma_sim_correct_merge_l:
  forall gamma1 gamma2 new_gamma sim sim',
  gamma_sim_correct gamma1 gamma2 sim ->
  merge_sim_gamma new_gamma sim  = Success sim' ->
  gamma_sim_correct gamma1 gamma2 sim'.
Proof.
  unfold gamma_sim_correct, merge_sim_gamma.
  induction gamma1; intros * Hsim Hmerge.
  - destruct gamma2; [ | inversions Hsim]. destruct sim; [ | inversions Hsim].
    destruct new_gamma; [ | discriminate ].
    simplify. simpl in Heqr. simplify. simpl in *. simplify. constructor.
  - destruct gamma2; [ inversions Hsim | ].
    destruct sim; [ inversions Hsim | ]. simpl.
    simplify. destruct new_gamma; [discriminate | ]. simpl in *. simplify. simpl in *.
    inversions Hsim. destruct_match_pairs. propositional. simpl in *. simplify.
    apply String.eqb_eq in Heqb1. subst.
    constructor; auto.
    + split_ands_in_goal; propositional. rewrite andb_true_iff in H; propositional.
    + eapply IHgamma1 with (new_gamma := new_gamma); eauto. simpl_match; auto.
Qed.

Lemma gamma_sim_correct_merge_r:
  forall gamma1 gamma2 new_gamma sim sim',
  gamma_sim_correct gamma1 gamma2 sim ->
  merge_sim_gamma sim new_gamma = Success sim' ->
  gamma_sim_correct gamma1 gamma2 sim'.
Proof.
  unfold gamma_sim_correct, merge_sim_gamma.
  induction gamma1; intros * Hsim Hmerge.
  - destruct gamma2; [ | inversions Hsim]. destruct sim; [ | inversions Hsim].
    destruct new_gamma; [ | discriminate ].
    simplify. simpl in Heqr. simplify. simpl in *. simplify. constructor.
  - destruct gamma2; [ inversions Hsim | ].
    destruct sim; [ inversions Hsim | ]. simpl.
    simplify. destruct new_gamma; [discriminate | ]. simpl in *. simplify. simpl in *.
    inversions Hsim. destruct_match_pairs. propositional. simpl in *. simplify.
    apply String.eqb_eq in Heqb1. subst.
    constructor; auto.
    + split_ands_in_goal; propositional. rewrite andb_true_iff in H; propositional.
    + eapply IHgamma1 with (new_gamma := new_gamma); eauto. simpl_match; auto.
Qed.
Lemma reg_sim_state_prop_merge_r:
  forall sim sim' st1 st2,
  reg_sim_state_prop sim st1 st2 ->
  reg_sim_state_prop (merge_sim_regs sim sim') st1 st2.
Proof.
  unfold reg_sim_state_prop, merge_sim_regs.
  intros * Hsim reg Hget.
  rewrite SortedRegEnv.opt_get_mapV in Hget.
  rewrite SortedRegEnv.opt_get_zip_default in Hget.
  specialize (Hsim reg). bash_destruct Hget; simplify.
  rewrite andb_true_iff in Hget. propositional.
Qed.

Lemma reg_sim_state_prop_merge_l:
  forall sim sim' st1 st2,
  reg_sim_state_prop sim st1 st2 ->
  reg_sim_state_prop (merge_sim_regs sim' sim ) st1 st2.
Proof.
  unfold reg_sim_state_prop, merge_sim_regs.
  intros * Hsim reg Hget.
  rewrite SortedRegEnv.opt_get_mapV in Hget.
  rewrite SortedRegEnv.opt_get_zip_default in Hget.
  specialize (Hsim reg). bash_destruct Hget; simplify.
  rewrite andb_true_iff in Hget. propositional.
Qed.

Lemma ext_fn_eq:
  forall (sigma1 sigma2: ext_sigma_t) ext_fn_sims fn,
  Forall (fun f : ext_fn_t => forall v, sigma1 f v = sigma2 f v) ext_fn_sims ->
  existsb (Nat.eqb fn) ext_fn_sims = true ->
  sigma1 fn = sigma2 fn.
Proof.
  intros. apply existsb_exists in H0. propositional; simplify.
  rewrite Forall_forall in H.
  apply functional_extensionality. auto.
Qed.

Lemma ext_fn_eq':
  forall (sigma1 sigma2: ext_sigma_t) ext_fn_sims fn v,
  Forall (fun f : ext_fn_t => forall v, sigma1 f v = sigma2 f v) ext_fn_sims ->
  existsb (Nat.eqb fn) ext_fn_sims = true ->
  success_or_default (sigma1 fn v) [] = success_or_default (sigma2 fn v) [].
Proof.
  intros. apply ext_fn_eq with (2 := H0) in H. rewrite_solve.
Qed.

Lemma gamma_sim_correct_tl:
  forall gamma1 gamma2 sim,
  gamma_sim_correct gamma1 gamma2 sim ->
  gamma_sim_correct (tl gamma1) (tl gamma2) (tl sim).
Proof.
  unfold gamma_sim_correct. intros. inversions H; simpl; auto. constructor.
Qed.
Lemma gamma_sim_correct_bind:
  forall gamma1 gamma2 sim var v0 v1 b,
  gamma_sim_correct gamma1 gamma2 sim ->
  match b with
  | true => v0 = v1
  | false => True
  end ->
  gamma_sim_correct (varenv_bind gamma1 var v0) (varenv_bind gamma2 var v1) (varenv_bind sim var b).
Proof.
  unfold gamma_sim_correct. intros.
  constructor; auto. split_ands_in_goal; propositional.
Qed.
Lemma reg_sim_state_prop_update:
  forall sim st1 st2 idx b v0 v1,
  reg_sim_state_prop sim st1 st2 ->
  match b with
  | true => v0 = v1
  | false => True
  end ->
  reg_sim_state_prop (update_sim_reg' sim idx b) (state_set st1 idx v0) (state_set st2 idx v1).
Proof.
  unfold reg_sim_state_prop, update_sim_reg'.
  intros * Hsim Hb reg Hget.
  specialize (Hsim reg).
  destruct_with_eqn (Nat.eqb reg idx); simplify.
  - rewrite SortedRegEnv.update_correct_eq in *.
    repeat rewrite unsafe_get_reg_state_set_eq. destruct_all_matches.
  - rewrite SortedRegEnv.update_correct_neq in * by auto.
    repeat rewrite unsafe_get_reg_state_set_neq by auto. destruct_all_matches.
Qed.


Lemma box_sim_state_update_l:
  forall box st1 st2 idx v,
  box_sim box st1 st2 ->
  forallb (fun a : nat => negb (reg_t_beq idx a)) (get_box_regs box) = true ->
  box_sim box (state_set st1 idx v) st2.
Proof.
  intros * Hsim Hreg. destruct Hsim.
  rewrite forallb_forall in Hreg.
  constructor.
  - intros r Hin. specialize (pf_box_valid_sim0 _ Hin).
    rewrite unsafe_get_reg_state_set_neq; auto.
    unfold reg_t_beq in *.
    consider get_box_regs. specialize (Hreg r).
    assert_pre_and_specialize Hreg.
    { apply in_or_app. auto. }
    rewrite negb_true_iff in Hreg.
    apply PeanoNat.Nat.eqb_neq in Hreg. auto.
  - consider box_data_sim. intros.
    assert (idx <> reg).
    { apply existsb_exists in H0. propositional; simplify. consider get_box_regs.
      specialize (Hreg x).
      assert_pre_and_specialize Hreg;[ apply in_or_app; auto | ].
      rewrite negb_true_iff in Hreg.
      apply PeanoNat.Nat.eqb_neq in Hreg. auto.
    }
    rewrite unsafe_get_reg_state_set_neq by auto.
    apply pf_box_data_sim0; auto. apply Forall_forall.
    rewrite Forall_forall in H. intros. specialize (H _ H2). destruct_match_pairs; simplify.
    rewrite unsafe_get_reg_state_set_neq; auto. consider get_box_regs.
    specialize (Hreg r).
    assert_pre_and_specialize Hreg.
    { apply in_or_app. left. apply in_map with (f := fst) in H2. auto. }
    { rewrite negb_true_iff in *. apply PeanoNat.Nat.eqb_neq. auto. }
Qed.

Lemma box_sim_sym:
  forall box st1 st2,
  box_sim box st1 st2 -> box_sim box st2 st1.
Proof.
  intros * Hsim. destruct Hsim.
  constructor.
  - intros; symmetry; auto.
  - consider box_data_sim. intros. symmetry. apply pf_box_data_sim0; auto.
    apply Forall_forall. rewrite Forall_forall in H.
    intros. specialize (H _ H1). destruct_match_pairs; simplify.
    apply pf_box_valid_sim0.
    eapply in_map with (f := fst) in H1; eauto.
Qed.
Lemma box_sim_state_update_r:
  forall box st1 st2 idx v,
  box_sim box st1 st2 ->
  forallb (fun a : nat => negb (reg_t_beq idx a)) (get_box_regs box) = true ->
  box_sim box st1 (state_set st2 idx v).
Proof.
  intros. apply box_sim_sym.
  apply box_sim_state_update_l; auto.
  apply box_sim_sym. auto.
Qed.
Notation reg_in_box_defs := (@reg_in_box_defs box_t).
Notation reg_box_defs := (reg_box_defs box_defs).
Lemma box_sim_state_prop_state_set:
  forall box_sim st1 st2 idx v0 v1,
  box_sim_state_prop box_sim st1 st2 ->
  reg_in_box_defs reg_box_defs idx = false ->
  box_sim_state_prop box_sim (state_set st1 idx v0) (state_set st2 idx v1).
Proof.
  unfold box_sim_state_prop, reg_in_box_defs, reg_box_defs.
  intros * Hsim Hreg.
  rewrite map_map in Hreg.
  apply Forall_forall.
  rewrite Forall_forall in Hsim. intros box HIn. specialize Hsim with (1 := HIn).
  destruct_match; auto. destruct_match_pairs; subst.
  apply existsb_false_forall in Hreg.
  rewrite forallb_forall in Hreg.
  apply find_some in Heqo; propositional. rewrite beq_dec_iff in Heqo1. subst.
  specialize (Hreg ((fun x0 => snd (let '(box,def) := x0 in (box, get_box_regs def))) (b,b0))).
  specialize Hreg with (1 := in_map _ _ _ Heqo0).
  rewrite negb_true_iff in Hreg. simpl in Hreg.
  apply existsb_false_forall in Hreg.
  apply box_sim_state_update_l; auto.
  apply box_sim_state_update_r; auto.
Qed.
Lemma gamma_sim_correct_fn_gamma :
  forall var v0 v1 b,
  match b with
  | true => v0 = v1
  | false => True
  end ->
  gamma_sim_correct (fn_gamma var v0) (fn_gamma var v1) [(var,b)].
Proof.
  unfold gamma_sim_correct, fn_gamma.
  intros; constructor; [ | constructor]; split_ands_in_goal; propositional.
Qed.


Hint Immediate gamma_sim_correct_lookup' : solve_box_sim.
Hint Immediate gamma_sim_correct_varenv_update : solve_box_sim.
Hint Immediate gamma_sim_correct_merge_r : solve_box_sim.
Hint Immediate gamma_sim_correct_merge_l : solve_box_sim.
Hint Immediate reg_sim_state_prop_merge_r: solve_box_sim.
Hint Immediate reg_sim_state_prop_merge_l: solve_box_sim.
Hint Immediate ext_fn_eq': solve_box_sim.
Hint Immediate gamma_sim_correct_tl: solve_box_sim.
Hint Immediate gamma_sim_correct_bind: solve_box_sim.
Hint Immediate gamma_sim_correct_bind: solve_box_sim.
Hint Immediate reg_sim_state_prop_update: solve_box_sim.
Hint Immediate box_sim_state_prop_state_set: solve_box_sim.
Hint Immediate gamma_sim_correct_fn_gamma : solve_box_sim.

Lemma function_writes_regs_only_def:
  forall box_fns box n n0 exts fn fn_spec,
  box_fn_preserves_prop box_fns ->
  find (fun '(f, _) => Nat.eqb fn f) box_fns = Some (n, (box, exts)) ->
  lookup_int_fn int_fns fn tt = Success (n0, fn_spec) ->
  exists def, In (box,def) box_defs /\
         function_preserves_box_sim int_fns struct_defs def fn_spec exts /\
         action_writes_regs_only int_fns (fn_body fn_spec) (get_box_regs def).
Proof.
  intros * Hpreserves Hboxes Hlookup.
  apply find_some in Hboxes. propositional; simplify.
  consider box_fn_preserves_prop. rewrite Forall_forall in Hpreserves.
  specialize Hpreserves with (1 := Hboxes0). simplify.
  propositional. apply find_some in Heqo. rewrite beq_dec_iff in Heqo. propositional.
  eauto.
Qed.
Lemma function_preserves_reg_sim_state_prop':
  forall reg_sims r_acc1 r_acc2 st1' st2' box_defs box def
    sigma1 sigma2 int_fns struct_defs fuel1 fuel2 r1 r2 is_safe1 is_safe2 gamma1 gamma2 action gamma1' gamma2' v1' v2',
  reg_sim_state_prop reg_sims r_acc1 r_acc2 ->
  oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 r_acc1 is_safe1 gamma1 action = (true, Some (gamma1', st1', v1')) ->
  oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 r_acc2 is_safe2 gamma2 action = (true, Some (gamma2', st2', v2')) ->
  WF_boxes box_defs ->
  In (box,def) box_defs ->
  action_writes_regs_only int_fns (action) (get_box_regs def) ->
  RegsNotInBoxes reg_sims (map (fun '(box, def) => (box, get_box_regs def)) box_defs) ->
  reg_sim_state_prop reg_sims st1' st2'.
Proof.
  intros * Hsim Horaat1 Horaat2 Hwf_boxes Hbox Hupdate Hsim'.
  consider reg_sim_state_prop.
  intros reg Hget.
  consider action_writes_regs_only.
  assert (is_safe1 = true) by (eapply oraat_interp_action_is_safe_generalizes in Horaat1; eauto); subst.
  assert (is_safe2 = true) by (eapply oraat_interp_action_is_safe_generalizes in Horaat2; eauto); subst.
  specialize taint_safety_function with (1 := Horaat1) as Htaint1.
  specialize taint_safety_function with (1 := Horaat2) as Htaint2.
  propositional; simplify. consider @is_success_some.
  specialize (Htaint1 fuel). specialize (Htaint2 fuel). consider taint_empty. repeat simpl_match. propositional.
   unfold RegsNotInBoxes in *.
  specialize Hsim' with (1 := Hget) (box := box) (def := get_box_regs def).
  assert_pre_and_specialize Hsim'.
  { apply in_map with (f := (fun '(box0,def0) => (box0, get_box_regs def0))) in Hbox; auto. }
  specialize (Hupdate0) with (1 := Hsim').
  assert (no_writes_in_taint_set (Success (Some t)) reg  = true) as Hno_write.
  { unfold no_writes_in_taint_set. destruct_match; auto. specialize Hupdate0 with (1 := eq_refl); propositional.
    rewrite Hupdate1. rewrite Hupdate2. auto.
  }
  erewrite taint_set_to_prop_no_write' with (1 := Htaint1) by auto.
  erewrite taint_set_to_prop_no_write' with (1 := Htaint2) by auto.
  apply Hsim. auto.
Qed.

Lemma function_preserves_reg_sim_state_prop:
  forall reg_sims r_acc1 r_acc2 st1' st2' box box_fns fn n exts n0 fn_spec
    sigma1 sigma2 struct_defs fuel1 fuel2 r1 r2 is_safe1 is_safe2 gamma1 gamma2 gamma1' gamma2' v1' v2',
  reg_sim_state_prop reg_sims r_acc1 r_acc2 ->
  oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 r_acc1 is_safe1 gamma1 (fn_body fn_spec) = (true, Some (gamma1', st1', v1')) ->
  oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 r_acc2 is_safe2 gamma2 (fn_body fn_spec) = (true, Some (gamma2', st2', v2')) ->
  WF_boxes box_defs ->
  box_fn_preserves_prop box_fns ->
  find (fun '(f, _) => Nat.eqb fn f) box_fns = Some (n, (box, exts)) ->
  lookup_int_fn int_fns fn tt = Success (n0, fn_spec) ->
  (* In (box,def) box_defs -> *)
  (* action_writes_regs_only int_fns (action) (get_box_regs def) -> *)
  RegsNotInBoxes reg_sims (map (fun '(box, def) => (box, get_box_regs def)) box_defs) ->
  reg_sim_state_prop reg_sims st1' st2'.
Proof.
  intros * Hsim Horaat1 Horaat2 Hwf_boxes Hbox Hfns Hlookup Hupdate Hsim'.
  eapply function_writes_regs_only_def in Hlookup; eauto. propositional.
  eapply function_preserves_reg_sim_state_prop'; eauto.
Qed.
Hint Immediate function_preserves_reg_sim_state_prop: solve_box_sim.
Lemma box_sim_state_prop_le_preserved:
  forall sim1 sim2 r1 r2,
  box_sim_state_prop sim2 r1 r2 ->
  box_sim_le sim1 sim2 ->
  box_sim_state_prop sim1 r1 r2.
Proof.
  consider box_sim_state_prop. consider box_sim_le.
  intros * Hsim Hle.
  apply Forall_forall. rewrite Forall_forall in Hsim.
  intros * Hin. apply Hle in Hin. apply Hsim. auto.
Qed.
Hint Immediate box_sim_state_prop_le_preserved: solve_box_sim.
Hint Immediate box_sim_le_trans: solve_box_sim.
Lemma box_sim_state_prop_merge_sim_boxes_l:
  forall sim1 sim2 st1 st2,
  box_sim_state_prop sim1 st1 st2 ->
  box_sim_state_prop (merge_sim_boxes sim1 sim2) st1 st2.
Proof.
  consider box_sim_state_prop. consider @merge_sim_boxes.
  intros * Hsim.
  rewrite Forall_forall in Hsim.
  apply Forall_forall.
  intros * HIn. apply filter_In in HIn. propositional.
  eapply Hsim; eauto.
Qed.

Lemma box_sim_state_prop_merge_sim_boxes_r:
  forall sim1 sim2 st1 st2,
  box_sim_state_prop sim2 st1 st2 ->
  box_sim_state_prop (merge_sim_boxes sim1 sim2) st1 st2.
Proof.
  consider box_sim_state_prop. consider @merge_sim_boxes.
  intros * Hsim.
  rewrite Forall_forall in Hsim.
  apply Forall_forall.
  intros * HIn. apply filter_In in HIn. propositional.
  eapply Hsim; eauto.
  apply existsb_exists in HIn1. propositional.
  rewrite beq_dec_iff in HIn3. subst. auto.
Qed.

Hint Immediate box_sim_state_prop_merge_sim_boxes_r: solve_box_sim.
Hint Immediate box_sim_state_prop_merge_sim_boxes_l: solve_box_sim.
Lemma box_sim_le_merge_sim_boxes_l:
  forall sim1 sim2 sim3,
  box_sim_le sim1 sim3 ->
  box_sim_le (merge_sim_boxes sim1 sim2) sim3.
Proof.
  consider box_sim_le. consider @merge_sim_boxes.
  intros * Hsim * HIn.
  apply filter_In in HIn. propositional.
Qed.

Lemma box_sim_le_merge_sim_boxes_r:
  forall sim1 sim2 sim3,
  box_sim_le sim2 sim3 ->
  box_sim_le (merge_sim_boxes sim1 sim2) sim3.
Proof.
  consider box_sim_le. consider @merge_sim_boxes.
  intros * Hsim * HIn.
  apply filter_In in HIn. propositional.
  apply existsb_exists in HIn1. propositional. rewrite beq_dec_iff in HIn3. propositional.
Qed.

Hint Immediate box_sim_le_merge_sim_boxes_l: solve_box_sim.
Hint Immediate box_sim_le_merge_sim_boxes_r: solve_box_sim.
Lemma sim_state_le_implies_reg_sim_le:
  forall sim1 sim2,
  sim_state_le sim1 sim2 ->
  reg_sim_le (sim_regs sim1) (sim_regs sim2).
Proof.
  intros. destruct H. auto.
Qed.
Lemma sim_state_le_implies_box_sim_le:
  forall sim1 sim2,
  sim_state_le sim1 sim2 ->
  box_sim_le (sim_boxes sim1) (sim_boxes sim2).
Proof.
  intros. destruct H. auto.
Qed.

Hint Immediate sim_state_le_implies_reg_sim_le : solve_box_sim.
Hint Immediate box_sim_le_merge_sim_boxes_r: solve_box_sim.
Hint Immediate reg_sim_le_trans : solve_box_sim.
Lemma gamma_sim_correct_implies_var_eq2:
forall sim g1 g2 ,
  gamma_sim_correct g1 g2 sim ->
  gamma_vars_eq g2 sim.
Proof.
  consider gamma_sim_correct. consider @gamma_vars_eq.
  induction sim; intros * Hsim.
  - inversions Hsim; constructor.
  - inversions Hsim. destruct_match_pairs; propositional.
    constructor; eauto.
Qed.
Hint Immediate gamma_sim_correct_implies_var_eq2: solve_box_sim.
Lemma gamma_sim_correct_implies_var_eq1:
forall sim g1 g2 ,
  gamma_sim_correct g1 g2 sim ->
  gamma_vars_eq g1 sim.
Proof.
  consider gamma_sim_correct. consider @gamma_vars_eq.
  induction sim; intros * Hsim.
  - inversions Hsim; constructor.
  - inversions Hsim. destruct_match_pairs; propositional.
    constructor; eauto.
Qed.
Hint Immediate gamma_sim_correct_implies_var_eq1: solve_box_sim.
Lemma gamma_sim_correct_trans:
  forall gamma1 gamma2 gamma1' gamma2' gamma_sims',
  gamma_sim_correct gamma1 gamma1' gamma_sims' ->
  gamma_sim_correct gamma2 gamma2' gamma_sims' ->
  gamma_sim_correct gamma1 gamma2 gamma_sims' ->
  gamma_sim_correct gamma1' gamma2' gamma_sims'.
Proof.
  consider gamma_sim_correct. induction gamma1; intros * Hsim0 Hsim1 Hsim.
  - inversions Hsim0. inversions Hsim1. auto.
  - inversions Hsim0. inversions Hsim1. inversions Hsim.
    destruct_match_pairs; propositional.
    constructor; eauto. split_ands_in_goal; propositional.
Qed.

Hint Immediate gamma_sim_correct_trans: solve_box_sim.
Lemma gamma_sim_correct_le:
  forall gamma1 gamma2 sim sim',
  gamma_state_le sim' sim ->
  gamma_sim_correct gamma1 gamma2 sim ->
  gamma_sim_correct gamma1 gamma2 sim'.
Proof.
  consider gamma_sim_correct. consider gamma_state_le.
  induction gamma1; intros * Hle Hsim.
  - inversions Hsim. inversions Hle. constructor.
  - inversions Hsim. inversions Hle. destruct_match_pairs; propositional.
    constructor; eauto.
Qed.
Hint Immediate gamma_sim_correct_le: solve_box_sim.
Lemma reg_sim_le_state_prop:
  forall sim1 sim2 st1 st2,
  reg_sim_le sim2 sim1 ->
  reg_sim_state_prop sim1 st1 st2 ->
  reg_sim_state_prop sim2 st1 st2.
Proof.
  consider reg_sim_le. consider reg_sim_state_prop.
  intros * Hle Hsim.
  intros. apply Hle in H. eauto.
Qed.
Hint Immediate reg_sim_le_state_prop : solve_box_sim.
Lemma reg_sim_state_prop_trans:
  forall sim sim1 sim2 sim1' sim2',
    reg_sim_state_prop sim sim1 sim2 ->
    reg_sim_state_prop sim sim1 sim1' ->
    reg_sim_state_prop sim sim2 sim2'->
    reg_sim_state_prop sim sim1' sim2'.
Proof.
  consider reg_sim_state_prop. intros * Hsim0 Hsim1 Hsim2.
  intros * Hreg0.
  rewrite<-Hsim1 by auto. rewrite<-Hsim2 by auto. eauto.
Qed.
Hint Immediate reg_sim_state_prop_trans: solve_box_sim.
Lemma box_sim_le_state_prop:
  forall sim1 sim2 st1 st2,
  box_sim_le sim2 sim1 ->
  box_sim_state_prop sim1 st1 st2 ->
  box_sim_state_prop sim2 st1 st2.
Proof.
  consider box_sim_le. consider box_sim_state_prop.
  intros * Hle Hsim.
  rewrite Forall_forall in Hsim. rewrite Forall_forall. intros. apply Hle in H.
  eapply Hsim. auto.
Qed.
Hint Immediate box_sim_le_state_prop : solve_box_sim.
Lemma box_sim_trans:
  forall b st1 st2 st3,
  box_sim b st1 st2 ->
  box_sim b st2 st3 ->
  box_sim b st1 st3.
Proof.
  intros. inversions H. inversions H0. constructor.
  - intros. rewrite pf_box_valid_sim0 by auto. auto.
  - consider box_data_sim. intros.
    rewrite pf_box_data_sim0 by auto.
    apply pf_box_data_sim1; auto.
    rewrite Forall_forall.
    rewrite Forall_forall in H. intros. destruct_match_pairs. subst. specialize H with (1 := H1). destruct_match_pairs. simplify.
    symmetry. apply pf_box_valid_sim0. eapply in_map with (f := fst) in H1; eauto.
Qed.

Lemma box_sim_state_prop_trans:
  forall sim st1 st2 st1' st2',
  box_sim_state_prop sim st1 st2 ->
  box_sim_state_prop sim st1 st1' ->
  box_sim_state_prop sim st2 st2' ->
  box_sim_state_prop sim st1' st2'.
Proof.
  consider box_sim_state_prop. intros * Hsim0 Hsim1 Hsim2.
  rewrite Forall_forall in *.
  intros. specialize (Hsim0 _ H). specialize (Hsim1 _ H). specialize (Hsim2 _ H).
  simplify.
  eapply box_sim_trans; eauto.
  apply box_sim_sym.
  eapply box_sim_trans with (2 := Hsim1).
  apply box_sim_sym. assumption.
Qed.
Hint Immediate box_sim_state_prop_trans: solve_box_sim.

Lemma box_sim_le_remove_box:
  forall sim box ,
  box_sim_le (filter (fun box2 : box_t => negb (beq_dec box box2)) sim) sim.
Proof.
  consider box_sim_le. induction sim; intros; [ inversions H| ].
  simpl in *. destruct_all_matches.
  - inversions H; eauto.
  - rewrite negb_false_iff in Heqb. rewrite beq_dec_iff in Heqb. subst.
    eauto.
Qed.
Hint Immediate box_sim_le_remove_box : solve_box_sim.
Lemma function_preserves_box_sim_state_prop:
  forall box box_fns fn n exts n0 fn_spec,
  box_fn_preserves_prop box_fns ->
  find (fun '(f, _) => Nat.eqb fn f) box_fns = Some (n, (box, exts)) ->
  lookup_int_fn int_fns fn tt = Success (n0, fn_spec) ->
  exists def, In (box,def) box_defs /\
           function_preserves_box_sim int_fns struct_defs def fn_spec exts /\
           action_writes_regs_only int_fns (fn_body fn_spec) (get_box_regs def).
Proof.
  intros * Hfn_preserves Hfind Hlookup.
  consider box_fn_preserves_prop. rewrite Forall_forall in Hfn_preserves.
  apply find_some in Hfind. propositional. simplify.
  specialize Hfn_preserves with (1 := Hfind0). destruct_match_pairs; simplify; propositional.
  apply find_some in Heqo. propositional. rewrite beq_dec_iff in *. subst.
  eauto.
Qed.
Lemma function_action_writes_regs_only:
  forall box_sims r_acc1 r_acc2 st1' st2' box box_fns fn n exts n0 fn_spec
    sigma1 sigma2 fuel1 fuel2 r1 r2 is_safe1 is_safe2 gamma_var1 gamma_var2 gamma1' gamma2' v1' v2',
  box_sim_state_prop box_sims r1 r2 ->
  box_sim_state_prop box_sims r_acc1 r_acc2 ->
  oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 r_acc1 is_safe1 (fn_gamma (fn_arg_name fn_spec) gamma_var1) (fn_body fn_spec) = (true, Some (gamma1', st1', v1')) ->
  oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 r_acc2 is_safe2 (fn_gamma (fn_arg_name fn_spec) gamma_var2) (fn_body fn_spec) = (true, Some (gamma2', st2', v2')) ->
  WF_boxes box_defs ->
  box_fn_preserves_prop box_fns ->
  find (fun '(f, _) => Nat.eqb fn f) box_fns = Some (n, (box, exts)) ->
  lookup_int_fn int_fns fn tt = Success (n0, fn_spec) ->
  exists def, In (box,def) box_defs /\
           function_preserves_box_sim int_fns struct_defs def fn_spec exts /\
           action_writes_regs_only int_fns (fn_body fn_spec) (get_box_regs def).
Proof.
  intros * Hsim0 Hsim1 Horaat1 Horaat2 Hwf_boxes Hfn_preserves Hfind Hlookup.
  clear Horaat1 Horaat2.
  consider box_fn_preserves_prop. rewrite Forall_forall in Hfn_preserves.
  apply find_some in Hfind. propositional. simplify.
  specialize Hfn_preserves with (1 := Hfind0). destruct_match_pairs; simplify; propositional.
  apply find_some in Heqo. propositional. rewrite beq_dec_iff in *. subst.
  eauto.
Qed.

Lemma ext_fns_forall:
  forall ext_fn_sims fns (sigma1 sigma2: ext_sigma_t),
  forallb (fun f : nat => existsb (Nat.eqb f) ext_fn_sims) fns = true ->
  Forall (fun f : ext_fn_t => forall v : list bool, sigma1 f v = sigma2 f v) ext_fn_sims ->
  Forall (fun f : ext_fn_t => forall v : list bool, sigma1 f v = sigma2 f v) fns.
Proof.
  intros. rewrite forallb_forall in H. apply Forall_forall. rewrite Forall_forall in H0.
  intros. specialize H with (1 := H1). apply existsb_exists in H. propositional. simplify.
  eauto.
Qed.
Lemma box_sim_state_prop_implies:
  forall box def sim st1 st2,
  In box sim ->
  WF_boxes box_defs ->
  In (box, def) box_defs ->
  box_sim_state_prop sim st1 st2 ->
  box_sim def st1 st2.
Proof.
  consider box_sim_state_prop.
  intros * Hin_sim Hwf Hin_def Hsim.
  rewrite Forall_forall in Hsim.
  specialize Hsim with (1 := Hin_sim).
  destruct Hwf. unfold BoxRegsUnique in *.
  simplify. apply find_some in Heqo. propositional. rewrite beq_dec_iff in Heqo1. propositional.
  specialize WFBoxes_Unique0 with (1 := Hin_def) (2 := Heqo0). subst. assumption.
Qed.
Lemma box_sim_regs_unchanged:
  forall box st1 st2 st1' st2',
  box_sim box st1 st2 ->
  (forall reg, In reg (get_box_regs box) -> st1.[reg] = st1'.[reg]) ->
  (forall reg, In reg (get_box_regs box) -> st2.[reg] = st2'.[reg]) ->
  box_sim box st1' st2'.
Proof.
  intros * Hsim Hin1 Hin2. destruct Hsim.
  assert (forall r : reg_t, In r (map fst (box_valid_regs box)) -> st1'.[r] = st2'.[r]).
  - consider get_box_regs.
    intros. rewrite<-Hin1. rewrite<-Hin2. auto.
    all: apply in_or_app; auto.
  - constructor; auto.
    consider box_data_sim.
    intros Hvalid. propositional.
    specialize pf_box_data_sim0 with (2 := H0).
    apply existsb_exists in H0. propositional; simplify.
    consider get_box_regs.
    rewrite<-Hin1 by (apply in_or_app; auto). rewrite<-Hin2 by (apply in_or_app; auto).
    apply pf_box_data_sim0. rewrite Forall_forall.
    rewrite Forall_forall in Hvalid. intros. specialize Hvalid with (1 := H1). destruct_match_pairs; propositional.
    apply Hin1. apply in_or_app. left. apply in_map with (f := fst) in H1. auto.
Qed.
Lemma action_writes_regs_only_sim:
  forall int_fns def sigma fuel r st gamma action gamma' st' v' is_safe b0,
  action_writes_regs_only int_fns action (get_box_regs def) ->
  oraat_interp_action sigma int_fns struct_defs fuel r st is_safe gamma action =
            (true, Some (gamma', st', v')) ->
  (forall r : reg_t, In r (get_box_regs b0) -> ~In r (get_box_regs def) ) ->
  (forall reg : reg_t, In reg (get_box_regs b0) -> st.[reg] = st'.[reg]).
Proof.
  intros * Hwrites Horaat Hdisjoint.
  consider action_writes_regs_only. propositional. simplify.
  specialize Hdisjoint with (1 := H). specialize Hwrites0 with (1 := Hdisjoint).
  simplify_oraat_interp_action_safety. consider taint_empty.
  eapply taint_safety_function in Horaat; eauto with solve_taint.
  2: { erewrite Heqr0. eauto. }
  symmetry.
  eapply taint_set_to_prop_no_write'; eauto.  consider no_writes_in_taint_set. rewrite Heqr0.
  destruct_match; auto. specialize Hwrites0 with (1 := eq_refl); propositional.
  rewrite Hwrites1. rewrite Hwrites2. auto.
Qed.
Lemma pf_oraat2_action_writes_regs_box_sim_state_preserved:
  forall sims st1 st2 st1' st2' sigma1 fuel1 r1 gamma1 action gamma1' v1' sigma2 fuel2 r2 gamma2 gamma2' v2' def box,
  box_sim_state_prop sims st1 st2 ->
  oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 st1 true gamma1
             action = (true, Some (gamma1', st1', v1')) ->
  oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 st2 true gamma2
             action = (true, Some (gamma2', st2', v2')) ->
  In (box, def) box_defs ->
  In box sims ->
  WF_boxes box_defs ->
  action_writes_regs_only int_fns action (get_box_regs def) ->
  box_sim def st1' st2' ->
  box_sim_state_prop sims st1' st2'.
Proof.
  intros * Hsim Horaat1 Horaat2 Hin_box Hin_sim Hwf_box Hwrite Hsim_preserved.
  (* assert (Hsim_def: box_sim def st1 st2) by (eapply box_sim_state_prop_implies; eauto). *)
  consider box_sim_state_prop.
  rewrite Forall_forall. rewrite Forall_forall in Hsim. intros * Hsim'.
  specialize (Hsim _ Hsim'). simplify.
  apply find_some in Heqo. propositional. rewrite beq_dec_iff in Heqo1. subst.
  destruct Hwf_box.
  destruct_with_eqn (beq_dec box b).
  - rewrite beq_dec_iff in Heqb1. subst.
    unfold BoxRegsUnique. rewrite (WFBoxes_Unique0  _ _ _ Heqo0 Hin_box). assumption.
  - unfold BoxRegsDisjoint in *.
    specialize WFBoxes_Disjoint0 with (1 := Heqo0) (2 := Hin_box).
    rewrite beq_dec_false_iff in Heqb1.
    eapply box_sim_regs_unchanged; eauto.
    + eapply action_writes_regs_only_sim; eauto. unfold not in *; intros. apply Heqb1. symmetry. eauto.
    + eapply action_writes_regs_only_sim; eauto. unfold not in *; intros. apply Heqb1. symmetry. eauto.
Qed.
Lemma pf_action_writes_regs_only_box_sim_preserved:
  forall box_fns fn sims st1 st2 st1' st2' sigma1 fuel1 r1 gamma1' v1' sigma2 fuel2 r2 gamma2' v2' box n exts n0 fn_spec is_safe1 is_safe2 gamma_var ext_fn_sims,
  box_sim_state_prop sims r1 r2 ->
  box_sim_state_prop sims st1 st2 ->
  oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 st1 is_safe1 (fn_gamma (fn_arg_name fn_spec) gamma_var) (fn_body fn_spec) = (true, Some (gamma1', st1', v1')) ->
  oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 st2 is_safe2 (fn_gamma (fn_arg_name fn_spec) gamma_var) (fn_body fn_spec) = (true, Some (gamma2', st2', v2')) ->
  box_fn_preserves_prop box_fns ->
  find (fun '(f, _) => Nat.eqb fn f) box_fns = Some (n, (box, exts)) ->
  lookup_int_fn int_fns fn tt = Success (n0, fn_spec) ->
  existsb (beq_dec box) sims = true ->
  WF_boxes box_defs ->
  Forall (fun f : ext_fn_t => forall v : list bool, sigma1 f v = sigma2 f v) ext_fn_sims ->
  forallb (fun f : nat => existsb (Nat.eqb f) ext_fn_sims) exts = true ->
  box_sim_state_prop sims st1' st2' /\ v1' = v2'.
Proof.
  intros * Hsim0 Hsim1 Horaat1 Horaat2 Hpreserves Hfind Hlookup Hexists Hext_sims Hext_fns Hwf_boxes.
  eapply function_preserves_box_sim_state_prop in Hpreserves; eauto.
  propositional.
  apply existsb_exists in Hexists. propositional. rewrite beq_dec_iff in Hexists2. subst.
  repeat simplify_oraat_interp_action_safety.
  split.
  - eapply pf_oraat2_action_writes_regs_box_sim_state_preserved with (2 := Horaat1) (3 := Horaat2); eauto.
    consider function_preserves_box_sim.
    eapply Hpreserves0; eauto.
    + eapply ext_fns_forall; eauto.
    + eapply box_sim_state_prop_implies; eauto.
    + eapply box_sim_state_prop_implies; eauto.
  - consider function_preserves_box_sim.
    eapply Hpreserves0; eauto.
    + eapply ext_fns_forall; eauto.
    + eapply box_sim_state_prop_implies; eauto.
    + eapply box_sim_state_prop_implies; eauto.
Qed.
Lemma pf_writes_not_in_box_sim_preserved:
  forall box_fns fn sims st1 st2 st1' st2' sigma1 fuel1 r1 gamma1' v1' sigma2 fuel2 r2 gamma2' v2' box n exts n0 fn_spec is_safe1 is_safe2 gamma_var ,
  box_sim_state_prop sims r1 r2 ->
  box_sim_state_prop sims st1 st2 ->
  oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 st1 is_safe1 (fn_gamma (fn_arg_name fn_spec) gamma_var) (fn_body fn_spec) = (true, Some (gamma1', st1', v1')) ->
  oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 st2 is_safe2 (fn_gamma (fn_arg_name fn_spec) gamma_var) (fn_body fn_spec) = (true, Some (gamma2', st2', v2')) ->
  box_fn_preserves_prop box_fns ->
  find (fun '(f, _) => Nat.eqb fn f) box_fns = Some (n, (box, exts)) ->
  lookup_int_fn int_fns fn tt = Success (n0, fn_spec) ->
  existsb (beq_dec box) sims = false ->
  WF_boxes box_defs ->
  box_sim_state_prop sims st1' st2'.
Proof.
  intros * Hsim0 Hsim1 Horaat1 Horaat2 Hpreserves Hfind Hlookup Hexists Hwf_boxes.
  eapply function_preserves_box_sim_state_prop in Hpreserves; eauto.
  consider box_sim_state_prop.
  rewrite Forall_forall in *. intros * Hin.
  specialize (Hsim0 _ Hin). simplify.
  specialize (Hsim1 _ Hin). simplify.
  propositional.
  destruct Hwf_boxes. unfold BoxRegsDisjoint in *.
  apply find_some in Heqo0. propositional. rewrite beq_dec_iff in Heqo2. subst.
  specialize WFBoxes_Disjoint0 with (1 := Hpreserves1) (2 := Heqo1).
  apply existsb_false_forall in Hexists. rewrite forallb_forall in Hexists.
  specialize Hexists with (1 := Hin). rewrite negb_true_iff in Hexists. rewrite beq_dec_false_iff in Hexists.
  eapply box_sim_regs_unchanged; eauto.
  + eapply action_writes_regs_only_sim; eauto.
  + eapply action_writes_regs_only_sim; eauto.
Qed.

Lemma pf_writes_filter_box_sim_preserved:
  forall box_fns fn sims st1 st2 st1' st2' sigma1 fuel1 r1 gamma1' v1' sigma2 fuel2 r2 gamma2' v2' box n exts n0 fn_spec is_safe1 is_safe2 gamma_var1 gamma_var2 ,
  box_sim_state_prop sims r1 r2 ->
  box_sim_state_prop sims st1 st2 ->
  oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 st1 is_safe1 (fn_gamma (fn_arg_name fn_spec) gamma_var1) (fn_body fn_spec) = (true, Some (gamma1', st1', v1')) ->
  oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 st2 is_safe2 (fn_gamma (fn_arg_name fn_spec) gamma_var2) (fn_body fn_spec) = (true, Some (gamma2', st2', v2')) ->
  box_fn_preserves_prop box_fns ->
  find (fun '(f, _) => Nat.eqb fn f) box_fns = Some (n, (box, exts)) ->
  lookup_int_fn int_fns fn tt = Success (n0, fn_spec) ->
  (* existsb (beq_dec box) sims = false -> *)
  WF_boxes box_defs ->
  box_sim_state_prop (filter (fun box2 : box_t => negb (beq_dec box box2)) sims) st1' st2'.
Proof.
  intros * Hsim0 Hsim1 Horaat1 Horaat2 Hpreserves Hfind Hlookup (* Hexists *) Hwf_boxes.
  eapply function_preserves_box_sim_state_prop in Hpreserves; eauto. propositional.

  consider box_sim_state_prop.
  rewrite Forall_forall in *. intros * Hin.
  propositional.
  apply filter_In in Hin. propositional. specialize (Hsim0 _ Hin0). specialize (Hsim1 _ Hin0). simplify.
  rewrite negb_true_iff in Hin1. rewrite beq_dec_false_iff in Hin1.
  destruct Hwf_boxes. unfold BoxRegsDisjoint in *.
  apply find_some in Heqo. propositional. rewrite beq_dec_iff in Heqo1. subst.
  specialize WFBoxes_Disjoint0 with (1 := Hpreserves1) (2 := Heqo0).
  eapply box_sim_regs_unchanged; eauto.
  + eapply action_writes_regs_only_sim; eauto.
  + eapply action_writes_regs_only_sim; eauto.
Qed.
Lemma gamma_sim_correct_refl:
  forall gamma sim_gamma,
  gamma_vars_eq gamma sim_gamma ->
  gamma_sim_correct gamma gamma sim_gamma.
Proof.
  consider @gamma_vars_eq. consider gamma_sim_correct.
  induction gamma; intros.
  - inversions H. constructor.
  - inversions H. destruct_match_pairs; simplify.
    constructor; auto.
Qed.

Hint Immediate gamma_sim_correct_refl: solve_box_sim.
Lemma reg_sim_state_prop_refl:
  forall sim (st: state_t),
  reg_sim_state_prop sim st st.
Proof.
  intros. consider reg_sim_state_prop. auto.
Qed.
Hint Immediate reg_sim_state_prop_refl: solve_box_sim.

Definition ValidBoxSims (boxes: list box_t) : Prop :=
  Forall (fun b => exists def, In (b,def) box_defs) boxes.
Lemma box_sim_state_prop_refl:
  forall sim (st: state_t),
  ValidBoxSims sim ->
  box_sim_state_prop sim st st.
Proof.
  consider ValidBoxSims. consider box_sim_state_prop.
  intros. rewrite Forall_forall in *.
  intros * Hin. specialize (H _ Hin). propositional.
  destruct_match; destruct_match_pairs; subst.
  - constructor; auto. unfold box_data_sim. auto.
  - eapply find_none in Heqo; eauto. destruct_match_pairs; simplify.
    rewrite beq_dec_false_iff in Heqo. contradiction.
Qed.
Hint Immediate box_sim_state_prop_refl: solve_box_sim.

Lemma remove_tainted_action_none_correct:
  forall fuel1 fuel2 box_fns sigma sim_st sim_gamma action r r_acc is_safe gamma opt,
  remove_tainted_action' int_fns reg_box_defs box_fns fuel1 sim_st sim_gamma action = Success None ->
  oraat_interp_action sigma int_fns struct_defs fuel2 r r_acc is_safe gamma action = (true, opt) ->
  opt = None.
Proof.
  induction fuel1; [discriminate | ].
  destruct fuel2; [discriminate | ].
  intros * Hremove Horaat.
  destruct action; cbn in *; unfold res_opt_bind in *; simplify; auto.
  destruct_all_matches; simplify.
  all: destruct_all_matches; repeat match goal with
       | H: remove_tainted_action' _ _ _ _ _ _ ?action = Success None,
         H1: oraat_interp_action _ _ _ _ _ _ _ _ ?action = (true, _) |- _ =>
         eapply IHfuel1 with (2 := H1) in H; subst
       | H: _ && _ = true |- _ => rewrite andb_true_iff in H
       | |- _ => simplify_oraat_interp_action_safety
       | |- _ => progress (simpl in *;simplify;propositional; eauto with solve_box_sim; try congruence)
       end.
Qed.
Lemma gamma_sim_correct_varenv_update_false:
  forall gamma g sim_gamma s1 var l,
  is_success (varenv_lookup_var g var tt) = true ->
  gamma_sim_correct gamma g s1 ->
  gamma_vars_eq gamma g ->
  gamma_vars_eq gamma sim_gamma ->
  gamma_state_le s1 sim_gamma ->
  gamma_sim_correct gamma (varenv_update g var l) (varenv_update s1 var false).
Proof.
  unfold gamma_vars_eq, gamma_state_le, gamma_sim_correct.
  consider @varenv_update. consider @varenv_lookup_var.
  induction gamma; intros * Hvar Hsim Heq1 Heq2 Hle.
  - inversions Hsim. inversions Hle. simpl in *. discriminate.
  - inversions Heq1. inversions Heq2. inversions Hle. inversions Hsim. destruct_match_pairs; propositional.
    simpl in *. destruct_match.
    + apply String.eqb_eq in Heqb1. subst. constructor; split_ands_in_goal; propositional; discriminate.
    + constructor; simpl in *; eauto.
Qed.
Hint Immediate gamma_sim_correct_varenv_update_false: solve_box_sim.
Lemma box_sim_state_prop_implies_valid_box_sim:
  forall bs st1 st2,
  box_sim_state_prop bs st1 st2  ->
  ValidBoxSims bs.
Proof.
  unfold box_sim_state_prop. unfold ValidBoxSims. intros.
  rewrite Forall_forall. rewrite Forall_forall in H. intros.
  specialize H with (1 := H0). simplify. apply find_some in Heqo. propositional; eauto. rewrite beq_dec_iff in Heqo1.
  subst. eauto.
Qed.
Lemma gamma_state_le_implies_gamma_var_eq:
  forall s1 s2,
  gamma_state_le s1 s2 ->
  gamma_vars_eq s1 s2.
Proof.
  consider gamma_state_le. consider @gamma_vars_eq.
  intros.
  eapply Forall2_impl; eauto. intros; destruct_match_pairs; propositional.
Qed.
Lemma gamma_sim_correct_sym:
  forall sim g1 g2 ,
  gamma_sim_correct g1 g2 sim ->
  gamma_sim_correct g2 g1 sim.
Proof.
  consider gamma_sim_correct.
  induction sim; intros * Hsim.
  - inversions Hsim. constructor.
  - inversions Hsim. destruct_match_pairs; propositional. constructor; eauto.
    split_ands_in_goal; propositional.
Qed.
Hint Immediate gamma_sim_correct_sym: solve_box_sim.
Lemma reg_sim_state_prop_sym:
  forall sim g1 g2 ,
  reg_sim_state_prop sim g1 g2 ->
  reg_sim_state_prop sim g2 g1 .
Proof.
  consider reg_sim_state_prop.
  intros * Hsim; simpl in *.
  intros; symmetry; auto.
Qed.
Hint Immediate reg_sim_state_prop_sym: solve_box_sim.
Lemma box_sim_state_prop_sym:
  forall sim g1 g2 ,
  box_sim_state_prop sim g1 g2 ->
  box_sim_state_prop sim g2 g1 .
Proof.
  consider box_sim_state_prop.
  induction sim; intros * Hsim.
  - constructor.
  - inversions Hsim. simplify. constructor; eauto.
    simpl_match. apply box_sim_sym. auto.
Qed.
Hint Immediate box_sim_state_prop_sym: solve_box_sim.
Lemma ValidBoxSims_le:
  forall sim sim',
  ValidBoxSims sim ->
  box_sim_le sim' sim ->
  ValidBoxSims sim'.
Proof.
  consider ValidBoxSims. consider box_sim_le.
  intros * Hsim Hle.
  rewrite Forall_forall. rewrite Forall_forall in *. propositional.
Qed.
Lemma gamma_vars_eq_sym:
  forall {A} (g1 g2: @varenv_t A),
  gamma_vars_eq g1 g2 ->
  gamma_vars_eq g2 g1.
Proof.
  consider @gamma_vars_eq.
  induction g1; intros.
  - inversions H. constructor.
  - inversions H. destruct_match_pairs; propositional.
Qed.
Hint Immediate gamma_vars_eq_sym : solve_box_sim.
Lemma gamma_vars_eq_varenv_bind:
  forall {A B} (g1: @varenv_t A) (g2: @varenv_t B) var v0 v1,
  gamma_vars_eq g1 g2 ->
  gamma_vars_eq (varenv_bind g1 var v0) (varenv_bind g2 var v1).
Proof.
  consider @gamma_vars_eq. consider @varenv_bind.
  intros; constructor; auto.
Qed.
Hint Immediate gamma_vars_eq_varenv_bind : solve_box_sim.
Lemma gamma_state_le_bind:
  forall sim1 sim2 v b,
  gamma_state_le sim2 (varenv_bind sim1 v b) ->
  gamma_state_le (tl sim2) sim1.
Proof.
  intros. eapply gamma_state_le_tl; eauto with solve_box_sim.
Qed.
Lemma reg_sim_state_prop_update_false':
  forall sim s1 s2 idx v,
  reg_sim_state_prop sim s1 s2 ->
  reg_sim_state_prop (update_sim_reg' sim idx false) s1 (state_set s2 idx v).
Proof.
  consider reg_sim_state_prop. consider @update_sim_reg'.
  intros * Hsim *  Hget. destruct_with_eqn (Nat.eqb reg idx); simplify.
  + rewrite SortedRegEnv.update_correct_eq in Hget. simplify.
  + rewrite SortedRegEnv.update_correct_neq in Hget by auto.
    rewrite unsafe_get_reg_state_set_neq by auto. auto.
Qed.
Hint Immediate reg_sim_state_prop_update_false' : solve_box_sim.
Lemma box_sim_state_prop_state_set_r:
  forall (box_sim : list box_t) (st1 st2 : state_t) (idx : reg_t) (v1 : Bits.vect_t),
  box_sim_state_prop box_sim st1 st2 ->
  reg_in_box_defs reg_box_defs idx = false ->
  box_sim_state_prop box_sim st1 (state_set st2 idx v1).
Proof.
  unfold box_sim_state_prop, reg_in_box_defs, reg_box_defs.
  intros * Hsim Hreg.
  rewrite map_map in Hreg.
  apply Forall_forall.
  rewrite Forall_forall in Hsim. intros box HIn. specialize Hsim with (1 := HIn).
  destruct_match; auto. destruct_match_pairs; subst.
  apply existsb_false_forall in Hreg.
  rewrite forallb_forall in Hreg.
  apply find_some in Heqo; propositional. rewrite beq_dec_iff in Heqo1. subst.
  specialize (Hreg ((fun x0 => snd (let '(box,def) := x0 in (box, get_box_regs def))) (b,b0))).
  specialize Hreg with (1 := in_map _ _ _ Heqo0).
  rewrite negb_true_iff in Hreg. simpl in Hreg.
  apply existsb_false_forall in Hreg.
  apply box_sim_state_update_r; auto.
Qed.
Hint Immediate box_sim_state_prop_state_set_r: solve_box_sim.

Lemma function_preserves_reg_sim_state_prop1:
  forall sims sigma fuel r r_acc gamma fn_spec gamma' st' v' box_fns fn n exts box n0,
  RegsNotInBoxes sims reg_box_defs ->
  box_fn_preserves_prop box_fns ->
  find (fun '(f, _) => Nat.eqb fn f) box_fns = Some (n, (box, exts)) ->
  lookup_int_fn int_fns fn tt = Success (n0, fn_spec) ->
  oraat_interp_action sigma int_fns struct_defs fuel r r_acc true gamma (fn_body fn_spec) = (true, Some (gamma', st', v')) ->
  reg_sim_state_prop sims r_acc st'.
Proof.
  intros * Hregs Hbox Hfind Hlookup Horaat.
  specialize function_writes_regs_only_def with (1 := Hbox) (2 := Hfind) (3 := Hlookup).
  intros (def & HIn & Hpreserves & Hwrites).
  specialize taint_safety_function with (1 := Horaat) as Htaint.
  consider action_writes_regs_only. propositional. simplify. consider @is_success_some.
  specialize (Htaint fuel0). consider taint_empty. repeat simpl_match. propositional.
  unfold RegsNotInBoxes in *.
  consider reg_sim_state_prop.
  intros * Hreg.

  specialize Hregs with (1 := Hreg) (box:= box) (def := get_box_regs def).
  assert_pre_and_specialize Hregs.
  { unfold reg_box_defs in *. apply in_map with (f := fun '(b,d) => (b,get_box_regs d)) in HIn; auto. }
  specialize Hwrites0 with (1 := Hregs).

  assert (no_writes_in_taint_set (Success (Some t)) reg  = true) as Hno_write.
  { unfold no_writes_in_taint_set. destruct_match; auto.
    specialize Hwrites0 with (1 := eq_refl); propositional. rewrite Hwrites1. rewrite Hwrites2. auto.
  }
  erewrite taint_set_to_prop_no_write' with (1 := Htaint) by auto. reflexivity.
Qed.

Hint Immediate function_preserves_reg_sim_state_prop1 : solve_box_sim.
Lemma box_sim_refl:
  forall box st,
  box_sim box st st.
Proof.
  constructor; auto.
  consider box_data_sim; auto.
Qed.
Hint Immediate box_sim_refl: solve_box_sims.
Lemma pf_writes_filter_box_sim_preserved1:
  forall box_fns fn sims st st' sigma fuel r gamma gamma' v' box n exts n0 fn_spec is_safe ,
  ValidBoxSims sims ->
  oraat_interp_action sigma int_fns struct_defs fuel r st is_safe gamma (fn_body fn_spec) = (true, Some (gamma', st', v')) ->
  box_fn_preserves_prop box_fns ->
  find (fun '(f, _) => Nat.eqb fn f) box_fns = Some (n, (box, exts)) ->
  lookup_int_fn int_fns fn tt = Success (n0, fn_spec) ->
  (* existsb (beq_dec box) sims = false -> *)
  WF_boxes box_defs ->
  box_sim_state_prop (filter (fun box2 : box_t => negb (beq_dec box box2)) sims) st st'.
Proof.
  intros * Hvalid Horaat Hpreserves Hfind Hlookup Hwf_boxes.
  eapply function_preserves_box_sim_state_prop in Hpreserves; eauto.
  consider ValidBoxSims.
  consider box_sim_state_prop.
  rewrite Forall_forall in *. intros * Hin.
  propositional.
  apply filter_In in Hin. propositional.
  rewrite negb_true_iff in Hin1. rewrite beq_dec_false_iff in Hin1.
  specialize Hvalid with (1 := Hin0). propositional.
  destruct Hwf_boxes. unfold BoxRegsDisjoint in *.
  apply find_some in Hfind. propositional; simplify.
  destruct_match.
  - apply find_some in Heqo. destruct_match_pairs; propositional. rewrite beq_dec_iff in Heqo1. subst.
    specialize WFBoxes_Disjoint0 with (1 := Hpreserves1) (2 := Heqo0).
    eapply box_sim_regs_unchanged with (1 := box_sim_refl _ _); eauto.
    eapply action_writes_regs_only_sim; eauto.
  - eapply find_none in Heqo; [ | eapply Hvalid0].
    destruct_match_pairs; simplify. rewrite beq_dec_false_iff in Heqo. congruence.
Qed.
Lemma ValidBoxSim_filter:
  forall f sim,
  ValidBoxSims sim ->
  ValidBoxSims (filter f sim).
Proof.
  intros * Hsim.
  unfold ValidBoxSims in *.
  rewrite Forall_forall in *.
  intros * Hfilter. rewrite filter_In in Hfilter. propositional.
Qed.
Hint Immediate ValidBoxSim_filter: solve_box_sim.
Lemma box_sim_state_prop_filter:
  forall f sims st1 st2,
  box_sim_state_prop sims st1 st2 ->
  box_sim_state_prop (filter f sims) st1 st2.
Proof.
  intros * Hsim. unfold box_sim_state_prop in *.
  rewrite Forall_forall in *.
  intros * Hin. rewrite filter_In in Hin. propositional. eapply Hsim; eauto.
Qed.
Hint Immediate box_sim_state_prop_filter: solve_box_sim.
Lemma gamma_vars_eq_cons:
  forall {A} {B} (xs: @varenv_t A) (ys: @varenv_t B) v vx vy,
  gamma_vars_eq xs ys ->
  gamma_vars_eq ((v,vx)::xs) ((v,vy)::ys).
Proof.
  constructor; auto.
Qed.
Hint Immediate gamma_vars_eq_cons: solve_box_sim.

Lemma gamma_vars_eq_nil:
  forall {A} {B},
  gamma_vars_eq ([]: @varenv_t A) ([]: @varenv_t B).
Proof.
  constructor.
Qed.
Hint Immediate gamma_vars_eq_nil: solve_box_sim.

Lemma remove_tainted_action_correct':
  forall fuel1 fuel2 box_fns sigma sim_st sim_gamma action sim_gamma' sim_st' r r_acc is_safe gamma gamma' st' v' ,
  gamma_vars_eq gamma sim_gamma ->
  ValidBoxSims (sim_boxes sim_st) ->
  WF_boxes box_defs ->
  RegsNotInBoxes (sim_regs sim_st) reg_box_defs ->
  box_fn_preserves_prop box_fns ->
  remove_tainted_action' int_fns reg_box_defs box_fns fuel1 sim_st sim_gamma action = Success (Some(sim_gamma', sim_st')) ->
  oraat_interp_action sigma int_fns struct_defs fuel2 r r_acc is_safe gamma action = (true, Some (gamma', st', v')) ->
  (* gamma_vars_eq gamma' sim_gamma' /\ *)
  gamma_sim_correct gamma gamma' sim_gamma' /\
  reg_sim_state_prop (sim_regs sim_st') r_acc st' /\
  box_sim_state_prop (sim_boxes sim_st') r_acc st'.
Proof.
  induction fuel1; [ discriminate | ].
  destruct fuel2; [discriminate | ].
  consider remove_tainted_action.
  intros * Hgammas_eq Hvalid Hwf Hregs_boxes Hbox_fns Hremove Horaat.
  specialize IHfuel1 with (3 := Hwf) (5 := Hbox_fns).
  destruct action; cbn in *; unfold res_opt_bind, __debug__ in *.
  Ltac solve_remove_tainted_action_correct IH :=
    match goal with
    | H: _ && _ = true |- _ => rewrite andb_true_iff in H
    | H: remove_tainted_action' _ _ _ _ _ _ _ = Success (Some _) |- _ =>
        (pose_fresh (proj1 (remove_tainted_action_decreases_sim' _ _ _ _ _ _ _ _ _ H)) ||
         pose_fresh (proj1 (proj2 (remove_tainted_action_decreases_sim' _ _ _ _ _ _ _ _ _ H))) ||
         pose_fresh (proj2 (proj2 (remove_tainted_action_decreases_sim' _ _ _ _ _ _ _ _ _ H))))
    | H: oraat_interp_action _ _ _ _ _ _ _ ?gamma ?action = (true, Some _) |- _ =>
        pose_fresh (oraat_interp_action_gamma_vars_eq _ _ _ _ _ _ _ _ _ _ _ _ H)
    | H: gamma_vars_eq ?gamma ?sim_gamma,
      H1: ValidBoxSims (sim_boxes ?sim_st),
      H2: RegsNotInBoxes (sim_regs ?sim_st) reg_box_defs,
      H3: remove_tainted_action' _ _ _ ?fuel1 ?sim_st ?sim_gamma ?action = Success (Some (_)),
      H4: oraat_interp_action _ _ _ _ _ _ _ _ ?action = (true, Some _) |- _ =>
      eapply IH  with (1 := H) (2 := H1) (3 := H2) (4 := H3) in H4
    | H: box_sim_state_prop ?bs _ _ |- _ =>
        pose_fresh (box_sim_state_prop_implies_valid_box_sim _ _ _ H)
    | H: gamma_state_le ?s1 ?s2 |- _ =>
        pose_fresh (gamma_state_le_implies_gamma_var_eq _ _ H)
    | H: gamma_sim_correct _ _ _ |- _ =>
        pose_fresh (gamma_sim_correct_implies_var_eq2 _ _ _ H) ||
        pose_fresh (gamma_sim_correct_implies_var_eq1 _ _ _ H)
    | H: remove_tainted_action' _ _ _ _ _ _ ?action = Success None,
        H1: oraat_interp_action _ _ _ _ _ _ _ _ ?action = (true, Some _) |- _ =>
        exfalso; specialize remove_tainted_action_none_correct with (1 := H) (2 := H1); intros; subst; discriminate
    | H: ValidBoxSims ?sim,
      H1: box_sim_le ?sim' ?sim |- _ =>
        pose_fresh (ValidBoxSims_le _ _ H H1)
    | H: gamma_vars_eq ?g1 ?g2 |- _ =>
        pose_fresh (gamma_vars_eq_sym _ _ H)
    | H1: gamma_vars_eq ?gamma1 ?gamma2,
      H2: gamma_vars_eq ?gamma2 ?gamma3 |- _ =>
        pose_fresh (gamma_vars_eq_trans _ _ _ H1 H2)
    | H: gamma_state_le ?sim1 ?sim2,
      H1: gamma_state_le ?sim2 ?sim3 |- _ =>
        pose_fresh (gamma_state_le_trans _ _ _ H H1)
    | H: gamma_sim_correct ?gamma1 ?gamma1' ?gamma_sims',
      H1: gamma_sim_correct ?gamma2 ?gamma2' ?gamma_sims',
      H2: gamma_sim_correct ?gamma1 ?gamma2 ?gamma_sims' |- _ =>
        pose_fresh (gamma_sim_correct_trans _ _ _ _ _ H H1 H2)
    | H: gamma_sim_correct ?x ?y ?Z |- _ =>
        pose_fresh (gamma_sim_correct_sym _ _ _ H)
    | H: gamma_state_le ?sim' ?sim,
      H1: gamma_sim_correct ?gamma1 ?gamma2 ?sim |- _ =>
        pose_fresh (gamma_sim_correct_le _ _ _ _ H H1)
    | H: remove_tainted_action' _ _ _ _ _ (varenv_bind ?s2 ?v ?v1) ?action2 = Success (Some _),
      H1: oraat_interp_action _ _ _ _ _ _ _ (varenv_bind ?g ?v ?v0) ?action2 = (true, Some _),
      H2: gamma_vars_eq ?g ?s2  |- _ =>
        pose_fresh (gamma_vars_eq_varenv_bind _ _ v v0 v1 H2)
    | H: gamma_state_le ?sim2 (varenv_bind ?sim1 ?v ?b) |- _ =>
        pose_fresh (gamma_state_le_bind _ _ _ _ H)
    | H: RegsNotInBoxes ?sim ?fns,
      H1: reg_sim_le ?sim' ?sim |- _ =>
        pose_fresh (RegNotInBoxes_decreases_preserve _ _ _ H H1)
    | |- _ => simplify_oraat_interp_action_safety
    | |- _ => progress (simpl in *;simplify;propositional; eauto with solve_box_sim; try congruence)
    end.
  all: destruct_all_matches; repeat solve_remove_tainted_action_correct IHfuel1.
  - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1.
    eapply gamma_sim_correct_varenv_update_false; eauto with solve_box_sim.
  - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1.
    + eapply gamma_sim_correct_trans with (3 := Horaat0); eauto with solve_box_sim.
    + eapply reg_sim_state_prop_trans; eauto with solve_box_sim.
      apply reg_sim_state_prop_sym; eauto with solve_box_sim.
    + eapply box_sim_state_prop_trans; eauto with solve_box_sim.
      apply box_sim_state_prop_sym; eauto with solve_box_sim.
  - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1.
    + eapply gamma_sim_correct_le with (sim := s4); eauto.
      eapply gamma_sim_correct_trans with (3 := Horaat0); eauto with solve_box_sim.
    + eapply reg_sim_le_state_prop; eauto with solve_box_sim.
      eapply reg_sim_state_prop_trans; eauto with solve_box_sim.
      eapply reg_sim_le_state_prop; eauto with solve_box_sim.
    + eapply box_sim_le_state_prop; eauto with solve_box_sim.
      eapply box_sim_state_prop_trans; eauto with solve_box_sim.
      eapply box_sim_le_state_prop; eauto with solve_box_sim.
  - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1.
    + eapply gamma_sim_correct_trans with (3 := Horaat0); eauto with solve_box_sim.
    + eapply reg_sim_state_prop_trans; eauto with solve_box_sim.
      apply reg_sim_state_prop_sym; eauto with solve_box_sim.
    + eapply box_sim_state_prop_trans; eauto with solve_box_sim.
      apply box_sim_state_prop_sym; eauto with solve_box_sim.
  - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1.
    + eapply gamma_sim_correct_trans; eauto with solve_box_sim.
    + eapply reg_sim_state_prop_trans; eauto with solve_box_sim.
      eapply reg_sim_le_state_prop; eauto with solve_box_sim.
      eapply reg_sim_le_state_prop; eauto with solve_box_sim.
    + eapply box_sim_state_prop_trans; eauto with solve_box_sim.
      eapply box_sim_le_state_prop; eauto with solve_box_sim.
      eapply box_sim_le_state_prop; eauto with solve_box_sim.
  - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1.
    + eapply gamma_sim_correct_trans; eauto with solve_box_sim.
    + eapply reg_sim_state_prop_trans; eauto with solve_box_sim.
      eapply reg_sim_le_state_prop; eauto with solve_box_sim.
    + eapply box_sim_state_prop_trans; eauto with solve_box_sim.
      eapply box_sim_le_state_prop; eauto with solve_box_sim.
  - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1.
    + eapply gamma_sim_correct_trans with (gamma2 := g); eauto with solve_box_sim.
      eapply gamma_sim_correct_sym. replace g with (tl (varenv_bind g v l)) by auto.
      eauto with solve_box_sim.
    + eapply reg_sim_state_prop_trans; eauto with solve_box_sim.
      eapply reg_sim_le_state_prop; eauto with solve_box_sim.
    + eapply box_sim_state_prop_trans; eauto with solve_box_sim.
      eapply box_sim_le_state_prop; eauto with solve_box_sim.
  - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1.
    + eapply gamma_sim_correct_trans; eauto with solve_box_sim.
    + eapply reg_sim_state_prop_trans; eauto with solve_box_sim.
      eapply reg_sim_le_state_prop; eauto with solve_box_sim.
    + eapply box_sim_state_prop_trans; eauto with solve_box_sim.
      eapply box_sim_le_state_prop; eauto with solve_box_sim.
  - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1.
    + consider get_fn_arg_and_body''. consider @success_or_default. simplify.
      eapply reg_sim_state_prop_trans; eauto with solve_box_sim.
    + eapply box_sim_state_prop_trans; eauto with solve_box_sim.
      * eapply box_sim_state_prop_refl; eauto with solve_box_sim.
      * consider get_fn_arg_and_body''; unfold success_or_default in *; simplify.
        eapply pf_writes_filter_box_sim_preserved1; eauto with solve_box_sim.
  - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1.
    + eapply reg_sim_state_prop_trans with (sim1 := s); eauto with solve_box_sim.
      { eapply reg_sim_state_prop_sym. eauto with solve_box_sim. }
      consider get_fn_arg_and_body''. consider @success_or_default. simplify.
      eapply IHfuel1 with (action := fn_body i) (4 := Heqr2) (5 := Heqp3); eauto with solve_box_sim.
      unfold fn_gamma.
      eapply gamma_vars_eq_cons; eauto with solve_box_sim.
    + eapply box_sim_state_prop_trans with (st1:= s); eauto with solve_box_sim.
      { eapply box_sim_state_prop_sym. eauto with solve_box_sim. }
      consider get_fn_arg_and_body''. consider @success_or_default. simplify.
      eapply IHfuel1 with (action := fn_body i) (4 := Heqr2) (5 := Heqp3); eauto with solve_box_sim.
      eapply gamma_vars_eq_cons; eauto with solve_box_sim.
Qed.
Lemma remove_tainted_action_correct:
  forall fuel1 fuel2 box_fns sigma sim_st sim_gamma action sim_gamma' sim_st' r r_acc is_safe gamma gamma' st' v' ,
  gamma_vars_eq gamma sim_gamma ->
  ValidBoxSims (sim_boxes sim_st) ->
  WF_boxes box_defs ->
  RegsNotInBoxes (sim_regs sim_st) reg_box_defs ->
  box_fn_preserves_prop box_fns ->
  remove_tainted_action int_fns reg_box_defs box_fns fuel1 sim_st sim_gamma action = Success (sim_gamma', sim_st') ->
  oraat_interp_action sigma int_fns struct_defs fuel2 r r_acc is_safe gamma action = (true, Some (gamma', st', v')) ->
  (* gamma_vars_eq gamma' sim_gamma' /\ *)
  gamma_sim_correct gamma gamma' sim_gamma' /\
  reg_sim_state_prop (sim_regs sim_st') r_acc st' /\
  box_sim_state_prop (sim_boxes sim_st') r_acc st'.
Proof.
  consider remove_tainted_action. intros * Hgamma Hbox Hwf Hregs Hfns Hremove Horaat.
  bash_destruct Hremove.
  - simplify. eapply remove_tainted_action_correct' with (6 := Heqr0); eauto.
  - eapply remove_tainted_action_none_correct with (2 := Horaat) in Heqr0. discriminate.
Qed.

      Ltac solve_box_sim_analyze_action_correct IH :=
        match goal with
        | H: oraat_interp_action _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
            match b with
            | true => fail
            | _ => let H' := fresh in
                  assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
                  rewrite H' in H; subst
            end
        | H: analyze_action _ _ _ _ _ _ _ _ ?action = Success None,
          H1: oraat_interp_action _ _ _ _ _ _ _ _ ?action = (true, Some _) |- _ =>
            exfalso; apply analyze_none_implies_fail with (1 := H) (2 := H1); auto
        | H: _ && _ = true |- _ => rewrite andb_true_iff in H
        | H1: oraat_interp_action _ _ _ _ ?r1 ?r_acc1 _ ?gamma1 ?action = (true, Some(?gamma1', ?st1', ?v1')),
          H2: oraat_interp_action _ _ _ _ ?r2 ?r_acc2 _ ?gamma2 ?action = (true, Some(?gamma2', ?st2', ?v2')),
          (* H3: box_sim_state_prop (sim_boxes ?acc_reg_sims) ?r1 ?r2, *)
          H4: box_sim_state_prop (sim_boxes ?acc_reg_sims) ?r_acc1 ?r_acc2,
          (* H4: gamma_sim_correct ?gamma1 ?gamma2 ?gamma_sims, *)
          H5: reg_sim_state_prop (sim_regs ?acc_reg_sims) ?r_acc1 ?r_acc2,
          H6: analyze_action _ _ _ _ _ _ ?acc_reg_sims ?gamma_sims ?action = Success (Some _) |- _ =>
            eapply IH with (2 := H2) (* (3 := H3) *) (4 := H4)  (6 := H5) (8 := H6) in H1; [ | solve[eauto with solve_box_sim] ..]; clear H2
        | H: remove_tainted_action _ _ _ _ ?sim_st ?sim_gamma _ = Success (_, _) |- _ =>
            (pose_fresh (proj1 (remove_tainted_action_decreases_sim _ _ _ _ _ _ _ _ _ H)) ||
            (pose_fresh (sim_state_le_implies_reg_sim_le _ _
                          (proj2 (remove_tainted_action_decreases_sim _ _ _ _ _ _ _ _ _ H)))) ||
            (pose_fresh (sim_state_le_implies_box_sim_le _ _
                          (proj2 (remove_tainted_action_decreases_sim _ _ _ _ _ _ _ _ _ H)))))
        | |- box_sim_le (merge_sim_boxes (sim_boxes _) (sim_boxes _)) _ =>
          (eapply box_sim_le_merge_sim_boxes_l; solve[eauto with solve_box_sim]) ||
          (eapply box_sim_le_merge_sim_boxes_r; solve[eauto with solve_box_sim])
        | H: RegsNotInBoxes ?sim1 ?fn
          |- RegsNotInBoxes ?sim2 ?fn =>
              eapply RegNotInBoxes_decreases_preserve with (1 := H); solve[eauto with solve_box_sim]
        | H: oraat_interp_action _ _ _ _ ?r1 ?r_acc1 _ ?gamma1 ?action = (true, Some(?gamma1', ?st1', ?v1')) |- _ =>
            pose_fresh (oraat_interp_action_gamma_vars_eq _ _ _ _ _ _ _ _ _ _ _ _ H)
        | H: box_sim_le ?sim1 ?sim2
          |- box_sim_le (filter _ ?sim1) ?sim2 =>
            eapply box_sim_le_trans with (2 := H); solve[eauto with solve_box_sim]
        | H: gamma_sim_correct ?g1 ?g2 ?s |- _ =>
            (pose_fresh (gamma_sim_correct_implies_var_eq1 _ _ _ H)) ||
              (pose_fresh (gamma_sim_correct_implies_var_eq2 _ _ _ H))
        | H: gamma_vars_eq ?gamma ?sim_gamma,
          H1: box_sim_state_prop (sim_boxes ?sim_st) _ _,
          H2: WF_boxes box_defs,
          H3: RegsNotInBoxes (sim_regs ?sim_st) _,
          H4: box_fn_preserves_prop ?box_fns,
          H5: remove_tainted_action _ _ _ _ ?sim_st ?sim_gamma ?action = Success (_, _),
          H6: oraat_interp_action _ _ _ _ _ _ _ ?gamma ?action = (true, Some _) |- _ =>
            let tuple := constr:(remove_tainted_action_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                           H (box_sim_state_prop_implies_valid_box_sim _ _ _ H1) H2 H3 H4 H5 H6) in
            pose_fresh (proj1 tuple) ||
            pose_fresh (proj1 (proj2 tuple)) ||
            pose_fresh (proj2 (proj2 tuple))
        | H: gamma_state_le ?sim' ?sim,
          H1: gamma_sim_correct ?gamma1 ?gamma2 ?sim |- _ =>
            pose_fresh (gamma_sim_correct_le _ _ _ _ H H1)
        | H: box_sim_le ?box1 ?box2,
          H1:box_sim_le ?box2 ?box3 |- _ =>
            pose_fresh (box_sim_le_trans _ _ _ H H1)
        | H : reg_sim_le ?sim2 ?sim1,
          H1: reg_sim_state_prop ?sim1 ?st1 ?st2 |- _ =>
            pose_fresh (reg_sim_le_state_prop _ _ _ _ H H1)
        | H : box_sim_le ?sim2 ?sim1,
          H1: box_sim_state_prop ?sim1 ?st1 ?st2 |- _ =>
            pose_fresh (box_sim_le_state_prop _ _ _ _ H H1)
        | H: RegsNotInBoxes ?sim _,
          H1: reg_sim_le ?sim' ?sim |- _ =>
            pose_fresh (RegNotInBoxes_decreases_preserve _ _ _ H H1)
        | |- _ => progress (simpl in *;simplify;propositional; eauto with solve_box_sim; try congruence)
        end.

    Lemma box_sim_analyze_action_correct:
      forall fuel1 fuel2 fuel3 sigma1 sigma2 r1 r_acc1 r2 r_acc2 safe1 safe2 gamma1 gamma2 action
        gamma1' gamma2' st1' st2' v1' v2' box_fns ext_fn_sims init_reg_sims acc_reg_sims gamma_sims
        gamma_sims' reg_sims' v_sim',
        oraat_interp_action sigma1 int_fns struct_defs fuel1
          r1 r_acc1 safe1 gamma1 action = (true, Some(gamma1', st1', v1')) ->
        oraat_interp_action sigma2 int_fns struct_defs fuel2
          r2 r_acc2 safe2 gamma2 action = (true, Some(gamma2', st2', v2')) ->
        reg_sim_state_prop init_reg_sims r1 r2 ->
        box_sim_state_prop (sim_boxes acc_reg_sims) r1 r2 ->
        box_sim_state_prop (sim_boxes acc_reg_sims) r_acc1 r_acc2 ->
        WF_boxes box_defs ->
        Forall (fun f => forall v, sigma1 f v = sigma2 f v) ext_fn_sims ->
        box_fn_preserves_prop box_fns ->
        gamma_sim_correct gamma1 gamma2 gamma_sims ->
        reg_sim_state_prop (sim_regs acc_reg_sims) r_acc1 r_acc2 ->
        RegsNotInBoxes (sim_regs acc_reg_sims) (map (fun '(box, def) => (box, get_box_regs def)) box_defs) ->
        analyze_action int_fns
          (map (fun '(box, def) => (box, get_box_regs def)) box_defs)
          box_fns ext_fn_sims init_reg_sims
          fuel3 acc_reg_sims gamma_sims action = Success (Some (gamma_sims', reg_sims', v_sim')) ->
        RegsNotInBoxes (sim_regs reg_sims') (map (fun '(box, def) => (box, get_box_regs def)) box_defs)
        /\ gamma_sim_correct gamma1' gamma2' gamma_sims'
        /\ reg_sim_state_prop (sim_regs reg_sims') st1' st2'
        /\ box_sim_state_prop (sim_boxes reg_sims') st1' st2'
        /\ box_sim_le (sim_boxes reg_sims') (sim_boxes acc_reg_sims)
        /\ (match v_sim' with
           | true => v1' = v2'
           | false => True
           end).
    Proof.
      induction fuel1; intros * Horaat1 Horaat2 Hreg_sim0 Hbox_sim0 Hbox_sim1 Hwf_boxes Hext_sim Hbox_fns Hgamma_sim
                                  Hreg_sim1 Hwf_regs Hanalyze; [discriminate | ].
      destruct fuel2; [discriminate | ].
      destruct fuel3; [discriminate | ].

      specialize IHfuel1 with (3 := Hreg_sim0) (6 := Hwf_boxes) (7 := Hext_sim) (8 := Hbox_fns).
      destruct action; cbn in *; simplify; simpl in *; unfold __debug__, opt_bind_to_res, res_opt_bind, get_fn_arg_and_body'' in *; simplify; auto.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
        split_ands_in_goal; eauto with solve_box_sim.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
        split_ands_in_goal; eauto with solve_box_sim.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
        split_ands_in_goal; eauto with solve_box_sim.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
          split_ands_in_goal; eauto with solve_box_sim.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1.
        all: split_ands_in_goal; repeat solve_box_sim_analyze_action_correct IHfuel1.
        + eapply reg_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim.
        + eapply box_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim.
        + eapply reg_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim.
        + eapply box_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim.
        + eapply reg_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim.
        + eapply box_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
          split_ands_in_goal; eauto with solve_box_sim.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
          split_ands_in_goal; eauto with solve_box_sim.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
          split_ands_in_goal; eauto with solve_box_sim.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
          split_ands_in_goal; eauto with solve_box_sim.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
          split_ands_in_goal; eauto with solve_box_sim.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
          split_ands_in_goal; eauto with solve_box_sim.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
          split_ands_in_goal; repeat solve_box_sim_analyze_action_correct IHfuel1.
        + eapply pf_action_writes_regs_only_box_sim_preserved with (3 := Heqp12) (4 := Heqp7); eauto.
        + eapply pf_action_writes_regs_only_box_sim_preserved with (3 := Heqp12) (4 := Heqp7); eauto.
        + rewrite Heqb1 in H6. repeat rewrite andb_true_r in *.
          eapply pf_writes_not_in_box_sim_preserved with (3 := Heqp12) (4 := Heqp7); eauto.
        + rewrite<-andb_assoc in H6.
          rewrite andb_comm in Heqb3. rewrite Heqb3 in H6.
          eapply pf_writes_filter_box_sim_preserved with (3 := Heqp12) (4 := Heqp7); eauto.
      - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1;
          split_ands_in_goal; eauto with solve_box_sim.
    Qed.

    Definition computable_regs_not_in_boxes (env: SortedRegEnv.EnvT bool) : bool :=
      forallb (fun '(b, def) =>
                 forallb (fun reg => match SortedRegEnv.opt_get env reg with
                                  | Some true => false
                                  | _ => true
                                  end) def)
        (map (fun '(box, def) => (box, get_box_regs def)) box_defs).

    Lemma computable_regs_not_in_boxes_correct:
      forall env, computable_regs_not_in_boxes env = true ->
        RegsNotInBoxes env (map (fun '(box, def) => (box, get_box_regs def)) box_defs).
    Proof.
      intros. consider computable_regs_not_in_boxes.
      rewrite forallb_forall in *.
      unfold RegsNotInBoxes in *.
      intros * Hbox Hreg.
      specialize H with (1 := Hreg). simpl in H. rewrite forallb_forall in *.
      intros. specialize H with (1 := H0). simpl_match. discriminate.
    Qed.

    Theorem box_sim_analyze_rule_correct:
      forall sigma1 sigma2 r1 r2 safe1 safe2 action gamma1' gamma2' st1' st2' v1' v2' box_fns ext_fn_sims reg_sims box_sims reg_sims',
        oraat_interp_action sigma1 int_fns struct_defs (safe_fuel int_fns (Datatypes.length int_fns) action)
          r1 r1 safe1 GenericGammaEmpty action = (true, Some(gamma1', st1', v1')) ->
        oraat_interp_action sigma2 int_fns struct_defs (safe_fuel int_fns (Datatypes.length int_fns) action)
          r2 r2 safe2 GenericGammaEmpty action = (true, Some(gamma2', st2', v2')) ->
        reg_sim_state_prop reg_sims r1 r2 ->
        box_sim_state_prop box_sims r1 r2 ->
        Forall (fun f => forall v, sigma1 f v = sigma2 f v) ext_fn_sims ->
        WF_boxes box_defs ->
        box_fn_preserves_prop box_fns ->
        RegsNotInBoxes reg_sims (map (fun '(box, def) => (box, get_box_regs def)) box_defs) ->
        @analyze_rule int_fns box_t box_t_eq_dec
          (map (fun '(box, def) => (box, get_box_regs def)) box_defs)
          box_fns ext_fn_sims reg_sims box_sims action = Success (Some (reg_sims')) ->
        reg_sim_state_prop (sim_regs reg_sims') st1' st2' /\ box_sim_state_prop (sim_boxes reg_sims') st1' st2'.
    Proof.
      unfold analyze_rule, res_opt_bind.
      intros; simplify.
      eapply box_sim_analyze_action_correct with (1 := H) (2 := H0) in Heqr; propositional; eauto.
      apply gamma_sim_correct_empty.
    Qed.

  End BoxSimAnalysis.

End BoxSimCorrect.
