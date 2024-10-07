Require Import koika.Common.
Require Import koika.Utils.
Require Import koika.Syntax.
Require Import koika.Semantics.
Require Import koika.Environments.
Require Import koika.Typechecking.
Require Import koika.Tactics.
Require Import koika.StaticAnalysis.
Require Import koika.TypecheckingCorrectness.
Require Import FunctionalExtensionality.
Require Import koika.SyntaxUtils.
Require Import koika.SemanticUtils.
Ltac simplify_oraat_interp_action_safety :=
  match goal with
  | H: oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
      match b with
      | true => fail
      | _ => let H' := fresh in
            assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
            rewrite H' in H; subst
      end
  | H: oraat_interp_scheduler' _ _ _ _ _ _ ?b _ = (true, _, _) |- _ =>
      match b with
      | true => fail
      | _ => let H' := fresh in
            assert (b = true) as H' by  (eapply oraat_interp_scheduler'_is_safe_generalizes; eauto);
            rewrite H' in H; subst
      end

  end.

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

(* Section FailSafety. *)
(*   Context (ext_sigma: @ext_sigma_t N). *)
(*   Context (int_fns: @int_fn_env_t N (@action N)). *)
(*   Context (struct_defs: @struct_env_t N). *)
(*   Ltac solve_action_fail_safety IH := *)
(*       match goal with *)
(*       | H: _ || _ = false |- _ => *)
(*           rewrite orb_false_iff in H *)
(*       | H: _ && _ = true |- _ => *)
(*           rewrite andb_true_iff in H *)
(*       | H: oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ => *)
(*           match b with *)
(*           | true => fail *)
(*           | _ => let H' := fresh in *)
(*                 assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto); *)
(*                 rewrite H' in H; subst *)
(*           end *)
(*       | H: oraat_interp_action ?sigma ?int_fns ?struct_defs ?fuel ?r ?r_acc ?ext_fn_log true ?gamma ?_action = (true, None), *)
(*         H1: action_contains_fail ?int_fns ?_fuel2 ?action = Success false *)
(*         |- _ => *)
(*           apply IH with (fuel2 := _fuel2) in H; auto *)
(*       | |- _ => progress (repeat simpl_match; simpl in *;simplify;propositional; auto) *)
(*       end. *)


(*   Lemma action_fail_safety: *)
(*     forall fuel1 fuel2 r r_acc b gamma action ext_fn_log, *)
(*     oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc ext_fn_log b gamma action = (true, None) -> *)
(*     action_contains_fail int_fns fuel2 action = Success false -> *)
(*     False. *)
(*   Proof. *)
(*     induction fuel1; intros fuel2 r r_acc b gamma action ext_fn_log Horaat Haction; *)
(*       simpl in *; simplify; [discriminate | ]. *)
(*     destruct fuel2; simpl in *; [discriminate | ]. *)
(*     destruct action; cbn in *; simplify; simpl in *; *)
(*       destruct_all_matches; unfold get_fn_arg_and_body'', __debug__ in *; *)
(*       repeat solve_action_fail_safety IHfuel1; propositional. *)
(*   Qed. *)

(* End FailSafety. *)

Section TaintSafety.
  Context (ext_sigma: @ext_sigma_t N).
  Context (int_fns: @int_fn_env_t N (@action N)).
  Context (struct_defs: @struct_env_t N).

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
    destruct_with_eqn (beq_dec idx reg); simplify.
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
    destruct_with_eqn (beq_dec idx reg); simplify.
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
    destruct_with_eqn (beq_dec idx reg); simplify.
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
    destruct_with_eqn (beq_dec idx reg); simplify.
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
  Hint Immediate taint_env_le_refl : solve_taint.
  Hint Immediate taint_env_corresponds_to_state_update__empty: solve_taint.
  Hint Immediate taint_env_corresponds_to_state_update__unchanged: solve_taint.
  Hint Immediate merge_taints_empty_l: solve_taint.
  Hint Immediate merge_taints_empty_r: solve_taint.
  Hint Resolve taint_le_empty_l : solve_taint.

  Ltac solve_taint_safety_action IH :=
    match goal with
    | |- taint_env_corresponds_to_state_update ?r ?r _ =>
      apply taint_env_corresponds_to_state_update__unchanged
    | H: _ && _ = true |- _ => rewrite andb_true_iff in H; propositional
    | H: true = _ && _ |- _ => symmetry in H
    | H: oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
        match b with
        | true => fail
        | _ => let H' := fresh in
              assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
              rewrite H' in H; subst
        end
    | H: oraat_interp_action ?sigma ?int_fns ?struct_defs ?fuel ?r ?r_acc ?ext_fn_log true ?gamma ?_action = (true, Some (_, ?_r', _)),
      Htaint : taint_env_corresponds_to_state_update ?r ?r_acc ?_taint_env,
      Hsuccess : taint_action ?int_fns ?_fuel2 ?_taint_env ?_action = Success (Some ?_env)
      |- _ =>
        eapply IH with (taint_env := _taint_env) (env := _env) (fuel2 := _fuel2) in H ; auto
    | H: oraat_interp_action ?sigma ?int_fns ?struct_defs ?fuel ?r ?r_acc ?ext_fn_log true ?gamma ?_action = (true, None),
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
    forall fuel1 fuel2 r r_acc gamma taint_env action env gamma' st' res ext_fn_log ext_fn_log',
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc ext_fn_log true
         gamma action = (true, Some (gamma', st', ext_fn_log', res)) ->
      taint_env_corresponds_to_state_update r r_acc taint_env ->
      taint_action int_fns fuel2 taint_env action = Success (Some env) ->
      taint_env_corresponds_to_state_update r st' env.
  Proof.
    induction fuel1;
      intros fuel2 r r_acc gamma taint_env action env gamma' st' res ext_fn_log
             Horaat Htaint Hsuccess; simpl in *; simplify; subst.
    destruct fuel2; [simpl in *; discriminate | ].
    destruct action; cbn in *; simplify_tupless; propositional;
      destruct_match_pairs; unfold res_opt_bind, get_fn_arg_and_body'', __debug__ in *; repeat solve_taint_safety_action IHfuel1; destruct_all_matches; simplify; repeat solve_taint_safety_action IHfuel1.
  Qed.

  Ltac solve_taint_safety_function' IH :=
    match goal with
    | H: oraat_interp_action _ _ _ _ _ ?r_acc ?ext_fn_log true _ ?action = (true, Some _),
      H1: taint_env_corresponds_to_state_update ?r_base ?r_acc ?env,
      H2: taint_action _ ?fuel2 ?env ?action = Success (Some _) |- _ =>
        eapply IH with (2 := H1) (3 := H2) in H
    | |- taint_env_corresponds_to_state_update ?r ?r _ =>
      apply taint_env_corresponds_to_state_update__unchanged
    | H: _ && _ = true |- _ => rewrite andb_true_iff in H; propositional
    | H: true = _ && _ |- _ => symmetry in H
    | H: oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
        match b with
        | true => fail
        | _ => let H' := fresh in
              assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
              rewrite H' in H; subst
        end
    | |- _ => progress (simpl in *;simplify;propositional; auto with solve_taint)
    end.


  Lemma taint_safety_function':
    forall fuel1 fuel2 r r_acc gamma action gamma' st' res env env' r_base ext_fn_log ext_fn_log',
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc ext_fn_log true
         gamma action = (true, Some (gamma', st', ext_fn_log', res)) ->
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
    forall fuel1 fuel2 r r_acc gamma action gamma' st' res ext_fn_log ext_fn_log',
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc ext_fn_log true
         gamma action = (true, Some (gamma', st', ext_fn_log', res)) ->
      is_success_some (taint_action int_fns fuel2 SortedRegEnv.empty action) = true ->
      taint_set_to_prop r_acc st' (taint_action int_fns fuel2 SortedRegEnv.empty action).
  Proof.
    intros * Horaat Hsuccess.
    unfold is_success_some in *. bash_destruct Hsuccess.
    eapply taint_safety_function' with (r_base := r_acc) (env := SortedRegEnv.empty) (fuel2 := fuel2) in Horaat; eauto.
    apply taint_env_corresponds_to_state_update__empty; auto.
  Qed.

  Lemma taint_safety_rule:
    forall st1 st2 rule ext_fn_log2,
    oraat_interp_rule ext_sigma int_fns struct_defs st1 rule = (true, st2, ext_fn_log2) ->
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
Lemma taint_env_le_merge_taint:
  forall t1 t2,
  taint_env_le t1 t2 ->
  taint_env_le (merge_taint_env t1 t2) t2.
Proof.
  unfold merge_taint_env. intros * Hle. consider taint_env_le.
  intros. consider get_reg_taint_default.
  rewrite SortedRegEnv.opt_get_mapV.
  rewrite SortedRegEnv.opt_get_zip_default.
  specialize (Hle reg).
  repeat destruct_match; auto with solve_taint.
  - unfold merge_taints.
    destruct Hle. constructor; simpl; intros H; rewrite orb_true_iff in H; split_cases.
  - apply taint_le_empty' in Hle. subst.
    rewrite merge_taints_empty_l.
    apply taint_le_empty_l.
  - rewrite merge_taints_empty_l.
    apply taint_le_refl.
Qed.


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
Lemma merge_taints_eq_empty_implies_l:
  forall t1 t2,
  merge_taints t1 t2 = empty_taint ->
  t1 = empty_taint.
Proof.
  unfold merge_taints. intros. unfold empty_taint in *. inversions H.
  destruct t1; simpl in *.
  f_equal;[ destruct taint_read0  | destruct taint_read1 | destruct taint_write0 | destruct taint_write1];
      repeat match goal with
      | H: true = false |- _ => discriminate
      | H: _ = false |- _ => progress (rewrite H in *)
      | |- _ => progress (simpl in *; auto)
      end.
Qed.

Lemma taint_le_merge_taint_impl_l:
  forall t1 t2 t3,
  taint_le (merge_taints t1 t2) t3 ->
  taint_le t1 t3.
Proof.
  unfold merge_taints.
  intros. inversions H; simpl in *.
  constructor; propositional;
      repeat match goal with
      | H: true = false |- _ => discriminate
      | H: _ = true |- _ => progress (rewrite H in *)
      | |- _ => progress (simpl in *; auto)
      end.
Qed.

Lemma taint_env_le_merge_taint_env_impl_l:
  forall t1 t2 t3,
  taint_env_le (merge_taint_env t1 t2) t3 ->
  taint_env_le t1 t3.
Proof.
  intros * Htaint. unfold merge_taint_env, taint_env_le, get_reg_taint_default in *.
  intros reg. specialize (Htaint reg).
  rewrite SortedRegEnv.opt_get_mapV in Htaint.
  rewrite SortedRegEnv.opt_get_zip_default in Htaint.
  repeat destruct_match; eauto with solve_taint.
  - bash_destruct Htaint.
    + apply taint_le_merge_taint_impl_l in Htaint. assumption.
    + rewrite merge_taints_empty_r in Htaint. assumption.
  - bash_destruct Htaint.
    + apply taint_le_empty' in Htaint.
      apply merge_taints_eq_empty_implies_l in Htaint. subst. eauto with solve_taint.
    + apply taint_le_empty' in Htaint.
      rewrite merge_taints_empty_r in Htaint. subst. eauto with solve_taint.
Qed.

  Lemma taint_safety_schedule':
    forall {rule_name_t: Type} rules (schedule: @scheduler rule_name_t) st1 st2 ext_fn_log1 ext_fn_log2 taint_env taint_env',
    oraat_interp_scheduler' ext_sigma int_fns struct_defs rules
      st1 ext_fn_log1 true schedule = (true, st2, ext_fn_log2) ->
    taint_schedule int_fns rules taint_env schedule = Success (Some taint_env') ->
    taint_env_corresponds_to_state_update st1 st2 taint_env' /\
    taint_env_le taint_env taint_env'.
  Proof.
    induction schedule; intros * Hsched Htaint; simpl in *; simplify.
    - split; [apply taint_env_corresponds_to_state_update__unchanged | eauto with solve_taint].
    - unfold res_opt_bind in *. simplify.
      simplify_oraat_interp_action_safety.
      specialize IHschedule with (1 := Hsched) (2 := Htaint).
      propositional.
      split.
      + eapply taint_env_corresponds_taint_le with (env := merge_taint_env t taint_env'); auto.
        * specialize taint_safety_rule with (1 := Heqp). intros Htaint_rule.
          consider @is_success_some.
          setoid_rewrite Heqr0 in Htaint_rule. propositional.
          eapply taint_env_corresponds_to_state_update_chain; eauto.
        * apply taint_env_le_merge_taint.
          eapply taint_env_le_merge_taint_env_impl_l; eauto.
      + rewrite merge_taint_env_comm in IHschedule1.
        eapply taint_env_le_merge_taint_env_impl_l; eauto.
  Qed.

  Lemma taint_safety_schedule:
    forall {rule_name_t: Type} rules (schedule: @scheduler rule_name_t) st1 st2 ext_fn_log ,
    oraat_interp_scheduler ext_sigma int_fns struct_defs rules st1 schedule = (true, st2, ext_fn_log) ->
    is_success_some (taint_schedule int_fns rules SortedRegEnv.empty schedule) = true ->
    taint_set_to_prop st1 st2 (taint_schedule int_fns rules SortedRegEnv.empty schedule).
  Proof.
    intros * Horaat Htaint.
    unfold is_success_some in *. bash_destruct Htaint. unfold taint_set_to_prop.
    eapply taint_safety_schedule'; eauto.
  Qed.
 (* Section ReadOnly. *)
 (*    Definition read_only_taint (env: taint_env_t) := *)
 (*      forall reg, *)
 (*        match SortedRegEnv.opt_get env reg with *)
 (*        | Some t => if taint_write0 t || taint_write1 t then False else True *)
 (*        | None => True *)
 (*        end. *)

 (*    Lemma empty_taint_read_only: read_only_taint SortedRegEnv.empty. *)
 (*    Proof. *)
 (*      unfold read_only_taint; intros. *)
 (*      rewrite SortedRegEnv.opt_get_empty. auto. *)
 (*    Qed. *)

 (*    Lemma read_only_taint_le: *)
 (*      forall env env', *)
 (*      read_only_taint env' -> *)
 (*      taint_env_le env env' -> *)
 (*      read_only_taint env. *)
 (*    Proof. *)
 (*      intros * Hread Htaint. unfold read_only_taint, taint_env_le in *. *)
 (*      intros reg. *)
 (*      specialize (Htaint reg). specialize (Hread reg). unfold get_reg_taint_default in *. *)
 (*      destruct Htaint. *)
 (*      destruct_all_matches; auto. *)
 (*      - rewrite orb_false_iff in Heqb0. rewrite orb_true_iff in Heqb. propositional. *)
 (*        split_cases; congruence. *)
 (*      - rewrite orb_true_iff in Heqb. simpl in *. split_cases; congruence. *)
 (*    Qed. *)

 (*    Lemma read_only_taint_merge_l_invert: *)
 (*      forall t1 t2, *)
 (*      read_only_taint (merge_taint_env t1 t2) -> *)
 (*      read_only_taint t1. *)
 (*    Proof. *)
 (*      intros; eapply read_only_taint_le; eauto. *)
 (*      eapply taint_env_le_merge_refl_l. *)
 (*    Qed. *)

 (*    Lemma read_only_taint_merge_r_invert: *)
 (*      forall t1 t2, *)
 (*      read_only_taint (merge_taint_env t1 t2) -> *)
 (*      read_only_taint t2. *)
 (*    Proof. *)
 (*      intros; eapply read_only_taint_le; eauto. *)
 (*      eapply taint_env_le_merge_refl_r. *)
 (*    Qed. *)
 (*    Ltac progress_pose_as Name Value := *)
 (*      lazymatch goal with *)
 (*      | H' : Value |- _ => fail *)
 (*      | _ => pose proof Value as Name *)
 (*      end. *)
 (*     Lemma not_read_only_set_write0: *)
 (*      forall taint idx, *)
 (*      read_only_taint (set_reg_taint taint idx set_taint_write0) -> False. *)
 (*    Proof. *)
 (*      intros * Htaint. consider read_only_taint. *)
 (*      specialize (Htaint idx). consider set_reg_taint. *)
 (*      rewrite SortedRegEnv.update_correct_eq in Htaint; simpl in *. *)
 (*      destruct_matches_in_hyp Htaint; simpl in *; auto. *)
 (*    Qed. *)

 (*    Lemma not_read_only_set_write1: *)
 (*      forall taint idx, *)
 (*      read_only_taint (set_reg_taint taint idx set_taint_write1) -> False. *)
 (*    Proof. *)
 (*      intros * Htaint. consider read_only_taint. *)
 (*      specialize (Htaint idx). consider set_reg_taint. *)
 (*      rewrite SortedRegEnv.update_correct_eq in Htaint; simpl in *. *)
 (*      destruct_matches_in_hyp Htaint; simpl in *; auto. *)
 (*      rewrite orb_true_r in Htaint; simpl in *; auto. *)
 (*    Qed. *)

 (*    Ltac solve_taint_safety_read_only_action IH := *)
 (*      match goal with *)
 (*      | H: _ && _ = true |- _ => rewrite andb_true_iff in H; propositional *)
 (*      | H: true = _ && _ |- _ => symmetry in H *)
 (*      | H: oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ => *)
 (*          match b with *)
 (*          | true => fail *)
 (*          | _ => let H' := fresh in *)
 (*                assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto); *)
 (*                rewrite H' in H; subst *)
 (*          end *)
 (*      | H: oraat_interp_action ?sigma ?int_fns ?struct_defs ?fuel ?r ?r_acc ?ext_fn_log true ?gamma ?_action = (true, Some (_, ?_r', _)), *)
 (*        Htaint0 : read_only_taint ?_taint_env, *)
 (*        Htaint1 : read_only_taint ?_env, *)
 (*        Hsuccess : taint_action ?int_fns ?_fuel2 ?_taint_env ?_action = Success (Some ?_env) *)
 (*        |- _ => *)
 (*          eapply IH with (env := _taint_env) (env' := _env) (fuel2 := _fuel2) in H ; auto *)
 (*      | H1: taint_env_le ?t ?env, *)
 (*        H2: taint_env_le ?env ?t' |- _ => *)
 (*          lazymatch goal with *)
 (*          | H : taint_env_le t t' |- _ => fail *)
 (*          | |- _ => (pose proof (taint_env_le_trans _ _ _ H1 H2)) *)
 (*          end *)
 (*      | H: taint_action _ _ ?taint_env _ = Success (Some ?taint_env') |- _ => *)
 (*          lazymatch goal with *)
 (*          | H': taint_env_le taint_env taint_env' |- _ => fail *)
 (*          | _ => (pose proof (taint_action_generalizes_taint _ _ _ _ _ H)) *)
 (*          end *)
 (*      | H : taint_env_le ?env ?env', *)
 (*        H1: read_only_taint ?env' |- _ => *)
 (*          lazymatch goal with *)
 (*          | H2: read_only_taint env |- _ => fail *)
 (*          | |- _ => pose proof (read_only_taint_le _ _ H1 H) *)
 (*          end *)
 (*      | H : read_only_taint (merge_taint_env ?env1 ?env2) |- _ => *)
 (*          lazymatch goal with *)
 (*          | H2: read_only_taint env1 |- _ => fail *)
 (*          | |- _ => pose proof (read_only_taint_merge_l_invert _ _ H) *)
 (*          end *)
 (*      | H : read_only_taint (merge_taint_env ?env1 ?env2) |- _ => *)
 (*          lazymatch goal with *)
 (*          | H2: read_only_taint env2 |- _ => fail *)
 (*          | |- _ => pose (read_only_taint_merge_r_invert _ _ H) *)
 (*          end *)
 (*      | H: read_only_taint (set_reg_taint _ _ set_taint_write1) |- _ => *)
 (*          apply not_read_only_set_write1 in H; contradiction *)
 (*      | H: read_only_taint (set_reg_taint _ _ set_taint_write0) |- _ => *)
 (*          apply not_read_only_set_write0 in H; contradiction *)
 (*      | |- _ /\ _ => split *)
 (*      | |- _ => progress (simpl in *;simplify;propositional; auto with solve_taint) *)
 (*      end. *)


 (*    Lemma taint_safety_read_only_function': *)
 (*      forall fuel1 fuel2 r r_acc gamma gamma' action st' env env' v ext_fn_log ext_fn_log', *)
 (*      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc ext_fn_log true gamma action = (true, Some (gamma', st', ext_fn_log', v)) -> *)
 (*      read_only_taint env -> *)
 (*      taint_action int_fns fuel2 env action = Success (Some env') -> *)
 (*      read_only_taint env' -> *)
 (*      st' = r_acc. *)
 (*    Proof. *)
 (*      induction fuel1; *)
 (*        intros fuel2 r r_acc gamma gamma' action st' env env' v ext_fn_log ext_fn_log' *)
 (*               Horaat Htaint Hsuccess; simpl in *; simplify; subst. *)
 (*      destruct fuel2; [simpl in *; discriminate | ]. *)
 (*      destruct action; cbn in *; simplify_tupless; propositional; *)
 (*        destruct_match_pairs; unfold res_opt_bind, get_fn_arg_and_body'', __debug__ in *; repeat solve_taint_safety_action IHfuel1; destruct_all_matches; simplify; repeat solve_taint_safety_read_only_action IHfuel1. *)
 (*    Qed. *)


 (*    Lemma taint_safety_read_only_function: *)
 (*      forall fuel1 fuel2 r r_acc gamma gamma' action st' env v ext_fn_log ext_fn_log', *)
 (*      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc ext_fn_log true gamma action = (true, Some (gamma', st', ext_fn_log', v)) -> *)
 (*      taint_action int_fns fuel2 SortedRegEnv.empty action = Success (Some env) -> *)
 (*      read_only_taint env -> *)
 (*      st' = r_acc. *)
 (*    Proof. *)
 (*      intros. eapply taint_safety_read_only_function' with (env := SortedRegEnv.empty) in H; eauto. *)
 (*      apply empty_taint_read_only. *)
 (*    Qed. *)
 (*  End ReadOnly. *)
End TaintSafety.
  Hint Immediate taint_env_corresponds_set_read0 : solve_taint.
  Hint Immediate taint_env_corresponds_set_read1 : solve_taint.
  Hint Immediate taint_env_corresponds_set_write0 : solve_taint.
  Hint Immediate taint_env_corresponds_set_write1 : solve_taint.
  Hint Immediate taint_env_corresponds_merge_l : solve_taint.
  Hint Immediate taint_env_corresponds_merge_r : solve_taint.
  Hint Immediate taint_env_le_refl : solve_taint.
  Hint Immediate taint_env_le_refl : solve_taint.
  Hint Immediate taint_env_corresponds_to_state_update__empty: solve_taint.
  Hint Immediate taint_env_corresponds_to_state_update__unchanged: solve_taint.
  Hint Immediate merge_taints_empty_l: solve_taint.
  Hint Immediate merge_taints_empty_r: solve_taint.
  Hint Resolve taint_le_empty_l : solve_taint.

(* Section ReadOnlyFunction. *)
(*   Context (ext_sigma: @ext_sigma_t N). *)
(*   Context (int_fns: @int_fn_env_t N (@action N)). *)
(*   Context (struct_defs: @struct_env_t N). *)

(*   Definition read_only_taintb (env: taint_env_t) : bool := *)
(*     forallb (fun '(_, v) => negb (taint_write0 v|| taint_write1 v)) (SortedRegEnv.to_list env). *)

(*   Lemma read_only_taintb_iff: *)
(*     forall env, *)
(*     read_only_taintb env = true <-> *)
(*     read_only_taint env. *)
(*   Proof. *)
(*     unfold read_only_taintb, read_only_taint. intros. *)
(*     rewrite forallb_forall. *)
(*     split. *)
(*     - intros. repeat destruct_match; subst; auto. *)
(*       rewrite<-SortedRegEnv.In_to_list in Heqo. *)
(*       specialize H with (1 := Heqo). destruct_match_pairs; simplify. *)
(*       rewrite Heqb in H. discriminate. *)
(*     - intros. destruct x. rewrite SortedRegEnv.In_to_list in H0. *)
(*       specialize (H t). simpl_match. destruct_matches_in_hyp H; auto. *)
(*   Qed. *)

(*   Lemma read_only_function_safety: *)
(*     forall fuel1 fuel2 fuel3 r r_acc gamma action env opt_res ext_fn_log , *)
(*     oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc ext_fn_log true gamma action = (true, opt_res) -> *)
(*     taint_action int_fns fuel2 SortedRegEnv.empty action = Success (Some env) -> *)
(*     read_only_taintb env = true -> *)
(*     action_contains_fail int_fns fuel3 action = Success false -> *)
(*     match opt_res with *)
(*     | Some (_, st', _, _) => st' = r_acc *)
(*     | None => False *)
(*     end. *)
(*   Proof. *)
(*     intros * Horaat Htaint Hread Hfail. *)
(*     repeat destruct_match; subst. *)
(*     - eapply taint_safety_read_only_function; eauto. *)
(*       apply read_only_taintb_iff. assumption. *)
(*     - eapply action_fail_safety; eauto. *)
(*   Qed. *)

(*   Lemma read_only_function_safety': *)
(*     forall fuel1 r r_acc gamma action env opt_res ext_fn_log, *)
(*     oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc ext_fn_log true gamma action = (true, opt_res) -> *)
(*     taint_action int_fns (safe_fuel int_fns action) *)
(*                          SortedRegEnv.empty action = Success (Some env) -> *)
(*     read_only_taintb env = true -> *)
(*     action_contains_fail int_fns (safe_fuel int_fns action)  action = Success false -> *)
(*     match opt_res with *)
(*     | Some (_, st', _, _) => st' = r_acc *)
(*     | None => False *)
(*     end. *)
(*   Proof. *)
(*     intros; eapply read_only_function_safety; eauto. *)
(*   Qed. *)

(* End ReadOnlyFunction. *)

Section TaintRec.
  Context (ext_sigma: @ext_sigma_t N).
  Context (int_fns: @int_fn_env_t N (@action N)).
  Context (struct_defs: @struct_env_t N).

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
    destruct_with_eqn (beq_dec idx reg); simplify; subst.
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
    destruct_with_eqn (beq_dec idx reg); simplify; subst.
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
    destruct_with_eqn (beq_dec idx reg); simplify; subst;
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
    destruct_with_eqn (beq_dec idx reg); simplify; subst;
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


  Ltac solve_taint_safety_rec IH :=
    match goal with
    | H: oraat_interp_action _ _ _ _ _ _ _ true _ ?action = (true, _),
      H1: taint_action_rec _ _ ?action = _ |- _ =>
        apply IH with (2 := H1) in H; auto
    | H: oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
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
    forall fuel1 fuel2 r r_acc gamma action gamma' st' res env' ext_fn_log ext_fn_log',
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r r_acc ext_fn_log true
         gamma action = (true, Some (gamma', st', ext_fn_log', res)) ->
      taint_action_rec int_fns fuel2 action = Success (Some env') ->
      taint_env_corresponds_to_state_update r_acc st' env'.
  Proof.
    induction fuel1;
      intros fuel2 r r_acc gamma action gamma' st' res env' ext_fn_log ext_fn_log'
             Horaat Htaint; simpl in *; simplify; subst.
    destruct fuel2; [simpl in *; discriminate | ].
    destruct action; cbn in *; simplify_tupless; propositional;
      destruct_match_pairs; unfold res_opt_bind, get_fn_arg_and_body'', __debug__, get_reg in *;
      destruct_all_matches; repeat solve_taint_safety_rec IHfuel1.
Search taint_env_corresponds_to_state_update__empty.
    + rewrite<-merge_taint_env_assoc. rewrite merge_taint_env_comm.
      apply taint_env_corresponds_merge_r. auto.
    + rewrite merge_taint_env_comm with (env1 := t0).
      rewrite<-merge_taint_env_assoc.
      apply taint_env_corresponds_merge_l. auto.
  Qed.

End TaintRec.

Section TaintEquivalence.
  Context (ext_sigma: @ext_sigma_t N).
  Context (int_fns: @int_fn_env_t N (@action N)).
  Context (struct_defs: @struct_env_t N).

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
  destruct_with_eqn (beq_dec reg reg0); simplify.
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
  destruct_with_eqn (beq_dec reg idx); simplify.
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
  destruct_with_eqn (beq_dec reg idx); simplify.
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
  destruct_with_eqn (beq_dec reg idx); simplify.
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
  destruct_with_eqn (beq_dec reg idx); simplify.
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
  destruct_with_eqn (beq_dec reg idx); simplify.
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
  destruct_with_eqn (beq_dec reg idx); simplify.
  - rewrite SortedRegEnv.update_correct_eq in H. destruct_match; propositional; simpl in *.
    repeat rewrite orb_true_r in *. destruct_match ;auto.
  - rewrite SortedRegEnv.update_correct_neq in H by auto. destruct_match; propositional.
Qed.

Ltac solve_oraat_interp_action_taint_eq IH :=
  match goal with
  | H : oraat_interp_action _ _ _ _ _ _ _ true _ ?action = (true, Some(_, ?st', _)),
    H1: taint_action_rec _ _ ?action = Success (Some _) |- _ =>
      pose_fresh (taint_safety_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H1)
  | H: oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
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
  | H1: oraat_interp_action _ _ _ _ ?r1 ?r_acc1 _ _ ?gamma ?action = (true, _),
    H2: oraat_interp_action _ _ _ _ ?r2 ?r_acc2 _ _ ?gamma ?action = (true, _),
    H3: taint_action_rec _ _ ?action = Success (Some ?taint_env),
    H4: taint_equiv_read0_state ?r1 ?r2 ?taint_env,
    H5: taint_equiv_acc_state ?r_acc1 ?r_acc2 ?taint_env
    |- _ =>
      eapply IH with (2 := H2) (3 := H3) (4 := H4) (5 := H5) in H1; clear H2
  | H1: oraat_interp_action _ _ _ _ ?r1 ?r_acc1 _ _ ?gamma ?action = (true, _),
    H3: taint_action_rec _ _ ?action = Success (Some ?taint_env),
    H4: taint_equiv_read0_state ?r1 ?r2 ?taint_env,
    H5: taint_equiv_acc_state ?r_acc1 ?r_acc2 ?taint_env,
    H2: oraat_interp_action _ _ _ _ ?r2 ?r_acc2 _ _ ?gamma ?action = (_, _)
    |- _ =>
      eapply IH with (5 := H2) (2 := H3) (3 := H4) (4 := H5) in H1
   | H: success_or_default (Success _) _ = _ |- _ => simpl in H
   | H: Datatypes.length _ = 1 |- _ => progress (rewrite H in *; simpl in *)
  | |- _ => progress (simpl; simplify; propositional; auto with solve_taint)
  end.

  Lemma oraat_interp_action_taint_eq':
    forall fuel1 fuel2 fuel3 r1 r2 r_acc1 r_acc2 safe1 safe2 gamma action opt_res1 opt_res2 taint_env ext_fn_log1 ext_fn_log2,
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r1 r_acc1 ext_fn_log1 safe1 gamma action = (true, opt_res1) ->
      oraat_interp_action ext_sigma int_fns struct_defs fuel2 r2 r_acc2 ext_fn_log2 safe2 gamma action = (true, opt_res2) ->
      taint_action_rec int_fns fuel3 action = Success (Some taint_env) ->
      taint_equiv_read0_state r1 r2 taint_env ->
      taint_equiv_acc_state r_acc1 r_acc2 taint_env -> (* taint_equiv_read1 not enough for if branch *)
      match opt_res1, opt_res2 with
      | Some (gamma1', st1', ext_fn_log1', v1), Some (gamma2', st2', ext_fn_log2', v2) =>
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
      destruct_all_matches; repeat solve_oraat_interp_action_taint_eq IHfuel1; try congruence.
  Qed.

  Lemma oraat_interp_action_taint_eq:
    forall fuel1 fuel2 fuel3 r1 r2 r_acc1 r_acc2 safe1 safe2 gamma action opt_res1 opt_res2 taint_env ext_fn_log1 ext_fn_log2,
      oraat_interp_action ext_sigma int_fns struct_defs fuel1 r1 r_acc1 ext_fn_log1 safe1 gamma action = (true, opt_res1) ->
      oraat_interp_action ext_sigma int_fns struct_defs fuel2 r2 r_acc2 ext_fn_log2 safe2 gamma action = (true, opt_res2) ->
      taint_action int_fns fuel3 SortedRegEnv.empty action = Success (Some taint_env) ->
      taint_equiv_read0_state r1 r2 taint_env ->
      taint_equiv_acc_state r_acc1 r_acc2 taint_env ->
      match opt_res1, opt_res2 with
      | Some (_, st1', _, v1), Some (_, st2', _, v2) =>
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
Section TODO_ORAAT_MOVE.
  Context (ext_fns: @ext_sigma_t N).
  Context (int_fns: @int_fn_env_t N (@action N)).
  Context (struct_defs: @struct_env_t N).

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
  Hint Resolve ext_fn_taint_env_subset_refl: solve_taint.

  Lemma oraat_interp_action_gamma_vars_eq:
    forall fuel r r_acc is_safe gamma action gamma' st' v ext_fn_log ext_fn_log' ,
    oraat_interp_action ext_fns int_fns struct_defs fuel r r_acc ext_fn_log is_safe gamma action = (true, Some (gamma', st', ext_fn_log', v)) ->
    gamma_vars_eq gamma gamma'.
  Proof.
    induction fuel; [ discriminate | ].
    intros * Horaat.
    destruct action; cbn in *; destruct_all_matches;
      repeat match goal with
             | |- _ => simplify_oraat_interp_action_safety
             | H: oraat_interp_action _ _ _ _ _ _ _ _ _ _ = (true, _) |- _ =>
                 apply IHfuel in H
             | H: _ && _ = true |- _ => rewrite andb_true_iff in H
             | |- _ => progress (propositional; simplify; eauto with solve_gamma)
             end.
    - eapply gamma_vars_eq_trans; eauto with solve_gamma.
  Qed.

  Fixpoint modular_schedule_does_not_conflict'
    {rule_name_t: Type} (rules: rule_name_t -> rule) (mod_sched: list scheduler) acc: bool :=
    match mod_sched with
    | [] => let '(b, _, _) := acc in b
    | s::ss =>
       let '(is_safe, taint_acc, ext_acc) := acc in
       match taint_schedule int_fns rules taint_empty s,
             ext_fn_taint_schedule int_fns rules SortedExtFnEnv.empty s with
       | Success (Some env), Success (Some ext_taint) =>
           if does_not_conflict taint_acc env &&
              negb (ext_fn_taint_env_conflicts ext_acc ext_taint) then
             modular_schedule_does_not_conflict' rules ss
               (is_safe, merge_taint_env env taint_acc, merge_ext_fn_taint_env ext_acc ext_taint)
           else
             false
       | _, _ => false
       end
    end.

     Definition modular_schedule_does_not_conflict
      {rule_name_t: Type} (rules: rule_name_t -> rule) (mod_sched: list scheduler) : bool :=
       modular_schedule_does_not_conflict' rules mod_sched (true, taint_empty, SortedExtFnEnv.empty).

    Lemma interp_modular_schedule'_cons:
      forall {rule_name_t: Type} (rules: rule_name_t -> rule)
        st ext_log sched scheds,
        interp_modular_schedule' ext_fns int_fns struct_defs rules st ext_log (sched::scheds) =
          let/res log' := interp_scheduler ext_fns int_fns struct_defs  st rules sched in
          interp_modular_schedule' ext_fns  int_fns struct_defs rules
                                   (commit_update st log'.(Log__koika))
                                   (ext_log_app log'.(Log__ext) ext_log)
                                   scheds.
    Proof.
      intros; auto.
    Qed.

    Lemma ext_fn_taint_action_subset:
      forall fuel int_fns base_env rule res_env ,
        ext_fn_taint_action int_fns fuel base_env rule = Success (Some res_env) ->
        ext_fn_taint_env_subset base_env res_env.
    Proof.
      intros. eapply ext_fn_taint_action_subset_correct; eauto.
    Qed.

    Lemma ext_fn_taint_rule_subset:
      forall int_fns base_env rule res_env,
        ext_fn_taint_rule int_fns base_env rule = Success (Some res_env) ->
        ext_fn_taint_env_subset base_env res_env.
    Proof.
      intros. eapply ext_fn_taint_action_subset; eauto.
    Qed.
Lemma ext_fn_taint_env_approximates_log_app_l:
  forall log1 log2 env,
  ext_fn_taint_env_approximates_log env (ext_log_app log1 log2) ->
  ext_fn_taint_env_approximates_log env log1.
Proof.
  intros. consider ext_fn_taint_env_approximates_log. consider ext_log_app.
  intros. consider @is_some. specialize (H fn). propositional.
  eapply H. rewrite SortedExtFnEnv.opt_get_mapV in *.
  rewrite SortedExtFnEnv.opt_get_zip_default in *.
  repeat simpl_match.
  destruct_match; auto.
  - repeat destruct_match; eauto.
  - destruct v; eauto.
Qed.
Lemma ext_fn_taint_env_approximates_log_app_r:
  forall log1 log2 env,
  ext_fn_taint_env_approximates_log env (ext_log_app log1 log2) ->
  ext_fn_taint_env_approximates_log env log2.
Proof.
  intros. consider ext_fn_taint_env_approximates_log. consider ext_log_app.
  intros. consider @is_some. specialize (H fn). propositional.
  eapply H. rewrite SortedExtFnEnv.opt_get_mapV in *.
  rewrite SortedExtFnEnv.opt_get_zip_default in *.
  repeat simpl_match.
  destruct_match; auto.
  - repeat destruct_match; eauto.
  - destruct v; eauto.
Qed.
Lemma ext_fn_taint_env_approximates_log_app:
  forall env log1 log2,
  ext_fn_taint_env_approximates_log env log1  ->
  ext_fn_taint_env_approximates_log env log2 ->
  ext_fn_taint_env_approximates_log env (ext_log_app log1 log2).
Proof.
  consider ext_fn_taint_env_approximates_log. consider ext_log_app. consider @is_some.
  intros.
  rewrite SortedExtFnEnv.opt_get_mapV in *.
  rewrite SortedExtFnEnv.opt_get_zip_default in *.
  propositional.
  bash_destruct H2; eauto.
Qed.
Hint Resolve ext_fn_taint_env_approximates_log_merge_r : solve_taint.
Hint Resolve ext_fn_taint_env_approximates_log_merge_l : solve_taint.
Hint Resolve ext_fn_taint_env_approximates_log_update : solve_taint.
    Lemma ext_fn_taint_action_correct:
      forall struct_defs ext_fns int_fns fuel1 rule base_env st sched_log res_env fuel2 max_fn_depth gamma action_log gamma' log' bv',
        ext_fn_taint_action int_fns fuel1 base_env rule = Success (Some res_env) ->
        ext_fn_taint_env_approximates_log base_env ((Log__ext action_log)) ->
        interp_action ext_fns int_fns struct_defs fuel2 max_fn_depth st gamma sched_log action_log rule = Success (Some (gamma', log', bv')) ->
        ext_fn_taint_env_approximates_log res_env (Log__ext log').
    Proof.
      induction fuel1; simpl; auto.
      - discriminate.
      - destruct fuel2; intros *; destruct rule; propositional; simpl in *; consider @res_opt_bind; simplify; eauto.
        all: repeat match goal with
        | H: ext_fn_taint_env_approximates_log _ (ext_log_app _ _) |- _ =>
            pose_fresh (ext_fn_taint_env_approximates_log_app_l _ _ _ H0)
        | H: ext_fn_taint_env_approximates_log _ (ext_log_app _ _) |- _ =>
            pose_fresh (ext_fn_taint_env_approximates_log_app_r _ _ _ H0)
        | H1: ext_fn_taint_action _ _ _ ?rule = Success (Some _),
          H2: ext_fn_taint_env_approximates_log _ (ext_log_app (Log__ext ?action_log) (Log__ext ?sched_log)) ,
          H3: interp_action _ _ _ _ _ ?st ?gamma ?sched_log ?action_log ?rule = Success (Some _) |- _ =>
            pose_fresh (IHfuel1 _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3)
        | H: ext_fn_taint_action _ _ _ ?rule = Success (Some _) |- _ =>
            pose_fresh (ext_fn_taint_action_subset _ _ _ _ _ H)
        | H: ext_fn_taint_env_approximates_log ?env ?log,
          H1: ext_fn_taint_env_subset ?env ?env' |- _ =>
            pose_fresh (ext_fn_taint_env_approximates_log_subset _ _ _ H H1)
        | H1: ext_fn_taint_action _ _ ?base ?rule = Success (Some _),
          H3: interp_action _ _ _ _ _ ?st ?gamma ?sched_log ?action_log ?rule = Success (Some _),
          H4: ext_fn_taint_env_approximates_log ?base (Log__ext ?sched_log),
          H5: ext_fn_taint_env_approximates_log ?base (Log__ext ?action_log)
          |- _ =>
            pose_fresh (IHfuel1 _ _ _ _ _ _ _ _ _ _ _ _ H1 (ext_fn_taint_env_approximates_log_app _ _ _ H5 H4) H3)
        | H: context[match _ with | _ => _ end] |- _ => bash_destruct H
        | _ => progress (simplify; eauto with solve_taint)
        end; eauto.
        { simpl. eapply IHfuel1; eauto. }
        { simpl. eapply IHfuel1; eauto. }
    Qed.
Lemma ext_fn_taint_env_approximates_log_empty':
  forall env,
  ext_fn_taint_env_approximates_log env SortedExtFnEnv.empty.
Proof.
  consider ext_fn_taint_env_approximates_log. intros *.
  rewrite SortedExtFnEnv.opt_get_empty.
  consider @is_some. propositional. discriminate.
Qed.

    Lemma ext_fn_taint_rule_correct:
      forall struct_defs ext_fns int_fns rule base_env st sched_log res_env log,
        ext_fn_taint_rule int_fns base_env rule = Success (Some res_env) ->
        interp_rule ext_fns int_fns struct_defs st sched_log rule = Success (Some log) ->
        (* ext_fn_taint_env_approximates_log base_env (Log__ext sched_log) -> *)
        ext_fn_taint_env_approximates_log res_env (Log__ext log).
    Proof.
      consider ext_fn_taint_rule. consider interp_rule.
      intros. specialize ext_fn_taint_action_correct with (1 := H).
      intros.
      bash_destruct H0; simplify; simpl.
      - specialize H1 with (action_log := Log_empty) (sched_log := sched_log). simpl in H1.
        eapply H1; eauto.
        apply ext_fn_taint_env_approximates_log_empty'.
    Qed.

    Lemma ext_fn_taint_schedule_empty_correct':
      forall {rule_name_t: Type} schedule (rules: rule_name_t -> rule) base_env
        st log' sched_log res_env fn,
        ext_fn_taint_schedule int_fns rules base_env schedule = Success (Some res_env) ->
        SortedExtFnEnv.opt_get res_env fn = None ->
        ext_fn_taint_env_approximates_log base_env (Log__ext sched_log) ->
        interp_scheduler' ext_fns int_fns struct_defs st rules schedule sched_log = Success log' ->
        SortedExtFnEnv.opt_get (Log__ext log') fn = None.
    Proof.
      induction schedule.
      - intros * hsched hres htaint hlog. simpl in *. simplify. specialize (htaint fn).
        destruct_with_eqn (SortedExtFnEnv.opt_get (Log__ext log') fn); consider @is_some; simpl in *; propositional.
        assert_pre_and_specialize htaint; eauto. congruence.
      - intros * hsched hres htaint hlog. simpl in *. simplify.
        unfold res_opt_bind in *. bash_destruct hsched.
        bash_destruct hlog.
        + specialize ext_fn_taint_rule_correct with (1 := Heqr1) (2 := Heqr0) ; intros henv'.
          specialize IHschedule with (1 := hsched) (2 := hres) (4 := hlog).
          apply IHschedule. consider ext_fn_taint_env_approximates_log. simpl.
          intros * happ. consider @is_some. propositional. consider ext_log_app.
          rewrite SortedExtFnEnv.opt_get_mapV in happ0. simplify.
          rewrite SortedExtFnEnv.opt_get_zip_default in Heqo.
          destruct_matches_in_hyp Heqo; simplify; eauto.
          specialize ext_fn_taint_rule_subset with (1 := Heqr1).
          consider ext_fn_taint_env_subset. eauto.
        + eapply IHschedule with (4 := hlog); auto.
          * eauto.
          * auto.
          * apply ext_fn_taint_rule_subset in Heqr1.
            eapply ext_fn_taint_env_approximates_log_subset; eauto.
    Qed.

    Lemma ext_fn_taint_schedule_empty_correct:
      forall {rule_name_t: Type} (rules: rule_name_t -> rule)
        st log' schedule res_env fn,
        ext_fn_taint_schedule int_fns rules SortedExtFnEnv.empty schedule = Success (Some res_env) ->
        interp_scheduler ext_fns int_fns struct_defs st rules schedule = Success log' ->
        SortedExtFnEnv.opt_get res_env fn = None ->
        SortedExtFnEnv.opt_get (Log__ext log') fn = None.
    Proof.
      consider interp_scheduler. intros.
      eapply ext_fn_taint_schedule_empty_correct' in H; eauto.
      apply ext_fn_taint_env_approximates_log_empty.
    Qed.

    Lemma interp_scheduler'_schedule_app:
      forall {rule_name_t: Type} (rules: rule_name_t -> rule)
        ext_fns int_fns struct_defs st ys xs x log,
        interp_scheduler' ext_fns int_fns struct_defs st rules
          (fold_left (fun acc s : scheduler => schedule_app acc s) ys (x |> xs)) log =
          interp_scheduler' ext_fns int_fns struct_defs st rules
            (x |> (fold_left (fun acc s : scheduler => schedule_app acc s) ys (xs))) log.
    Proof.
      induction ys; simpl; auto.
    Qed.

    Lemma interp_scheduler'_concatenate:
      forall {rule_name_t: Type} (rules: rule_name_t -> rule) x ext_fns int_fns struct_defs st y log,
        interp_scheduler' ext_fns int_fns struct_defs st rules (concatenate_modular_schedule (x::y)) log =
          let/res log' := interp_scheduler' ext_fns int_fns struct_defs st rules x log  in
          interp_scheduler' ext_fns int_fns struct_defs st rules (concatenate_modular_schedule y) log'.
    Proof.
      induction x; simpl in *; auto. intros.
      cbn.
      rewrite interp_scheduler'_schedule_app. simpl.
      destruct_match; auto. destruct_match; auto.
      - rewrite<-IHx. reflexivity.
      - rewrite<-IHx. reflexivity.
    Qed.
Lemma ext_log_app_log_app:
  forall (log1 log2: Log_t),
  ext_log_app (Log__ext log1) (Log__ext log2) = Log__ext (Log_app log1 log2).
Proof.
  reflexivity.
Qed.
Lemma latest_write_logentry_app:
  forall l1 l2,
  (match lwrite1 l2 with
   | Some v => lwrite0 l1 = None
   | _ => True
   end) ->
  latest_write (logentry_app l1 l2) = match latest_write l1 with
                                      | Some v => Some v
                                      | None => latest_write l2
                                      end.
Proof.
  consider latest_write. consider logentry_app. simpl.
  intros. destruct_with_eqn (lwrite1 l1); simpl; auto.
  destruct_match; auto.
  - destruct_with_eqn (lwrite0 l1); auto. discriminate.
  - destruct_match; simpl; auto.
    + destruct_match; simpl in *; auto. simpl_match. auto.
    + destruct_match; simpl in *; auto. simpl_match; auto.
Qed.

Record wf_koika_sched_log_pair log1 log2 :=
  { wf_write0: forall reg, LE_may_write0 (log_get (Log__koika log2) reg) = false ->
                      lwrite0 (log_get (Log__koika log1) reg) = None;
    wf_write1: forall reg, LE_may_write1 (log_get (Log__koika log2) reg) = false ->
                      lwrite1 (log_get (Log__koika log1) reg) = None;
    wf_read1: forall reg, LE_may_read1 (log_get (Log__koika log2) reg) = false ->
                     lread1 (log_get (Log__koika log1) reg) = false;
    wf_read0: forall reg, LE_may_read0 (log_get (Log__koika log2) reg) = false ->
                     lread0 (log_get (Log__koika log1) reg) = false;
    wf_ext: forall fn, ext_log_can_call (Log__ext log2) fn = false ->
                  ext_log_can_call (Log__ext log1) fn = true
  }.

Lemma commit_update_commit_update:
  forall log1 log2 st,
  wf_koika_sched_log_pair log2 log1 ->
  commit_update (commit_update st (Log__koika log1)) (Log__koika log2) = commit_update st (log_app (Log__koika log2) (Log__koika log1)).
Proof.
  consider commit_update. consider log_app. intros * hwf. consider log_get.
  destruct hwf.
  apply SortedRegEnv.env_ext. intros.
  specialize (wf_write2 reg). consider log_get.
  repeat rewrite SortedRegEnv.opt_get_map.
  destruct_match; auto.
  rewrite SortedRegEnv.opt_get_mapV.
  rewrite SortedRegEnv.opt_get_zip_default.
  destruct_match.
  - destruct_match.
    + destruct_match; auto.
      * consider latest_write. simpl. destruct_matches_in_hyp Heqo1; simplify; auto.
        simpl. destruct_match; auto.
        assert_pre_and_specialize wf_write2.
        { consider LE_may_write0. repeat simpl_match. repeat destruct_match; auto. }
        discriminate.
      * rewrite logentry_app_empty_r. simpl_match. auto.
    + destruct_match.
      * consider latest_write; simpl.
        destruct_match; simpl.
        { bash_destruct Heqo1; auto. }
        { bash_destruct Heqo1; simpl; auto. }
      * simpl in *. rewrite logentry_app_empty_r. simpl_match. auto.
  - simpl. destruct_match; auto.
Qed.
Lemma wf_koika_sched_log_pair_empty_l:
  forall log, wf_koika_sched_log_pair Log_empty log.
Proof.
  intros. constructor; auto.
Qed.
Lemma Log_app_empty_l:
  forall log, log = Log_app Log_empty log.
Proof.
  intros; unfold Log_app. simpl. rewrite log_app_empty_l. rewrite ext_log_app_empty_l.
  destruct log; reflexivity.
Qed.
Lemma opt_or_assoc:
  forall {A} (x y z: option A),
  opt_or x (opt_or y z) = opt_or (opt_or x y) z.
Proof.
  consider @opt_or. intros. repeat destruct_match; auto.
Qed.

Lemma logentry_app_assoc:
  forall l1 l2 l3,
  logentry_app l1 (logentry_app l2 l3) = logentry_app (logentry_app l1 l2) l3.
Proof.
  intros. consider logentry_app. simpl. repeat rewrite orb_assoc. repeat rewrite opt_or_assoc. auto.
Qed.
Hint Rewrite @SortedExtFnEnv.opt_get_mapV : solve_taint.
Hint Rewrite @SortedExtFnEnv.opt_get_map : solve_taint.
Hint Rewrite @SortedExtFnEnv.opt_get_zip_default : solve_taint.
Hint Rewrite logentry_app_empty_r : solve_taint.
Hint Rewrite logentry_app_empty_l : solve_taint.
Hint Rewrite logentry_app_assoc : solve_taint.
Hint Rewrite @opt_or_None_r: solve_taint.
Lemma log_app_assoc:
  forall l1 l2 l3,
  log_app l1 (log_app l2 l3) = log_app (log_app l1 l2) l3.
Proof.
  intros. consider log_app. apply SortedRegEnv.env_ext.
  intros; autorewrite with solve_taint; repeat destruct_match; autorewrite with solve_taint; auto.
Qed.
Lemma ext_log_can_call_app_r:
  forall log1 log2 fn,
  ext_log_can_call (ext_log_app log1 log2) fn = true ->
  ext_log_can_call log1 fn = true.
Proof.
  consider ext_log_can_call. consider ext_log_app. intros *.
  autorewrite with solve_taint. repeat destruct_match; auto.
Qed.
Lemma LE_may_read0_log_get_app_r:
  forall log1 log2 idx,
  LE_may_read0 (log_get (log_app (Log__koika log1) (Log__koika log2)) idx) = true ->
  LE_may_read0 (log_get (Log__koika log1) idx) = true.
Proof.
  unfold log_app, log_get. intros *. consider LE_may_read0. consider logentry_app.
  autorewrite with solve_taint. repeat destruct_match; simpl in *; auto; try discriminate.
Qed.

Lemma LE_may_read0_log_get_app_l:
  forall log1 log2 idx,
  LE_may_read0 (log_get (log_app (Log__koika log1) (Log__koika log2)) idx) = true ->
  LE_may_read0 (log_get (Log__koika log2) idx) = true.
Proof.
  unfold log_app, log_get. intros *. consider LE_may_read0. consider logentry_app.
  autorewrite with solve_taint. repeat destruct_match; simpl in *; auto; try discriminate.
  - destruct (lwrite0 l); simpl in *; discriminate.
  - destruct (lwrite0 l); simpl in *; try discriminate.
    destruct (lwrite1 l); simpl in *; try discriminate.
Qed.
Lemma LE_may_read1_log_get_app_l:
  forall log1 log2 idx,
  LE_may_read1 (log_get (log_app (Log__koika log1) (Log__koika log2)) idx) = true ->
  LE_may_read1 (log_get (Log__koika log2) idx) = true.
Proof.
  unfold log_app, log_get. intros *. consider LE_may_read1. consider logentry_app.
  autorewrite with solve_taint. repeat destruct_match; simpl in *; auto; try discriminate.
  - destruct (lwrite1 l); simpl in *; discriminate.
Qed.

Lemma LE_may_read1_log_get_app_r:
  forall log1 log2 idx,
  LE_may_read1 (log_get (log_app (Log__koika log1) (Log__koika log2)) idx) = true ->
  LE_may_read1 (log_get (Log__koika log1) idx) = true.
Proof.
  unfold log_app, log_get. intros *. consider LE_may_read1. consider logentry_app.
  autorewrite with solve_taint. repeat destruct_match; simpl in *; auto; try discriminate.
Qed.
Lemma LE_may_write0_log_get_app_r:
  forall log1 log2 idx,
  LE_may_write0 (log_get (log_app (Log__koika log1) (Log__koika log2)) idx) = true ->
  LE_may_write0 (log_get (Log__koika log1) idx) = true.
Proof.
  unfold log_app, log_get. intros *. consider LE_may_write0. consider logentry_app.
  autorewrite with solve_taint. repeat destruct_match; simpl in *; auto; try discriminate.
Qed.
Lemma LE_may_write1_log_get_app_r:
  forall log1 log2 idx,
  LE_may_write1 (log_get (log_app (Log__koika log1) (Log__koika log2)) idx) = true ->
  LE_may_write1 (log_get (Log__koika log1) idx) = true.
Proof.
  unfold log_app, log_get. intros *. consider LE_may_write1. consider logentry_app.
  autorewrite with solve_taint. repeat destruct_match; simpl in *; auto; try discriminate.
Qed.

Lemma r_get_reg_commit_update_success:
  forall st idx log s,
  r_get_reg st idx = Success s ->
  match r_get_reg (commit_update st log) idx with
  | Success _ => True
  | Failure _ => False
  end.
Proof.
  consider r_get_reg. consider commit_update.
  intros. rewrite SortedRegEnv.opt_get_map in *. bash_destruct H. auto.
Qed.
Lemma lwrite0_log_app_None_r:
  forall log1 log2 idx,
  lwrite0 (log_get (log_app log1 log2) idx) = None ->
  lwrite0 (log_get log1 idx) = None.
Proof.
  intros *; unfold log_get, log_app, logentry_app; autorewrite with solve_taint; repeat destruct_match; simpl; auto.
  - destruct_with_eqn (lwrite0 l); simpl in *; auto.
  - rewrite opt_or_None_r. auto.
Qed.
Lemma lwrite0_log_app_None_l:
  forall log1 log2 idx,
  lwrite0 (log_get (log_app log1 log2) idx) = None ->
  lwrite0 (log_get log2 idx) = None.
Proof.
  intros *; unfold log_get, log_app.
  rewrite SortedRegEnv.opt_get_mapV. rewrite SortedRegEnv.opt_get_zip_default.
  destruct_match; auto. consider @opt_or; repeat destruct_match; simpl; auto.
  - destruct_with_eqn (lwrite0 l); simpl in *; auto. discriminate.
  - destruct_match; auto.
Qed.
Lemma lwrite1_log_app_None_r:
  forall log1 log2 idx,
  lwrite1 (log_get (log_app log1 log2) idx) = None ->
  lwrite1 (log_get log1 idx) = None.
Proof.
  intros *; unfold log_get, log_app.
  rewrite SortedRegEnv.opt_get_mapV. rewrite SortedRegEnv.opt_get_zip_default.
  destruct_match; auto. consider @opt_or; repeat destruct_match; simpl; auto.
  - destruct_with_eqn (lwrite1 l); simpl in *; auto.
  - rewrite opt_or_None_r. auto.
Qed.
Lemma lwrite1_log_app_None_l:
  forall log1 log2 idx,
  lwrite1 (log_get (log_app log1 log2) idx) = None ->
  lwrite1 (log_get log2 idx) = None.
Proof.
  intros *; unfold log_get, log_app, logentry_app. consider @opt_or. autorewrite with solve_taint.
  repeat destruct_match ; simpl; auto; discriminate.
Qed.

Lemma r_get_reg_commit_update_may_read0:
  forall st log idx,
  LE_may_read0 (log_get log idx) = true ->
  r_get_reg (commit_update st log) idx = r_get_reg st idx.
Proof.
  consider commit_update. consider latest_write. consider r_get_reg.
  intros. consider LE_may_read0. bash_destruct H.
  rewrite SortedRegEnv.opt_get_map.
  destruct_match; auto.
  repeat simpl_match. auto.
Qed.

Lemma opt_get_commit_update_same:
  forall st log idx,
  latest_write (log_get log idx) = None ->
  SortedRegEnv.opt_get (commit_update st log) idx = SortedRegEnv.opt_get st idx.
Proof.
  intros. specialize getenv_commit_None with (1 := H). consider get_reg. auto.
Qed.
Lemma LE_may_read0_log_app_false:
  forall log1 log2 idx,
  LE_may_read0 (log_get (log_app log1 log2) idx) = false ->
  LE_may_read0 (log_get log1 idx) = true ->
  LE_may_read0 (log_get log2 idx) = false.
Proof.
  intros *. rewrite get_log_app. unfold logentry_app. consider LE_may_read0; simpl.
  intros.
  bash_destruct H0. simpl in *. auto.
Qed.
Lemma LE_may_read1_log_app_false:
  forall log1 log2 idx,
  LE_may_read1 (log_get (log_app log1 log2) idx) = false ->
  LE_may_read1 (log_get log1 idx) = true ->
  LE_may_read1 (log_get log2 idx) = false.
Proof.
  intros *. rewrite get_log_app. unfold logentry_app. consider LE_may_read1; simpl.
  intros.
  bash_destruct H0. simpl in *. auto.
Qed.

Lemma opt_or_None_implies:
  forall T (x1 x2: option T),
  opt_or x1 x2 = None ->
  x1 = None /\ x2 = None.
Proof.
  intros. consider @opt_or.
  bash_destruct H; auto.
Qed.
Lemma wf_koika_sched_log_pair_app1_r:
  forall log1 log1' log2,
  wf_koika_sched_log_pair (Log_app log1 log1') log2 ->
  wf_koika_sched_log_pair log1' log2.
Proof.
  intros * hwf. destruct hwf as [wf_write0  wf_write1 wf_read1 wf_read0].
  constructor; intros reg.
  - specialize (wf_write0 reg). propositional.
    rewrite<-log_app_Log_app__koika in *.
    rewrite get_log_app in *. consider logentry_app. simpl in *.
    apply opt_or_None_implies in wf_write0. propositional.
  - specialize (wf_write1 reg). propositional.
    rewrite<-log_app_Log_app__koika in *.
    rewrite get_log_app in *. consider logentry_app. simpl in *.
    apply opt_or_None_implies in wf_write1. propositional.
  - specialize (wf_read1 reg); propositional.
    rewrite<-log_app_Log_app__koika in *.
    rewrite get_log_app in *. consider logentry_app. simpl in *.
    rewrite orb_false_iff in *. propositional.
  - specialize (wf_read0 reg); propositional.
    rewrite<-log_app_Log_app__koika in *.
    rewrite get_log_app in *. consider logentry_app. simpl in *.
    rewrite orb_false_iff in *. propositional.
  - specialize (wf_ext0 reg); propositional.
    rewrite<-ext_log_app_log_app in *.
    unfold ext_log_can_call, ext_log_app in *.
    rewrite SortedExtFnEnv.opt_get_mapV in *.
    rewrite SortedExtFnEnv.opt_get_zip_default in *.
    bash_destruct wf_ext0.
Qed.



Lemma map2_failure:
  forall A B C (f: A -> B -> C) v v1 ,
  Datatypes.length v <> Datatypes.length v1 <->
  map2 f v v1 = Failure tt.
Proof.
  induction v; propositional.
  - destruct_with_eqn v1; simpl in *; split; auto. congruence.
  - simpl in *. destruct_match; simpl in *; auto.
    + split; auto.
    + split; subst.
      * intros.
        assert ((Datatypes.length v) <> (Datatypes.length l)) by auto.
        apply IHv in H0. simpl_match. auto.
      * destruct_match; propositional; try discriminate; simplify.
        apply IHv in Heqr. auto.
Qed.
Lemma map2_orb_success_assoc:
  forall v v0 v1 s s' s1 s1',
  map2 orb v0 v1 = Success s ->
  map2 orb v s = Success s' ->
  map2 orb v v0 = Success s1 ->
  map2 orb s1 v1 = Success s1' ->
  s' = s1'.
Proof.
  induction v; simpl; auto.
  - intros. simplify. destruct v1; simpl in *; simplify; auto.
  - intros. bash_destruct H0. bash_destruct H1. simplify. simpl in *.
    destruct v1; simpl in *; simplify; eauto.
    assert (s0 = s1) by eauto. subst.
    rewrite orb_assoc. auto.
Qed.

Lemma ext_log_app_assoc:
  forall l1 l2 l3,
  ext_log_app l1 (ext_log_app l2 l3) = ext_log_app (ext_log_app l1 l2) l3.
Proof.
  intros. consider ext_log_app.
  apply  SortedExtFnEnv.env_ext. intros.
  repeat rewrite SortedExtFnEnv.opt_get_mapV. repeat rewrite SortedExtFnEnv.opt_get_zip_default.
  destruct_match; repeat rewrite SortedExtFnEnv.opt_get_mapV; repeat rewrite SortedExtFnEnv.opt_get_zip_default; repeat simpl_match.
  - destruct_match; auto.
    + destruct_match; auto.
      * repeat destruct_match; auto. subst.
        consider @success_or_default.
        consider Bits.or.
        destruct_with_eqn (beq_dec (Datatypes.length v0) (Datatypes.length v1));
        destruct_with_eqn (beq_dec (Datatypes.length v) (Datatypes.length v0)); simplify;
        repeat destruct_match;
        repeat match goal with
        | H: Datatypes.length _ = Datatypes.length _ |- _ =>
            pose_fresh (map2_success _ _ orb H)
        | H: Datatypes.length _ <> Datatypes.length _ |- _ =>
            pose_fresh (map2_failure _ _ orb H)
        end; consider @is_success; simplify;
        repeat match goal with
        | H: map2 _ _ _ = Success _ |- _ =>
            pose_fresh (map2_length _ _ _ _ H)
        | H: unit |- _ => destruct H
        end;propositional;
        repeat match goal with
        | H: map2 _ ?x ?y = Failure _ |- _ =>
          assert (Datatypes.length x <> Datatypes.length y) by (eapply map2_failure;eauto); clear H
        | H: Datatypes.length [] = Datatypes.length ?v |- _ =>
            (destruct v; simpl in H; [ | lia]); clear H
        | H: Datatypes.length ?v = Datatypes.length [] |- _ =>
            (destruct v; simpl in H; [ | lia]); clear H
        end; try lia; auto.
        eapply map2_orb_success_assoc with (1 := Heqr3); eauto.
      * repeat destruct_match; auto.
    + repeat destruct_match; auto.
  - destruct_match.
    + destruct_match; auto.
    + destruct_match; auto.
Qed.

Lemma Log_app_assoc:
  forall l1 l2 l3,
  Log_app l1 (Log_app l2 l3) = Log_app (Log_app l1 l2) l3.
Proof.
  intros. consider Log_app. simpl.
  rewrite log_app_assoc. rewrite ext_log_app_assoc. reflexivity.
Qed.
Lemma ext_fn_taint_env_approximates_append:
  forall (taint1 taint2 : ext_fn_taint_env_t) (log1 log2 : ext_log_t),
  ext_fn_taint_env_approximates_log taint1 log1 ->
  ext_fn_taint_env_approximates_log taint2 log2 ->
  ext_fn_taint_env_approximates_log (merge_ext_fn_taint_env taint2 taint1) (ext_log_app log1 log2).
Proof.
  consider ext_fn_taint_env_approximates_log. consider merge_ext_fn_taint_env.
  intros.
  consider ext_log_app.
  rewrite SortedExtFnEnv.opt_get_mapV in *.
  rewrite SortedExtFnEnv.opt_get_zip_default in *.
  rewrite SortedExtFnEnv.opt_get_mapV in *.
  rewrite SortedExtFnEnv.opt_get_zip_default in *.
  consider @is_some. propositional.
  destruct_matches_in_hyp H2.
  - rewrite H; eauto.
    destruct_match; rewrite orb_true_r; auto.
  - destruct_matches_in_hyp H2; simplify.
    rewrite H0; eauto. destruct_match; simpl; auto.
Qed.
Lemma taint_env_approximates_log_empty':
  forall env, taint_env_approximates_log env log_empty.
Proof.
  consider taint_env_approximates_log.
  consider taint_approximates_log_entry. consider log_get.
  intros.
  setoid_rewrite SortedRegEnv.opt_get_empty. consider le_to_taint.
  constructor; simpl; propositional; discriminate.
Qed.
Lemma taint_env_approximates_log_add_taints_r:
  forall (taint : taint_env_t) (log : log_t) (taint' : taint_env_t),
  taint_env_approximates_log taint' log -> taint_env_approximates_log (merge_taint_env taint taint') log.
Proof.
  intros. rewrite merge_taint_env_comm.
  apply taint_env_approximates_log_add_taints. auto.
Qed.
Hint Resolve  taint_env_approximates_log_add_taints: solve_taint.
Hint Resolve  taint_env_approximates_log_add_taints_r: solve_taint.
Hint Resolve taint_env_approximates_log_set__read0: solve_taint.
Hint Resolve taint_env_approximates_log_set__read1: solve_taint.
Hint Resolve taint_env_approximates_log_set__write0: solve_taint.
Hint Resolve taint_env_approximates_log_set__write1: solve_taint.

Lemma taint_action_approximates_log:
  forall fuel int_fn_depth ext_fns int_fns struct_defs st sched_log rl log taint_base t gamma gamma' action_log v fuel',
  interp_action ext_fns int_fns struct_defs fuel int_fn_depth
    st gamma sched_log action_log rl = Success (Some (gamma',log,v)) ->
  taint_action int_fns fuel' taint_base rl = Success (Some t) ->
  taint_env_approximates_log taint_base (Log__koika action_log) ->
  taint_env_approximates_log t (Log__koika log).
Proof.
  induction fuel; propositional; simpl in *; [discriminate | ].
  destruct fuel'; simpl in *; [discriminate | ].
  consider @res_opt_bind.
  destruct rl; simplify; simpl in *; auto.
  all: repeat match goal with
       | H: interp_action _ _ _ _ _ _ _ _ ?action_log ?rl = Success (Some _),
         H1: taint_action _ _ ?taint_base ?rl = Success (Some _),
         H2: taint_env_approximates_log ?taint_base (Log__koika ?action_log) |- _ =>
           pose_fresh (IHfuel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H1 H2)
       | |- _ => progress destruct_all_matches_in_hyps; try discriminate; simplify; simpl
       end; eauto with solve_taint.
Qed.


Lemma taint_rule_approximates_log:
  forall ext_fns int_fns struct_defs st sched_log rl log taint_base t,
  interp_rule ext_fns int_fns struct_defs st sched_log rl = Success (Some log) ->
  taint_rule int_fns taint_base rl = Success (Some t) ->
  taint_env_approximates_log t (Log__koika log).
Proof.
  intros.  consider interp_rule. consider taint_rule. simplify. simpl.
  eapply taint_action_approximates_log; eauto. simpl.
  apply taint_env_approximates_log_empty'.
Qed.

Lemma merge_ext_fn_taint_env_empty_l:
  forall base, merge_ext_fn_taint_env SortedExtFnEnv.empty base = base.
Proof.
  intros. unfold merge_ext_fn_taint_env.
  apply SortedExtFnEnv.env_ext. intros.
  rewrite SortedExtFnEnv.opt_get_mapV.
  rewrite SortedExtFnEnv.opt_get_zip_default.
  rewrite SortedExtFnEnv.opt_get_empty. destruct_match; auto.
Qed.

Lemma merge_ext_fn_taint_env_empty_r:
  forall base, merge_ext_fn_taint_env base SortedExtFnEnv.empty = base.
Proof.
  intros. unfold merge_ext_fn_taint_env.
  apply SortedExtFnEnv.env_ext. intros.
  rewrite SortedExtFnEnv.opt_get_mapV.
  rewrite SortedExtFnEnv.opt_get_zip_default.
  rewrite SortedExtFnEnv.opt_get_empty. destruct_match; auto. rewrite orb_false_r. auto.
Qed.
Lemma taint_schedule_subset:
  forall {rule_name_t: Type} int_fns (rules: rule_name_t -> rule) sched taint_env taint_env',
  taint_schedule int_fns rules taint_env sched = Success (Some taint_env') ->
  taint_env_le taint_env taint_env'.
Proof.
  induction sched; simpl; propositional; simplify; auto.
  - apply taint_env_le_refl.
  - consider @res_opt_bind. simplify.
    apply IHsched in H.
    rewrite merge_taint_env_comm in H.
    eapply taint_env_le_merge_taint_env_impl_l; eauto.
Qed.
Lemma taint_env_le_merge_taint_env_r:
  forall taint_env t1 t2 : taint_env_t,
  taint_env_le taint_env t2 ->  taint_env_le taint_env (merge_taint_env t1 t2).
Proof.
  consider taint_env_le. consider merge_taint_env.
  consider get_reg_taint_default. intros.
  rewrite SortedRegEnv.opt_get_mapV.
  rewrite SortedRegEnv.opt_get_zip_default.
  consider merge_taints.
  specialize (H reg).
  inversion H. repeat destruct_match; auto; simpl; constructor; simpl; propositional; simpl in *.
  all: repeat match goal with
       | H: _ = true |- _ => progress rewrite H
       | |- context[_ || true ] => rewrite orb_true_r
       | |- context[_ || false ] => rewrite orb_false_r
       end; auto.
Qed.
Lemma merge_ext_fn_taint_env_assoc
  : forall env1 env2 env3 : ext_fn_taint_env_t,
  merge_ext_fn_taint_env (merge_ext_fn_taint_env env1 env2) env3 = merge_ext_fn_taint_env env1 (merge_ext_fn_taint_env env2 env3).
Proof.
  consider merge_ext_fn_taint_env.
  intros. apply SortedExtFnEnv.env_ext.
  intros. repeat rewrite SortedExtFnEnv.opt_get_mapV.
  repeat rewrite SortedExtFnEnv.opt_get_zip_default.
  repeat rewrite SortedExtFnEnv.opt_get_mapV.
  repeat rewrite SortedExtFnEnv.opt_get_zip_default.
  repeat destruct_match; simpl; auto; repeat rewrite orb_false_r; auto.
  rewrite orb_assoc. reflexivity.
Qed.

Lemma ext_fn_taint_schedule_subset:
  forall {rule_name_t: Type} int_fns (rules: rule_name_t -> rule) sched taint_env taint_env',
  ext_fn_taint_schedule int_fns rules taint_env sched = Success (Some taint_env') ->
  ext_fn_taint_env_subset taint_env taint_env'.
Proof.
  induction sched; simpl; propositional; simplify; auto.
  - apply ext_fn_taint_env_subset_refl.
  - consider @res_opt_bind. simplify.
    apply IHsched in H.
    apply ext_fn_taint_rule_subset in Heqr0.
    eapply ext_fn_taint_env_subset_trans; eauto.
Qed.

Lemma merge_ext_fn_taint_env_subset:
  forall e e1,
  ext_fn_taint_env_subset e e1 ->
  ext_fn_taint_env_subset (merge_ext_fn_taint_env e e1) e1 .
Proof.
  consider ext_fn_taint_env_subset. consider merge_ext_fn_taint_env.
  intros.
  repeat rewrite SortedExtFnEnv.opt_get_mapV in *.
  repeat rewrite SortedExtFnEnv.opt_get_zip_default in *.
  specialize (H fn).
  bash_destruct H0; simplify; propositional.
  destruct b; propositional; simpl in *; simplify; auto.
Qed.
Lemma merge_ext_fn_taint_env_comm:
  forall e1 e2,
  merge_ext_fn_taint_env e1 e2 = merge_ext_fn_taint_env e2 e1.
Proof.
  consider merge_ext_fn_taint_env.
  intros. apply SortedExtFnEnv.env_ext. intros.
  repeat rewrite SortedExtFnEnv.opt_get_mapV.
   repeat rewrite SortedExtFnEnv.opt_get_zip_default.
   repeat destruct_match; simpl; repeat rewrite orb_false_r; auto.
   rewrite orb_comm. reflexivity.
Qed.
Lemma does_not_conflict_subset:
  forall taint1 taint2 taint3,
  does_not_conflict taint1 taint2 = true ->
  taint_env_le taint3 taint2 ->
  does_not_conflict taint1 taint3 = true.
Proof.
  consider does_not_conflict.
  intros * hconflict hle. repeat rewrite forallb_forall in *.
  intros * hin.  consider taint_env_le.
  repeat destruct_match; subst. rewrite negb_true_iff.
  specialize (hle t). destruct hle.
  consider taint_conflicts.
  repeat rewrite orb_false_iff.
  specialize hconflict with (x := (t, (t0, get_reg_taint_default taint2 t))).
  rewrite SortedRegEnv.In_to_list in *.
  assert (t0 = get_reg_taint_default taint1 t).
  { rewrite SortedRegEnv.opt_get_zip_default in hin.
    unfold get_reg_taint_default.  bash_destruct hin.
  }
  assert (t1 = get_reg_taint_default taint3 t).
  { rewrite SortedRegEnv.opt_get_zip_default in hin.
    unfold get_reg_taint_default.  bash_destruct hin.
  }
  subst.
  split_ands_in_goal;
    match goal with
    | |- ?x && _ = false => destruct x eqn:?; simpl; propositional
    end.
  all: assert_pre_and_specialize hconflict;
    [ rewrite SortedRegEnv.opt_get_zip_default;
      consider get_reg_taint_default;
      destruct_all_matches; simpl in *; discriminate | ];
    rewrite negb_true_iff in *; repeat rewrite orb_false_iff in *; repeat rewrite andb_false_iff in *;
      propositional;
      match goal with
      | H: ?x = true, H1: ?x = false \/ _ |- _ =>
          rewrite H in H1; destruct H1; [ discriminate | ]
      end; auto.
Qed.
Lemma taint_env_le_merge_taint_env_proj:
  forall t1 t2 t3,
  taint_env_le t2 t3 ->
  taint_env_le (merge_taint_env t1 t2) (merge_taint_env t1 t3).
Proof.
  consider taint_env_le. intros. consider merge_taint_env.
  specialize (H reg). consider get_reg_taint_default.
  repeat rewrite SortedRegEnv.opt_get_mapV.
  repeat rewrite SortedRegEnv.opt_get_zip_default.
  consider merge_taints. inversions H.
  destruct_all_matches; constructor; simpl; intros; try rewrite orb_true_iff in *; split_cases; try auto.
Qed.
Lemma ext_fn_conflicts_subset:
  forall t1 t2 t3,
  ext_fn_taint_env_conflicts t1 t2 = false ->
  ext_fn_taint_env_subset t3 t2 ->
  ext_fn_taint_env_conflicts t1 t3 = false.
Proof.
  consider ext_fn_taint_env_conflicts. intros.
  destruct_with_eqn (existsb (fun '(_, (t0, t4)) => t0 && t4) (SortedExtFnEnv.to_list (SortedExtFnEnv.zip_default t1 t3 false false))); auto.
  apply existsb_false_forall in H. rewrite forallb_forall in H.
  rewrite existsb_exists in Heqb. propositional.
  destruct_all_matches. rewrite andb_true_iff in *. propositional.
  consider ext_fn_taint_env_subset.
  specialize (H (t, (true,true))).
  rewrite SortedRegEnv.In_to_list in *.
  rewrite SortedRegEnv.opt_get_zip_default in *.
  bash_destruct Heqb1; simplify. simpl in *.
  rewrite H0 in H by auto. propositional.
Qed.
Lemma ext_fn_taint_env_subset_merge_taint_env_proj:
  forall t1 t2 t3,
  ext_fn_taint_env_subset t2 t3 ->
  ext_fn_taint_env_subset (merge_ext_fn_taint_env t1 t2) (merge_ext_fn_taint_env t1 t3).
Proof.
  consider ext_fn_taint_env_subset. intros. consider merge_ext_fn_taint_env.
  specialize (H fn). consider get_reg_taint_default.
  repeat rewrite SortedRegEnv.opt_get_mapV in *.
  repeat rewrite SortedRegEnv.opt_get_zip_default in *.
  bash_destruct H0; simplify; repeat rewrite orb_true_iff in *; destruct_all_matches; split_cases; simplify; auto.
  rewrite orb_true_r. reflexivity.
Qed.
Lemma ext_fn_taint_env_subset_merge_l:
  forall e1 e2 e3,
  ext_fn_taint_env_subset (merge_ext_fn_taint_env e1 e2) e3 ->
  ext_fn_taint_env_subset e1 e3 /\ ext_fn_taint_env_subset e2 e3.
Proof.
  consider merge_ext_fn_taint_env. consider ext_fn_taint_env_subset.
  intros. split; intros; specialize (H fn);
    rewrite SortedExtFnEnv.opt_get_mapV in *;
    rewrite SortedExtFnEnv.opt_get_zip_default in *;
    simpl_match;
    assert_pre_and_specialize H; [destruct_match; auto | | destruct_match; auto | ];
    try rewrite orb_true_r; auto.
Qed.
Lemma ext_fn_taint_env_subset_merge_l_l:
  forall e1 e2 e3,
  ext_fn_taint_env_subset (merge_ext_fn_taint_env e1 e2) e3 ->
  ext_fn_taint_env_subset e1 e3.
Proof.
  intros. apply ext_fn_taint_env_subset_merge_l in H. propositional.
Qed.
Lemma ext_fn_taint_env_subset_merge_l_r:
  forall e1 e2 e3,
  ext_fn_taint_env_subset (merge_ext_fn_taint_env e1 e2) e3 ->
  ext_fn_taint_env_subset e2 e3.
Proof.
  intros. apply ext_fn_taint_env_subset_merge_l in H. propositional.
Qed.
Lemma ext_fn_taint_env_subset_merge_l_idem:
  forall e2 e,
  ext_fn_taint_env_subset e2 e ->
  ext_fn_taint_env_subset (merge_ext_fn_taint_env e e2) e.
Proof.
  intros. consider ext_fn_taint_env_subset. intros. specialize (H fn).
  consider merge_ext_fn_taint_env.
  rewrite SortedExtFnEnv.opt_get_mapV in *.
  rewrite SortedExtFnEnv.opt_get_zip_default in *.
  destruct_all_matches; simplify; propositional.
  destruct b; simpl in *; propositional. simplify; auto.
Qed.
Hint Resolve ext_fn_taint_env_approximates_log_subset: solve_taints.
Hint Resolve ext_fn_taint_env_subset_merge_taint_env_proj : solve_taints.
Lemma taint_env_le_merge_r_idem:
  forall t1 t2,
  taint_env_le t1 (merge_taint_env t1 t2).
Proof.
  consider merge_taint_env. consider @taint_env_le.
  intros. consider get_reg_taint_default.
  rewrite SortedRegEnv.opt_get_mapV.
  rewrite SortedRegEnv.opt_get_zip_default.
  repeat destruct_match; constructor; simpl; propositional; try discriminate; try rewrite H; auto.
Qed.
Lemma ext_fn_taint_env_subset_merge_r_idem:
  forall e1 e2,
  ext_fn_taint_env_subset e1 (merge_ext_fn_taint_env e1 e2).
Proof.
  intros.  eapply TypecheckingCorrectness.ext_fn_taint_env_subset_merge_l.
  apply ext_fn_taint_env_subset_refl.
Qed.
Lemma ext_fn_taint_env_subset_merge_r':
  forall e1 e2,
  ext_fn_taint_env_subset e1 (merge_ext_fn_taint_env e2 e1).
Proof.
  consider ext_fn_taint_env_subset. consider merge_ext_fn_taint_env.
  intros. rewrite SortedExtFnEnv.opt_get_mapV.
  rewrite SortedExtFnEnv.opt_get_zip_default. simpl_match.
  destruct_match; rewrite orb_true_r; auto.
Qed.
Lemma ext_log_can_call_false_iff:
  forall log1 log2 fn,
  ext_log_can_call (ext_log_app log1 log2) fn = false <->
  ext_log_can_call log1 fn = false \/
  ext_log_can_call log2 fn = false.
Proof.
  consider ext_log_can_call. consider ext_log_app. intros.
  rewrite SortedExtFnEnv.opt_get_mapV.
  rewrite SortedExtFnEnv.opt_get_zip_default.
  repeat destruct_match; propositional; split; propositional; split_cases.
Qed.
Lemma ext_fn_taint_env_conflicts_false:
  forall fn base2 base1 log2 ,
  ext_fn_taint_env_conflicts base2 base1 = false ->
  ext_fn_taint_env_approximates_log base2 log2 ->
  ext_log_can_call (log2) fn = false ->
  SortedExtFnEnv.opt_get base1 fn = Some true ->
  False.
Proof.
  intros * hconflicts happrox2 happrox1 hcall.
  consider ext_fn_taint_env_conflicts.
  apply existsb_false_forall in hconflicts.
  rewrite forallb_forall in *.
  consider ext_fn_taint_env_approximates_log.
  consider ext_log_can_call. bash_destruct hcall.
  specialize (happrox2 fn).
  consider @is_some.
  bash_destruct happrox1.
  assert_pre_and_specialize happrox2; eauto.
  specialize (hconflicts (fn, (true,true))).
  rewrite SortedExtFnEnv.In_to_list in hconflicts.
  rewrite SortedExtFnEnv.opt_get_zip_default in hconflicts.
  repeat simpl_match. propositional. simpl in *. discriminate.
Qed.
Lemma wf_koika_sched_log_pair_ext_update:
  forall l log1 log2 fn v,
  wf_koika_sched_log_pair (Log_app l log1) log2  ->
  (* ext_log_can_call (Log__ext log1) fn = true -> *)
  ext_log_can_call (Log__ext log2) fn = true ->
  wf_koika_sched_log_pair
    (Log_app {| Log__koika := Log__koika l; Log__ext := ext_log_update (Log__ext l) fn v |} log1) log2.
Proof.
  intros * hwf hcan_call2. destruct hwf.
  constructor; simpl; auto.
  intros fn0 hcall.
  consider ext_log_can_call.
  consider ext_log_app. consider ext_log_update.
  autorewrite with solve_taint.
  destruct_with_eqn (beq_dec fn fn0); simplify.
  - rewrite SortedExtFnEnv.update_correct_eq by auto.
    bash_destruct hcall.
  - rewrite SortedExtFnEnv.update_correct_neq by auto.
    specialize (wf_ext0 fn0). propositional.
    rewrite<-ext_log_app_log_app in *. consider ext_log_app.
    autorewrite with solve_taint in *. destruct_all_matches.
Qed.
Lemma ext_log_can_call_app_l:
  forall log1 log2 fn,
  ext_log_can_call (ext_log_app log1 log2) fn = true ->
  ext_log_can_call log2 fn = true.
Proof.
  consider ext_log_can_call. consider ext_log_app. intros *.
  autorewrite with solve_taint. repeat destruct_match; auto.
Qed.

Lemma interp_action_equiv:
  forall fuel rule ext_fns int_fns struct_defs st log1 log2 max_fn_depth gamma action_log opt_res taint_fuel
    taint_base_action action_taint ext_taint_fuel ext_taint_base_action ext_action_taint
    taint_base1 taint_base2 ext_taint_base1 ext_taint_base2 ext_taint_base_action',
  wf_koika_sched_log_pair ((Log_app action_log log1)) (log2) ->
  taint_action int_fns taint_fuel taint_base_action rule = Success (Some action_taint) ->
  ext_fn_taint_action int_fns ext_taint_fuel ext_taint_base_action' rule = Success (Some ext_action_taint)->
  ext_fn_taint_env_subset (merge_ext_fn_taint_env ext_taint_base_action ext_taint_base1) ext_taint_base_action' ->
  taint_env_approximates_log taint_base_action (Log__koika action_log) ->
  taint_env_approximates_log taint_base1 (Log__koika log1) ->
  taint_env_approximates_log taint_base2 (Log__koika log2) ->
  ext_fn_taint_env_approximates_log ext_taint_base_action (Log__ext action_log) ->
  ext_fn_taint_env_approximates_log ext_taint_base1 (Log__ext log1) ->
  ext_fn_taint_env_approximates_log ext_taint_base2 (Log__ext log2) ->
  does_not_conflict taint_base2 (merge_taint_env taint_base1 action_taint) = true ->
  ext_fn_taint_env_conflicts ext_taint_base2 (merge_ext_fn_taint_env ext_taint_base1 ext_action_taint)  = false ->
  interp_action ext_fns int_fns struct_defs fuel max_fn_depth st gamma (Log_app log1 log2) action_log rule = Success opt_res ->
  match interp_action ext_fns int_fns struct_defs fuel max_fn_depth (commit_update st (Log__koika log2) )
                      gamma log1 action_log rule with
  | Success (Some (gamma0, log0, v0)) =>
      opt_res = Some (gamma0, log0, v0) /\
      wf_koika_sched_log_pair ((Log_app log0 log1)) (log2) /\
      taint_env_approximates_log action_taint (Log__koika log0) /\
      ext_fn_taint_env_approximates_log ext_action_taint (Log__ext log0)
  | Success None => opt_res = None
  | Failure _ => False
  end.
Proof.
  induction fuel; intros * hwf_koika htaint hext_taint hext_subset haction_approx hlog1_approx hlog2_approx
                           haction_ext_approx hlog1_ext_approx hlog2_ext_approx
                           hconflict hext_conflict hrule; simpl in *; [discriminate | ].
  specialize IHfuel with (6 := hlog1_approx) (7 := hlog2_approx)
                         (9 := hlog1_ext_approx) (10 := hlog2_ext_approx).
  destruct taint_fuel; simpl in *; [discriminate | ].
  destruct ext_taint_fuel; simpl in *; [discriminate | ].

  destruct_match; simplify; split_ands_in_goal; unfold res_opt_bind in *; simplify; auto.
Lemma wf_koika_sched_log_pair_set_read0:
  forall l log1 log2 idx,
  wf_koika_sched_log_pair (Log_app l log1) log2  ->
  LE_may_read0 (log_get (Log__koika log2) idx) = true ->
  wf_koika_sched_log_pair
    (Log_app {| Log__koika := log_set (Log__koika l) idx (LE_set_read0 (log_get (Log__koika l) idx));
                Log__ext := Log__ext l |} log1) log2.
Proof.
  intros * hwf hmay_read0.
  destruct hwf. constructor; simpl; auto; intros reg; intros * hp.
  1: specialize wf_write2 with (1 := hp).
  2: specialize wf_write3 with (1 := hp).
  3: specialize wf_read2 with (1 := hp).
  all: rewrite get_log_app in *; simpl in *; try rewrite get_log_app in *;
    destruct_with_eqn (beq_dec idx reg); simplify;
      try rewrite log_set_eq by auto;
      try rewrite log_set_neq by auto; simpl; auto.
  - congruence.
  - specialize wf_read3 with (1 := hp).
    rewrite get_log_app in *; simpl in *; try rewrite get_log_app in *; auto.
Qed.
Lemma wf_koika_sched_log_pair_set_read1:
  forall l log1 log2 idx,
  wf_koika_sched_log_pair (Log_app l log1) log2  ->
  LE_may_read1 (log_get (Log__koika log2) idx) = true ->
  wf_koika_sched_log_pair
    (Log_app {| Log__koika := log_set (Log__koika l) idx (LE_set_read1 (log_get (Log__koika l) idx));
                Log__ext := Log__ext l |} log1) log2.
Proof.
  intros * hwf hmay_read1.
  destruct hwf. constructor; simpl; auto; intros reg; intros * hp.
  1: specialize wf_write2 with (1 := hp).
  2: specialize wf_write3 with (1 := hp).
  4: specialize wf_read3 with (1 := hp).
  all: rewrite get_log_app in *; simpl in *; try rewrite get_log_app in *;
    destruct_with_eqn (beq_dec idx reg); simplify;
      try rewrite log_set_eq by auto;
      try rewrite log_set_neq by auto; simpl; auto.
  - congruence.
  - specialize wf_read2 with (1 := hp).
    rewrite get_log_app in *; simpl in *; try rewrite get_log_app in *; auto.
Qed.
Lemma wf_koika_sched_log_pair_set_write0:
  forall l log1 log2 idx v,
  wf_koika_sched_log_pair (Log_app l log1) log2  ->
  LE_may_write0 (log_get (Log__koika log2) idx) = true ->
  wf_koika_sched_log_pair
    (Log_app {| Log__koika := log_set (Log__koika l) idx (LE_set_write0 (log_get (Log__koika l) idx) v);
                Log__ext := Log__ext l |} log1) log2.
Proof.
  intros * hwf hmay_write0.
  destruct hwf. constructor; simpl; auto; intros reg; intros * hp.
  1: specialize wf_write2 with (1 := hp).
  2: specialize wf_write3 with (1 := hp).
  3: specialize wf_read2 with (1 := hp).
  4: specialize wf_read3 with (1 := hp).
  all: rewrite get_log_app in *; simpl in *; try rewrite get_log_app in *;
    destruct_with_eqn (beq_dec idx reg); simplify;
      try rewrite log_set_eq by auto;
      try rewrite log_set_neq by auto; simpl; auto.
  congruence.
Qed.
Lemma wf_koika_sched_log_pair_set_write1:
  forall l log1 log2 idx v,
  wf_koika_sched_log_pair (Log_app l log1) log2  ->
  LE_may_write1 (log_get (Log__koika log2) idx) = true ->
  wf_koika_sched_log_pair
    (Log_app {| Log__koika := log_set (Log__koika l) idx (LE_set_write1 (log_get (Log__koika l) idx) v);
                Log__ext := Log__ext l |} log1) log2.
Proof.
  intros * hwf hmay_write0.
  destruct hwf. constructor; simpl; auto; intros reg; intros * hp.
  1: specialize wf_write2 with (1 := hp).
  2: specialize wf_write3 with (1 := hp).
  3: specialize wf_read2 with (1 := hp).
  4: specialize wf_read3 with (1 := hp).
  all: rewrite get_log_app in *; simpl in *; try rewrite get_log_app in *;
    destruct_with_eqn (beq_dec idx reg); simplify;
      try rewrite log_set_eq by auto;
      try rewrite log_set_neq by auto; simpl; auto.
  congruence.
Qed.


Ltac t_interp_action_equiv_solve_match :=
  let X := get_innermost_match_in_goal in
  match X with
  | r_get_reg (commit_update ?st ?_log) ?idx =>
      match goal with
      | H: r_get_reg ?st ?idx = Success _ |- _ =>
          specialize r_get_reg_commit_update_success with (1 := H) (log := _log); intros; simplify
      end
  | LE_may_read0 (log_get (?log1) ?idx) =>
      match goal with
      | H: LE_may_read0 (log_get (log_app ?log1 _) ?idx) = true |- _ =>
          erewrite LE_may_read0_log_get_app_r with (1 := H)
      end
  end.
Ltac t_interp_action_equiv IHfuel :=
match goal with
| H:  wf_koika_sched_log_pair (Log_app (?action_log) (?log1)) (?log2),
  H1: taint_action _ _ _ ?rule = Success (Some ?action_taint),
  H2: ext_fn_taint_action _ _ ?ext_taint_base_action' ?rule = Success (Some ?ext_action_taint),
  H3: taint_env_approximates_log ?taint_base_action (Log__koika ?action_log),
  H4: ext_fn_taint_env_approximates_log ?ext_taint_base_action (Log__ext ?action_log),
  H5: does_not_conflict ?taint_base2 (merge_taint_env ?taint_base1 ?action_taint) = true,
  H6: interp_action ?ext_fns ?int_fns ?struct_defs ?fuel ?max_fn_depth ?st ?gamma (Log_app ?log1 ?log2) ?action_log
             ?rule = Success ?opt_res
  (* H7: ext_fn_taint_env_subset  (merge_ext_fn_taint_env ?ext_taint_base_action ?ext_taint_base1) *)
  (*            ?ext_taint_base_action' *)
  |- _ =>
    let G := fresh in
    pose IHfuel as G;
    specialize G with (1 := H) (2 := H1) (3 := H2) (* (4 := H7) *) (5 := H3) (6 := H4)
                           (7 := H5) (* (8 := H8) *) (9 := H6) (* (6 := H4) *);
    do 2 (assert_pre_and_specialize G; [ solve[repeat t_interp_action_equiv G] | ]);
    clear H6; bash_destruct G; propositional
  | H: _ && _ = true |- _ =>
      rewrite andb_true_iff in H
  | H: _ && _ = false |- _ =>
      rewrite andb_false_iff in H
  | H: LE_may_read0 (log_get (log_app ?log1 _) ?idx) = true |- _ =>
      pose_fresh (LE_may_read0_log_get_app_r _ _ _ H)
  | H: LE_may_read0 (log_get (log_app ?log1 _) ?idx) = true |- _ =>
      pose_fresh (LE_may_read0_log_get_app_l _ _ _ H)
  | H: LE_may_read0 (log_get (log_app ?log1 ?log2) ?idx) = false,
    H1: LE_may_read0 (log_get ?log1 ?idx) = true |- _ =>
      pose_fresh (LE_may_read0_log_app_false _ _ _ H H1)
  | H: LE_may_read1 (log_get (log_app ?log1 _) ?idx) = true |- _ =>
      pose_fresh (LE_may_read1_log_get_app_r _ _ _ H)
  | H: LE_may_read1 (log_get (log_app ?log1 _) ?idx) = true |- _ =>
      pose_fresh (LE_may_read1_log_get_app_l _ _ _ H)
  | H: LE_may_read1 (log_get (log_app ?log1 ?log2) ?idx) = false,
    H1: LE_may_read1 (log_get ?log1 ?idx) = true |- _ =>
      pose_fresh (LE_may_read1_log_app_false _ _ _ H H1)
  | H: wf_koika_sched_log_pair (Log_app _ _) _ |- _ =>
      pose_fresh (wf_koika_sched_log_pair_app1_r _ _ _ H)
  | H: taint_action _ _ _ ?action = Success (Some _) |- _ =>
      pose_fresh (taint_action_generalizes_taint _ _ _ _ _ H)
  | |-taint_env_le (merge_taint_env ?t ?t3) (merge_taint_env ?t ?t2) =>
      apply taint_env_le_merge_taint_env_proj
  | |- taint_env_le ?t1 (merge_taint_env ?t1 _) =>
      apply taint_env_le_merge_r_idem
  | H: context[merge_taint_env ?t1 ?t2],
    H2: taint_env_le ?t3 ?t2 |- _ =>
      pose_fresh (taint_env_le_merge_taint_env_proj t1 _ _ H2)
  (* | H: context[merge_ext_fn_taint_env ?t1 ?t2], *)
  (*   H2: ext_fn_taint_env_subset ?t3 ?t2 |- _ => *)
  (*     pose_fresh (ext_fn_taint_env_subset_merge_taint_env_proj t1 _ _ H2) *)
  | H: does_not_conflict ?t1 ?t2 = true,
    H1: taint_env_le ?t3 ?t2 |- _ =>
      pose_fresh (does_not_conflict_subset _ _ _ H H1)
  | |- ext_fn_taint_env_subset (merge_ext_fn_taint_env ?e ?e2) ?e =>
      apply ext_fn_taint_env_subset_merge_l_idem
  | H: ext_fn_taint_env_conflicts ?t1 ?t2 = false ,
    H1: ext_fn_taint_env_subset ?t3 ?t2 |- _ =>
      pose_fresh (ext_fn_conflicts_subset _ _ _ H H1)
  | H: does_not_conflict ?t0 _ = true
    |- does_not_conflict ?t0 (merge_taint_env ?taint_base1 ?t) = true =>
      eapply does_not_conflict_subset; [ eapply H | ];
      solve[repeat t_interp_action_equiv IHfuel]
  | H: ext_fn_taint_action _ _ _ ?rule = Success (Some _) |- _ =>
      pose_fresh (ext_fn_taint_action_subset _ _ _ _ _ H)
  | H: ext_fn_taint_env_subset ?env1 ?env2,
    H1: ext_fn_taint_env_subset ?env2 ?env3 |- _ =>
      pose_fresh (ext_fn_taint_env_subset_trans _ _ _ H H1)
  | H: taint_env_le ?taint_env ?taint_env',
    H1: taint_env_approximates_log ?taint_env ?log |- _ =>
      pose_fresh (taint_env_approximates_log_generalize_taint _ _ _ H H1)
  (* | H: ext_fn_taint_env_approximates_log ?env ?log, *)
  (*   H1: ext_fn_taint_env_subset ?env ?env' |- _ => *)
  (*     pose_fresh (ext_fn_taint_env_approximates_log_subset _ _ _ H H1) *)
  | H: ext_fn_taint_env_subset (merge_ext_fn_taint_env ?e1 ?e2) ?e3 |- _ =>
      pose_fresh (ext_fn_taint_env_subset_merge_l_l _ _ _ H)
  | H: ext_fn_taint_env_subset (merge_ext_fn_taint_env ?e1 ?e2) ?e3 |- _ =>
      pose_fresh (ext_fn_taint_env_subset_merge_l_r _ _ _ H)
  | |- ext_fn_taint_env_subset (merge_ext_fn_taint_env ?ext_taint_base1 _)
                              (merge_ext_fn_taint_env ?ext_taint_base1 _) =>
      apply ext_fn_taint_env_subset_merge_taint_env_proj
  | H: ext_fn_taint_env_subset ?env ?e1
    |- ext_fn_taint_env_subset ?env (merge_ext_fn_taint_env ?e0 ?e1) =>
    eapply ext_fn_taint_env_subset_merge_r; eauto
  | |- ext_fn_taint_env_conflicts ?ext_taint_base2 (merge_ext_fn_taint_env ?ext_taint_base1 ?e) = false =>
    solve[eapply ext_fn_conflicts_subset; eauto with solve_taints]
  | |- taint_env_le ?t (merge_taint_env _ ?t) =>
    apply taint_env_le_merge_refl_r
  | |- ext_fn_taint_env_subset ?e1 (merge_ext_fn_taint_env ?e1 ?e2) =>
      apply ext_fn_taint_env_subset_merge_r_idem
  | H: ext_fn_taint_env_conflicts ?t1 ?t2 = false
    |- ext_fn_taint_env_conflicts ?t1 (merge_ext_fn_taint_env ?ext_taint_base1 ?e) = false =>
      eapply ext_fn_conflicts_subset; [apply H | ];
      solve[repeat t_interp_action_equiv IHfuel]
  | H: taint_env_approximates_log ?taint ?log
    |- taint_env_approximates_log (merge_taint_env ?taint ?taint') ?log =>
      apply taint_env_approximates_log_add_taints with (1 := H)
  | H: ext_fn_taint_env_approximates_log ?env0 ?log
    |- ext_fn_taint_env_approximates_log (merge_ext_fn_taint_env ?env0 ?env1) ?log =>
      apply ext_fn_taint_env_approximates_log_merge_l; auto
  | |- ext_fn_taint_env_subset ?e1 (merge_ext_fn_taint_env _ ?e1) =>
    apply ext_fn_taint_env_subset_merge_r'
  | H: taint_env_approximates_log ?taint' ?log
    |- taint_env_approximates_log (merge_taint_env ?taint ?taint') ?log =>
      apply taint_env_approximates_log_add_taints_r
  | H: ext_fn_taint_env_approximates_log ?env1 ?log
    |- ext_fn_taint_env_approximates_log (merge_ext_fn_taint_env ?env0 ?env1) ?log =>
    apply ext_fn_taint_env_approximates_log_merge_r
  | _ => progress t_interp_action_equiv_solve_match
  | _ => progress (simplify; propositional; split_ands_in_goal; eauto with solve_taints)
  end.


  all: repeat t_interp_action_equiv IHfuel.
Ltac t_interp_action_equiv_custom IHfuel foo :=
match goal with
| H:  wf_koika_sched_log_pair (Log_app (?action_log) (?log1)) (?log2),
  H1: taint_action _ _ _ ?rule = Success (Some ?action_taint),
  H2: ext_fn_taint_action _ _ ?ext_taint_base_action' ?rule = Success (Some ?ext_action_taint),
  H3: taint_env_approximates_log ?taint_base_action (Log__koika ?action_log),
  H4: ext_fn_taint_env_approximates_log ?ext_taint_base_action (Log__ext ?action_log),
  H6: interp_action ?ext_fns ?int_fns ?struct_defs ?fuel ?max_fn_depth ?st ?gamma (Log_app ?log1 ?log2) ?action_log
             ?rule = Success ?opt_res
  |- _ =>
    pose IHfuel as foo;
    specialize foo with (1 := H) (2 := H1) (3 := H2) (5 := H3) (6 := H4) (9 := H6);
    do 3 (assert_pre_and_specialize foo; [solve[repeat t_interp_action_equiv IHfuel] | ]);
    clear H6; bash_destruct foo
| H:  wf_koika_sched_log_pair (Log_app (?action_log) (?log1)) (?log2),
  H1: taint_action _ _ _ ?rule = Success (Some ?action_taint),
  H2: ext_fn_taint_action _ _ ?ext_taint_base_action' ?rule = Success (Some ?ext_action_taint),
  H3: taint_env_approximates_log ?taint_base_action (Log__koika ?action_log),
  H4: ext_fn_taint_env_approximates_log ?ext_taint_base_action (Log__ext ?action_log),
  H6: interp_action ?ext_fns ?int_fns ?struct_defs ?fuel ?max_fn_depth ?st ?gamma (Log_app ?log1 ?log2) ?action_log
             ?rule = Success ?opt_res
  |- _ =>
    pose IHfuel as foo;
    specialize foo with (1 := H) (2 := H1) (3 := H2) (5 := H3) (6 := H4) (9 := H6)
end.

  - t_interp_action_equiv_custom IHfuel foo; repeat t_interp_action_equiv IHfuel.
    destruct_match; repeat t_interp_action_equiv IHfuel.
    destruct_match; repeat t_interp_action_equiv IHfuel;
      t_interp_action_equiv_custom IHfuel foo; repeat t_interp_action_equiv IHfuel.
Lemma does_not_conflict_may_read0:
  forall idx base2 base1 log2 taint,
  does_not_conflict base2 base1 = true ->
  taint_env_approximates_log base2 log2 ->
  LE_may_read0 (log_get log2 idx) = false ->
  SortedExtFnEnv.opt_get base1 idx = Some taint ->
  taint_read0 taint = true -> False.
Proof.
  intros * does_not_conflict approx may_read0 taint hread0.
  consider StaticAnalysis.does_not_conflict.
  rewrite forallb_forall in *. consider taint_env_approximates_log.
  consider get_reg_taint_default. consider taint_approximates_log_entry.
  specialize (approx idx). consider le_to_taint.
  inversions approx.
  consider LE_may_read0. bash_destruct may_read0; propositional; bash_destruct tle_write0;
    try discriminate; specialize (does_not_conflict (idx, (t, taint0)));
    rewrite SortedRegEnv.In_to_list in *;
    rewrite SortedRegEnv.opt_get_zip_default in *; repeat simpl_match; propositional; simplify;
    consider taint_conflicts; consider conflicts_with_read0;
    try rewrite tle_write0 in * by auto;
    try rewrite tle_write1 in * by auto;
    simpl in *; try rewrite andb_true_r in *;
    destruct_with_eqn (taint_read0 taint0); simpl in *; auto; try discriminate.
  rewrite orb_true_r in *. discriminate.
Qed.

Lemma does_not_conflict_merge_taint_env_r:
  forall base2 base1 base0,
    does_not_conflict base2 (merge_taint_env base1 base0) = true ->
    does_not_conflict base2 base0 = true.
Proof.
  consider does_not_conflict. consider merge_taint_env.
  intros. rewrite forallb_forall in *. intros.
  destruct_match; propositional.
  rewrite SortedExtFnEnv.In_to_list in *.
  autorewrite with solve_taint in *.
  destruct_match; propositional; simplify.
  bash_destruct H0; simplify; simpl; auto.
  - destruct_with_eqn (SortedExtFnEnv.opt_get base1 t ).
    + specialize (H (t, (t0,merge_taints t2 t1))).
      rewrite SortedExtFnEnv.In_to_list in *.
      autorewrite with solve_taint in *. repeat simpl_match; propositional.
      simplify. consider taint_conflicts. consider merge_taints; simpl in *; simplify.
      rewrite negb_true_iff.
      repeat rewrite orb_false_iff in *.
      repeat rewrite andb_false_iff in *.
      repeat rewrite orb_false_iff in *.
      propositional.
      split_ands_in_goal; auto; split_cases; propositional.
    + specialize (H (t, (t0,merge_taints empty_taint t1))).
      rewrite SortedExtFnEnv.In_to_list in *.
      autorewrite with solve_taint in *. repeat simpl_match; propositional.
  - rewrite taint_conflicts_empty_l_false. auto.
Qed.
Lemma lwrite0_latest_write:
  forall log idx,
  lwrite1 (log_get log idx) = None ->
  latest_write (log_get log idx) = lwrite0 (log_get log idx).
Proof.
  intros. consider latest_write. simpl_match.
  destruct_match; auto.
Qed.
Lemma does_not_conflict_may_read1:
  forall idx base2 base1 log2 taint,
  does_not_conflict base2 base1 = true ->
  taint_env_approximates_log base2 log2 ->
  LE_may_read1 (log_get log2 idx) = false ->
  SortedExtFnEnv.opt_get base1 idx = Some taint ->
  taint_read1 taint = true -> False.
Proof.
  intros * does_not_conflict approx may_read1 taint hread1.
  consider StaticAnalysis.does_not_conflict.
  rewrite forallb_forall in *. consider taint_env_approximates_log.
  consider get_reg_taint_default. consider taint_approximates_log_entry.
  specialize (approx idx). consider le_to_taint.
  inversions approx.
  consider LE_may_read1. bash_destruct may_read1; propositional; bash_destruct tle_write1;
    try discriminate; specialize (does_not_conflict (idx, (t, taint0)));
    rewrite SortedRegEnv.In_to_list in *;
    rewrite SortedRegEnv.opt_get_zip_default in *; repeat simpl_match; propositional; simplify;
    consider taint_conflicts; consider conflicts_with_read1;
    try rewrite tle_write0 in * by auto;
    try rewrite tle_write1 in * by auto;
    simpl in *; try rewrite andb_true_r in *;
    destruct_with_eqn (taint_read1 taint0); simpl in *; auto; try discriminate.
    repeat rewrite orb_true_r in *.  discriminate.
Qed.
Lemma does_not_conflict_may_write0:
  forall idx base2 base1 log2 taint,
  does_not_conflict base2 base1 = true ->
  taint_env_approximates_log base2 log2 ->
  LE_may_write0 (log_get log2 idx) = false ->
  SortedExtFnEnv.opt_get base1 idx = Some taint ->
  taint_write0 taint = true -> False.
Proof.
  intros * does_not_conflict approx may_write0 taint hwrite0.
  consider StaticAnalysis.does_not_conflict.
  rewrite forallb_forall in *. consider taint_env_approximates_log.
  consider get_reg_taint_default. consider taint_approximates_log_entry.
  specialize (approx idx). consider le_to_taint.
  inversions approx.
  consider LE_may_write0. bash_destruct may_write0; propositional; bash_destruct tle_write0;
    try discriminate; specialize (does_not_conflict (idx, (t, taint0)));
    rewrite SortedRegEnv.In_to_list in *;
    rewrite SortedRegEnv.opt_get_zip_default in *; repeat simpl_match; propositional; simplify;
    consider taint_conflicts; consider conflicts_with_write0;
    try rewrite tle_write0 in * by auto;
    try rewrite tle_write1 in * by auto;
    try rewrite tle_read1 in * by auto;
    simpl in *; try rewrite andb_true_r in *;
    destruct_with_eqn (taint_write0 taint0); simpl in *; auto; try discriminate;
    repeat rewrite orb_true_r in *; try discriminate.
Qed.
Lemma does_not_conflict_may_write1:
  forall idx base2 base1 log2 taint,
  does_not_conflict base2 base1 = true ->
  taint_env_approximates_log base2 log2 ->
  LE_may_write1 (log_get log2 idx) = false ->
  SortedExtFnEnv.opt_get base1 idx = Some taint ->
  taint_write1 taint = true -> False.
Proof.
  intros * does_not_conflict approx may_write1 taint hwrite1.
  consider StaticAnalysis.does_not_conflict.
  rewrite forallb_forall in *. consider taint_env_approximates_log.
  consider get_reg_taint_default. consider taint_approximates_log_entry.
  specialize (approx idx). consider le_to_taint.
  inversions approx.
  consider LE_may_write1. bash_destruct may_write1; propositional; bash_destruct tle_write1;
    try discriminate; specialize (does_not_conflict (idx, (t, taint0)));
    rewrite SortedRegEnv.In_to_list in *;
    rewrite SortedRegEnv.opt_get_zip_default in *; repeat simpl_match; propositional; simplify;
    consider taint_conflicts; consider conflicts_with_write1;
    try rewrite tle_write0 in * by auto;
    try rewrite tle_write1 in * by auto;
    try rewrite tle_read1 in * by auto;
    simpl in *; try rewrite andb_true_r in *;
    destruct_with_eqn (taint_write0 taint0); simpl in *; auto; try discriminate;
    repeat rewrite orb_true_r in *; try discriminate.
  all: try rewrite hwrite1 in *; try rewrite orb_true_r in *; discriminate.
Qed.


Lemma LE_may_write0_log_get_app_l:
  forall (log1 log2 : Log_t) (idx : reg_t),
  LE_may_write0 (log_get (log_app (Log__koika log1) (Log__koika log2)) idx) = true ->
  LE_may_write0 (log_get (Log__koika log2) idx) = true.
Proof.
  unfold log_app, log_get. intros *. consider LE_may_write0. consider logentry_app.
  autorewrite with solve_taint. repeat destruct_match; simpl in *; auto; try discriminate.
  all: try rewrite orb_true_r in *; try discriminate.
  - destruct_with_eqn (lwrite0 l); simpl in *; discriminate.
  - destruct_with_eqn (lwrite1 l); simpl in *; discriminate.
Qed.
Lemma LE_may_write0_false_r:
  forall log1 log2 idx,
  LE_may_write0 (log_get (log_app log1 log2) idx) = false ->
  LE_may_write0 (log_get (log1) idx) = true ->
  LE_may_write0 (log_get (log2) idx) = false.
Proof.
  consider LE_may_write0. intros. rewrite get_log_app in *. simpl in *.
  bash_destruct H0. auto.
Qed.
Lemma LE_may_write1_log_get_app_l:
  forall (log1 log2 : Log_t) (idx : reg_t),
  LE_may_write1 (log_get (log_app (Log__koika log1) (Log__koika log2)) idx) = true ->
  LE_may_write1 (log_get (Log__koika log2) idx) = true.
Proof.
  unfold log_app, log_get. intros *. consider LE_may_write1. consider logentry_app.
  autorewrite with solve_taint. repeat destruct_match; simpl in *; auto; try discriminate.
  all: try rewrite orb_true_r in *; try discriminate.
  - destruct_with_eqn (lwrite1 l); simpl in *; discriminate.
Qed.
Lemma LE_may_write1_false_r:
  forall log1 log2 idx,
  LE_may_write1 (log_get (log_app log1 log2) idx) = false ->
  LE_may_write1 (log_get (log1) idx) = true ->
  LE_may_write1 (log_get (log2) idx) = false.
Proof.
  consider LE_may_write1. intros. rewrite get_log_app in *. simpl in *.
  bash_destruct H0. auto.
Qed.

  - destruct_match; repeat t_interp_action_equiv IHfuel.
    + destruct_matches_in_hyp hrule; simplify; repeat t_interp_action_equiv IHfuel;
      try match goal with
      | H: LE_may_read0 (log_get ?log ?idx) = true,
          H2: r_get_reg (commit_update ?st ?log) ?idx = _,
            H3: r_get_reg ?st ?idx = Success _ |- _ =>
          rewrite r_get_reg_commit_update_may_read0 with (1 := H) in H2;
          rewrite H3 in H2; simplify
      end; auto.
      * apply wf_koika_sched_log_pair_set_read0; auto.
      * apply taint_env_approximates_log_set__read0; auto.
      * destruct_match; auto. repeat t_interp_action_equiv IHfuel.
        exfalso.
        apply does_not_conflict_merge_taint_env_r in hconflict.
        destruct_with_eqn (SortedExtFnEnv.opt_get taint_base_action idx);
          eapply does_not_conflict_may_read0; eauto; unfold set_reg_taint;
          try rewrite SortedExtFnEnv.update_correct_eq; try simpl_match; eauto.
    + bash_destruct htaint; simplify.
      destruct_matches_in_hyp hrule; simplify; repeat t_interp_action_equiv IHfuel;
        repeat simpl_match; repeat t_interp_action_equiv IHfuel; simpl.
      * apply wf_koika_sched_log_pair_set_read1; auto.
      * apply taint_env_approximates_log_set__read1; auto.
      * destruct_match.
        { rewrite get_log_app in *. simpl in *. rewrite Heqo1 in *. simpl in *. simplify.
          repeat t_interp_action_equiv IHfuel.
          - apply wf_koika_sched_log_pair_set_read1; auto.
          - apply taint_env_approximates_log_set__read1; auto.
        }
        { rewrite get_log_app in *. simpl in *. rewrite Heqo1 in *. simpl in *.
          unfold r_get_reg in *. simplify. unfold commit_update in *. rewrite SortedRegEnv.opt_get_map in *.
          simpl_match.
          consider LE_may_read1; simplify; auto.
          erewrite lwrite0_latest_write; eauto; simplify. repeat simpl_match.
          repeat t_interp_action_equiv IHfuel.
          - apply wf_koika_sched_log_pair_set_read1; auto.
            unfold LE_may_read1; simpl_match; auto.
          - apply taint_env_approximates_log_set__read1; auto.
        }
      * erewrite lwrite0_log_app_None_r; eauto.
        unfold r_get_reg in *. simplify. unfold commit_update in *. rewrite SortedRegEnv.opt_get_map in *.
        consider latest_write. consider LE_may_read1. simplify.
        erewrite lwrite0_log_app_None_l; eauto.
        repeat t_interp_action_equiv IHfuel.
        { apply wf_koika_sched_log_pair_set_read1; auto. consider LE_may_read1; simpl_match; auto. }
        { apply taint_env_approximates_log_set__read1; auto. }
      * destruct_match; auto.
        { apply LE_may_read1_log_app_false in Heqb0; auto.
        apply does_not_conflict_merge_taint_env_r in hconflict.
        exfalso.
        eapply does_not_conflict_may_read1 with (1 := hconflict) (2 := hlog2_approx) (3 := Heqb0); eauto.
        { unfold set_reg_taint; try rewrite SortedExtFnEnv.update_correct_eq; try simpl_match; eauto. }
        { destruct_match; auto. }
    }
  - destruct_match; repeat t_interp_action_equiv IHfuel.
    + assert (action_taint = (set_reg_taint t idx set_taint_write0)).
      { bash_destruct htaint; simplify. }
      assert (taint_env_le t action_taint); subst.
      { subst. apply taint_env_le_write0. }
      repeat t_interp_action_equiv IHfuel.
      destruct_matches_in_hyp hrule; repeat t_interp_action_equiv IHfuel.
      { destruct_match; repeat t_interp_action_equiv IHfuel; simpl.
        - apply wf_koika_sched_log_pair_set_write0; auto.
          eapply LE_may_write0_log_get_app_l; eauto.
        - apply taint_env_approximates_log_set__write0; auto.
        - exfalso. split_cases; try congruence.
          apply LE_may_write0_log_get_app_r in Heqb0.
          congruence.
      }
      { destruct_match; repeat t_interp_action_equiv IHfuel; split_cases; try congruence.
        - exfalso.
          apply does_not_conflict_merge_taint_env_r in hconflict.
          eapply does_not_conflict_may_write0 with (1 := hconflict) (2 := hlog2_approx).
          { eapply LE_may_write0_false_r; eauto. }
          { unfold set_reg_taint; try rewrite SortedExtFnEnv.update_correct_eq; try simpl_match; eauto. }
          { destruct_match; auto. }
        - apply wf_koika_sched_log_pair_set_write0; auto.
          destruct_with_eqn (LE_may_write0 (log_get (Log__koika log2) idx)); auto.
          exfalso.
          apply does_not_conflict_merge_taint_env_r in hconflict.
          eapply does_not_conflict_may_write0 with (1 := hconflict) (2 := hlog2_approx) (3 := Heqb).
          { unfold set_reg_taint; try rewrite SortedExtFnEnv.update_correct_eq; try simpl_match; eauto. }
          { destruct_match; auto. }
        - simpl. apply taint_env_approximates_log_set__write0; auto.
      }
    + assert (action_taint = (set_reg_taint t idx set_taint_write1)).
      { bash_destruct htaint; simplify. }
      assert (taint_env_le t action_taint); subst.
      { subst. apply taint_env_le_write1. }
      repeat t_interp_action_equiv IHfuel.
      destruct_matches_in_hyp hrule; repeat t_interp_action_equiv IHfuel.
      { destruct_match; repeat t_interp_action_equiv IHfuel; simpl.
        - apply wf_koika_sched_log_pair_set_write1; auto.
          eapply LE_may_write1_log_get_app_l; eauto.
        - apply taint_env_approximates_log_set__write1; auto.
        - exfalso. split_cases; try congruence.
          apply LE_may_write1_log_get_app_r in Heqb0.
          congruence.
      }
      { destruct_match; repeat t_interp_action_equiv IHfuel; split_cases; try congruence.
        - exfalso.
          apply does_not_conflict_merge_taint_env_r in hconflict.
          eapply does_not_conflict_may_write1 with (1 := hconflict) (2 := hlog2_approx).
          { eapply LE_may_write1_false_r; eauto. }
          { unfold set_reg_taint; try rewrite SortedExtFnEnv.update_correct_eq; try simpl_match; eauto. }
          { destruct_match; auto. }
        - apply wf_koika_sched_log_pair_set_write1; auto.
          destruct_with_eqn (LE_may_write1 (log_get (Log__koika log2) idx)); auto.
          exfalso.
          apply does_not_conflict_merge_taint_env_r in hconflict.
          eapply does_not_conflict_may_write1 with (1 := hconflict) (2 := hlog2_approx) (3 := Heqb).
          { unfold set_reg_taint; try rewrite SortedExtFnEnv.update_correct_eq; try simpl_match; eauto. }
          { destruct_match; auto. }
        - simpl. apply taint_env_approximates_log_set__write1; auto.
      }
  - assert (ext_action_taint = (SortedExtFnEnv.update e fn (fun _ : bool => true) false)).
    { bash_destruct hext_taint. simplify. }
    assert (ext_fn_taint_env_subset e ext_action_taint).
    { bash_destruct hext_taint; simplify; apply ext_fn_taint_env_subset_update. }
    repeat t_interp_action_equiv IHfuel.
    destruct_matches_in_hyp hrule; repeat t_interp_action_equiv IHfuel.
    { destruct_match; repeat t_interp_action_equiv IHfuel; simpl.
      - apply wf_koika_sched_log_pair_ext_update; auto.
        eapply ext_log_can_call_app_l; eauto.
      - apply ext_fn_taint_env_approximates_log_update; auto.
      - exfalso. split_cases; try congruence.
        apply ext_log_can_call_app_r in Heqb0. congruence.
    }
    {
      destruct_match; repeat t_interp_action_equiv IHfuel; split_cases; try congruence.
      rewrite ext_log_can_call_false_iff in *. split_cases; try congruence.
      exfalso.
      eapply ext_fn_taint_env_conflicts_false; eauto.
      unfold merge_ext_fn_taint_env. autorewrite with solve_taint.
      rewrite SortedExtFnEnv.update_correct_eq.
      repeat destruct_match; rewrite orb_true_r; auto.
    }
Qed.

Lemma interp_rule_equiv:
  forall ext_fns int_fns struct_defs st log1 log2 opt_log rl rl_taint rl_ext_taint taint_base1
    taint_base2 ext_taint_base1 ext_taint_base2,
  wf_koika_sched_log_pair (log1) (log2) ->
  taint_rule int_fns taint_empty rl = Success (Some rl_taint) ->
  ext_fn_taint_rule int_fns ext_taint_base1 rl  = Success (Some rl_ext_taint) ->
  taint_env_approximates_log taint_base1 (Log__koika log1) ->
  taint_env_approximates_log taint_base2 (Log__koika log2) ->
  ext_fn_taint_env_approximates_log ext_taint_base1 (Log__ext log1) ->
  ext_fn_taint_env_approximates_log ext_taint_base2 (Log__ext log2) ->
  does_not_conflict taint_base2 (merge_taint_env taint_base1 rl_taint) = true ->
  ext_fn_taint_env_conflicts ext_taint_base2 (merge_ext_fn_taint_env ext_taint_base1 rl_ext_taint) = false ->
  interp_rule ext_fns int_fns struct_defs st (Log_app log1 log2) rl = Success opt_log ->
  match interp_rule ext_fns int_fns struct_defs (commit_update st (Log__koika log2)) log1 rl with
  | Success (Some res) =>
      opt_log = Some res /\
        wf_koika_sched_log_pair ((Log_app res log1)) (log2)
  | Success None => opt_log = None
  | _ => False
  end.
Proof.
  unfold interp_rule.
  intros * hwf htaint hext_taint happrox1 happrox2 hext_approx1 hext_approx2 hconflict hext_conflict hrule.
  bash_destruct hrule; simplify.
  - eapply interp_action_equiv with (ext_taint_base_action := SortedExtFnEnv.empty) in Heqr; simplify; eauto.
    + bash_destruct Heqr; propositional; eauto. simplify. simpl.
      split_ands_in_goal; auto.
    + setoid_rewrite<-Log_app_empty_l. auto.
    + rewrite merge_ext_fn_taint_env_empty_l. apply ext_fn_taint_env_subset_refl.
    + simpl. apply taint_env_approximates_log_empty.
    + simpl. apply ext_fn_taint_env_approximates_log_empty.
  - eapply interp_action_equiv with (ext_taint_base_action := SortedExtFnEnv.empty) in Heqr; simplify; eauto.
    + bash_destruct Heqr; propositional; discriminate.
    + setoid_rewrite<-Log_app_empty_l. auto.
    + rewrite merge_ext_fn_taint_env_empty_l. apply ext_fn_taint_env_subset_refl.
    + simpl. apply taint_env_approximates_log_empty.
    + simpl. apply ext_fn_taint_env_approximates_log_empty.
Qed.
Lemma ext_fn_taint_env_subset_merge_l_implied:
  forall e1 e2 e3,
  ext_fn_taint_env_subset e1 e3 ->
  ext_fn_taint_env_subset e2 e3 ->
  ext_fn_taint_env_subset (merge_ext_fn_taint_env e1 e2) e3.
Proof.
  consider ext_fn_taint_env_subset. intros.
  consider merge_ext_fn_taint_env.
  rewrite SortedExtFnEnv.opt_get_mapV in *.
  rewrite SortedExtFnEnv.opt_get_zip_default in *.
  specialize (H fn). specialize (H0 fn).
  bash_destruct H1; propositional; simplify.
  - destruct b; simpl in *; propositional.
  - propositional.
Qed.

Lemma interp_scheduler_equiv:
  forall {rule_name_t: Type} (rules: rule_name_t -> rule) sched ext_fns int_fns struct_defs st log res log1 log2
    taint_base2 ext_taint_base2 taint_full ext_taint_full taint_base1 ext_taint_base1,
  interp_scheduler' ext_fns int_fns struct_defs st rules sched log = Success res ->
  log = Log_app log1 log2 ->
  wf_koika_sched_log_pair (log1) (log2) ->
  taint_schedule int_fns rules taint_base1 sched = Success (Some taint_full) ->
  ext_fn_taint_schedule int_fns rules ext_taint_base1 sched = Success (Some ext_taint_full) ->
  does_not_conflict taint_base2 taint_full = true ->
  ext_fn_taint_env_conflicts ext_taint_base2 ext_taint_full = false ->
  taint_env_approximates_log taint_base1 (Log__koika log1) ->
  ext_fn_taint_env_approximates_log ext_taint_base1 (Log__ext log1) ->
  taint_env_approximates_log taint_base2 (Log__koika log2) ->
  ext_fn_taint_env_approximates_log ext_taint_base2 (Log__ext log2) ->
  match interp_scheduler' ext_fns int_fns struct_defs (commit_update st (Log__koika log2)) rules sched log1 with
  | Success res' => Log__koika res = log_app (Log__koika res') (Log__koika log2) /\
                   Log__ext res = ext_log_app (Log__ext res') (Log__ext log2) /\
                   wf_koika_sched_log_pair (res') (log2) /\
                   taint_env_approximates_log (merge_taint_env taint_full taint_base2) (Log__koika res) /\
                   ext_fn_taint_env_approximates_log (merge_ext_fn_taint_env ext_taint_full ext_taint_base2) (Log__ext res)
  | _ => False
  end.
Proof.
  induction sched; propositional; simpl in *; simplify.
  - split_ands_in_goal; auto.
    + rewrite<-log_app_Log_app__koika.  rewrite merge_taint_env_comm.
      apply taint_env_approximates_append; auto.
    + rewrite<-ext_log_app_log_app. rewrite merge_ext_fn_taint_env_comm.
      apply ext_fn_taint_env_approximates_append; auto; auto.
  - consider @res_opt_bind. simplify.
    eapply interp_rule_equiv in Heqr0; eauto.
    2: { eapply does_not_conflict_subset; eauto.
         eapply taint_schedule_subset; eauto.
         rewrite merge_taint_env_comm. eauto.
       }
    bash_destruct H; eauto; simplify.
    + bash_destruct Heqr0; try discriminate. propositional. simplify.
      specialize IHsched with (1 := H) (4 := H2) (5 := H3)
                              (log1 := Log_app l0 log1) (log2 := log2)
                              (taint_base2 := taint_base2) (ext_taint_base2 := ext_taint_base2).
      assert_pre_and_specialize IHsched.
      { rewrite<-Log_app_assoc; auto. }
      assert_pre_and_specialize IHsched.
      { auto. }
      assert_pre_and_specialize IHsched.
      { auto. }
      assert_pre_and_specialize IHsched.
      { auto. }
      assert_pre_and_specialize IHsched.
      { specialize taint_rule_approximates_log with (1 := Heqr3) (2 := Heqr2). intros.
        rewrite merge_taint_env_comm.
        apply taint_env_approximates_append; auto.
      }
      assert_pre_and_specialize IHsched.
      { rewrite<-ext_log_app_log_app.
        apply ext_fn_taint_env_approximates_log_app; auto.
        - eapply ext_fn_taint_rule_correct; eauto.
        - eapply ext_fn_taint_env_approximates_log_subset; eauto.
          eapply ext_fn_taint_rule_subset; eauto.
      }
      assert_pre_and_specialize IHsched.
      { auto. }
      assert_pre_and_specialize IHsched.
      { auto. }
      simplify. propositional.
    + bash_destruct Heqr0; propositional; try discriminate.
      consider @res_opt_bind. simplify.
      eapply IHsched; eauto.
      { apply taint_env_approximates_log_add_taints_r. auto. }
      { apply ext_fn_taint_rule_subset in Heqr1.
        eapply ext_fn_taint_env_approximates_log_subset; eauto.
      }
  + eapply ext_fn_conflicts_subset; eauto.
    apply ext_fn_taint_env_subset_merge_l_implied; auto.
    * eapply ext_fn_taint_env_subset_trans; eauto.
      { eapply ext_fn_taint_rule_subset; eauto. }
      { eapply ext_fn_taint_schedule_subset; eauto. }
    * eapply ext_fn_taint_schedule_subset; eauto.
Qed.



    Lemma check_modular_conflicts_correct':
      forall {rule_name_t: Type} (rules: rule_name_t -> rule) mod_schedule log log' st taint ext_taint st',
        modular_schedule_does_not_conflict' rules mod_schedule (true, taint, ext_taint) = true ->
        interp_scheduler' ext_fns int_fns struct_defs st rules
          (concatenate_modular_schedule mod_schedule) log = Success log' ->
        taint_env_approximates_log taint (Log__koika log) ->
        ext_fn_taint_env_approximates_log ext_taint (Log__ext log) ->
        commit_update st (Log__koika log) = st' ->
        interp_modular_schedule' ext_fns int_fns struct_defs rules st' (Log__ext log) mod_schedule =
          Success (commit_update st (Log__koika log'), (Log__ext log')).
    Proof.
      induction mod_schedule; simpl in *; propositional; simplify; auto.
      bash_destruct H. rewrite andb_true_iff in *. propositional; simplify.
      rewrite interp_scheduler'_concatenate in H0. simplify.
      consider interp_scheduler.
      specialize @interp_scheduler_equiv with (1 := Heqr1) (4 := Heqr) (5 := Heqr0) ( 6 := Heqb0) (7 := Heqb1)
                                              (log1 := Log_empty) (2 := Log_app_empty_l _)
                                              (3 := wf_koika_sched_log_pair_empty_l _ ); intros Hequiv; propositional.
      specialize Hequiv with (1 := taint_env_approximates_log_empty' _ )
                             (2 := ext_fn_taint_env_approximates_log_empty' _ ).
      propositional.
      simplify. propositional.
      rewrite commit_update_commit_update.
      2: { propositional. } propositional.
      specialize IHmod_schedule with (1 := H) (2 := H0) (5 := eq_refl).
      propositional. rewrite Hequiv0 in *. rewrite Hequiv2 in *.
      apply IHmod_schedule; auto.
      rewrite merge_ext_fn_taint_env_comm. auto.
    Qed.

    Lemma check_modular_conflicts_correct:
      forall {rule_name_t: Type} (rules: rule_name_t -> rule) mod_schedule log st,
      modular_schedule_does_not_conflict rules mod_schedule = true ->
      interp_scheduler ext_fns int_fns struct_defs st rules (concatenate_modular_schedule mod_schedule) = Success log ->
      interp_modular_schedule ext_fns int_fns struct_defs rules st mod_schedule = Success (commit_update st log.(Log__koika), log.(Log__ext)).
    Proof.
      unfold modular_schedule_does_not_conflict.
      unfold interp_scheduler. unfold interp_modular_schedule.
      intros * hmod hsched.
      eapply check_modular_conflicts_correct' with (log := Log_empty); eauto; simpl.
      - apply taint_env_approximates_log_empty.
      - apply ext_fn_taint_env_approximates_log_empty.
      - apply commit_update_empty.
    Qed.

    Corollary ext_fn_taint_schedule_empty_correct_fn:
      forall {rule_name_t: Type} (rules: rule_name_t -> rule)
        st log' schedule fn,
        match ext_fn_taint_schedule int_fns rules SortedExtFnEnv.empty schedule with
        | Success (Some res_env) =>
          match SortedExtFnEnv.opt_get res_env fn with
          | None => true
          | _ => false
          end
        | _ => false
        end = true ->
        interp_scheduler ext_fns int_fns struct_defs st rules schedule = Success log' ->
        SortedExtFnEnv.opt_get (Log__ext log') fn = None.
    Proof.
      consider interp_scheduler. intros.
      bash_destruct H. eapply ext_fn_taint_schedule_empty_correct in Heqr; eauto.
    Qed.

End TODO_ORAAT_MOVE.

(* Module BoxSimCorrect. *)

(*   Import BoxSimAnalysis. *)

(*   Include BoxSimPreserved. *)

(*   Section BoxSimAnalysis. *)
(*     Context (int_fns: @int_fn_env_t N (@action N)). *)
(*     Context (struct_defs: @struct_env_t N). *)
(*     Context (box_t: Type). *)
(*     Context {box_t_eq_dec: EqDec box_t}. *)
(*     Context (box_defs: list (box_t * box_def)). *)
(*     (* Context (box_fns: list (fn_name_t * (box_t * list ext_fn_t))). *) *)

(*     Notation RegsNotInBoxes := (@RegsNotInBoxes box_t). *)
(*     Notation BoxRegsUnique := (@BoxRegsUnique box_t). *)
(*     Notation BoxRegsDisjoint := (@BoxRegsDisjoint box_t). *)

(*     (* For all registers in the environment, there is no box that contains the register *) *)
(*     Lemma computable_RegsNotInBoxes_correct: *)
(*       forall env boxes, *)
(*       computable_RegsNotInBoxes env boxes = true -> *)
(*       RegsNotInBoxes env boxes. *)
(*     Proof. *)
(*       unfold computable_RegsNotInBoxes. unfold RegsNotInBoxes. *)
(*       intros * Hcompute * Hreg Hin_box Hin_def. rewrite forallb_forall in *. unfold RegsNotInBoxes. *)
(*       rewrite<-SortedRegEnv.In_to_list in Hreg. *)
(*       specialize (Hcompute _ Hreg). simpl in Hcompute. rewrite forallb_forall in *. *)
(*       specialize (Hcompute _ Hin_box). simpl in *. rewrite negb_true_iff in Hcompute. *)
(*       apply existsb_false_forall in Hcompute. rewrite forallb_forall in *. specialize (Hcompute _ Hin_def). *)
(*       rewrite negb_true_iff in *. simplify. contradiction. *)
(*     Qed. *)

(*     Lemma computable_BoxRegsUnique_correct: *)
(*       forall boxes, *)
(*       computable_BoxRegsUnique boxes = true -> *)
(*       BoxRegsUnique boxes. *)
(*     Proof. *)
(*       unfold computable_BoxRegsUnique. *)
(*       intros * Hunique. unfold BoxRegsUnique. intros. *)
(*       eapply unique_correct in Hunique; eauto. *)
(*     Qed. *)

(*     Lemma computable_BoxRegsDisjoint_correct: *)
(*       forall boxes, *)
(*       computable_BoxRegsDisjoint boxes = true -> *)
(*       BoxRegsDisjoint boxes. *)
(*     Proof. *)
(*       unfold BoxRegsDisjoint. induction boxes; auto. *)
(*       simpl. intros. destruct_match_pairs; simplify. *)
(*       destruct_all_matches; auto. *)
(*       + split_cases. simplify. auto. *)
(*       + rewrite andb_true_iff in *. propositional. rewrite forallb_forall in *. *)
(*         split_cases; simplify; auto. *)
(*         * specialize H4 with (1 := H3). rewrite negb_true_iff in *. *)
(*           apply existsb_false_forall in H4. rewrite forallb_forall in *. *)
(*           specialize H4 with (1 := H0). rewrite negb_true_iff in *. *)
(*           apply existsb_false_forall in H4. rewrite forallb_forall in H4. *)
(*           specialize H4 with (1 := H2). rewrite beq_dec_refl in H4. discriminate. *)
(*         * specialize H4 with (1 := H2). rewrite negb_true_iff in *. *)
(*           apply existsb_false_forall in H4. rewrite forallb_forall in *. *)
(*           specialize H4 with (1 := H). rewrite negb_true_iff in *. *)
(*           apply existsb_false_forall in H4. rewrite forallb_forall in H4. *)
(*           specialize H4 with (1 := H3). rewrite beq_dec_refl in *. discriminate. *)
(*     Qed. *)

(*   Lemma computable_WF_boxes_correct: *)
(*     forall boxes, *)
(*     computable_WF_boxes boxes  = true -> *)
(*     WF_boxes boxes. *)
(*   Proof. *)
(*     unfold computable_WF_boxes. intros. rewrite andb_true_iff in *. propositional. *)
(*     constructor. *)
(*     - apply computable_BoxRegsUnique_correct. auto. *)
(*     - apply computable_BoxRegsDisjoint_correct. auto. *)
(*   Qed. *)
(* Create HintDb solve_box_sim. *)
(* Lemma merge_sim_regs_comm: *)
(*   forall sim1 sim2, *)
(*   merge_sim_regs sim1 sim2 = merge_sim_regs sim2 sim1. *)
(* Proof. *)
(*   unfold merge_sim_regs. *)
(*   intros. apply SortedRegEnv.env_ext. *)
(*   intros. repeat rewrite SortedRegEnv.opt_get_mapV, SortedRegEnv.opt_get_zip_default. *)
(*   destruct_all_matches; rewrite andb_comm; auto. *)
(* Qed. *)

(* Lemma RegsNotInBoxes_merge_l: *)
(*   forall sim1 sim2 box_defs, *)
(*   RegsNotInBoxes sim1 box_defs -> *)
(*   RegsNotInBoxes (merge_sim_regs sim1 sim2) box_defs. *)
(* Proof. *)
(*   unfold RegsNotInBoxes, merge_sim_regs. *)
(*   intros * Hsim1 * Hget Hin_box Hreg. *)
(*   rewrite SortedRegEnv.opt_get_mapV in Hget. *)
(*   rewrite SortedRegEnv.opt_get_zip_default in Hget. *)
(*   destruct_all_matches; simplify; rewrite andb_true_iff in *; propositional; try discriminate. *)
(*   specialize Hsim1 with (1 := Heqo). *)
(*   eauto. *)
(* Qed. *)

(* Lemma RegsNotInBoxes_merge_r: *)
(*   forall sim1 sim2 box_defs, *)
(*   RegsNotInBoxes sim2 box_defs -> *)
(*   RegsNotInBoxes (merge_sim_regs sim1 sim2) box_defs. *)
(* Proof. *)
(*   intros. rewrite merge_sim_regs_comm. apply RegsNotInBoxes_merge_l. auto. *)
(* Qed. *)

(* Lemma RegsNotInBoxes_update: *)
(*   forall defs sim idx b, *)
(*   RegsNotInBoxes sim defs -> *)
(*   reg_in_box_defs defs idx = false -> *)
(*   RegsNotInBoxes (update_sim_reg' sim idx b) defs. *)
(* Proof. *)
(*   unfold RegsNotInBoxes. *)
(*   intros * Hsim Hreg * Hupdate HIn_box HIn_reg. *)
(*   consider @reg_in_box_defs. *)
(*   consider @update_sim_reg'. *)
(*   apply existsb_false_forall in Hreg. *)
(*   rewrite forallb_forall in Hreg. *)
(*   consider @update_sim_reg. *)
(*   destruct_with_eqn (beq_dec idx reg); simplify. *)
(*   - rewrite SortedRegEnv.update_correct_eq in Hupdate. *)
(*     specialize (Hreg def). rewrite negb_true_iff in Hreg. *)
(*     assert_pre_and_specialize Hreg. *)
(*     { apply in_map with (f := snd) in HIn_box. assumption. } *)
(*     apply existsb_false_forall in Hreg. *)
(*     rewrite forallb_forall in Hreg. *)
(*     specialize (Hreg _ HIn_reg). rewrite negb_true_iff in Hreg. simplify. auto. *)
(*   - rewrite SortedRegEnv.update_correct_neq in Hupdate by auto. eauto. *)
(* Qed. *)

(* Definition reg_sim_le sim1 sim2 : Prop := *)
(*   (forall idx, SortedRegEnv.opt_get sim1 idx = Some true -> SortedRegEnv.opt_get sim2 idx = Some true). *)

(* Definition box_sim_le (sim1 sim2: list box_t) : Prop := *)
(*   forall box, In box sim1 -> In box sim2. *)

(* Definition sim_state_le (sim1 sim2: sim_state_t) := *)
(*   reg_sim_le sim1.(sim_regs) sim2.(sim_regs) /\ *)
(*   box_sim_le sim1.(sim_boxes) sim2.(sim_boxes). *)

(* Lemma RegNotInBoxes_decreases_preserve: *)
(*   forall box_defs sim sim', *)
(*   RegsNotInBoxes sim box_defs -> *)
(*   reg_sim_le sim' sim -> *)
(*   RegsNotInBoxes sim' box_defs. *)
(* Proof. *)
(*   unfold RegsNotInBoxes in *. consider reg_sim_le. *)
(*   intros * Hsim Hdecrease. *)
(*   intros. apply Hdecrease in H. eauto. *)
(* Qed. *)
(* Lemma reg_sim_le_refl: *)
(*   forall st, reg_sim_le st st. *)
(* Proof. *)
(*   consider reg_sim_le; auto. *)
(* Qed. *)

(* Lemma box_sim_le_refl: *)
(*   forall st, box_sim_le st st. *)
(* Proof. *)
(*   consider box_sim_le. auto. *)
(* Qed. *)

(* Hint Immediate box_sim_le_refl: solve_box_sim. *)
(* Lemma sim_state_le_refl: *)
(*   forall st, sim_state_le st st. *)
(* Proof. *)
(*   consider sim_state_le. *)
(*   intros; split. *)
(*   - apply reg_sim_le_refl. *)
(*   - apply box_sim_le_refl. *)
(* Qed. *)
(* Lemma reg_sim_le_trans: *)
(*   forall sim1 sim2 sim3, *)
(*   reg_sim_le sim1 sim2 -> *)
(*   reg_sim_le sim2 sim3 -> *)
(*   reg_sim_le sim1 sim3. *)
(* Proof. *)
(*   consider reg_sim_le. intros. *)
(*   apply H0. apply H. auto. *)
(* Qed. *)

(* Lemma box_sim_le_trans: *)
(*   forall sim1 sim2 sim3, *)
(*   box_sim_le sim1 sim2 -> *)
(*   box_sim_le sim2 sim3 -> *)
(*   box_sim_le sim1 sim3. *)
(* Proof. *)
(*   consider box_sim_le. intros. *)
(*   apply H0. apply H. auto. *)
(* Qed. *)

(* Lemma sim_state_le_trans: *)
(*   forall sim1 sim2 sim3, *)
(*   sim_state_le sim1 sim2 -> *)
(*   sim_state_le sim2 sim3 -> *)
(*   sim_state_le sim1 sim3. *)
(* Proof. *)
(*   intros * Hsim0 Hsim1. *)
(*   consider sim_state_le. propositional. split. *)
(*   - eapply reg_sim_le_trans; eauto. *)
(*   - eapply box_sim_le_trans; eauto. *)
(* Qed. *)

(* Lemma sim_state_le_update_sim_reg_false: *)
(*   forall st idx, *)
(*   sim_state_le (update_sim_reg st idx false) st. *)
(* Proof. *)
(*   unfold sim_state_le, update_sim_reg. simpl. intros; split; eauto with solve_box_sim. *)
(*   - consider update_sim_reg'. consider reg_sim_le. *)
(*     intros. destruct_with_eqn (beq_dec idx idx0); simplify. *)
(*     + rewrite SortedRegEnv.update_correct_eq in H. bash_destruct H; auto. *)
(*     + rewrite SortedRegEnv.update_correct_neq in H by auto. auto. *)
(* Qed. *)

(* Hint Immediate sim_state_le_update_sim_reg_false : solve_box_sim. *)
(* Hint Immediate sim_state_le_trans: solve_box_sim. *)
(* Lemma sim_state_le_remove_box: *)
(*   forall st box, *)
(*   sim_state_le (remove_box st box) st. *)
(* Proof. *)
(*   consider sim_state_le. consider @remove_box. simpl. intros; split. *)
(*   - apply reg_sim_le_refl. *)
(*   - unfold box_sim_le. intros. rewrite filter_In in H. propositional. *)
(* Qed. *)


(* Hint Immediate RegsNotInBoxes_merge_l : solve_box_sim. *)
(* Hint Immediate RegsNotInBoxes_merge_r : solve_box_sim. *)
(* Hint Immediate RegsNotInBoxes_update: solve_box_sim. *)
(* Hint Immediate sim_state_le_refl: solve_box_sim. *)
(* Hint Immediate sim_state_le_remove_box : solve_box_sim. *)

(* Definition gamma_state_le (gamma1 gamma2: sim_gamma_t) : Prop := *)
(*   Forall2 (fun '(var1,v1) '(var2,v2) => *)
(*              var1 = var2 /\ (v1 = true -> v2 = true) *)
(*           ) gamma1 gamma2. *)

(* Lemma gamma_state_le_refl: forall gamma, gamma_state_le gamma gamma. *)
(* Proof. *)
(*   intros; consider gamma_state_le; induction gamma; eauto. *)
(*   constructor; auto. destruct_match_pairs; propositional. *)
(* Qed. *)

(* Lemma gamma_state_le_trans : *)
(*   forall (gamma1 gamma2 gamma3: sim_gamma_t), *)
(*   gamma_state_le gamma1 gamma2 -> *)
(*   gamma_state_le gamma2 gamma3 -> *)
(*   gamma_state_le gamma1 gamma3. *)
(* Proof. *)
(*   consider gamma_state_le. *)
(*   induction gamma1; intros * Hsim0 Hsim1. *)
(*   - destruct gamma2; [ | inversions Hsim0]. *)
(*     destruct gamma3; [ | inversions Hsim1]. *)
(*     constructor. *)
(*   - destruct gamma2; [ inversions Hsim0 | ]. *)
(*     destruct gamma3; [ inversions Hsim1 | ]. *)
(*     inversions Hsim0. inversions Hsim1. *)
(*     destruct_match_pairs; propositional. *)
(*     constructor; eauto. *)
(* Qed. *)

(* Hint Immediate gamma_state_le_trans: solve_box_sim. *)

(* Lemma gamma_state_le_update: *)
(*   forall st var v, *)
(*   varenv_lookup_var st var tt = Success v -> *)
(*   gamma_state_le (varenv_update st var false) st. *)
(* Proof. *)
(*   consider @varenv_lookup_var. consider @varenv_update. consider gamma_state_le. *)
(*   induction st; simpl; [ discriminate | ]. *)
(*   intros *. destruct_match; subst. destruct_match; propositional; simplify. *)
(*   - apply String.eqb_eq in Heqb0. subst. constructor; [split_ands_in_goal; propositional; discriminate | ]. *)
(*     apply gamma_state_le_refl. *)
(*   - constructor; propositional. *)
(*     eapply IHst; simpl_match; eauto. *)
(* Qed. *)

(* Hint Immediate gamma_state_le_refl: solve_box_sim. *)
(* Hint Immediate gamma_state_le_update: solve_box_sim. *)
(* Lemma gamma_state_le_tl: *)
(*   forall sim1 sim2 sim3 v b, *)
(*   gamma_state_le sim1 sim3 -> *)
(*   gamma_state_le sim2 (varenv_bind sim1 v b) -> *)
(*   gamma_state_le (tl sim2) sim3. *)
(* Proof. *)
(*   consider gamma_state_le. consider @varenv_bind. *)
(*   induction sim1; intros * Hsim0 Hsim1. *)
(*   - destruct sim3; [ | inversions Hsim0]. *)
(*     destruct sim2; [ inversions Hsim1| ]. simpl. *)
(*     inversions Hsim1; auto. *)
(*   - destruct sim3; [ inversions Hsim0 | ]. *)
(*     destruct sim2; [inversions Hsim1 | ]. *)
(*     simpl. *)
(*     inversions Hsim1. *)
(*     inversions Hsim0. *)
(*     destruct sim2; [inversions H4 | ]. *)
(*     inversions H4. destruct_match_pairs. propositional. *)
(*     constructor. *)
(*     + destruct_match_pairs; propositional. *)
(*     + eapply gamma_state_le_trans; eauto. *)
(* Qed. *)

(* Hint Immediate gamma_state_le_tl: solve_box_sim. *)

(* Lemma remove_tainted_action_decreases_sim': *)
(*   forall fuel int_fns box_defs box_fns sim_st sim_gamma action sim_gamma' sim_st', *)
(*   remove_tainted_action' int_fns box_defs box_fns fuel sim_st sim_gamma action = Success (Some(sim_gamma', sim_st')) -> *)
(*   gamma_state_le sim_gamma' sim_gamma /\ *)
(*   sim_state_le sim_st' sim_st. *)
(* Proof. *)
(*   induction fuel; [discriminate | ]. *)
(*   intros * Hremove. destruct action; cbn in *; unfold res_opt_bind, __debug__ in *; destruct_all_matches; *)
(*     repeat match goal with *)
(*     | H1: gamma_state_le ?g1 ?g2, *)
(*       H2: gamma_state_le ?g2 ?g3 |- _ => *)
(*         pose_fresh (gamma_state_le_trans _ _ _ H1 H2) *)
(*     | H1: sim_state_le ?s1 ?s2, *)
(*       H2: sim_state_le ?s2 ?s3 |- _ => *)
(*         pose_fresh (sim_state_le_trans _ _ _ H1 H2) *)
(*     | H: remove_tainted_action' _ _ _ _ _ _ ?action = Success (Some (_, _)) |- _ => *)
(*         apply IHfuel in H *)
(*     | _ => progress (propositional; simplify; eauto with solve_box_sim) *)
(*     end. *)
(*   - split_ands_in_goal; eauto with solve_box_sim. *)
(*     eapply gamma_state_le_trans; eauto with solve_box_sim. *)
(*   - split_ands_in_goal; eauto with solve_box_sim. *)
(*     eapply sim_state_le_trans with (2 := Heqr1); eauto with solve_box_sim. *)
(*   - split_ands_in_goal; eauto with solve_box_sim. *)
(*     eapply sim_state_le_trans; eauto with solve_box_sim. *)
(* Qed. *)

(* Theorem remove_tainted_action_decreases_sim: *)
(*   forall fuel int_fns box_defs box_fns sim_st sim_gamma action sim_gamma' sim_st', *)
(*   remove_tainted_action int_fns box_defs box_fns fuel sim_st sim_gamma action = Success (sim_gamma', sim_st') -> *)
(*   gamma_state_le sim_gamma' sim_gamma /\ *)
(*   sim_state_le sim_st' sim_st. *)
(* Proof. *)
(*   intros * Haction. consider remove_tainted_action. bash_destruct Haction; simplify. *)
(*   - eapply remove_tainted_action_decreases_sim'; eauto. *)
(*   - eauto with solve_box_sim. *)
(* Qed. *)

(*     Theorem analyze_preserves_RegsNotInBoxes: *)
(*       forall fuel1 box_defs box_fns ext_fn_sims init_reg_sims acc_reg_sims gamma_sims action *)
(*         int_fns gamma' sim' b, *)
(*       RegsNotInBoxes acc_reg_sims.(sim_regs) box_defs -> *)
(*       analyze_action int_fns box_defs box_fns ext_fn_sims init_reg_sims (* box_sims *) fuel1 *)
(*           acc_reg_sims gamma_sims action = Success (Some (gamma', sim', b)) -> *)
(*       RegsNotInBoxes sim'.(sim_regs) box_defs. *)
(*     Proof. *)
(*       induction fuel1; [discriminate | ]. *)
(*       intros * Hbox Hanalyze. *)

(*       destruct action; cbn in *; simplify; unfold res_opt_bind, opt_bind_to_res in *; unfold __debug__ in *; destruct_all_matches; *)
(*         repeat match goal with *)
(*         | H: RegsNotInBoxes (sim_regs ?sim) _, *)
(*           H1: analyze_action _ _ _ _ _ _ ?sim _ ?action = Success (Some (_, _, _)) |- _ => *)
(*             apply IHfuel1 with (1 := H) in H1 *)
(*         | |- _ => progress (simpl in *; simplify; propositional; eauto with solve_box_sim) *)
(*         end. *)
(*       - apply remove_tainted_action_decreases_sim in Heqr1. *)
(*         apply remove_tainted_action_decreases_sim in Heqr0. *)
(*         propositional. *)
(*         eapply RegNotInBoxes_decreases_preserve; eauto. *)
(*         destruct Heqr4. destruct Heqr3. *)
(*         eapply reg_sim_le_trans; eauto with solve_box_sim. *)
(*     Qed. *)

(* Hint Immediate analyze_preserves_RegsNotInBoxes: solve_box_sim. *)

(*     Theorem analyze_none_implies_fail: *)
(*       forall fuel1 box_defs box_fns ext_fn_sims init_reg_sims acc_reg_sims gamma_sims action *)
(*         sigma int_fns fuel2 r r_acc is_safe gamma res ext_fn_log, *)
(*       analyze_action int_fns box_defs box_fns ext_fn_sims init_reg_sims fuel1 *)
(*           acc_reg_sims gamma_sims action = Success None -> *)
(*       oraat_interp_action sigma int_fns struct_defs fuel2 r r_acc ext_fn_log is_safe gamma action = (true, Some res) -> *)
(*       False. *)
(*     Proof. *)
(*       induction fuel1; [discriminate | ]. *)
(*       intros *. destruct fuel2; [ discriminate | ]. *)
(*       intros Hanalyze Horaat. *)
(*       destruct action; cbn in *; simplify; unfold res_opt_bind, opt_bind_to_res in *; unfold __debug__ in *; *)
(*         destruct_all_matches; *)
(*         repeat match goal with *)
(*         | H: analyze_action _ _ _ _ _ _ _ _ ?action = Success None, *)
(*           H1: oraat_interp_action _ _ _ _ _ _ _ _ _ ?action = (true, Some _) |- _ => *)
(*             apply IHfuel1 with (1 := H) in H1 *)
(*         | H: oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ => *)
(*             match b with *)
(*             | true => fail *)
(*             | _ => let H' := fresh in *)
(*                   assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto); *)
(*                   rewrite H' in H; subst *)
(*             end *)
(*         | H: _ && _ = true |- _ => rewrite andb_true_iff in H *)
(*         | |- _ => progress (simpl in *; simplify; propositional) *)
(*         end. *)
(*     Qed. *)

(*     Definition reg_sim_state_prop (sims: SortedRegEnv.EnvT bool) (st1 st2: state_t) : Prop := *)
(*       forall reg, SortedRegEnv.opt_get sims reg = Some true -> *)
(*              st1.[reg] = st2.[reg]. *)

(*     Definition box_sim_state_prop (sims: list box_t) (st1 st2: state_t) : Prop := *)
(*       Forall (fun b => match find (fun '(b2, _) => beq_dec b b2) box_defs with *)
(*                     | Some (_, def) => box_sim def st1 st2 *)
(*                     | None => False *)
(*                     end) sims. *)

(*     Definition action_writes_regs_only (int_fns: int_fn_env_t) (action: action) (regs: list reg_t) : Prop := *)
(*         exists fuel, match taint_action int_fns fuel taint_empty action with *)
(*                 | Success (Some taint_env) => *)
(*                     forall reg taint, *)
(*                     not (In reg regs) -> *)
(*                     SortedRegEnv.opt_get taint_env reg = Some taint -> *)
(*                     taint.(taint_write0) = false /\ *)
(*                     taint.(taint_write1) = false *)
(*                 | _ => False *)
(*                 end. *)

(*   Definition compute_action_writes_regs_only (int_fns: int_fn_env_t) (a: action) (regs: list reg_t) := *)
(*     match taint_action int_fns (safe_fuel int_fns a) taint_empty a with *)
(*     | Success (Some taint_env) => *)
(*         forallb (fun '(r, taint) => *)
(*                    existsb (beq_dec r) regs || *)
(*                    (negb (taint_write0 taint || taint_write1 taint)) *)
(*                 ) (SortedRegEnv.to_list taint_env) *)
(*     | _ => false *)
(*     end. *)

(*   Lemma compute_action_writes_regs_only_correct: *)
(*     forall a int_fns regs, *)
(*     compute_action_writes_regs_only int_fns a regs = true -> *)
(*     action_writes_regs_only int_fns a regs. *)
(*   Proof. *)
(*     consider compute_action_writes_regs_only. *)
(*     consider action_writes_regs_only. *)
(*     intros * Hcompute. *)
(*     exists (safe_fuel int_fns0 a). *)
(*     bash_destruct Hcompute. *)
(*     intros * Hregs Htaint. *)
(*     unfold not in *. *)
(*     rewrite forallb_forall in Hcompute. *)
(*     rewrite SortedRegEnv.opt_get_find in Htaint. *)
(*     simplify. apply find_some in Heqo. propositional; simplify. *)
(*     specialize (Hcompute _ Heqo0). simpl in Hcompute. *)
(*     rewrite orb_true_iff in *. rewrite negb_true_iff in Hcompute. rewrite orb_false_iff in Hcompute. *)
(*     destruct Hcompute; auto. *)
(*     rewrite existsb_exists in H. propositional; simplify. contradiction. *)
(*   Qed. *)

(*     Definition function_preserves_box_sim *)
(*       (int_fns: @int_fn_env_t N (@action N)) (struct_defs: @struct_env_t N) *)
(*       (* (valid_regs: list (reg_t * list bool)) (regs: list reg_t)  *) *)
(*       (box: box_def) (fn_spec: @int_fn_spec_t N (@action N)) *)
(*       (sigmas : list ext_fn_t):= *)
(*       forall arg sigma1 sigma2 fuel1 fuel2  r1 r2 r_acc1 r_acc2 gamma1' gamma2' st1' st2' v1 v2 ext_fn_log1 ext_fn_log1' ext_fn_log2 ext_fn_log2', *)
(*       Forall (fun fn => forall v, sigma1 fn v = sigma2 fn v) sigmas -> *)
(*       oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 r_acc1 ext_fn_log1 true *)
(*         (fn_gamma (fn_arg_name fn_spec) arg) *)
(*         (fn_body fn_spec) = (true, Some (gamma1', st1', ext_fn_log1', v1)) -> *)
(*       oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 r_acc2 ext_fn_log2 true *)
(*         (fn_gamma (fn_arg_name fn_spec) arg) (fn_body fn_spec) = (true, Some (gamma2', st2', ext_fn_log2', v2)) -> *)
(*       box_sim box r1 r2 -> *)
(*       box_sim box r_acc1 r_acc2 -> *)
(*       v1 = v2 /\ box_sim box st1' st2'. *)


(*     Definition box_fn_preserves_prop *)
(*       (box_fns: list (fn_name_t * (box_t * list ext_fn_t))) : Prop := *)
(*       Forall (fun '(fn, (box, ext_fns)) => *)
(*                 match lookup_int_fn int_fns fn tt with *)
(*                 | Success (_, fn_spec) => *)
(*                     match find (fun '(b2,_) => beq_dec box b2) box_defs with *)
(*                     | Some (_, def) => function_preserves_box_sim int_fns struct_defs def fn_spec ext_fns /\ *)
(*                                       action_writes_regs_only int_fns fn_spec.(fn_body) (get_box_regs def) *)
(*                     | _ => False *)
(*                     end *)
(*                 | _ => False *)
(*                 end) box_fns. *)
(*     Section Forall3. *)
(*       Context {A B C: Type}. *)
(*       Inductive Forall3 (R: A -> B -> C -> Prop) : list A -> list B -> list C -> Prop := *)
(*         | Forall3_nil : Forall3 R [] [] [] *)
(*         | Forall3_cons: forall (x: A) (y: B) (z: C) (xs: list A) (ys: list B) (zs: list C), *)
(*                         R x y z  -> Forall3 R xs ys zs -> Forall3 R (x::xs) (y:: ys) (z:: zs). *)
(*     End Forall3. *)

(*     Definition gamma_sim_correct (gamma1 gamma2: gamma_t) (sim: sim_gamma_t) : Prop := *)
(*       Forall3 (fun '(var1,v1) '(var2, v2) '(var3, b) => *)
(*                  var1 = var2 /\ var2 = var3 /\ (b = true -> v1 = v2)) gamma1 gamma2 sim. *)

(*     Lemma gamma_sim_correct_empty : gamma_sim_correct [] [] [] . *)
(*     Proof. *)
(*       constructor. *)
(*     Qed. *)

(* Lemma gamma_sim_correct_lookup: *)
(*   forall gamma1 gamma2 gamma_sim var, *)
(*     gamma_sim_correct gamma1 gamma2 gamma_sim -> *)
(*     varenv_lookup_var gamma_sim var tt = Success true -> *)
(*     varenv_lookup_var gamma1 var tt = varenv_lookup_var gamma2 var tt. *)
(* Proof. *)
(*   unfold gamma_sim_correct, varenv_lookup_var. *)
(*   induction gamma1; intros gamma2 gamma_sim var Hsim Hlookup. *)
(*   - destruct gamma2; [ | inversions Hsim]. destruct gamma_sim; [ | inversions Hsim]. *)
(*     simpl in *. discriminate. *)
(*   - destruct gamma2; [ inversions Hsim | ]. *)
(*     destruct gamma_sim; [ inversions Hsim | ]. *)
(*     inversions Hsim. destruct_match_pairs; propositional. simpl in *. *)
(*     destruct_match; simplify. *)
(*     + apply String.eqb_eq in Heqb0. propositional. *)
(*     + eapply IHgamma1; eauto. simpl_match. auto. *)
(* Qed. *)
(* Lemma gamma_sim_correct_lookup': *)
(*   forall gamma1 gamma2 gamma_sim var, *)
(*     gamma_sim_correct gamma1 gamma2 gamma_sim -> *)
(*     varenv_lookup_var gamma_sim var tt = Success true -> *)
(*     success_or_default (varenv_lookup_var gamma1 var tt) [] = success_or_default (varenv_lookup_var gamma2 var tt) []. *)
(* Proof. *)
(*   intros. eapply gamma_sim_correct_lookup in H; eauto. rewrite_solve. *)
(* Qed. *)
(* Lemma gamma_sim_correct_varenv_update: *)
(*   forall gamma1 gamma2 sim v1 v2 var b, *)
(*   gamma_sim_correct gamma1 gamma2 sim -> *)
(*   match b with *)
(*   | true => v1 = v2 *)
(*   | false => True *)
(*   end -> *)
(*   gamma_sim_correct (varenv_update gamma1 var v1) (varenv_update gamma2 var v2) (varenv_update sim var b). *)
(* Proof. *)
(*   unfold gamma_sim_correct, varenv_update. *)
(*   induction gamma1; intros * Hsim Hb. *)
(*   - destruct gamma2; [ | inversions Hsim]. destruct sim; [ | inversions Hsim]. *)
(*     simpl in *. constructor; destruct b; split_ands_in_goal; propositional. discriminate. *)
(*   - destruct gamma2; [ inversions Hsim | ]. *)
(*     destruct sim; [ inversions Hsim | ]. simpl. *)
(*     inversions Hsim. *)
(*     destruct_match_pairs. propositional. *)
(*     destruct_match. *)
(*     + apply String.eqb_eq in Heqb1. subst. constructor; auto. split_ands_in_goal; propositional. *)
(*     + constructor; auto. *)
(* Qed. *)
(* Lemma gamma_sim_correct_merge_l: *)
(*   forall gamma1 gamma2 new_gamma sim sim', *)
(*   gamma_sim_correct gamma1 gamma2 sim -> *)
(*   merge_sim_gamma new_gamma sim  = Success sim' -> *)
(*   gamma_sim_correct gamma1 gamma2 sim'. *)
(* Proof. *)
(*   unfold gamma_sim_correct, merge_sim_gamma. *)
(*   induction gamma1; intros * Hsim Hmerge. *)
(*   - destruct gamma2; [ | inversions Hsim]. destruct sim; [ | inversions Hsim]. *)
(*     destruct new_gamma; [ | discriminate ]. *)
(*     simplify. simpl in Heqr. simplify. simpl in *. simplify. constructor. *)
(*   - destruct gamma2; [ inversions Hsim | ]. *)
(*     destruct sim; [ inversions Hsim | ]. simpl. *)
(*     simplify. destruct new_gamma; [discriminate | ]. simpl in *. simplify. simpl in *. *)
(*     inversions Hsim. destruct_match_pairs. propositional. simpl in *. simplify. *)
(*     apply String.eqb_eq in Heqb1. subst. *)
(*     constructor; auto. *)
(*     + split_ands_in_goal; propositional. rewrite andb_true_iff in H; propositional. *)
(*     + eapply IHgamma1 with (new_gamma := new_gamma); eauto. simpl_match; auto. *)
(* Qed. *)

(* Lemma gamma_sim_correct_merge_r: *)
(*   forall gamma1 gamma2 new_gamma sim sim', *)
(*   gamma_sim_correct gamma1 gamma2 sim -> *)
(*   merge_sim_gamma sim new_gamma = Success sim' -> *)
(*   gamma_sim_correct gamma1 gamma2 sim'. *)
(* Proof. *)
(*   unfold gamma_sim_correct, merge_sim_gamma. *)
(*   induction gamma1; intros * Hsim Hmerge. *)
(*   - destruct gamma2; [ | inversions Hsim]. destruct sim; [ | inversions Hsim]. *)
(*     destruct new_gamma; [ | discriminate ]. *)
(*     simplify. simpl in Heqr. simplify. simpl in *. simplify. constructor. *)
(*   - destruct gamma2; [ inversions Hsim | ]. *)
(*     destruct sim; [ inversions Hsim | ]. simpl. *)
(*     simplify. destruct new_gamma; [discriminate | ]. simpl in *. simplify. simpl in *. *)
(*     inversions Hsim. destruct_match_pairs. propositional. simpl in *. simplify. *)
(*     apply String.eqb_eq in Heqb1. subst. *)
(*     constructor; auto. *)
(*     + split_ands_in_goal; propositional. rewrite andb_true_iff in H; propositional. *)
(*     + eapply IHgamma1 with (new_gamma := new_gamma); eauto. simpl_match; auto. *)
(* Qed. *)
(* Lemma reg_sim_state_prop_merge_r: *)
(*   forall sim sim' st1 st2, *)
(*   reg_sim_state_prop sim st1 st2 -> *)
(*   reg_sim_state_prop (merge_sim_regs sim sim') st1 st2. *)
(* Proof. *)
(*   unfold reg_sim_state_prop, merge_sim_regs. *)
(*   intros * Hsim reg Hget. *)
(*   rewrite SortedRegEnv.opt_get_mapV in Hget. *)
(*   rewrite SortedRegEnv.opt_get_zip_default in Hget. *)
(*   specialize (Hsim reg). bash_destruct Hget; simplify. *)
(*   rewrite andb_true_iff in Hget. propositional. *)
(* Qed. *)

(* Lemma reg_sim_state_prop_merge_l: *)
(*   forall sim sim' st1 st2, *)
(*   reg_sim_state_prop sim st1 st2 -> *)
(*   reg_sim_state_prop (merge_sim_regs sim' sim ) st1 st2. *)
(* Proof. *)
(*   unfold reg_sim_state_prop, merge_sim_regs. *)
(*   intros * Hsim reg Hget. *)
(*   rewrite SortedRegEnv.opt_get_mapV in Hget. *)
(*   rewrite SortedRegEnv.opt_get_zip_default in Hget. *)
(*   specialize (Hsim reg). bash_destruct Hget; simplify. *)
(*   rewrite andb_true_iff in Hget. propositional. *)
(* Qed. *)

(* Lemma ext_fn_eq: *)
(*   forall (sigma1 sigma2: ext_sigma_t) ext_fn_sims fn, *)
(*   Forall (fun f : ext_fn_t => forall v, sigma1 f v = sigma2 f v) ext_fn_sims -> *)
(*   existsb (beq_dec fn) ext_fn_sims = true -> *)
(*   sigma1 fn = sigma2 fn. *)
(* Proof. *)
(*   intros. apply existsb_exists in H0. propositional; simplify. *)
(*   rewrite Forall_forall in H. *)
(*   apply functional_extensionality. auto. *)
(* Qed. *)

(* Lemma ext_fn_eq': *)
(*   forall (sigma1 sigma2: ext_sigma_t) ext_fn_sims fn v, *)
(*   Forall (fun f : ext_fn_t => forall v, sigma1 f v = sigma2 f v) ext_fn_sims -> *)
(*   existsb (beq_dec fn) ext_fn_sims = true -> *)
(*   success_or_default (sigma1 fn v) [] = success_or_default (sigma2 fn v) []. *)
(* Proof. *)
(*   intros. apply ext_fn_eq with (2 := H0) in H. rewrite_solve. *)
(* Qed. *)

(* Lemma gamma_sim_correct_tl: *)
(*   forall gamma1 gamma2 sim, *)
(*   gamma_sim_correct gamma1 gamma2 sim -> *)
(*   gamma_sim_correct (tl gamma1) (tl gamma2) (tl sim). *)
(* Proof. *)
(*   unfold gamma_sim_correct. intros. inversions H; simpl; auto. constructor. *)
(* Qed. *)
(* Lemma gamma_sim_correct_bind: *)
(*   forall gamma1 gamma2 sim var v0 v1 b, *)
(*   gamma_sim_correct gamma1 gamma2 sim -> *)
(*   match b with *)
(*   | true => v0 = v1 *)
(*   | false => True *)
(*   end -> *)
(*   gamma_sim_correct (varenv_bind gamma1 var v0) (varenv_bind gamma2 var v1) (varenv_bind sim var b). *)
(* Proof. *)
(*   unfold gamma_sim_correct. intros. *)
(*   constructor; auto. split_ands_in_goal; propositional. *)
(* Qed. *)
(* Lemma reg_sim_state_prop_update: *)
(*   forall sim st1 st2 idx b v0 v1, *)
(*   reg_sim_state_prop sim st1 st2 -> *)
(*   match b with *)
(*   | true => v0 = v1 *)
(*   | false => True *)
(*   end -> *)
(*   reg_sim_state_prop (update_sim_reg' sim idx b) (state_set st1 idx v0) (state_set st2 idx v1). *)
(* Proof. *)
(*   unfold reg_sim_state_prop, update_sim_reg'. *)
(*   intros * Hsim Hb reg Hget. *)
(*   specialize (Hsim reg). *)
(*   destruct_with_eqn (beq_dec reg idx); simplify. *)
(*   - rewrite SortedRegEnv.update_correct_eq in *. *)
(*     repeat rewrite unsafe_get_reg_state_set_eq. destruct_all_matches. *)
(*   - rewrite SortedRegEnv.update_correct_neq in * by auto. *)
(*     repeat rewrite unsafe_get_reg_state_set_neq by auto. destruct_all_matches. *)
(* Qed. *)


(* Lemma box_sim_state_update_l: *)
(*   forall box st1 st2 idx v, *)
(*   box_sim box st1 st2 -> *)
(*   forallb (fun a : N => negb (beq_dec idx a)) (get_box_regs box) = true -> *)
(*   box_sim box (state_set st1 idx v) st2. *)
(* Proof. *)
(*   intros * Hsim Hreg. destruct Hsim. *)
(*   rewrite forallb_forall in Hreg. *)
(*   constructor. *)
(*   - intros r Hin. specialize (pf_box_valid_sim0 _ Hin). *)
(*     rewrite unsafe_get_reg_state_set_neq; auto. *)
(*     consider get_box_regs. specialize (Hreg r). *)
(*     assert_pre_and_specialize Hreg. *)
(*     { apply in_or_app. auto. } *)
(*     rewrite negb_true_iff in Hreg. simplify. auto. *)
(*   - consider box_data_sim. intros. *)
(*     assert (idx <> reg). *)
(*     { apply existsb_exists in H0. propositional; simplify. consider get_box_regs. *)
(*       specialize (Hreg x). *)
(*       assert_pre_and_specialize Hreg;[ apply in_or_app; auto | ]. *)
(*       rewrite negb_true_iff in Hreg. simplify; auto. *)
(*     } *)
(*     rewrite unsafe_get_reg_state_set_neq by auto. *)
(*     apply pf_box_data_sim0; auto. apply Forall_forall. *)
(*     rewrite Forall_forall in H. intros. specialize (H _ H2). destruct_match_pairs; simplify. *)
(*     rewrite unsafe_get_reg_state_set_neq; auto. consider get_box_regs. *)
(*     specialize (Hreg r). *)
(*     assert_pre_and_specialize Hreg. *)
(*     { apply in_or_app. left. apply in_map with (f := fst) in H2. auto. } *)
(*     { rewrite negb_true_iff in *. simplify; auto. } *)
(* Qed. *)

(* Lemma box_sim_sym: *)
(*   forall box st1 st2, *)
(*   box_sim box st1 st2 -> box_sim box st2 st1. *)
(* Proof. *)
(*   intros * Hsim. destruct Hsim. *)
(*   constructor. *)
(*   - intros; symmetry; auto. *)
(*   - consider box_data_sim. intros. symmetry. apply pf_box_data_sim0; auto. *)
(*     apply Forall_forall. rewrite Forall_forall in H. *)
(*     intros. specialize (H _ H1). destruct_match_pairs; simplify. *)
(*     apply pf_box_valid_sim0. *)
(*     eapply in_map with (f := fst) in H1; eauto. *)
(* Qed. *)
(* Lemma box_sim_state_update_r: *)
(*   forall box st1 st2 idx v, *)
(*   box_sim box st1 st2 -> *)
(*   forallb (fun a : N => negb (beq_dec idx a)) (get_box_regs box) = true -> *)
(*   box_sim box st1 (state_set st2 idx v). *)
(* Proof. *)
(*   intros. apply box_sim_sym. *)
(*   apply box_sim_state_update_l; auto. *)
(*   apply box_sim_sym. auto. *)
(* Qed. *)
(* Notation reg_in_box_defs := (@reg_in_box_defs box_t). *)
(* Notation reg_box_defs := (reg_box_defs box_defs). *)
(* Lemma box_sim_state_prop_state_set: *)
(*   forall box_sim st1 st2 idx v0 v1, *)
(*   box_sim_state_prop box_sim st1 st2 -> *)
(*   reg_in_box_defs reg_box_defs idx = false -> *)
(*   box_sim_state_prop box_sim (state_set st1 idx v0) (state_set st2 idx v1). *)
(* Proof. *)
(*   unfold box_sim_state_prop, reg_in_box_defs, reg_box_defs. *)
(*   intros * Hsim Hreg. *)
(*   rewrite map_map in Hreg. *)
(*   apply Forall_forall. *)
(*   rewrite Forall_forall in Hsim. intros box HIn. specialize Hsim with (1 := HIn). *)
(*   destruct_match; auto. destruct_match_pairs; subst. *)
(*   apply existsb_false_forall in Hreg. *)
(*   rewrite forallb_forall in Hreg. *)
(*   apply find_some in Heqo; propositional. rewrite beq_dec_iff in Heqo1. subst. *)
(*   specialize (Hreg ((fun x0 => snd (let '(box,def) := x0 in (box, get_box_regs def))) (b,b0))). *)
(*   specialize Hreg with (1 := in_map _ _ _ Heqo0). *)
(*   rewrite negb_true_iff in Hreg. simpl in Hreg. *)
(*   apply existsb_false_forall in Hreg. *)
(*   apply box_sim_state_update_l; auto. *)
(*   apply box_sim_state_update_r; auto. *)
(* Qed. *)
(* Lemma gamma_sim_correct_fn_gamma : *)
(*   forall var v0 v1 b, *)
(*   match b with *)
(*   | true => v0 = v1 *)
(*   | false => True *)
(*   end -> *)
(*   gamma_sim_correct (fn_gamma var v0) (fn_gamma var v1) [(var,b)]. *)
(* Proof. *)
(*   unfold gamma_sim_correct, fn_gamma. *)
(*   intros; constructor; [ | constructor]; split_ands_in_goal; propositional. *)
(* Qed. *)


(* Hint Immediate gamma_sim_correct_lookup' : solve_box_sim. *)
(* Hint Immediate gamma_sim_correct_varenv_update : solve_box_sim. *)
(* Hint Immediate gamma_sim_correct_merge_r : solve_box_sim. *)
(* Hint Immediate gamma_sim_correct_merge_l : solve_box_sim. *)
(* Hint Immediate reg_sim_state_prop_merge_r: solve_box_sim. *)
(* Hint Immediate reg_sim_state_prop_merge_l: solve_box_sim. *)
(* Hint Immediate ext_fn_eq': solve_box_sim. *)
(* Hint Immediate gamma_sim_correct_tl: solve_box_sim. *)
(* Hint Immediate gamma_sim_correct_bind: solve_box_sim. *)
(* Hint Immediate gamma_sim_correct_bind: solve_box_sim. *)
(* Hint Immediate reg_sim_state_prop_update: solve_box_sim. *)
(* Hint Immediate box_sim_state_prop_state_set: solve_box_sim. *)
(* Hint Immediate gamma_sim_correct_fn_gamma : solve_box_sim. *)

(* Lemma function_writes_regs_only_def: *)
(*   forall box_fns box n n0 exts fn fn_spec, *)
(*   box_fn_preserves_prop box_fns -> *)
(*   find (fun '(f, _) => beq_dec fn f) box_fns = Some (n, (box, exts)) -> *)
(*   lookup_int_fn int_fns fn tt = Success (n0, fn_spec) -> *)
(*   exists def, In (box,def) box_defs /\ *)
(*          function_preserves_box_sim int_fns struct_defs def fn_spec exts /\ *)
(*          action_writes_regs_only int_fns (fn_body fn_spec) (get_box_regs def). *)
(* Proof. *)
(*   intros * Hpreserves Hboxes Hlookup. *)
(*   apply find_some in Hboxes. propositional; simplify. *)
(*   consider box_fn_preserves_prop. rewrite Forall_forall in Hpreserves. *)
(*   specialize Hpreserves with (1 := Hboxes0). simplify. *)
(*   propositional. apply find_some in Heqo. rewrite beq_dec_iff in Heqo. propositional. *)
(*   eauto. *)
(* Qed. *)
(* Lemma function_preserves_reg_sim_state_prop': *)
(*   forall reg_sims r_acc1 r_acc2 st1' st2' box_defs box def *)
(*     sigma1 sigma2 int_fns struct_defs fuel1 fuel2 r1 r2 is_safe1 is_safe2 gamma1 gamma2 action gamma1' gamma2' v1' v2' ext_fn_log1 ext_fn_log1' ext_fn_log2 ext_fn_log2', *)
(*   reg_sim_state_prop reg_sims r_acc1 r_acc2 -> *)
(*   oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 r_acc1 ext_fn_log1 is_safe1 gamma1 action = *)
(*     (true, Some (gamma1', st1', ext_fn_log1', v1')) -> *)
(*   oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 r_acc2 ext_fn_log2 is_safe2 gamma2 action = (true, Some (gamma2', st2', ext_fn_log2', v2')) -> *)
(*   WF_boxes box_defs -> *)
(*   In (box,def) box_defs -> *)
(*   action_writes_regs_only int_fns (action) (get_box_regs def) -> *)
(*   RegsNotInBoxes reg_sims (map (fun '(box, def) => (box, get_box_regs def)) box_defs) -> *)
(*   reg_sim_state_prop reg_sims st1' st2'. *)
(* Proof. *)
(*   intros * Hsim Horaat1 Horaat2 Hwf_boxes Hbox Hupdate Hsim'. *)
(*   consider reg_sim_state_prop. *)
(*   intros reg Hget. *)
(*   consider action_writes_regs_only. *)
(*   assert (is_safe1 = true) by (eapply oraat_interp_action_is_safe_generalizes in Horaat1; eauto); subst. *)
(*   assert (is_safe2 = true) by (eapply oraat_interp_action_is_safe_generalizes in Horaat2; eauto); subst. *)
(*   specialize taint_safety_function with (1 := Horaat1) as Htaint1. *)
(*   specialize taint_safety_function with (1 := Horaat2) as Htaint2. *)
(*   propositional; simplify. consider @is_success_some. *)
(*   specialize (Htaint1 fuel). specialize (Htaint2 fuel). consider taint_empty. repeat simpl_match. propositional. *)
(*    unfold RegsNotInBoxes in *. *)
(*   specialize Hsim' with (1 := Hget) (box := box) (def := get_box_regs def). *)
(*   assert_pre_and_specialize Hsim'. *)
(*   { apply in_map with (f := (fun '(box0,def0) => (box0, get_box_regs def0))) in Hbox; auto. } *)
(*   specialize (Hupdate0) with (1 := Hsim'). *)
(*   assert (no_writes_in_taint_set (Success (Some t)) reg  = true) as Hno_write. *)
(*   { unfold no_writes_in_taint_set. destruct_match; auto. specialize Hupdate0 with (1 := eq_refl); propositional. *)
(*     rewrite Hupdate1. rewrite Hupdate2. auto. *)
(*   } *)
(*   erewrite taint_set_to_prop_no_write' with (1 := Htaint1) by auto. *)
(*   erewrite taint_set_to_prop_no_write' with (1 := Htaint2) by auto. *)
(*   apply Hsim. auto. *)
(* Qed. *)

(* Lemma function_preserves_reg_sim_state_prop: *)
(*   forall reg_sims r_acc1 r_acc2 st1' st2' box box_fns fn n exts n0 fn_spec *)
(*     sigma1 sigma2 struct_defs fuel1 fuel2 r1 r2 is_safe1 is_safe2 gamma1 gamma2 gamma1' gamma2' v1' v2' *)
(*     ext_fn_log1 ext_fn_log2 ext_fn_log1' ext_fn_log2', *)
(*   reg_sim_state_prop reg_sims r_acc1 r_acc2 -> *)
(*   oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 r_acc1 ext_fn_log1 is_safe1 gamma1 (fn_body fn_spec) = (true, Some (gamma1', st1', ext_fn_log1', v1')) -> *)
(*   oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 r_acc2 ext_fn_log2 is_safe2 gamma2 (fn_body fn_spec) = (true, Some (gamma2', st2', ext_fn_log2', v2')) -> *)
(*   WF_boxes box_defs -> *)
(*   box_fn_preserves_prop box_fns -> *)
(*   find (fun '(f, _) => beq_dec fn f) box_fns = Some (n, (box, exts)) -> *)
(*   lookup_int_fn int_fns fn tt = Success (n0, fn_spec) -> *)
(*   (* In (box,def) box_defs -> *) *)
(*   (* action_writes_regs_only int_fns (action) (get_box_regs def) -> *) *)
(*   RegsNotInBoxes reg_sims (map (fun '(box, def) => (box, get_box_regs def)) box_defs) -> *)
(*   reg_sim_state_prop reg_sims st1' st2'. *)
(* Proof. *)
(*   intros * Hsim Horaat1 Horaat2 Hwf_boxes Hbox Hfns Hlookup Hupdate Hsim'. *)
(*   eapply function_writes_regs_only_def in Hlookup; eauto. propositional. *)
(*   eapply function_preserves_reg_sim_state_prop'; eauto. *)
(* Qed. *)
(* Hint Immediate function_preserves_reg_sim_state_prop: solve_box_sim. *)
(* Lemma box_sim_state_prop_le_preserved: *)
(*   forall sim1 sim2 r1 r2, *)
(*   box_sim_state_prop sim2 r1 r2 -> *)
(*   box_sim_le sim1 sim2 -> *)
(*   box_sim_state_prop sim1 r1 r2. *)
(* Proof. *)
(*   consider box_sim_state_prop. consider box_sim_le. *)
(*   intros * Hsim Hle. *)
(*   apply Forall_forall. rewrite Forall_forall in Hsim. *)
(*   intros * Hin. apply Hle in Hin. apply Hsim. auto. *)
(* Qed. *)
(* Hint Immediate box_sim_state_prop_le_preserved: solve_box_sim. *)
(* Hint Immediate box_sim_le_trans: solve_box_sim. *)
(* Lemma box_sim_state_prop_merge_sim_boxes_l: *)
(*   forall sim1 sim2 st1 st2, *)
(*   box_sim_state_prop sim1 st1 st2 -> *)
(*   box_sim_state_prop (merge_sim_boxes sim1 sim2) st1 st2. *)
(* Proof. *)
(*   consider box_sim_state_prop. consider @merge_sim_boxes. *)
(*   intros * Hsim. *)
(*   rewrite Forall_forall in Hsim. *)
(*   apply Forall_forall. *)
(*   intros * HIn. apply filter_In in HIn. propositional. *)
(*   eapply Hsim; eauto. *)
(* Qed. *)

(* Lemma box_sim_state_prop_merge_sim_boxes_r: *)
(*   forall sim1 sim2 st1 st2, *)
(*   box_sim_state_prop sim2 st1 st2 -> *)
(*   box_sim_state_prop (merge_sim_boxes sim1 sim2) st1 st2. *)
(* Proof. *)
(*   consider box_sim_state_prop. consider @merge_sim_boxes. *)
(*   intros * Hsim. *)
(*   rewrite Forall_forall in Hsim. *)
(*   apply Forall_forall. *)
(*   intros * HIn. apply filter_In in HIn. propositional. *)
(*   eapply Hsim; eauto. *)
(*   apply existsb_exists in HIn1. propositional. *)
(*   rewrite beq_dec_iff in HIn3. subst. auto. *)
(* Qed. *)

(* Hint Immediate box_sim_state_prop_merge_sim_boxes_r: solve_box_sim. *)
(* Hint Immediate box_sim_state_prop_merge_sim_boxes_l: solve_box_sim. *)
(* Lemma box_sim_le_merge_sim_boxes_l: *)
(*   forall sim1 sim2 sim3, *)
(*   box_sim_le sim1 sim3 -> *)
(*   box_sim_le (merge_sim_boxes sim1 sim2) sim3. *)
(* Proof. *)
(*   consider box_sim_le. consider @merge_sim_boxes. *)
(*   intros * Hsim * HIn. *)
(*   apply filter_In in HIn. propositional. *)
(* Qed. *)

(* Lemma box_sim_le_merge_sim_boxes_r: *)
(*   forall sim1 sim2 sim3, *)
(*   box_sim_le sim2 sim3 -> *)
(*   box_sim_le (merge_sim_boxes sim1 sim2) sim3. *)
(* Proof. *)
(*   consider box_sim_le. consider @merge_sim_boxes. *)
(*   intros * Hsim * HIn. *)
(*   apply filter_In in HIn. propositional. *)
(*   apply existsb_exists in HIn1. propositional. rewrite beq_dec_iff in HIn3. propositional. *)
(* Qed. *)

(* Hint Immediate box_sim_le_merge_sim_boxes_l: solve_box_sim. *)
(* Hint Immediate box_sim_le_merge_sim_boxes_r: solve_box_sim. *)
(* Lemma sim_state_le_implies_reg_sim_le: *)
(*   forall sim1 sim2, *)
(*   sim_state_le sim1 sim2 -> *)
(*   reg_sim_le (sim_regs sim1) (sim_regs sim2). *)
(* Proof. *)
(*   intros. destruct H. auto. *)
(* Qed. *)
(* Lemma sim_state_le_implies_box_sim_le: *)
(*   forall sim1 sim2, *)
(*   sim_state_le sim1 sim2 -> *)
(*   box_sim_le (sim_boxes sim1) (sim_boxes sim2). *)
(* Proof. *)
(*   intros. destruct H. auto. *)
(* Qed. *)

(* Hint Immediate sim_state_le_implies_reg_sim_le : solve_box_sim. *)
(* Hint Immediate box_sim_le_merge_sim_boxes_r: solve_box_sim. *)
(* Hint Immediate reg_sim_le_trans : solve_box_sim. *)
(* Lemma gamma_sim_correct_implies_var_eq2: *)
(* forall sim g1 g2 , *)
(*   gamma_sim_correct g1 g2 sim -> *)
(*   gamma_vars_eq g2 sim. *)
(* Proof. *)
(*   consider gamma_sim_correct. consider @gamma_vars_eq. *)
(*   induction sim; intros * Hsim. *)
(*   - inversions Hsim; constructor. *)
(*   - inversions Hsim. destruct_match_pairs; propositional. *)
(*     constructor; eauto. *)
(* Qed. *)
(* Hint Immediate gamma_sim_correct_implies_var_eq2: solve_box_sim. *)
(* Lemma gamma_sim_correct_implies_var_eq1: *)
(* forall sim g1 g2 , *)
(*   gamma_sim_correct g1 g2 sim -> *)
(*   gamma_vars_eq g1 sim. *)
(* Proof. *)
(*   consider gamma_sim_correct. consider @gamma_vars_eq. *)
(*   induction sim; intros * Hsim. *)
(*   - inversions Hsim; constructor. *)
(*   - inversions Hsim. destruct_match_pairs; propositional. *)
(*     constructor; eauto. *)
(* Qed. *)
(* Hint Immediate gamma_sim_correct_implies_var_eq1: solve_box_sim. *)
(* Lemma gamma_sim_correct_trans: *)
(*   forall gamma1 gamma2 gamma1' gamma2' gamma_sims', *)
(*   gamma_sim_correct gamma1 gamma1' gamma_sims' -> *)
(*   gamma_sim_correct gamma2 gamma2' gamma_sims' -> *)
(*   gamma_sim_correct gamma1 gamma2 gamma_sims' -> *)
(*   gamma_sim_correct gamma1' gamma2' gamma_sims'. *)
(* Proof. *)
(*   consider gamma_sim_correct. induction gamma1; intros * Hsim0 Hsim1 Hsim. *)
(*   - inversions Hsim0. inversions Hsim1. auto. *)
(*   - inversions Hsim0. inversions Hsim1. inversions Hsim. *)
(*     destruct_match_pairs; propositional. *)
(*     constructor; eauto. split_ands_in_goal; propositional. *)
(* Qed. *)

(* Hint Immediate gamma_sim_correct_trans: solve_box_sim. *)
(* Lemma gamma_sim_correct_le: *)
(*   forall gamma1 gamma2 sim sim', *)
(*   gamma_state_le sim' sim -> *)
(*   gamma_sim_correct gamma1 gamma2 sim -> *)
(*   gamma_sim_correct gamma1 gamma2 sim'. *)
(* Proof. *)
(*   consider gamma_sim_correct. consider gamma_state_le. *)
(*   induction gamma1; intros * Hle Hsim. *)
(*   - inversions Hsim. inversions Hle. constructor. *)
(*   - inversions Hsim. inversions Hle. destruct_match_pairs; propositional. *)
(*     constructor; eauto. *)
(* Qed. *)
(* Hint Immediate gamma_sim_correct_le: solve_box_sim. *)
(* Lemma reg_sim_le_state_prop: *)
(*   forall sim1 sim2 st1 st2, *)
(*   reg_sim_le sim2 sim1 -> *)
(*   reg_sim_state_prop sim1 st1 st2 -> *)
(*   reg_sim_state_prop sim2 st1 st2. *)
(* Proof. *)
(*   consider reg_sim_le. consider reg_sim_state_prop. *)
(*   intros * Hle Hsim. *)
(*   intros. apply Hle in H. eauto. *)
(* Qed. *)
(* Hint Immediate reg_sim_le_state_prop : solve_box_sim. *)
(* Lemma reg_sim_state_prop_trans: *)
(*   forall sim sim1 sim2 sim1' sim2', *)
(*     reg_sim_state_prop sim sim1 sim2 -> *)
(*     reg_sim_state_prop sim sim1 sim1' -> *)
(*     reg_sim_state_prop sim sim2 sim2'-> *)
(*     reg_sim_state_prop sim sim1' sim2'. *)
(* Proof. *)
(*   consider reg_sim_state_prop. intros * Hsim0 Hsim1 Hsim2. *)
(*   intros * Hreg0. *)
(*   rewrite<-Hsim1 by auto. rewrite<-Hsim2 by auto. eauto. *)
(* Qed. *)
(* Hint Immediate reg_sim_state_prop_trans: solve_box_sim. *)
(* Lemma box_sim_le_state_prop: *)
(*   forall sim1 sim2 st1 st2, *)
(*   box_sim_le sim2 sim1 -> *)
(*   box_sim_state_prop sim1 st1 st2 -> *)
(*   box_sim_state_prop sim2 st1 st2. *)
(* Proof. *)
(*   consider box_sim_le. consider box_sim_state_prop. *)
(*   intros * Hle Hsim. *)
(*   rewrite Forall_forall in Hsim. rewrite Forall_forall. intros. apply Hle in H. *)
(*   eapply Hsim. auto. *)
(* Qed. *)
(* Hint Immediate box_sim_le_state_prop : solve_box_sim. *)
(* Lemma box_sim_trans: *)
(*   forall b st1 st2 st3, *)
(*   box_sim b st1 st2 -> *)
(*   box_sim b st2 st3 -> *)
(*   box_sim b st1 st3. *)
(* Proof. *)
(*   intros. inversions H. inversions H0. constructor. *)
(*   - intros. rewrite pf_box_valid_sim0 by auto. auto. *)
(*   - consider box_data_sim. intros. *)
(*     rewrite pf_box_data_sim0 by auto. *)
(*     apply pf_box_data_sim1; auto. *)
(*     rewrite Forall_forall. *)
(*     rewrite Forall_forall in H. intros. destruct_match_pairs. subst. specialize H with (1 := H1). destruct_match_pairs. simplify. *)
(*     symmetry. apply pf_box_valid_sim0. eapply in_map with (f := fst) in H1; eauto. *)
(* Qed. *)

(* Lemma box_sim_state_prop_trans: *)
(*   forall sim st1 st2 st1' st2', *)
(*   box_sim_state_prop sim st1 st2 -> *)
(*   box_sim_state_prop sim st1 st1' -> *)
(*   box_sim_state_prop sim st2 st2' -> *)
(*   box_sim_state_prop sim st1' st2'. *)
(* Proof. *)
(*   consider box_sim_state_prop. intros * Hsim0 Hsim1 Hsim2. *)
(*   rewrite Forall_forall in *. *)
(*   intros. specialize (Hsim0 _ H). specialize (Hsim1 _ H). specialize (Hsim2 _ H). *)
(*   simplify. *)
(*   eapply box_sim_trans; eauto. *)
(*   apply box_sim_sym. *)
(*   eapply box_sim_trans with (2 := Hsim1). *)
(*   apply box_sim_sym. assumption. *)
(* Qed. *)
(* Hint Immediate box_sim_state_prop_trans: solve_box_sim. *)

(* Lemma box_sim_le_remove_box: *)
(*   forall sim box , *)
(*   box_sim_le (filter (fun box2 : box_t => negb (beq_dec box box2)) sim) sim. *)
(* Proof. *)
(*   consider box_sim_le. induction sim; intros; [ inversions H| ]. *)
(*   simpl in *. destruct_all_matches. *)
(*   - inversions H; eauto. *)
(*   - rewrite negb_false_iff in Heqb. rewrite beq_dec_iff in Heqb. subst. *)
(*     eauto. *)
(* Qed. *)
(* Hint Immediate box_sim_le_remove_box : solve_box_sim. *)
(* Lemma function_preserves_box_sim_state_prop: *)
(*   forall box box_fns fn n exts n0 fn_spec, *)
(*   box_fn_preserves_prop box_fns -> *)
(*   find (fun '(f, _) => beq_dec fn f) box_fns = Some (n, (box, exts)) -> *)
(*   lookup_int_fn int_fns fn tt = Success (n0, fn_spec) -> *)
(*   exists def, In (box,def) box_defs /\ *)
(*            function_preserves_box_sim int_fns struct_defs def fn_spec exts /\ *)
(*            action_writes_regs_only int_fns (fn_body fn_spec) (get_box_regs def). *)
(* Proof. *)
(*   intros * Hfn_preserves Hfind Hlookup. *)
(*   consider box_fn_preserves_prop. rewrite Forall_forall in Hfn_preserves. *)
(*   apply find_some in Hfind. propositional. simplify. *)
(*   specialize Hfn_preserves with (1 := Hfind0). destruct_match_pairs; simplify; propositional. *)
(*   apply find_some in Heqo. propositional. rewrite beq_dec_iff in *. subst. *)
(*   eauto. *)
(* Qed. *)
(* Lemma function_action_writes_regs_only: *)
(*   forall box_sims r_acc1 r_acc2 st1' st2' box box_fns fn n exts n0 fn_spec *)
(*     sigma1 sigma2 fuel1 fuel2 r1 r2 is_safe1 is_safe2 gamma_var1 gamma_var2 gamma1' gamma2' v1' v2' *)
(*     ext_fn_log1 ext_fn_log2 ext_fn_log1' ext_fn_log2', *)
(*   box_sim_state_prop box_sims r1 r2 -> *)
(*   box_sim_state_prop box_sims r_acc1 r_acc2 -> *)
(*   oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 r_acc1 ext_fn_log1 is_safe1 (fn_gamma (fn_arg_name fn_spec) gamma_var1) (fn_body fn_spec) = (true, Some (gamma1', st1', ext_fn_log1', v1')) -> *)
(*   oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 r_acc2 ext_fn_log2 is_safe2 (fn_gamma (fn_arg_name fn_spec) gamma_var2) (fn_body fn_spec) = (true, Some (gamma2', st2', ext_fn_log2', v2')) -> *)
(*   WF_boxes box_defs -> *)
(*   box_fn_preserves_prop box_fns -> *)
(*   find (fun '(f, _) => beq_dec fn f) box_fns = Some (n, (box, exts)) -> *)
(*   lookup_int_fn int_fns fn tt = Success (n0, fn_spec) -> *)
(*   exists def, In (box,def) box_defs /\ *)
(*            function_preserves_box_sim int_fns struct_defs def fn_spec exts /\ *)
(*            action_writes_regs_only int_fns (fn_body fn_spec) (get_box_regs def). *)
(* Proof. *)
(*   intros * Hsim0 Hsim1 Horaat1 Horaat2 Hwf_boxes Hfn_preserves Hfind Hlookup. *)
(*   clear Horaat1 Horaat2. *)
(*   consider box_fn_preserves_prop. rewrite Forall_forall in Hfn_preserves. *)
(*   apply find_some in Hfind. propositional. simplify. *)
(*   specialize Hfn_preserves with (1 := Hfind0). destruct_match_pairs; simplify; propositional. *)
(*   apply find_some in Heqo. propositional. rewrite beq_dec_iff in *. subst. *)
(*   eauto. *)
(* Qed. *)

(* Lemma ext_fns_forall: *)
(*   forall ext_fn_sims fns (sigma1 sigma2: ext_sigma_t), *)
(*   forallb (fun f : N => existsb (beq_dec f) ext_fn_sims) fns = true -> *)
(*   Forall (fun f : ext_fn_t => forall v : list bool, sigma1 f v = sigma2 f v) ext_fn_sims -> *)
(*   Forall (fun f : ext_fn_t => forall v : list bool, sigma1 f v = sigma2 f v) fns. *)
(* Proof. *)
(*   intros. rewrite forallb_forall in H. apply Forall_forall. rewrite Forall_forall in H0. *)
(*   intros. specialize H with (1 := H1). apply existsb_exists in H. propositional. simplify. *)
(*   eauto. *)
(* Qed. *)
(* Lemma box_sim_state_prop_implies: *)
(*   forall box def sim st1 st2, *)
(*   In box sim -> *)
(*   WF_boxes box_defs -> *)
(*   In (box, def) box_defs -> *)
(*   box_sim_state_prop sim st1 st2 -> *)
(*   box_sim def st1 st2. *)
(* Proof. *)
(*   consider box_sim_state_prop. *)
(*   intros * Hin_sim Hwf Hin_def Hsim. *)
(*   rewrite Forall_forall in Hsim. *)
(*   specialize Hsim with (1 := Hin_sim). *)
(*   destruct Hwf. unfold BoxRegsUnique in *. *)
(*   simplify. apply find_some in Heqo. propositional. rewrite beq_dec_iff in Heqo1. propositional. *)
(*   specialize WFBoxes_Unique0 with (1 := Hin_def) (2 := Heqo0). subst. assumption. *)
(* Qed. *)
(* Lemma box_sim_regs_unchanged: *)
(*   forall box st1 st2 st1' st2', *)
(*   box_sim box st1 st2 -> *)
(*   (forall reg, In reg (get_box_regs box) -> st1.[reg] = st1'.[reg]) -> *)
(*   (forall reg, In reg (get_box_regs box) -> st2.[reg] = st2'.[reg]) -> *)
(*   box_sim box st1' st2'. *)
(* Proof. *)
(*   intros * Hsim Hin1 Hin2. destruct Hsim. *)
(*   assert (forall r : reg_t, In r (map fst (box_valid_regs box)) -> st1'.[r] = st2'.[r]). *)
(*   - consider get_box_regs. *)
(*     intros. rewrite<-Hin1. rewrite<-Hin2. auto. *)
(*     all: apply in_or_app; auto. *)
(*   - constructor; auto. *)
(*     consider box_data_sim. *)
(*     intros Hvalid. propositional. *)
(*     specialize pf_box_data_sim0 with (2 := H0). *)
(*     apply existsb_exists in H0. propositional; simplify. *)
(*     consider get_box_regs. *)
(*     rewrite<-Hin1 by (apply in_or_app; auto). rewrite<-Hin2 by (apply in_or_app; auto). *)
(*     apply pf_box_data_sim0. rewrite Forall_forall. *)
(*     rewrite Forall_forall in Hvalid. intros. specialize Hvalid with (1 := H1). destruct_match_pairs; propositional. *)
(*     apply Hin1. apply in_or_app. left. apply in_map with (f := fst) in H1. auto. *)
(* Qed. *)
(* Lemma action_writes_regs_only_sim: *)
(*   forall int_fns def sigma fuel r st gamma action gamma' st' v' is_safe b0 ext_fn_log ext_fn_log', *)
(*   action_writes_regs_only int_fns action (get_box_regs def) -> *)
(*   oraat_interp_action sigma int_fns struct_defs fuel r st ext_fn_log is_safe gamma action = *)
(*             (true, Some (gamma', st', ext_fn_log', v')) -> *)
(*   (forall r : reg_t, In r (get_box_regs b0) -> ~In r (get_box_regs def) ) -> *)
(*   (forall reg : reg_t, In reg (get_box_regs b0) -> st.[reg] = st'.[reg]). *)
(* Proof. *)
(*   intros * Hwrites Horaat Hdisjoint. *)
(*   consider action_writes_regs_only. propositional. simplify. *)
(*   specialize Hdisjoint with (1 := H). specialize Hwrites0 with (1 := Hdisjoint). *)
(*   simplify_oraat_interp_action_safety. consider taint_empty. *)
(*   eapply taint_safety_function in Horaat; eauto with solve_taint. *)
(*   2: { erewrite Heqr0. eauto. } *)
(*   symmetry. *)
(*   eapply taint_set_to_prop_no_write'; eauto.  consider no_writes_in_taint_set. rewrite Heqr0. *)
(*   destruct_match; auto. specialize Hwrites0 with (1 := eq_refl); propositional. *)
(*   rewrite Hwrites1. rewrite Hwrites2. auto. *)
(* Qed. *)
(* Lemma pf_oraat2_action_writes_regs_box_sim_state_preserved: *)
(*   forall sims st1 st2 st1' st2' sigma1 fuel1 r1 gamma1 action gamma1' v1' sigma2 fuel2 r2 gamma2 gamma2' v2' def box *)
(*     ext_fn_log1 ext_fn_log1' *)
(*     ext_fn_log2 ext_fn_log2' *)
(*   , *)
(*   box_sim_state_prop sims st1 st2 -> *)
(*   oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 st1 ext_fn_log1 true gamma1 *)
(*              action = (true, Some (gamma1', st1', ext_fn_log1', v1')) -> *)
(*   oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 st2 ext_fn_log2 true gamma2 *)
(*              action = (true, Some (gamma2', st2', ext_fn_log2', v2')) -> *)
(*   In (box, def) box_defs -> *)
(*   In box sims -> *)
(*   WF_boxes box_defs -> *)
(*   action_writes_regs_only int_fns action (get_box_regs def) -> *)
(*   box_sim def st1' st2' -> *)
(*   box_sim_state_prop sims st1' st2'. *)
(* Proof. *)
(*   intros * Hsim Horaat1 Horaat2 Hin_box Hin_sim Hwf_box Hwrite Hsim_preserved. *)
(*   (* assert (Hsim_def: box_sim def st1 st2) by (eapply box_sim_state_prop_implies; eauto). *) *)
(*   consider box_sim_state_prop. *)
(*   rewrite Forall_forall. rewrite Forall_forall in Hsim. intros * Hsim'. *)
(*   specialize (Hsim _ Hsim'). simplify. *)
(*   apply find_some in Heqo. propositional. rewrite beq_dec_iff in Heqo1. subst. *)
(*   destruct Hwf_box. *)
(*   destruct_with_eqn (beq_dec box b). *)
(*   - rewrite beq_dec_iff in Heqb1. subst. *)
(*     unfold BoxRegsUnique. rewrite (WFBoxes_Unique0  _ _ _ Heqo0 Hin_box). assumption. *)
(*   - unfold BoxRegsDisjoint in *. *)
(*     specialize WFBoxes_Disjoint0 with (1 := Heqo0) (2 := Hin_box). *)
(*     rewrite beq_dec_false_iff in Heqb1. *)
(*     eapply box_sim_regs_unchanged; eauto. *)
(*     + eapply action_writes_regs_only_sim; eauto. unfold not in *; intros. apply Heqb1. symmetry. eauto. *)
(*     + eapply action_writes_regs_only_sim; eauto. unfold not in *; intros. apply Heqb1. symmetry. eauto. *)
(* Qed. *)
(* Lemma pf_action_writes_regs_only_box_sim_preserved: *)
(*   forall box_fns fn sims st1 st2 st1' st2' sigma1 fuel1 r1 gamma1' v1' sigma2 fuel2 r2 gamma2' v2' box n exts n0 fn_spec is_safe1 is_safe2 gamma_var ext_fn_sims *)
(*   ext_fn_log1 ext_fn_log1' ext_fn_log2 ext_fn_log2', *)
(*   box_sim_state_prop sims r1 r2 -> *)
(*   box_sim_state_prop sims st1 st2 -> *)
(*   oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 st1 ext_fn_log1 is_safe1 (fn_gamma (fn_arg_name fn_spec) gamma_var) (fn_body fn_spec) = (true, Some (gamma1', st1', ext_fn_log1', v1')) -> *)
(*   oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 st2 ext_fn_log2 is_safe2 (fn_gamma (fn_arg_name fn_spec) gamma_var) (fn_body fn_spec) = (true, Some (gamma2', st2', ext_fn_log2', v2')) -> *)
(*   box_fn_preserves_prop box_fns -> *)
(*   find (fun '(f, _) => beq_dec fn f) box_fns = Some (n, (box, exts)) -> *)
(*   lookup_int_fn int_fns fn tt = Success (n0, fn_spec) -> *)
(*   existsb (beq_dec box) sims = true -> *)
(*   WF_boxes box_defs -> *)
(*   Forall (fun f : ext_fn_t => forall v : list bool, sigma1 f v = sigma2 f v) ext_fn_sims -> *)
(*   forallb (fun f : N => existsb (beq_dec f) ext_fn_sims) exts = true -> *)
(*   box_sim_state_prop sims st1' st2' /\ v1' = v2'. *)
(* Proof. *)
(*   intros * Hsim0 Hsim1 Horaat1 Horaat2 Hpreserves Hfind Hlookup Hexists Hext_sims Hext_fns Hwf_boxes. *)
(*   eapply function_preserves_box_sim_state_prop in Hpreserves; eauto. *)
(*   propositional. *)
(*   apply existsb_exists in Hexists. propositional. rewrite beq_dec_iff in Hexists2. subst. *)
(*   repeat simplify_oraat_interp_action_safety. *)
(*   split. *)
(*   - eapply pf_oraat2_action_writes_regs_box_sim_state_preserved with (2 := Horaat1) (3 := Horaat2); eauto. *)
(*     consider function_preserves_box_sim. *)
(*     eapply Hpreserves0; eauto. *)
(*     + eapply ext_fns_forall; eauto. *)
(*     + eapply box_sim_state_prop_implies; eauto. *)
(*     + eapply box_sim_state_prop_implies; eauto. *)
(*   - consider function_preserves_box_sim. *)
(*     eapply Hpreserves0; eauto. *)
(*     + eapply ext_fns_forall; eauto. *)
(*     + eapply box_sim_state_prop_implies; eauto. *)
(*     + eapply box_sim_state_prop_implies; eauto. *)
(* Qed. *)
(* Lemma pf_writes_not_in_box_sim_preserved: *)
(*   forall box_fns fn sims st1 st2 st1' st2' sigma1 fuel1 r1 gamma1' v1' sigma2 fuel2 r2 gamma2' v2' box n exts n0 fn_spec is_safe1 is_safe2 gamma_var ext_fn_log1 ext_fn_log1' ext_fn_log2 ext_fn_log2', *)
(*   box_sim_state_prop sims r1 r2 -> *)
(*   box_sim_state_prop sims st1 st2 -> *)
(*   oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 st1 ext_fn_log1 is_safe1 (fn_gamma (fn_arg_name fn_spec) gamma_var) (fn_body fn_spec) = (true, Some (gamma1', st1', ext_fn_log1', v1')) -> *)
(*   oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 st2 ext_fn_log2 is_safe2 (fn_gamma (fn_arg_name fn_spec) gamma_var) (fn_body fn_spec) = (true, Some (gamma2', st2', ext_fn_log2', v2')) -> *)
(*   box_fn_preserves_prop box_fns -> *)
(*   find (fun '(f, _) => beq_dec fn f) box_fns = Some (n, (box, exts)) -> *)
(*   lookup_int_fn int_fns fn tt = Success (n0, fn_spec) -> *)
(*   existsb (beq_dec box) sims = false -> *)
(*   WF_boxes box_defs -> *)
(*   box_sim_state_prop sims st1' st2'. *)
(* Proof. *)
(*   intros * Hsim0 Hsim1 Horaat1 Horaat2 Hpreserves Hfind Hlookup Hexists Hwf_boxes. *)
(*   eapply function_preserves_box_sim_state_prop in Hpreserves; eauto. *)
(*   consider box_sim_state_prop. *)
(*   rewrite Forall_forall in *. intros * Hin. *)
(*   specialize (Hsim0 _ Hin). simplify. *)
(*   specialize (Hsim1 _ Hin). simplify. *)
(*   propositional. *)
(*   destruct Hwf_boxes. unfold BoxRegsDisjoint in *. *)
(*   apply find_some in Heqo0. propositional. rewrite beq_dec_iff in Heqo2. subst. *)
(*   specialize WFBoxes_Disjoint0 with (1 := Hpreserves1) (2 := Heqo1). *)
(*   apply existsb_false_forall in Hexists. rewrite forallb_forall in Hexists. *)
(*   specialize Hexists with (1 := Hin). rewrite negb_true_iff in Hexists. rewrite beq_dec_false_iff in Hexists. *)
(*   eapply box_sim_regs_unchanged; eauto. *)
(*   + eapply action_writes_regs_only_sim; eauto. *)
(*   + eapply action_writes_regs_only_sim; eauto. *)
(* Qed. *)

(* Lemma pf_writes_filter_box_sim_preserved: *)
(*   forall box_fns fn sims st1 st2 st1' st2' sigma1 fuel1 r1 gamma1' v1' sigma2 fuel2 r2 gamma2' v2' box n exts n0 fn_spec is_safe1 is_safe2 gamma_var1 gamma_var2 *)
(*     ext_fn_log1 ext_fn_log1' ext_fn_log2 ext_fn_log2', *)
(*   box_sim_state_prop sims r1 r2 -> *)
(*   box_sim_state_prop sims st1 st2 -> *)
(*   oraat_interp_action sigma1 int_fns struct_defs fuel1 r1 st1 ext_fn_log1 is_safe1 (fn_gamma (fn_arg_name fn_spec) gamma_var1) (fn_body fn_spec) = (true, Some (gamma1', st1', ext_fn_log1', v1')) -> *)
(*   oraat_interp_action sigma2 int_fns struct_defs fuel2 r2 st2 ext_fn_log2 is_safe2 (fn_gamma (fn_arg_name fn_spec) gamma_var2) (fn_body fn_spec) = (true, Some (gamma2', st2', ext_fn_log2', v2')) -> *)
(*   box_fn_preserves_prop box_fns -> *)
(*   find (fun '(f, _) => beq_dec fn f) box_fns = Some (n, (box, exts)) -> *)
(*   lookup_int_fn int_fns fn tt = Success (n0, fn_spec) -> *)
(*   (* existsb (beq_dec box) sims = false -> *) *)
(*   WF_boxes box_defs -> *)
(*   box_sim_state_prop (filter (fun box2 : box_t => negb (beq_dec box box2)) sims) st1' st2'. *)
(* Proof. *)
(*   intros * Hsim0 Hsim1 Horaat1 Horaat2 Hpreserves Hfind Hlookup (* Hexists *) Hwf_boxes. *)
(*   eapply function_preserves_box_sim_state_prop in Hpreserves; eauto. propositional. *)

(*   consider box_sim_state_prop. *)
(*   rewrite Forall_forall in *. intros * Hin. *)
(*   propositional. *)
(*   apply filter_In in Hin. propositional. specialize (Hsim0 _ Hin0). specialize (Hsim1 _ Hin0). simplify. *)
(*   destruct Hwf_boxes. unfold BoxRegsDisjoint in *. *)
(*   apply find_some in Heqo. propositional. rewrite beq_dec_iff in Heqo1. subst. *)
(*   specialize WFBoxes_Disjoint0 with (1 := Hpreserves1) (2 := Heqo0). *)
(*   eapply box_sim_regs_unchanged; eauto. *)
(*   + eapply action_writes_regs_only_sim; eauto. *)
(*   + eapply action_writes_regs_only_sim; eauto. *)
(* Qed. *)
(* Lemma gamma_sim_correct_refl: *)
(*   forall gamma sim_gamma, *)
(*   gamma_vars_eq gamma sim_gamma -> *)
(*   gamma_sim_correct gamma gamma sim_gamma. *)
(* Proof. *)
(*   consider @gamma_vars_eq. consider gamma_sim_correct. *)
(*   induction gamma; intros. *)
(*   - inversions H. constructor. *)
(*   - inversions H. destruct_match_pairs; simplify. *)
(*     constructor; auto. *)
(* Qed. *)

(* Hint Immediate gamma_sim_correct_refl: solve_box_sim. *)
(* Lemma reg_sim_state_prop_refl: *)
(*   forall sim (st: state_t), *)
(*   reg_sim_state_prop sim st st. *)
(* Proof. *)
(*   intros. consider reg_sim_state_prop. auto. *)
(* Qed. *)
(* Hint Immediate reg_sim_state_prop_refl: solve_box_sim. *)

(* Definition ValidBoxSims (boxes: list box_t) : Prop := *)
(*   Forall (fun b => exists def, In (b,def) box_defs) boxes. *)
(* Lemma box_sim_state_prop_refl: *)
(*   forall sim (st: state_t), *)
(*   ValidBoxSims sim -> *)
(*   box_sim_state_prop sim st st. *)
(* Proof. *)
(*   consider ValidBoxSims. consider box_sim_state_prop. *)
(*   intros. rewrite Forall_forall in *. *)
(*   intros * Hin. specialize (H _ Hin). propositional. *)
(*   destruct_match; destruct_match_pairs; subst. *)
(*   - constructor; auto. unfold box_data_sim. auto. *)
(*   - eapply find_none in Heqo; eauto. destruct_match_pairs; simplify. *)
(*     contradiction. *)
(* Qed. *)
(* Hint Immediate box_sim_state_prop_refl: solve_box_sim. *)

(* Lemma remove_tainted_action_none_correct: *)
(*   forall fuel1 fuel2 box_fns sigma sim_st sim_gamma action r r_acc is_safe gamma opt ext_fn_log, *)
(*   remove_tainted_action' int_fns reg_box_defs box_fns fuel1 sim_st sim_gamma action = Success None -> *)
(*   oraat_interp_action sigma int_fns struct_defs fuel2 r r_acc ext_fn_log is_safe gamma action = (true, opt) -> *)
(*   opt = None. *)
(* Proof. *)
(*   induction fuel1; [discriminate | ]. *)
(*   destruct fuel2; [discriminate | ]. *)
(*   intros * Hremove Horaat. *)
(*   destruct action; cbn in *; unfold res_opt_bind in *; simplify; auto. *)
(*   destruct_all_matches; simplify. *)
(*   all: destruct_all_matches; repeat match goal with *)
(*        | H: remove_tainted_action' _ _ _ _ _ _ ?action = Success None, *)
(*          H1: oraat_interp_action _ _ _ _ _ _ _ _ _ ?action = (true, _) |- _ => *)
(*          eapply IHfuel1 with (2 := H1) in H; subst *)
(*        | H: _ && _ = true |- _ => rewrite andb_true_iff in H *)
(*        | |- _ => simplify_oraat_interp_action_safety *)
(*        | |- _ => progress (simpl in *;simplify;propositional; eauto with solve_box_sim; try congruence) *)
(*        end. *)
(* Qed. *)
(* Lemma gamma_sim_correct_varenv_update_false: *)
(*   forall gamma g sim_gamma s1 var l, *)
(*   is_success (varenv_lookup_var g var tt) = true -> *)
(*   gamma_sim_correct gamma g s1 -> *)
(*   gamma_vars_eq gamma g -> *)
(*   gamma_vars_eq gamma sim_gamma -> *)
(*   gamma_state_le s1 sim_gamma -> *)
(*   gamma_sim_correct gamma (varenv_update g var l) (varenv_update s1 var false). *)
(* Proof. *)
(*   unfold gamma_vars_eq, gamma_state_le, gamma_sim_correct. *)
(*   consider @varenv_update. consider @varenv_lookup_var. *)
(*   induction gamma; intros * Hvar Hsim Heq1 Heq2 Hle. *)
(*   - inversions Hsim. inversions Hle. simpl in *. discriminate. *)
(*   - inversions Heq1. inversions Heq2. inversions Hle. inversions Hsim. destruct_match_pairs; propositional. *)
(*     simpl in *. destruct_match. *)
(*     + apply String.eqb_eq in Heqb1. subst. constructor; split_ands_in_goal; propositional; discriminate. *)
(*     + constructor; simpl in *; eauto. *)
(* Qed. *)
(* Hint Immediate gamma_sim_correct_varenv_update_false: solve_box_sim. *)
(* Lemma box_sim_state_prop_implies_valid_box_sim: *)
(*   forall bs st1 st2, *)
(*   box_sim_state_prop bs st1 st2  -> *)
(*   ValidBoxSims bs. *)
(* Proof. *)
(*   unfold box_sim_state_prop. unfold ValidBoxSims. intros. *)
(*   rewrite Forall_forall. rewrite Forall_forall in H. intros. *)
(*   specialize H with (1 := H0). simplify. apply find_some in Heqo. propositional; eauto. rewrite beq_dec_iff in Heqo1. *)
(*   subst. eauto. *)
(* Qed. *)
(* Lemma gamma_state_le_implies_gamma_var_eq: *)
(*   forall s1 s2, *)
(*   gamma_state_le s1 s2 -> *)
(*   gamma_vars_eq s1 s2. *)
(* Proof. *)
(*   consider gamma_state_le. consider @gamma_vars_eq. *)
(*   intros. *)
(*   eapply Forall2_impl; eauto. intros; destruct_match_pairs; propositional. *)
(* Qed. *)
(* Lemma gamma_sim_correct_sym: *)
(*   forall sim g1 g2 , *)
(*   gamma_sim_correct g1 g2 sim -> *)
(*   gamma_sim_correct g2 g1 sim. *)
(* Proof. *)
(*   consider gamma_sim_correct. *)
(*   induction sim; intros * Hsim. *)
(*   - inversions Hsim. constructor. *)
(*   - inversions Hsim. destruct_match_pairs; propositional. constructor; eauto. *)
(*     split_ands_in_goal; propositional. *)
(* Qed. *)
(* Hint Immediate gamma_sim_correct_sym: solve_box_sim. *)
(* Lemma reg_sim_state_prop_sym: *)
(*   forall sim g1 g2 , *)
(*   reg_sim_state_prop sim g1 g2 -> *)
(*   reg_sim_state_prop sim g2 g1 . *)
(* Proof. *)
(*   consider reg_sim_state_prop. *)
(*   intros * Hsim; simpl in *. *)
(*   intros; symmetry; auto. *)
(* Qed. *)
(* Hint Immediate reg_sim_state_prop_sym: solve_box_sim. *)
(* Lemma box_sim_state_prop_sym: *)
(*   forall sim g1 g2 , *)
(*   box_sim_state_prop sim g1 g2 -> *)
(*   box_sim_state_prop sim g2 g1 . *)
(* Proof. *)
(*   consider box_sim_state_prop. *)
(*   induction sim; intros * Hsim. *)
(*   - constructor. *)
(*   - inversions Hsim. simplify. constructor; eauto. *)
(*     simpl_match. apply box_sim_sym. auto. *)
(* Qed. *)
(* Hint Immediate box_sim_state_prop_sym: solve_box_sim. *)
(* Lemma ValidBoxSims_le: *)
(*   forall sim sim', *)
(*   ValidBoxSims sim -> *)
(*   box_sim_le sim' sim -> *)
(*   ValidBoxSims sim'. *)
(* Proof. *)
(*   consider ValidBoxSims. consider box_sim_le. *)
(*   intros * Hsim Hle. *)
(*   rewrite Forall_forall. rewrite Forall_forall in *. propositional. *)
(* Qed. *)
(* Lemma gamma_vars_eq_sym: *)
(*   forall {A} (g1 g2: @varenv_t A), *)
(*   gamma_vars_eq g1 g2 -> *)
(*   gamma_vars_eq g2 g1. *)
(* Proof. *)
(*   consider @gamma_vars_eq. *)
(*   induction g1; intros. *)
(*   - inversions H. constructor. *)
(*   - inversions H. destruct_match_pairs; propositional. *)
(* Qed. *)
(* Hint Immediate gamma_vars_eq_sym : solve_box_sim. *)
(* Lemma gamma_vars_eq_varenv_bind: *)
(*   forall {A B} (g1: @varenv_t A) (g2: @varenv_t B) var v0 v1, *)
(*   gamma_vars_eq g1 g2 -> *)
(*   gamma_vars_eq (varenv_bind g1 var v0) (varenv_bind g2 var v1). *)
(* Proof. *)
(*   consider @gamma_vars_eq. consider @varenv_bind. *)
(*   intros; constructor; auto. *)
(* Qed. *)
(* Hint Immediate gamma_vars_eq_varenv_bind : solve_box_sim. *)
(* Lemma gamma_state_le_bind: *)
(*   forall sim1 sim2 v b, *)
(*   gamma_state_le sim2 (varenv_bind sim1 v b) -> *)
(*   gamma_state_le (tl sim2) sim1. *)
(* Proof. *)
(*   intros. eapply gamma_state_le_tl; eauto with solve_box_sim. *)
(* Qed. *)
(* Lemma reg_sim_state_prop_update_false': *)
(*   forall sim s1 s2 idx v, *)
(*   reg_sim_state_prop sim s1 s2 -> *)
(*   reg_sim_state_prop (update_sim_reg' sim idx false) s1 (state_set s2 idx v). *)
(* Proof. *)
(*   consider reg_sim_state_prop. consider @update_sim_reg'. *)
(*   intros * Hsim *  Hget. destruct_with_eqn (beq_dec reg idx); simplify. *)
(*   + rewrite SortedRegEnv.update_correct_eq in Hget. simplify. *)
(*   + rewrite SortedRegEnv.update_correct_neq in Hget by auto. *)
(*     rewrite unsafe_get_reg_state_set_neq by auto. auto. *)
(* Qed. *)
(* Hint Immediate reg_sim_state_prop_update_false' : solve_box_sim. *)
(* Lemma box_sim_state_prop_state_set_r: *)
(*   forall (box_sim : list box_t) (st1 st2 : state_t) (idx : reg_t) (v1 : Bits.vect_t), *)
(*   box_sim_state_prop box_sim st1 st2 -> *)
(*   reg_in_box_defs reg_box_defs idx = false -> *)
(*   box_sim_state_prop box_sim st1 (state_set st2 idx v1). *)
(* Proof. *)
(*   unfold box_sim_state_prop, reg_in_box_defs, reg_box_defs. *)
(*   intros * Hsim Hreg. *)
(*   rewrite map_map in Hreg. *)
(*   apply Forall_forall. *)
(*   rewrite Forall_forall in Hsim. intros box HIn. specialize Hsim with (1 := HIn). *)
(*   destruct_match; auto. destruct_match_pairs; subst. *)
(*   apply existsb_false_forall in Hreg. *)
(*   rewrite forallb_forall in Hreg. *)
(*   apply find_some in Heqo; propositional. rewrite beq_dec_iff in Heqo1. subst. *)
(*   specialize (Hreg ((fun x0 => snd (let '(box,def) := x0 in (box, get_box_regs def))) (b,b0))). *)
(*   specialize Hreg with (1 := in_map _ _ _ Heqo0). *)
(*   rewrite negb_true_iff in Hreg. simpl in Hreg. *)
(*   apply existsb_false_forall in Hreg. *)
(*   apply box_sim_state_update_r; auto. *)
(* Qed. *)
(* Hint Immediate box_sim_state_prop_state_set_r: solve_box_sim. *)

(* Lemma function_preserves_reg_sim_state_prop1: *)
(*   forall sims sigma fuel r r_acc gamma fn_spec gamma' st' v' box_fns fn n exts box n0 ext_fn_log ext_fn_log', *)
(*   RegsNotInBoxes sims reg_box_defs -> *)
(*   box_fn_preserves_prop box_fns -> *)
(*   find (fun '(f, _) => beq_dec fn f) box_fns = Some (n, (box, exts)) -> *)
(*   lookup_int_fn int_fns fn tt = Success (n0, fn_spec) -> *)
(*   oraat_interp_action sigma int_fns struct_defs fuel r r_acc ext_fn_log true gamma (fn_body fn_spec) = (true, Some (gamma', st', ext_fn_log', v')) -> *)
(*   reg_sim_state_prop sims r_acc st'. *)
(* Proof. *)
(*   intros * Hregs Hbox Hfind Hlookup Horaat. *)
(*   specialize function_writes_regs_only_def with (1 := Hbox) (2 := Hfind) (3 := Hlookup). *)
(*   intros (def & HIn & Hpreserves & Hwrites). *)
(*   specialize taint_safety_function with (1 := Horaat) as Htaint. *)
(*   consider action_writes_regs_only. propositional. simplify. consider @is_success_some. *)
(*   specialize (Htaint fuel0). consider taint_empty. repeat simpl_match. propositional. *)
(*   unfold RegsNotInBoxes in *. *)
(*   consider reg_sim_state_prop. *)
(*   intros * Hreg. *)

(*   specialize Hregs with (1 := Hreg) (box:= box) (def := get_box_regs def). *)
(*   assert_pre_and_specialize Hregs. *)
(*   { unfold reg_box_defs in *. apply in_map with (f := fun '(b,d) => (b,get_box_regs d)) in HIn; auto. } *)
(*   specialize Hwrites0 with (1 := Hregs). *)

(*   assert (no_writes_in_taint_set (Success (Some t)) reg  = true) as Hno_write. *)
(*   { unfold no_writes_in_taint_set. destruct_match; auto. *)
(*     specialize Hwrites0 with (1 := eq_refl); propositional. rewrite Hwrites1. rewrite Hwrites2. auto. *)
(*   } *)
(*   erewrite taint_set_to_prop_no_write' with (1 := Htaint) by auto. reflexivity. *)
(* Qed. *)

(* Hint Immediate function_preserves_reg_sim_state_prop1 : solve_box_sim. *)
(* Lemma box_sim_refl: *)
(*   forall box st, *)
(*   box_sim box st st. *)
(* Proof. *)
(*   constructor; auto. *)
(*   consider box_data_sim; auto. *)
(* Qed. *)
(* Hint Immediate box_sim_refl: solve_box_sims. *)
(* Lemma pf_writes_filter_box_sim_preserved1: *)
(*   forall box_fns fn sims st st' sigma fuel r gamma gamma' v' box n exts n0 fn_spec is_safe ext_fn_log ext_fn_log', *)
(*   ValidBoxSims sims -> *)
(*   oraat_interp_action sigma int_fns struct_defs fuel r st ext_fn_log is_safe gamma (fn_body fn_spec) = (true, Some (gamma', st', ext_fn_log', v')) -> *)
(*   box_fn_preserves_prop box_fns -> *)
(*   find (fun '(f, _) => beq_dec fn f) box_fns = Some (n, (box, exts)) -> *)
(*   lookup_int_fn int_fns fn tt = Success (n0, fn_spec) -> *)
(*   (* existsb (beq_dec box) sims = false -> *) *)
(*   WF_boxes box_defs -> *)
(*   box_sim_state_prop (filter (fun box2 : box_t => negb (beq_dec box box2)) sims) st st'. *)
(* Proof. *)
(*   intros * Hvalid Horaat Hpreserves Hfind Hlookup Hwf_boxes. *)
(*   eapply function_preserves_box_sim_state_prop in Hpreserves; eauto. *)
(*   consider ValidBoxSims. *)
(*   consider box_sim_state_prop. *)
(*   rewrite Forall_forall in *. intros * Hin. *)
(*   propositional. *)
(*   apply filter_In in Hin. propositional. *)
(*   rewrite negb_true_iff in Hin1. rewrite beq_dec_false_iff in Hin1. *)
(*   specialize Hvalid with (1 := Hin0). propositional. *)
(*   destruct Hwf_boxes. unfold BoxRegsDisjoint in *. *)
(*   apply find_some in Hfind. propositional; simplify. *)
(*   destruct_match. *)
(*   - apply find_some in Heqo. destruct_match_pairs; propositional. rewrite beq_dec_iff in Heqo1. subst. *)
(*     specialize WFBoxes_Disjoint0 with (1 := Hpreserves1) (2 := Heqo0). *)
(*     eapply box_sim_regs_unchanged with (1 := box_sim_refl _ _); eauto. *)
(*     eapply action_writes_regs_only_sim; eauto. *)
(*   - eapply find_none in Heqo; [ | eapply Hvalid0]. *)
(*     destruct_match_pairs; simplify. congruence. *)
(* Qed. *)
(* Lemma ValidBoxSim_filter: *)
(*   forall f sim, *)
(*   ValidBoxSims sim -> *)
(*   ValidBoxSims (filter f sim). *)
(* Proof. *)
(*   intros * Hsim. *)
(*   unfold ValidBoxSims in *. *)
(*   rewrite Forall_forall in *. *)
(*   intros * Hfilter. rewrite filter_In in Hfilter. propositional. *)
(* Qed. *)
(* Hint Immediate ValidBoxSim_filter: solve_box_sim. *)
(* Lemma box_sim_state_prop_filter: *)
(*   forall f sims st1 st2, *)
(*   box_sim_state_prop sims st1 st2 -> *)
(*   box_sim_state_prop (filter f sims) st1 st2. *)
(* Proof. *)
(*   intros * Hsim. unfold box_sim_state_prop in *. *)
(*   rewrite Forall_forall in *. *)
(*   intros * Hin. rewrite filter_In in Hin. propositional. eapply Hsim; eauto. *)
(* Qed. *)
(* Hint Immediate box_sim_state_prop_filter: solve_box_sim. *)
(* Lemma gamma_vars_eq_cons: *)
(*   forall {A} {B} (xs: @varenv_t A) (ys: @varenv_t B) v vx vy, *)
(*   gamma_vars_eq xs ys -> *)
(*   gamma_vars_eq ((v,vx)::xs) ((v,vy)::ys). *)
(* Proof. *)
(*   constructor; auto. *)
(* Qed. *)
(* Hint Immediate gamma_vars_eq_cons: solve_box_sim. *)

(* Lemma gamma_vars_eq_nil: *)
(*   forall {A} {B}, *)
(*   gamma_vars_eq ([]: @varenv_t A) ([]: @varenv_t B). *)
(* Proof. *)
(*   constructor. *)
(* Qed. *)
(* Hint Immediate gamma_vars_eq_nil: solve_box_sim. *)

(* Lemma remove_tainted_action_correct': *)
(*   forall fuel1 fuel2 box_fns sigma sim_st sim_gamma action sim_gamma' sim_st' r r_acc is_safe gamma gamma' st' v' ext_fn_log ext_fn_log', *)
(*   gamma_vars_eq gamma sim_gamma -> *)
(*   ValidBoxSims (sim_boxes sim_st) -> *)
(*   WF_boxes box_defs -> *)
(*   RegsNotInBoxes (sim_regs sim_st) reg_box_defs -> *)
(*   box_fn_preserves_prop box_fns -> *)
(*   remove_tainted_action' int_fns reg_box_defs box_fns fuel1 sim_st sim_gamma action = Success (Some(sim_gamma', sim_st')) -> *)
(*   oraat_interp_action sigma int_fns struct_defs fuel2 r r_acc ext_fn_log is_safe gamma action = (true, Some (gamma', st', ext_fn_log', v')) -> *)
(*   (* gamma_vars_eq gamma' sim_gamma' /\ *) *)
(*   gamma_sim_correct gamma gamma' sim_gamma' /\ *)
(*   reg_sim_state_prop (sim_regs sim_st') r_acc st' /\ *)
(*   box_sim_state_prop (sim_boxes sim_st') r_acc st'. *)
(* Proof. *)
(*   induction fuel1; [ discriminate | ]. *)
(*   destruct fuel2; [discriminate | ]. *)
(*   consider remove_tainted_action. *)
(*   intros * Hgammas_eq Hvalid Hwf Hregs_boxes Hbox_fns Hremove Horaat. *)
(*   specialize IHfuel1 with (3 := Hwf) (5 := Hbox_fns). *)
(*   destruct action; cbn in *; unfold res_opt_bind, __debug__ in *. *)
(*   Ltac solve_remove_tainted_action_correct IH := *)
(*     match goal with *)
(*     | H: _ && _ = true |- _ => rewrite andb_true_iff in H *)
(*     | H: remove_tainted_action' _ _ _ _ _ _ _ = Success (Some _) |- _ => *)
(*         (pose_fresh (proj1 (remove_tainted_action_decreases_sim' _ _ _ _ _ _ _ _ _ H)) || *)
(*          pose_fresh (proj1 (proj2 (remove_tainted_action_decreases_sim' _ _ _ _ _ _ _ _ _ H))) || *)
(*          pose_fresh (proj2 (proj2 (remove_tainted_action_decreases_sim' _ _ _ _ _ _ _ _ _ H)))) *)
(*     | H: oraat_interp_action _ _ _ _ _ _ _ _ ?gamma ?action = (true, Some _) |- _ => *)
(*         pose_fresh (oraat_interp_action_gamma_vars_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) *)
(*     | H: gamma_vars_eq ?gamma ?sim_gamma, *)
(*       H1: ValidBoxSims (sim_boxes ?sim_st), *)
(*       H2: RegsNotInBoxes (sim_regs ?sim_st) reg_box_defs, *)
(*       H3: remove_tainted_action' _ _ _ ?fuel1 ?sim_st ?sim_gamma ?action = Success (Some (_)), *)
(*       H4: oraat_interp_action _ _ _ _ _ _ _ _ _ ?action = (true, Some _) |- _ => *)
(*       eapply IH  with (1 := H) (2 := H1) (3 := H2) (4 := H3) in H4 *)
(*     | H: box_sim_state_prop ?bs _ _ |- _ => *)
(*         pose_fresh (box_sim_state_prop_implies_valid_box_sim _ _ _ H) *)
(*     | H: gamma_state_le ?s1 ?s2 |- _ => *)
(*         pose_fresh (gamma_state_le_implies_gamma_var_eq _ _ H) *)
(*     | H: gamma_sim_correct _ _ _ |- _ => *)
(*         pose_fresh (gamma_sim_correct_implies_var_eq2 _ _ _ H) || *)
(*         pose_fresh (gamma_sim_correct_implies_var_eq1 _ _ _ H) *)
(*     | H: remove_tainted_action' _ _ _ _ _ _ ?action = Success None, *)
(*         H1: oraat_interp_action _ _ _ _ _ _ _ _ _ ?action = (true, Some _) |- _ => *)
(*         exfalso; specialize remove_tainted_action_none_correct with (1 := H) (2 := H1); intros; subst; discriminate *)
(*     | H: ValidBoxSims ?sim, *)
(*       H1: box_sim_le ?sim' ?sim |- _ => *)
(*         pose_fresh (ValidBoxSims_le _ _ H H1) *)
(*     | H: gamma_vars_eq ?g1 ?g2 |- _ => *)
(*         pose_fresh (gamma_vars_eq_sym _ _ H) *)
(*     | H1: gamma_vars_eq ?gamma1 ?gamma2, *)
(*       H2: gamma_vars_eq ?gamma2 ?gamma3 |- _ => *)
(*         pose_fresh (gamma_vars_eq_trans _ _ _ H1 H2) *)
(*     | H: gamma_state_le ?sim1 ?sim2, *)
(*       H1: gamma_state_le ?sim2 ?sim3 |- _ => *)
(*         pose_fresh (gamma_state_le_trans _ _ _ H H1) *)
(*     | H: gamma_sim_correct ?gamma1 ?gamma1' ?gamma_sims', *)
(*       H1: gamma_sim_correct ?gamma2 ?gamma2' ?gamma_sims', *)
(*       H2: gamma_sim_correct ?gamma1 ?gamma2 ?gamma_sims' |- _ => *)
(*         pose_fresh (gamma_sim_correct_trans _ _ _ _ _ H H1 H2) *)
(*     | H: gamma_sim_correct ?x ?y ?Z |- _ => *)
(*         pose_fresh (gamma_sim_correct_sym _ _ _ H) *)
(*     | H: gamma_state_le ?sim' ?sim, *)
(*       H1: gamma_sim_correct ?gamma1 ?gamma2 ?sim |- _ => *)
(*         pose_fresh (gamma_sim_correct_le _ _ _ _ H H1) *)
(*     | H: remove_tainted_action' _ _ _ _ _ (varenv_bind ?s2 ?v ?v1) ?action2 = Success (Some _), *)
(*       H1: oraat_interp_action _ _ _ _ _ _ _ _ (varenv_bind ?g ?v ?v0) ?action2 = (true, Some _), *)
(*       H2: gamma_vars_eq ?g ?s2  |- _ => *)
(*         pose_fresh (gamma_vars_eq_varenv_bind _ _ v v0 v1 H2) *)
(*     | H: gamma_state_le ?sim2 (varenv_bind ?sim1 ?v ?b) |- _ => *)
(*         pose_fresh (gamma_state_le_bind _ _ _ _ H) *)
(*     | H: RegsNotInBoxes ?sim ?fns, *)
(*       H1: reg_sim_le ?sim' ?sim |- _ => *)
(*         pose_fresh (RegNotInBoxes_decreases_preserve _ _ _ H H1) *)
(*     | |- _ => simplify_oraat_interp_action_safety *)
(*     | |- _ => progress (simpl in *;simplify;propositional; eauto with solve_box_sim; try congruence) *)
(*     end. *)
(*   all: destruct_all_matches; repeat solve_remove_tainted_action_correct IHfuel1. *)
(*   - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1. *)
(*     eapply gamma_sim_correct_varenv_update_false; eauto with solve_box_sim. *)
(*   - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1. *)
(*     + eapply gamma_sim_correct_trans with (3 := Horaat0); eauto with solve_box_sim. *)
(*     + eapply reg_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       apply reg_sim_state_prop_sym; eauto with solve_box_sim. *)
(*     + eapply box_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       apply box_sim_state_prop_sym; eauto with solve_box_sim. *)
(*   - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1. *)
(*     + eapply gamma_sim_correct_le with (sim := s4); eauto. *)
(*       eapply gamma_sim_correct_trans with (3 := Horaat0); eauto with solve_box_sim. *)
(*     + eapply reg_sim_le_state_prop; eauto with solve_box_sim. *)
(*       eapply reg_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       eapply reg_sim_le_state_prop; eauto with solve_box_sim. *)
(*     + eapply box_sim_le_state_prop; eauto with solve_box_sim. *)
(*       eapply box_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       eapply box_sim_le_state_prop; eauto with solve_box_sim. *)
(*   - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1. *)
(*     + eapply gamma_sim_correct_trans with (3 := Horaat0); eauto with solve_box_sim. *)
(*     + eapply reg_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       apply reg_sim_state_prop_sym; eauto with solve_box_sim. *)
(*     + eapply box_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       apply box_sim_state_prop_sym; eauto with solve_box_sim. *)
(*   - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1. *)
(*     + eapply gamma_sim_correct_trans; eauto with solve_box_sim. *)
(*     + eapply reg_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       eapply reg_sim_le_state_prop; eauto with solve_box_sim. *)
(*       eapply reg_sim_le_state_prop; eauto with solve_box_sim. *)
(*     + eapply box_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       eapply box_sim_le_state_prop; eauto with solve_box_sim. *)
(*       eapply box_sim_le_state_prop; eauto with solve_box_sim. *)
(*   - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1. *)
(*     + eapply gamma_sim_correct_trans; eauto with solve_box_sim. *)
(*     + eapply reg_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       eapply reg_sim_le_state_prop; eauto with solve_box_sim. *)
(*     + eapply box_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       eapply box_sim_le_state_prop; eauto with solve_box_sim. *)
(*   - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1. *)
(*     + eapply gamma_sim_correct_trans with (gamma2 := g); eauto with solve_box_sim. *)
(*       eapply gamma_sim_correct_sym. replace g with (tl (varenv_bind g v l)) by auto. *)
(*       eauto with solve_box_sim. *)
(*     + eapply reg_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       eapply reg_sim_le_state_prop; eauto with solve_box_sim. *)
(*     + eapply box_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       eapply box_sim_le_state_prop; eauto with solve_box_sim. *)
(*   - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1. *)
(*     + eapply gamma_sim_correct_trans; eauto with solve_box_sim. *)
(*     + eapply reg_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       eapply reg_sim_le_state_prop; eauto with solve_box_sim. *)
(*     + eapply box_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       eapply box_sim_le_state_prop; eauto with solve_box_sim. *)
(*   - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1. *)
(*     + consider get_fn_arg_and_body''. consider @success_or_default. simplify. *)
(*       eapply reg_sim_state_prop_trans; eauto with solve_box_sim. *)
(*     + eapply box_sim_state_prop_trans; eauto with solve_box_sim. *)
(*       * eapply box_sim_state_prop_refl; eauto with solve_box_sim. *)
(*       * consider get_fn_arg_and_body''; unfold success_or_default in *; simplify. *)
(*         eapply pf_writes_filter_box_sim_preserved1; eauto with solve_box_sim. *)
(*   - split_ands_in_goal; repeat solve_remove_tainted_action_correct IHfuel1. *)
(*     + eapply reg_sim_state_prop_trans with (sim1 := s); eauto with solve_box_sim. *)
(*       { eapply reg_sim_state_prop_sym. eauto with solve_box_sim. } *)
(*       consider get_fn_arg_and_body''. consider @success_or_default. simplify. *)
(*       eapply IHfuel1 with (action := fn_body i) (4 := Heqr2) (5 := Heqp4); eauto with solve_box_sim. *)
(*       unfold fn_gamma. *)
(*       eapply gamma_vars_eq_cons; eauto with solve_box_sim. *)
(*     + eapply box_sim_state_prop_trans with (st1:= s); eauto with solve_box_sim. *)
(*       { eapply box_sim_state_prop_sym. eauto with solve_box_sim. } *)
(*       consider get_fn_arg_and_body''. consider @success_or_default. simplify. *)
(*       eapply IHfuel1 with (action := fn_body i) (4 := Heqr2) (5 := Heqp4); eauto with solve_box_sim. *)
(*       eapply gamma_vars_eq_cons; eauto with solve_box_sim. *)
(* Qed. *)
(* Lemma remove_tainted_action_correct: *)
(*   forall fuel1 fuel2 box_fns sigma sim_st sim_gamma action sim_gamma' sim_st' r r_acc is_safe gamma gamma' st' v' ext_log ext_log', *)
(*   gamma_vars_eq gamma sim_gamma -> *)
(*   ValidBoxSims (sim_boxes sim_st) -> *)
(*   WF_boxes box_defs -> *)
(*   RegsNotInBoxes (sim_regs sim_st) reg_box_defs -> *)
(*   box_fn_preserves_prop box_fns -> *)
(*   remove_tainted_action int_fns reg_box_defs box_fns fuel1 sim_st sim_gamma action = Success (sim_gamma', sim_st') -> *)
(*   oraat_interp_action sigma int_fns struct_defs fuel2 r r_acc ext_log is_safe gamma action = (true, Some (gamma', st', ext_log', v')) -> *)
(*   (* gamma_vars_eq gamma' sim_gamma' /\ *) *)
(*   gamma_sim_correct gamma gamma' sim_gamma' /\ *)
(*   reg_sim_state_prop (sim_regs sim_st') r_acc st' /\ *)
(*   box_sim_state_prop (sim_boxes sim_st') r_acc st'. *)
(* Proof. *)
(*   consider remove_tainted_action. intros * Hgamma Hbox Hwf Hregs Hfns Hremove Horaat. *)
(*   bash_destruct Hremove. *)
(*   - simplify. eapply remove_tainted_action_correct' with (6 := Heqr0); eauto. *)
(*   - eapply remove_tainted_action_none_correct with (2 := Horaat) in Heqr0. discriminate. *)
(* Qed. *)

(*       Ltac solve_box_sim_analyze_action_correct IH := *)
(*         match goal with *)
(*         | H: oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ => *)
(*             match b with *)
(*             | true => fail *)
(*             | _ => let H' := fresh in *)
(*                   assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto); *)
(*                   rewrite H' in H; subst *)
(*             end *)
(*         | H: analyze_action _ _ _ _ _ _ _ _ ?action = Success None, *)
(*           H1: oraat_interp_action _ _ _ _ _ _ _ _ _ ?action = (true, Some _) |- _ => *)
(*             exfalso; apply analyze_none_implies_fail with (1 := H) (2 := H1); auto *)
(*         | H: _ && _ = true |- _ => rewrite andb_true_iff in H *)
(*         | H1: oraat_interp_action _ _ _ _ ?r1 ?r_acc1 _ _ ?gamma1 ?action = (true, Some(?gamma1', ?st1', ?v1')), *)
(*           H2: oraat_interp_action _ _ _ _ ?r2 ?r_acc2 _ _ ?gamma2 ?action = (true, Some(?gamma2', ?st2', ?v2')), *)
(*           (* H3: box_sim_state_prop (sim_boxes ?acc_reg_sims) ?r1 ?r2, *) *)
(*           H4: box_sim_state_prop (sim_boxes ?acc_reg_sims) ?r_acc1 ?r_acc2, *)
(*           (* H4: gamma_sim_correct ?gamma1 ?gamma2 ?gamma_sims, *) *)
(*           H5: reg_sim_state_prop (sim_regs ?acc_reg_sims) ?r_acc1 ?r_acc2, *)
(*           H6: analyze_action _ _ _ _ _ _ ?acc_reg_sims ?gamma_sims ?action = Success (Some _) |- _ => *)
(*             eapply IH with (2 := H2) (* (3 := H3) *) (4 := H4)  (6 := H5) (8 := H6) in H1; [ | solve[eauto with solve_box_sim] ..]; clear H2 *)
(*         | H: remove_tainted_action _ _ _ _ ?sim_st ?sim_gamma _ = Success (_, _) |- _ => *)
(*             (pose_fresh (proj1 (remove_tainted_action_decreases_sim _ _ _ _ _ _ _ _ _ H)) || *)
(*             (pose_fresh (sim_state_le_implies_reg_sim_le _ _ *)
(*                           (proj2 (remove_tainted_action_decreases_sim _ _ _ _ _ _ _ _ _ H)))) || *)
(*             (pose_fresh (sim_state_le_implies_box_sim_le _ _ *)
(*                           (proj2 (remove_tainted_action_decreases_sim _ _ _ _ _ _ _ _ _ H))))) *)
(*         | |- box_sim_le (merge_sim_boxes (sim_boxes _) (sim_boxes _)) _ => *)
(*           (eapply box_sim_le_merge_sim_boxes_l; solve[eauto with solve_box_sim]) || *)
(*           (eapply box_sim_le_merge_sim_boxes_r; solve[eauto with solve_box_sim]) *)
(*         | H: RegsNotInBoxes ?sim1 ?fn *)
(*           |- RegsNotInBoxes ?sim2 ?fn => *)
(*               eapply RegNotInBoxes_decreases_preserve with (1 := H); solve[eauto with solve_box_sim] *)
(*         | H: oraat_interp_action _ _ _ _ ?r1 ?r_acc1 _ _ ?gamma1 ?action = (true, Some(?gamma1', ?st1', ?v1')) |- _ => *)
(*             pose_fresh (oraat_interp_action_gamma_vars_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) *)
(*         | H: box_sim_le ?sim1 ?sim2 *)
(*           |- box_sim_le (filter _ ?sim1) ?sim2 => *)
(*             eapply box_sim_le_trans with (2 := H); solve[eauto with solve_box_sim] *)
(*         | H: gamma_sim_correct ?g1 ?g2 ?s |- _ => *)
(*             (pose_fresh (gamma_sim_correct_implies_var_eq1 _ _ _ H)) || *)
(*               (pose_fresh (gamma_sim_correct_implies_var_eq2 _ _ _ H)) *)
(*         | H: gamma_vars_eq ?gamma ?sim_gamma, *)
(*           H1: box_sim_state_prop (sim_boxes ?sim_st) _ _, *)
(*           H2: WF_boxes box_defs, *)
(*           H3: RegsNotInBoxes (sim_regs ?sim_st) _, *)
(*           H4: box_fn_preserves_prop ?box_fns, *)
(*           H5: remove_tainted_action _ _ _ _ ?sim_st ?sim_gamma ?action = Success (_, _), *)
(*           H6: oraat_interp_action _ _ _ _ _ _ _ _ ?gamma ?action = (true, Some _) |- _ => *)
(*             let tuple := constr:(remove_tainted_action_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ *)
(*                            H (box_sim_state_prop_implies_valid_box_sim _ _ _ H1) H2 H3 H4 H5 H6) in *)
(*             pose_fresh (proj1 tuple) || *)
(*             pose_fresh (proj1 (proj2 tuple)) || *)
(*             pose_fresh (proj2 (proj2 tuple)) *)
(*         | H: gamma_state_le ?sim' ?sim, *)
(*           H1: gamma_sim_correct ?gamma1 ?gamma2 ?sim |- _ => *)
(*             pose_fresh (gamma_sim_correct_le _ _ _ _ H H1) *)
(*         | H: box_sim_le ?box1 ?box2, *)
(*           H1:box_sim_le ?box2 ?box3 |- _ => *)
(*             pose_fresh (box_sim_le_trans _ _ _ H H1) *)
(*         | H : reg_sim_le ?sim2 ?sim1, *)
(*           H1: reg_sim_state_prop ?sim1 ?st1 ?st2 |- _ => *)
(*             pose_fresh (reg_sim_le_state_prop _ _ _ _ H H1) *)
(*         | H : box_sim_le ?sim2 ?sim1, *)
(*           H1: box_sim_state_prop ?sim1 ?st1 ?st2 |- _ => *)
(*             pose_fresh (box_sim_le_state_prop _ _ _ _ H H1) *)
(*         | H: RegsNotInBoxes ?sim _, *)
(*           H1: reg_sim_le ?sim' ?sim |- _ => *)
(*             pose_fresh (RegNotInBoxes_decreases_preserve _ _ _ H H1) *)
(*         | |- _ => progress (simpl in *;simplify;propositional; eauto with solve_box_sim; try congruence) *)
(*         end. *)

(*     Lemma box_sim_analyze_action_correct: *)
(*       forall fuel1 fuel2 fuel3 sigma1 sigma2 r1 r_acc1 r2 r_acc2 safe1 safe2 gamma1 gamma2 action *)
(*         gamma1' gamma2' st1' st2' v1' v2' box_fns ext_fn_sims init_reg_sims acc_reg_sims gamma_sims *)
(*         gamma_sims' reg_sims' v_sim' *)
(*         ext_fn_log1 ext_fn_log1' ext_fn_log2 ext_fn_log2', *)
(*         oraat_interp_action sigma1 int_fns struct_defs fuel1 *)
(*           r1 r_acc1 ext_fn_log1 safe1 gamma1 action = (true, Some(gamma1', st1', ext_fn_log1', v1')) -> *)
(*         oraat_interp_action sigma2 int_fns struct_defs fuel2 *)
(*           r2 r_acc2 ext_fn_log2 safe2 gamma2 action = (true, Some(gamma2', st2', ext_fn_log2', v2')) -> *)
(*         reg_sim_state_prop init_reg_sims r1 r2 -> *)
(*         box_sim_state_prop (sim_boxes acc_reg_sims) r1 r2 -> *)
(*         box_sim_state_prop (sim_boxes acc_reg_sims) r_acc1 r_acc2 -> *)
(*         WF_boxes box_defs -> *)
(*         Forall (fun f => forall v, sigma1 f v = sigma2 f v) ext_fn_sims -> *)
(*         box_fn_preserves_prop box_fns -> *)
(*         gamma_sim_correct gamma1 gamma2 gamma_sims -> *)
(*         reg_sim_state_prop (sim_regs acc_reg_sims) r_acc1 r_acc2 -> *)
(*         RegsNotInBoxes (sim_regs acc_reg_sims) (map (fun '(box, def) => (box, get_box_regs def)) box_defs) -> *)
(*         analyze_action int_fns *)
(*           (map (fun '(box, def) => (box, get_box_regs def)) box_defs) *)
(*           box_fns ext_fn_sims init_reg_sims *)
(*           fuel3 acc_reg_sims gamma_sims action = Success (Some (gamma_sims', reg_sims', v_sim')) -> *)
(*         RegsNotInBoxes (sim_regs reg_sims') (map (fun '(box, def) => (box, get_box_regs def)) box_defs) *)
(*         /\ gamma_sim_correct gamma1' gamma2' gamma_sims' *)
(*         /\ reg_sim_state_prop (sim_regs reg_sims') st1' st2' *)
(*         /\ box_sim_state_prop (sim_boxes reg_sims') st1' st2' *)
(*         /\ box_sim_le (sim_boxes reg_sims') (sim_boxes acc_reg_sims) *)
(*         /\ (match v_sim' with *)
(*            | true => v1' = v2' *)
(*            | false => True *)
(*            end). *)
(*     Proof. *)
(*       induction fuel1; intros * Horaat1 Horaat2 Hreg_sim0 Hbox_sim0 Hbox_sim1 Hwf_boxes Hext_sim Hbox_fns Hgamma_sim *)
(*                                   Hreg_sim1 Hwf_regs Hanalyze; [discriminate | ]. *)
(*       destruct fuel2; [discriminate | ]. *)
(*       destruct fuel3; [discriminate | ]. *)

(*       specialize IHfuel1 with (3 := Hreg_sim0) (6 := Hwf_boxes) (7 := Hext_sim) (8 := Hbox_fns). *)
(*       destruct action; destruct action; cbn in *; simplify; simpl in *; unfold __debug__, opt_bind_to_res, res_opt_bind, get_fn_arg_and_body'' in *; simplify; auto. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*         split_ands_in_goal; eauto with solve_box_sim. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*         split_ands_in_goal; eauto with solve_box_sim. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*         split_ands_in_goal; eauto with solve_box_sim. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*           split_ands_in_goal; eauto with solve_box_sim. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1. *)
(*         all: split_ands_in_goal; repeat solve_box_sim_analyze_action_correct IHfuel1. *)
(*         + eapply reg_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim. *)
(*         + eapply box_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim. *)
(*         + eapply reg_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim. *)
(*         + eapply box_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim. *)
(*         + eapply reg_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim. *)
(*         + eapply box_sim_state_prop_trans; [ | eauto with solve_box_sim .. ]; eauto with solve_box_sim. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*           split_ands_in_goal; eauto with solve_box_sim. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*           split_ands_in_goal; eauto with solve_box_sim. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*           split_ands_in_goal; eauto with solve_box_sim. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*           split_ands_in_goal; eauto with solve_box_sim. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*           split_ands_in_goal; eauto with solve_box_sim. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*           split_ands_in_goal; eauto with solve_box_sim. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*           split_ands_in_goal; repeat solve_box_sim_analyze_action_correct IHfuel1. *)
(*         + eapply pf_action_writes_regs_only_box_sim_preserved with (3 := Heqp15) (4 := Heqp8); eauto. *)
(*         + eapply pf_action_writes_regs_only_box_sim_preserved with (3 := Heqp15) (4 := Heqp8); eauto. *)
(*         + rewrite Heqb1 in H6. repeat rewrite andb_true_r in *. *)
(*           eapply pf_writes_not_in_box_sim_preserved with (3 := Heqp15) (4 := Heqp8); eauto. *)
(*         + rewrite<-andb_assoc in H6. *)
(*           rewrite andb_comm in Heqb3. rewrite Heqb3 in H6. *)
(*           eapply pf_writes_filter_box_sim_preserved with (3 := Heqp15) (4 := Heqp8); eauto. *)
(*       - destruct_all_matches; repeat solve_box_sim_analyze_action_correct IHfuel1; *)
(*           split_ands_in_goal; eauto with solve_box_sim. *)
(*         rewrite Forall_forall in Hext_sim. *)
(*         rewrite Hext_sim; auto. *)
(*         apply existsb_exists in Heqb0. propositional; simplify; auto. *)
(*     Qed. *)

(*     Definition computable_regs_not_in_boxes (env: SortedRegEnv.EnvT bool) : bool := *)
(*       forallb (fun '(b, def) => *)
(*                  forallb (fun reg => match SortedRegEnv.opt_get env reg with *)
(*                                   | Some true => false *)
(*                                   | _ => true *)
(*                                   end) def) *)
(*         (map (fun '(box, def) => (box, get_box_regs def)) box_defs). *)

(*     Lemma computable_regs_not_in_boxes_correct: *)
(*       forall env, computable_regs_not_in_boxes env = true -> *)
(*         RegsNotInBoxes env (map (fun '(box, def) => (box, get_box_regs def)) box_defs). *)
(*     Proof. *)
(*       intros. consider computable_regs_not_in_boxes. *)
(*       rewrite forallb_forall in *. *)
(*       unfold RegsNotInBoxes in *. *)
(*       intros * Hbox Hreg. *)
(*       specialize H with (1 := Hreg). simpl in H. rewrite forallb_forall in *. *)
(*       intros. specialize H with (1 := H0). simpl_match. discriminate. *)
(*     Qed. *)

(*     Theorem box_sim_analyze_rule_correct: *)
(*       forall sigma1 sigma2 r1 r2 safe1 safe2 action gamma1' gamma2' st1' st2' v1' v2' box_fns ext_fn_sims reg_sims box_sims reg_sims' ext_fn_log1 ext_fn_log1' ext_fn_log2 ext_fn_log2', *)
(*         oraat_interp_action sigma1 int_fns struct_defs (safe_fuel int_fns action) *)
(*           r1 r1 ext_fn_log1 safe1 GenericGammaEmpty action = (true, Some(gamma1', st1', ext_fn_log1', v1')) -> *)
(*         oraat_interp_action sigma2 int_fns struct_defs (safe_fuel int_fns action) *)
(*           r2 r2 ext_fn_log2 safe2 GenericGammaEmpty action = (true, Some(gamma2', st2', ext_fn_log2', v2')) -> *)
(*         reg_sim_state_prop reg_sims r1 r2 -> *)
(*         box_sim_state_prop box_sims r1 r2 -> *)
(*         Forall (fun f => forall v, sigma1 f v = sigma2 f v) ext_fn_sims -> *)
(*         WF_boxes box_defs -> *)
(*         box_fn_preserves_prop box_fns -> *)
(*         RegsNotInBoxes reg_sims (map (fun '(box, def) => (box, get_box_regs def)) box_defs) -> *)
(*         @analyze_rule int_fns box_t box_t_eq_dec *)
(*           (map (fun '(box, def) => (box, get_box_regs def)) box_defs) *)
(*           box_fns ext_fn_sims reg_sims box_sims action = Success (Some (reg_sims')) -> *)
(*         reg_sim_state_prop (sim_regs reg_sims') st1' st2' /\ box_sim_state_prop (sim_boxes reg_sims') st1' st2'. *)
(*     Proof. *)
(*       unfold analyze_rule, res_opt_bind. *)
(*       intros; simplify. *)
(*       eapply box_sim_analyze_action_correct with (1 := H) (2 := H0) in Heqr; propositional; eauto. *)
(*       apply gamma_sim_correct_empty. *)
(*     Qed. *)

(*   End BoxSimAnalysis. *)

(* End BoxSimCorrect. *)
