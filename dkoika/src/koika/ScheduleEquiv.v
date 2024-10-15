(*
Require Import koika.Frontend.
Require Import Lia.
Instance EqDec_struct_t : EqDec (@struct_t N) := _.
Definition struct_beq_in_envs (env1 env2: @struct_env_t N) (sname: N) : bool :=
  match lookup_struct env1 sname tt, lookup_struct env2 sname tt with
  | Success s1,  Success s2 => beq_dec s1 s2
  | Failure tt, Failure tt => false (* could be true *)
  | _, _ => false
  end.

Fixpoint struct_defs_equiv_at_inlined_rule (env1 env2: @struct_env_t N) (rule: @action N) : bool :=
  let struct_defs_equiv_at_rule := struct_defs_equiv_at_inlined_rule env1 env2 in
  match rule with
      | Fail _ => true
      | Var _ => true
      | Const _ => true
      | Assign _ a => struct_defs_equiv_at_rule a
      | Seq a1 a2 => struct_defs_equiv_at_rule a1 && struct_defs_equiv_at_rule a2
      | If a1 a2 a3 =>
          struct_defs_equiv_at_rule a1 && struct_defs_equiv_at_rule a2 && struct_defs_equiv_at_rule a3
      | Bind _ a1 a2 =>
          struct_defs_equiv_at_rule a1 && struct_defs_equiv_at_rule a2
      | Read _ _ => true
      | Write _ _ a => struct_defs_equiv_at_rule a
      | Zop (StructInit sname) => struct_beq_in_envs env1 env2 sname
      | Unop fn a1 =>
          struct_defs_equiv_at_rule a1 &&
            (match fn with
             | Bits1 bs => true
             | Struct1 (GetField sname _) =>
                 struct_beq_in_envs env1 env2 sname
             | Ignore => true
             end)
      | Binop fn2 a1 a2 =>
          struct_defs_equiv_at_rule a1 &&
          struct_defs_equiv_at_rule a2 &&
          match fn2 with
          | Bits2 bs => true
          | Struct2 (SubstField sname _) =>
              struct_beq_in_envs env1 env2 sname
          end
      | InternalCall _ _ => false (* assume inlined *)
      | ExternalCall _ a => struct_defs_equiv_at_rule a
  end.
Fixpoint fn_depth_ok (fuel: nat) (int_fn_env: @int_fn_env_t N (@action N)) (depth: nat) (rule: @action N) : bool :=
  match fuel with
  | 0 => false
  | S fuel =>
      let recurse := fn_depth_ok fuel int_fn_env depth in
      match rule with
          | Fail _ => true
          | Var _ => true
          | Const _ => true
          | Assign _ a => recurse a
          | Seq a1 a2 => recurse a1 && recurse a2
          | If a1 a2 a3 =>
              recurse a1 && recurse a2 && recurse a3
          | Bind _ a1 a2 =>
              recurse a1 && recurse a2
          | Read _ _ => true
          | Write _ _ a => recurse a
          | Zop _ => true
          | Unop _ a1 => recurse a1
          | Binop _ a1 a2 => recurse a1 && recurse a2
          | InternalCall fn a =>
              recurse a && match lookup_int_fn int_fn_env fn tt with
              | Success (id, spec) =>
                  PeanoNat.Nat.ltb id depth &&
                    fn_depth_ok fuel int_fn_env id spec.(fn_body)
              | _ => false
              end
          | ExternalCall _ a => recurse a
          end
  end.
Definition var_in_var_list (v: var_t) (gamma: list var_t) : bool :=
  match find (beq_dec v) gamma with
  | Some _ => true
  | None => false
  end.


Fixpoint gamma_ok (fuel: nat) (int_fns: @int_fn_env_t N (@action N)) (gamma: list var_t) (action: @action N) : bool :=
  match fuel with
  | 0 => false
  | S fuel =>
   let recurse := gamma_ok fuel int_fns gamma in
    match action with
        | Fail _ => true
        | Var v => var_in_var_list v gamma
        | Const _ => true
        | Assign v a => recurse a && var_in_var_list v gamma
        | Seq a1 a2 => recurse a1 && recurse a2
        | If a1 a2 a3 =>
            recurse a1 && recurse a2 && recurse a3
        | Bind v ex body =>
            recurse ex && (gamma_ok fuel int_fns (v::gamma) body)
        | Read _ _ => true
        | Write _ _ a => recurse a
        | Zop _ => true
        | Unop _ a => recurse a
        | Binop fn a1 a2 => recurse a1 && recurse a2
        | ExternalCall _ a => recurse a
        | InternalCall fn a =>
            recurse a &&
              (match lookup_int_fn int_fns fn tt with
               | Success (id, spec) =>
                   gamma_ok fuel int_fns [spec.(fn_arg_name)] spec.(fn_body)
               | _ => false
               end)
        end
  end.

Definition int_fns_gamma_ok (int_fns: int_fn_env_t) : bool :=
  forallb (fun fn => gamma_ok (max_fn_height int_fns * Datatypes.length int_fns) int_fns [fn.(fn_arg_name)] fn.(fn_body)) int_fns .

Definition setoid_rule_equiv
  (int_fns1 int_fns2: @int_fn_env_t N (@action N))
  (struct_env1 struct_env2: @struct_env_t N)
  (rule1 rule2: @action N) : Prop :=
  inline_rule int_fns1 rule1 = inline_rule int_fns2 rule2 /\
  struct_defs_equiv_at_inlined_rule struct_env1 struct_env2 (inline_rule int_fns1 rule1) = true /\
  fn_depth_ok (SyntaxUtils.safe_fuel int_fns1 rule1) int_fns1 (Datatypes.length int_fns1) rule1 = true /\
  fn_depth_ok (SyntaxUtils.safe_fuel int_fns2 rule2) int_fns2 (Datatypes.length int_fns2) rule2 = true /\
  int_fns_gamma_ok int_fns1 = true /\
  int_fns_gamma_ok int_fns2 = true.

Inductive setoid_sched_equiv
                     {rule_name_t1 rule_name_t2: Type}
                     (int_fns1 int_fns2: @int_fn_env_t N (@action N))
                     (struct_env1 struct_env2: @struct_env_t N)
                     (rules1 : rule_name_t1 -> @Syntax.rule N)
                     (rules2 : rule_name_t2 -> @Syntax.rule N) : scheduler -> scheduler -> Prop :=
| SetoidSchedEquivDone :
  setoid_sched_equiv int_fns1 int_fns2 struct_env1 struct_env2 rules1 rules2 Done Done
| SetoidSchedEquivCons : forall rl1 rl2 sched1 sched2,
                     setoid_rule_equiv int_fns1 int_fns2 struct_env1 struct_env2 (rules1 rl1) (rules2 rl2) ->
                     setoid_sched_equiv int_fns1 int_fns2 struct_env1 struct_env2 rules1 rules2 sched1 sched2 ->
                     setoid_sched_equiv int_fns1 int_fns2 struct_env1 struct_env2 rules1 rules2 (Cons rl1 sched1) (Cons rl2 sched2).

Require Import Lia.
Lemma struct_beq_in_envs_impl_interp_zop_eq:
  forall env1 env2 sname,
  struct_beq_in_envs env1 env2 sname = true ->
  interp_zop env1 (StructInit sname) = interp_zop env2 (StructInit sname).
Proof.
  intros. consider struct_beq_in_envs. simpl. unfold __debug__ in *.
  bash_destruct H; simplify. setoid_rewrite Heqr. setoid_rewrite Heqr0.
  reflexivity.
Qed.
Lemma struct_beq_in_envs_impl_interp_unop_eq:
  forall env1 env2 sname f arg,
  struct_beq_in_envs env1 env2 sname = true ->
  interp_unop env1 (Struct1 (GetField sname f)) arg = interp_unop env2 (Struct1 (GetField sname f)) arg.
Proof.
  intros. consider struct_beq_in_envs. simpl. unfold __debug__ in *.
  bash_destruct H; simplify. setoid_rewrite Heqr. setoid_rewrite Heqr0.
  auto.
Qed.
Lemma struct_beq_in_envs_impl_interp_binop_eq:
  forall env1 env2 sname f arg1 arg2,
  struct_beq_in_envs env1 env2 sname = true ->
  interp_binop env1 (Struct2 (SubstField sname f)) arg1 arg2 = interp_binop env2 (Struct2 (SubstField sname f)) arg1 arg2.
Proof.
  intros. consider struct_beq_in_envs. simpl. unfold __debug__ in *.
  bash_destruct H; simplify. setoid_rewrite Heqr. setoid_rewrite Heqr0.
  auto.
Qed.


Ltac step_solve_setoid_equiv IHfuel1 :=
  repeat match goal with
       | _ => progress (repeat simpl_match; propositional)
       (* | H: @eq (@action _) _ _ |- _ => inversion H *)
       (* | H: Action _ _ = Action _ _ |- _ => inversions H *)
       | H: _ && _ = true |- _ => rewrite andb_true_iff in H
       | |- match interp_action _ _ _ _ _ _ _ _ _ _ with | _ => _ end =
            match interp_action _ _ _ _ _ _ _ _ _ _ with | _ => _ end  =>
           let H := fresh in assert_match_eq_as H; [solve[eapply IHfuel1; eauto; nia] | ]; rewrite H; destruct_match
       | |- match ?s with | _ => _ end = match ?s with | _ => _ end => destruct_match
       | |- match interp_zop _ _ with | _ => _ end =
            match interp_zop _ _ with | _ => _ end =>
           let H := fresh in assert_match_eq_as H; [solve[eapply struct_beq_in_envs_impl_interp_zop_eq; auto] | ]; rewrite H; destruct_match
       | |- match interp_unop _ _ _ with | _ => _ end =
            match interp_unop _ _ _ with | _ => _ end =>
           let H := fresh in assert_match_eq_as H; [solve[eapply struct_beq_in_envs_impl_interp_unop_eq; auto] | ]; rewrite H; destruct_match
       | |- match interp_binop _ _ _ _ with | _ => _ end =
            match interp_binop _ _ _ _ with | _ => _ end =>
           let H := fresh in assert_match_eq_as H; [solve[eapply struct_beq_in_envs_impl_interp_binop_eq; auto] | ]; rewrite H; destruct_match
       | |- interp_action _ _ _ _ _ _ _ _ _ _  = interp_action _ _ _ _ _ _ _ _ _ _  =>
           solve[eapply IHfuel1; eauto; nia]
       | f: unit |- _ => destruct f
       | H: fn_arg_name ?x = fn_arg_name ?y |- context[fn_arg_name ?x] =>
           match x with
           | y => fail
           | _ => rewrite H
           end
       | H : lookup_int_fn _ _ _ = _ |- _ =>
           pose_fresh (max_fn_height_correct _ _ _ _ H)
       | H: PeanoNat.Nat.ltb _ _ = true |- _ => rewrite PeanoNat.Nat.ltb_lt in H
       end.
Lemma int_fns_gamma_ok_pick:
  forall int_fns spec n fn,
  int_fns_gamma_ok int_fns = true ->
  lookup_int_fn int_fns fn tt = Success (n, spec) ->
  gamma_ok (max_fn_height int_fns * Datatypes.length int_fns)
    int_fns [fn_arg_name spec] (fn_body spec) = true.
Proof.
  intros * hwf hlookup. consider @lookup_int_fn. consider int_fns_gamma_ok.
  rewrite forallb_forall in hwf. simplify.
  apply find_with_index_Some in Heqo. propositional; simplify.
  apply nth_error_In in Heqo0. eauto.
Qed.
Lemma varenv_update_app:
  forall {B: Type} env1 env2 v (val: B),
  var_in_var_list v (map fst env1) = true ->
  varenv_update (env1 ++ env2)%list v val = (varenv_update env1 v val ++ env2)%list.
Proof.
  consider @var_in_var_list. consider @varenv_update. induction env1; simpl; [discriminate | ].
  destruct_match_pairs; subst. simpl. intros. bash_destruct H; simplify.
  - rewrite eqb_refl. auto.
  - apply eqb_neq in Heqb0. simpl_match. rewrite IHenv1; try simpl_match; auto.
Qed.
Lemma varenv_lookup_append:
  forall {B: Type} (base: @varenv_t B) tail v,
  var_in_var_list v (map fst base) = true ->
  varenv_lookup_var (base ++ tail)%list v tt = varenv_lookup_var base v tt.
Proof.
  induction base; consider var_in_var_list; simpl; [discriminate | ].
  intros. bash_destruct H; simplify; unfold varenv_lookup_var; simpl; destruct_match_pairs; subst; simpl.
  - rewrite eqb_refl. reflexivity.
  - apply eqb_neq in Heqb. simpl in Heqb. simpl_match. apply IHbase. simpl_match. auto.
Qed.
Lemma varenv_bind_keys_eq_tail:
  forall {B: Type} g v0 (v1: B) (g0: @varenv_t B),
  map fst (varenv_bind g v0 v1) = map fst g0 ->
  map fst (tl g0) = map fst g.
Proof.
  intros. consider @varenv_bind. destruct g0; simpl in *; [discriminate | ].
  inversions H. reflexivity.
Qed.

Lemma varenv_update_preserves_keys:
  forall {B: Type} env v (val val0: B),
  varenv_lookup_var env v tt = Success val0 ->
  map fst (varenv_update env v val) = map fst env.
Proof.
  consider @varenv_lookup_var. consider @varenv_update.
  induction env; simpl; [discriminate | ].
  destruct_match_pairs; subst; simpl.
  intros. bash_destruct H; simplify; auto.
  simpl. f_equal. eapply IHenv. simpl_match. eauto.
Qed.

Lemma interp_action_gamma_keys_eq:
  forall fuel sigma int_fns struct_env sched_log action_log fn_depth body st gamma gamma' action_log' v,
  interp_action sigma int_fns struct_env fuel fn_depth st gamma sched_log action_log body = Success (Some (gamma', action_log', v)) ->
  map fst gamma = map fst gamma'.
Proof.
  induction fuel; simpl; auto; [discriminate | ].
  all: destruct body; intros * hinterp.
  all: unfold __debug__ in *; unfold res_opt_bind in *; destruct_all_matches.
  all: repeat match goal with
       | H: interp_action _ _ _ _ _ _ _ _ _ _ = _ |- _ =>
           let H' := fresh in
           pose_fresh_as H' (IHfuel _ _ _ _ _ _ _ _ _ _ _ _ H)
         | H: varenv_lookup_var ?env ?v tt = Success ?val0
           |- context[map fst (varenv_update ?env ?v _)] =>
             rewrite varenv_update_preserves_keys with (1 := H)
       | _ => progress (simplify; propositional; try rewrite_solve)
       end.
  erewrite varenv_bind_keys_eq_tail; eauto.
Qed.

Lemma skipn_app_first:
  forall {T: Type} (ls1 ls2: list T),
  skipn (Datatypes.length ls1) (ls1 ++ ls2) = ls2.
Proof.
  intros. rewrite skipn_app. rewrite skipn_all.
  rewrite PeanoNat.Nat.sub_diag. reflexivity.
Qed.

Ltac solve_typecheck_int_fns_gamma_ok' IHfuel1 :=
  match goal with
        | H : var_in_var_list ?v (map fst ?base) = true
          |- context[varenv_lookup_var (?base ++ _)%list ?v _] =>
            rewrite varenv_lookup_append
        | |- match (match ?s with | _ => _ end) with | _ => _ end =
             match (match ?s with | _ => _ end) with | _ => _ end =>
            destruct s
        | H: gamma_ok _ _ (map fst ?base) ?a = true
          |- match (match interp_action ?_sigma _ ?_struct_env ?_fuel ?_fn_depth ?_st (?base ++ ?_g)%list ?_sched_log ?_action_log ?a with | _ => _ end) with | _ => _ end =
             match (match interp_action _ _ _ _ _ _ ?base _ _ ?a with | _ => _ end) with | _ => _ end =>
            let H' := fresh in
            pose proof IHfuel1 as H';
            specialize H' with (1 := H) (sigma := _sigma) (struct_env := _struct_env)
                               (fuel := _fuel) (sched_log := _sched_log) (action_log := _action_log)
                               (fn_depth := _fn_depth) (st := _st) (g := _g);
            bash_destruct H'
        | H: gamma_ok _ _ (map fst ?base) ?a = true
          |- (match interp_action ?_sigma _ ?_struct_env ?_fuel ?_fn_depth ?_st (?base ++ ?_g)%list ?_sched_log ?_action_log ?a with | _ => _ end)  =
             (match interp_action _ _ _ _ _ _ ?base _ _ ?a with | _ => _ end) =>
            let H' := fresh in
            pose proof IHfuel1 as H';
            specialize H' with (1 := H) (sigma := _sigma) (struct_env := _struct_env)
                               (fuel := _fuel) (sched_log := _sched_log) (action_log := _action_log)
                               (fn_depth := _fn_depth) (st := _st) (g := _g);
            bash_destruct H'
        | |- context[skipn (Datatypes.length ?s) (?s ++ _)%list] =>
            rewrite skipn_app_first
        | H: _ && _ = true |- _ => rewrite andb_true_iff in H
        | H: interp_action _ _ _ _ _ _ _ _ _ _ = _ |- _ =>
            pose_fresh (interp_action_gamma_keys_eq _ _ _ _ _ _ _ _ _ _ _ _ _ H)
        | H : unit |- _ => destruct H
        | H: var_in_var_list _ (map fst ?gbase) = true ,
          H1: map fst ?gbase = map fst ?g1
          |- match (match varenv_lookup_var (?g1 ++ _)%list _ _ with | _ => _ end) with | _ => _ end = _ =>
            rewrite varenv_lookup_append; [ | rewrite<-H1; assumption]
        | |- context[varenv_update (_++ _)%list _ _] =>
            rewrite varenv_update_app by congruence
        | _ => progress (simplify; propositional)
        end.

Lemma typecheck_int_fns_gamma_ok':
  forall fuel1 sigma int_fns struct_env fuel sched_log action_log fn_depth body st g gamma_base,
  gamma_ok fuel1 int_fns (map fst gamma_base) body = true ->
  match
    interp_action sigma int_fns struct_env fuel fn_depth st
      (gamma_base ++ g)%list  sched_log action_log body
  with
  | Success (Some (gamma', action_log0, v_body)) =>
      Success (Some (gamma', action_log0, v_body))
  | Success None => Success None
  | Failure f => Failure f
  end =
  match
    interp_action sigma int_fns struct_env fuel fn_depth st
      (gamma_base)%list sched_log action_log body
  with
  | Success (Some (gamma_base', action_log0, v_body)) => Success (Some ((gamma_base' ++ g)%list, action_log0, v_body))
  | Success None => Success None
  | Failure f => Failure f
  end.
Proof.
  induction fuel1; simpl; [ discriminate | ].
  destruct fuel; simpl; auto.
  intros * hgamma; destruct body;  unfold __debug__, res_opt_bind in *.
  all :   repeat solve_typecheck_int_fns_gamma_ok' IHfuel1.
  all: rewrite H0 in *.
  all :   repeat solve_typecheck_int_fns_gamma_ok' IHfuel1.
  unfold varenv_bind. rewrite app_comm_cons.
  all :   repeat solve_typecheck_int_fns_gamma_ok' IHfuel1.
  replace v with (fst (v,v1)) in hgamma1 by auto.
  rewrite<-map_cons in hgamma1.
  consider var_t.
  repeat solve_typecheck_int_fns_gamma_ok' IHfuel1.
  destruct g2; [ discriminate | ]. auto.
Qed.


Lemma typecheck_int_fns_gamma_ok:
  forall fuel1 sigma int_fns struct_env fuel sched_log action_log fn_depth body st v arg_name g ,
  gamma_ok fuel1 int_fns [arg_name] body = true ->
  match
    interp_action sigma int_fns struct_env fuel fn_depth st
      (varenv_bind g arg_name v) sched_log action_log body
  with
  | Success (Some (gamma', action_log0, v_body)) => Success (Some (tl gamma', action_log0, v_body))
  | Success None => Success None
  | Failure f => Failure f
  end =
  match
    interp_action sigma int_fns struct_env fuel fn_depth st
      ((fn_gamma arg_name v))%list sched_log action_log body
  with
  | Success (Some (_, action_log0, v_body)) => Success (Some (g, action_log0, v_body))
  | Success None => Success None
  | Failure f => Failure f
  end.
Proof.
  intros.
  specialize typecheck_int_fns_gamma_ok' with (sigma := sigma) (int_fns := int_fns)
                                              (struct_env := struct_env) (fuel := fuel)
                                              (sched_log := sched_log) (action_log := action_log)
                                              (fn_depth := fn_depth) (body := body)
                                              (st := st) (fuel1 := fuel1) (g := g) (gamma_base := fn_gamma arg_name v). simpl. propositional. destruct_all_matches; consider @varenv_bind; simplify;
    repeat match goal with
    | H1 : ?x = _, H2: ?x = _ |- _ => rewrite H1 in H2; clear H1
    end; simpl in *; simplify; auto.
  apply interp_action_gamma_keys_eq in Heqr0. destruct g1; simpl in *; [discriminate | ]; simplify.
  inversions Heqr0. destruct g1; simpl in *; [ | discriminate]. reflexivity.
Qed.

Lemma setoid_equiv_implies_action_eq:
  forall fuel1 fuel2 rl1 rl2 sigma int_fns1 int_fns2 struct_env1 struct_env2 st sched_log action_log gamma fn_depth1 fn_depth2,
  inline_action int_fns1 (fuel1) rl1 = inline_action int_fns2 (fuel2) rl2 ->
  struct_defs_equiv_at_inlined_rule struct_env1 struct_env2
    (inline_action int_fns1 fuel1 rl1) = true ->
  fuel1 >= (max_fn_height int_fns1 * fn_depth1 ) + height (rl1) ->
  fuel2 >= (max_fn_height int_fns2 * fn_depth2 ) + height rl2 ->
  fn_depth_ok fuel1 int_fns1 fn_depth1 rl1 = true ->
  fn_depth_ok fuel2 int_fns2 fn_depth2 rl2 = true ->
  int_fns_gamma_ok int_fns1 = true ->
  int_fns_gamma_ok int_fns2 = true ->
  interp_action sigma int_fns1 struct_env1 fuel1
          fn_depth1 st gamma sched_log action_log rl1 =
  interp_action sigma int_fns2 struct_env2 fuel2
          fn_depth2 st gamma sched_log action_log rl2.
Proof.
  consider @safe_fuel.
  induction fuel1 ; [destruct rl1; simpl; lia | ].
  destruct fuel2; [ destruct rl2; simpl; lia | ].
  destruct rl1;
    intros * hinline hdefs_equiv hfuel1 hfuel2 hdepth1 hdepth2 hgamma1 hgamma2; simpl in *;
    destruct rl2;  simpl in *; destruct_all_matches_in_hyps; unfold res_opt_bind;
    unfold __debug__, SortedExtFnEnv.EqDec_KeyT,OrderedN.EqDec_T;
    unfold OrderedN.T in *.
  (* all : step_solve_setoid_equiv IHfuel1; unfold OrderedN.T in *. *)
  (* - erewrite<-typecheck_int_fns_gamma_ok; unfold OrderedN.T in *; [ step_solve_setoid_equiv IHfuel1 | ]. *)
  (*   eapply int_fns_gamma_ok_pick; eauto. *)
  (* - erewrite<-typecheck_int_fns_gamma_ok; unfold OrderedN.T in *; [ step_solve_setoid_equiv IHfuel1 | ]. *)
  (*   eapply int_fns_gamma_ok_pick; eauto. *)
  (* - step_solve_setoid_equiv IHfuel1. *)

Lemma setoid_equiv_implies_rule_eq:
  forall sigma int_fns1 int_fns2 struct_env1 struct_env2 st rl1 rl2 log0,
 setoid_rule_equiv int_fns1 int_fns2 struct_env1 struct_env2 rl1 rl2  ->
 interp_rule sigma int_fns1 struct_env1 st log0 (rl1)  = interp_rule sigma int_fns2 struct_env2 st log0 (rl2).
Proof.
  consider interp_rule. consider setoid_rule_equiv. consider @inline_rule.
  intros * hsetoid ; propositional.
  specialize setoid_equiv_implies_action_eq with (1 := hsetoid0) (2 := hsetoid2). intros.
  assert_match_eq; [eauto | ].
  rewrite H0; auto.
Qed.

Lemma interp_scheduler_setoid_eq:
  forall {rule_name_t1 rule_name_t2: Type} sched1 sched2 sigma int_fns1 int_fns2 struct_env1 struct_env2 st
    (rules1: rule_name_t1 -> Syntax.rule) (rules2: rule_name_t2 -> Syntax.rule) log,
  setoid_sched_equiv int_fns1 int_fns2 struct_env1 struct_env2 rules1 rules2 sched1 sched2 ->
  interp_scheduler' sigma int_fns1 struct_env1 st rules1 sched1 log =
  interp_scheduler' sigma int_fns2 struct_env2 st rules2 sched2 log.
Proof.
  intros * hequiv. generalize log. induction hequiv; auto. intros. simpl.
  erewrite setoid_equiv_implies_rule_eq with (1 := H) (struct_env2 := struct_env2) . repeat destruct_match; eauto.
Qed.
Ltac fast_solve_sched_equiv :=
  match goal with
  | |- setoid_sched_equiv _ _ _ _ _ _ (done) (done) =>
      constructor
  | |- _ =>
    constructor; [ constructor; [vm_compute; reflexivity | ]; split_ands_in_goal; vm_compute; reflexivity| ]
  end.
*)
