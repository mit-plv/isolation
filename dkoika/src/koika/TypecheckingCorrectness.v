Require Import koika.Common.
Require Import koika.Utils.
Require Import koika.Syntax.
Require Import koika.Semantics.
Require Import koika.Environments.
Require Import koika.Typechecking.
Require Import koika.Tactics.
Require Import koika.SyntaxMacros.
Require Import koika.SemanticUtils.
Require Import koika.StaticAnalysis.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.PeanoNat.
Require Import koika.SyntaxUtils.
Section Typechecking.
    Ltac solve_typecheck_action_correct:=
      repeat match goal with
      | _ => progress simplify_result
      | _ => progress option_simpl
     (* | H: is_some (?gamma ?var2) |- is_some (gamma_set ?gamma ?var1 _ ?var2) => *)
     (*    apply is_some_gamma_set; assumption *)
      | H : String.eqb _ _ = true|- _ =>
        apply String.eqb_eq in H; subst
      | H : String.eqb _ _ = false|- _ =>
        apply String.eqb_neq in H; subst
      | H : Nat.eqb _ _ = true |- _ =>
        apply PeanoNat.Nat.eqb_eq in H; subst
      | |- context[varenv_lookup_var (varenv_update ?gamma ?var _) ?var _] =>
        rewrite varenv_update_var_eq
      | |- context[varenv_lookup_var (varenv_bind ?gamma ?var _) ?var _] =>
        rewrite varenv_bind_var_eq
      | H: ?var' <> ?var
        |- context[varenv_lookup_var (varenv_update ?gamma ?var' _) ?var _] =>
        rewrite varenv_update_var_neq
      | H: ?var' <> ?var
        |- context[varenv_lookup_var (varenv_bind ?gamma ?var' _) ?var _] =>
        rewrite varenv_bind_var_neq
      | H : ?idx' <> ?idx
       |- context[log_set _ ?idx' _ ?idx] =>
        rewrite log_set_neq
      | |- context[log_set ?log ?idx _ ?idx] =>
        rewrite log_set_eq
      | H: varenv_lookup_var (varenv_bind _ ?var _) ?var _ = _ |- _ =>
        rewrite varenv_bind_var_eq in H
      | |- _ => progress propositional
      | |- _ => progress simpl_match
      | |- _ => auto
      end.

    Ltac destruct_one_interp_action :=
        match goal with
        | [  |- context[interp_action] ] =>
          destruct interp_action as [[((?, ?), ?) | ] | ]; simpl; auto
        end.

    Lemma typecheck_zop_correct:
      forall struct_defs fn n,
      typecheck_fn0 struct_defs fn = Success n ->
      match interp_zop struct_defs fn with
      | Success result => List.length result = n
      | Failure _ => False
      end.
    Proof.
      unfold typecheck_fn0, interp_zop; intros.
      destruct_match.
      simplify_result. unfold __debug__ in *. simpl_match.
      unfold Bits.zeroes.
      rewrite firstn_fill_length. auto.
    Qed.

    Lemma typecheck_struct1_correct:
      forall struct_defs fn arg n,
      typecheck_struct1 struct_defs fn (Datatypes.length arg) = Success n ->
      match interp_struct1 struct_defs fn arg with
      | Success result => Datatypes.length result = n
      | Failure _ => False
      end.
    Proof.
      unfold typecheck_struct1, interp_struct1. destruct fn. propositional.
      simplify_result. unfold __debug__ in *. simpl_match. unfold get_field, struct_sz in *.
      unfold SyntaxMacros.element_offset, SyntaxMacros.get_field_width in *.
      simplify_result. repeat simpl_match.
      destruct_match_pairs. simplify_result.
      apply find_with_index_Some_eq in Heqo. propositional.
      repeat simpl_match.
      unfold Bits.slice.
      rewrite firstn_fill_length. reflexivity.
    Qed.

    Lemma typecheck_struct2_correct:
      forall struct_defs fn arg1 arg2 n,
      typecheck_struct2 struct_defs fn (Datatypes.length arg1) (Datatypes.length arg2) = Success n ->
      match interp_struct2 struct_defs fn arg1 arg2 with
      | Success result => Datatypes.length result = n
      | Failure _ => False
      end.
    Proof.
      unfold typecheck_struct2, interp_struct2, subst_field, dstruct_fields. destruct fn. propositional.
      simplify_result. unfold __debug__ in *. simpl_match.
      unfold SyntaxMacros.element_offset, SyntaxMacros.get_field_width in *.
      simplify_result. repeat simpl_match.
      destruct_match_pairs. simplify_result. consider @SyntaxMacros.struct_sz; simpl in *.
      unfold OrderedN.T in *.  simpl_match.
      apply find_with_index_Some_eq in Heqo. propositional. repeat simpl_match.
      unfold Bits.slice_subst.
      repeat rewrite app_length.
      rewrite firstn_length.
      rewrite PeanoNat.Nat.eqb_eq in Heqb0, Heqb. subst.
      remember (list_sum _) as offset in *.
      apply find_with_index_Some in Heqo0. propositional. simplify.

      remember (list_sum _) as offset in *.
      consider @SyntaxMacros.struct_sz'.
      assert (offset <= Datatypes.length arg1).
      { subst. rewrite Heqb. rewrite map_firstn.
        apply list_sum_firstn_le.
      }
      rewrite skipn_length.
      assert (Datatypes.length arg1 >= offset + Datatypes.length arg2).
      { apply map_nth_error with (f := snd) in Heqo1.
        apply list_sum_nth_error_ge in Heqo1. subst.
        rewrite map_firstn. simpl in *.
        rewrite Heqb. auto.
      }
      assert ( Datatypes.length arg1 =
                offset
              + Datatypes.length arg2
              + (Datatypes.length arg1 - (offset + Datatypes.length arg2))).
      { lia. }
      rewrite<-Heqb.
      lia.
    Qed.


    Lemma typecheck_unop_correct:
      forall struct_defs fn arg n,
        typecheck_fn1 struct_defs fn (Datatypes.length arg) = Success n ->
        match interp_unop struct_defs fn arg with
        | Success result => List.length result = n
        | Failure f => False
        end.
    Proof.
      intros * Htypecheck.
      destruct fn; simpl in *. destruct fn; simpl in *; simplify_result.
      - consider Bits.neg. rewrite map_length. reflexivity.
      - consider Bits.slice. rewrite firstn_fill_length. reflexivity.
      - consider Bits.extend_end. unfold Bits.vect_const.
        rewrite app_length. rewrite firstn_fill_length.
        destruct_with_eqn (Nat.leb width (Datatypes.length arg)).
        + rewrite Nat.leb_le in Heqb. lia.
        + rewrite Nat.leb_nle in Heqb. lia.
      - consider Bits.extend_end. unfold Bits.vect_const.
        rewrite app_length. rewrite firstn_fill_length.
        destruct_with_eqn (Nat.leb width (Datatypes.length arg)).
        + rewrite Nat.leb_le in Heqb. lia.
        + rewrite Nat.leb_nle in Heqb. lia.
      - apply typecheck_struct1_correct. auto.
      - simplify. reflexivity.
    Qed.

    Lemma typecheck_binop_correct:
      forall struct_defs fn arg1 arg2 n,
        typecheck_fn2 struct_defs fn (Datatypes.length arg1) (Datatypes.length arg2) = Success n ->
        match interp_binop struct_defs fn arg1 arg2 with
        | Success result => List.length result = n
        | Failure f => False
        end.
    Proof.
      intros * Htypecheck.
      destruct fn; simpl in *. destruct fn; simpl in *; simplify_result.
      - unfold Bits.and. solve_typecheck_action_correct.
        apply map2_success with (f := andb) in Heqb.
        destruct_match; solve_typecheck_action_correct.
        apply map2_length in Heqr. propositional.
      - unfold Bits.or. solve_typecheck_action_correct.
        apply map2_success with (f := orb) in Heqb.
        destruct_match; solve_typecheck_action_correct.
        apply map2_length in Heqr. propositional.
      - unfold Bits.xor. solve_typecheck_action_correct.
        apply map2_success with (f := xorb) in Heqb.
        destruct_match; solve_typecheck_action_correct.
        apply map2_length in Heqr. propositional.
      - rewrite Bits.lsl_length. reflexivity.
      - rewrite Bits.lsr_length. reflexivity.
      - rewrite Bits.asr_length. reflexivity.
      - unfold Bits.concat. rewrite app_length.
        rewrite PeanoNat.Nat.add_comm. reflexivity.
      - unfold Bits.sel. apply andb_true_iff in Heqb. solve_typecheck_action_correct.
        unfold opt_result.
        destruct_match; auto.
        apply PeanoNat.Nat.ltb_lt in Heqb.
        destruct_match; auto.
        apply nth_error_None in Heqo. lia.
      - unfold Bits.plus. rewrite Heqb.
        apply firstn_fill_length.
      - unfold Bits.minus. unfold Bits.plus. unfold Bits.neg.
        rewrite map_length. rewrite Heqb. rewrite firstn_fill_length.
        unfold Bits.one. rewrite firstn_fill_length.
        rewrite PeanoNat.Nat.eqb_refl. rewrite firstn_fill_length. auto.
      - destruct_match; auto.
      - unfold Bits.bitfun_of_predicate.
        unfold Bits.signed_lt, Bits.signed_gt, Bits.signed_le, Bits.signed_ge,
        Bits.unsigned_le, Bits.unsigned_lt, Bits.unsigned_gt, Bits.unsigned_ge.
        rewrite Heqb. unfold Bits.lift_comparison. repeat destruct_match; auto.
      - simplify. unfold Bits.slice. rewrite firstn_fill_length. reflexivity.
      - apply typecheck_struct2_correct. auto.
    Qed.

    Ltac typecheck_IH_helper IH NewIH action :=
        match goal with
        | [  H: typecheck' _ _ _ _ _ _ action = Success _
             |- context[interp_action ?_ext_sigma ?_int_fn_env ?_struct_defs ?_fuel ?_fn_depth ?_st ?_gamma ?_sched_log
                                     ?_action_log action] ] =>
          pose proof IH as NewIH;
          specialize NewIH with (10 := H) (gamma := _gamma) (action_log := _action_log) (* (sched_log := _sched_log) *)
                             (ext_sigma := _ext_sigma) (* (int_fn_env := _int_fn_env) (struct_env := _struct_defs) *)
                             (st := _st)
                             (fuel := _fuel) (fn_depth := _fn_depth); propositional;
          try (let Htmp := fresh in
          assert_pre_as Htmp NewIH; [ lia | ]; propositional; clear Htmp;
          destruct_one_interp_action; propositional)
        end.


    Lemma typecheck_int_fns'_Success:
      forall (reg_types: @reg_types_t N) ext_fn_types int_fn_env struct_env fn fn_spec {A} (msg: A) fn_id int_fns',
        typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env = Success int_fns' ->
        lookup_int_fn int_fn_env fn msg = Success (fn_id, fn_spec) ->
        exists fn', nth_error int_fns' fn_id = Some fn' /\
        typecheck' reg_types ext_fn_types int_fn_env struct_env fn_id
                   (fn_var_types fn_spec.(fn_arg_name) fn_spec.(fn_arg_ty))
                   fn_spec.(fn_body) = Success (fn'.(fn_body), fn_spec.(fn_ret_ty)).
    Proof.
      intros * Htype Hlookup.
Set Printing All.
      apply lookup_int_fn_Success in Hlookup; propositional.
      consider @typecheck_int_fns'.
      specialize @result_list_map_success_nth with (1 := Htype).
      intros Hresult.
      apply nth_error_mapi with (f := fun i v => (i,v)) in Hlookup0.
      specialize Hresult with (1 := Hlookup0). propositional. simplify_result.
      f_equal. bash_destruct Hresult2; simplify.
      eexists. split; eauto.
    Qed.

    Lemma WF_fn_arg_gamma:
      forall arg_name arg_ty arg,
        Datatypes.length arg = arg_ty ->
        WF_gamma (fn_var_types arg_name arg_ty) (fn_gamma arg_name arg).
    Proof.
      unfold WF_gamma, fn_var_types, fn_gamma.
      intros. constructor; auto.
    Qed.

    (* Lemma WF_args_gamma: *)
    (*   forall fn_arg_tys fn_gamma typed_list, *)
    (*     Forall2 (fun (name : var_t) (v : var_t * list bool) => fst v = name) (map fst fn_arg_tys) fn_gamma -> *)
    (*     list_beq nat Nat.eqb typed_list (map snd (fn_arg_tys)) = true -> *)
    (*     Forall2 (fun ty v => Datatypes.length (snd v) = ty) typed_list fn_gamma -> *)
    (*     WF_gamma (lookup_arg_ty fn_arg_tys) (lookup_var_from_list fn_gamma). *)
    (* Proof. *)
    (*   consider WF_gamma. induction fn_arg_tys; propositional; simpl; auto. *)
    (*   simpl in *. destruct_match; auto. *)
    (*   consider @lookup_arg_ty. consider @lookup_var_from_list. bash_destruct Heqo; option_simpl; subst. *)
    (*   destruct fn_gamma; [ inversion H | ]. *)
    (*   destruct typed_list; [ inversion H1 | ]. simpl. *)
    (*   destruct_match_pairs. simpl in *. apply andb_true_iff in H0. propositional. *)
    (*   apply Nat.eqb_eq in H2. subst. *)
    (*   inversions H. inversions H1. simpl in *; subst. *)
    (*   bash_destruct Heqo0; option_simpl; simplify_tupless; subst. *)
    (*   + apply String.eqb_eq in Heqb. subst. destruct_match; auto. simpl in *. *)
    (*     rewrite String.eqb_refl in Heqb. discriminate. *)
    (*   + simpl. rewrite eqb_sym. simpl_match. *)
    (*     specialize IHfn_arg_tys with (fn_gamma := fn_gamma) (typed_list := typed_list) (var := var). propositional. *)
    (*     repeat simpl_match. auto. *)
    (* Qed. *)


    Ltac typecheck'_simplify_first_match IH E :=
      match E with
      | varenv_lookup_var ?gamma ?var ?_msg =>
        match goal with
        | H1: WF_gamma ?var_types ?gamma,
              H2: varenv_lookup_var ?var_types ?var _ = Success _
          |- _ =>
          specialize WF_gamma_lookup_var with (msg := _msg) (1 := H1) (2 := H2); propositional; simpl_match
        end
      | interp_action _ _ _ _ _ _ _ _ _ ?action =>
        let IHaction' := fresh "IHaction" in
        typecheck_IH_helper IH IHaction' action
      end.

    Ltac typecheck_t IH :=
      match goal with
      | |- _ =>
        let inner := get_innermost_match_in_goal in
        typecheck'_simplify_first_match IH inner
      | H1: WF_gamma ?var_types ?gamma,
        H2: varenv_lookup_var ?gamma ?var ?msg = Success ?v,
        H3: Datatypes.length ?v = Datatypes.length ?v'
        |- WF_gamma ?var_types (varenv_update ?gamma ?var ?v') =>
        solve[eapply WF_gamma_update; eauto]
      end.


    (* Section Args. *)
    (*   Context (IH: forall fuel (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) (int_fn_env: int_fn_env_t) *)
    (*                  (ext_sigma: ext_sigma_t) (struct_env: struct_env_t) *)
    (*                  (st: state_t) (sched_log: log_t) (max_fn_id: nat) (fn_depth: nat) *)
    (*                  action (var_types: var_types_t) *)
    (*                  (action_log: log_t) (gamma: gamma_t) (n: nat), *)
    (*               WF_state reg_types st -> *)
    (*               WF_log reg_types sched_log -> *)
    (*               WF_log reg_types action_log -> *)
    (*               WF_gamma var_types gamma -> *)
    (*               WF_ext_sigma ext_fn_types ext_sigma -> *)
    (*               WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env -> *)
    (*               fn_depth >= max_fn_id -> *)
    (*               fuel >= ((max_fn_height int_fn_env) * fn_depth) + height action -> *)
    (*               typecheck' reg_types ext_fn_types int_fn_env struct_env max_fn_id var_types action = Success n -> *)
    (*               match interp_action ext_sigma int_fn_env struct_env  *)
    (*                                   fuel fn_depth st gamma sched_log action_log action with *)
    (*               | Success (Some (gamma', log, value)) => *)
    (*                 WF_log reg_types log /\ WF_gamma var_types gamma' /\ List.length value = n *)
    (*               | Success None => True *)
    (*               | _ => False *)
    (*               end). *)

    (*   Lemma interp_args_typecheck_correct: *)
    (*     forall fuel args reg_types var_types ext_sigma ext_fn_types (int_fn_env: int_fn_env_t) max_fn_id fn_depth *)
    (*       (st: state_t) gamma sched_log action_log arg_types (fn_arg_names: list var_t), *)
    (*       WF_state reg_types st -> *)
    (*       WF_log reg_types sched_log -> *)
    (*       WF_log reg_types action_log -> *)
    (*       WF_gamma var_types gamma -> *)
    (*       WF_ext_sigma ext_fn_types ext_sigma -> *)
    (*       WF_int_fn_env reg_types ext_fn_types int_fn_env -> *)
    (*       fn_depth >= max_fn_id -> *)
    (*       fuel >= ((max_fn_height int_fn_env) * fn_depth) + (fold_left max (map height args) 0) -> *)
    (*       List.length arg_types = List.length fn_arg_names -> *)
    (*       result_list_map (typecheck' reg_types ext_fn_types int_fn_env max_fn_id var_types) args *)
    (*         = Success arg_types -> *)
    (*       match interp_args (interp_action ext_sigma int_fn_env fuel fn_depth) *)
    (*                         st gamma sched_log action_log fn_arg_names args with *)
    (*       | Success (Some (gamma', log, v_args)) => *)
    (*         WF_log reg_types log *)
    (*         /\ WF_gamma var_types gamma' *)
    (*         /\ Forall2 (fun ty v => List.length (snd v) = ty) arg_types v_args *)
    (*         /\ Forall2 (fun name v => fst v = name) fn_arg_names v_args *)
    (*       | Success None => True *)
    (*       | _ => False *)
    (*       end. *)
    (*   Proof. *)
    (*     intro fuel. *)
    (*     induction args; *)
    (*       intros * Hstate Hsched Haction Hgamma Hext_sigma Hint_fn_env Hmax_fn Hwf_max_interp Hwf_params Htype; *)
    (*       simpl in *; simplify_result. *)
    (*     - destruct fn_arg_names; [ | simpl in Hwf_params; lia]. simpl; eauto. *)
    (*     - destruct fn_arg_names; [ simpl in Hwf_params; lia | ]. simpl. *)
    (*       simpl in Hwf_params. inversions Hwf_params. *)
    (*       match goal with *)
    (*       | H: result_list_map (typecheck' _ _ _ _ _) ?_args = Success _ *)
    (*         |- context[interp_args (interp_action ?_ext_sigma ?_int_fn_env ?_fuel ?_fn_depth) *)
    (*                               ?_st ?_gamma ?_sched_log ?_action_log ?_fn_names ?_args] => *)
    (*         specialize IHargs with *)
    (*             (10 := H) (ext_sigma := _ext_sigma) (int_fn_env:= _int_fn_env) (st := _st) *)
    (*              (gamma := _gamma) (sched_log := _sched_log) (action_log := _action_log) *)
    (*              (fn_depth := _fn_depth) (fn_arg_names := _fn_names) *)
    (*       end; propositional. *)
    (*       assert_pre_as Hfoo IHargs; propositional. *)
    (*       { pose proof (max_base_order (map height args) (height a) 0). *)
    (*         assert_pre H. { lia. } propositional. lia. *)
    (*       } *)
    (*       destruct interp_args as [[((?, ?), ?) | ] | ]; propositional; cbn. *)
    (*       typecheck_t IH. *)
    (*       assert_pre_as Hfoo' IHaction; propositional. *)
    (*       { pose proof (max_gt_min (map height args) (height a)). lia. } *)
    (*       destruct_one_interp_action. *)
    (*       propositional. *)
    (*   Defined. *)
    (* End Args. *)
    Lemma WF_ext_log_update:
      forall (tys: ext_fn_types_t) (log: ext_log_t) (fn: ext_fn_t) (v: Bits.vect_t) ret_ty,
      lookup_ext_fn tys fn = Some (Datatypes.length v, ret_ty) ->
      WF_ext_log tys log ->
      WF_ext_log tys (ext_log_update log fn v).
    Proof.
      intros * Hlookup Hwf.
      consider WF_ext_log.
      intros * hupdate. consider ext_log_update.
      destruct_with_eqn (beq_dec fn fn0); simplify.
      - rewrite SortedExtFnEnv.update_correct_eq in hupdate. simplify. bash_destruct hupdate; simplify; eauto.
      - rewrite SortedExtFnEnv.update_correct_neq in hupdate by auto.
        eauto.
    Qed.

    Theorem typecheck_action_correct:
      forall fuel (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) (int_fn_env: int_fn_env_t)
        (struct_env: struct_env_t)
        (ext_sigma: ext_sigma_t)
        (st: state_t) (sched_log: Log_t) (max_fn_id: nat) (fn_depth: nat)
        action (var_types: var_types_t)
        (action_log: Log_t) (gamma: gamma_t) action' (n: nat),
        WF_state reg_types st ->
        WF_ext_log ext_fn_types sched_log.(Log__ext) ->
        WF_ext_log ext_fn_types action_log.(Log__ext) ->
        WF_log reg_types sched_log.(Log__koika) ->
        WF_log reg_types action_log.(Log__koika) ->
        WF_gamma var_types gamma ->
        WF_ext_sigma ext_fn_types ext_sigma ->
        WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
        fn_depth >= max_fn_id ->
        fuel >= ((max_fn_height int_fn_env) * fn_depth) + height action ->
        typecheck' reg_types ext_fn_types int_fn_env struct_env max_fn_id var_types action = Success (action', n) ->
        is_success (typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env) = true ->
        match interp_action ext_sigma int_fn_env struct_env fuel fn_depth st gamma sched_log action_log action with
        | Success (Some (gamma', log, value)) =>
          WF_log reg_types log.(Log__koika) /\
          WF_ext_log ext_fn_types (Log__ext log) /\
            WF_gamma var_types gamma' /\ List.length value = n
                                                              (* TODO: and keys Eq *)
        | Success None => True
        | _ => False
        end.
    Proof.
      unfold interp_rule.
      (* consider WF_gamma. (* consider WF_ext_log. *) consider WF_log. consider WF_state. consider WF_int_fn_env. *)
      fix IHfuel 1. destruct fuel.
      + intros; destruct action; simpl height in *; try lia.
      + destruct action; simpl;
        intros * Hstate Hsched_ext haction_ext Hsched Haction Hgamma Hext_sigma Hint_fn_env Hmax_fn Hwf_max_interp Htype Hfn_type;
          simpl in Hwf_max_interp; cbn; unfold __debug__ in *;
          specialize IHfuel with (12 := Hfn_type).
        all: specialize IHfuel with (2 := Hsched_ext).
        all: consider @lookup_var_type; solve_typecheck_action_correct; simplify.
        - typecheck_t IHfuel. split_ands_in_goal; auto.
        - typecheck_t IHfuel.
          typecheck_t IHfuel.
          split_ands_in_goal; auto.
          typecheck_t IHfuel.
        - typecheck_t IHfuel.
          typecheck_t IHfuel.
        - typecheck_t IHfuel.
          destruct (case_singleton_bv v); auto; subst.
          * typecheck_t IHfuel.
          * typecheck_t IHfuel.
        - typecheck_t IHfuel.
          typecheck_t IHfuel.
          assert_pre IHaction.
          { unfold WF_gamma; intros.
            constructor; auto.
          }
          { propositional.
            assert_pre_as Htmp IHaction; [ lia | ]; propositional; clear Htmp.
            destruct_one_interp_action; propositional; solve_typecheck_action_correct.
            split_ands_in_goal; auto.
            consider WF_gamma.
            unfold varenv_bind in *. inversions IHaction4; simpl.
            destruct_match_pairs; propositional.
          }
        - consider @lookup_reg_type. solve_typecheck_action_correct.
          pose proof Hsched idx as Hsched__idx.
          pose proof Hstate idx as Hstate__idx.
          pose proof Haction idx as Haction__idx.
          rewrite Heqo in *. solve_typecheck_action_correct.
          unfold r_get_reg. unfold get_reg in *.
          solve_typecheck_action_correct.
          destruct_match.
          * destruct_match; subst; auto.
            split_ands_in_goal; eauto.
            eapply WF_log_set; eauto.
          * destruct_match; auto.
            destruct_match; auto.
            { split_ands_in_goal; eauto.
              { eapply WF_log_set; eauto; consider WF_LE; solve_typecheck_action_correct. }
              { consider WF_LE; solve_typecheck_action_correct. }
            }
            { destruct_match; auto.
              { split_ands_in_goal; subst; eauto.
                { eapply WF_log_set; eauto; consider WF_LE; solve_typecheck_action_correct. }
                { consider WF_LE; solve_typecheck_action_correct. }
              }
              { split_ands_in_goal; auto.
                eapply WF_log_set; eauto; consider WF_LE; solve_typecheck_action_correct.
              }
            }
        - consider @lookup_reg_type. solve_typecheck_action_correct.
          pose proof Hsched idx as Hsched__idx.
          pose proof Hstate idx as Hstate__idx.
          pose proof Haction idx as Haction__idx.
          rewrite Heqo in *. solve_typecheck_action_correct.
          unfold r_get_reg. repeat simpl_match.
          solve_typecheck_action_correct.
          destruct port.
          * typecheck_t IHfuel.
            pose proof IHaction0 idx. simpl_match.
            solve_typecheck_action_correct.
            destruct_match; auto.
            split_ands_in_goal; auto.
            eapply WF_log_set; eauto; consider WF_LE; solve_typecheck_action_correct.
          * typecheck_t IHfuel.
            pose proof IHaction0 idx. simpl_match.
            solve_typecheck_action_correct.
            destruct_match; auto.
            split_ands_in_goal; auto.
            eapply WF_log_set; eauto; consider WF_LE; solve_typecheck_action_correct.
        - apply typecheck_zop_correct in Heqr. solve_typecheck_action_correct.
        - typecheck_t IHfuel.
          apply typecheck_unop_correct in Heqr0. solve_typecheck_action_correct.
        - typecheck_t IHfuel.
          typecheck_t IHfuel.
          apply typecheck_binop_correct in Heqr1. solve_typecheck_action_correct.
        - destruct_match_pairs. solve_typecheck_action_correct.
          (* Show. *)
          (* simpl_match. unfold __debug__ in *. simpl_match. *)
          (* apply PeanoNat.Nat.ltb_lt in Heqb. *)
          destruct fn_depth ; [ lia | ].
          destruct_match.
          2: { apply PeanoNat.Nat.leb_gt in Heqb0. lia. }
          typecheck_t IHfuel.
          consider @is_success. simplify.
          specialize typecheck_int_fns'_Success with (1 := Heqr1) (2 := Heqr0); intros Htype_fn.
          propositional. unfold OrderedN.T in *.
          typecheck_t IHfuel.
          assert_pre_as Htmp IHaction.
          { apply WF_fn_arg_gamma; auto. }
          propositional; clear Htmp.
          assert_pre_as Htmp IHaction.
          { apply PeanoNat.Nat.leb_le in Heqb0.
            assert (max_fn_height int_fn_env * fn_depth >= max_fn_height int_fn_env * n1).
            { apply PeanoNat.Nat.mul_le_mono_l. lia. }
            assert (max_fn_height int_fn_env >= height (fn_body i)).
            { eapply max_fn_height_correct; eauto. }
            lia.
          }
          propositional; clear Htmp.
          destruct_one_interp_action; propositional.
          (* destruct_match_pairs. solve_typecheck_action_correct. *)
           (* simpl_match. unfold __debug__ in *. simpl_match. *)

          (* match goal with *)
          (* | H: result_list_map (typecheck' _ _ _ _ _) ?_args = Success _ *)
          (*   |- context[interp_args (interp_action ?_ext_sigma ?_int_fn_env ?_fuel ?_fn_depth) *)
          (*                         ?_st ?_gamma ?_sched_log ?_action_log ?_fn_names ?_args] => *)
          (*   specialize (interp_args_typecheck_correct IHfuel _fuel) *)
          (*   with (10 := H) (ext_sigma := _ext_sigma) (int_fn_env:= _int_fn_env) (st := _st) *)
          (*        (gamma := _gamma) (sched_log := _sched_log) (action_log := _action_log) *)
          (*        (fn_depth := _fn_depth) (fn_arg_names := _fn_names); intros Hargs *)
          (* end; propositional. *)
          (* assert_pre_as Htmp Hargs; [ lia | ]; propositional; clear Htmp. *)
          (* assert_pre Hargs. *)
          (* { apply list_beq_length in Heqb0. rewrite map_length in Heqb0. rewrite map_length; auto. } *)
          (* propositional. *)
          (* destruct interp_args as [[((?, ?), ?) | ] | ]; propositional; cbn; auto. *)
          (* apply Nat.ltb_lt in Heqb. *)
          (* destruct fn_depth ; [ lia | ]. *)
          (* destruct_match; [ | apply Nat.leb_nle in Heqb1; lia ]. *)
          (* specialize typecheck_int_fns'_Success with (1 := Hint_fn_env) (2 := Heqr0); intros Htype_fn. *)
          (* typecheck_t IHfuel. *)
          (* assert_pre_as Htmp IHaction. *)
          (* { eapply WF_args_gamma; eauto. } *)
          (* propositional. clear Htmp. *)
          (* assert_pre_as Htmp IHaction. *)
          (* { move Hwf_max_interp at bottom. *)
          (*   apply Nat.leb_le in Heqb1. *)
          (*   assert (max_fn_height int_fn_env * fn_depth >= max_fn_height int_fn_env * n0). *)
          (*   { apply mult_le_compat_l. lia. } *)
          (*   assert (max_fn_height int_fn_env >= height (fn_body i)). *)
          (*   { eapply max_fn_height_correct; eauto. } *)
          (*   lia. *)
          (* } *)
          (* propositional; clear Htmp. *)
          (* destruct_one_interp_action; propositional. *)
        - typecheck_t IHfuel.
          unfold lookup_ext_fn_type in Heqr0.
          destruct_match_pairs. solve_typecheck_action_correct.
          consider WF_ext_sigma. specialize Hext_sigma with (fn := fn).
          unfold OrderedN.T in *.
          unfold AnnotatedSyntax.ext_fn_t in *.
          unfold ext_fn_t in *.
          simpl_match.
          specialize Hext_sigma with (arg := v). propositional.
          solve_typecheck_action_correct.
          destruct_match; auto; simpl.
          split_ands_in_goal; auto.
          eapply WF_ext_log_update; eauto.
      Qed.

    Lemma WF_gamma_empty :
      WF_gamma [] [].
    Proof.
      constructor; auto.
    Qed.

    Lemma typecheck_rule_correct:
      forall (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) (int_fn_env: int_fn_env_t)
        (struct_env: struct_env_t)
        (ext_sigma: ext_sigma_t)
        (st: state_t) (sched_log: Log_t) action rule' ,
        WF_state reg_types st ->
        WF_ext_log ext_fn_types sched_log.(Log__ext) ->
        WF_log reg_types sched_log.(Log__koika) ->
        WF_ext_sigma ext_fn_types ext_sigma ->
        WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
        typecheck_rule reg_types ext_fn_types int_fn_env struct_env action = Success (rule', 0) ->
        is_success (typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env) = true ->
        match interp_rule ext_sigma int_fn_env struct_env st sched_log action with
        | Success (Some log) => WF_log reg_types log.(Log__koika) /\
                               WF_ext_log ext_fn_types log.(Log__ext)
        | Success None => True
        | _ => False
        end.
    Proof.
      intros * Hstate Hext_log Hlog Hext Hfn_env Htype Htype_fns.
      unfold interp_rule.
      specialize typecheck_action_correct with
          (action_log := Log_empty)
          (1 := Hstate) (3 := WF_ext_log__empty _ )
          (4 := Hlog) (5 := WF_log_GenericLogEmpty _)
          (6 := WF_gamma_empty) (7 := Hext) (8 := Hfn_env) (11 := Htype) (12 := Htype_fns)
          (fuel := (safe_fuel int_fn_env action))
          (fn_depth := Datatypes.length int_fn_env). unfold GenericGammaEmpty. consider Log_empty.
      intros Haction. unfold OrderedN.T in *. bash_destruct Haction; simpl; auto.
      split; apply Haction; auto.
    Qed.

    Lemma typecheck_schedule_correct'_log:
      forall {rule_name_t: Type} (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) (int_fn_env: int_fn_env_t)
        (struct_env: struct_env_t)
        (ext_sigma: ext_sigma_t)
        (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t) (sched_log: Log_t) ,
        typecheck_schedule reg_types ext_fn_types int_fn_env struct_env s rls= Success tt ->
        WF_state reg_types st ->
        WF_ext_log ext_fn_types (Log__ext sched_log) ->
        WF_log reg_types sched_log.(Log__koika) ->
        WF_ext_sigma ext_fn_types ext_sigma ->
        WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
        is_success (typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env) = true ->
        match interp_scheduler' ext_sigma int_fn_env struct_env
                                st rls s sched_log with
        | Success s => WF_log reg_types s.(Log__koika) /\
                      WF_ext_log ext_fn_types s.(Log__ext)
        | _ => False
        end.
    Proof.
      induction s.
      - intros * Htype Hstate Hext_log Hlog Hext Hfn_env Htype_fns. simpl interp_scheduler'. simpl.
        split; auto.
        (* consider WF_state. consider WF_log. intros *. *)
        (* specialize Hstate with (reg := reg). *)
        (* specialize Hlog with (reg := reg). unfold latest_write. *)
        (* repeat destruct_match; propositional; unfold is_some; eauto. *)
      - intros * Htype Hstate Hext_log Hlog Hext Hfn_env Htype_fns. simpl.
        simpl in Htype.
        destruct_matches_in_hyp Htype.
        + specialize typecheck_rule_correct with
              (1 := Hstate) (action := rls r) (sched_log := sched_log) (2 := Hext_log)
              (4 := Hext) (5 := Hfn_env) (7 := Htype_fns).
          rewrite Heqr0. simpl. propositional.
          destruct_match_pairs; simplify. specialize H with (2 := eq_refl). propositional.
          simplify.
          destruct_match; simplify; propositional.
          * eapply IHs; eauto.
            { apply WF_ext_log_app; auto. }
            { apply WF_log_app; eauto. }
          * eapply IHs; eauto.
        + simpl in Htype. discriminate.
    Qed.

    Corollary typecheck_schedule_correct'_WF_log:
      forall {rule_name_t: Type} (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) (int_fn_env: int_fn_env_t)
        (struct_env: struct_env_t)
        (ext_sigma: ext_sigma_t)
        (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t) (sched_log: Log_t) log int_fns',
        typecheck_schedule reg_types ext_fn_types int_fn_env struct_env s rls = Success tt ->
        typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env = Success int_fns' ->
        WF_state reg_types st ->
        WF_ext_log ext_fn_types sched_log.(Log__ext) ->
        WF_log reg_types sched_log.(Log__koika) ->
        WF_ext_sigma ext_fn_types ext_sigma ->
        WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
        interp_scheduler' ext_sigma int_fn_env struct_env
                                st rls s sched_log = Success log ->
        WF_log reg_types log.(Log__koika) /\
        WF_ext_log ext_fn_types log.(Log__ext).
    Proof.
      intros.
      eapply typecheck_schedule_correct'_log in H; eauto.
      simplify; auto.
    Qed.

    Lemma typecheck_schedule_correct':
      forall {rule_name_t: Type} (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) (int_fn_env: int_fn_env_t)
        (struct_env: struct_env_t)
        (ext_sigma: ext_sigma_t)
        (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t) (sched_log: Log_t) ,
        typecheck_schedule reg_types ext_fn_types int_fn_env struct_env s rls = Success tt ->
        is_success (typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env) = true ->
        WF_state reg_types st ->
        WF_log reg_types sched_log.(Log__koika) ->
        WF_ext_log ext_fn_types sched_log.(Log__ext) ->
        WF_ext_sigma ext_fn_types ext_sigma ->
        WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
        match interp_scheduler' ext_sigma int_fn_env struct_env
                                st rls s sched_log with
        | Success log => WF_state reg_types (commit_update st log.(Log__koika)) /\
                        WF_ext_log ext_fn_types log.(Log__ext)
        | _ => False
        end.
    Proof.
      intros * Htype Hfns Hstate Hlog Hext_log Hext Hfn_env.
      specialize @typecheck_schedule_correct'_log with
          (1 := Htype) (2 := Hstate) (3 := Hext_log) (4 := Hlog) (5 := Hext) (6 := Hfn_env) (7 := Hfns).
      intros Hlog'. simplify_result. unfold commit_update, WF_state in *.
      destruct Hlog' as (Hlog' & Hlog__ext).
      split.
      - intros reg.
        consider WF_log.
        specialize Hstate with (reg := reg).
        specialize Hlog' with (reg := reg).
        bash_destruct Hstate; auto.
        unfold get_reg in *.
        rewrite SortedRegEnv.opt_get_map.
        repeat simpl_match.
        consider log_get.
        bash_destruct Hlog'.
        + consider WF_LE. consider latest_write.
          bash_destruct Hlog'; propositional; auto.
        + simpl. auto.
     - auto.
    Qed.

    Lemma typecheck_schedule_correct:
      forall {rule_name_t: Type} (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) (int_fn_env: int_fn_env_t)
        (struct_env: struct_env_t)
        (ext_sigma: ext_sigma_t)
        (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t) ,
        is_success (typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env) = true ->
        typecheck_schedule reg_types ext_fn_types int_fn_env struct_env s rls = Success tt ->
        WF_state reg_types st ->
        WF_ext_sigma ext_fn_types ext_sigma ->
        WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
        match interp_cycle ext_sigma int_fn_env struct_env st rls s with
        | Success st' => WF_state reg_types st'
        | _ => False
        end.
    Proof.
      unfold interp_cycle. unfold interp_scheduler.
      intros.
      eapply typecheck_schedule_correct' with (sched_log := Log_empty) in H; eauto with WF_auto; simplify; propositional; simpl.
    Qed.

    Section TypecheckWeaken.
      Definition reg_types_subset (r1 r2: reg_types_t) : Prop :=
        forall reg ty, Environments.lookup_reg_type r1 reg = Some ty ->
                  Environments.lookup_reg_type r2 reg = Some ty.

      Lemma reg_types_subset_refl:
        forall r, reg_types_subset r r.
      Proof.
        unfold reg_types_subset; auto.
      Qed.

      Definition ext_fn_types_subset (tys1 tys2: ext_fn_types_t) : Prop :=
        forall fn ty, Environments.lookup_ext_fn tys1 fn = Some ty ->
                 Environments.lookup_ext_fn tys2 fn = Some ty.

      Lemma ext_fn_types_subset_refl:
        forall r, ext_fn_types_subset r r.
      Proof.
        unfold ext_fn_types_subset; auto.
      Qed.


      Definition struct_env_subset (tys1 tys2: struct_env_t) : Prop :=
        forall sname v, find (fun s => beq_dec sname s.(dstruct_name)) tys1 = Some v ->
                   find (fun s => beq_dec sname s.(dstruct_name)) tys2 = Some v.

      Lemma struct_env_subset_refl:
        forall r, struct_env_subset r r.
      Proof.
        unfold struct_env_subset; auto.
      Qed.

      (* Definition gamma_subset (gamma1 gamma2: var_types_t) : Prop := *)
      (*   forall var ty, gamma1 var = Some ty -> *)
      (*             gamma2 var = Some ty. *)

      (* Lemma gamma_subset_refl: forall gamma, gamma_subset gamma gamma. *)
      (* Proof. intros; unfold gamma_subset; auto. Qed. *)

      Definition int_fn_subset (fns1 fns2: @int_fn_env_t N (@action N)) (max_id: nat): Prop :=
        forall fn i v,
          find_with_index (fun f => (fn =? fn_name f)%N) fns1 = Some (i, v) ->
          i < max_id ->
          find_with_index (fun f => (fn =? fn_name f)%N) fns2 = Some (i, v).

      Lemma int_fn_subset_refl (fns: int_fn_env_t):
        forall id, int_fn_subset fns fns id.
      Proof.
        unfold int_fn_subset; intros; auto.
      Qed.

      Lemma int_fn_subset_length':
        forall n idx_base xs1 xs2,
          (forall i, i < n -> nth_error xs1 i = nth_error xs2 i) ->
          n < List.length xs1 ->
          forall (fn: N) (i : nat) (v : int_fn_spec_t),
            find_with_index' (fun f : (@int_fn_spec_t N (@action N))=> (fn =? fn_name f)%N) xs1 idx_base = Some (i, v) ->
            i < (n + idx_base) ->
            find_with_index' (fun f : int_fn_spec_t => (fn =? fn_name f)%N) xs2 idx_base = Some (i, v).
      Proof.
        induction n; propositional; auto.
        - apply find_with_index'_Some in H1. propositional; lia.
        - destruct xs1; try simpl in *; try lia.
          destruct xs2; simpl in *; try lia.
          + specialize H with ( i := 0). assert_pre_and_specialize  H; [ lia | ].
            simpl in *; discriminate.
          + pose proof (H 0). simpl in *. assert_pre_and_specialize H3; [ lia | ].
            option_simpl; subst. destruct_match; auto.
            eapply IHn with (3 := H1); eauto; try lia.
            intros. specialize H with (i := S i0). simpl in *. apply H. lia.
      Qed.

      Lemma int_fn_subset_length:
        forall n xs1 xs2,
          (forall i, i < n -> nth_error xs1 i = nth_error xs2 i) ->
          n < List.length xs1 ->
          int_fn_subset xs1 xs2 n.
      Proof.
        unfold int_fn_subset, find_with_index.
        intros.
        eapply int_fn_subset_length'; eauto. lia.
      Qed.

      Ltac typecheck_weaken_simplify_first_match IH E :=
        match E with
        | typecheck' ?_reg_types ?ext_fn_types ?_int_fn_env2 ?struct_env ?_max_id2 ?_gamma2 ?action =>
          match goal with
          | H: typecheck' _ _ ?int_fn_env1 _ ?max_id1 ?gamma1 ?action = _ |- _ =>
            specialize IH with (max_id2 := _max_id2) (gamma2 := _gamma2)
                               (7 := H);
            propositional; repeat simpl_match
          end
        end.


      Ltac typecheck_weaken_t IH :=
        match goal with
        | |- _ =>
          let inner := get_innermost_match_in_goal in
          typecheck_weaken_simplify_first_match IH inner
        | |- _ => progress (propositional; repeat simpl_match)
        end.

      Lemma typecheck_weaken_zop:
        forall struct_env1 struct_env2 fn s,
          struct_env_subset struct_env1 struct_env2 ->
          typecheck_fn0 struct_env1 fn = Success s ->
          typecheck_fn0 struct_env2 fn = Success s.
      Proof.
        intros * Hsubset Htype.
        destruct fn; simpl in *; unfold __debug__ in *.
        simplify_result. consider @lookup_struct.
        simplify_result.
        consider struct_env_subset.
        erewrite Hsubset; auto.
      Qed.

      Lemma typecheck_weaken_unop:
        forall struct_env1 struct_env2 fn ty s,
          struct_env_subset struct_env1 struct_env2 ->
          typecheck_fn1 struct_env1 fn ty = Success s ->
          typecheck_fn1 struct_env2 fn ty = Success s.
      Proof.
        intros * Hsubset Htype.
        destruct fn; simpl in *; unfold __debug__ in *; auto.
        destruct fn; simpl in *; unfold __debug__ in *; auto.
        simplify_result. consider @lookup_struct.
        simplify_result.
        consider struct_env_subset.
        erewrite Hsubset; eauto.
        repeat simpl_match. reflexivity.
      Qed.

      Lemma typecheck_weaken_binop:
        forall struct_env1 struct_env2 fn ty1 ty2 s,
          struct_env_subset struct_env1 struct_env2 ->
          typecheck_fn2 struct_env1 fn ty1 ty2 = Success s ->
          typecheck_fn2 struct_env2 fn ty1 ty2 = Success s.
      Proof.
        intros * Hsubset Htype.
        destruct fn; simpl in *; unfold __debug__ in *; auto.
        destruct fn; simpl in *; unfold __debug__ in *; auto.
        simplify_result. consider @lookup_struct.
        simplify_result.
        consider struct_env_subset.
        erewrite Hsubset; eauto.
        repeat simpl_match. reflexivity.
      Qed.

      Create HintDb typecheck_weaken_db.
      Hint Immediate reg_types_subset_refl: typecheck_weaken_db.
      Hint Immediate ext_fn_types_subset_refl: typecheck_weaken_db.
      Hint Immediate struct_env_subset_refl: typecheck_weaken_db.
      (* Hint Immediate gamma_subset_refl : typecheck_weaken_db. *)
      Hint Immediate int_fn_subset_refl : typecheck_weaken_db.

      (* Lemma typecheck_weaken: *)
      (*   forall reg_types1 reg_types2 ext_fn_types1 ext_fn_types2 *)
      (*     int_fn_env1 int_fn_env2 struct_env1 struct_env2 *)
      (*     action max_id1 max_id2 gamma1 gamma2 s, *)
      (*     reg_types_subset reg_types1 reg_types2 -> *)
      (*     ext_fn_types_subset ext_fn_types1 ext_fn_types2 -> *)
      (*     struct_env_subset struct_env1 struct_env2 -> *)
      (*     gamma_subset gamma1 gamma2 -> *)
      (*     max_id1 <= max_id2 -> *)
      (*     int_fn_subset int_fn_env1 int_fn_env2 max_id1 -> *)
      (*     typecheck' reg_types1 ext_fn_types1 int_fn_env1 struct_env1 max_id1 gamma1 action = Success s -> *)
      (*     typecheck' reg_types2 ext_fn_types2 int_fn_env2 struct_env2 max_id2 gamma2 action = Success s. *)
      (* Proof. *)
      (*   Transparent __debug__. *)
      (*   induction action; simpl; unfold __debug__; auto; *)
      (*     intros max_id1 max_id2 gamma1 gamma2 s *)
      (*            Hreg_tys Hext_fn_tys Hstruct_env Hgamma Hmax_id Hint_fn. *)
      (*   all: unfold lookup_var_type. *)
      (*   - intros; simplify_result. erewrite Hgamma; eauto. *)
      (*   - intros; simplify_result. erewrite Hgamma; eauto. *)
      (*     typecheck_weaken_t IHaction. auto. *)
      (*   - intros; simplify_result. *)
      (*     typecheck_weaken_t IHaction1. auto. *)
      (*     eapply IHaction2; eauto. *)
      (*   - intros; simplify_result. *)
      (*     typecheck_weaken_t IHaction1. *)
      (*     typecheck_weaken_t IHaction2. *)
      (*     typecheck_weaken_t IHaction3. *)
      (*     auto. *)
      (*   - intros; simplify_result. *)
      (*     typecheck_weaken_t IHaction1. *)
      (*     eapply IHaction2; eauto. *)
      (*     unfold gamma_subset. intros; destruct_match; auto. *)
      (*   - unfold lookup_reg_type. intros; simplify_result. *)
      (*     erewrite Hreg_tys; eauto. *)
      (*   - unfold lookup_reg_type; intros; simplify_result. *)
      (*     erewrite Hreg_tys; eauto. *)
      (*     typecheck_weaken_t IHaction. reflexivity. *)
      (*   - apply typecheck_weaken_zop. assumption. *)
      (*   - intros; simplify_result. *)
      (*     typecheck_weaken_t IHaction. *)
      (*     eapply typecheck_weaken_unop; eauto. *)
      (*   - intros; simplify_result. *)
      (*     typecheck_weaken_t IHaction1. *)
      (*     typecheck_weaken_t IHaction2. *)
      (*     eapply typecheck_weaken_binop; eauto. *)
      (*   - intros; simplify_result; destruct_match_pairs; simplify_result. *)
      (*     typecheck_weaken_t IHaction. *)
      (*     unfold lookup_int_fn in *. *)
      (*     simplify_result. *)
      (*     rewrite Nat.ltb_lt in *. *)
      (*     consider int_fn_subset. *)
      (*     erewrite Hint_fn; eauto. *)
      (*     simpl_match. *)
      (*     destruct_match; auto. *)
      (*     rewrite Nat.ltb_nlt in *. *)
      (*     lia. *)
      (*   - unfold lookup_ext_fn_type. *)
      (*     intros; simplify_result; destruct_match_pairs; simplify_result. *)
      (*     typecheck_weaken_t IHaction. *)
      (*     erewrite Hext_fn_tys; eauto. simpl; simpl_match. reflexivity. *)
      (* Qed. *)

      Lemma nth_error_mapi'_helper:
        forall {T} ls n idx_base v idx,
          nth_error (mapi' idx_base (fun (i : nat) (v : T) => (i, v)) ls) n = Some (idx, v) ->
          In v ls /\ idx = n + idx_base.
      Proof.
        induction ls.
        - intros; simpl in *; auto. destruct n; simpl in *; discriminate.
        - intros; simpl in *. destruct n; simpl in *; option_simpl; simplify_tupless.
          + split; auto.
          + specialize IHls with (1 := H). propositional.
      Qed.


     (*  Lemma typecheck_int_fns_implies: *)
     (*    forall (int_fn_env: int_fn_env_t) *)
     (*      (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) *)
     (*      (struct_env: struct_env_t), *)
     (*      (forall fn, In fn int_fn_env -> *)
     (*            reg_types_subset fn.(fn_reg_tys) reg_types /\ *)
     (*            ext_fn_types_subset fn.(fn_ext_fn_tys) ext_fn_types /\ *)
     (*            struct_env_subset fn.(fn_struct_defs) struct_env) -> *)
     (*      is_success (typecheck_int_fns int_fn_env) = true -> *)
     (*      is_success (typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env) = true. *)
     (*  Proof. *)
     (*    unfold typecheck_int_fns, typecheck_int_fns'. unfold mapi. *)
     (*    induction int_fn_env using rev_ind; auto. *)
     (*    intros * Hsubset Htypecheck. simplify_result. simpl in Heqr. simplify_result. *)
     (*    rewrite mapi'_app in *. simpl in *. *)
     (*    rewrite result_list_map_app in *. simpl in *. simplify_result. *)
     (*    unfold __debug__ in *. *)

     (*    pose proof (Hsubset x) as Hsubset_x. *)
     (*    assert_pre_and_specialize Hsubset_x; [ apply in_or_app; right; constructor; reflexivity | ]. *)
     (*    propositional. *)
     (*    specialize typecheck_weaken with *)
     (*        (1 := Hsubset_x0) (2 := Hsubset_x2) (3 := Hsubset_x3) (6 := int_fn_subset_refl _ _) (7 := Heqr1) *)
     (*        (4 := gamma_subset_refl _) (5 := Nat.le_refl _). *)
     (*    intros Htype2. repeat simpl_match. *)
     (*    specialize IHint_fn_env with (reg_types := reg_types) (ext_fn_types := ext_fn_types) *)
     (*                                 (struct_env := struct_env). *)
     (*    assert_pre_as Hsubset' IHint_fn_env. *)
     (*    { intros; apply Hsubset. apply in_or_app. auto. } propositional. *)

     (*    assert_pre_and_specialize IHint_fn_env. *)
     (*    { erewrite result_list_map_feq; [erewrite Heqr0; eauto | ]. *)
     (*      intros * HIn. destruct_match_pairs. *)
     (*      apply In_nth_error in HIn. propositional. *)
     (*      specialize @result_list_map_success_nth with (1 := Heqr0) (2 := HIn0). *)
     (*      propositional. simplify_result. *)
     (*      eapply typecheck_weaken in Heqr. *)
     (*      { erewrite Heqr. simpl_match; auto. } *)
     (*      all: eauto with typecheck_weaken_db. *)

     (*      assert (n < Datatypes.length (int_fn_env)) as Hlength. *)
     (*      { apply nth_error_Some. *)
     (*        specialize @nth_error_mapi'_Some with (1 := HIn0). *)
     (*        intros. *)
     (*        destruct_with_eqn (nth_error int_fn_env n0); option_simpl; auto. *)
     (*        specialize @nth_error_mapi' with (1 := Heqo). *)
     (*        intros. rewrite H0 in HIn0. option_simpl; simplify_tupless. *)
     (*        Nat.nzsimpl. rewrite Heqo. auto. *)
     (*      } *)
     (*      apply int_fn_subset_length; auto. *)
     (*      { intros. *)
     (*        rewrite nth_error_app1; auto. lia. *)
     (*      } *)
     (*      { rewrite app_length. simpl. lia. } *)
     (*    } *)
     (*    simplify_result. *)
     (*    erewrite result_list_map_feq; [erewrite Heqr; eauto | ]. *)
     (*    intros * HIn. destruct_match_pairs; subst. *)

     (*    apply In_nth_error in HIn. propositional. *)
     (*    assert (In i int_fn_env) as HIn'. *)
     (*    { eapply nth_error_mapi'_helper; eauto. } *)

     (*    specialize @result_list_map_success_nth with (1 := Heqr0) (2 := HIn0). *)
     (*    propositional. simplify_result. *)
     (*    specialize Hsubset' with (1 := HIn'); propositional. *)
     (*    assert (n < Datatypes.length (int_fn_env)) as Hlength. *)
     (*    { apply nth_error_Some. *)
     (*      specialize @nth_error_mapi'_Some with (1 := HIn0). *)
     (*      intros. *)
     (*      destruct_with_eqn (nth_error int_fn_env n0); option_simpl; auto. *)
     (*      specialize @nth_error_mapi' with (1 := Heqo). *)
     (*      intros. rewrite H0 in HIn0. option_simpl; simplify_tupless. *)
     (*      Nat.nzsimpl. rewrite Heqo. auto. *)
     (*    } *)

     (*    eapply typecheck_weaken in Heqr2. *)
     (*    { erewrite Heqr2. simpl_match; auto. *)
     (*      eapply typecheck_weaken in Heqr2. *)
     (*      { erewrite Heqr2; simpl_match; eauto. } *)
     (*      all: eauto with typecheck_weaken_db. *)
     (*      apply int_fn_subset_length; auto. *)
     (*      { intros. rewrite nth_error_app1; auto. lia. *)
     (*      } *)
     (*      { rewrite app_length. simpl. lia. } *)
     (*    } *)
     (*    all: auto with typecheck_weaken_db; try lia. *)
     (* Qed. *)


     (* Lemma typecheck_int_fns_implies': *)
     (*   forall (int_fn_env: int_fn_env_t) *)
     (*     (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) *)
     (*     (struct_env: struct_env_t), *)
     (*     (forall fn, In fn int_fn_env -> *)
     (*           reg_types_subset fn.(fn_reg_tys) reg_types /\ *)
     (*           ext_fn_types_subset fn.(fn_ext_fn_tys) ext_fn_types /\ *)
     (*           struct_env_subset fn.(fn_struct_defs) struct_env) -> *)
     (*     (typecheck_int_fns int_fn_env) = Success tt -> *)
     (*     (typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env) = Success tt. *)
     (* Proof. *)
     (*   intros. apply typecheck_int_fns_implies in H; unfold is_success in *; simplify_result; auto. *)
     (*   - bash_destruct H. destruct s; auto. *)
     (*   - simpl_match. auto. *)
     (* Qed. *)

    End TypecheckWeaken.

End Typechecking.

Section UnsafeSemantics.
    Ltac simplify_res_opt_bind :=
      match goal with
      | H: res_opt_bind (interp_action _ _ _ _ _ _ _ _ _ _) _ = Success _ |- _ =>
        let H1 := fresh H in
        destruct interp_action eqn:H1; [ | simpl in H; discriminate]
      | H: context[res_opt_bind (Success _) _]|- _ =>
        simpl in H
      end.

    Theorem unsafe_interp_action_correct':
      forall fuel (int_fn_env: int_fn_env_t)
        (struct_env: struct_env_t)
        (ext_sigma: ext_sigma_t)
        (st: state_t) (sched_log: Log_t)  (fn_depth: nat)
        action
        (action_log: Log_t) (gamma: gamma_t) res,
        interp_action ext_sigma int_fn_env struct_env fuel fn_depth st gamma sched_log action_log action = Success res ->
        res = unsafe_interp_action ext_sigma int_fn_env struct_env fuel st gamma sched_log action_log action.
    Proof.
      induction fuel; cbn; [discriminate |].
      intros * Hinterp.
      destruct action; simpl in *; simplify; try simplify_res_opt_bind;
        unfold unsafe_read1, __debug__, unsafe_r_get_reg,
               unsafe_varenv_lookup_var, unsafe_interp_zop, unsafe_interp_binop, unsafe_interp_unop,
               unsafe_get_fn_arg_and_body,
               unsafe_call_ext in *.
      all : repeat match goal with
                  | _ => progress (simpl; subst)
                  | H: interp_action _ _ _ _ _ _ _ _ _ _ = Success _ |- _ =>
                    eapply IHfuel in H; eauto
                  | _ => simplify_res_opt_bind
                  | _ => progress simplify
                  | [  |- context[match ?x with _ => _ end] ] => destruct x eqn:?
                  | _ => reflexivity || assumption
                  end.
      - rewrite<-Heqo. reflexivity.
      - rewrite<-Heqo. reflexivity.
      - rewrite<-Heqo. reflexivity.
    Qed.

    Theorem unsafe_interp_action_correct:
      forall fuel (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) (int_fn_env: int_fn_env_t)
        (struct_env: struct_env_t)
        (ext_sigma: ext_sigma_t)
        (st: state_t) (sched_log: Log_t) (max_fn_id: nat) (fn_depth: nat)
        action (var_types: var_types_t)
        (action_log: Log_t) (gamma: gamma_t) (n: nat) action',
        WF_state reg_types st ->
        WF_ext_log ext_fn_types sched_log.(Log__ext) ->
        WF_ext_log ext_fn_types (Log__ext action_log) ->
        WF_log reg_types sched_log.(Log__koika) ->
        WF_log reg_types action_log.(Log__koika) ->
        WF_gamma var_types gamma ->
        WF_ext_sigma ext_fn_types ext_sigma ->
        WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
        fn_depth >= max_fn_id ->
        fuel >= ((max_fn_height int_fn_env) * fn_depth) + height action ->
        is_success (typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env) = true ->
        typecheck' reg_types ext_fn_types int_fn_env struct_env max_fn_id var_types action = Success (action', n) ->
        interp_action ext_sigma int_fn_env struct_env fuel fn_depth st gamma sched_log action_log action
         = Success (unsafe_interp_action ext_sigma int_fn_env struct_env fuel st gamma sched_log action_log action).
    Proof.
      intros * Hstate Hsched_ext_log Haction_ext_log Hsched Haction Hgamma Hext_sigma Hint_fn_env Hmax_fn Hwf_max_interp Hfns_type Htype.
      consider @is_success. simplify.
      pose proof Htype as Htype'.
      eapply typecheck_action_correct with (sched_log := sched_log) (action_log := action_log) in Htype; eauto.
      simplify.
      eapply unsafe_interp_action_correct' in Heqr0; subst; eauto.
    Qed.
    Hint Resolve WF_gamma_empty : WF_auto.

    Theorem unsafe_interp_rule_correct:
      forall (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) (int_fn_env: int_fn_env_t)
        (struct_env: struct_env_t)
        (ext_sigma: ext_sigma_t)
        (st: state_t) (sched_log: Log_t)
        action rule',
        WF_state reg_types st ->
        WF_ext_log ext_fn_types sched_log.(Log__ext) ->
        WF_log reg_types sched_log.(Log__koika) ->
        WF_ext_sigma ext_fn_types ext_sigma ->
        WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
        typecheck_rule reg_types ext_fn_types int_fn_env struct_env action = Success (rule', 0) ->
        interp_rule ext_sigma int_fn_env struct_env st sched_log action =
          Success (unsafe_interp_rule ext_sigma int_fn_env struct_env st sched_log action).
    Proof.
      intros * Hstate Hsched_ext Hsched Hext_sigma Hint_fn_env Htype.
      pose proof Htype as Htype'.
      eapply typecheck_rule_correct in Htype; eauto. simplify.
      consider interp_rule. simplify.
      erewrite unsafe_interp_action_correct in Heqr0; eauto with WF_auto.
      simplify. consider unsafe_interp_rule. consider Log_empty.
      destruct_match; destruct_match_pairs; simplify; auto. destruct l0; reflexivity.
    Qed.

    Lemma unsafe_interp_scheduler'_correct:
      forall {rule_name_t: Type} (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) (int_fn_env: int_fn_env_t)
        (struct_env: struct_env_t)
        (ext_sigma: ext_sigma_t)
        (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t) (sched_log: Log_t),
        WF_state reg_types st ->
        WF_ext_log ext_fn_types sched_log.(Log__ext) ->
        WF_log reg_types sched_log.(Log__koika) ->
        WF_ext_sigma ext_fn_types ext_sigma ->
        WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
        typecheck_schedule reg_types ext_fn_types int_fn_env struct_env s rls = Success tt ->
        interp_scheduler' ext_sigma int_fn_env struct_env st rls s sched_log =
          Success (unsafe_interp_scheduler' ext_sigma int_fn_env struct_env
                                            st rls s sched_log).
    Proof.
      induction s; simpl; auto.
      intros * Hstate Hext_log Hlog Hext_sigma Hint_fn_env Htype. simplify.
      pose proof Heqr0 as Htype_rule.
      eapply typecheck_rule_correct in Htype_rule; eauto. simplify.
      erewrite unsafe_interp_rule_correct in *; eauto; simplify.
      destruct_match; auto.
      apply IHs; eauto.
      - apply WF_ext_log_app; propositional.
      - apply WF_log_app; propositional.
    Qed.

    (* Lemma unsafe_interp_cycle_correct: *)
    (*   forall {rule_name_t: Type} (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) (int_fn_env: int_fn_env_t) *)
    (*     (struct_env: struct_env_t) *)
    (*     (ext_sigma: ext_sigma_t) *)
    (*     (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t) (sched_log: Log_t), *)
    (*     WF_state reg_types st -> *)
    (*     WF_log reg_types sched_log -> *)
    (*     WF_ext_sigma ext_fn_types ext_sigma -> *)
    (*     WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env -> *)
    (*     typecheck_schedule reg_types ext_fn_types int_fn_env struct_env s rls = Success tt -> *)
    (*     interp_cycle ext_sigma int_fn_env struct_env st rls s = *)
    (*       Success (unsafe_interp_cycle ext_sigma int_fn_env struct_env st rls s). *)
    (* Proof. *)
    (*   intros * Hst Hlog Hext_sigma Hint_fn_env Htype. *)
    (*   unfold unsafe_interp_cycle, unsafe_interp_scheduler, interp_cycle, interp_scheduler. *)
    (*   erewrite unsafe_interp_scheduler'_correct; eauto with WF_auto. *)
    (* Qed. *)

End UnsafeSemantics.

Section ORAAT.

    Definition le_to_taint (le: LogEntry) : taint_t :=
      {| taint_read0 := le.(lread0);
         taint_read1 := le.(lread1);
         taint_write0 := is_someb le.(lwrite0);
         taint_write1 := is_someb le.(lwrite1)
      |}.

    Record taint_le (t1 t2: taint_t) : Prop :=
      { tle_read0 : t1.(taint_read0) = true -> t2.(taint_read0) = true;
        tle_read1 : t1.(taint_read1) = true -> t2.(taint_read1) = true;
        tle_write0 : t1.(taint_write0) = true -> t2.(taint_write0) = true;
        tle_write1 : t1.(taint_write1) = true -> t2.(taint_write1) = true;
      }.

    Definition taint_approximates_log_entry (taint: taint_t) (le: LogEntry) : Prop :=
      taint_le (le_to_taint le) taint.

    Definition taint_env_approximates_log (taint_env: taint_env_t) (log: log_t) : Prop :=
      forall reg, taint_approximates_log_entry (get_reg_taint_default taint_env reg)
                                          (log_get log reg).

    Definition taint_env_le (taint_env1 taint_env2: taint_env_t) : Prop :=
      forall reg, taint_le (get_reg_taint_default taint_env1 reg) (get_reg_taint_default taint_env2 reg).

    Lemma taint_le_generalize_taint:
      forall taint1 taint2 le,
        taint_le taint1 taint2 ->
        taint_approximates_log_entry taint1 le ->
        taint_approximates_log_entry taint2 le.
    Proof.
      intros * Htaint Hle.
      consider taint_approximates_log_entry. destruct Hle.
      destruct Htaint.
      constructor; propositional.
    Qed.

    Lemma taint_env_approximates_log_generalize_taint:
      forall taint_env taint_env' log,
        taint_env_le taint_env taint_env' ->
        taint_env_approximates_log taint_env log ->
        taint_env_approximates_log taint_env' log.
    Proof.
      intros * Hle Happrox.
      unfold taint_env_approximates_log, taint_env_le in *.
      intros reg. specialize Hle with (reg := reg). specialize Happrox with (reg := reg).
      eapply taint_le_generalize_taint; eauto.
    Qed.

    Ltac simplify_res_opt_bind :=
      match goal with
      | H: res_opt_bind (interp_action _ _ _ _ _ _ _ _ _ _) _ = Success _ |- _ =>
        let H1 := fresh H in
        destruct interp_action eqn:H1; [ | simpl in H; discriminate]
      | H: context[res_opt_bind (Success _) _]|- _ =>
        simpl in H
      | H: res_opt_bind ?x _ = Success (Some _) |- _ =>
        let H1 := fresh H in
        destruct x as [ [ | ]| ] eqn:H1; simpl in H; [ | discriminate | discriminate]
      end.
    Lemma taint_le_refl:
      forall t, taint_le t t.
    Proof.
      intros. constructor; auto.
    Qed.

    Lemma taint_env_le_refl:
      forall t, taint_env_le t t.
    Proof.
      intros. unfold taint_env_le. intros.
      unfold get_reg_taint_default.
      destruct_match; apply taint_le_refl.
    Qed.

    Lemma taint_le_trans:
      forall t0 t1 t2,
        taint_le t0 t1 ->
        taint_le t1 t2 ->
        taint_le t0 t2.
    Proof.
      intros * Ht1 Ht2.
      destruct Ht1. destruct Ht2.
      constructor; propositional.
    Qed.

    Lemma taint_env_le_trans:
      forall env0 env1 env2,
        taint_env_le env0 env1 ->
        taint_env_le env1 env2 ->
        taint_env_le env0 env2.
    Proof.
      intros * Ht1 Ht2. consider taint_env_le.
      intros. eapply taint_le_trans; eauto.
    Qed.

    Ltac solve_taint_env_le :=
      intros taint_env idx; unfold set_reg_taint, taint_env_le, get_reg_taint_default;
      intros reg; destruct_with_eqn (beq_dec reg idx); simplify; subst;
      [ rewrite SortedRegEnv.update_correct_eq;
        rewrite SortedRegEnv.opt_get_find;
        unfold SortedRegEnv.to_list;
        destruct_match; destruct_match_pairs; subst; constructor; auto
      | rewrite SortedRegEnv.update_correct_neq; auto;
        destruct_match; apply taint_le_refl
      ].

    Lemma taint_env_le_read0:
      forall taint_env idx,
      taint_env_le taint_env (set_reg_taint taint_env idx set_taint_read0).
    Proof.
      solve_taint_env_le.
    Qed.
    Lemma taint_env_le_read1:
      forall taint_env idx,
      taint_env_le taint_env (set_reg_taint taint_env idx set_taint_read1).
    Proof.
      solve_taint_env_le.
    Qed.
    Lemma taint_env_le_write0:
      forall taint_env idx,
      taint_env_le taint_env (set_reg_taint taint_env idx set_taint_write0).
    Proof.
      solve_taint_env_le.
    Qed.

    Lemma taint_env_le_write1:
      forall taint_env idx,
      taint_env_le taint_env (set_reg_taint taint_env idx set_taint_write1).
    Proof.
      solve_taint_env_le.
    Qed.

    Lemma commit_update_empty:
      forall st,
        commit_update st log_empty = st.
    Proof.
      intros; unfold commit_update.
      apply SortedRegEnv.env_ext.
      intros. rewrite SortedRegEnv.opt_get_map.
      simpl. destruct_match; auto.
    Qed.

    Lemma state_ext:
      forall (st1 st2: state_t),
        (forall reg, get_reg st1 reg = get_reg st2 reg) ->
        st1 = st2.
    Proof.
      intros. apply SortedRegEnv.env_ext. auto.
    Qed.

    Lemma taint_le_merge_taint:
      forall taint t1 t2,
        taint_le taint t1 ->
        taint_le taint t2 ->
        taint_le taint (merge_taints t1 t2).
    Proof.
      intros * Ht1 Ht2. destruct Ht1; destruct Ht2; unfold merge_taints.
      constructor; intros Ht; simpl; rewrite Ht in *; propositional; rewrite_solve.
    Qed.

    Lemma taint_env_le_merge_taint_env:
      forall taint_env t1 t2,
        taint_env_le taint_env t1 ->
        taint_env_le taint_env t2 ->
        taint_env_le taint_env (merge_taint_env t1 t2).
    Proof.
      intros * Ht1 Ht2.
      unfold taint_env_le, merge_taint_env, get_reg_taint_default in *.
      intros reg; specialize (Ht1 reg); specialize (Ht2 reg).
      rewrite SortedRegEnv.opt_get_mapV.
      rewrite SortedRegEnv.opt_get_zip_default.
      repeat destruct_match; auto.
      all: apply taint_le_merge_taint; auto.
    Qed.

    Lemma taint_action_generalizes_taint:
      forall int_fn_env fuel taint_env taint_env' action,
        taint_action int_fn_env fuel taint_env action = Success (Some taint_env') ->
        taint_env_le taint_env taint_env'.
    Proof.
      induction fuel; cbn; [discriminate |].
      destruct action; simpl; intros * Htaint; simplify.
      all: repeat match goal with
                  | |- _ => progress (simplify; try simplify_res_opt_bind)
                  | |- taint_env_le ?t ?t =>
                    apply taint_env_le_refl
                  | H: taint_action _ _ _ _ = _ |- _ =>
                    apply IHfuel in H
                  | H2: taint_env_le ?e1 ?e2
                    |- taint_env_le ?e0 ?e2 =>
                    apply taint_env_le_trans with (2 := H2); auto
                  | H: match _ with | _ => _ end = _ |- _=>
                    destruct_matches_in_hyp H
                  | H1: taint_env_le ?t ?t1,
                    H2: taint_env_le ?t ?t2
                    |- taint_env_le ?taint_env (merge_taint_env ?t1 ?t2) =>
                    apply taint_env_le_merge_taint_env; eauto; solve[eapply taint_env_le_trans; eauto]
                  | _ => assumption
                  end.
      - apply taint_env_le_read0.
      - apply taint_env_le_read1.
      - apply taint_env_le_trans with (1 := Htaint0).
        apply taint_env_le_write0.
      - apply taint_env_le_trans with (1 := Htaint0).
        apply taint_env_le_write1.
    Qed.

      Definition taint_env_does_not_conflict (env1: taint_env_t) (env2: taint_env_t) : Prop :=
        forall reg, taint_conflicts (get_reg_taint_default env1 reg) (get_reg_taint_default env2 reg) = false.
      Lemma taint_env_does_not_conflict_weaken:
        forall log taint1 taint2,
          taint_env_does_not_conflict log taint1 ->
          taint_env_le taint2 taint1 ->
          taint_env_does_not_conflict log taint2.
      Proof.
        intros * X1 X2.
        consider taint_env_does_not_conflict.
        intros. specialize X1 with (reg := reg).
        consider taint_conflicts.
        consider taint_env_le. specialize X2 with (reg := reg).
        destruct X2.
        repeat rewrite orb_false_iff.
        repeat rewrite orb_false_iff in *. propositional.
        repeat rewrite andb_false_iff in *.
        repeat rewrite orb_false_iff in *.
        split_ands_in_goal.
        all: repeat match goal with
                    | |- ?x = false \/ _  =>
                      destruct x eqn:?; [right | left]
                    | H: ?x = _ |- _ =>
                      progress (rewrite H in *)
                               | H: true = false \/ _ |- _ =>
                                 destruct H; [discriminate | ]
                               | |- _ => progress propositional
                                end.
      Qed.

      Ltac solve_taint_le :=
          repeat match goal with
          | |- _ => progress simpl
          | H: _ = _ |- _ => progress (rewrite H)
          | |- context[_ || true] => rewrite orb_true_r
          | _ => reflexivity
          end.

      Ltac solve_taint_conflicts :=
        intros log idx taint_env env Henv Htaint;
        unfold taint_conflicts, taint_env_approximates_log, LE_may_read0, LE_may_read1, LE_may_write0, LE_may_write1,
               taint_approximates_log_entry, get_reg_taint_default, set_reg_taint, le_to_taint, is_someb,
               conflicts_with_read0, conflicts_with_read1, conflicts_with_write0, conflicts_with_write1 in *;
        specialize Htaint with (reg := idx); simpl in *; destruct Htaint;
        repeat rewrite SortedRegEnv.update_correct_eq; simpl in *;
        destruct_match; destruct_match_pairs; subst; simpl; auto;
          bash_destruct Henv; propositional; solve_taint_le.
      Lemma taint_conflicts_read0:
        forall log idx taint_env env,
        LE_may_read0 (log_get log idx) = false ->
        taint_env_approximates_log taint_env log ->
        taint_conflicts (get_reg_taint_default taint_env idx)
                        (get_reg_taint_default (set_reg_taint env idx set_taint_read0) idx) = true.
      Proof.
        solve_taint_conflicts.
      Qed.

      Lemma taint_conflicts_read1:
        forall log idx taint_env env,
        LE_may_read1 (log_get log idx) = false ->
        taint_env_approximates_log taint_env log ->
        taint_conflicts (get_reg_taint_default taint_env idx)
                        (get_reg_taint_default (set_reg_taint env idx set_taint_read1) idx) = true.
      Proof.
        solve_taint_conflicts.
      Qed.


      Lemma taint_conflicts_write0:
        forall log idx taint_env env,
        LE_may_write0 (log_get log idx) = false ->
        taint_env_approximates_log taint_env log ->
        taint_conflicts (get_reg_taint_default taint_env idx)
                        (get_reg_taint_default (set_reg_taint env idx set_taint_write0) idx) = true.
      Proof.
        solve_taint_conflicts.
      Qed.

      Lemma taint_conflicts_write0':
        forall log idx taint_env env,
        LE_may_write0 (log_get log idx) = false ->
        taint_env_approximates_log env log ->
        conflicts_with_write0 (get_reg_taint_default env idx) = false ->
        taint_conflicts (get_reg_taint_default taint_env idx)
                        (get_reg_taint_default (set_reg_taint env idx set_taint_write0) idx) = true.
      Proof.
        consider conflicts_with_write0.
        solve_taint_conflicts; simpl in *; try discriminate.
        - rewrite tle_read3 in *. simpl in *. discriminate.
        - rewrite tle_write2 in *. simpl in *. rewrite orb_true_r in *. discriminate.
        - rewrite tle_write3 in *. simpl in *. repeat rewrite orb_true_r in *. discriminate.
      Qed.

      Lemma taint_conflicts_write1:
        forall log idx taint_env env,
        LE_may_write1 (log_get log idx) = false ->
        taint_env_approximates_log taint_env log ->
        taint_conflicts (get_reg_taint_default taint_env idx)
                        (get_reg_taint_default (set_reg_taint env idx set_taint_write1) idx) = true.
      Proof.
        solve_taint_conflicts.
      Qed.
      Lemma taint_conflicts_write1':
        forall log idx taint_env env,
        LE_may_write1 (log_get log idx) = false ->
        taint_env_approximates_log env log ->
        conflicts_with_write1 (get_reg_taint_default env idx) = false ->
        taint_conflicts (get_reg_taint_default taint_env idx)
                        (get_reg_taint_default (set_reg_taint env idx set_taint_write1) idx) = true.
      Proof.
        consider conflicts_with_write1.
        solve_taint_conflicts; simpl in *; try discriminate.
        congruence.
      Qed.

      Lemma taint_le_empty:
        taint_le (le_to_taint LE_empty) (empty_taint).
      Proof.
        unfold le_to_taint. simpl. constructor; auto.
      Qed.

      Lemma taint_approximates_log_entry_empty:
        taint_approximates_log_entry empty_taint LE_empty.
      Proof.
        unfold taint_approximates_log_entry.
        apply taint_le_empty.
      Qed.

      Lemma taint_env_approximates_log_empty:
         taint_env_approximates_log SortedRegEnv.empty log_empty.
      Proof.
        unfold taint_env_approximates_log. intros. simpl.
        unfold get_reg_taint_default.
        rewrite SortedRegEnv.opt_get_empty.
        rewrite log_get_empty.
        apply taint_approximates_log_entry_empty.
      Qed.

      Definition log_to_taint_env (log: log_t) : taint_env_t :=
        SortedRegEnv.mapV le_to_taint log.
      Lemma taint_approximates_log_entry_refl:
        forall le,
        taint_approximates_log_entry (le_to_taint le) le.
      Proof.
        intros; unfold taint_approximates_log_entry; auto.
        apply taint_le_refl.
      Qed.

      Lemma taint_env_approximates_log_refl:
       forall log,
       taint_env_approximates_log (log_to_taint_env log) log.
      Proof.
        unfold taint_env_approximates_log, log_to_taint_env, get_reg_taint_default, log_get.
        intros.
        rewrite SortedRegEnv.opt_get_mapV.
        destruct_match.
        - apply taint_approximates_log_entry_refl.
        - apply taint_approximates_log_entry_empty.
      Qed.

      Lemma does_not_conflict_equiv:
        forall taint_sched taint_rule,
          does_not_conflict taint_sched taint_rule = true <->
          taint_env_does_not_conflict taint_sched taint_rule.
      Proof.
        split; unfold does_not_conflict, taint_env_does_not_conflict, taint_conflicts, get_reg_taint_default,
               conflicts_with_read0, conflicts_with_read1, conflicts_with_write0, conflicts_with_write1; intros.
        - rewrite forallb_forall in H.
          destruct_match; auto.
          destruct_match; simpl; auto.
          + specialize (H (reg, (t0,t))). hnf in H.
            apply negb_true_iff in H; auto.
            apply SortedRegEnv.In_to_list.
            rewrite SortedRegEnv.opt_get_zip_default. repeat simpl_match. reflexivity.
          + repeat rewrite andb_false_r. auto.
        - apply forallb_forall. intros (reg & (t0 & t1)).
          intros HIn. specialize (H reg).
          apply SortedRegEnv.In_to_list in HIn.
          rewrite SortedRegEnv.opt_get_zip_default in HIn.
          apply negb_true_iff.
          bash_destruct HIn; simplify; auto.
      Qed.

      Lemma taint_conflicts_empty_l_false:
        forall t, taint_conflicts empty_taint t = false.
      Proof.
        intros; unfold taint_conflicts, conflicts_with_read0,
                conflicts_with_read1, conflicts_with_write0, conflicts_with_write1.
        simpl. repeat rewrite andb_false_r; auto.
      Qed.

      Lemma taint_conflicts_empty_r_false:
        forall t, taint_conflicts t empty_taint = false.
      Proof.
        intros; unfold taint_conflicts, conflicts_with_read0,
                conflicts_with_read1, conflicts_with_write0, conflicts_with_write1.
        simpl. repeat rewrite andb_false_r; auto.
      Qed.

      Lemma taint_approximates_does_not_conflict:
        forall t t0 t1 log taint r,
          taint_conflicts t1 t0 = false ->
          SortedRegEnv.opt_get taint r = Some t1 ->
          taint_env_approximates_log taint log ->
          SortedRegEnv.opt_get (log_to_taint_env log) r = Some t ->
          taint_conflicts t t0 = false.
      Proof.
        intros. unfold taint_conflicts, taint_env_approximates_log, get_reg_taint_default,
                taint_approximates_log_entry, conflicts_with_read0,
                conflicts_with_read1, conflicts_with_write0, conflicts_with_write1 in *.
        specialize (H1 r). simpl_match. unfold log_to_taint_env in *.
        rewrite SortedRegEnv.opt_get_mapV in H2. bash_destruct H2; simplify.
        destruct H1. unfold log_get in *. repeat simpl_match.
        repeat rewrite orb_false_iff in H.
        repeat rewrite andb_false_iff in H.
        repeat rewrite orb_false_iff in H.
        repeat rewrite orb_false_iff.
        repeat rewrite andb_false_iff. propositional.
        repeat rewrite orb_false_iff.
        split_ands_in_goal.
        all: repeat match goal with
                    | H: true = false \/ _ |- _ => destruct H; [discriminate |]; propositional
                    | |- true = false \/ _ => right
                    | |- false = false /\ _ => split; [reflexivity | ]
                    | |- ?x = false \/ _  =>
                      destruct x eqn:?; auto; propositional; try congruence
                    | |- ?x = false /\ _  =>
                      destruct x eqn:?; auto; propositional; try congruence
                    | |- ?x = false =>
                      destruct x eqn:?; auto; propositional; try congruence
                    end.
        - destruct_with_eqn (taint_read1 (le_to_taint l)); propositional; try congruence.
          destruct_with_eqn (taint_write0 (le_to_taint l)); propositional; try congruence.
          destruct_with_eqn (taint_write1 (le_to_taint l)); propositional; try congruence.
      Qed.

      Lemma taint_env_approximates_does_not_conflict:
        forall taint log1 log2,
          taint_env_approximates_log taint log1 ->
          does_not_conflict taint log2 = true ->
          does_not_conflict (log_to_taint_env log1) log2 = true.
      Proof.
        intros * Happrox Hconflict.
        consider does_not_conflict.
        apply forallb_forall.
        rewrite forallb_forall in Hconflict.
        intros. destruct_match_pairs; subst.
        apply negb_true_iff.
        apply SortedRegEnv.In_to_list in H.
        rewrite SortedRegEnv.opt_get_zip_default in H.
        bash_destruct H; simplify.
        - destruct_with_eqn (SortedRegEnv.opt_get taint t).
          + specialize (Hconflict (t, (t2,t1))). hnf in Hconflict.
            assert_pre Hconflict; propositional.
            { apply SortedRegEnv.In_to_list. rewrite SortedRegEnv.opt_get_zip_default.
              repeat simpl_match. reflexivity.
            }
            { apply negb_true_iff in Hconflict.
              eapply taint_approximates_does_not_conflict; eauto.
            }
          + unfold taint_env_approximates_log, get_reg_taint_default, taint_approximates_log_entry in *.
            specialize (Happrox t).
            simpl_match.
            destruct Happrox; consider @is_someb; simpl in *.
            unfold taint_conflicts. consider log_get.
            consider log_to_taint_env.
            rewrite SortedRegEnv.opt_get_mapV in Heqo; bash_destruct Heqo; simplify;
              unfold is_someb, conflicts_with_read0, conflicts_with_read1,
              conflicts_with_write0, conflicts_with_write1, le_to_taint, is_someb in *; simpl.
            bash_destruct tle_write2; propositional; simplify_bool.
            bash_destruct tle_write3; propositional; simplify_bool; simpl.
            destruct_with_eqn (lread1 l); propositional; simplify_bool.
            repeat rewrite andb_false_r; auto.
        - apply taint_conflicts_empty_r_false; auto.
        - apply taint_conflicts_empty_l_false; auto.
      Qed.

      Lemma taint_env_approximates_append:
        forall taint1 taint2 log1 log2,
          taint_env_approximates_log taint1 log1 ->
          taint_env_approximates_log taint2 log2 ->
          taint_env_approximates_log (merge_taint_env taint2 taint1) (log_app log1 log2).
      Proof.
        intros * Hlog1 Hlog2.
        unfold taint_env_approximates_log, merge_taint_env,
               get_reg_taint_default, taint_approximates_log_entry in *.
        intros; rewrite get_log_app; simpl.
        specialize (Hlog1 reg); specialize (Hlog2 reg).
        rewrite SortedRegEnv.opt_get_mapV. rewrite SortedRegEnv.opt_get_zip_default.
        destruct Hlog1. destruct Hlog2.
        unfold logentry_app, le_to_taint, is_someb in *; simpl in *.
        destruct_with_eqn (SortedRegEnv.opt_get taint2 reg);
          destruct_with_eqn (SortedRegEnv.opt_get taint1 reg); simpl in *; unfold merge_taints.
        all: constructor; simpl; repeat rewrite orb_true_iff; intros H; propositional; unfold opt_or in *; simplify;
            bash_destruct H; try solve[try destruct H; repeat simpl_match; propositional; discriminate].
      Qed.

      Ltac solve_taint_env_approximates_log_set :=
        unfold taint_env_approximates_log, taint_approximates_log_entry,
        get_reg_taint_default, set_reg_taint in *;
        intros taint_env log idx * Htaint reg;
        specialize Htaint with (reg := reg);
        destruct Htaint;
        destruct_with_eqn (beq_dec reg idx); simplify; subst;
        [ rewrite log_set_eq by auto; rewrite SortedRegEnv.update_correct_eq;
          destruct_match; auto; constructor; auto
        | rewrite log_set_neq by auto; rewrite SortedRegEnv.update_correct_neq by auto;
          destruct_match; constructor; auto
        ].

      Lemma taint_env_approximates_log_set__read0:
        forall taint_env log idx,
          taint_env_approximates_log taint_env log ->
          taint_env_approximates_log (set_reg_taint taint_env idx set_taint_read0)
                                     (log_set log idx (LE_set_read0 (log_get log idx))).
      Proof.
        solve_taint_env_approximates_log_set.
      Qed.

      Lemma taint_env_approximates_log_set__read1:
        forall taint_env log idx,
          taint_env_approximates_log taint_env log ->
          taint_env_approximates_log (set_reg_taint taint_env idx set_taint_read1)
                                     (log_set log idx (LE_set_read1 (log_get log idx))).
      Proof.
        solve_taint_env_approximates_log_set.
      Qed.

      Lemma taint_env_approximates_log_set__write0:
        forall taint_env log idx v,
          taint_env_approximates_log taint_env log ->
          taint_env_approximates_log (set_reg_taint taint_env idx set_taint_write0)
                                     (log_set log idx (LE_set_write0 (log_get log idx) v)).
      Proof.
        solve_taint_env_approximates_log_set.
      Qed.

      Lemma taint_env_approximates_log_set__write1:
        forall taint_env log idx v,
          taint_env_approximates_log taint_env log ->
          taint_env_approximates_log (set_reg_taint taint_env idx set_taint_write1)
                                     (log_set log idx (LE_set_write1 (log_get log idx) v)).
      Proof.
        solve_taint_env_approximates_log_set.
      Qed.

      Lemma taint_le_empty':
        forall t, taint_le t empty_taint -> t = empty_taint.
      Proof.
        intros. destruct H. destruct t; simpl in *; propositional.
        unfold empty_taint.
        f_equal; [destruct taint_read0 | destruct taint_read1 | destruct taint_write0 | destruct taint_write1]; propositional.
      Qed.

(* Lemma no_read1_and_write1_increasing: *)
(*   forall env1 env2, *)
(*   no_read1_and_write1 env2 = true -> *)
(*   taint_env_le env1 env2 -> *)
(*   no_read1_and_write1 env1 = true. *)
(* Proof. *)
(*   intros. consider no_read1_and_write1. *)
(*   consider taint_env_le. consider get_reg_taint_default. consider reg_t_beq. *)
(*   apply forallb_forall. *)
(*   rewrite forallb_forall in H. *)
(*   intros. destruct_match_pairs; subst. *)
(*   apply negb_true_iff. *)
(*   apply andb_false_iff. *)
(*   specialize H0 with (reg := r). *)
(*   apply SortedRegEnv.In_to_list in H1. simpl_match. *)
(*   destruct_matches_in_hyp H0. *)
(*   - apply SortedRegEnv.In_to_list in Heqo. *)
(*     specialize H with (1 := Heqo). destruct_match_pairs; simplify_tupless. *)
(*     apply negb_true_iff in H. *)
(*     apply andb_false_iff in H. *)
(*     destruct H0. *)
(*     destruct H; rewrite H in *. *)
(*     + destruct (taint_write1 t) eqn:?; propositional. *)
(*     + destruct (taint_read1 t) eqn:?; propositional. *)
(*   - apply taint_le_empty' in H0. subst. auto. *)
(* Qed. *)
(* Lemma no_read1_and_write1_set_write0: *)
(*   forall env idx, *)
(*   no_read1_and_write1 (set_reg_taint env idx set_taint_write0) = true -> *)
(*   no_read1_and_write1 env = true. *)
(* Proof. *)
(*   intros. unfold no_read1_and_write1 in *. *)
(*   rewrite forallb_forall in H. *)
(*   apply forallb_forall. intros. destruct_match_pairs; simplify. *)
(*   unfold set_reg_taint in *. *)
(*   apply SortedRegEnv.In_to_list in H0. *)
(*   destruct (Nat.eqb idx r) eqn:?; simplify; subst. *)
(*   { specialize H with (x := (r, set_taint_write0 t)). *)
(*     assert_pre H. *)
(*     { apply SortedRegEnv.In_to_list. rewrite SortedRegEnv.update_correct_eq. simpl_match. auto. } *)
(*     { propositional. } *)
(*   } *)
(*   { specialize H with (x := (r, t)). *)
(*     assert_pre H. *)
(*     { apply SortedRegEnv.In_to_list. rewrite SortedRegEnv.update_correct_neq by auto. assumption. } *)
(*     { propositional. } *)
(*   } *)
(* Qed. *)

    Lemma taint_le_empty_l:
      forall t,
        taint_le empty_taint t.
    Proof.
      intros; constructor; simpl; propositional; discriminate.
    Qed.
    Lemma merge_taints_empty_r:
      forall t,
        merge_taints t empty_taint = t.
    Proof.
      intros; unfold merge_taints. destruct t; simpl; repeat rewrite orb_false_r; auto.
    Qed.
    Lemma merge_taints_empty_l:
      forall t,
        merge_taints empty_taint t = t.
    Proof.
      intros; unfold merge_taints. simpl. destruct t; reflexivity.
    Qed.
    Lemma taint_le_merge_taints_refl_l:
      forall t t2,
        taint_le t (merge_taints t t2).
    Proof.
      unfold merge_taints. intros; constructor; simpl; propositional; rewrite_solve.
    Qed.

    Lemma taint_le_merge_taints_refl_r:
      forall t t2,
        taint_le t (merge_taints t2 t).
    Proof.
      unfold merge_taints. intros; constructor; simpl; intro H; rewrite H; rewrite orb_true_r; reflexivity.
    Qed.

    Lemma taint_env_le_merge_refl_l:
      forall t0 t1,
        taint_env_le t0 (merge_taint_env t0 t1).
    Proof.
      intros. unfold taint_env_le, merge_taint_env, get_reg_taint_default.
      intros. rewrite SortedRegEnv.opt_get_mapV.
      rewrite SortedRegEnv.opt_get_zip_default.
      destruct_match; auto.
      + destruct_match.
        * apply taint_le_merge_taints_refl_l.
        * rewrite merge_taints_empty_r. apply taint_le_refl.
      + apply taint_le_empty_l.
    Qed.

    Lemma taint_env_le_merge_refl_r:
      forall t0 t1,
        taint_env_le t0 (merge_taint_env t1 t0).
    Proof.
      intros. unfold taint_env_le, merge_taint_env, get_reg_taint_default.
      intros. rewrite SortedRegEnv.opt_get_mapV.
      rewrite SortedRegEnv.opt_get_zip_default.
      destruct_match; auto.
      + destruct_match.
        * apply taint_le_merge_taints_refl_r.
        * rewrite merge_taints_empty_l. apply taint_le_refl.
      + destruct_match; apply taint_le_empty_l.
    Qed.

    Lemma taint_env_does_not_conflict_merge_taint_l:
      forall log t1 t2,
        taint_env_does_not_conflict log (merge_taint_env t1 t2) ->
        taint_env_does_not_conflict log t1.
    Proof.
      unfold taint_env_does_not_conflict, get_reg_taint_default, taint_conflicts, merge_taint_env,
      conflicts_with_read0, conflicts_with_read1, conflicts_with_write0, conflicts_with_write1 in *.
      intros * H reg. specialize (H reg).
      rewrite SortedRegEnv.opt_get_mapV in H.
      rewrite SortedRegEnv.opt_get_zip_default in H.
      destruct_match; simpl; auto.
      destruct_match; simpl; repeat rewrite andb_false_r; auto.
      unfold merge_taints in *; simpl in *.
      repeat rewrite orb_false_iff in H; repeat rewrite andb_false_iff in H.
      repeat rewrite orb_false_iff. repeat rewrite andb_false_iff.
      destruct_matches_in_hyp H; propositional; simpl in *.
      all: split_ands_in_goal;
        [ destruct_with_eqn (taint_read0 t); auto
        | destruct_with_eqn (taint_read1 t); auto
        | destruct_with_eqn (taint_write0 t); auto
        | destruct_with_eqn (taint_write1 t); auto].
    Qed.
Definition ext_fn_taint_env_approximates_log (env: ext_fn_taint_env_t) (log: ext_log_t) : Prop :=
  forall fn, is_some (SortedExtFnEnv.opt_get log fn) ->
        SortedExtFnEnv.opt_get env fn = Some true.
Lemma ext_fn_taint_env_approximates_log_merge_l:
  forall env0 env1 log0,
  ext_fn_taint_env_approximates_log env0 (Log__ext log0) ->
  ext_fn_taint_env_approximates_log (merge_ext_fn_taint_env env0 env1) (Log__ext log0).
Proof.
  unfold ext_fn_taint_env_approximates_log.
  intros * approx0 fn hin.
  consider @merge_ext_fn_taint_env.
  rewrite SortedRegEnv.opt_get_mapV.
  rewrite SortedRegEnv.opt_get_zip_default.
  specialize approx0 with (1 := hin).
  consider @is_some. propositional. simpl_match.
  destruct_match; auto.
Qed.
Lemma ext_fn_taint_env_approximates_log_merge_r:
  forall env0 env1 log1,
  ext_fn_taint_env_approximates_log env1 (Log__ext log1) ->
  ext_fn_taint_env_approximates_log (merge_ext_fn_taint_env env0 env1) (Log__ext log1).
Proof.
  unfold ext_fn_taint_env_approximates_log.
  intros * approx0 fn hin.
  consider @merge_ext_fn_taint_env.
  rewrite SortedRegEnv.opt_get_mapV.
  rewrite SortedRegEnv.opt_get_zip_default.
  specialize approx0 with (1 := hin).
  consider @is_some. propositional. simpl_match.
  destruct_match; rewrite orb_true_r; auto.
Qed.

Lemma ext_fn_taint_env_approximates_log_implies:
  forall env log v fn,
  SortedExtFnEnv.opt_get log fn = Some v ->
  ext_fn_taint_env_approximates_log env log ->
  SortedExtFnEnv.opt_get env fn = Some true.
Proof.
  unfold ext_fn_taint_env_approximates_log.
  intros. consider @is_some.
  eapply H0; eauto.
Qed.
Lemma ext_fn_taint_env_approximates_log_update:
  forall log fn v env,
  ext_fn_taint_env_approximates_log env log ->
  ext_fn_taint_env_approximates_log (SortedExtFnEnv.update env fn (fun _ : bool => true) false)
    (ext_log_update log fn v).
Proof.
  unfold ext_fn_taint_env_approximates_log.
  intros. consider ext_log_update. consider @is_some. propositional.
  destruct_with_eqn (beq_dec fn fn0); simplify.
  - repeat rewrite SortedRegEnv.update_correct_eq in *.
    assert (v0 = Some v) by (bash_destruct H1); subst.
    destruct_match; auto.
  - repeat rewrite SortedRegEnv.update_correct_neq in * by auto.
    apply H. eauto.
Qed.

Definition ext_fn_taint_env_subset (env0 env1: ext_fn_taint_env_t) : Prop :=
  forall fn, SortedExtFnEnv.opt_get env0 fn = Some true ->
        SortedExtFnEnv.opt_get env1 fn = Some true.
Lemma ext_fn_taint_env_subset_update:
  forall env fn default,
  ext_fn_taint_env_subset env (SortedExtFnEnv.update env fn (fun _ : bool => true) default).
Proof.
  unfold ext_fn_taint_env_subset. intros.
  destruct_with_eqn (beq_dec fn fn0); simplify.
  - rewrite SortedExtFnEnv.update_correct_eq. simpl_match. auto.
  - rewrite SortedExtFnEnv.update_correct_neq by auto. auto.
Qed.

Lemma ext_fn_taint_env_subset_refl:
  forall env, ext_fn_taint_env_subset env env.
Proof.
  unfold ext_fn_taint_env_subset; auto.
Qed.
  Lemma ext_fn_taint_env_subset_trans:
    forall env1 env2 env3,
      ext_fn_taint_env_subset env1 env2 ->
      ext_fn_taint_env_subset env2 env3 ->
      ext_fn_taint_env_subset env1 env3.
  Proof.
    unfold ext_fn_taint_env_subset; auto.
  Qed.
Lemma ext_fn_taint_env_subset_merge_l:
  forall env e0 e1,
  ext_fn_taint_env_subset env e0 ->
  ext_fn_taint_env_subset env (merge_ext_fn_taint_env e0 e1).
Proof.
  unfold ext_fn_taint_env_subset, merge_ext_fn_taint_env.
  intros. rewrite SortedExtFnEnv.opt_get_mapV. rewrite SortedExtFnEnv.opt_get_zip_default.
  rewrite H; auto. destruct_match; auto.
Qed.
Lemma ext_fn_taint_env_subset_merge_r:
  forall env e0 e1,
  ext_fn_taint_env_subset env e1 ->
  ext_fn_taint_env_subset env (merge_ext_fn_taint_env e0 e1).
Proof.
  unfold ext_fn_taint_env_subset, merge_ext_fn_taint_env.
  intros. rewrite SortedExtFnEnv.opt_get_mapV. rewrite SortedExtFnEnv.opt_get_zip_default.
  rewrite H; auto. destruct_match; auto.
  rewrite orb_true_r; auto.
Qed.

    Lemma ext_fn_taint_action_subset_correct:
      forall fuel int_fn_env action env env',
      ext_fn_taint_action int_fn_env fuel env action = Success (Some env') ->
      ext_fn_taint_env_subset env env'.
    Proof.
      induction fuel; cbn; [discriminate |].
      destruct action; simpl; intros env env';
      intros Htaint; unfold res_opt_bind in *; simplify; auto.
      Ltac t_ext_fn_taint_action_subset IHfuel :=
        repeat match goal with
        | H: ext_fn_taint_action _ _ _ _ = _ |- _ =>
            apply IHfuel in H
        | |- ext_fn_taint_env_subset ?x ?x =>
            apply ext_fn_taint_env_subset_refl
        | H1: ext_fn_taint_env_subset ?e1 ?e2,
          H2: ext_fn_taint_env_subset ?e2 ?e3 |- _ =>
            pose_fresh (ext_fn_taint_env_subset_trans _ _ _ H1 H2 )
        | H: ext_fn_taint_env_subset ?env ?e0
          |- ext_fn_taint_env_subset ?env (merge_ext_fn_taint_env ?e0 ?e1) =>
            apply ext_fn_taint_env_subset_merge_l with (1 := H)
        | |- ext_fn_taint_env_subset ?env (SortedExtFnEnv.update ?env _ (fun _ : bool => true) _) =>
              apply ext_fn_taint_env_subset_update
        end; auto.


      all: t_ext_fn_taint_action_subset IHfuel.
      - bash_destruct Htaint.
      - bash_destruct Htaint; simplify; t_ext_fn_taint_action_subset IHfuel.
      - bash_destruct Htaint; simplify.
        + eapply ext_fn_taint_env_subset_trans with (1 := Heqr).
          t_ext_fn_taint_action_subset IHfuel.
        + eapply ext_fn_taint_env_subset_trans with (1 := Heqr).
          t_ext_fn_taint_action_subset IHfuel.
    Qed.

Lemma ext_fn_taint_env_approximates_log_subset:
  forall env env' log,
  ext_fn_taint_env_approximates_log env log ->
  ext_fn_taint_env_subset env env' ->
  ext_fn_taint_env_approximates_log env' log.
Proof.
  unfold ext_fn_taint_env_approximates_log, ext_fn_taint_env_subset.
  intros; consider @is_some; propositional; eauto.
Qed.
Definition ext_taint_env_does_not_conflict (env1 env2: ext_fn_taint_env_t) : Prop :=
  forall fn, SortedExtFnEnv.opt_get env1 fn = Some true ->
        SortedExtFnEnv.opt_get env2 fn = Some true ->
        False.
Definition ext_log_to_ext_fn_taint_env (log: ext_log_t) : ext_fn_taint_env_t :=
  SortedExtFnEnv.mapV (fun opt_v => match opt_v with
                                 | Some _ => true
                                 | _ => false
                                 end) log .
Lemma ext_fn_taint_env_does_not_conflict_log_to_taint:
  forall fn log ext_fn_taint v,
  ext_taint_env_does_not_conflict (ext_log_to_ext_fn_taint_env log) ext_fn_taint ->
  SortedExtFnEnv.opt_get log fn = Some (Some v) ->
  SortedExtFnEnv.opt_get ext_fn_taint fn = Some true ->
  False.
Proof.
  intros. consider ext_taint_env_does_not_conflict.
  eapply H; eauto. unfold ext_log_to_ext_fn_taint_env.
  rewrite SortedExtFnEnv.opt_get_mapV. simpl_match. auto.
Qed.

Lemma ext_taint_env_does_not_conflict_subset:
  forall env0 env1 env2,
  ext_taint_env_does_not_conflict env0 env1 ->
  ext_fn_taint_env_subset env2 env1 ->
  ext_taint_env_does_not_conflict env0 env2.
Proof.
  intros. consider ext_taint_env_does_not_conflict.
  consider ext_fn_taint_env_subset.
  intros. eapply H; eauto.
Qed.
Lemma ext_taint_env_does_not_conflict_merge_l:
  forall env0 env1 env2,
  ext_taint_env_does_not_conflict env0 (merge_ext_fn_taint_env env1 env2) ->
  ext_taint_env_does_not_conflict env0 env1.
Proof.
  intros.
  consider ext_taint_env_does_not_conflict. consider merge_ext_fn_taint_env.
  intros. eapply H; eauto.
  rewrite SortedExtFnEnv.opt_get_mapV.
  rewrite SortedExtFnEnv.opt_get_zip_default.
  repeat simpl_match.
  destruct_match; auto.
Qed.

Lemma ext_taint_env_does_not_conflict_merge_r:
  forall env0 env1 env2,
  ext_taint_env_does_not_conflict env0 (merge_ext_fn_taint_env env1 env2) ->
  ext_taint_env_does_not_conflict env0 env2.
Proof.
  intros.
  consider ext_taint_env_does_not_conflict. consider merge_ext_fn_taint_env.
  intros. eapply H; eauto.
  rewrite SortedExtFnEnv.opt_get_mapV.
  rewrite SortedExtFnEnv.opt_get_zip_default.
  repeat simpl_match.
  destruct_match; rewrite orb_true_r; auto.
Qed.
Lemma ext_taint_env_does_not_conflict_update:
  forall env1 env2 fn default,
    ext_taint_env_does_not_conflict env1 (SortedExtFnEnv.update env2 fn (fun _ => true) default) ->
    ext_taint_env_does_not_conflict env1 env2.
Proof.
  unfold ext_taint_env_does_not_conflict. intros.
  eapply H; eauto.
  destruct_with_eqn (beq_dec fn fn0); simplify.
  - rewrite SortedExtFnEnv.update_correct_eq. simpl_match. auto.
  - rewrite SortedExtFnEnv.update_correct_neq by auto. auto.
Qed.

    Ltac t_oraat_interp_action_correct' IHfuel :=
      repeat match goal with
           | _ => progress (simpl; simplify; propositional)
           | H: taint_env_does_not_conflict ?log (merge_taints ?t1 _)
             |- taint_env_does_not_conflict ?log ?t1 =>
             apply taint_env_does_not_conflict_merge_taint_l with (1 := H); assumption
           | H: match _ with | Some _ => _ | None => None end = None |- _ =>
             destruct_matches_in_hyp H; destruct_match_pairs; [ discriminate | ]
           | _ => simpl_match
           | H: interp_action _ _ _ _ _ _ _ _ _ _ = Success ?opt |- _ =>
             eapply IHfuel in H; [ | solve[eauto] | | solve[eauto] | solve[eauto]  | solve[eauto]| solve[eauto] | solve[eauto] | | ]; destruct_with_eqn opt; subst
           | H1: oraat_interp_action _ _ _ _ _ ?st' _ _ _ ?action = _,
             H2: oraat_interp_action _ _ _ _ _ ?st' _ _ _ ?action = _ |- _ =>
             rewrite H1 in H2
           | H: res_opt_bind ?expr _ = Success _ |- _ =>
             destruct expr eqn:?; simpl in H
           | H1: taint_env_does_not_conflict ?taint_sched ?taint1
             |- taint_env_does_not_conflict ?taint_sched ?taint2 =>
             eapply taint_env_does_not_conflict_weaken; eauto
           | H: taint_action _ _ ?t1 _ = Success (Some ?t2)
             |- taint_env_le ?t1 ?t2 =>
             eapply taint_action_generalizes_taint; eauto
           | H: taint_env_approximates_log ?taint_env0 ?log
             |- taint_env_approximates_log ?taint_env1 ?log =>
             eapply taint_env_approximates_log_generalize_taint; eauto
           (* | H1: no_read1_and_write1 ?t' = true, *)
           (*       H2: taint_action _ _ ?t _ = Success ?t' *)
           (*   |- no_read1_and_write1 ?t = true => *)
           (*   apply no_read1_and_write1_increasing with (1 := H1); auto *)
           | H1: taint_action _ _ ?s1 _ = Success (Some ?s2),
             H2: taint_action _ _ ?s2 _ = Success (Some ?s3) |- taint_env_le ?s1 ?s3 =>
             eapply taint_env_le_trans; eapply taint_action_generalizes_taint; solve[eauto]
           | |- taint_env_le ?taint_env (set_reg_taint ?taint_env ?idx set_taint_read1) =>
             apply taint_env_le_read1
           | |- taint_env_le ?taint_env (set_reg_taint ?taint_env ?idx set_taint_read0) =>
             apply taint_env_le_read0
           | |- taint_env_le ?taint_env (set_reg_taint ?taint_env ?idx set_taint_write0) =>
             apply taint_env_le_write0
           | |- taint_env_le ?taint_env (set_reg_taint ?taint_env ?idx set_taint_write1) =>
             apply taint_env_le_write1
           | H: (match _ with | Some _ => _ | None => Success None end) = Success (Some _) |- _ =>
             destruct_matches_in_hyp H; [ | discriminate]
           | |- taint_env_le ?t0 (merge_taint_env ?t0 _ ) =>
             apply taint_env_le_merge_refl_l; auto
           | |- taint_env_le ?t0 (merge_taint_env _ ?t0 ) =>
             apply taint_env_le_merge_refl_r; auto
           | H1: taint_action _ _ ?s1 _ = Success (Some ?s2),
             H2: taint_action _ _ ?s1 _ = Success (Some ?s2')
             |- taint_env_le ?s1 (merge_taint_env ?s2 ?s2') =>
             apply taint_env_le_merge_taint_env
           | H: ext_fn_taint_env_approximates_log ?env0 ?log0
             |- ext_fn_taint_env_approximates_log (merge_ext_fn_taint_env ?env0 _) ?log0 =>
               apply ext_fn_taint_env_approximates_log_merge_l with (1 := H)
           | H: ext_fn_taint_env_approximates_log ?env0 ?log0
             |- ext_fn_taint_env_approximates_log (merge_ext_fn_taint_env _ ?env0) ?log0 =>
               apply ext_fn_taint_env_approximates_log_merge_r with (1 := H)
           | H: ext_fn_taint_action _ _ ?env _ = Success (Some ?env') |- _ =>
             pose_fresh (ext_fn_taint_action_subset_correct _ _ _ _ _ H)
           | H: ext_fn_taint_env_approximates_log ?env ?log,
             H1: ext_fn_taint_env_subset ?env ?env' |- _ =>
               pose_fresh (ext_fn_taint_env_approximates_log_subset _ _ _ H H1)
           | H: ext_taint_env_does_not_conflict ?env0 ?env1,
             H1: ext_fn_taint_env_subset ?env2 ?env1
             |- ext_taint_env_does_not_conflict ?env0 ?env2 =>
              pose_fresh (ext_taint_env_does_not_conflict_subset _ _ _ H H1)
           | H: ext_taint_env_does_not_conflict ?env0 (merge_ext_fn_taint_env ?env1 ?env2)
             |- _ =>
               pose_fresh (ext_taint_env_does_not_conflict_merge_r _ _ _ H)
           | H: ext_taint_env_does_not_conflict ?env0 (merge_ext_fn_taint_env ?env1 ?env2)
             |- _ =>
               pose_fresh (ext_taint_env_does_not_conflict_merge_l _ _ _ H)
           | H: ext_taint_env_does_not_conflict ?env1 (SortedExtFnEnv.update ?env2 _ (fun _ => true) ?default)
             |- _ =>
               pose_fresh (ext_taint_env_does_not_conflict_update _ _ _ _ H)
          (* | H: no_read1_and_write1 (set_reg_taint ?env ?idx set_taint_write0) = true *)
           (*   |- no_read1_and_write1 ?env = true  => *)
           (*   apply no_read1_and_write1_set_write0 with (1 := H) *)
           | _ => reflexivity || assumption
           end; auto.

    Lemma conflicts_with_read1_false_implies_no_write1:
      forall env log idx,
        conflicts_with_read1 (get_reg_taint_default env idx) = false ->
        taint_env_approximates_log env log ->
        lwrite1 (log_get log idx) = None.
    Proof.
      intros; unfold conflicts_with_read1, taint_env_approximates_log in *.
      unfold taint_approximates_log_entry in *. specialize (H0 idx).
      destruct H0. rewrite H in *. consider le_to_taint; simpl in *.
      destruct_with_eqn (lwrite1 (log_get log idx)); simpl in *; propositional. discriminate.
    Qed.
Lemma getenv_commit_wf:
  forall st log reg,
  is_some' (get_reg st reg) ->
  get_reg (commit_update st log) reg =
    match latest_write (log_get log reg) with
    | Some le => Some le
    | None => get_reg st reg
    end.
Proof.
  intros. unfold get_reg, commit_update, is_some' in *.
  repeat rewrite SortedRegEnv.opt_get_map.
  repeat rewrite SortedRegEnv.opt_get_zip_default.
  unfold log_get.
  destruct_match; auto.
  repeat destruct_match; auto.
Qed.
Lemma getenv_commit:
  forall st log reg,
  get_reg (commit_update st log) reg =
    match get_reg st reg, latest_write (log_get log reg) with
    | Some v, Some w => Some w
    | Some v, None => Some v
    | None, _ => None
    end.
Proof.
  intros. unfold get_reg, commit_update, is_some' in *.
  repeat rewrite SortedRegEnv.opt_get_map.
  repeat rewrite SortedRegEnv.opt_get_zip_default.
  repeat destruct_match; auto.
Qed.


    (* Lemma oraat_interp_action_correct': *)
    (*   forall fuel *)
    (*     (int_fn_env: int_fn_env_t) *)
    (*     (struct_env: struct_env_t) *)
    (*     (ext_sigma: ext_sigma_t) *)
    (*     (st: state_t) *)
    (*     (sched_log: Log_t) opt_res gamma *)
    (*     fn_depth action (action_log: Log_t) taint_env ext_fn_taint taint_env' ext_fn_taint' n *)
    (*     reg_types ext_fn_types var_types max_fn_id, *)
    (*     taint_env_approximates_log taint_env action_log.(Log__koika) -> *)
    (*     (* ext_fn_taint_env_approximates_log ext_fn_taint (Log__ext sched_log) -> *) *)
    (*     ext_fn_taint_env_approximates_log ext_fn_taint action_log.(Log__ext) -> *)
    (*     taint_action int_fn_env fuel taint_env action = Success (Some taint_env') -> *)
    (*     ext_fn_taint_action int_fn_env fuel ext_fn_taint action = Success (Some ext_fn_taint') -> *)
    (*     interp_action ext_sigma int_fn_env struct_env fuel fn_depth *)
    (*                   st gamma sched_log action_log action = Success opt_res -> *)
    (*     WF_ext_sigma ext_fn_types ext_sigma -> *)
    (*     WF_state reg_types st -> *)
    (*     WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env -> *)
    (*     typecheck' reg_types ext_fn_types int_fn_env struct_env max_fn_id var_types action = Success n -> *)
    (*     taint_env_does_not_conflict (log_to_taint_env sched_log.(Log__koika)) taint_env' -> *)
    (*     ext_taint_env_does_not_conflict (ext_log_to_ext_fn_taint_env (Log__ext sched_log)) ext_fn_taint' -> *)
    (*     is_success (typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env) = true -> *)
    (*     match opt_res with *)
    (*     | Some (gamma', log', v) => *)
    (*       oraat_interp_action ext_sigma int_fn_env struct_env fuel *)
    (*                          (commit_update st sched_log.(Log__koika)) *)
    (*                          (commit_update st (log_app action_log.(Log__koika) sched_log.(Log__koika))) *)
    (*                          action_log.(Log__ext) *)
    (*                          true gamma action *)
    (*        = (true, Some (gamma', commit_update st (log_app log'.(Log__koika) sched_log.(Log__koika)), *)
    (*                               log'.(Log__ext), v)) /\ *)
    (*        taint_env_approximates_log taint_env' log'.(Log__koika) /\ *)
    (*        ext_fn_taint_env_approximates_log ext_fn_taint' log'.(Log__ext) *)
    (*     | None => *)
    (*      oraat_interp_action ext_sigma int_fn_env struct_env fuel *)
    (*                          (commit_update st sched_log.(Log__koika)) *)
    (*                          (commit_update st (log_app action_log.(Log__koika) sched_log.(Log__koika))) *)
    (*                          action_log.(Log__ext) *)
    (*                          true gamma action = (true, None) *)
    (*     end. *)
    (* Proof. *)
    (*   induction fuel; cbn; [discriminate |]. *)
    (*   destruct action; simpl;  unfold __debug__, unsafe_varenv_lookup_var, get_fn_arg_and_body''. *)
    (*   all: intros action_log taint_env ext_fn_taint taint_env' ext_fn_taint' n *)
    (*               reg_types ext_fn_types var_types max_fn_id *)
    (*               Htaint_eq (* Hext_taint_sched *) Hext_taint_action Hext_taint_eq Htaint_action Hinterp *)
    (*               Hwf_ext Hwf_state Hwf_fns Htype Hconflict Hconflict_ext Hint_fns; simplify; try simplify_res_opt_bind; auto; *)
    (*        specialize IHfuel with (12 := Hint_fns) (6 := Hwf_ext) (* (2 := Hext_taint_sched) *). *)
    (*   all: t_oraat_interp_action_correct' IHfuel. *)
    (*   - destruct_matches_in_hyp Hinterp; simplify. *)
    (*     destruct_matches_in_hyp Hinterp; simplify. *)
    (*     + t_oraat_interp_action_correct' IHfuel. *)
    (*       rewrite Hinterp1. split_ands_in_goal; auto; *)
    (*       t_oraat_interp_action_correct' IHfuel. *)
    (*     + t_oraat_interp_action_correct' IHfuel; eauto. *)
    (*       split_ands_in_goal;  t_oraat_interp_action_correct' IHfuel. *)
    (*   - destruct port. *)
    (*     + t_oraat_interp_action_correct' IHfuel. *)
    (*       bash_destruct Hinterp; simplify. *)
    (*       * simpl. erewrite is_success_commit_update; eauto. *)
    (*         unfold r_get_reg in Heqr0; simplify. *)
    (*         split. *)
    (*         { simpl. f_equal. f_equal. repeat rewrite pair_equal_spec; split_ands_in_goal; auto. *)
    (*           { apply state_ext. *)
    (*             intros. *)
    (*             destruct_with_eqn (beq_dec reg idx); simplify; subst. *)
    (*             { repeat rewrite getenv_commit_wf by (unfold get_reg, is_some'; simpl_match; auto). *)
    (*               repeat rewrite get_log_app. *)
    (*               repeat rewrite log_set_eq. reflexivity. *)
    (*             } *)
    (*             { repeat rewrite getenv_commit. *)
    (*               repeat rewrite get_log_app. *)
    (*               rewrite log_set_neq by auto. *)
    (*               reflexivity. *)
    (*             } *)
    (*           } *)
    (*           { unfold LE_may_read0 in *. *)
    (*             unfold commit_update, r_get_reg, latest_write. *)
    (*             rewrite SortedRegEnv.opt_get_map. *)
    (*             bash_destruct Heqb.  consider log_get. *)
    (*             repeat simpl_match; auto. *)
    (*           } *)
    (*         } *)
    (*         { split; auto. *)
    (*           apply taint_env_approximates_log_set__read0; auto. *)
    (*         } *)
    (*       * exfalso. clear IHfuel. *)
    (*         consider taint_env_does_not_conflict. specialize Hconflict with (reg := idx). *)
    (*         erewrite taint_conflicts_read0 in Hconflict; eauto; [ discriminate | ]. *)
    (*         apply taint_env_approximates_log_refl. *)
    (*     + t_oraat_interp_action_correct' IHfuel. *)
    (*       destruct (LE_may_read1 _) eqn:? in Hinterp. *)
    (*       * bash_destruct Heqb. *)
    (*         erewrite is_success_commit_update; eauto. *)
    (*         destruct_match; [ | subst; bash_destruct Hinterp; simplify]. *)
    (*         destruct_match_pairs; subst. *)
    (*         match_outermost_in Hinterp; simplify; try discriminate. *)
    (*         split. *)
    (*         { f_equal. f_equal.  simpl. *)
    (*           repeat rewrite pair_equal_spec; split_ands_in_goal; auto. *)
    (*           { apply state_ext. *)
    (*             intros. repeat rewrite get_log_app. *)
    (*             destruct_with_eqn (beq_dec idx reg); simplify; subst. *)
    (*             { repeat rewrite getenv_commit_wf by (unfold r_get_reg, get_reg, is_some' in *; simplify; auto). *)
    (*               repeat rewrite get_log_app. repeat rewrite log_set_eq. reflexivity. *)
    (*             } *)
    (*             { repeat rewrite getenv_commit. *)
    (*               repeat rewrite get_log_app. *)
    (*               rewrite log_set_neq by auto. *)
    (*               reflexivity. *)
    (*             } *)
    (*           } *)
    (*           { unfold r_get_reg, commit_update, __debug__, latest_write. *)
    (*             repeat rewrite get_log_app. simpl. consider LE_may_read1. *)
    (*             repeat rewrite SortedRegEnv.opt_get_map. *)
    (*             bash_destruct Hext_taint_eq; simplify. *)
    (*             unfold r_get_reg in *. simplify; simpl. *)
    (*             rewrite get_log_app. simpl. *)
    (*             repeat match goal with *)
    (*                    | H: ?x = _ |- context[opt_or ?x _ ] => rewrite H *)
    (*                    | H: ?x = _ |- context[opt_or _ ?x ] => rewrite H *)
    (*                    end; repeat simpl_match; auto. *)
    (*             rewrite opt_or_None_r. *)
    (*             destruct_match; simplify. *)
    (*             - specialize conflicts_with_read1_false_implies_no_write1 with (1 := Heqb0) (2 := Htaint_eq); intros. *)
    (*               congruence. *)
    (*             - bash_destruct Heqr1; simplify; auto. *)
    (*           } *)
    (*         } *)
    (*         { bash_destruct Hext_taint_eq; simplify; simpl. split; auto. *)
    (*           eapply taint_env_approximates_log_set__read1; auto. *)
    (*         } *)
    (*      * exfalso. clear IHfuel. simplify. bash_destruct Hext_taint_eq; simplify. *)
    (*         consider taint_env_does_not_conflict. specialize Hconflict with (reg := idx); eauto. *)
    (*         erewrite taint_conflicts_read1 in Hconflict; eauto; [discriminate |]. *)
    (*         apply taint_env_approximates_log_refl. *)
    (*   - destruct port. *)
    (*     + t_oraat_interp_action_correct' IHfuel; bash_destruct Hext_taint_eq; simplify; *)
    (*       t_oraat_interp_action_correct' IHfuel. *)
    (*       destruct_match; subst; bash_destruct Hinterp; simplify. *)
    (*       * apply andb_true_iff in Heqb0; propositional. *)
    (*         split. *)
    (*         { f_equal. f_equal.  simpl. *)
    (*           repeat rewrite pair_equal_spec; split_ands_in_goal; auto. *)
    (*           apply state_ext. *)
    (*           consider LE_may_write0; simplify. *)
    (*           unfold WF_state in *. *)
    (*           intros reg. *)
    (*           specialize (Hwf_state reg); unfold lookup_reg_type in *; simplify. *)
    (*           destruct_with_eqn (beq_dec reg idx); simplify; subst. *)
    (*           all: repeat rewrite get_set_reg; *)
    (*                repeat rewrite get_set_reg_neq by auto; *)
    (*                repeat rewrite getenv_commit; *)
    (*                repeat rewrite get_log_app; *)
    (*                repeat rewrite log_set_eq; *)
    (*                repeat rewrite log_set_neq by auto; repeat simpl_match; simplify. *)
    (*           - unfold latest_write; simpl. *)
    (*             repeat match goal with *)
    (*             | H: ?x = _ |- context[opt_or ?x _ ] => rewrite H *)
    (*             | H: ?x = _ |- context[opt_or _ ?x ] => rewrite H *)
    (*             end; try reflexivity. *)
    (*           - destruct_match; auto. *)
    (*         } *)
    (*         { split; auto. eapply taint_env_approximates_log_set__write0; auto. } *)
    (*       * exfalso. clear IHfuel. *)
    (*         consider taint_env_does_not_conflict. specialize Hconflict with (reg := idx); eauto. *)
    (*         apply andb_false_iff in Heqb0. *)
    (*         destruct Heqb0. *)
    (*         { erewrite taint_conflicts_write0 in Hconflict; eauto; [discriminate | ]. *)
    (*           apply taint_env_approximates_log_refl. *)
    (*         } *)
    (*         { erewrite taint_conflicts_write0' in Hconflict; eauto. discriminate. } *)
    (*     + t_oraat_interp_action_correct' IHfuel; bash_destruct Hext_taint_eq; simplify; *)
    (*       t_oraat_interp_action_correct' IHfuel. *)
    (*       destruct_match; subst; bash_destruct Hinterp; simplify. *)
    (*       * apply andb_true_iff in Heqb0; propositional. *)
    (*         split; simpl. *)
    (*         { f_equal. f_equal. *)
    (*           repeat rewrite pair_equal_spec; split_ands_in_goal; auto. *)
    (*           apply state_ext; intros. *)
    (*           consider LE_may_write1. simplify. *)
    (*           unfold WF_state in *. *)
    (*           specialize (Hwf_state reg); unfold lookup_reg_type in *; simplify. *)
    (*           destruct_with_eqn (beq_dec reg idx); simplify; subst. *)
    (*           all: repeat rewrite get_set_reg; *)
    (*                repeat rewrite get_set_reg_neq by auto; *)
    (*                repeat rewrite getenv_commit; *)
    (*                repeat rewrite get_log_app; *)
    (*                repeat rewrite log_set_eq; *)
    (*                repeat rewrite log_set_neq by auto; repeat simpl_match; simplify. *)
    (*           - unfold latest_write; simpl. *)
    (*             repeat match goal with *)
    (*             | H: ?x = _ |- context[opt_or ?x _ ] => rewrite H *)
    (*             | H: ?x = _ |- context[opt_or _ ?x ] => rewrite H *)
    (*             end; try reflexivity. *)
    (*           - destruct_match; auto. *)
    (*         } *)
    (*         { split; auto. eapply taint_env_approximates_log_set__write1; auto. } *)
    (*       * exfalso. clear IHfuel. *)
    (*         consider taint_env_does_not_conflict. specialize Hconflict with (reg := idx); eauto. *)
    (*         apply andb_false_iff in Heqb0. *)
    (*         destruct Heqb0. *)
    (*         { erewrite taint_conflicts_write1 in Hconflict; eauto; [discriminate | ]. *)
    (*           apply taint_env_approximates_log_refl. *)
    (*         } *)
    (*         { erewrite taint_conflicts_write1' in Hconflict; eauto. discriminate. } *)
    (*   - rewrite_solve. *)
    (*   - simpl in *. simplify_tupless. *)
    (*     unfold is_success in Hint_fns. simplify. *)
    (*     specialize typecheck_int_fns'_Success with (1 := Heqr4) (2 := Heqr0). propositional. *)
    (*     t_oraat_interp_action_correct' IHfuel. *)
    (*   - simplify. *)
    (*     bash_destruct Hinterp; simplify; simpl. *)
    (*     + split_ands_in_goal; auto. *)
    (*       assert (ext_fn_taint' = (SortedExtFnEnv.update e fn (fun _ : bool => true) false)) *)
    (*              by (bash_destruct Htaint_action); subst. *)
    (*       apply ext_fn_taint_env_approximates_log_update; auto. *)
    (*     + exfalso. *)
    (*       rewrite andb_false_iff in Heqb. *)
    (*       consider ext_log_can_call. *)
    (*       split_ors_in Heqb. *)
    (*       * bash_destruct Heqb. *)
    (*         assert (ext_taint_env_does_not_conflict (ext_log_to_ext_fn_taint_env (Log__ext sched_log)) ext_fn_taint'). *)
    (*         { t_oraat_interp_action_correct' IHfuel. } *)

    (*         assert (ext_fn_taint' = (SortedExtFnEnv.update e fn (fun _ : bool => true) false)) by (bash_destruct Htaint_action); subst. *)
    (*         specialize ext_fn_taint_env_does_not_conflict_log_to_taint with (1 := H1) (2 := Heqo). *)
    (*         rewrite SortedExtFnEnv.update_correct_eq; propositional; simplify. bash_destruct Htaint_action. *)
    (*       * bash_destruct Heqb. *)
    (*         specialize ext_fn_taint_env_approximates_log_implies with (1 := Heqo) (2 := Hinterp3); intros; simpl_match. *)
    (*         discriminate. *)
    (*   - assert (ext_fn_taint' = (SortedExtFnEnv.update e fn (fun _ : bool => true) false)) *)
    (*       by (bash_destruct Htaint_action); subst. *)
    (*     t_oraat_interp_action_correct' IHfuel. *)
    (*   - assert (ext_fn_taint' = (SortedExtFnEnv.update e fn (fun _ : bool => true) false)) *)
    (*       by (bash_destruct Htaint_action); subst. *)
    (*     t_oraat_interp_action_correct' IHfuel. *)
    (* Qed. *)
Lemma ext_fn_taint_env_approximates_log_empty:
  ext_fn_taint_env_approximates_log SortedExtFnEnv.empty SortedExtFnEnv.empty.
Proof.
  consider ext_fn_taint_env_approximates_log.
  intros. consider @is_some. propositional. rewrite SortedExtFnEnv.opt_get_empty in H0. discriminate.
Qed.

    (* TODO: ext fns *)
    (* Lemma oraat_interp_rule_correct': *)
    (*   forall (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) *)
    (*     (int_fn_env: int_fn_env_t) *)
    (*     (struct_env: struct_env_t) *)
    (*     (ext_sigma: ext_sigma_t) *)
    (*     (st: state_t) *)
    (*     taint_rule (sched_log: Log_t) opt_res rule rule' ext_fn_taint', *)
    (*     WF_state reg_types st -> *)
    (*     WF_log reg_types sched_log.(Log__koika) -> *)
    (*     WF_ext_sigma ext_fn_types ext_sigma -> *)
    (*     WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env -> *)
    (*     typecheck_rule reg_types ext_fn_types int_fn_env struct_env rule = Success (rule', 0) -> *)
    (*     taint_rule_from_empty int_fn_env rule = Success (Some taint_rule) -> *)
    (*     interp_rule ext_sigma int_fn_env struct_env st sched_log rule = Success opt_res -> *)
    (*     taint_env_does_not_conflict (log_to_taint_env sched_log.(Log__koika)) taint_rule -> *)
    (*     ext_fn_taint_action int_fn_env (safe_fuel int_fn_env rule) SortedExtFnEnv.empty rule = Success (Some ext_fn_taint') -> *)
    (*     ext_taint_env_does_not_conflict (ext_log_to_ext_fn_taint_env (Log__ext sched_log)) ext_fn_taint' -> *)
    (*     match opt_res with *)
    (*     | Some log => *)
    (*       oraat_interp_rule ext_sigma int_fn_env struct_env (commit_update st sched_log.(Log__koika)) rule *)
    (*          = (true, commit_update st (log_app log.(Log__koika) sched_log.(Log__koika)), *)
    (*                   log.(Log__ext)) /\ *)
    (*       taint_env_approximates_log taint_rule log.(Log__koika) *)
    (*     | None => *)
    (*       oraat_interp_rule ext_sigma int_fn_env struct_env (commit_update st sched_log.(Log__koika)) rule *)
    (*          = (true, commit_update st sched_log.(Log__koika), SortedExtFnEnv.empty) *)
    (*     end. *)
    (* Proof. *)
    (*   intros * Hst Hlog Hext_sigma Hint_fn_env Htype Htaint Hinterp Hconflict Hext_fn_taint Hext_conflict. *)
    (*   unfold oraat_interp_rule, interp_rule, taint_rule_from_empty, typecheck_rule in *. *)
    (*   destruct_match. simplify. *)
    (*   + eapply oraat_interp_action_correct' in Heqr; eauto with WF_auto. *)
    (*     - rewrite log_app_empty_l in *.  simpl in *. *)
    (*       rewrite Heqp in *. propositional. simplify; auto. *)
    (*     - apply taint_env_approximates_log_empty. *)
    (*     - simpl. apply ext_fn_taint_env_approximates_log_empty. *)
    (*   + bash_destruct Hinterp. simplify. *)
    (*     eapply oraat_interp_action_correct' in Heqr; eauto with WF_auto. *)
    (*     - rewrite log_app_empty_l in *. simpl in *. rewrite Heqr in Heqp. simplify_tupless. *)
    (*       reflexivity. *)
    (*     - apply taint_env_approximates_log_empty. *)
    (*     - simpl. apply ext_fn_taint_env_approximates_log_empty. *)
    (* Qed. *)

    (* Lemma oraat_interp_rule_correct: *)
    (*   forall (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) *)
    (*     (int_fn_env: int_fn_env_t) *)
    (*     (struct_env: struct_env_t) *)
    (*     (ext_sigma: ext_sigma_t) *)
    (*     (st: state_t) *)
    (*     taint_rule (sched_log: Log_t) opt_res rule rule' ext_fn_taint', *)
    (*     WF_state reg_types st -> *)
    (*     WF_log reg_types sched_log.(Log__koika) -> *)
    (*     WF_ext_sigma ext_fn_types ext_sigma -> *)
    (*     WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env -> *)
    (*     typecheck_rule reg_types ext_fn_types int_fn_env struct_env rule = Success (rule', 0) -> *)
    (*     taint_rule_from_empty int_fn_env rule = Success (Some taint_rule) -> *)
    (*     interp_rule ext_sigma int_fn_env struct_env st sched_log rule = Success opt_res -> *)
    (*     taint_env_does_not_conflict (log_to_taint_env sched_log.(Log__koika)) taint_rule -> *)
    (*     ext_taint_env_does_not_conflict (ext_log_to_ext_fn_taint_env (Log__ext sched_log)) ext_fn_taint' -> *)
    (*     ext_fn_taint_action int_fn_env (safe_fuel int_fn_env rule) SortedExtFnEnv.empty rule = *)
    (*       Success (Some ext_fn_taint') -> *)
    (*     oraat_interp_rule ext_sigma int_fn_env struct_env (commit_update st sched_log.(Log__koika)) rule *)
    (*       = (true, match opt_res with *)
    (*                | Some log => commit_update st (log_app log.(Log__koika) sched_log.(Log__koika)) *)
    (*                | None => commit_update st sched_log.(Log__koika) *)
    (*                end, *)
    (*                match opt_res with *)
    (*                | Some log => log.(Log__ext) *)
    (*                | None => SortedExtFnEnv.empty *)
    (*                end). *)
    (* Proof. *)
    (*   intros * Hst Hlog Hext_sigma Hint_fn_env Htype Htaint Hinterp Hconflict Hext_conflict hext_action. *)
    (*   eapply oraat_interp_rule_correct' in Hinterp; eauto. *)
    (*   bash_destruct Hinterp; propositional. *)
    (* Qed. *)

    Lemma taint_env_approximates_log_add_taints:
      forall taint log taint',
        taint_env_approximates_log taint log ->
        taint_env_approximates_log (merge_taint_env taint taint') log.
    Proof.
      intros. consider taint_env_approximates_log. consider merge_taint_env.
      intros. unfold get_reg_taint_default in *.
      rewrite SortedRegEnv.opt_get_mapV.
      rewrite SortedRegEnv.opt_get_zip_default.
      specialize H with (reg := reg).
      repeat destruct_match; auto.
      - unfold merge_taints, taint_approximates_log_entry in *.
        destruct H. constructor; propositional; simpl; try rewrite_solve.
      - unfold merge_taints. simpl. repeat rewrite orb_false_r. destruct t; auto.
      - unfold merge_taints. simpl. destruct t; simpl.
        unfold taint_approximates_log_entry in *.
        destruct H; simpl in *.
        constructor; simpl; propositional; discriminate.
    Qed.

Lemma log_app_Log_app__koika:
  forall l1 l2,
  log_app (Log__koika l1) (Log__koika l2) = (Log_app l1 l2).(Log__koika).
Proof.
  unfold Log_app; auto.
Qed.

Lemma log_empty_Log_empty:
  log_empty = Log__koika Log_empty.
Proof.
  reflexivity.
Qed.
Lemma ext_log_app_empty_l:
  forall log, ext_log_app SortedExtFnEnv.empty log = log.
Proof.
  intros. apply SortedExtFnEnv.env_ext.
  unfold ext_log_app. intros. rewrite SortedExtFnEnv.opt_get_mapV.
  rewrite SortedExtFnEnv.opt_get_zip_default.
  rewrite SortedExtFnEnv.opt_get_empty.
  destruct_match; auto.
Qed.

    (* Lemma oraat_interp_schedule'_correct: *)
    (*   forall {rule_name_t: Type} (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) *)
    (*     (int_fn_env: int_fn_env_t) *)
    (*     (struct_env: struct_env_t) *)
    (*     (ext_sigma: ext_sigma_t) *)
    (*     (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t) *)
    (*     taint taint' sched_log log, *)
    (*     WF_state reg_types st -> *)
    (*     WF_ext_log ext_fn_types sched_log.(Log__ext) -> *)
    (*     WF_log reg_types sched_log.(Log__koika) -> *)
    (*     WF_ext_sigma ext_fn_types ext_sigma -> *)
    (*     WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env -> *)
    (*     typecheck_schedule reg_types ext_fn_types int_fn_env struct_env s rls = Success tt -> *)
    (*     taint_env_approximates_log taint sched_log.(Log__koika) -> *)
    (*     (* ext_fn_taint_rule int_fn_env SortedExtFnEnv.empty (rls r) = Success (Some ext_fn_taint') -> *) *)
    (*     (* ext_taint_env_does_not_conflict (ext_log_to_ext_fn_taint_env (Log__ext sched_log)) ext_fn_taint' -> *) *)
    (*     interp_taint_scheduler' int_fn_env rls s taint = Success (Some taint') -> *)
    (*     interp_scheduler' ext_sigma int_fn_env struct_env st rls s sched_log = Success log -> *)
    (*     oraat_interp_scheduler' ext_sigma int_fn_env struct_env rls (commit_update st sched_log.(Log__koika)) sched_log.(Log__ext) true s = (true, commit_update st log.(Log__koika), log.(Log__ext)). *)
    (* Proof. *)
    (*   induction s. *)
    (*   - simpl; intros; simplify. reflexivity. *)
    (*   - intros * Hst Hext_log Hlog Hext_sigma Hint_fn_env Htype Htaint Happrox Hinterp. *)
    (*     simpl in *. simplify. bash_destruct Htaint. *)
    (*     bash_destruct Happrox. *)
    (*     destruct_matches_in_hyp Hinterp; subst. *)
    (*     + pose proof Heqr0 as Hrule. simplify_res_opt_bind. bash_destruct Happrox. *)
    (*       eapply oraat_interp_rule_correct' in Heqr0; eauto. *)
    (*       * rewrite Heqp in Heqr0. propositional. simplify_tupless. *)
    (*         rewrite log_app_Log_app__koika. *)
    (*         eapply IHs; eauto. *)
    (*         { apply WF_ext_log_app; auto. *)
    (*           eapply typecheck_rule_correct in Heqr1; eauto; simpl_match; propositional. *)
    (*         } *)
    (*         { apply WF_log_app; auto. *)
    (*           eapply typecheck_rule_correct in Heqr1; eauto; simpl_match; propositional. *)
    (*         } *)
    (*         { eapply taint_env_approximates_append; eauto. } *)
    (*       * eapply does_not_conflict_equiv. *)
    (*         eapply taint_env_approximates_does_not_conflict; eauto. *)
    (*       * admit. *)
    (*       * admit. *)
    (*     + simplify_res_opt_bind. bash_destruct Happrox. *)
    (*       erewrite oraat_interp_rule_correct in Heqp; simplify_tupless; eauto. *)
    (*       * simpl in *. subst. *)
    (*         rewrite ext_log_app_empty_l in *. *)
    (*         eapply IHs with (taint := merge_taint_env taint t); eauto. *)
    (*         apply taint_env_approximates_log_add_taints. assumption. *)
    (*       * eapply does_not_conflict_equiv. *)
    (*         eapply taint_env_approximates_does_not_conflict; eauto. *)
    (*       * admit. *)
    (*       * admit. *)
    (* Admitted. *)

    (* Lemma oraat_interp_scheduler_correct: *)
    (*   forall {rule_name_t: Type} (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) *)
    (*     (int_fn_env: int_fn_env_t) *)
    (*     (struct_env: struct_env_t) *)
    (*     (ext_sigma: ext_sigma_t) *)
    (*     (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t) *)
    (*     taint taint' log, *)
    (*     WF_state reg_types st -> *)
    (*     WF_ext_sigma ext_fn_types ext_sigma -> *)
    (*     WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env -> *)
    (*     typecheck_schedule reg_types ext_fn_types int_fn_env struct_env s rls = Success tt -> *)
    (*     interp_taint_scheduler' int_fn_env rls s taint = Success (Some taint') -> *)
    (*     interp_scheduler' ext_sigma int_fn_env struct_env st rls s sched_log = Success log -> *)
    (*     oraat_interp_scheduler' ext_sigma int_fn_env struct_env rls (commit_update st sched_log.(Log__koika)) sched_log.(Log__ext) true s = (true, commit_update st log.(Log__koika), log.(Log__ext)). *)

    (* Lemma oraat_interp_scheduler_correct: *)
    (*   forall {rule_name_t: Type} (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) *)
    (*     (int_fn_env: int_fn_env_t) *)
    (*     (struct_env: struct_env_t) *)
    (*     (ext_sigma: ext_sigma_t) *)
    (*     (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t) log', *)
    (*     WF_state reg_types st -> *)
    (*     WF_ext_sigma ext_fn_types ext_sigma -> *)
    (*     WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env -> *)
    (*     typecheck_schedule reg_types ext_fn_types int_fn_env struct_env s rls = Success tt -> *)
    (*     schedule_does_not_conflict int_fn_env rls s = Success true -> *)
    (*     interp_scheduler ext_sigma int_fn_env struct_env st rls s = Success log' -> *)
    (*     oraat_interp_scheduler ext_sigma int_fn_env struct_env rls st s = (true, commit_update st log'.(Log__koika), log'.(Log__ext)). *)
    (* Proof. *)
    (*   unfold oraat_interp_scheduler, interp_scheduler, schedule_does_not_conflict in *. *)
    (*   intros * Hst Hext_sigma Hint_fn_env Htype Hconflict Hsched. simplify. *)
    (*   bash_destruct Hconflict. *)
    (*   unfold interp_taint_schedule, interp_scheduler, oraat_interp_scheduler in *. *)
    (*   specialize @oraat_interp_schedule'_correct with (8 := Heqr) (9 := Hsched) *)
    (*                                                   (reg_types := reg_types) (ext_fn_types := ext_fn_types). *)
    (*   intros Hcorrect. *)
    (*   propositional; simpl in *. *)
    (*   rewrite commit_update_empty in *. *)
    (*   eapply Hcorrect; auto with WF_auto. *)
    (*   apply taint_env_approximates_log_empty. *)
    (* Qed. *)

    (* Lemma oraat_interp_cycle_correct: *)
    (*   forall {rule_name_t: Type} (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) *)
    (*     (int_fn_env: int_fn_env_t) *)
    (*     (struct_env: struct_env_t) *)
    (*     (ext_sigma: ext_sigma_t) *)
    (*     (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t), *)
    (*     WF_state reg_types st -> *)
    (*     WF_ext_sigma ext_fn_types ext_sigma -> *)
    (*     WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env -> *)
    (*     typecheck_schedule reg_types ext_fn_types int_fn_env struct_env s rls = Success tt -> *)
    (*     schedule_does_not_conflict int_fn_env rls s = Success true -> *)
    (*     interp_cycle ext_sigma int_fn_env struct_env st rls s = *)
    (*       Success (fst(unsafe_oraat_interp_cycle ext_sigma int_fn_env struct_env rls st s)). *)
    (* Proof. *)
    (*   intros * Hst Hext_sigma Hint_fn_env Htype Hconflict. *)
    (*   unfold interp_cycle, unsafe_oraat_interp_cycle, schedule_does_not_conflict in *. *)
    (*   bash_destruct Hconflict. *)
    (*   unfold interp_taint_schedule, interp_scheduler, oraat_interp_scheduler in *. *)
    (*   destruct_match. *)
    (*   - rewrite<-commit_update_empty with (st := st). *)
    (*     rewrite log_empty_Log_empty. *)
    (*     erewrite @oraat_interp_schedule'_correct; eauto with WF_auto. *)
    (*     rewrite commit_update_empty. reflexivity. *)
    (*     apply taint_env_approximates_log_empty. *)
    (*   - eapply typecheck_schedule_correct'_log with (sched_log := Log_empty) in Htype; eauto with WF_auto. *)
    (*     simplify. *)
    (* Qed. *)
    (* Lemma oraat_interp_cycle'_correct: *)
    (*   forall {rule_name_t: Type} (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t) *)
    (*     (int_fn_env: int_fn_env_t) *)
    (*     (struct_env: struct_env_t) *)
    (*     (ext_sigma: ext_sigma_t) *)
    (*     (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t), *)
    (*     WF_state reg_types st -> *)
    (*     WF_ext_sigma ext_fn_types ext_sigma -> *)
    (*     WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env -> *)
    (*     typecheck_schedule reg_types ext_fn_types int_fn_env struct_env s rls = Success tt -> *)
    (*     schedule_does_not_conflict int_fn_env rls s = Success true -> *)
    (*     interp_cycle' ext_sigma int_fn_env struct_env st rls s = *)
    (*       Success (unsafe_oraat_interp_cycle ext_sigma int_fn_env struct_env rls st s). *)
    (* Proof. *)
    (*   intros * Hst Hext_sigma Hint_fn_env Htype Hconflict. *)
    (*   unfold interp_cycle', unsafe_oraat_interp_cycle, schedule_does_not_conflict in *. *)
    (*   bash_destruct Hconflict. *)
    (*   unfold interp_taint_schedule, interp_scheduler, oraat_interp_scheduler in *. *)
    (*   destruct_match. *)
    (*   - rewrite<-commit_update_empty with (st := st). *)
    (*     rewrite log_empty_Log_empty. *)
    (*     erewrite @oraat_interp_schedule'_correct; eauto with WF_auto. *)
    (*     rewrite commit_update_empty. reflexivity. *)
    (*     apply taint_env_approximates_log_empty. *)
    (*   - eapply typecheck_schedule_correct'_log with (sched_log := Log_empty) in Htype; eauto with WF_auto. *)
    (*     simplify. *)
    (* Qed. *)


    Lemma WF_gamma_length:
      forall gamma var_types var n value {A} (msg: A),
        WF_gamma var_types gamma ->
        varenv_lookup_var var_types var msg = Success n ->
        varenv_lookup_var gamma var msg = Success value ->
        Datatypes.length value = n.
    Proof.
      induction gamma; intros * Hwf Htype Hvar; unfold WF_gamma, varenv_lookup_var in *; simplify.
      - inversions Hwf. simpl in *. discriminate.
      - simpl in *. inversions Hwf. destruct_match_pairs. propositional.
        destruct_matches_in_hyp Heqo; simplify.
        + apply String.eqb_eq in Heqb; subst. simpl in *. rewrite String.eqb_refl in Heqo0. simplify.
          reflexivity.
        + simpl in *. simpl_match. eapply IHgamma with (var := var) (msg := tt); eauto; simpl_match; auto.
    Qed.

    Lemma WF_gamma_update':
      forall gamma v l var_types {A} (msg: A),
        WF_gamma var_types gamma ->
        varenv_lookup_var var_types v msg = Success (Datatypes.length l) ->
        WF_gamma var_types (varenv_update gamma v l).
    Proof.
      induction gamma; unfold WF_gamma, varenv_lookup_var in *.
      - intros. inversions H. simpl in *. discriminate.
      - intros. inversions H. simplify. propositional.
        simpl in *. unfold varenv_update. simpl. destruct_match; simplify.
        + apply String.eqb_eq in Heqb. simplify.
          constructor; auto.
        + constructor; auto.
          eapply IHgamma with (msg := tt); auto. simpl_match; auto.
    Qed.

    Lemma WF_state_length:
      forall reg_types idx st v n,
        WF_state reg_types st ->
        lookup_reg_type reg_types idx tt = Success n ->
        r_get_reg st idx = Success v ->
        Datatypes.length v = n.
    Proof.
      unfold WF_state, lookup_reg_type, r_get_reg, get_reg.
      intros. specialize (H idx). simplify.
      reflexivity.
    Qed.

    Lemma WF_state_set:
      forall reg_types st idx v,
        WF_state reg_types st ->
        lookup_reg_type reg_types idx tt = Success (Datatypes.length v) ->
        WF_state reg_types (state_set st idx v).
    Proof.
      unfold WF_state, lookup_reg_type, get_reg.
      intros. destruct_match; auto. specialize (H reg).
      destruct_with_eqn (beq_dec reg idx); simplify.
      - unfold state_set. rewrite SortedRegEnv.update_correct_eq.  destruct_match; auto.
      - unfold state_set. rewrite SortedRegEnv.update_correct_neq by auto.
        simpl_match. destruct_match; auto.
    Qed.

    Lemma WF_sigma_length:
      forall ext_fn_types sigma fn v v' n,
        WF_ext_sigma ext_fn_types sigma ->
        sigma fn v = Success v' ->
        lookup_ext_fn_type ext_fn_types fn tt = Success (Datatypes.length v, n) ->
        Datatypes.length v' = n.
    Proof.
      unfold WF_ext_sigma, lookup_ext_fn_type.
      intros. specialize (H fn). simplify.
      unfold OrderedN.T in *.
      unfold AnnotatedSyntax.ext_fn_t in *.
      unfold ext_fn_t in *.
      simpl_match. specialize H with (1 := eq_refl).
      simplify. reflexivity.
    Qed.

    Lemma WF_gamma_bind:
      forall var_types gamma v l,
        WF_gamma var_types gamma ->
        WF_gamma (varenv_bind var_types v (Datatypes.length l)) (varenv_bind gamma v l).
    Proof.
      intros. constructor; auto.
    Qed.

    Lemma WF_gamma_tl:
      forall var_types length var gamma,
        WF_gamma (varenv_bind var_types var length) gamma ->
        WF_gamma var_types (tl gamma).
    Proof.
      intros. inversions H. auto.
    Qed.

    Hint Resolve @WF_gamma_length : WF_auto.
    Hint Resolve @WF_gamma_update: WF_auto.
    Hint Resolve @WF_gamma_update' : WF_auto.
    Hint Resolve @WF_gamma_bind : WF_auto.
    Hint Resolve @WF_gamma_tl : WF_auto.

    Hint Resolve @WF_state_length : WF_auto.
    Hint Resolve @WF_state_set : WF_auto.
    Hint Resolve @WF_fn_arg_gamma: WF_auto.
    Hint Resolve @WF_sigma_length: WF_auto.

    Lemma oraat_interp_scheduler'_is_safe_generalizes:
      forall {rule_name_t} (rules: rule_name_t -> rule) sched
        sigma int_fn_env struct_env  st b st' ext_log ext_log',
      oraat_interp_scheduler' sigma int_fn_env struct_env rules st ext_log b sched = (true, st', ext_log') ->
      b = true.
    Proof.
      induction sched.
      - simpl. intros; simplify_tupless; auto.
      - intros. simpl in H. destruct_match_pairs.
        eapply IHsched in H; subst.
        apply andb_true_iff in H. propositional.
    Qed.

    Lemma oraat_interp_action_is_safe_generalizes:
      forall (fuel: nat) action sigma int_fn_env struct_env st0 st1 is_safe gamma ret ext_log ,
        oraat_interp_action sigma int_fn_env struct_env fuel st0 st1 ext_log is_safe gamma action =
          (true, ret) ->
        is_safe = true.
    Proof.
      induction fuel; cbn; [discriminate | ].
      destruct action; simpl in *. intros.
      all: repeat match goal with
           | |- _ => progress (simplify; simplify_tupless; propositional)
           | H: _ && _ = true |- _ =>
             apply andb_true_iff in H
           | H: match _ with | _ => _ end = _ |- _ =>
             bash_destruct H
           | H: oraat_interp_action _ _ _ _ _ _ _ _ _ _ = (true, _) |- _ =>
             eapply IHfuel in H; eauto
           | |- _ => discriminate || reflexivity || assumption || solve[auto]
           end.
    Qed.

    Lemma oraat_interp_action_safety:
      forall fuel reg_types var_types ext_fn_types
        sigma int_fn_env struct_env st0 st1 st2 is_safe gamma gamma' v n max_fn_id action ext_log ext_log' rule',
        WF_state reg_types st0 ->
        WF_state reg_types st1 ->
        WF_gamma var_types gamma ->
        WF_ext_sigma ext_fn_types sigma ->
        WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
        typecheck' reg_types ext_fn_types int_fn_env struct_env max_fn_id var_types action = Success (rule', n) ->
        is_success (typecheck_int_fns' reg_types ext_fn_types int_fn_env struct_env) = true  ->
        oraat_interp_action sigma int_fn_env struct_env fuel st0 st1 ext_log is_safe gamma action =
          (true, Some (gamma', st2, ext_log', v)) ->
        WF_gamma var_types gamma' /\
        WF_state reg_types st2 /\
        List.length v = n /\
        is_safe = true.
    Proof.
      induction fuel; cbn; [discriminate |].
      simpl; unfold __debug__ in *.
      all: intros *; destruct action; intros Hwf_st0 Hwf_st1 Hwf_gamma Hwf_sigma Hwf_fns Htype Hint_fns Hinterp; simpl in *;
            unfold __debug__, is_success, lookup_var_type in *;
            specialize IHfuel with (7 := Hint_fns).

      Ltac t_oraat_interp_action_safety IHfuel :=
        repeat match goal with
           | |- _ => progress (simplify; simplify_tupless; propositional)
           | H: match _ with | Some _ => _ | None => (_, None) end = (_, Some _) |- _ =>
             destruct_matches_in_hyp H; try destruct_match_pairs; subst;
               [ | simplify_tupless; discriminate]
           | H: _ && _ = true |- _ =>
             apply andb_true_iff in H
           | H : oraat_interp_action _ _ _ _ _ _ _ true _ _ = (true, _) |- _ =>
             eapply IHfuel in H;
               [ | solve[eauto] | solve[eauto] | solve[eauto]| solve[eauto]|
                   solve[eauto]| solve[eauto]]
           | H : oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
             match b with
             | true => fail
             | _ => let H' := fresh in
                   assert (b = true) as H' by (eapply oraat_interp_action_is_safe_generalizes in H; eauto); rewrite H' in *
             end
           | |- _ => discriminate || reflexivity || assumption || solve[eauto with WF_auto]
           end.
        all: t_oraat_interp_action_safety IHfuel.

      - destruct_matches_in_hyp Hinterp;
        t_oraat_interp_action_safety IHfuel.
      - eapply IHfuel in Heqp3; eauto; t_oraat_interp_action_safety IHfuel.
      - destruct_matches_in_hyp Hinterp;
          t_oraat_interp_action_safety IHfuel.
      - apply typecheck_zop_correct in Heqr0 . simplify; auto.
      - apply typecheck_unop_correct in Heqr1; simplify; auto.
      - apply typecheck_binop_correct in Heqr2; simplify; auto.
      - pose proof Hwf_fns as Hwf_fns'; unfold get_fn_arg_and_body'' in *. simpl in *.
        t_oraat_interp_action_safety IHfuel.
        eapply typecheck_int_fns'_Success in Heqr ; eauto. propositional.
        eapply IHfuel in Heqp4; eauto; t_oraat_interp_action_safety IHfuel.
    Qed.

    Lemma oraat_interp_rule_safety:
      forall reg_types ext_fn_types
        sigma int_fn_env struct_env st st' action ext_log' rule',
        WF_state reg_types st ->
        WF_ext_sigma ext_fn_types sigma ->
        WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
        typecheck_rule reg_types ext_fn_types int_fn_env struct_env action = Success (rule', 0) ->
        oraat_interp_rule sigma int_fn_env struct_env st action = (true, st', ext_log') ->
        WF_state reg_types st'.
    Proof.
      intros * Hwf_st Hwf_sigma Hwf_fns Htype Horaat.
      consider oraat_interp_rule. destruct_match_pairs; simplify.
      bash_destruct Horaat; auto.
      eapply oraat_interp_action_safety in Heqp; eauto with WF_auto; propositional.
      constructor.
    Qed.

    (* Lemma oraat_interp_scheduler_safety: *)
    (*   forall rule_name_t (rules: rule_name_t -> rule) sched *)
    (*     reg_types ext_fn_types *)
    (*     sigma int_fn_env struct_env st st' ext_log' , *)
    (*     WF_state reg_types st -> *)
    (*     WF_ext_sigma ext_fn_types sigma -> *)
    (*     WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env -> *)
    (*     typecheck_schedule reg_types ext_fn_types int_fn_env struct_env sched rules = Success tt -> *)
    (*     oraat_interp_scheduler sigma int_fn_env struct_env rules st sched = (true, st', ext_log') -> *)
    (*     WF_state reg_types st'. *)
    (* Proof. *)
    (*   induction sched; unfold oraat_interp_scheduler; simpl. *)
    (*   - intros; simplify; auto. *)
    (*   - simpl; intros * Hw_st Hwf_sigma Hwf_fns Htype Horaat. simplify. *)


    (*     specialize oraat_interp_rule_safetywith (5 :=in Heqp. *)

    (*   intros * Hwf_st Hwf_sigma Hwf_fns Htype Horaat. *)
    (*   induction sched *)
    (*   consider oraat_interp_rule. destruct_match_pairs; simplify. *)
    (*   bash_destruct Horaat; auto. *)
    (*   eapply oraat_interp_action_safety in Heqp; eauto with WF_auto; propositional. *)
    (*   constructor. *)
    (* Qed. *)


    Lemma schedule_does_not_conflict_implies:
      forall int_fn_env rule_name_t (rules: rule_name_t -> rule) sched,
        schedule_does_not_conflict int_fn_env rules sched = Success true ->
        exists taint,
          interp_taint_scheduler' int_fn_env rules sched SortedRegEnv.empty = Success (Some taint).
    Proof.
      intros. unfold schedule_does_not_conflict in *. bash_destruct H; eauto.
    Qed.

    Ltac solve_replace_fuel IHfuel fuel1:=
      repeat match goal with
      | H1: oraat_interp_action _ _ _ fuel1 ?r ?r_acc ?ext_log ?b ?gamma ?action = (true, ?o1),
        H2: oraat_interp_action _ _ _ ?fuel2 ?r ?r_acc ?ext_log ?b ?gamma ?action = (true, ?o2) |- _  =>
        eapply IHfuel with (2 := H2) in H1; clear H2
      | H: oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
          match b with
          | true => fail
          | _ => let H' := fresh in
                assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
                rewrite H' in H; subst
          end
      | H: _ && _ = true |- _ => rewrite andb_true_iff in H
      | _ => progress (simplify; propositional; try congruence)
      end.


    Lemma oraat_interp_action_replace_fuel:
      forall fuel1 fuel2 action sigma int_fn_env struct_env r r_acc gamma b opt_res opt_res' ext_log,
      oraat_interp_action sigma int_fn_env struct_env
                          fuel1 r r_acc ext_log b gamma action = (true, opt_res) ->
      oraat_interp_action sigma int_fn_env struct_env
        fuel2 r r_acc ext_log b gamma action = (true, opt_res') ->
      opt_res = opt_res'.
    Proof.
      induction fuel1; simpl; [discriminate | ].
      destruct fuel2; simpl; [discriminate | ].
      destruct action; cbn; intros sigma int_fn_env struct_env r r_acc gamma b opt_res opt_res';
        intros Horaat_fuel1 Horaat_fuel2; simplify; auto.
      all: destruct_all_matches; solve_replace_fuel IHfuel1 fuel1.
    Qed.

    Ltac solve_increase_fuel IHfuel fuel1:=
      repeat match goal with
      | H1: oraat_interp_action _ _ _ fuel1 ?r ?r_acc ?ext_log ?b ?gamma ?action = (true, ?o1),
        H2: oraat_interp_action _ _ _ ?fuel2 ?r ?r_acc ?ext_log ?b ?gamma ?action = (_, ?o2) |- _  =>
          rewrite IHfuel with (1 := H1) in H2 by lia; clear H1
      | H1: oraat_interp_action _ _ _ fuel1 ?r ?r_acc ?ext_log ?b ?gamma ?action = (true, ?o1)
        |- oraat_interp_action _ _ _ ?fuel2 ?r ?r_acc ?ext_log ?b ?gamma ?action = (_, ?o2) =>
          rewrite IHfuel with (1 := H1) by lia; clear H1
      | H: oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = (true, _) |- _ =>
          match b with
          | true => fail
          | _ => let H' := fresh in
                assert (b = true) as H' by  (eapply oraat_interp_action_is_safe_generalizes; eauto);
                rewrite H' in H; subst
          end
      | H: _ && _ = true |- _ => rewrite andb_true_iff in H
      | |- context[_ && true] => rewrite andb_true_r
      | H: context[_ && true] |- _ => rewrite andb_true_r in H
      | H: Datatypes.length ?b = ?n  |- context[(Datatypes.length ?b =? ?n)%nat] =>
          rewrite H
      | H : oraat_interp_action _ _ _ _ _ _ _ ?b _ _ = _,
        H1: ?b = true |- _  =>
          match b with
          | true => fail
          | _ => rewrite H1 in H
          end
      | _ => progress (simpl; simplify; propositional; try congruence)
      end.


    Lemma oraat_interp_action_increase_fuel:
      forall fuel1 fuel2 action sigma int_fn_env struct_env r r_acc gamma b opt_res ext_log,
      oraat_interp_action sigma int_fn_env struct_env
                          fuel1 r r_acc ext_log b gamma action = (true, opt_res) ->
      fuel2 >= fuel1 ->
      oraat_interp_action sigma int_fn_env struct_env
        fuel2 r r_acc ext_log b gamma action = (true, opt_res).
    Proof.
      induction fuel1; simpl; [discriminate | ].
      destruct fuel2; simpl; [lia| ].
      destruct action; cbn; intros sigma int_fn_env struct_env r r_acc gamma b opt_res ;
        intros Horaat_fuel1 Hfuel2; simplify; auto.
      all: destruct_all_matches; solve_increase_fuel IHfuel1 fuel1.
      rewrite_solve.
    Qed.



  Section ORAAT_CPS.
    Context (ext_sigma: @ext_sigma_t N).
    Context (int_fns: @int_fn_env_t N (@action N)).
    Context (struct_defs: @struct_env_t N).
    Notation oraat_interp_action_cps := (oraat_interp_action_cps ext_sigma int_fns struct_defs).
    Notation oraat_interp_action := (oraat_interp_action ext_sigma int_fns struct_defs).

    Section WP.
      Notation oraat_wp_action := (oraat_wp_action ext_sigma int_fns struct_defs).

      Lemma oraat_wp_fail__safe:
        forall fuel r ty_hint
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log ,
          (forall res, post (false, res)) ->
          post (true, None) ->
          oraat_wp_action fuel r ((Fail ty_hint) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_var__safe:
        forall fuel r (var: var_t)
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log true ,
          (forall res, post (false, res)) ->
          (let '(safe, v) := varenv_lookup_var' gamma var in
           safe = true ->
           post (true, Some (gamma, r_acc, ext_log, v))) ->
          oraat_wp_action fuel r ((Var var) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        destruct_matches_in_hyp H0.
        setoid_rewrite andb_true_l. destruct_match; auto.
        unfold varenv_lookup_var' in *. simplify.
        match goal with
        | |- post (?bs, _) => destruct  bs; auto
        end.
      Qed.

      Lemma oraat_wp_const__safe:
        forall fuel r (cst: list bool)
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log ,
          (forall res, post (false, res)) ->
          post (true, (Some (gamma, r_acc, ext_log, cst))) ->
          oraat_wp_action fuel r ((Const cst) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_assign__safe:
        forall fuel r var ex
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log ,
          (forall res, post (false, res)) ->
          oraat_wp_action (Nat.pred fuel) r ex
                          (fun res =>
                             let '(is_safe, opt) := res in
                             is_safe = true ->
                             match opt with
                             | Some (gamma, r_acc, ext_log, v_ex) =>
                                 post (is_success (varenv_lookup_var gamma var tt),
                                       Some (varenv_update gamma var v_ex, r_acc, ext_log, []))
                             | None => post (true, None)
                             end
                          ) gamma r_acc ext_log true ->
          oraat_wp_action fuel r ((Assign var ex) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        rewrite oraat_interp_action_cps_correct.
        rewrite oraat_wp_action_correct in H0. simpl in *.
        destruct_match.
        destruct o as [[[[? ?] ?] ?]  | ].
        - destruct b; auto.
        - destruct b; auto.
      Qed.

      Lemma oraat_wp_seq__safe:
        forall fuel r (a1 a2: action)
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log ,
          (forall res, post (false, res)) ->
          oraat_wp_action (Nat.pred fuel) r a1
                          (fun res =>
                             let '(is_safe, opt) := res in
                             is_safe = true ->
                             match opt with
                             | (Some (gamma, r_acc, ext_log, v_ex)) =>
                               oraat_wp_action (Nat.pred fuel) r a2 post gamma r_acc ext_log true
                             | None => post (true, None)
                             end) gamma r_acc ext_log true ->
          oraat_wp_action fuel r ((Seq a1 a2) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        rewrite oraat_interp_action_cps_correct.
        rewrite oraat_wp_action_correct in H0. simpl in *.
        destruct_match; auto.
        destruct o as [[[[? ?] ?] ?]  | ].
        - destruct b; propositional.
          rewrite oraat_interp_action_cps_correct.
          match goal with
          | |- post (?x) => destruct  x eqn:?
          end.
          destruct b; auto.
          apply oraat_interp_action_is_safe_generalizes in Heqp0. discriminate.
        - destruct b; auto.
      Qed.
Require Import koika.Bits.

      Lemma oraat_wp_if__safe:
        forall fuel r (cond tbranch fbranch: action)
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log ,
          (forall res, post (false, res)) ->
            oraat_wp_action (Nat.pred fuel) r cond (fun res =>
                        let '(is_safe, opt) := res in
                        is_safe = true ->
                        match opt with
                        | Some (gamma, r_acc, ext_log, v_cond) =>
                          (Nat.eqb (Datatypes.length v_cond) 1) = true ->
                          if bits_eq v_cond [true] then
                            oraat_wp_action (Nat.pred fuel) r tbranch post gamma r_acc ext_log true
                          else
                            oraat_wp_action (Nat.pred fuel) r fbranch post gamma r_acc ext_log true
                        | None => post (true, None)
                        end) gamma r_acc ext_log true ->
          oraat_wp_action fuel r ((If cond tbranch fbranch) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        rewrite oraat_interp_action_cps_correct.
        rewrite oraat_wp_action_correct in H0. simpl in *.
        destruct_match; auto.
        destruct o as [[[[? ?] ?] ?]  | ].
        - repeat rewrite oraat_interp_action_cps_correct.
          destruct_match;
            match goal with
            | |- post (?x) => destruct  x eqn:?
            end.
          + destruct b0; auto.
            repeat rewrite oraat_wp_action_correct in H0. simpl in *.
            specialize oraat_interp_action_is_safe_generalizes with (1 := Heqp0).
            propositional.  apply andb_true_iff in H1; propositional. rewrite H2 in *. simpl in *.
            rewrite Heqp0 in *. auto.
          + destruct b0; auto.
            repeat rewrite oraat_wp_action_correct in H0. simpl in *.
            specialize oraat_interp_action_is_safe_generalizes with (1 := Heqp0).
            propositional.  apply andb_true_iff in H1; propositional. rewrite H2 in *. simpl in *.
            rewrite Heqp0 in *. auto.
        - destruct b; auto.
      Qed.
Notation "'let/opt4' v1 ',' v2 ',' v3 ',' v4 ':=' expr 'in' body" :=
  (match expr with
   | Some (v1, v2, v3, v4) => body
   | None => None
   end)
    (at level 200).

      Lemma oraat_wp_bind__safe:
        forall fuel r var ex body
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log ,
          (forall res, post (false, res)) ->
          oraat_wp_action (Nat.pred fuel) r ex (fun res =>
                    let '(is_safe, opt) := res in
                    is_safe = true ->
                    match opt with
                    | (Some (gamma, r_acc, ext_log, v_ex)) =>
                      oraat_wp_action (Nat.pred fuel) r body
                                      (fun res =>
                                         let '(is_safe, opt) := res in
                                         is_safe = true ->
                                         post (true, let/opt4 gamma', r_acc, ext_log, v := opt in
                                                     (Some (tl gamma', r_acc, ext_log, v))))
                          (varenv_bind gamma var v_ex) r_acc ext_log is_safe
                    | _ => post (true, opt)
                    end) gamma r_acc ext_log true ->
          oraat_wp_action fuel r ((Bind var ex body) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        rewrite oraat_interp_action_cps_correct.
        rewrite oraat_wp_action_correct in H0. simpl in *.
        destruct_match; auto.
        destruct o as [[[[? ?] ?] ?]  | ].
        - rewrite oraat_interp_action_cps_correct.
          rewrite oraat_wp_action_correct in H0. simpl in *.
          destruct_match; auto.
          destruct b; destruct b0; destruct o as [[[[? ?] ?] ?]  | ]; propositional.
          + apply oraat_interp_action_is_safe_generalizes in Heqp0. discriminate.
          + apply oraat_interp_action_is_safe_generalizes in Heqp0. discriminate.
        - destruct b; auto.
      Qed.


      Lemma oraat_wp_read0__safe:
        forall fuel r idx
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log true ,
          (forall res, post (false, res)) ->
          (let '(safe, v) := r_get_reg' r idx in
          safe = true ->
          post (true, Some (gamma, r_acc, ext_log, v))) ->
          oraat_wp_action fuel r ((Read P0 idx) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        simpl; intros. setoid_rewrite andb_true_l. destruct_match; auto.
        match goal with
        | |- post (?x, _) => destruct x eqn:?
        end; auto.
      Qed.

      Lemma oraat_wp_read1__safe:
        forall fuel r idx
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log is_safe ,
          (forall res, post (false, res)) ->
          (let '(safe, v) := r_get_reg' r_acc idx in
          safe = true ->
          post (true, Some (gamma, r_acc, ext_log, v))) ->
          oraat_wp_action fuel r ((Read P1 idx) ) post gamma r_acc ext_log is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
        simpl; intros. setoid_rewrite andb_true_l. destruct_match; auto. subst.
        unfold r_get_reg' in *.
        match goal with
          | |- post (?x, _) => destruct x eqn:?
          end; auto.
      Qed.

      Lemma oraat_wp_write__safe:
        forall fuel r port idx value
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log ,
          (forall res, post (false, res)) ->
          oraat_wp_action (Nat.pred fuel) r value (fun res =>
                      let '(is_safe, opt) := res in
                      is_safe = true ->
                      match opt with
                      | (Some (gamma, r_acc, ext_log, v_value)) =>
                        post (true, Some (gamma, state_set r_acc idx v_value, ext_log, []))
                      | None => post (true,None)
                      end) gamma r_acc ext_log true ->
          oraat_wp_action fuel r ((Write port idx value) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        rewrite oraat_interp_action_cps_correct.
        rewrite oraat_wp_action_correct in H0. simpl in *.
        destruct_match; auto.
        destruct o as [[[[? ?]?] ?]  | ].
        - destruct b; propositional.
        - destruct b; auto.
      Qed.

      Lemma oraat_wp_zop__safe:
        forall fuel r fn
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log true ,
          (forall res, post (false, res)) ->
          (let '(safe, v) := interp_zop' struct_defs fn in
           safe = true ->
           post ((true, Some (gamma, r_acc, ext_log, v))))  ->
          oraat_wp_action fuel r ((Zop fn) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        intros.
        match goal with
        | |- post (?x, _) => destruct x eqn:?
        end; auto. simpl in *. apply andb_true_iff in Heqb. propositional.
      Qed.

      Lemma oraat_wp_unop__safe:
        forall fuel r fn arg
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log true ,
          (forall res, post (false, res)) ->
          oraat_wp_action (Nat.pred fuel) r arg (fun res =>
                    let '(is_safe, opt) := res in
                    is_safe = Datatypes.true ->
                    match opt with
                    | Some (gamma, r_acc, v_arg) =>
                      let '(safe, v) := interp_unop' struct_defs fn v_arg in
                      safe = Datatypes.true ->
                      post (Datatypes.true, Some (gamma, r_acc, v))
                    | None => post (Datatypes.true,None)
                    end) gamma r_acc ext_log true ->
          oraat_wp_action fuel r ((Unop fn arg) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        rewrite oraat_interp_action_cps_correct.
        rewrite oraat_wp_action_correct in H0. simpl in *.
        destruct_match; auto.
        destruct o as [[[[? ?] ?] ?]  | ].
        - match goal with
          | |- post (?x, _) => destruct x eqn:?
          end.
          + apply andb_true_iff in Heqb0; propositional.
          + auto.
        - destruct b; auto.
      Qed.

      Lemma oraat_wp_binop__safe:
        forall fuel r fn arg1 arg2
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log ,
          (forall res, post (false, res)) ->
          oraat_wp_action (Nat.pred fuel) r arg1 (fun res =>
                      let '(is_safe, opt) := res in
                      is_safe = Datatypes.true ->
                      match opt with
                      | (Some (gamma, r_acc, ext_log, v_arg1)) =>
                        oraat_wp_action (Nat.pred fuel) r arg2 (fun res =>
                                    let '(is_safe, opt) := res in
                                    is_safe = Datatypes.true ->
                                    match opt with
                                    | (Some (gamma, r_acc, ext_log, v_arg2)) =>
                                      let '(safe, v) := interp_binop' struct_defs fn v_arg1 v_arg2 in
                                      safe = Datatypes.true ->
                                      post (true, Some (gamma, r_acc, ext_log, v))
                                    | _ => post (true, None)
                                    end) gamma r_acc ext_log is_safe
                      | None => post (true, None)
                      end) gamma r_acc ext_log true ->
          oraat_wp_action fuel r ((Binop fn arg1 arg2) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        rewrite oraat_interp_action_cps_correct.
        rewrite oraat_wp_action_correct in H0. simpl in *.
        destruct_match; auto.
        destruct o as [[[[? ?] ?] ?]  | ].
        - rewrite oraat_interp_action_cps_correct.
          rewrite oraat_wp_action_correct in H0. simpl in *.
          destruct_match.
          destruct b; destruct b0; destruct o as [[[[? ?] ?] ?]  | ]; propositional; simpl.
          + match goal with
            | |- post (?x, _) => destruct x eqn:?
            end; auto.
          + apply oraat_interp_action_is_safe_generalizes in Heqp0. discriminate.
          + apply oraat_interp_action_is_safe_generalizes in Heqp0. discriminate.
        - destruct b; auto.
      Qed.

      Lemma oraat_wp_internal_call__safe:
        forall fuel r fn arg
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log ,
          (forall res, post (false, res)) ->
          oraat_wp_action (Nat.pred fuel) r arg (fun res =>
                           let '(is_safe, opt) := res in
                           is_safe = Datatypes.true ->
                           match opt with
                           | Some (gamma, r_acc, ext_log, v_arg) =>
                             let '(safe, (arg_name, body)) := get_fn_arg_and_body' int_fns fn in
                             safe = true ->
                             oraat_wp_action (Nat.pred fuel) r body (fun res =>
                                         let '(is_safe, opt) := res in
                                         is_safe = Datatypes.true ->
                                         match opt with
                                         | (Some (_, r_acc, ext_log, v)) =>
                                           post (true, Some (gamma, r_acc, ext_log, v))
                                         | None => post (true, None)
                                         end) (fn_gamma arg_name v_arg) r_acc ext_log is_safe
                           | None => post (true, None)
                           end) gamma r_acc ext_log true ->
          oraat_wp_action fuel r ((InternalCall fn arg) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        rewrite oraat_interp_action_cps_correct.
        rewrite oraat_wp_action_correct in H0. simpl in *.
        destruct_match; auto.
        destruct o as [[[[? ?] ?] ?]  | ].
        - destruct_match.
          rewrite oraat_interp_action_cps_correct.
          rewrite oraat_wp_action_correct in H0. simpl in *.
          destruct_match.
          destruct b0.
          + specialize oraat_interp_action_is_safe_generalizes with (1 := Heqp1).
            propositional. apply andb_true_iff in H1; propositional. rewrite H2 in *. simpl in *.
            rewrite Heqp1 in H0. propositional.
            destruct o; auto.
          + repeat destruct_match; auto.
        - destruct b; auto.
      Qed.

      Lemma oraat_wp_external_call__safe:
        forall fuel r fn arg
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc ext_log ,
          (forall res, post (false, res)) ->
          oraat_wp_action (Nat.pred fuel) r arg
                          (fun res =>
                           let '(is_safe, opt) := res in
                           is_safe = Datatypes.true ->
                           match opt with
                           | Some (gamma, r_acc, ext_log, v_arg) =>
                             let '(safe, v) := call_ext' ext_sigma fn v_arg in
                             safe = true ->
                             post (true, Some (gamma, r_acc, ext_log_update ext_log fn v_arg, v))
                           | None => post (true, None)
                           end) gamma r_acc ext_log true ->
          oraat_wp_action fuel r ((ExternalCall fn arg) ) post gamma r_acc ext_log true.
      Proof.
        destruct fuel; propositional; cbn; auto.
        rewrite oraat_interp_action_cps_correct.
        rewrite oraat_wp_action_correct in H0. simpl in *.
        destruct_match; auto.
        destruct o as [[[[? ?] ?] ?]  | ].
        - match goal with
          | |- post (?x, _) => destruct x eqn:?
          end; auto.
          apply andb_true_iff in Heqb0. propositional.
        - destruct b; auto.
      Qed.

      (* Lemma oraat_wp_action_struct_init: *)
      (*   forall fuel r dstruct_name fld_subst (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe, *)
      (*     post (false, None) -> *)
      (*     match fld_subst with *)
      (*     | [] => oraat_wp_action fuel r (Zop (StructInit dstruct_name)) post gamma r_acc is_safe *)
      (*     | _ => False *)
      (*     end -> *)
      (*     oraat_wp_action fuel r (action_struct_init dstruct_name fld_subst) post gamma r_acc is_safe. *)
      (* Proof. *)
      (*   destruct fuel; propositional; cbn; auto. *)
      (*   bash_destruct H0; auto. *)


    End WP.

  End ORAAT_CPS.



End ORAAT.

Create HintDb solve_taint.
Hint Immediate taint_env_approximates_log_empty : solve_taint.
