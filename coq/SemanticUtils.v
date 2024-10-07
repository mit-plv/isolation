Require Import Koika.Common.
Require Import Koika.Utils.
Require Import Koika.Syntax.
Require Import Koika.Semantics.
Require Import Koika.Environments.
Require Import Koika.Typechecking.
Require Import Koika.Tactics.
Require Import Koika.Magic.
Require Import Koika.SyntaxMacros.
Require Import Koika.Std.
Require Import Coq.NArith.NArith.
Require Import Koika.Bits.

Section Env.


End Env.

Section StructLemmas.
  Definition unsafe_get_field (flds: list (struct_field_t * nat)) (fld: struct_field_t) (v: list bool)
                              : list bool :=
    success_or_default (Semantics.get_field flds fld v) [].

  Lemma slice_subst_length:
    forall offset v vstruct,
    offset <= Datatypes.length vstruct ->
    Datatypes.length vstruct >= offset + Datatypes.length v ->
    Datatypes.length (slice_subst offset v vstruct) = Datatypes.length vstruct.
  Proof.
    intros. unfold slice_subst.
    repeat rewrite app_length.
    rewrite firstn_length.
    rewrite skipn_length.
    replace (Nat.min offset (Datatypes.length vstruct)) with offset by lia.
    lia.
  Qed.
  Lemma element_offset_cons:
    forall fld fld' flds,
    element_offset (fld::flds) fld' =
      if Nat.eqb fld' (fst fld)
      then Success 0
      else (let/res res := element_offset flds fld' in
            Success ((snd fld) + res)).
  Proof.
    unfold element_offset, find_with_index. simpl. intros. destruct_match; subst; simpl.
    destruct_match; auto.
    specialize @find_with_index'_acc with
        (xs := flds) (acc := 1) (acc0 := 0) (f := (fun '(fld, _) => Nat.eqb fld' fld)).
    replace (1 + 0) with 1 in * by lia.
    destruct_match; destruct_match_pairs; subst; auto; intros.
    + setoid_rewrite H.
      setoid_rewrite Heqo. simpl. f_equal.
      unfold list_sum; simpl.
      repeat rewrite list_sum_add. lia.
    + setoid_rewrite Heqo.
      setoid_rewrite H. reflexivity.
  Qed.
  Lemma element_offset_lt_struct_sz:
    forall flds fld offset,
    element_offset flds fld = Success offset ->
    offset <= struct_sz' flds.
  Proof.
    induction flds; propositional; simpl in *.
    - discriminate.
    - destruct a.
      rewrite element_offset_cons in H; simpl in *.
      destruct_matches_in_hyp H; simplify; try lia.
      apply IHflds in Heqr. unfold struct_sz' in *. simpl.
      unfold list_sum in *; simpl. rewrite list_sum_add; unfold list_sum.
      set (fold_left Nat.add (map snd flds) 0) in *. lia.
  Qed.
  Lemma get_field_width_cons:
    forall x xs fld,
    get_field_width (x::xs) fld =
      if Nat.eqb fld (fst x)
      then Success (snd x)
      else get_field_width xs fld.
  Proof.
    unfold get_field_width. simpl. intros.
    destruct_match_pairs; simpl; subst. destruct_match; auto.
  Qed.
  Lemma struct_sz'_cons:
    forall x xs,
    struct_sz' (x::xs) = snd x + struct_sz' xs .
  Proof.
    intros; unfold struct_sz', list_sum; simpl; rewrite list_sum_add; unfold list_sum; lia.
  Qed.
  Lemma element_offset_and_width_lt_struct_sz:
    forall flds fld offset len,
    element_offset flds fld = Success offset ->
    get_field_width flds fld = Success len ->
    offset + len <= struct_sz' flds.
  Proof.
    induction flds; propositional; simpl in *.
    - discriminate.
    - destruct a; simpl in *.
      rewrite element_offset_cons in H; simpl in *.
      rewrite get_field_width_cons in H0. simpl in *. destruct_matches_in_hyp H; simplify; simpl.
      + unfold struct_sz', list_sum; simpl. rewrite list_sum_add. lia.
      + specialize IHflds with (1 := Heqr) (2 := H0).
        rewrite struct_sz'_cons; simpl. lia.
  Qed.

  Lemma slice_slice_subst_neq:
    forall base offset offset' width arg,
    (offset' + List.length arg) <= offset \/ (offset + width) <= offset' ->
    offset + width <= List.length base ->
    offset' + List.length arg <= List.length base ->
    slice offset width (slice_subst offset' arg base) = slice offset width base.
  Proof.
    intros; unfold slice, slice_subst.
    repeat rewrite firstn_fill_eq.
    - destruct H; repeat rewrite skipn_app; repeat rewrite firstn_app;
        repeat rewrite skipn_length; repeat rewrite firstn_length;
        replace (Nat.min offset' (Datatypes.length base)) with offset' by lia;
        try replace (offset' - offset) with 0 by lia;
        try replace (offset - offset') with 0 by lia;
        replace (width - 0) with width by lia;
        try replace (width - (offset' - offset)) with 0 by lia;
        repeat rewrite skipn_all2 by (rewrite firstn_length; lia);
        repeat rewrite firstn_nil; simpl;
        repeat rewrite skipn_all2 by (lia); simpl;
        repeat rewrite firstn_nil; simpl.
      + replace (Datatypes.length arg - (offset - offset')) with 0 by lia.
        rewrite PeanoNat.Nat.sub_0_r.
        replace (offset - offset' - Datatypes.length arg) with (offset - (offset' + Datatypes.length arg)) by lia.
        rewrite skipn_skipn by lia. reflexivity.
      + rewrite app_nil_r.
        rewrite firstn_skipn_comm.
        rewrite firstn_firstn. replace (Nat.min (offset + width) offset') with (offset + width) by lia.
        rewrite firstn_skipn_comm. reflexivity.
    - rewrite skipn_length. lia.
    - rewrite skipn_length. repeat rewrite app_length.
      rewrite skipn_length.
      rewrite firstn_length. lia.
  Qed.
  Lemma elements_disjoint:
    forall (flds: list (struct_field_t * nat)) fld1 fld2 offset1 width1 offset2 width2,
    element_offset flds fld1 = Success offset1 ->
    get_field_width flds fld1 = Success width1 ->
    element_offset flds fld2 = Success offset2 ->
    get_field_width flds fld2 = Success width2 ->
    fld1 <> fld2 ->
    offset1 + width1 <= offset2 \/ offset2 + width2 <= offset1.
  Proof.
    induction flds; intros * Hoffset1 Hwidth Hoffset2 Hwidth2 Hneq; simpl in *.
    - discriminate.
    - rewrite element_offset_cons in *.
      rewrite get_field_width_cons in *.
      destruct_matches_in_hyp Hoffset1; simplify_nat; subst; simplify.
      + destruct_matches_in_hyp Hoffset2; simplify_nat; subst; simplify; try discriminate; lia.
      + destruct_matches_in_hyp Hoffset2; simplify_nat; subst; simplify; try discriminate.
        { right; lia. }
        { specialize IHflds with (1 := Heqr) (2 := Hwidth) (3 := Heqr0) (4 := Hwidth2) (5 := Hneq).
          lia.
        }
  Qed.

  Lemma get_field_slice_subst_neq:
    forall flds offset fld fld' vstruct vfld',
      element_offset flds fld' = Success offset ->
      get_field_width flds fld' = Success (Datatypes.length vfld') ->
      Datatypes.length vstruct = struct_sz' flds ->
      fld <> fld' ->
      Semantics.get_field flds fld (slice_subst offset vfld' vstruct) =
      Semantics.get_field flds fld vstruct.
  Proof.
    intros. unfold Semantics.get_field.
    destruct_match; auto.
    destruct_match; auto.
    rewrite slice_subst_length.
    + destruct_match; auto. f_equal.
      apply slice_slice_subst_neq.
      * eapply elements_disjoint; eauto.
      * rewrite H1; eapply element_offset_and_width_lt_struct_sz; eauto.
      * rewrite H1; eapply element_offset_and_width_lt_struct_sz; eauto.
    + rewrite H1. eapply element_offset_lt_struct_sz; eauto.
    + specialize element_offset_and_width_lt_struct_sz with (1 := H) (2 := H0). lia.
  Qed.

  Lemma unsafe_get_subst_field_neq:
    forall (flds: list (struct_field_t * nat)) (fld: struct_field_t) fld' vstruct vfld' default,
    is_success ((subst_field flds fld' vstruct vfld')) = true ->
    fld <> fld' ->
    unsafe_get_field flds fld (success_or_default (subst_field flds fld' vstruct vfld') default) =
    unsafe_get_field flds fld vstruct.
  Proof.
    intros *. intros; unfold subst_field, unsafe_get_field in *.
    simplify. simpl in *.
    erewrite get_field_slice_subst_neq; eauto.
  Qed.

  Lemma slice_slice_subst_eq:
    forall base offset arg,
    offset + Datatypes.length arg <= Datatypes.length base ->
    slice offset (Datatypes.length arg) (slice_subst offset arg base) = arg.
  Proof.
    intros.
    unfold slice, slice_subst.
    repeat rewrite skipn_app.
    repeat rewrite firstn_length.
    rewrite firstn_fill_eq.
    2: { repeat rewrite app_length.
         repeat rewrite skipn_length.
         repeat rewrite firstn_length. lia.
       }
    repeat rewrite firstn_app.
    repeat rewrite skipn_length.
    repeat rewrite firstn_length.
    replace (Init.Nat.min offset (Datatypes.length base)) with offset by lia.
    replace (offset - offset) with 0 by lia.
    repeat rewrite PeanoNat.Nat.sub_0_r.
    replace (Datatypes.length arg - Datatypes.length arg) with 0 by lia.
    rewrite PeanoNat.Nat.sub_0_l.
    repeat rewrite skipn_O. repeat rewrite firstn_O. rewrite app_nil_r.
    rewrite skipn_firstn_comm. replace (offset - offset) with 0 by lia. rewrite firstn_O.
    rewrite firstn_nil. simpl.
    rewrite firstn_all. reflexivity.
  Qed.

  Lemma get_field_slice_subst_eq:
    forall flds offset fld vstruct vfld,
      element_offset flds fld = Success offset ->
      get_field_width flds fld = Success (Datatypes.length vfld) ->
      Datatypes.length vstruct = struct_sz' flds ->
      Semantics.get_field flds fld (slice_subst offset vfld vstruct) = Success vfld.
  Proof.
    intros. unfold subst_field, get_field in *; simplify.
    repeat simpl_match.
    rewrite slice_subst_length.
    + rewrite H1.  rewrite PeanoNat.Nat.eqb_refl. f_equal.
      apply slice_slice_subst_eq. rewrite H1.
      specialize element_offset_and_width_lt_struct_sz with (1 := H) (2 := H0). lia.
    + rewrite H1. eapply element_offset_lt_struct_sz; eauto.
    + specialize element_offset_and_width_lt_struct_sz with (1 := H) (2 := H0). lia.
  Qed.

  Lemma unsafe_get_subst_field_eq:
    forall (flds: list (struct_field_t * nat)) (fld: struct_field_t) vstruct vfld' default,
    is_success ((subst_field flds fld vstruct vfld')) = true ->
    unsafe_get_field flds fld (success_or_default (subst_field flds fld vstruct vfld') default) =
    vfld'.
  Proof.
    intros *. intros; unfold subst_field, unsafe_get_field in *.
    simplify. simpl in *.
    erewrite get_field_slice_subst_eq; eauto.
  Qed.

  Lemma unsafe_get_field_slice_subst_eq:
    forall flds fld offset vfld vstruct,
      element_offset flds fld = Success offset ->
      get_field_width flds fld = Success (Datatypes.length vfld) ->
      Datatypes.length vstruct = struct_sz' flds ->
      unsafe_get_field flds fld (slice_subst offset vfld vstruct) = vfld.
  Proof.
    intros. unfold unsafe_get_field, Semantics.get_field.
    repeat simpl_match.
    repeat rewrite app_length.
    repeat rewrite firstn_length.
    specialize element_offset_lt_struct_sz with (1 := H); intros.
    specialize element_offset_and_width_lt_struct_sz with (1 := H) (2 := H0); intros.
    replace (Nat.min offset (Datatypes.length vstruct)) with offset by lia.
    destruct_match.
    + simplify_nat. apply slice_slice_subst_eq. lia.
    + simplify_nat. rewrite<-H1 in *.
      rewrite slice_subst_length in Heqb by lia. congruence.
  Qed.


End StructLemmas.

Section WF.

  Definition WF_state (types: reg_types_t) (st: state_t) : Prop :=
    forall reg, match types reg, get_reg st reg with
           | Some n, Some v => List.length v = n
           | None, _ => True
           | _, _ => False
           end.

  Definition WF_LE (le: LogEntry) (n: nat) : Prop :=
    (match le.(lwrite0) with
     | Some v => List.length v = n
     | _ => True
     end) /\
    (match le.(lwrite1) with
     | Some v => List.length v = n
     | _ => True
     end).

  Definition WF_log (types: reg_types_t) (log: log_t) : Prop :=
    forall reg, match types reg with
           | Some n => WF_LE (log_get log reg) n
           | None => True
           end.
  Definition WF_gamma (var_types: var_types_t) (gamma: gamma_t) : Prop :=
    Forall2 (fun '(v1, ty) '(v2, val) => v1 = v2 /\ List.length val = ty) var_types gamma.

  Definition WF_ext_sigma (ext_fn_types: ext_fn_types_t) (ext_sigma: ext_sigma_t) : Prop :=
    forall fn,
      match ext_fn_types fn with
      | Some (arg_ty, ret_ty) =>
        forall arg, Datatypes.length arg = arg_ty ->
        match ext_sigma fn arg with
        | Success res => Datatypes.length res = ret_ty
        | Failure _ => False
        end
      | None => True
      end.

  Definition WF_int_fn_env (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t)
                           (int_fns: int_fn_env_t) (struct_defs: struct_env_t) : Prop :=
    typecheck_int_fns' reg_types ext_fn_types int_fns struct_defs = Success tt.

  Section Lemmas.
    Lemma WF_LE_empty: forall n,
        WF_LE LE_empty n.
    Proof.
      consider WF_LE. intros. simpl. auto.
    Qed.


    Lemma WF_LE_app: forall l1 l2 n,
        WF_LE l1 n ->
        WF_LE l2 n ->
        WF_LE (logentry_app l1 l2) n.
    Proof.
      intros. consider WF_LE. propositional.
      unfold logentry_app. simpl. unfold opt_or.
      split_ands_in_goal; destruct_all_matches; auto.
    Qed.

    (* Lemma WF_gamma_GenericGammaEmpty (gamma: gamma_t): *)
    (*   WF_gamma GenericGammaTEmpty gamma. *)
    (* Proof. *)
    (*   unfold WF_gamma, GenericGammaTEmpty, varenv_lookup_var; intros; simpl; auto. *)
    (* Qed. *)

    Lemma WF_log_GenericLogEmpty:
      forall (reg_types: reg_types_t),
        WF_log reg_types log_empty.
    Proof.
      intros. unfold WF_log. intros. unfold is_some in *.
      propositional. rewrite log_get_empty.
      destruct_match; auto.
      apply WF_LE_empty.
    Qed.

    Lemma find_find_and_replace_eq:
      forall A B (f: (A * B) -> bool) (xs: list (A * B)) a (g: A -> A -> bool) (b: B) default,
        (forall a a', g a a' = true <-> a = a') ->
        (forall a' b', f (a',b') = true <-> a = a') ->
        is_some (find f xs) ->
        find f (find_and_replace xs a g (fun _ => b) default) = Some (a, b).
    Proof.
      induction xs; simpl; auto; intros * Hg Hf Hsome.
      - unfold is_some in *. propositional. discriminate.
      - destruct_match; subst.
        destruct_match; simpl.
        + rewrite Hg in *. subst.
          specialize (Hf a1 b). destruct Hf. propositional. simpl_match. auto.
        + pose proof (Hf a1 b0). destruct H. destruct_match; propositional; auto.
          specialize (Hg a1 a1). propositional. congruence.
    Qed.

    Lemma find_find_and_replace_neq:
      forall A B (f: (A * B) -> bool) (xs: list (A * B)) a (g: A -> A -> bool) (b: B) default,
        (forall a a', g a a' = true <-> a = a') ->
        (forall b', f (a, b') = false) ->
        find f (find_and_replace xs a g (fun _ => b) default) = find f xs.
    Proof.
      induction xs; simpl; auto; [ | intros * Hg Hf].
      - intros. destruct_match; auto. rewrite H0 in *. discriminate.
      - destruct_match_pairs; subst. destruct_match; simpl; auto.
        + apply Hg in Heqb1. subst. rewrite Hf. rewrite Hf. auto.
        + destruct_match; auto.
    Qed.


    Lemma WF_gamma_update:
      forall gamma var_types {A} (msg: A) var v v',
        WF_gamma var_types gamma ->
        varenv_lookup_var gamma var msg = Success v ->
        Datatypes.length v = Datatypes.length v' ->
        WF_gamma var_types (varenv_update gamma var v').
    Proof.
      induction gamma; unfold WF_gamma, varenv_lookup_var in *.
      - intros. inversions H. simpl in *. discriminate.
      - intros. simplify.
        simpl in *. destruct_match_pairs; subst.
        destruct_matches_in_hyp Heqo; simplify.
        + apply String.eqb_eq in Heqb; subst. unfold varenv_update; simpl.
          rewrite String.eqb_refl. inversions H.
          constructor; auto.
          destruct_match_pairs; propositional.
        + unfold varenv_update. simpl. simpl_match.
          inversions H. constructor; auto.
          destruct_match_pairs; propositional.
          eapply IHgamma with (msg := tt); eauto.
          rewrite Heqo. auto.
    Qed.

    Lemma WF_log_app:
      forall (reg_types: reg_types_t) (l1 l2: log_t),
        WF_log reg_types l1 ->
        WF_log reg_types l2 ->
        WF_log reg_types (log_app l1 l2).
    Proof.
      intros. unfold WF_log in *. intros. unfold is_some in *.
      specialize H with (reg := reg). specialize H0 with (reg := reg).
      destruct_match; auto.
      rewrite get_log_app.
      apply WF_LE_app; auto.
    Qed.

    Lemma max_fn_height_correct:
      forall int_fn_env idx fn fn_name,
        lookup_int_fn int_fn_env fn_name tt = Success (idx, fn) ->
        max_fn_height int_fn_env >= height (fn_body fn).
    Proof.
      intros. apply lookup_int_fn_Success in H. propositional.
      intros. consider max_fn_height.
      eapply max_map_correct' with (base := 0) (f := fun f => height (fn_body f)) in H0.
      lia.
    Qed.

    Lemma WF_gamma_lookup_var:
      forall gamma var_types var n A (msg: A),
        WF_gamma var_types gamma ->
        varenv_lookup_var var_types var msg = Success n ->
        exists v, varenv_lookup_var gamma var msg = Success v /\ Datatypes.length v = n.
    Proof.
      induction gamma; intros; unfold WF_gamma, varenv_lookup_var in *; propositional.
      - inversions H. simpl in *. discriminate.
      - simplify. inversions H. destruct_match_pairs; propositional.
        simpl in *. destruct_match.
        + apply String.eqb_eq in Heqb. simplify. eexists; eauto.
        + eapply IHgamma; eauto. simpl_match. auto.
    Qed.


    Lemma case_singleton_bv:
      forall bs,
        Datatypes.length bs = 1 ->
        bs = [true] \/ bs = [false].
    Proof.
      destruct bs; simpl in *; try discriminate.
      destruct b; simpl in *; try discriminate; propositional;
        destruct bs; simpl in *; try discriminate; eauto.
    Qed.

    Lemma WF_log_set:
      forall reg_types log idx le n,
        WF_log reg_types log ->
        reg_types idx = Some n ->
        WF_LE le n ->
        WF_log reg_types (log_set log idx le).
    Proof.
      unfold WF_log; intros; propositional.
      destruct_match; auto.
      destruct_with_eqn (Nat.eqb idx reg).
      - apply PeanoNat.Nat.eqb_eq in Heqb; subst. rewrite log_set_eq. rewrite H0 in Heqo. option_simpl; subst. auto.
      - apply PeanoNat.Nat.eqb_neq in Heqb. rewrite log_set_neq; auto.
        specialize H with (reg := reg). simpl_match. auto.
    Qed.

    Lemma WF_commit_update:
      forall st tys log  ,
        WF_state tys st ->
        WF_log tys log  ->
        WF_state tys (commit_update st log).
    Proof.
      unfold WF_state, WF_log. intros * Hst Hlog; simplify.
      intros reg. specialize Hst with (reg := reg). specialize Hlog with (reg := reg).
      destruct_match; auto. simplify.
      unfold WF_LE, commit_update, get_reg, latest_write in *.
      rewrite SortedRegEnv.opt_get_map.
      propositional.
      simpl_match. unfold log_get in *. repeat destruct_match; auto.
    Qed.

  End Lemmas.

End WF.

Create HintDb WF_auto.
Hint Immediate WF_LE_empty: WF_auto.
(* Hint Immediate WF_gamma_GenericGammaEmpty: WF_auto. *)
Hint Immediate WF_log_GenericLogEmpty: WF_auto.

Section Conversions.
  Definition option_to_maybe (fields: list (struct_name_t * nat))
                             (v_opt: option (list bool)): result (list bool) unit :=
    let base := (Bits.zeroes (struct_sz' fields)) in
    match v_opt with
    | Some v => let/res base_valid := subst_field fields FIELD_maybe_valid base [true] in
               subst_field fields FIELD_maybe_data base_valid v
    | None => Success base
    end.

  Definition option_to_maybe' (sz: nat) (v_opt: option (list bool)) : list bool :=
    match v_opt with
    | Some v => [true] ++ v
    | None => zeroes (S sz)
    end.

  Lemma simplify_option_to_maybe_None:
    forall sz, option_to_maybe (STRUCT_maybe_fields sz) None = Success (zeroes (S sz)).
  Proof.
    reflexivity.
  Qed.

  Lemma simplify_option_to_maybe_Some:
    forall sz v,
    Datatypes.length v = sz ->
    option_to_maybe (STRUCT_maybe_fields sz) (Some v) = Success (option_to_maybe' sz (Some v)).
  Proof.
    intros. unfold option_to_maybe, option_to_maybe'; simpl.
    unfold subst_field. simpl.
    rewrite firstn_fill_length. rewrite PeanoNat.Nat.eqb_refl.
    simpl. rewrite firstn_fill_length. rewrite PeanoNat.Nat.eqb_refl. rewrite H.
    rewrite PeanoNat.Nat.eqb_refl. f_equal.
    unfold slice_subst. simpl. f_equal.
    rewrite H.
    rewrite skipn_all2.
    - rewrite app_nil_r. reflexivity.
    - rewrite firstn_fill_length. lia.
  Qed.

  Definition unsafe_option_to_maybe (fields: list (struct_name_t * nat))
                                    (v_opt: option (list bool)): list bool :=
    match option_to_maybe fields v_opt with
    | Success v => v
    | Failure _ => []
    end.

End Conversions.

Section CPS.
    Context (ext_sigma: ext_sigma_t).
    Context (int_fns: int_fn_env_t).
    Context (struct_defs: struct_env_t).

    Notation interp_action_cps := (interp_action_cps ext_sigma int_fns struct_defs).
    Notation interp_rule_cps := (interp_rule_cps ext_sigma int_fns struct_defs).
    Notation interp_scheduler'_cps := (interp_scheduler'_cps ext_sigma int_fns struct_defs).
    Notation interp_scheduler_cps := (interp_scheduler_cps ext_sigma int_fns struct_defs).
    Notation interp_cycle_cps := (interp_cycle_cps ext_sigma int_fns struct_defs).

    Notation interp_action := (interp_action ext_sigma int_fns struct_defs).
    Notation interp_rule := (interp_rule ext_sigma int_fns struct_defs).
    Notation interp_scheduler' := (interp_scheduler' ext_sigma int_fns struct_defs).
    Notation interp_scheduler := (interp_scheduler ext_sigma int_fns struct_defs).
    Notation interp_cycle := (interp_cycle ext_sigma int_fns struct_defs).


    Lemma interp_action_cps_correct:
      forall fuel fn_depth (r: state_t) (sched_log: log_t) (a: action)
        {A} (k: action_continuation unit A) (gamma: gamma_t) (action_log: log_t),
        interp_action_cps fuel fn_depth r sched_log a k gamma action_log =
        k (interp_action fuel fn_depth r gamma sched_log action_log a).
    Proof.
      induction fuel; [ reflexivity | ]; simpl.
      destruct a; cbn; intros; unfold __debug__, var_t  in *;
      repeat match goal with
             | _ => progress simpl
             | [ H: context[_ = _] |- _ ] => setoid_rewrite H
             | [  |- context[interp_action] ] => destruct interp_action as [((?, ?), ?) | ]
             | [  |- context[match ?x with _ => _ end] ] => destruct x eqn:?
             | _ => reflexivity || assumption
             end.
    Qed.

    Lemma interp_action_cps_correct_rev:
      forall fuel fn_depth (r: state_t)
        (sched_log: log_t)
        (a: action)
        (gamma: gamma_t)
        (action_log: log_t),
        interp_action fuel fn_depth r gamma sched_log action_log a =
        interp_action_cps fuel fn_depth r sched_log a id gamma action_log.
    Proof.
      intros; rewrite interp_action_cps_correct; reflexivity.
    Qed.

    Lemma interp_rule_cps_correct:
      forall (r: state_t)
        (L: log_t)
        (a: action )
        {A} (k: _ -> A),
        interp_rule_cps r a k (Success L) =
        k (interp_rule r L a).
    Proof.
      unfold interp_rule, interp_rule_cps; intros.
      rewrite interp_action_cps_correct.
      destruct interp_action as [[((?, ?), ?) | ] | ]; reflexivity.
    Qed.

    Lemma interp_rule_cps_correct_rev:
      forall (r: state_t)
        (L: log_t)
        (a: action),
        interp_rule r L a =
        interp_rule_cps r a id (Success L).
    Proof.
      intros; rewrite interp_rule_cps_correct; reflexivity.
    Qed.

    Lemma interp_scheduler'_cps_correct:
      forall {rule_name_t: Type} (r: state_t)
        (rules: rule_name_t -> rule)
        (s: scheduler)
        (L: log_t )
        {A} (k: _ -> A),
        interp_scheduler'_cps r rules s k (Success L) =
        k (interp_scheduler' r rules s L).
    Proof.
      induction s; cbn; intros.
      - reflexivity.
      - all: repeat match goal with
             | _ => progress simpl
             | _ => rewrite interp_action_cps_correct
             | [ H: context[_ = _] |- _ ] => rewrite H
             | [  |- context[interp_rule] ] => unfold interp_rule; destruct interp_action as [[((?, ?), ?) | ] | ]
             | [  |- context[match ?x with _ => _ end] ] => destruct x
             | _ => reflexivity
             end.
    Qed.

    Lemma interp_scheduler_cps_correct:
      forall {rule_name_t: Type} (r: state_t) (rules: rule_name_t -> rule)
        (s: scheduler)
        {A} (k: _ -> A),
        interp_scheduler_cps r rules s k =
        k (interp_scheduler r rules s).
    Proof.
      intros; apply interp_scheduler'_cps_correct.
    Qed.

    Lemma interp_cycle_cps_correct:
      forall {rule_name_t: Type} (r: state_t) (rules: rule_name_t -> rule)
        (s: scheduler)
        {A} (k: _ -> A),
        interp_cycle_cps r rules s k =
        k (interp_cycle r rules s).
    Proof.
      unfold interp_cycle, interp_cycle_cps; intros; rewrite interp_scheduler_cps_correct.
      reflexivity.
    Qed.

    Lemma interp_cycle_cps_correct_rev:
      forall {rule_name_t: Type} (r: state_t) (rules: rule_name_t -> rule)
        (s: scheduler),
        interp_cycle r rules s =
        interp_cycle_cps r rules s id.
    Proof.
      intros; rewrite interp_cycle_cps_correct; reflexivity.
    Qed.

    Section WP.
      Notation wp_action := (wp_action ext_sigma int_fns struct_defs).
      Notation wp_rule := (wp_rule ext_sigma int_fns struct_defs).
      Notation wp_scheduler := (wp_scheduler ext_sigma int_fns struct_defs).
      Notation wp_cycle := (wp_cycle ext_sigma int_fns struct_defs).

      Lemma wp_action_correct:
        forall fuel fn_depth (r: state_t)
          (gamma: gamma_t)
          (sched_log: log_t)
          (action_log: log_t)
          (a: action )
          (post: action_postcondition),
          wp_action fuel fn_depth r sched_log a post gamma action_log <->
          post (interp_action fuel fn_depth r gamma sched_log action_log a).
      Proof.
        intros; unfold wp_action; rewrite interp_action_cps_correct; reflexivity.
      Qed.

      Lemma wp_rule_correct:
        forall (r: state_t) (L: log_t)
          (rl: rule)
          (post: rule_postcondition),
          wp_rule r rl post (Success L) <->
          post (interp_rule r L rl).
      Proof.
        intros; unfold wp_rule; rewrite interp_rule_cps_correct; reflexivity.
      Qed.

      Lemma wp_scheduler_correct:
        forall {rule_name_t: Type} (rules: rule_name_t -> rule)
          (r: state_t)
          (s: scheduler)
          (post: scheduler_postcondition),
          wp_scheduler r rules s post <->
          post (interp_scheduler r rules s).
      Proof.
        intros; unfold wp_scheduler; rewrite interp_scheduler_cps_correct; reflexivity.
      Qed.

      Lemma wp_cycle_correct:
        forall {rule_name_t: Type} (rules: rule_name_t -> rule)
          (r: state_t)
          (s: scheduler)
          (post: cycle_postcondition),
          wp_cycle r rules s post <->
          post (interp_cycle r rules s).
      Proof.
        intros; unfold wp_cycle; rewrite interp_cycle_cps_correct; reflexivity.
      Qed.

      Lemma wp_fail:
        forall fuel fn_depth st sched_log ty_hint (post: action_postcondition) (gamma: gamma_t) (action_log: log_t),
          post (Failure tt) ->
          post (Success None) ->
          wp_action fuel fn_depth st sched_log (Fail ty_hint) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_var:
        forall fuel fn_depth st sched_log (var: var_t) (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          post (Failure tt) ->
          post (let/res var_value := varenv_lookup_var gamma var (__debug__ ("Var not found", gamma,var) tt) in
                Success (Some (gamma, action_log, var_value))) ->
          wp_action fuel fn_depth st sched_log (Var var) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_const:
        forall fuel fn_depth st sched_log (cst: list bool) (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          post (Failure tt) ->
          post (Success (Some (gamma, action_log, cst))) ->
          wp_action fuel fn_depth st sched_log (Const cst) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_assign:
        forall fuel fn_depth st sched_log (var: var_t) (ex: action) (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          wp_action (Nat.pred fuel) fn_depth st sched_log ex (fun res =>
                                       post (let/res opt := res in
                                             match opt with
                                             | Some (gamma, log, v) =>
                                               let/res _ := varenv_lookup_var gamma var (__debug__ ("Assign/var not found", var) tt) in
                                               (Success (Some (varenv_update gamma var v, log, [])))
                                             | None => (Success None)
                                             end)) gamma action_log ->
          wp_action fuel fn_depth st sched_log (Assign var ex) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_seq:
        forall fuel fn_depth st sched_log (a1 a2: action) (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          wp_action (pred fuel) fn_depth st sched_log a1
                    (fun res => match res with
                             | Success (Some (gamma, log, _)) =>
                               wp_action (pred fuel) fn_depth st sched_log a2 post gamma log
                             | _ => post res
                             end) gamma action_log ->
          wp_action fuel fn_depth st sched_log (Seq a1 a2) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_if:
        forall fuel fn_depth st sched_log (cond tbranch fbranch: action) (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          wp_action (pred fuel) fn_depth st sched_log cond
                    (fun res => match res with
                             | Success (Some (gamma, log,v)) =>
                               match v with
                               | [true] => wp_action (pred fuel) fn_depth st sched_log tbranch post gamma log
                               | [false] => wp_action (pred fuel) fn_depth st sched_log fbranch post gamma log
                               | _ => post (Failure (__debug__ ("If: cond not single bit", v) tt))
                               end
                             | _ => post res
                             end) gamma action_log ->
          wp_action fuel fn_depth st sched_log (If cond tbranch fbranch) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_read0:
        forall fuel fn_depth st sched_log (idx: reg_t) (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          post (Failure tt) ->
          post (let sched_le := log_get sched_log idx in
                let action_le := log_get action_log idx in
                if LE_may_read0 sched_le then
                  let/res v := r_get_reg st idx in
                  let le' := LE_set_read0 action_le in
                  Success (Some (gamma, log_set action_log idx le', v))
                else Success None) ->
          wp_action fuel fn_depth st sched_log (Read P0 idx) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_read1:
        forall fuel fn_depth st sched_log (idx: reg_t) (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          post (Failure tt) ->
          post (let/res v0 := r_get_reg st idx in
                let sched_le := log_get sched_log idx in
                let action_le := log_get action_log idx in
                if LE_may_read1 sched_le then
                  let le' := LE_set_read1 action_le in
                  let/res v :=
                     match action_le.(lwrite0), sched_le.(lwrite0) with
                     | Some v, _ => Success v
                     | _, Some v => Success v
                     | _, _ => Success v0
                     end in
                  Success (Some (gamma, log_set action_log idx le', v))
                else Success None) ->
          wp_action fuel fn_depth st sched_log (Read P1 idx) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_write0:
        forall fuel fn_depth st sched_log (idx: reg_t) (value: action) (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          wp_action (pred fuel) fn_depth st sched_log value
                    (fun res =>
                       match res with
                       | Success (Some (gamma, l, v)) =>
                         post (let sched_le := log_get sched_log idx in
                               let action_le := log_get l idx in
                               if LE_may_write0 sched_le && LE_may_write0 action_le then
                                 let le' := LE_set_write0 action_le v in
                                 Success (Some (gamma, log_set l idx le', []))
                               else Success None)
                       | _ => post res
                       end) gamma action_log ->
          wp_action fuel fn_depth st sched_log (Write P0 idx value) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_write1:
        forall fuel fn_depth st sched_log (idx: reg_t) (value: action) (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          wp_action (pred fuel) fn_depth st sched_log value
                    (fun res =>
                       match res with
                       | Success (Some (gamma, l, v)) =>
                         post (let sched_le := log_get sched_log idx in
                               let action_le := log_get l idx in
                               if LE_may_write1 sched_le && LE_may_write1 action_le then
                                 let le' := LE_set_write1 action_le v in
                                 Success (Some (gamma, log_set l idx le', []))
                               else Success None)
                       | _ => post res
                       end) gamma action_log ->
          wp_action fuel fn_depth st sched_log (Write P1 idx value) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_zop:
        forall fuel fn_depth st sched_log fn (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          post (Failure tt) ->
          post (let/res result := interp_zop struct_defs fn in
                Success (Some (gamma, action_log, result))) ->
          wp_action fuel fn_depth st sched_log (Zop fn) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_unop:
        forall fuel fn_depth st sched_log fn arg1 (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          wp_action (pred fuel) fn_depth st sched_log arg1
                    (fun res =>
                      match res with
                      | Success (Some (gamma, l, v)) =>
                        post (let/res result := interp_unop struct_defs fn v in
                              Success (Some (gamma, l, result)))
                      | _ => post res
                      end) gamma action_log ->
          wp_action fuel fn_depth st sched_log (Unop fn arg1) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_binop:
        forall fuel fn_depth st sched_log fn arg1 arg2 (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          wp_action (pred fuel) fn_depth st sched_log arg1
                    (fun res =>
                     match res with
                     | Success (Some (gamma, l, v1)) =>
                       wp_action (pred fuel) fn_depth st sched_log arg2
                                 (fun res =>
                                  match res with
                                  | Success (Some (gamma, l, v2)) =>
                                    post (let/res result := interp_binop struct_defs fn v1 v2 in
                                          Success (Some (gamma, l, result)))
                                  | _ => post res
                                  end) gamma l
                     | _ => post res
                     end) gamma action_log ->
          wp_action fuel fn_depth st sched_log (Binop fn arg1 arg2) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_internal_call:
        forall fuel fn_depth st sched_log fn arg (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          wp_action (pred fuel) fn_depth st sched_log arg
                    (fun res =>
                     match res with
                     | Success (Some (gamma, l, v)) =>
                        match lookup_int_fn int_fns fn ((__debug__ ("Int fn not found", fn) tt)) with
                         | Success (id, fn_spec) =>
                             if Nat.ltb id fn_depth then
                               wp_action (pred fuel) id st sched_log
                                            fn_spec.(fn_body)
                                            (fun res =>
                                             match res with
                                             | Success (Some (_, l, v)) =>
                                               post (Success (Some (gamma, l, v)))
                                             | _ => post res
                                             end) (fn_gamma fn_spec.(fn_arg_name) v) l
                             else post (Failure (__debug__ ("Int fn call out of bounds", fn, id) tt))
                         | Failure f => post (Failure f)
                         end
                     | _ => post res
                     end) gamma action_log ->
          wp_action fuel fn_depth st sched_log (InternalCall fn arg) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

      Lemma wp_external_call:
        forall fuel fn_depth st sched_log fn arg (post: action_postcondition)
          (gamma: gamma_t) (action_log: log_t),
          wp_action (pred fuel) fn_depth st sched_log arg
                    (fun res =>
                       match res with
                       | Success (Some (gamma, l, v)) =>
                         post (let/res result := ext_sigma fn v in
                            Success (Some (gamma, l, result)))
                       | _ => post res
                       end) gamma action_log ->
          wp_action fuel fn_depth st sched_log (ExternalCall fn arg) post gamma action_log.
      Proof.
        destruct fuel; auto.
      Qed.

    End WP.
End CPS.

Section ORAAT_CPS.
    Context (ext_sigma: ext_sigma_t).
    Context (int_fns: int_fn_env_t).
    Context (struct_defs: struct_env_t).
    Notation oraat_interp_action_cps := (oraat_interp_action_cps ext_sigma int_fns struct_defs).
    Notation oraat_interp_action := (oraat_interp_action ext_sigma int_fns struct_defs).

    Lemma oraat_interp_action_cps_correct:
      forall fuel (r: state_t) (a: action)
        {A} (k: oraat_action_continuation A) (gamma: gamma_t) (r_acc: state_t) (is_safe: bool),
        oraat_interp_action_cps fuel r a k gamma r_acc is_safe =
        k (oraat_interp_action fuel r r_acc is_safe gamma a).
    Proof.
      induction fuel; [ reflexivity | ]; simpl.
      destruct a; cbn; intros;
      repeat match goal with
             | _ => progress simpl
             | [ H: context[_ = _] |- _ ] => rewrite H
             | [  |- context[match ?x with _ => _ end] ] => destruct x
             | _ => reflexivity || assumption
             end.
    Qed.

    Lemma oraat_interp_action_cps_correct_rev:
      forall fuel (r: state_t) (a: action)
        (gamma: gamma_t) (r_acc: state_t) (is_safe: bool),
        oraat_interp_action fuel r r_acc is_safe gamma a =
        oraat_interp_action_cps fuel r a id gamma r_acc is_safe.
    Proof.
      intros; rewrite oraat_interp_action_cps_correct; reflexivity.
    Qed.

    Section WP.
      Notation oraat_wp_action := (oraat_wp_action ext_sigma int_fns struct_defs).

      Lemma oraat_wp_action_correct:
      forall fuel (r: state_t) (a: action)
        (gamma: gamma_t) (r_acc: state_t) (is_safe: bool)
        (post: oraat_action_postcondition),
        oraat_wp_action fuel r a post gamma r_acc is_safe <->
        post (oraat_interp_action fuel r r_acc is_safe gamma a).
      Proof.
        intros; unfold oraat_wp_action; rewrite oraat_interp_action_cps_correct; reflexivity.
      Qed.

      Lemma oraat_wp_fail:
        forall fuel r ty_hint
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          post (false, None) ->
          post (is_safe, None) ->
          oraat_wp_action fuel r (Fail ty_hint) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_var:
        forall fuel r (var: var_t)
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          post (false, None) ->
          post (let '(safe, v) := varenv_lookup_var' gamma var in
                (is_safe && safe, Some (gamma, r_acc, v))) ->
          oraat_wp_action fuel r (Var var) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_const:
        forall fuel r (cst: list bool)
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          post (false, None) ->
          post (is_safe, (Some (gamma, r_acc, cst))) ->
          oraat_wp_action fuel r (Const cst) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Notation "'let/bopt3' b ',' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
        (match expr with
         | (b, Some (v1, v2, v3)) => body
         | (b, None) => (b, None)
         end) (at level 200).

      Lemma oraat_wp_assign:
        forall fuel r var ex
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          oraat_wp_action (Nat.pred fuel) r ex
                          (fun res =>
                             post (let/bopt3 is_safe, gamma, r_acc, v_ex := res in
                                   let is_safe' := is_success (varenv_lookup_var gamma var tt) in
                                   (is_safe && is_safe', Some (varenv_update gamma var v_ex, r_acc, [])))
                          ) gamma r_acc is_safe ->
          oraat_wp_action fuel r (Assign var ex) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_seq:
        forall fuel r (a1 a2: action)
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          oraat_wp_action (Nat.pred fuel) r a1
                          (fun res =>
                             match res with
                             | (is_safe, Some (gamma, r_acc, v_ex)) =>
                               oraat_wp_action (Nat.pred fuel) r a2 post gamma r_acc is_safe
                             | _ => post res
                             end) gamma r_acc is_safe ->
          oraat_wp_action fuel r (Seq a1 a2) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_if:
        forall fuel r (cond tbranch fbranch: action)
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
            oraat_wp_action (Nat.pred fuel) r cond (fun res =>
                        match res with
                        | (is_safe, Some (gamma, r_acc, v_cond)) =>
                          let is_safe := ((Nat.eqb (Datatypes.length v_cond) 1) && is_safe) in
                          if bits_eq v_cond [true] then
                            oraat_wp_action (Nat.pred fuel) r tbranch post gamma r_acc is_safe
                          else
                            oraat_wp_action (Nat.pred fuel) r fbranch post gamma r_acc is_safe
                        | _ => post res
                        end) gamma r_acc is_safe ->
          oraat_wp_action fuel r (If cond tbranch fbranch) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_bind:
        forall fuel r var ex body
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          oraat_wp_action (Nat.pred fuel) r ex (fun res =>
                    match res with
                    | (is_safe, Some (gamma, r_acc, v_ex)) =>
                      oraat_wp_action (Nat.pred fuel) r body (fun res =>
                                  post (let/bopt3 is_safe, gamma', r_acc, v := res in
                                     (is_safe, Some (tl gamma', r_acc, v))))
                          (varenv_bind gamma var v_ex) r_acc is_safe
                    | _ => post res
                    end) gamma r_acc is_safe ->
          oraat_wp_action fuel r (Bind var ex body) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.


      Lemma oraat_wp_read0:
        forall fuel r idx
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          post (false, None) ->
          post (let '(safe, v) := r_get_reg' r idx in
                (is_safe && safe, Some (gamma, r_acc, v)))->
          oraat_wp_action fuel r (Read P0 idx) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_read1:
        forall fuel r idx
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          post (false, None) ->
          post (let '(safe, v) := r_get_reg' r_acc idx in
                (is_safe && safe, Some (gamma, r_acc, v)))->
          oraat_wp_action fuel r (Read P1 idx) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_write:
        forall fuel r port idx value
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          oraat_wp_action (Nat.pred fuel) r value (fun res =>
                      match res with
                      | (is_safe, Some (gamma, r_acc, v_value)) =>
                        post (is_safe, Some (gamma, state_set r_acc idx v_value, []))
                      | _ => post res
                      end) gamma r_acc is_safe ->
          oraat_wp_action fuel r (Write port idx value) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_zop:
        forall fuel r fn
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          post (false, None) ->
          post (let '(safe, v) := interp_zop' struct_defs fn in
                (is_safe && safe, Some (gamma, r_acc, v)))  ->
          oraat_wp_action fuel r (Zop fn) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_unop:
        forall fuel r fn arg
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          oraat_wp_action (Nat.pred fuel) r arg (fun res =>
                    match res with
                    | (is_safe, Some (gamma, r_acc, v_arg)) =>
                      post (let '(safe, v) := interp_unop' struct_defs fn v_arg in
                         (is_safe && safe, Some (gamma, r_acc, v)))
                    | _ => post res
                    end) gamma r_acc is_safe ->
          oraat_wp_action fuel r (Unop fn arg) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_binop:
        forall fuel r fn arg1 arg2
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          oraat_wp_action (Nat.pred fuel) r arg1 (fun res =>
                      match res with
                      | (is_safe, Some (gamma, r_acc, v_arg1)) =>
                        oraat_wp_action (Nat.pred fuel) r arg2 (fun res =>
                                    match res with
                                    | (is_safe, Some (gamma, r_acc, v_arg2)) =>
                                      post (let '(safe, v) := interp_binop' struct_defs fn v_arg1 v_arg2 in
                                         (is_safe && safe, Some (gamma, r_acc, v)))
                                    | _ => post res
                                    end) gamma r_acc is_safe
                      | _ => post res
                      end) gamma r_acc is_safe ->
          oraat_wp_action fuel r (Binop fn arg1 arg2) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_internal_call_spec:
        forall fuel r fn arg
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,

          oraat_wp_action (Nat.pred fuel) r arg (fun res =>
                           match res with
                           | (is_safe, Some (gamma, r_acc, v_arg)) =>
                             let '(safe, (arg_name, body)) := get_fn_arg_and_body' int_fns fn in
                             let is_safe := safe && is_safe in



                             oraat_wp_action (Nat.pred fuel) r body (fun res =>
                                         match res with
                                         | (is_safe, Some (_, r_acc, v)) =>
                                           post (is_safe, Some (gamma, r_acc, v))
                                         | _ => post res
                                         end) (fn_gamma arg_name v_arg) r_acc is_safe
                           | _ => post res
                           end) gamma r_acc is_safe ->
          oraat_wp_action fuel r (InternalCall fn arg) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.



      Lemma oraat_wp_internal_call:
        forall fuel r fn arg
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          oraat_wp_action (Nat.pred fuel) r arg (fun res =>
                           match res with
                           | (is_safe, Some (gamma, r_acc, v_arg)) =>
                             let '(safe, (arg_name, body)) := get_fn_arg_and_body' int_fns fn in
                             let is_safe := safe && is_safe in
                             oraat_wp_action (Nat.pred fuel) r body (fun res =>
                                         match res with
                                         | (is_safe, Some (_, r_acc, v)) =>
                                           post (is_safe, Some (gamma, r_acc, v))
                                         | _ => post res
                                         end) (fn_gamma arg_name v_arg) r_acc is_safe
                           | _ => post res
                           end) gamma r_acc is_safe ->
          oraat_wp_action fuel r (InternalCall fn arg) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      Lemma oraat_wp_external_call:
        forall fuel r fn arg
          (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe,
          oraat_wp_action (Nat.pred fuel) r arg
                          (fun res =>
                           match res with
                           | (is_safe, Some (gamma, r_acc, v_arg)) =>
                             post (let '(safe, v) := call_ext' ext_sigma fn v_arg in
                                   (is_safe && safe, Some (gamma, r_acc, v)))
                           | _ => post res
                           end) gamma r_acc is_safe ->
          oraat_wp_action fuel r (ExternalCall fn arg) post gamma r_acc is_safe.
      Proof.
        destruct fuel; propositional; cbn; auto.
      Qed.

      (* Lemma oraat_wp_action_struct_init: *)
      (*   forall fuel r struct_name fld_subst (post: oraat_action_postcondition) (gamma: gamma_t) r_acc is_safe, *)
      (*     post (false, None) -> *)
      (*     match fld_subst with *)
      (*     | [] => oraat_wp_action fuel r (Zop (StructInit struct_name)) post gamma r_acc is_safe *)
      (*     | _ => False *)
      (*     end -> *)
      (*     oraat_wp_action fuel r (action_struct_init struct_name fld_subst) post gamma r_acc is_safe. *)
      (* Proof. *)
      (*   destruct fuel; propositional; cbn; auto. *)
      (*   bash_destruct H0; auto. *)


    End WP.

End ORAAT_CPS.
