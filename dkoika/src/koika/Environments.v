Require Import koika.Common.
Require Import koika.Tactics.
Require Import koika.Syntax.
Require Import koika.Utils.
Require Import koika.Bits.
Require Import Program.Wf.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import FunInd.
Require Recdef.

(* Definition reg_t_beq := N.eqb. *)

Module Type Env_T.
  Parameter KeyT: Type.
  Parameter EqDec_KeyT: EqDec KeyT.
  Parameter EnvT: Type -> Type.
  Parameter empty : forall {Value: Type}, EnvT Value.
  Parameter update: forall {Value: Type}, EnvT Value -> KeyT -> (Value -> Value) -> Value -> EnvT Value.
  Parameter opt_get: forall {Value: Type}, EnvT Value -> KeyT -> option Value.
  Parameter zip_default : forall {Value1 Value2: Type}, EnvT Value1 -> EnvT Value2 -> Value1 -> Value2 ->
                                                   EnvT (Value1 * Value2).
  Parameter to_list: forall {Value: Type}, EnvT Value -> list (KeyT * Value).

  Parameter map: forall {Value1 Value2: Type}, (KeyT -> Value1 -> Value2) -> EnvT Value1 -> EnvT Value2.
  Parameter mapV: forall {Value1 Value2: Type}, (Value1 -> Value2) -> EnvT Value1 -> EnvT Value2.

  Parameter keys : forall {Value: Type}, EnvT Value -> list KeyT.

  Parameter update_correct_eq:
    forall {Value: Type} (env: EnvT Value) (key: KeyT) fn default,
      opt_get (update env key fn default) key =
        Some (match opt_get env key with
              | Some v0 => (fn v0)
              | None => (fn default)
              end).

  Parameter update_correct_neq:
    forall {Value: Type} (env: EnvT Value) key key' fn default ,
    key <> key' ->
    opt_get (update env key' fn default) key = opt_get env key.

  Parameter opt_get_find:
      forall {Value: Type} (env: EnvT Value) key,
      opt_get env key = match find (fun '(r, _) => (beq_dec (EQ := EqDec_KeyT) key r)) (to_list env) with
                        | Some (_, v) => Some v
                        | None => None
                        end.

  Parameter opt_get_empty:
      forall {Value: Type} key, @opt_get Value empty key = None.

  Parameter env_ext:
      forall {Value: Type} (env1 env2: EnvT Value),
        (forall key, opt_get env1 key = opt_get env2 key) ->
        env1 = env2.

  Parameter opt_get_mapV:
    forall {Value1 Value2: Type} (env: EnvT Value1) (fn: Value1 -> Value2) idx,
    opt_get (mapV fn env) idx = let/opt v := opt_get env idx in
                                Some (fn v).

  Parameter opt_get_map:
    forall {Value1 Value2: Type} (env: EnvT Value1) (fn: KeyT -> Value1 -> Value2) idx,
    opt_get (map fn env) idx = let/opt v := opt_get env idx in
                                Some (fn idx v).

  Parameter opt_get_zip_default:
    forall {Value1 Value2: Type} (default1: Value1) (default2: Value2)
      key (env1: EnvT Value1) (env2: EnvT Value2),
    opt_get (zip_default env1 env2 default1 default2) key =
      match opt_get env1 key, opt_get env2 key with
      | Some (v1), Some (v2) => Some (v1,v2)
      | Some v1, None => Some (v1, default2)
      | None, Some v2 => Some (default1, v2)
      | None, None => None
      end.

  Parameter In_to_list:
    forall {Value: Type} (env: EnvT Value) r v,
    In (r,v) (to_list env) <->
    opt_get env r = Some v.

  Parameter to_list_In_unique:
    forall {Value: Type} (env: EnvT Value) r v1 v2,
    In (r,v1) (to_list env) ->
    In (r,v2) (to_list env) ->
    v1 = v2.

  Parameter forallb: forall {Value: Type}, (KeyT -> Value -> bool) -> EnvT Value -> bool.
  Parameter forallb_forall : forall {Value: Type} (f: KeyT -> Value -> bool) (env: EnvT Value),
      forallb f env = true <-> (forall k v, opt_get env k = Some v -> f k v = true).

  Parameter opt_get_keys_eq: forall {Value1 Value2: Type} (env1: EnvT Value1) (env2: EnvT Value2),
      keys env1 = keys env2 ->
      forall reg, match opt_get env1 reg, opt_get env2 reg with
             | Some _, Some _ => True
             | None, None => True
             |_, _ => False
             end.

End Env_T.

Module Type OrderedT.
  Parameter T: Type.
  Parameter EqDec_T: EqDec T.
  Parameter ltb: T -> T -> bool.
  Parameter strict_order_T : strict_order ltb.
End OrderedT.

Module SortedEnv (Key: OrderedT) <: Env_T.

  Definition KeyT := Key.T.
  Instance EqDec_KeyT : EqDec Key.T := Key.EqDec_T.
  Notation sorted := (@sorted _ Key.ltb).

  Import Key.
  Section Env.
    Context {T: Type}.

    Definition env_t := list (Key.T * T).

    Inductive Increasing : list Key.T -> Prop :=
    | Increasing0 : Increasing []
    | Increasing__cons : forall x xs,
        (forall y, In y xs -> Key.ltb x y = true) ->
        Increasing xs ->
        Increasing (x :: xs).

    Lemma Increasing_nth_error:
      forall xs i j x y,
        Increasing xs ->
        (i < j)%nat ->
        nth_error xs i = Some x ->
        nth_error xs j = Some y ->
        Key.ltb x y = true.
    Proof.
      induction xs; intros * Hinc Hlt Hi Hj.
      - destruct j; simpl in *; try discriminate.
      - inversions Hinc.
        destruct i; simpl in *; simplify.
        + apply H1. destruct j; simpl in *; [lia | ].
          apply nth_error_In in Hj. assumption.
        + destruct j; simpl in *; [lia | ].
          assert (i < j) by lia.
          eapply IHxs; eauto.
    Qed.

    Lemma Increasing_nth_error':
      forall xs i j x y,
        Increasing xs ->
        Key.ltb x y = true ->
        nth_error xs i = Some x ->
        nth_error xs j = Some y ->
        i < j.
    Proof.
      induction xs; intros * Hinc Hlt Hi Hj.
      - destruct j; simpl in *; try discriminate.
      - inversions Hinc.
        destruct i; simpl in *; simplify.
        + destruct j ;simpl in *; simplify; try lia.
          rewrite (@ltb_antirefl _ _ Key.strict_order_T) in Hlt. discriminate.
        + destruct j; simpl in *; simplify; try lia.
          { apply nth_error_In in Hi. specialize H1 with (1 := Hi).
            pose proof (@ltb_antisym _ _ Key.EqDec_T Key.strict_order_T) as Hantisym.
            destruct_with_eqn (@beq_dec _ Key.EqDec_T x y).
            - simplify. rewrite (@ltb_antirefl _ _ Key.strict_order_T) in H1. discriminate.
            - rewrite Hantisym in Hlt by auto. rewrite H1 in *. discriminate.
          }
          { assert (i < j).
            { eapply IHxs; eauto. }
            lia.
          }
    Qed.


    Lemma Increasing_iff_sorted:
      forall (xs: list Key.T),
      Increasing xs <-> sorted xs = true.
    Proof.
      split.
      - induction xs; auto.
        intros. inversions H. propositional. simpl.
        destruct xs; auto. rewrite andb_true_iff.
        split; auto.
        apply H2. constructor. auto.
      - induction xs; eauto.
        + intros. constructor.
        + intros Hsorted. constructor; auto.
          * intros. simpl in Hsorted.
            destruct xs; auto. apply andb_true_iff in Hsorted. propositional.
            inversions IHxs. simplify.
            inversions H; try auto.
            apply H2 in H0. apply (@ltb_trans _ _ Key.strict_order_T) with (1 := Hsorted0). auto.
          * apply IHxs. eapply (sorted_cons); eauto.
    Qed.

    Lemma not_Increasing_iff_not_sorted:
      forall (xs: list Key.T),
      (not (Increasing xs)) <-> sorted  xs = false.
    Proof.
      intros. unfold not. split.
      - intros. destruct_with_eqn (sorted xs); auto. apply Increasing_iff_sorted in Heqb. auto.
      - intros. apply Increasing_iff_sorted in H0. congruence.
    Qed.

    Record EnvT' : Type :=
      { Env : env_t;
        pf_sorted : (sorted (map fst Env)) = true
      }.
    Definition EnvT := EnvT'.

    Lemma sorted_empty : sorted [] = true.
    Proof. auto.
    Qed.

    Lemma Increasing_empty : Increasing [].
    Proof. constructor. Qed.

    Definition empty : EnvT :=
      {| Env := [];
         pf_sorted := sorted_empty
      |}.

    Fixpoint update' (env: env_t) (key: Key.T) (fn: T -> T) (default: T) : env_t :=
     match env with
     | [] => [(key, fn default)]
     | (x,v)::xs =>
       if Key.ltb x key then
         (x,v) :: (update' xs key fn default)
       else if beq_dec x key then
         (x, fn v)::xs
       else
         (key, fn default)::((x,v)::xs)
     end.

    Lemma update_in:
      forall env reg fn default,
      exists i, nth_error (map fst (update' env reg fn default)) i = Some reg.
    Proof.
      induction env.
      - simpl. propositional. exists 0. auto.
      - propositional. simpl. destruct_match_pairs; subst.
        specialize IHenv with (reg := reg) (fn := fn) (default := default). propositional.
        destruct_match; simpl.
        + exists (S i). eauto.
        + destruct_match; simpl.
          * exists 0. simplify. subst. auto.
          * exists 0; auto.
    Qed.

    Lemma update_In:
      forall env reg fn default x,
        In x (map fst (update' env reg fn default)) ->
        In x (map fst env) \/ x = reg.
    Proof.
      induction env; simpl; auto.
      - intros. destruct H; auto.
      - intros; destruct_match_pairs; subst.
        repeat destruct_matches_in_hyp H; simpl in *.
        + destruct H; subst; auto.
          specialize IHenv with (1 := H). destruct IHenv; auto.
        + destruct H; auto.
        + simplify.
          destruct H; auto.
    Qed.
    Hint Resolve Key.strict_order_T.

    Lemma pf_sorted_update':
      forall env reg fn default,
        Increasing (map fst env) ->
        Increasing (map fst (update' env reg fn default)).
    Proof.
      induction env; intros * Hincreasing.
      - propositional. simpl in *.
        constructor; auto.
      - simpl. destruct_match_pairs; subst; simpl in *.
        repeat destruct_match; simpl; simplify.
        + inversions Hincreasing.
          constructor; eauto.
          specialize IHenv with (1 := H2).
          specialize IHenv with (reg := reg) (fn := fn) (default := default).
          intros * HIn.
          specialize update_In with (1 := HIn); intros HIn'. destruct HIn'; auto; subst.
          auto.
        + subst. auto.
        + constructor; auto.
          intros * Hin. inversions Hin; try lia.
          * rewrite<-beq_dec_false_iff with (EQ := EqDec_KeyT) in Heqb0.
            rewrite ltb_antisym with (eq_dec := EqDec_KeyT).
            { rewrite Heqb. auto. }
            { apply Key.strict_order_T. }
            { simplify. rewrite beq_dec_false_iff. auto. }
          * inversions Hincreasing; eauto. specialize H2 with (1 := H).
            rewrite ltb_antisym with (eq_dec := EqDec_KeyT) in Heqb; auto.
            2: { rewrite beq_dec_false_iff. auto. }
            rewrite negb_false_iff in Heqb.
            eapply (@ltb_trans _ _ Key.strict_order_T); eauto.
    Qed.

    Lemma pf_sorted_update :
      forall env reg fn default,
        sorted (map fst env) = true ->
        sorted (map fst (update' env reg fn default)) = true.
    Proof.
      intros. apply Increasing_iff_sorted. apply pf_sorted_update'. apply Increasing_iff_sorted.
      assumption.
    Qed.


    Definition update (env: EnvT) (key: Key.T) (fn: T -> T) (default: T) : EnvT :=
      {| Env := update' env.(Env) key fn default;
         pf_sorted := pf_sorted_update _ _ _ _ (env.(pf_sorted))
      |}.

    Definition opt_get (env: EnvT) (key: Key.T) : option T :=
      let/opt2 _, v := find (fun '(r, _) => (beq_dec key) r) env.(Env) in
      Some v.

    Lemma update_correct_eq':
      forall env reg fn default ,
      opt_get (update env reg fn default) reg =
        Some
          match find (fun '(r, _) => beq_dec reg r) env.(Env) with
          | Some (_, v0) => fn v0
          | None => fn default
          end.
    Proof.
      destruct env. unfold opt_get, update; cbn [Env].
      apply Increasing_iff_sorted in pf_sorted0.
      induction Env0; simpl.
      - intros. consider opt_get; simpl. rewrite beq_dec_refl. reflexivity.
      - destruct_match_pairs.
        inversions pf_sorted0; propositional.
        specialize IHEnv0 with (reg := reg) (fn := fn) (default := default).
        destruct_matches_in_hyp IHEnv0; destruct_match_pairs; simplify.
        destruct_match; simplify; simpl.
        + destruct_match; simplify.
          { rewrite (@ltb_antirefl _ _ Key.strict_order_T)in Heqb. discriminate. }
          destruct_match; simplify; auto.
        + destruct_match; simplify; subst; try lia.
          * simpl. rewrite beq_dec_refl. reflexivity.
          * simpl. rewrite beq_dec_refl. destruct_match; simplify; try lia.
            destruct_match; auto. destruct_match_pairs; subst.
            apply find_some in Heqo0; propositional; simplify; subst.
            eapply in_map in Heqo1.
            specialize H1 with (1 := Heqo1). simpl in *.
            congruence.
     Qed.

    Lemma update_correct_eq:
    forall env (key: Key.T) fn default,
      opt_get (update env key fn default) key =
        Some (match opt_get env key with
              | Some v0 => (fn v0)
              | None => (fn default)
              end).
    Proof.
      intros. rewrite update_correct_eq'.
      unfold opt_get. repeat destruct_match; auto.
    Qed.

    Lemma update_correct_neq:
      forall env reg reg' fn default ,
      reg <> reg' ->
      opt_get (update env reg' fn default) reg = opt_get env reg.
    Proof.
      destruct env. unfold opt_get, update; cbn [Env].
      apply Increasing_iff_sorted in pf_sorted0.
      induction Env0; simpl in *.
      - intros. destruct_match; simplify; subst; auto.
      - intros. destruct_match_pairs; subst. simpl in *.
        inversions pf_sorted0. propositional.
        specialize IHEnv0 with (1 := H) (fn := fn) (default := default).
        destruct_match; simpl; simplify.
        + destruct_match; simplify; auto.
        + destruct_match; simplify; simpl; auto.
          * destruct_match; simplify; simpl; subst; auto.
          * destruct_match; simplify; try lia.
            destruct_match; simplify; try lia; auto.
    Qed.

    Lemma P_opt_get_update:
      forall P reg env fn default nv,
      (forall v, P (fn v)) ->
      opt_get (update env reg fn default) reg = Some nv ->
      P nv.
    Proof.
      intros. rewrite update_correct_eq in *.
      simplify. repeat destruct_match; auto.
    Qed.


    Definition to_list (env: EnvT) := env.(Env).

    Definition from_list (xs: env_t) (pf: sorted (map fst xs) = true) : EnvT :=
      {| Env := xs;
         pf_sorted := pf
      |}.

    Lemma opt_get_find:
      forall env reg,
      opt_get env reg = match find (fun '(r, _) => beq_dec reg r) (to_list env) with
                        | Some (_, v) => Some v
                        | None => None
                        end.
    Proof.
      intros. unfold opt_get. reflexivity.
    Qed.

    Lemma opt_get_empty:
      forall reg, opt_get empty reg = None.
    Proof.
      auto.
    Qed.

    Lemma eq_value (env1 env2: EnvT) :
      Env env1 = Env env2 ->
      env1 = env2.
    Proof.
      cbv [Env]; destruct env1 as [env1 p1]; destruct env2 as [env2 p2].
      intro. subst env2.
      apply f_equal.
      apply Eqdep_dec.UIP_dec.
      apply bool_dec.
    Qed.

    Lemma env_ext:
      forall env1 env2,
        (forall reg, opt_get env1 reg = opt_get env2 reg) ->
        env1 = env2.
    Proof.
      intros [l1 pf1] [l2 pf2] Hget_eq.
      apply eq_value. unfold opt_get in *; cbn [Env] in *.
      apply Increasing_iff_sorted in pf1.
      apply Increasing_iff_sorted in pf2.
      revert pf1 l2 pf2 Hget_eq.
      induction l1; intros pf1 l2 pf2 Hget_eq; simpl in *.
      - destruct l2 as [ | [k v] t2]; [reflexivity |].
        specialize Hget_eq with (reg := k). simpl in *.
        rewrite beq_dec_refl in Hget_eq. discriminate.
      - destruct a as [k1 v1].
        destruct l2 as [|[k2 v2] l2].
        + simpl in *. specialize (Hget_eq k1). rewrite beq_dec_refl in Hget_eq. discriminate.
        + simpl in *.
          inversions pf1. propositional.
          inversions pf2.
          destruct (beq_dec k1 k2) eqn:Heq; simplify; subst.
          * specialize (Hget_eq k2) as Hget_eq2.
            rewrite beq_dec_refl in Hget_eq2. simplify.
            f_equal.
            eapply IHl1; auto. intros.
            specialize (Hget_eq reg).
            destruct (beq_dec reg k2) eqn:Heq'; simplify; auto.
            destruct_match; destruct_match_pairs; subst.
            { apply find_some in Heqo; propositional; simplify.
              eapply in_map in Heqo0. specialize H1 with (1 := Heqo0); simpl in *.
              rewrite (@ltb_antirefl _ _ Key.strict_order_T) in H1.
              discriminate.
            }
            { destruct_match; auto.
              apply find_some in Heqo0; propositional; simplify.
              eapply in_map in Heqo1. specialize H3 with (1 := Heqo1); simpl in *.
              rewrite (@ltb_antirefl _ _ Key.strict_order_T) in H3.
              lia.
            }
         * exfalso.
            specialize (Hget_eq k1) as Hget_eq1.
            rewrite beq_dec_refl in Hget_eq1.
            destruct_matches_in_hyp Hget_eq1; simplify; try congruence.
            destruct_matches_in_hyp Hget_eq1; [ | discriminate].
            destruct_match_pairs; simplify.
            apply find_some in Heqo; propositional; simplify.
            eapply in_map in Heqo0. specialize H3 with (1 := Heqo0).
            simpl in *.
            specialize (Hget_eq k2). rewrite beq_dec_refl in Hget_eq.
            destruct_matches_in_hyp Hget_eq; simplify; try congruence.
            apply find_some in Heqo; propositional; simplify.
            eapply in_map in Heqo1. specialize H1 with (1 := Heqo1). simpl in *.
            rewrite (@ltb_antisym _ _ Key.EqDec_T Key.strict_order_T) in H1.
            { rewrite H3 in *. discriminate. }
            { apply beq_dec_false_iff. auto. }
    Qed.

    Lemma In_to_list:
      forall (env: EnvT) r v,
        In (r,v) (to_list env) <->
        opt_get env r = Some v.
    Proof.
      destruct env as [env pf]; unfold to_list, opt_get; simpl.
      apply Increasing_iff_sorted in pf.
      induction env.
      - simpl. intros; split; auto; discriminate.
      - simpl. intros. split; intros.
        + destruct H; subst; auto.
          * rewrite beq_dec_refl. reflexivity.
          * destruct_match_pairs; simpl in *; subst.
            inversions pf; propositional.
            destruct_match; simplify; subst.
            { eapply in_map in H. specialize H2 with (1 := H). simpl in *.
              rewrite (@ltb_antirefl _ _ Key.strict_order_T) in *.
              discriminate.
            }
            { apply IHenv. auto. }
        + destruct_match_pairs; subst; simpl in *.
          inversions pf; propositional.
          destruct_matches_in_hyp H; simplify; simplify; auto.
          apply find_some in Heqo. propositional; simplify; subst; auto.
    Qed.
    Lemma to_list_In_unique:
      forall (env: EnvT) r v1 v2,
        In (r,v1) (to_list env) ->
        In (r,v2) (to_list env) ->
        v1 = v2.
    Proof.
      intros * In1 In2.
      apply In_to_list in In1.
      apply In_to_list in In2.
      rewrite In1 in In2. simplify; auto.
    Qed.

    Definition forallb (f: Key.T -> T -> bool) (env: EnvT) : bool :=
      forallb (fun '(k,v) => f k v) (to_list env).

    Lemma forallb_forall : forall (f: Key.T -> T -> bool) (env: EnvT),
      forallb f env = true <-> (forall k v, opt_get env k = Some v -> f k v = true).
    Proof.
      intros; split; intros.
      - rewrite opt_get_find in H0. simplify. apply find_some in Heqo; propositional.
        rewrite beq_dec_iff in Heqo1. subst. consider forallb.
        rewrite forallb_forall in H. specialize H with (1 := Heqo0). simpl in *. auto.
      - unfold forallb. rewrite forallb_forall.
        intros. destruct_match_pairs; subst.
        rewrite In_to_list in H0.
        apply H. auto.
    Qed.

    Definition keys (env: EnvT) : list Key.T :=
      map fst (to_list env).


  End Env.
  Arguments EnvT : clear implicits.
  Arguments env_t : clear implicits.
  Section ZipDefault.
    Context {T1: Type}.
    Context {T2: Type}.
    Fixpoint zip_default__fuel' (fuel: nat)
                              (env1: env_t T1)
                              (env2: env_t T2)
                              (default1: T1)
                              (default2: T2)
                             : env_t (T1 * T2) :=
      match fuel with
      | 0 => []
      | S n =>
        match env1, env2 with
        | [], _ => map (fun '(r,v) => (r, (default1, v))) env2
        | _, [] => map (fun '(r,v) => (r, (v, default2))) env1
        | (r1,v1)::x1s, (r2,v2)::x2s =>
            if Key.ltb r1 r2 then
              (r1,(v1,default2))::(zip_default__fuel' n x1s env2 default1 default2)
            else if beq_dec r1 r2 then
              (r1, (v1, v2))::(zip_default__fuel' n x1s x2s default1 default2)
            else
              (r2, (default1, v2))::(zip_default__fuel' n env1 x2s default1 default2)
        end
      end.
    Definition zip_default__fuel (env1: env_t T1) (env2: env_t T2) (default1: T1) (default2: T2)
                               : env_t (T1 * T2) :=
      zip_default__fuel' (S (List.length env1 + List.length env2)) env1 env2 default1 default2.

    Function zip_default'' (arg: (env_t T1 * env_t T2 * T1 * T2))
            {measure (fun '(env1,env2,_, _) => (List.length env1 + List.length env2))}
      : env_t (T1 * T2) :=
      let '(env1,env2, default1, default2) := arg in
      match env1, env2 with
      | [], _ => map (fun '(r,v) => (r, (default1, v))) env2
      | _, [] => map (fun '(r,v) => (r, (v, default2))) env1
      | (r1,v1)::x1s, (r2,v2)::x2s =>
          if Key.ltb r1 r2 then
            (r1,(v1,default2))::(zip_default'' (x1s,env2,default1, default2))
          else if beq_dec r1 r2 then
            (r1, (v1, v2))::(zip_default'' (x1s,x2s,default1, default2))
          else
            (r2, (default1, v2))::(zip_default'' (env1,x2s,default1, default2))
      end.
    all: simpl; lia.
    Qed.


    Definition zip_default' env1 env2 default1 default2 := zip_default'' (env1,env2,default1, default2).

    Lemma zip_default_fuel_enough':
      forall fuel env1 env2 default1 default2,
      fuel > List.length env1 + List.length env2 ->
      zip_default__fuel' fuel env1 env2 default1 default2 = zip_default' env1 env2 default1 default2.
    Proof.
      induction fuel; consider zip_default'; intros * Hfuel; rewrite zip_default''_equation.
      - intros; simpl in *.
        destruct_with_eqn env1; simpl in *; try lia.
      - simpl. destruct_with_eqn env1; simpl in *; try lia; auto.
        destruct_match_pairs; subst.
        destruct_with_eqn env2; simpl in *; try lia; auto.
        destruct_match_pairs; subst.
        destruct_match; auto.
        + rewrite IHfuel; simpl; auto.
          revert Hfuel. lia.
        + destruct_match.
          * rewrite IHfuel; simpl; auto.  revert Hfuel. lia.
          * rewrite IHfuel; auto. simpl. revert Hfuel; lia.
    Qed.

    Lemma zip_default_fuel_enough:
      forall env1 env2 default1 default2,
      zip_default__fuel env1 env2 default1 default2 = zip_default' env1 env2 default1 default2.
    Proof.
      intros; unfold zip_default__fuel.
      apply zip_default_fuel_enough'. lia.
    Qed.

    Lemma zip_default''_result:
      forall env1 env2 reg default1 default2 v1 v2,
      Increasing (map fst env1) ->
      Increasing (map fst env2) ->
      In (reg, (v1, v2)) (zip_default'' (env1,env2,default1, default2)) ->
      (v1 = default1 \/ (In (reg, v1) env1)) /\
      (v2 = default2 \/ (In (reg, v2) env2)) /\
      (In reg (map fst env1) \/ In reg (map fst env2)).
    Proof.
      induction env1.
      - simpl. intros * Henv1 Henv2 HIn.
        rewrite zip_default''_equation in HIn.
        apply in_map_iff in HIn. propositional. destruct_match_pairs. simplify_tupless.
        repeat split; auto. right.
        eapply in_map_iff; eauto.
        exists (reg, v2); eauto.
      - induction env2; simpl; intros * Henv1 Henv2 HIn.
        + specialize IHenv1 with (env2 := []) (reg := reg) (default1 := default1) (default2 := default2)
                                 (v1 := v1) (v2 := v2); simpl in *; propositional.
          inversions Henv1; propositional.
          rewrite zip_default''_equation in HIn. destruct_match_pairs; simpl in *; subst.
          destruct HIn; simplify_tupless.
          * split_ands_in_goal; auto.
          * rewrite zip_default''_equation in IHenv1.
            destruct env1; simpl in *; auto. destruct_match_pairs; subst; simpl in *; propositional.
            destruct IHenv3; auto.
            destruct IHenv1; propositional.
            split; auto.
            destruct H; simplify_tupless; auto.
            destruct IHenv0; simplify_tupless; auto.
        + specialize IHenv1 with (reg := reg) (default1 := default1) (default2 := default2) (v1 := v1) (v2 := v2).
          specialize IHenv2 with (reg := reg) (default1 := default1) (default2 := default2) (v1 := v1) (v2 := v2).
          propositional. simpl in *.
          rewrite zip_default''_equation in HIn.
          destruct_match_pairs; subst.
          repeat destruct_matches_in_hyp HIn; simplify; simplify_tupless; simpl in *.
          * specialize IHenv1 with (env2 := (t1,t2)::env2).
            inversions Henv1; propositional.
            inversions Henv2; propositional.
            destruct HIn; simplify_tupless; propositional; simpl in *.
            split_ands_in_goal; auto.
            { destruct IHenv0; auto. }
            { destruct IHenv4; auto. }
          * specialize IHenv1 with (env2 := env2).
            inversions Henv1; propositional.
            inversions Henv2; propositional.
            destruct HIn; simplify_tupless; propositional.
            destruct IHenv4.
            { bash_destruct IHenv0. specialize H1 with (1 := H0).
              split_ands_in_goal; auto.
              { destruct IHenv0; auto. }
              { destruct IHenv1; auto. }
            }
            { bash_destruct IHenv1. specialize H3 with (1 := H0).
              split_ands_in_goal; auto.
              { destruct IHenv0; auto. }
              { destruct IHenv1; auto. }
            }
          * inversions Henv2; propositional.
            inversions Henv1; propositional.
            destruct HIn; simplify_tupless; propositional.
            { split_ands_in_goal; propositional.
              { destruct IHenv2; auto. }
              { destruct IHenv4; auto. }
            }
    Qed.


    Lemma zip_default''_In:
      forall reg env1 env2 default1 default2,
        Increasing (map fst env1) ->
        Increasing (map fst env2) ->
        In reg (map fst (zip_default'' (env1,env2, default1, default2))) ->
        In reg (map fst env1) \/ In reg (map fst env2).
    Proof.
      intros * Henv1 Henv2 HIn.
      specialize zip_default''_result with (1 := Henv1) (2 := Henv2).
      intros Hres.
      eapply in_map_iff in HIn; propositional.
      destruct x. destruct p.
      specialize Hres with (1 := HIn2); propositional.
    Qed.

    Lemma pf_sorted_zip_default':
      forall env1 env2 default1 default2,
      Increasing (map fst env1) ->
      Increasing (map fst env2) ->
      Increasing (map fst (zip_default' env1 env2 default1 default2)).
    Proof.
      unfold zip_default'; induction env1.
      - intros * X1 X2. rewrite zip_default''_equation; simpl; auto.
        rewrite map_map.
        erewrite map_ext; eauto. intros; destruct_match_pairs; auto.
      - induction env2; intros * X1 X2.
        + specialize IHenv1 with (env2 := []) (default1 := default1) (default2 := default2).
          rewrite zip_default''_equation in *. destruct_match_pairs; subst.
          simpl in *. inversions X1; propositional.
          constructor; auto.
          * intros. rewrite map_map in H. erewrite map_ext in H; eauto.
            intros; destruct_match_pairs; auto.
          * destruct env1; simpl; auto; destruct_match_pairs; simpl in *.
            rewrite map_map. erewrite map_ext; eauto.
            intros; destruct_match_pairs; auto.
        + simpl in *; propositional.
          specialize IHenv2 with (default1 := default1) (default2 := default2).
          rewrite zip_default''_equation. destruct_match_pairs; subst; simpl in *.
          inversions X2. propositional.
          inversions X1.
          repeat destruct_match; simpl; simplify; subst; auto.
          * constructor; auto.
            { intros. apply zip_default''_In in H; simpl; auto; [ | constructor; auto].
              destruct H; simpl in H; auto. destruct H; subst; try lia; auto.
              specialize H1 with (1 := H).
              eapply (@ltb_trans _ _ Key.strict_order_T); eauto.
            }
            { apply IHenv1; auto. simpl. constructor; auto. }
          * constructor; auto.
            { intros. apply zip_default''_In in H; simpl; auto.
              destruct H; simpl in H; auto.
            }
          * constructor; auto.
            intros. apply zip_default''_In in H; auto; [ | constructor; auto]; simpl in H.
            destruct H; auto. destruct H; subst; auto.
            { rewrite (@ltb_antisym _ _ EqDec_KeyT Key.strict_order_T); auto.
              2: { apply beq_dec_false_iff. auto. }
              rewrite_solve.
            }
            specialize H3 with (1 := H).
            eapply (@ltb_trans _ _ Key.strict_order_T); eauto.
            rewrite (@ltb_antisym _ _ EqDec_KeyT Key.strict_order_T); auto.
            2: { apply beq_dec_false_iff. auto. }
              rewrite_solve.
    Qed.

    Lemma pf_sorted_zip_default:
      forall env1 env2  default1 default2,
      sorted (map fst env1) = true ->
      sorted (map fst env2) = true ->
      sorted (map fst (zip_default' env1 env2 default1 default2)) = true.
    Proof.
      intros.
      apply Increasing_iff_sorted.
      apply pf_sorted_zip_default'; apply Increasing_iff_sorted; auto.
    Qed.

    Lemma pf_sorted_zip_default__fuel:
      forall env1 env2 default1 default2,
      sorted (map fst env1) = true ->
      sorted (map fst env2) = true ->
      sorted (map fst (zip_default__fuel env1 env2 default1 default2)) = true.
    Proof.
      intros. rewrite zip_default_fuel_enough.
      apply pf_sorted_zip_default; auto.
    Qed.

    Definition zip_default (env1: EnvT T1) (env2: EnvT T2) default1 default2 : EnvT (T1 * T2) :=
      {| Env := zip_default__fuel env1.(Env) env2.(Env) default1 default2;
         pf_sorted := @pf_sorted_zip_default__fuel env1.(Env) env2.(Env) default1 default2
                                               env1.(pf_sorted) env2.(pf_sorted)
      |}.
  End ZipDefault.

  Lemma pf_mapV_sorted':
    forall (T1 T2: Type) (env: env_t T1) (fn: T1 -> T2),
    Increasing (map fst env) ->
    Increasing (map fst (map (fun '(reg, v) => (reg, fn v)) env)).
  Proof.
    induction env; simpl in *; propositional.
    destruct_match_pairs; subst; simpl in *.
    inversions H. constructor; auto.
    intros.
    rewrite map_map in H.
    erewrite map_ext in H.
    { apply H2. eauto. }
    { intros; destruct_match; auto. }
  Qed.

  Lemma pf_mapV_sorted:
    forall (T1 T2: Type) (env: env_t T1) (fn: T1 -> T2),
    sorted (map fst env) = true ->
    sorted (map fst (map (fun '(reg, v) => (reg, fn v)) env)) = true.
  Proof.
    intros. apply Increasing_iff_sorted. apply pf_mapV_sorted'. apply Increasing_iff_sorted. auto.
  Qed.

  Definition mapV {T1 T2: Type} (fn: T1 -> T2) (env: EnvT T1): EnvT T2 :=
    {| Env := map (fun '(reg, v) => (reg, fn v)) env.(Env);
       pf_sorted := pf_mapV_sorted _ _ _ _ env.(pf_sorted)
    |}.

  Lemma pf_map_sorted':
    forall (T1 T2: Type) (env: env_t T1) (fn: Key.T -> T1 -> T2),
    Increasing (map fst env) ->
    Increasing (map fst (map (fun '(reg, v) => (reg, fn reg v)) env)).
  Proof.
    induction env; simpl in *; propositional.
    destruct_match_pairs; subst; simpl in *.
    inversions H. constructor; auto.
    intros.
    rewrite map_map in H.
    erewrite map_ext in H.
    { apply H2. eauto. }
    { intros; destruct_match; auto. }
  Qed.

  Lemma pf_map_sorted:
    forall (T1 T2: Type) (env: env_t T1) (fn: Key.T -> T1 -> T2),
    sorted (map fst env) = true ->
    sorted (map fst (map (fun '(reg, v) => (reg, fn reg v)) env)) = true.
  Proof.
    intros. apply Increasing_iff_sorted. apply pf_map_sorted'.  apply Increasing_iff_sorted. auto.
  Qed.

  Definition map {Value1 Value2: Type} (fn: Key.T -> Value1 -> Value2) (env: EnvT Value1) : EnvT Value2 :=
    {| Env := map (fun '(reg, v) => (reg, fn reg v)) env.(Env);
       pf_sorted := pf_map_sorted _ _ _ _ env.(pf_sorted)
    |}.

  Lemma opt_get_mapV:
    forall {Value1 Value2: Type} (env: EnvT Value1) (fn: Value1 -> Value2) idx,
    opt_get (mapV fn env) idx = let/opt v := opt_get env idx in
                                Some (fn v).
  Proof.
    destruct env. unfold mapV, opt_get; cbn [Env].
    apply Increasing_iff_sorted in pf_sorted0.
    induction Env0; simpl in *; auto; intros.
    destruct_match_pairs; simplify_tupless; simpl in *.
    destruct_match; simplify; subst; auto.
    apply IHEnv0. inversions pf_sorted0; auto.
  Qed.

  Lemma opt_get_map:
    forall {Value1 Value2: Type} (env: EnvT Value1) (fn: Key.T -> Value1 -> Value2) idx,
    opt_get (map fn env) idx = let/opt v := opt_get env idx in
                                Some (fn idx v).
  Proof.
    destruct env. unfold map, opt_get; cbn [Env].
    apply Increasing_iff_sorted in pf_sorted0.
    induction Env0; simpl in *; auto; intros.
    destruct_match_pairs; simplify_tupless; simpl in *.
    destruct_match; simplify; subst; auto.
    apply IHEnv0. inversions pf_sorted0; auto.
  Qed.

  Lemma opt_get_zip_default:
    forall {Value1 Value2: Type} default1 default2 reg (env1: EnvT Value1) (env2: EnvT Value2),
    opt_get (zip_default env1 env2 default1 default2) reg =
      match opt_get env1 reg, opt_get env2 reg with
      | Some (v1), Some (v2) => Some (v1,v2)
      | Some v1, None => Some (v1, default2)
      | None, Some v2 => Some (default1, v2)
      | None, None => None
      end.
  Proof.
    destruct env1; destruct env2. unfold zip_default, zip_default', opt_get; simpl.
    apply Increasing_iff_sorted in pf_sorted0.
    apply Increasing_iff_sorted in pf_sorted1.
    rewrite zip_default_fuel_enough; unfold zip_default' in *.
    revert pf_sorted0 Env1 pf_sorted1.
    induction Env0; simpl; auto; intros * pf_sorted0 Env1 pf_sorted1.
    - induction Env1.
      + intros; simpl. rewrite zip_default''_equation. reflexivity.
      + intros; simpl in *. rewrite zip_default''_equation.
        simpl. destruct_match_pairs; simplify_tupless.
        destruct_match; simplify; auto.
        rewrite zip_default''_equation in IHEnv1.
        apply IHEnv1.
        inversions pf_sorted1.
        auto.
    - induction Env1.
      + simpl. rewrite zip_default''_equation. destruct_match_pairs; subst; simplify.
        simpl in *.
        destruct_match; simplify; auto.
        specialize IHEnv0 with (Env1 := []). simpl in *; inversions pf_sorted0; propositional.
        rewrite zip_default''_equation in IHEnv0.
        destruct Env0; simpl in *; auto.
        destruct_match_pairs; subst; simpl in *; auto.
      + rewrite zip_default''_equation; simpl.
        destruct_match_pairs; simplify_tupless.
        simpl in *.
        destruct_match; simplify.
        * (* specialize IHEnv0 with (Env1 := (r0,v0)::Env1). simpl in *. *)
          inversions pf_sorted0; propositional.
          inversion pf_sorted1; propositional.
          simpl. destruct_match; simplify; subst.
          { destruct_match; simplify; subst; auto.
            { rewrite (@ltb_antirefl _ _ Key.strict_order_T) in *. discriminate. }
            destruct_match; destruct_match_pairs; subst; auto.
            exfalso.
            apply find_some in Heqo; propositional; simplify; subst.
            eapply in_map in Heqo0. specialize H3 with (1 := Heqo0). simpl in *.
            rewrite (@ltb_antisym _ _ Key.EqDec_T Key.strict_order_T) in H3.
            2: { rewrite beq_dec_false_iff. auto. }
            rewrite Heqb in *. discriminate.
          }
          { specialize IHEnv0 with (Env1 := (t0,v0)::Env1). simpl in *. propositional. }
        * inversions pf_sorted0. inversions pf_sorted1. propositional.
          destruct_match; simplify; subst.
          { specialize IHEnv0 with (Env1 := Env1). simpl.
            destruct_match; simplify; subst; auto.
          }
          { specialize IHEnv0 with (Env1 := Env1). propositional.
            simpl. destruct_match; simplify; subst; try lia.
            { destruct_match; simplify; try lia.
              destruct_match; auto.
              destruct_match_pairs; subst; auto.
              apply find_some in Heqo. propositional; simplify; subst.
              eapply in_map in Heqo0. specialize H1 with (1 := Heqo0). simpl in *. congruence.
            }
            { destruct_match; destruct_match_pairs; subst; auto.
              - setoid_rewrite Heqo in IHEnv1; auto.
              - setoid_rewrite Heqo in IHEnv1. auto.
            }
          }
  Qed.

  Lemma opt_get_keys_eq: forall {Value1 Value2: Type} (env1: EnvT Value1) (env2: EnvT Value2),
      keys env1 = keys env2 ->
      forall reg, match opt_get env1 reg, opt_get env2 reg with
             | Some _, Some _ => True
             | None, None => True
             |_, _ => False
             end.
  Proof.
    unfold keys, to_list, opt_get.
    intros. repeat destruct_match; auto; subst.
    - apply find_some in Heqo. propositional; simplify.
      eapply in_map with (f := fst)  in Heqo1. simpl in Heqo1. rewrite H in *.
      apply in_map_iff in Heqo1. propositional.
      eapply find_none with (x := x) in Heqo0; auto. destruct x. simpl in *. simplify. contradiction.
    - apply find_some in Heqo0. propositional; simplify.
      eapply in_map with (f := fst)  in Heqo1. simpl in Heqo1. rewrite<-H in *.
      apply in_map_iff in Heqo1. propositional.
       eapply find_none with (x := x) in Heqo; auto. destruct x. simpl in *. simplify. contradiction.
  Qed.
End SortedEnv.

Module OrderedN <: OrderedT.
  Definition T : Type := N.
  Definition EqDec_T: EqDec T := _.
  Definition ltb: T -> T -> bool := N.ltb.
  Definition strict_order_T : strict_order ltb := N_strict_order.
End OrderedN.

Module SortedNEnv <: Env_T.
  Include (SortedEnv OrderedN).

  Section WithValueT.
    Context {T: Type}.
    Notation Env_t := (@EnvT T).

    Definition shift_up' (env: env_t T) (n: N) : env_t T :=
      List.map (fun '(k,v) => ((k + n)%N, v)) env.

    Lemma shift_up'_sorted:
      forall env n,
        sorted (List.map fst env) = true ->
        sorted (List.map fst (shift_up' env n)) = true.
    Proof.
      induction env; auto.
      simpl. intros; destruct env; simpl in *; try discriminate; auto.
      rewrite andb_true_iff in H. simplify. propositional. simpl in *.
      rewrite andb_true_iff. rewrite N.ltb_lt in *. split; try lia.
      eauto.
    Qed.

    Definition shift_up (env: EnvT T) (n: N): EnvT T :=
      {| Env := shift_up' (to_list env) n;
         pf_sorted := shift_up'_sorted _ _ env.(pf_sorted)
      |}.

    Lemma shift_up_equiv:
      forall env x n,
      opt_get (shift_up env n) (x + n)%N = opt_get env x.
    Proof.
      unfold opt_get, shift_up; simpl.
      destruct env. unfold to_list. simpl.
      clear. induction Env0; auto.
      simpl. intros; destruct_match_pairs; simplify.
      destruct_match.
      - simplify. destruct_match; simplify.  lia.
      - rewrite IHEnv0. destruct_with_eqn (beq_dec x t0).
        + simplify. lia.
        + setoid_rewrite Heqb0. reflexivity.
    Qed.

    Lemma to_list_ext:
      forall (env1 env2: EnvT T) x,
      to_list env1 = to_list env2 ->
      opt_get env1 x = opt_get env2 x.
    Proof.
      unfold opt_get. unfold to_list. intros. rewrite H. reflexivity.
    Qed.

    Lemma sorted_env_shift_equiv':
      forall (env1 env2: EnvT T) n,
      to_list env1 = to_list (shift_up env2 n) ->
      forall x, opt_get env1 ((x + n)%N) = opt_get env2 x.
    Proof.
      unfold to_list. destruct env1. destruct env2. simpl in *.
      unfold opt_get. intros; subst; simpl. clear.
      induction Env1; auto.
      simpl. destruct_match_pairs; simplify. destruct_match; simplify.
      - repeat destruct_match; simplify; lia.
      - repeat destruct_match; simplify; auto.
    Qed.

    Definition shift_down' (env: env_t T) (n: N) : (env_t T) :=
      List.map (fun '(k,v) => ((k - n)%N, v)) (filter (fun '(k,v) => N.leb n k) env).

    Definition restrict' (env: env_t T) (n: N) (n_max: N) : (env_t T) :=
      List.map (fun '(k,v) => ((k - n)%N, v)) (filter (fun '(k,v) => N.leb n k && N.ltb k n_max) env).

    Definition keys_ge (env: env_t T) (n: N) : Prop :=
        List.forallb (fun k => N.leb n k) (List.map fst env) = true.

    Lemma restrict'_sorted:
      forall env n max,
        sorted (List.map fst env) = true ->
        sorted (List.map fst (restrict' env n max)) = true.
    Proof.
      induction env; auto.
      simpl; intros; unfold restrict'; simpl; simplify; destruct_match; simpl.
      - destruct env; simpl in *; auto.
        rewrite andb_true_iff in H; propositional.
        specialize IHenv with (1 := H1).
        specialize IHenv with (n := n) (max := max).
        unfold restrict' in IHenv.  simpl in IHenv. rewrite IHenv.
        destruct_match_pairs. simpl in H0. rewrite N.ltb_lt in *.
        rewrite andb_true_iff in *.
        rewrite N.leb_le in *. propositional.
        destruct_match; simpl.
        + rewrite andb_true_r. rewrite N.ltb_lt. lia.
        + rewrite andb_false_iff in Heqb.
          rewrite N.leb_nle in *.
          rewrite N.ltb_nlt in *. destruct Heqb.
          * lia.
          * destruct_match; auto. exfalso. simpl in *.
            assert (filter (fun '(k, _) => (n <=? k)%N && (k <? max)%N) env = []).
            { clear - H1 H. generalize dependent env. induction env; auto.
              intros sorted. simpl in *. rewrite andb_true_iff in *. propositional.
              rewrite N.ltb_lt in *.
              destruct_match_pairs; subst; simpl in *. rewrite IHenv.
              { destruct_match; auto. rewrite andb_true_iff in Heqb.
                rewrite N.leb_le in Heqb. rewrite N.ltb_lt in Heqb. lia.
              }
              { destruct_match; auto. rewrite andb_true_iff in *. rewrite N.ltb_lt in *. propositional. split; auto. lia.
              }
            }
            rewrite H2 in *. discriminate.

      - apply IHenv. destruct env; simpl in H; auto. simpl. rewrite andb_true_iff in H. propositional.
    Qed.

    Lemma shift_down'_sorted:
      forall env n,
        sorted (List.map fst env) = true ->
        sorted (List.map fst (shift_down' env n)) = true.
    Proof.
      induction env; auto.
      simpl. intros.  unfold shift_down'. simpl. simplify. destruct_match.
      - rewrite N.leb_le in *.
        simpl. destruct env; simpl in *; auto. simplify.
        simpl in *. rewrite andb_true_iff in *. propositional. rewrite N.ltb_lt in *.
        specialize IHenv with (1 := H1).
        destruct_with_eqn (n <=? t1)%N.
        + simpl. rewrite andb_true_iff; split; auto.
          * rewrite N.ltb_lt. lia.
          * specialize IHenv with (n := n).
            unfold shift_down' in *. simpl in *. simpl_match. simpl in *.
            auto.
        + rewrite N.leb_nle in *. lia.
      - apply IHenv. destruct env; simpl in *; auto. rewrite andb_true_iff in H. propositional.
    Qed.

    Definition shift_down (env: EnvT T) (n: N) : EnvT T :=
      {| Env :=  shift_down' env.(Env) n;
         pf_sorted := shift_down'_sorted _ _ env.(pf_sorted)
      |}.

    Definition restrict (env: EnvT T) (n: N) (max: N): EnvT T :=
      {| Env :=  restrict' env.(Env) n max;
         pf_sorted := restrict'_sorted _ _ _ env.(pf_sorted)
      |}.

    Lemma shift_down_equiv:
      forall env x n ,
      opt_get (shift_down env n ) x = opt_get env (x + n)%N.
    Proof.
      unfold opt_get, shift_down; simpl. unfold keys_ge.
      destruct env. unfold to_list. simpl. revert pf_sorted0.
      induction Env0; auto.
      simpl. destruct Env0.
      - simpl in *. propositional. unfold shift_down'. simpl. simplify.
        destruct_with_eqn (n <=? t)%N; simpl; auto.
        + rewrite N.leb_le in *. repeat destruct_match; simplify; try lia; auto.
        + destruct (beq_dec (x+n)%N t) eqn:Hfoo; try setoid_rewrite Hfoo; rewrite N.leb_nle in *; simplify; try lia; auto.
      - simpl. rewrite andb_true_iff. intros; simplify; propositional.
        unfold shift_down'. simpl in *. rewrite N.ltb_lt in *.
        specialize IHEnv0 with (x := x) ( n := n).
        destruct_with_eqn (n <=? t)%N.
        + rewrite N.leb_le in *. simpl. destruct_with_eqn (beq_dec x (t-n)%N); simplify.
          * destruct_with_eqn (beq_dec (t - n + n)%N t); try setoid_rewrite Heqb0; simplify; try lia.
          * destruct_with_eqn (beq_dec (x + n)%N t); try setoid_rewrite Heqb1; auto.
            setoid_rewrite IHEnv0. destruct_match; simplify; try lia.
        + setoid_rewrite IHEnv0. rewrite N.leb_nle in Heqb.
          destruct_with_eqn (beq_dec (x + n)%N t); setoid_rewrite Heqb0; simplify; auto.
          lia.
    Qed.

    Lemma restrict_equiv:
      forall env x n max,
      (x + n < max)%N ->
      opt_get (restrict env n max) x = opt_get env (x + n)%N.
    Proof.
      unfold opt_get, shift_down; simpl. unfold keys_ge.
      destruct env. unfold to_list. simpl. revert pf_sorted0.
      induction Env0; auto.
      simpl. destruct Env0.
      - simpl in *. propositional. rename H into lt. unfold restrict'. simpl. simplify.
        destruct_with_eqn ((n <=? t) && (t <? max))%N; simpl; auto.
        + rewrite andb_true_iff in *. rewrite N.leb_le in *. rewrite N.ltb_lt in *.
          repeat destruct_match; simplify; try lia; auto.
        + destruct_match; simplify; auto.
          rewrite andb_false_iff in Heqb. rewrite N.leb_nle in *. rewrite N.ltb_nlt in *.
          lia.
      - simpl. rewrite andb_true_iff. intros; simplify; propositional.
        unfold restrict'. simpl in *. rewrite N.ltb_lt in *.
        specialize IHEnv0 with (x := x) ( n := n) (max := max).
        destruct_with_eqn ((n <=? t) && (t <? max))%N.
        +  rewrite andb_true_iff in *. rewrite N.leb_le in *. rewrite N.ltb_lt in *.
           simpl. destruct_with_eqn (beq_dec x (t-n)%N); simplify.
          * rewrite beq_dec_refl.
            destruct_with_eqn (beq_dec (t - n + n)%N t); try setoid_rewrite Heqb0; simplify; try lia.
          * rewrite<-beq_dec_false_iff in Heqb0. rewrite Heqb0.
            destruct_with_eqn (beq_dec (x + n)%N t); try setoid_rewrite Heqb1; auto.
            setoid_rewrite IHEnv0. destruct_match; simplify; try lia.
            simplify. lia.
        + setoid_rewrite IHEnv0; [ | lia].
          rewrite andb_false_iff in Heqb. rewrite N.leb_nle in *. rewrite N.ltb_nlt in *.
          propositional. destruct_match; simplify; try lia.
          * destruct_match; simplify; lia.
          * destruct_with_eqn (beq_dec (x + n)%N t); simplify; [ lia | ].
            rewrite<-beq_dec_false_iff in Heqb1. rewrite Heqb1. reflexivity.
    Qed.

    Lemma in_restrict:
      forall key v n len env,
        In (key, v) (Env (restrict env n (n + len))) ->
        (key < len)%N.
    Proof.
      intros. consider @restrict. simpl in H.
      unfold restrict' in *.
      rewrite in_map_iff in H. propositional; destruct_match_pairs; simplify.
      rewrite filter_In in H2. propositional. rewrite andb_true_iff in H1.
      rewrite N.leb_le in H1. rewrite N.ltb_lt in H1.
      lia.
    Qed.


  End WithValueT.

End SortedNEnv.
Module SortedRegEnv := SortedNEnv.

Section LogEntry.

  Record LogEntry :=
    LE { lread0: bool;
         lread1: bool;
         lwrite0: option (vect_t);
         lwrite1: option (vect_t) }.
  Definition LE_empty :=
    {| lread0 := false;
       lread1 := false;
       lwrite0 := None;
       lwrite1 := None |}.

  Definition LE_may_read0 (le: LogEntry) : bool :=
    match le.(lwrite0), le.(lwrite1) with
    | None, None => true
    | _, _ => false
    end.

  Definition LE_may_read1 (le: LogEntry) : bool :=
    match le.(lwrite1) with
    | None => true
    | _ => false
    end.

  Definition LE_may_write0 (le: LogEntry) : bool :=
    match le.(lread1), le.(lwrite0), le.(lwrite1) with
    | false, None, None => true
    | _, _, _ => false
    end.

  Definition LE_may_write1 (le: LogEntry) : bool :=
    match le.(lwrite1) with
    | None => true
    | _ => false
    end.

  Definition LE_set_read0 (le: LogEntry) : LogEntry :=
    {| lread0 := true;
       lread1 := le.(lread1);
       lwrite0 := le.(lwrite0);
       lwrite1 := le.(lwrite1) |}.

  Definition LE_set_read1 (le: LogEntry) : LogEntry :=
    {| lread0 := le.(lread0);
       lread1 := true;
       lwrite0 := le.(lwrite0);
       lwrite1 := le.(lwrite1) |}.

  Definition LE_set_write0 (le: LogEntry) (v: vect_t): LogEntry :=
    {| lread0 := le.(lread0);
       lread1 := le.(lread1);
       lwrite0 := Some v;
       lwrite1 := le.(lwrite1) |}.

  Definition LE_set_write1 (le: LogEntry) (v: vect_t) : LogEntry :=
    {| lread0 := le.(lread0);
       lread1 := le.(lread1);
       lwrite0 := le.(lwrite0);
       lwrite1 := Some v |}.

  Definition opt_or {A} (o1 o2: option A) :=
    match o1 with
    | Some _ => o1
    | None => o2
    end.

  Lemma opt_or_None_r:
    forall {T} (v: option T), opt_or v None = v.
  Proof.
    destruct v; auto.
  Qed.

  Definition logentry_app (l1 l2: LogEntry) :=
    {| lread0 := l1.(lread0) || l2.(lread0);
       lread1 := l1.(lread1) || l2.(lread1);
       lwrite0 := opt_or l1.(lwrite0) l2.(lwrite0);
       lwrite1 := opt_or l1.(lwrite1) l2.(lwrite1) |}.

  Lemma logentry_app_empty_l:
    forall le, logentry_app LE_empty le = le.
  Proof.
    intros; unfold logentry_app.
    simpl. destruct le; reflexivity.
  Qed.

  Lemma logentry_app_empty_r:
    forall le, logentry_app le LE_empty = le.
  Proof.
    intros; unfold logentry_app.
    simpl. repeat rewrite orb_false_r. repeat rewrite opt_or_None_r.
    destruct le; reflexivity.
  Qed.

End LogEntry.

Module Type Log_T.
  Parameter T : Type.

  Notation reg_t := N.
  Parameter log_empty : T.
  Parameter log_set: T -> reg_t -> LogEntry -> T.
  Parameter log_get: T -> reg_t -> LogEntry.

  Parameter log_app: T -> T -> T.

  Parameter log_get_empty: forall reg, log_get log_empty reg = LE_empty.

  Parameter log_set_eq: forall log reg le,
      log_get (log_set log reg le) reg = le.

  Parameter log_set_neq: forall log idx idx' le,
      idx <> idx' ->
      log_get (log_set log idx' le) idx = log_get log idx.

  Parameter log_app_empty_l: forall log, log_app log_empty log = log.
  Parameter log_app_empty_r: forall log, log_app log log_empty = log.

  Parameter get_log_app:
    forall l1 l2 reg,
    log_get (log_app l1 l2) reg = logentry_app (log_get l1 reg) (log_get l2 reg).

  (* Parameter log_ext: *)
  (*   forall l1 l2, *)
  (*   (forall reg, log_get l1 reg = log_get l2 reg) -> *)
  (*   l1 = l2. *)

End Log_T.

Module SortedLog <: Log_T.
  Definition T := SortedRegEnv.EnvT LogEntry.
  Definition log_empty : T := SortedRegEnv.empty.
  Definition log_set (log: T) (r: reg_t) (le: LogEntry) : T :=
    SortedRegEnv.update log r (fun _ => le) LE_empty.

  Definition log_get (log: T) (idx: reg_t) : LogEntry :=
    match SortedRegEnv.opt_get log idx with
    | Some le => le
    | None => LE_empty
    end.

  Definition log_app (log1 log2: T) : T :=
    let zipped := SortedRegEnv.zip_default log1 log2 LE_empty LE_empty in
    SortedRegEnv.mapV (fun '(le1,le2) => logentry_app le1 le2) zipped.

  Lemma log_get_empty: forall reg, log_get log_empty reg = LE_empty.
  Proof.
    intros. unfold log_get.
    unfold log_empty. rewrite SortedRegEnv.opt_get_empty.
    reflexivity.
  Qed.

  Lemma log_set_eq: forall log reg le,
      log_get (log_set log reg le) reg = le.
  Proof.
    intros; unfold log_get, log_set.
    rewrite SortedRegEnv.update_correct_eq.
    destruct_match; destruct_match_pairs; auto.
  Qed.

  Lemma log_set_neq: forall log idx idx' le,
      idx <> idx' ->
      log_get (log_set log idx' le) idx = log_get log idx.
  Proof.
    intros; unfold log_get, log_set.
    rewrite SortedRegEnv.update_correct_neq; auto.
  Qed.

  Lemma log_app_empty_l: forall log, log_app log_empty log = log.
  Proof.
    intros. unfold log_app.
    apply SortedRegEnv.env_ext.
    intros. rewrite SortedRegEnv.opt_get_mapV.
    rewrite SortedRegEnv.opt_get_zip_default; unfold log_empty.
    rewrite SortedRegEnv.opt_get_empty.
    destruct_match; auto.
    rewrite logentry_app_empty_l.
    reflexivity.
  Qed.

  Lemma log_app_empty_r: forall log, log_app log log_empty = log.
    intros. unfold log_app.
    apply SortedRegEnv.env_ext.
    intros. rewrite SortedRegEnv.opt_get_mapV.
    rewrite SortedRegEnv.opt_get_zip_default; unfold log_empty.
    rewrite SortedRegEnv.opt_get_empty.
    destruct_match; auto.
    rewrite logentry_app_empty_r.
    reflexivity.
  Qed.

  Lemma get_log_app:
    forall l1 l2 reg,
    log_get (log_app l1 l2) reg = logentry_app (log_get l1 reg) (log_get l2 reg).
  Proof.
    unfold log_get, log_app.
    intros. rewrite SortedRegEnv.opt_get_mapV.
    rewrite SortedRegEnv.opt_get_zip_default.
    repeat destruct_match; auto.
  Qed.

  (* Lemma log_ext: *)
  (*   forall l1 l2, *)
  (*   (forall reg, log_get l1 reg = log_get l2 reg) -> *)
  (*   l1 = l2. *)
  (* Proof. *)
  (*   intros * Heq. *)
  (*   consider log_get. *)
  (*   consider log_get. *)
  (*   apply SortedRegEnv.env_ext. *)
  (*   intros reg. specialize Heq with (reg := reg). *)
  (*   repeat destruct_matches_in_hyp Heq; subst; auto. *)

  (*   bash_destruct Heq. *)
  (*   - *)


End SortedLog.

Definition log_t := SortedLog.T.
Include SortedLog.

(* TODO: MOVE *)
Module SortedExtFnEnv := SortedNEnv.
Definition ext_log_t : Type := SortedExtFnEnv.EnvT (option vect_t).

Definition ext_log_can_call (log: ext_log_t) (fn: ext_fn_t) : bool :=
  match SortedExtFnEnv.opt_get log fn with
  | Some (Some _) => false
  | _ => true
  end.

Definition ext_log_update (log: ext_log_t) (fn: ext_fn_t) (value: vect_t): ext_log_t :=
  SortedExtFnEnv.update log fn (fun _ => Some value) None.


Create HintDb log_simpl.
Hint Rewrite log_app_empty_l : log_simpl.
Hint Rewrite log_app_empty_r : log_simpl.

Definition state_t := SortedRegEnv.EnvT (vect_t).

Definition varenv_t {A} : Type := list (var_t * A).
Definition gamma_t : Type := @varenv_t vect_t.
Definition var_types_t := @varenv_t nat.

Section WithIdTy.
  Context {id_ty : Type}.
  Context {EqDec_id_ty : EqDec id_ty}.
  Notation reg_t := (@reg_t id_ty).
  Notation ext_fn_t := (@ext_fn_t id_ty).
  Notation struct_t := (@struct_t id_ty).
  Notation action := (@action id_ty).

  Definition reg_types_t := list (reg_t * nat).
  Definition ext_fn_types_t := list (ext_fn_t * (nat * nat)).

  Definition struct_env_t := list (struct_t).


  Notation fn_name_t := (@fn_name_t id_ty).
  Record int_fn_spec_t {action_t: Type}:=
  { fn_name : fn_name_t ;
    fn_reg_tys : reg_types_t;
    fn_ext_fn_tys: ext_fn_types_t;
    fn_struct_defs: struct_env_t;
    fn_arg_ty: nat;
    fn_arg_name: var_t;
    fn_ret_ty: nat;
    fn_body: action_t
  }.

  Definition mk_int_fn_spec reg_types ext_fn_tys struct_defs (name: fn_name_t) (arg_ty: nat) (ret_ty: nat) (body: action) :=
    {| fn_name := name;
       fn_reg_tys := reg_types;
       fn_ext_fn_tys := ext_fn_tys;
       fn_struct_defs := struct_defs;
       fn_arg_ty := arg_ty;
       fn_arg_name := "_ARG_";
       fn_ret_ty := ret_ty;
       fn_body := body
    |}.

  Definition int_fn_env_t {action_t: Type} := list (@int_fn_spec_t action_t).
  Definition empty_var_t : var_types_t := [].
  Definition empty_ext_fn_t : ext_fn_types_t := [].
  Definition empty_int_fn_env {action_t: Type}: @int_fn_env_t  action_t := [].
  Definition empty_struct_env_t : struct_env_t := [].

  Definition lookup_struct {A} (env: struct_env_t) (name: dstruct_name_t) (msg: A) : result struct_t A :=
    match find (fun s => beq_dec name s.(dstruct_name)) env with
    | Some s => Success s
    | None => Failure msg
    end.

  Definition lookup_int_fn {A action_t} (int_fns: @int_fn_env_t action_t) (int_fn: fn_name_t) (msg: A)
                                : result (nat * int_fn_spec_t) A :=
    match find_with_index (fun f => beq_dec int_fn f.(fn_name)) int_fns with
    | Some t => Success t
    | None => Failure msg
    end.

  Definition lookup_reg_type (tys: list (reg_t * nat)) : reg_t -> option nat :=
    fun r =>
    match find (fun '(r',t) => beq_dec r r') tys with
    | Some (_, t) => Some t
    | _ => None
    end.

  Definition lookup_ext_fn (ext_fns: list (ext_fn_t * (nat * nat))) : ext_fn_t -> option (nat * nat) :=
    fun ext_fn =>
    match find (fun '(f,_) => beq_dec ext_fn f) ext_fns with
    | Some (_, t) => Some t
    | None => None
    end.

End WithIdTy.




Definition fn_var_types (fn_arg_name: var_t) (fn_arg_ty: nat) : var_types_t :=
  [(fn_arg_name, fn_arg_ty)].

Definition fn_gamma (fn_arg_name: var_t) (fn_arg: vect_t) : gamma_t :=
  [(fn_arg_name, fn_arg)].

Lemma lookup_int_fn_Success:
  forall {action_t: Type} (int_fn_env: @int_fn_env_t N action_t) fn {A} (msg: A) spec i,
  lookup_int_fn int_fn_env fn msg = Success (i, spec) ->
  nth_error int_fn_env i = Some spec /\ spec.(fn_name) = fn.
Proof.
  intros. consider @lookup_int_fn. simplify_result.
  apply find_with_index_Some in Heqo.
  propositional. split; auto. simplify. reflexivity.
Qed.


Definition lookup_var_from_list {A} (vars: list (var_t * A)) (var: var_t) : option A :=
  match find (fun '(v, _) => String.eqb var v) vars with
  | Some (_, a) => Some a
  | None => None
  end.


Section Utils.
  Definition GenericGammaEmpty : gamma_t := [].

  Definition varenv_lookup_var {A B} (varenv: @varenv_t B) (var: var_t) (msg: A) : result B A :=
    match find (fun '(v, _) => String.eqb var v) varenv with
    | Some (_, a) => Success a
    | None => Failure msg
    end.


  Definition varenv_bind {A} (varenv: @varenv_t A) (var: var_t) (v: A) : varenv_t :=
    (var,v)::varenv.

  Definition varenv_update {A} (varenv: @varenv_t A) (var: var_t) (v: A) : varenv_t :=
    find_and_replace varenv var String.eqb (fun _ => v) v.

  Definition get_reg (r: state_t) (idx: reg_t) : option vect_t :=
    SortedRegEnv.opt_get r idx.

  Definition r_get_reg (r: state_t) (idx: reg_t) : result (vect_t) unit :=
    match SortedRegEnv.opt_get r idx with
    | Some v => Success v
    | None => Failure (__debug__ ("r_get_reg: not found", r,idx) tt)
    end.

  Definition unsafe_get_reg (st: state_t) (reg: reg_t) : list bool :=
    success_or_default (r_get_reg st reg) [].

  Definition blacklist_unsafe_get_reg := unsafe_get_reg.

  Definition latest_write (le: LogEntry) : option (vect_t) :=
    match le.(lwrite1), le.(lwrite0) with
    | Some w, _ => Some w
    | _, Some w => Some w
    | _, _ => None
    end.

  Definition state_set (st: state_t) (r: reg_t) (v: vect_t): state_t :=
    SortedRegEnv.update st r (fun _ => v) v.

  Definition commit_update (st: state_t) (log: log_t) : state_t :=
    SortedRegEnv.map (fun reg v => match latest_write (log_get log reg) with
                                    | Some w => w
                                    | None => v
                                    end) st.

  Section Lemmas.
    Lemma varenv_bind_var_eq :
      forall {A} varenv var (v: A) {T} (msg: T),
        varenv_lookup_var (varenv_bind varenv var v) var msg = Success v.
    Proof.
      intros. unfold varenv_lookup_var, varenv_bind.
      simpl. rewrite String.eqb_refl. reflexivity.
    Qed.

    Lemma varenv_update_var_eq :
      forall {A} varenv var (v: A) {T} (msg: T),
        varenv_lookup_var (varenv_update varenv var v) var msg = Success v.
    Proof.
      intros. unfold varenv_lookup_var, varenv_update.
      induction varenv; simpl; auto.
      - rewrite String.eqb_refl. reflexivity.
      - destruct_match; subst. destruct_match; simpl.
        + rewrite Heqb. reflexivity.
        + rewrite Heqb. auto.
    Qed.

    Lemma varenv_bind_var_neq :
      forall {A} varenv var var' (v: A) {T} (msg: T),
        var' <> var ->
        varenv_lookup_var (varenv_bind varenv var' v) var msg = varenv_lookup_var varenv var msg.
    Proof.
      intros. unfold varenv_bind, varenv_lookup_var. simpl.
      destruct_match.
      - apply String.eqb_eq in Heqb. subst. congruence.
      - reflexivity.
    Qed.

    Lemma varenv_update_var_neq :
      forall {A} varenv var var' (v: A) {T} (msg: T),
        var <> var' ->
        varenv_lookup_var (varenv_update varenv var' v) var msg = varenv_lookup_var varenv var msg.
    Proof.
      intros. unfold varenv_lookup_var, varenv_update. simpl.
      induction varenv; simpl.
      - apply String.eqb_neq in H. rewrite H. reflexivity.
      - destruct_match; subst; auto. destruct_match; simpl; auto.
        + apply String.eqb_eq in Heqb. subst. destruct_match; auto.
          apply String.eqb_eq in Heqb. subst. congruence.
        + destruct_match; auto.
    Qed.

    Lemma is_success_commit_update:
      forall st idx log v,
        r_get_reg st idx = Success v ->
        is_success (r_get_reg (commit_update st log) idx) = true.
    Proof.
      intros. consider r_get_reg. consider commit_update.
      rewrite SortedRegEnv.opt_get_map.
      simplify. destruct_match; auto.
    Qed.

    Lemma get_set_reg:
      forall st reg v,
        get_reg (state_set st reg v) reg = Some v.
    Proof.
      unfold state_set, get_reg. intros.
      rewrite SortedRegEnv.update_correct_eq. destruct_match; auto.
    Qed.

    Lemma get_set_reg_neq:
      forall st reg idx v,
        reg <> idx ->
        get_reg (state_set st idx v) reg = get_reg st reg.
    Proof.
      unfold state_set, get_reg. intros.
      rewrite SortedRegEnv.update_correct_neq by auto. reflexivity.
    Qed.


    Lemma unsafe_get_reg_ext:
      forall st0 st1 reg0 reg1,
        get_reg st0 reg0 = get_reg st1 reg1 ->
        unsafe_get_reg st0 reg0 = unsafe_get_reg st1 reg1.
    Proof.
      intros.
      consider get_reg. consider unsafe_get_reg. consider r_get_reg.
      rewrite H. reflexivity.
    Qed.
    Lemma unsafe_get_reg_safe:
      forall st reg v,
        get_reg st reg = Some v ->
        unsafe_get_reg st reg = v.
    Proof.
      intros. unfold unsafe_get_reg, r_get_reg.
      unfold get_reg in *. simpl_match. auto.
    Qed.
    Definition is_some' {T} (v: option T) : Prop :=
      match v with
      | Some _ => True
      | None => False
      end.


    Lemma getenv_commit:
      forall impl_st ' log reg v,
        is_some' (get_reg impl_st reg) ->
        latest_write (log_get log reg) = Some v ->
        get_reg (commit_update impl_st log) reg = Some v.
    Proof.
      intros. consider commit_update. unfold get_reg, is_some' in *.
      rewrite SortedRegEnv.opt_get_map. simplify.
      simpl_match. auto.
    Qed.

    Lemma getenv_commit_None:
      forall impl_st log reg,
        latest_write (log_get log reg) = None ->
        get_reg (commit_update impl_st log) reg = get_reg impl_st reg.
    Proof.
      unfold is_some', commit_update, get_reg. intros.
      rewrite SortedRegEnv.opt_get_map.
      unfold log_get in *.
      destruct_match; auto.
      destruct_match; simpl_match; auto.
    Qed.

    Lemma getenv_commit':
      forall impl_st log reg v,
        is_some' (get_reg impl_st reg) ->
        latest_write (log_get log reg) = Some v ->
        unsafe_get_reg (commit_update impl_st log) reg = v.
    Proof.
      intros. unfold unsafe_get_reg, r_get_reg. erewrite getenv_commit; eauto.
      reflexivity.
    Qed.

    Lemma getenv_commit'_None:
      forall impl_st log reg ,
        latest_write (log_get log reg) = None ->
        unsafe_get_reg (commit_update impl_st log) reg = unsafe_get_reg impl_st reg.
    Proof.
      intros. consider unsafe_get_reg.
      unfold commit_update, r_get_reg.
      rewrite SortedRegEnv.opt_get_map.
      unfold log_get in *.
      destruct_matches_in_hyp H.
      - destruct_match; auto; simpl_match; auto.
      - destruct_match; auto.
    Qed.

    Lemma unsafe_get_reg_state_set_eq:
      forall st idx v, unsafe_get_reg (state_set st idx v) idx = v.
    Proof.
      unfold state_set, unsafe_get_reg, r_get_reg. intros. rewrite SortedRegEnv.update_correct_eq. simpl.
      destruct_match; auto.
    Qed.

    Lemma unsafe_get_reg_state_set_neq:
      forall st idx1 idx2 v,
        idx1 <> idx2 ->
        unsafe_get_reg (state_set st idx1 v) idx2 = unsafe_get_reg st idx2.
    Proof.
      unfold state_set, unsafe_get_reg, r_get_reg. intros. rewrite SortedRegEnv.update_correct_neq by auto.
      unfold __debug__. reflexivity.
    Qed.

  End Lemmas.
End Utils.

Notation "st .[ idx ]" := (unsafe_get_reg st idx) (at level 1, format "st .[ idx ]").
Notation fid := fn_name.
Notation sid := dstruct_name.

Ltac solve_is_sorted :=
  cbv - [N.add N.ltb];
  repeat match goal with
  | |- (if N.ltb _ _ then _ else _) = true =>
      let H := fresh in
      destruct_match_as H; [ | apply N.ltb_nlt in H; lia]
  end; reflexivity.
Ltac solve_is_sorted' :=
  repeat (match goal with
  | |- _ => progress (simpl; repeat rewrite<-N.add_assoc; try lia)
  | |- (?x < ?y)%N =>
      unfold x
  | |- (?x < ?y)%N =>
      unfold y
  | |- (?x _ < ?y)%N =>
      unfold x
  | |- (?x _ < ?y _)%N =>
      unfold y
  | |- (?x < ?y + 0)%N =>
      unfold y
  | |- (?x + _ < ?y )%N =>
      unfold x
  end).


    Lemma sorted_app:
      forall (xs ys: list N),
      sorted (ltb := N.ltb) (xs) = true ->
      sorted (ltb := N.ltb) (ys) = true ->
      match xs, ys with
      | [], _ => True
      | _, [] => True
      | x::xs, y::ys =>
          ((List.last (x::xs) 0%N) < y )%N
      end ->
      sorted (ltb := N.ltb) (xs ++ ys) = true.
    Proof.
      destruct xs; auto. destruct ys; auto.
      - rewrite List.app_nil_r. auto.
      - revert n0. revert n. revert ys. induction xs; simpl.
        + intros. rewrite andb_true_iff. split; auto. apply N.ltb_lt. assumption.
        + intros; simplify. rewrite andb_true_iff in *.
          propositional. split; auto.
          simpl in *. eauto.
    Qed.

Definition sorted := @sorted _ N.ltb.
  Definition koika_state_t : Type := Environments.state_t.
