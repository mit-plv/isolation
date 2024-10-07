Require Import Koika.Common.
Require Import Koika.Tactics.

Section Lists.

  Lemma find_with_index'_Some:
    forall {A} f (la: list A) i a start,
      find_with_index' f la start = Some (i, a) ->
      nth_error la (i - start) = Some a /\ (f a = true) /\ i >= start.
  Proof.
    induction la; intros; simpl in *; auto.
    - discriminate.
    - destruct_with_eqn (f a); inversion H; subst.
      + replace (i - i) with 0 by lia. auto.
      + specialize IHla with (1 := H). destruct IHla as (? & ? & ?).
        destruct i; [ lia | ].
        simpl. destruct start; simpl.
        * replace (S i - 1) with i in * by lia.
          repeat split; auto; lia.
        * replace (S i - S (S start)) with (i - S start) in * by lia.
          destruct_with_eqn (i - start); simpl; try lia.
          replace (i - S start) with n in * by lia.
          repeat split; auto. lia.
  Qed.


  Lemma find_with_index_Some:
    forall {A} f (la: list A) i a,
      find_with_index f la = Some (i, a) ->
      nth_error la i = Some a /\ (f a = true).
  Proof.
    intros. unfold find_with_index in *. apply find_with_index'_Some in H.
    replace (i - 0) with i in * by lia. destruct H as (? & ? & ?); auto.
  Qed.

  Lemma find_with_index_Some_eq:
    forall {A} f (l: list A) a,
      find f l = Some a ->
      exists i, find_with_index f l = Some (i, a).
  Proof.
    unfold find_with_index. generalize 0. intros *. revert n. revert a. induction l.
    - simpl. propositional. discriminate.
    - simpl. intros. destruct_match; option_simpl; subst; eauto.
  Qed.

  Lemma find_with_index'_acc:
    forall {A} f (xs: list A) acc0 acc,
      match find_with_index' f xs acc0 with
      | Some (i, v) => find_with_index' f xs (acc + acc0) = Some (acc+ i, v)
      | None => find_with_index' f xs (acc + acc0) = None
      end.
  Proof.
    induction xs; simpl; unfold find_with_index; propositional.
    destruct_match; destruct_match_pairs; subst; simpl in *.
    - f_equal.
    - specialize (IHxs (S acc0) acc).
      replace (S (acc + acc0)) with (acc + S acc0) in * by lia. auto.
  Qed.

  Lemma map2_success:
    forall {A B C} (xs: list A) (ys: list B) (f: A -> B -> C),
      Datatypes.length xs = Datatypes.length ys ->
      is_success (map2 f xs ys) = true.
  Proof.
    induction xs; destruct ys; simpl in *; auto.
    - intros. discriminate.
    - intros. discriminate.
    - intros. inversion H; subst. apply IHxs with (f := f) in H1.
      destruct_with_eqn (map2 f xs ys); auto.
  Qed.


  Lemma map2_length:
    forall {A B C} (xs: list A) (ys: list B) zs (f: A -> B -> C),
      map2 f xs ys = Success zs ->
      Datatypes.length xs = Datatypes.length ys /\ Datatypes.length xs = Datatypes.length zs.
  Proof.
    induction xs; destruct ys; simpl in *; auto.
    - intros; simpl in *. inversion H; subst. auto.
    - intros. discriminate.
    - intros. discriminate.
    - intros. destruct (map2 _ _ _ ) eqn:?.
      + apply IHxs with (f := f) in Heqr. destruct Heqr.
        rewrite H0. inversion H. simpl. rewrite<-H1. rewrite H0. auto.
      + discriminate.
   Qed.

  Lemma result_list_map_feq:
    forall {A B F} (f f': A -> result B F) ls,
      (forall a, In a ls -> f a = f' a ) ->
      result_list_map f ls =
      result_list_map f' ls.
  Proof.
    induction ls; simpl; auto.
    intros. propositional. rewrite IHls. rewrite H; auto.
  Qed.

  Lemma result_list_map_app:
    forall {A B F} (f: A -> result B F) ls1 ls2,
      result_list_map f (ls1 ++ ls2) =
      match result_list_map f ls1, result_list_map f ls2 with
      | Success ls1', Success ls2' => Success (ls1' ++ ls2')%list
      | Failure f, _ => Failure f
      | _, Failure f => Failure f
      end.
  Proof.
    induction ls1; simpl; auto.
    - intros; destruct_match; auto.
    - intros. destruct_match; auto.
      rewrite IHls1.
      destruct_match; auto.
      destruct_match; auto.
  Qed.


  Lemma result_list_map_success_nth:
    forall {A B F} (f: A -> result B F) la (lb: list B) n x,
    result_list_map f la = Success lb ->
    nth_error la n = Some x ->
    exists v, nth_error lb n = Some v /\ f x = Success v.
  Proof.
    induction la; intros.
    - simpl in *. destruct lb; simplify_result. destruct n; simpl in *; option_simpl.
    - simpl in *. simplify_result. destruct n; simpl in *; option_simpl; subst; eauto.
  Qed.

  Lemma nth_error_mapi'_Some:
    forall {A B} (f: nat -> A -> B) (la: list A) n s v,
      nth_error (mapi' s f la) n = Some (v) ->
      nth_error la n <> None.
  Proof.
    induction la; propositional.
    - simpl in *. destruct n; simpl in *; try discriminate.
    - simpl in *. destruct n; simpl in *; option_simpl; subst.
      eapply IHla; eauto.
  Qed.

  Lemma nth_error_mapi':
    forall {A B} (f: nat -> A -> B) (la: list A) n s a,
      nth_error la n = Some a ->
      nth_error (mapi' s f la) n = Some (f (n+ s) a).
  Proof.
    induction la; propositional.
    - simpl in *. destruct n; simpl in *; option_simpl.
    - simpl. destruct n; simpl in *; option_simpl; subst; auto.
      erewrite IHla by eauto. f_equal. replace (S (n+s)) with (n + S s) by lia. auto.
  Qed.

  Lemma nth_error_mapi:
    forall {A B} (f: nat -> A -> B) (la: list A) n a,
      nth_error la n = Some a ->
      nth_error (mapi f la) n = Some (f n a).
  Proof.
    consider @mapi. intros. replace n with (n + 0) at 2 by lia. apply nth_error_mapi'; auto.
  Qed.

  Lemma mapi'_app:
    forall A B (f: nat -> A -> B) (ls1 ls2: list A) n,
    mapi' n f (ls1 ++ ls2)%list =
    List.app (mapi' n f ls1) (mapi' (n + List.length ls1) f ls2).
  Proof.
    induction ls1.
    - simpl. intros. rewrite <-plus_n_O. reflexivity.
    - intros. simpl. rewrite IHls1. rewrite PeanoNat.Nat.add_succ_comm. reflexivity.
  Qed.

  Lemma max_gt_min:
    forall (ls: list nat) base,
      fold_left Nat.max ls base >= base.
  Proof.
    induction ls; propositional.
    simpl. specialize IHls with (base := Nat.max base a). lia.
  Qed.

  Lemma max_base_order:
    forall (ls: list nat) base1 base2,
      base1 >= base2 ->
      fold_left Nat.max ls base1 >= fold_left Nat.max ls base2.
  Proof.
    induction ls; propositional.
    simpl. apply IHls. lia.
  Qed.

  Lemma max_map_correct':
    forall {A} (f: A -> nat) ls idx a base,
      nth_error ls idx = Some a ->
      fold_left Nat.max (map f ls) base >= Nat.max base (f a).
  Proof.
    induction ls; propositional; simpl in *.
    - destruct idx; simpl in H; discriminate.
    - destruct idx; simpl in *; auto.
      + option_simpl; subst. apply max_gt_min.
      + specialize IHls with (1 := H) (base := Nat.max base (f a)). lia.
  Qed.

  Lemma list_beq_length:
    forall T f l1 l2,
      list_beq T f l1 l2 = true ->
      Datatypes.length l1 = Datatypes.length l2.
  Proof.
    induction l1.
    - destruct l2; simpl; auto. propositional. discriminate.
    - destruct l2; simpl; propositional; try discriminate.
      apply f_equal. apply IHl1. apply andb_true_iff in H. propositional.
  Qed.

  Lemma bool_list_beq_iff:
    forall a b,
      list_beq bool Bool.eqb a b = true <-> a = b.
  Proof.
    induction a; propositional.
    - destruct b; simpl; split; propositional; simplify; discriminate.
    - destruct b; simpl; split; propositional; try discriminate.
      + apply andb_true_iff in H. propositional.
        f_equal.
        * apply eqb_true_iff. auto.
        * apply IHa. auto.
      + apply andb_true_iff. inversions H. split; auto.
        * apply eqb_reflx.
        * apply IHa. auto.
  Qed.

  Lemma bool_list_bneq_iff:
    forall a b,
      list_beq bool Bool.eqb a b = false <-> a <> b.
  Proof.
    induction a; propositional.
    - destruct b; simpl; split; propositional; simplify; discriminate.
    - destruct b; simpl; split; propositional; try discriminate.
      + apply andb_false_iff in H. propositional.
        unfold not. intros. inversions H0.
        destruct H; auto.
        * rewrite eqb_reflx in H. discriminate.
        * rewrite IHa in H. contradiction.
      + apply andb_false_iff. unfold not in *.
        destruct_with_eqn (Bool.eqb a b); auto.
        right. rewrite eqb_true_iff in Heqb1; subst.
        rewrite IHa. propositional.
  Qed.

  Lemma map_firstn:
    forall {A B} (f: A -> B) la n,
      map f (firstn n la ) = firstn n (map f la).
  Proof.
    induction la; propositional.
    - destruct n;simpl; auto.
    - simpl. destruct n; simpl; auto. rewrite IHla. auto.
  Qed.

  Lemma firstn_fill_eq:
    forall {A} (value: list A) width default ,
      width <= List.length value ->
      firstn_fill default width value = firstn width value.
  Proof.
    induction value; simpl; auto; intros.
    - destruct width; auto; lia.
    - destruct width; simpl; auto.
      erewrite IHvalue; auto. lia.
  Qed.

  Lemma skipn_skipn:
    forall {A} (arg: list A) len1 len2 ,
      len1 >= len2 ->
      skipn (len1 - len2) (skipn len2 arg) = skipn len1 arg.
  Proof.
    induction arg; propositional; simpl.
    - repeat rewrite skipn_nil. reflexivity.
    - destruct len1; simpl.
      + destruct len2; simpl; [| lia]. reflexivity.
      + destruct len2; simpl; auto.
        apply IHarg. lia.
  Qed.


  Lemma fold_left_add_ge_base:
    forall xs base,
      fold_left Nat.add xs base >= base.
  Proof.
    induction xs; simpl; try lia.
    intros. specialize IHxs with (base := base + a). lia.
  Qed.

  Lemma list_sum_add:
    forall xs base,
      fold_left Nat.add xs base = list_sum xs + base.
  Proof.
    induction xs; simpl; try lia.
    intros. unfold list_sum; simpl.
    pose proof (IHxs (base + a)).
    pose proof (IHxs a). lia.
  Qed.


  Lemma list_sum_firstn_le:
    forall n xs,
      list_sum (firstn n xs) <= list_sum xs.
  Proof.
    induction n; unfold list_sum.
    - simpl; intros; lia.
    - intros. simpl. destruct xs; simpl; try lia.
      consider list_sum. specialize IHn with (xs := xs).
      rewrite list_sum_add in *. rewrite list_sum_add in *.
      lia.
  Qed.
  Lemma list_sum_nth_error_ge:
    forall i struct_fields len,
      nth_error struct_fields i = Some len ->
      list_sum struct_fields >= list_sum (firstn i struct_fields) + len.
  Proof.
    induction i; unfold list_sum.
    - intros. simpl. destruct struct_fields; simpl in *; auto.
      + discriminate.
      + option_simpl; subst. simpl. apply fold_left_add_ge_base.
    - simpl. intros. destruct struct_fields; [discriminate | ]. simpl.
      specialize IHi with (1 := H).
      repeat rewrite list_sum_add. lia.
  Qed.

  (* Fixpoint is_increasing' (ls: list nat) (base: nat) : bool := *)
  (*   match ls with *)
  (*   | [] => true *)
  (*   | x::xs => *)
  (*     if Nat.ltb base x then *)
  (*       is_increasing' xs x *)
  (*     else false *)
  (*   end. *)

  (* Definition is_increasing (ls: list nat) : bool := *)
  (*   match ls with *)
  (*   | [] => true *)
  (*   | x::xs => is_increasing' xs x *)
  (*   end. *)

  Fixpoint sorted (m: list nat) : bool :=
    match m with
    | x::((y::zs) as m') => andb (Nat.ltb x y) (sorted m')
    | _ => true
    end.


  (* TODO: tail-recursive? *)
  Fixpoint find_and_replace {A B} (ls: list (A * B)) (key: A) (aeq: A -> A -> bool)
                              (f_subst: B -> B) (default: B)
                            : list (A * B) :=
    match ls with
    | [] => [(key,default)]
    | (a,b)::xs =>
      if aeq key a then
        (a, f_subst b)::xs
      else (a,b)::find_and_replace xs key aeq f_subst default
    end.

  Section Forall2.

   Ltac simplify_forall :=
     match goal with
     | H: Forall2 _ [] (_ :: _) |- _ => solve[inversion H]
     | H: Forall2 _ (_ :: _) [] |- _ => solve[inversion H]
     | H: Forall2 _ [] [] |- _ => solve[constructor]
     end.

   Lemma Forall2_setoid_refl :
     forall X (eq: X -> X -> Prop) xs,
     (forall x, eq x x) ->
     Forall2 eq xs xs.
   Proof.
     induction xs; auto.
   Qed.


   Lemma Forall2_eq : forall {A} (xs ys: list A),
       List.Forall2 (@eq A) xs ys ->
       xs = ys.
   Proof.
     induction xs; intros.
     - destruct ys; intuition; simplify_forall.
     - destruct ys; simpl in *; try simplify_forall.
       f_equal.
       + inversion H; auto.
       + apply IHxs; inversion H; auto.
   Qed.

   Lemma Forall2_impl : forall {X Y} {P: X -> Y -> Prop} {Q: X -> Y -> Prop}
                          {xs: list X} {ys: list Y},
       (forall x y, P x y -> Q x y) ->
       List.Forall2 P xs ys ->
       List.Forall2 Q xs ys.
   Proof.
     intros. induction H0; auto.
   Qed.

   Lemma Forall2_compose : forall {X Y Z} {P: X -> Y -> Prop} {Q: Y -> Z -> Prop} {R: X -> Z -> Prop}
                             {xs: list X} {ys: list Y} {zs: list Z},
       (forall x y z, P x y -> Q y z -> R x z) ->
       List.Forall2 P xs ys ->
       List.Forall2 Q ys zs ->
       List.Forall2 R xs zs.
   Proof.
     induction xs.
     - induction ys; induction zs; intuition; simplify_forall.
     - induction ys; intuition; try simplify_forall.
       generalize dependent zs.
       induction zs; intuition; try simplify_forall.
       inversion_clear H0; subst.
       inversion_clear H1; subst.
       constructor.
       + eapply H; eauto.
       + eapply IHxs; eauto.
   Qed.

    Lemma app_unit_eq :
      forall X (xs ys : list X) x y,
      xs ++ [x] = ys ++ [y] ->
      xs = ys /\ x = y.
    Proof.
      induction xs.
      - destruct ys.
        + intros. simpl in H. inversions H. auto.
        + intros. inversions H.
          destruct ys; simpl in H2; inversion H2.
      - induction ys.
        + simpl. intros. inversions H. destruct xs; inversions H2.
        + simpl; intros. inversions H. apply IHxs in H2. propositional.
    Qed.

    Lemma Forall2_inv_app_unit :
      forall A B (as1: list A) (bs1: list B) a b (P: A -> B -> Prop),
      Forall2 P (as1 ++ [a]) (bs1 ++ [b]) ->
      Forall2 P as1 bs1 /\ P a b.
    Proof.
      intros.
      apply Forall2_app_inv_l in H; propositional.
      destruct l2'.
      - inversion H1.
      - inversions H1. inversions H7.
        apply app_unit_eq in H3; propositional.
    Qed.

    Lemma app_unit_not_nil:
      forall A (xs: list A) y,
        [] = xs ++ [y] -> False.
    Proof.
      intros. destruct xs; simpl in *; discriminate.
    Qed.

    Theorem Forall2_rev_ind:
      forall (A B : Type) (R : A -> B -> Prop) (P : list A -> list B -> Prop),
        P [] [] ->
        (forall (x : A) (y : B) (l : list A) (l' : list B), R x y -> Forall2 R l l' -> P l l' -> P (l ++ [x]) (l'++[y])) ->
        forall (l : list A) (l0 : list B), Forall2 R l l0 -> P l l0.
    Proof.
      induction l using rev_ind.
      - intros. inversions H1. auto.
      - induction l0 using rev_ind.
        + intros; inversions H1. apply app_unit_not_nil in H3. auto.
        + intros; apply Forall2_inv_app_unit in H1. propositional.
    Qed.

  End Forall2.
  Lemma existsb_false_forall:
    forall {A: Type} (f: A -> bool) (xs: list A),
    existsb f xs = false ->
    forallb (fun a => negb (f a)) xs = true.
  Proof.
    induction xs; auto.
    simpl in *. propositional. rewrite orb_false_iff in H. propositional. rewrite H0. simpl. auto.
  Qed.

  Section Unique.
    Context {A: Type}.
    Context {EqDec_A: EqDec A}.

    Lemma unique_correct:
      forall B xs a (b1 b2: B),
        unique xs = true ->
        In (a,b1) xs ->
        In (a,b2) xs ->
        b1 = b2.
    Proof.
      induction xs; auto.
      simpl. intros; destruct_match_pairs; subst.
      destruct_all_matches.
      + split_cases. simplify. auto.
      + rewrite andb_true_iff in *. propositional. rewrite negb_true_iff in H2.
        apply existsb_false_forall in H2. rewrite forallb_forall in *.
        specialize IHxs with (1 := H3). split_cases; simplify; auto.
        * specialize H2 with (1 := H0). rewrite negb_true_iff in *. rewrite beq_dec_false_iff in *. congruence.
        * specialize H2 with (1 := H). rewrite negb_true_iff in *. rewrite beq_dec_false_iff in *. congruence.
    Qed.

  End Unique.
End Lists.

Section Nats.
  Lemma nat_ltb_succ:
    forall n, Nat.ltb n (S n) = true.
  Proof.
    intros. apply PeanoNat.Nat.ltb_lt. lia.
  Qed.

End Nats.

Section Option.
  Definition option_get_error {A} (v: option A) (default: A) : A :=
    match v with
    | Some v => v
    | None => default
    end.
End Option.
