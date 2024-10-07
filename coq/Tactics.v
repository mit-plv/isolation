Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.
Require Import EquivDec.
Require Import Koika.Common.
Module General.
  Ltac get_innermost_match_in_goal :=
    match goal with
    | [ |- context[match ?E with _ => _ end] ]=>
      match E with
      | context[match _ with _ => _ end] => fail 1
      | _ => E
      end
    | [ |- context[res_opt_bind ?E _]] =>
      match E with
      | context[match _ with _ => _ end] => fail 1
      | _ => E
      end

    end.

  Ltac get_innermost_match_in_hyp H :=
    match type of H with
    | context[match ?E with _ => _ end] =>
      match E with
      | context[match _ with _ => _ end] => fail 1
      | _ => E
      end
    | context[res_opt_bind ?E _] =>
      match E with
      | context[match _ with _ => _ end] => fail 1
      | _ => E
      end
    end.


  Ltac simpl_match :=
    let repl_match_goal d d' :=
        replace d with d';
        lazymatch goal with
        | [ |- context[match d' with _ => _ end] ] => fail
        | _ => idtac
        end in
    let repl_match_hyp H d d' :=
        replace d with d' in H;
        lazymatch type of H with
        | context[match d' with _ => _ end] => fail
        | _ => idtac
        end in
    match goal with
    | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
        repl_match_goal d d'
    | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
        repl_match_goal d d'
    | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
        repl_match_hyp H d d'
    | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
        repl_match_hyp H d d'
    end.

  Ltac match_outermost_in H :=
    match type of H with
    | context[match ?x with | _ => _ end] =>
      destruct x eqn:?
    end.

  Ltac destruct_matches_in e :=
    lazymatch e with
    | context[match ?d with | _ => _ end] =>
        destruct_matches_in d
    | _ =>
        destruct e eqn:?(* ; intros *)
    end.

  Ltac destruct_matches_in_as H e :=
    lazymatch e with
    | context[match ?d with | _ => _ end] =>
        destruct_matches_in_as H d
    | _ =>
        destruct e eqn:H(* ; intros *)
    end.


  Ltac destruct_matches_in_hyp H :=
    lazymatch type of H with
    | context[match ?d with | _ => _ end] =>
        destruct_matches_in d
    | ?v =>
        let H1 := fresh H in
        destruct v eqn:H1(* ; intros *)
    end.


  Ltac destruct_all_matches :=
    repeat (try simpl_match;
            try match goal with
                | [ |- context[match ?d with | _ => _ end] ] =>
                    destruct_matches_in d
                | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                    destruct_matches_in d
                end);
    subst;
    try congruence;
    auto.

  Ltac destruct_all_matches_in_hyps :=
    repeat (try simpl_match;
            try match goal with
                | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                    destruct_matches_in d
                end);
    subst;
    auto.
  Ltac assert_no_dup H :=
    let t := fresh in
    let t := type of H in
    lazymatch goal with
    | H1: t, H2: t |- _ => fail
    | |- _ => idtac
    end.

  Ltac pose_fresh_as H Term :=
    pose proof Term as H; assert_no_dup H.
  Ltac pose_fresh Term :=
    let H := fresh "H" in
    pose_fresh_as H Term.



  Ltac destruct_nongoal_matches :=
    repeat (try simpl_match;
            try match goal with
            | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
                end);
    subst;
    try congruence;
    auto.

  Ltac destruct_match :=
    (match goal with
     | [ |- context[match ?d with | _ => _ end] ] =>
     destruct_matches_in d
     end).

  Ltac destruct_match_as H :=
    (match goal with
     | [ |- context[match ?d with | _ => _ end] ] =>
     destruct_matches_in_as H d
     end).

  Ltac fast_destruct_goal_matches :=
    repeat (match goal with
            | [ |- context[match ?d with | _ => _ end] ] =>
                destruct_matches_in d
            end)
    .

  Ltac fast_destruct_nongoal_matches :=
    repeat (match goal with
            | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
                end).


  Ltac destruct_goal_matches :=
    repeat (try simpl_match;
            match goal with
            | [ |- context[match ?d with | _ => _ end] ] =>
                destruct_matches_in d
            end);
    try congruence;
    auto.

  Tactic Notation "destruct" "matches" "in" "*" := destruct_all_matches.
  Tactic Notation "destruct" "matches" "in" "*|-" := destruct_nongoal_matches.
  Tactic Notation "destruct" "matches" := destruct_goal_matches.



  Ltac match_innermost_in H :=
    match type of H with
    | context[match ?E with _ => _ end] =>
      match E with
      | context[match _ with _ => _ end] => fail 1
      | _ => destruct E eqn:?; simpl in *
      end
    end; subst; try congruence; eauto.

  Ltac match_innermost_in_goal :=
    match goal with
    | [ |- context[match ?E with _ => _ end] ]=>
      match E with
      | context[match _ with _ => _ end] => fail 1
      | _ => destruct E eqn:?; simpl in *
      end
    end; subst; try congruence; eauto.

  Ltac fast_match_innermost_in_goal :=
      match goal with
      | [ |- context[match ?E with _ => _ end] ]=>
        match E with
        | context[match _ with _ => _ end] => fail 1
        | _ => destruct E eqn:?
        end
      end.

  Ltac destruct_one_match_in H :=
    lazymatch type of H with
    | context[match ?d with | _ => _ end] =>
        let H1 := fresh H in
        destruct d eqn:H1
    end.

  Ltac find_match t :=
    match t with
    | context[match ?x with | _ => _ end] =>
      x
    end.

  Ltac assert_match_eq :=
    match goal with
    | |- ?_x = ?_y =>
      let x := find_match _x in
      let y := find_match _y in
      assert (x = y)
    end.

  Ltac assert_match_eq_as H :=
    match goal with
    | |- ?_x = ?_y =>
      let x := find_match _x in
      let y := find_match _y in
      assert (x = y) as H
    end.

  Ltac assert_if_eq_as H v :=
    match goal with
    | |- context[if ?x then _ else _] =>
      assert (x = v) as H; [ | rewrite H]
    end.

  Ltac destruct_pair :=
    match goal with
    | [ P : _ * _ |- _ ] =>
      let p1 := fresh P in
      let p2 := fresh P in
      destruct P as [p1 p2]
  end.

  Ltac destruct_pairs := repeat destruct_pair.

  Ltac destruct_match_pairs :=
    repeat match goal with
           | H: context[let '(_,_) := ?x in _] |- _ =>
             destruct x eqn:?
           | |- context[let '(_,_) := ?x in _] =>
             destruct x eqn:?
           end.


  Ltac destruct_one_ind :=
    match goal with
    | [ H: ?T |- _ ] => is_ind T; destruct H
    end.

  Ltac destruct_inds := repeat destruct_one_ind.

  Ltac destruct_rightmost_var term :=
    lazymatch term with
    | ?f ?x =>
        destruct_rightmost_var x
    | ?x => is_var x; destruct x
    end.

  Ltac destruct_one_var_with t :=
    match goal with
    | [ H: ?T |- _ ] => is_var H; destruct H; try t
    end.

  Ltac destruct_vars_with t :=
    repeat (destruct_one_var_with t).

  Tactic Notation "destruct_one_var" := destruct_one_var_with auto.
  Tactic Notation "destruct_vars_with" tactic(t) := repeat (destruct_one_var_with t).
  Tactic Notation "destruct_vars" := destruct_vars_with auto.

  Ltac solve' :=
    match goal with
    | |- ?x = (fst ?x, snd ?x) =>
      destruct x; reflexivity
    | [ H: False |- _ ] => solve [ destruct H ]
    | [ H: ?P |- ?P ] => exact H
    end.



  Ltac destruct_units :=
    repeat match goal with
           | x: unit |- _ =>
             destruct x
           end.


  Ltac propositional_with t :=
    repeat match goal with
    | [ H : _ /\ _  |- _ ] =>
        let H1 := fresh H in
        let H2 := fresh H in
        destruct H as [H1 H2]
    | [ H : _ <-> _  |- _ ] =>
        let H1 := fresh H in
        let H2 := fresh H in
        destruct H as [H1 H2]
    | |- forall _, _ => intros
    | [ H: False |- _ ] => solve [ destruct H ]
    | [ |- True ] => exact I
    | [ H : exists (varname: _ ), _ |- _ ] =>
        let newvar := fresh varname in
        let Hpref  := fresh H in
        destruct H as [newvar Hpref]
    | [ H: ?P -> _ |- _ ] =>
      lazymatch type of P with
      | Prop => match goal with
            | [ H': P |- _ ] => specialize (H H')
            | _ => specialize (H ltac:(try t))
            end
      end
    | [ H: forall x, x = _ -> _ |- _ ] =>
      specialize (H _ eq_refl)
    | [ H: forall x, _ = x -> _ |- _ ] =>
      specialize (H _ eq_refl)
    | [ H: exists (varname : _), _ |- _ ] =>
      let newvar := fresh varname in
      destruct H as [newvar ?]
    | [ H: ?P |- ?P ] => exact H
    | _ => progress subst
    | _ => solve [ t ]
    end.

  Tactic Notation "propositional" := propositional_with auto.
  Tactic Notation "propositional" tactic(t) := propositional_with t.

  Ltac safe_propositional_with t :=
    repeat match goal with
    | [ H : _ /\ _  |- _ ] =>
        let H1 := fresh H in
        let H2 := fresh H in
        destruct H as [H1 H2]
    | [ H : _ <-> _  |- _ ] =>
        let H1 := fresh H in
        let H2 := fresh H in
        destruct H as [H1 H2]
    | |- forall _, _ => intros
    | [ H: False |- _ ] => solve [ destruct H ]
    | [ |- True ] => exact I
    | [ H : exists (varname: _ ), _ |- _ ] =>
        let newvar := fresh varname in
        let Hpref  := fresh H in
        destruct H as [newvar Hpref]
    | [ H: ?P -> _ |- _ ] =>
      lazymatch type of P with
      | Prop => match goal with
            | [ H': P |- _ ] => specialize (H H')
            | _ => specialize (H ltac:(try t))
            end
      end
    (* | [ H: forall x, x = _ -> _ |- _ ] => *)
    (*   specialize (H _ eq_refl) *)
    (* | [ H: forall x, _ = x -> _ |- _ ] => *)
    (*   specialize (H _ eq_refl) *)
    | [ H: exists (varname : _), _ |- _ ] =>
      let newvar := fresh varname in
      destruct H as [newvar ?]
    | [ H: ?P |- ?P ] => exact H
    | _ => progress subst
    | _ => solve [ t ]
    end.

  Tactic Notation "safe_propositional" := safe_propositional_with auto.
  Tactic Notation "safe_propositional" tactic(t) := safe_propositional_with t.


  Ltac assert_left :=
    match goal with
    | |- ?t /\ _ => assert t; [ | split; auto]
    end.
  Ltac assert_right :=
    match goal with
    | |- _ /\ ?x => assert x; [ | split; auto]
    end.

  Ltac assert_left_as H :=
    match goal with
    | |- ?t /\ _ => assert t as H; [ | split; auto]
    end.
  Ltac assert_right_as H :=
    match goal with
    | |- _ /\ ?x => assert x as H; [ | split; auto]
    end.

 Ltac split_ands_in_hyp H :=
   match type of H with
   | _ /\ _  =>
     let H1 := fresh H in
     let H2 := fresh H in
     destruct H as [H1 H2];
     try split_ands_in_hyp H1; try split_ands_in_hyp H2
   end.


  Ltac split_ands_in_hyps :=
    repeat match goal with
    | H: _ /\ _ |- _ =>
      split_ands_in_hyp H
    end.

  Ltac split_ands_in_hyps' :=
    repeat match goal with
    | [ H : _ /\ _  |- _ ] =>
        let H1 := fresh H in
        let H2 := fresh H in
        destruct H as [H1 H2]
    end.


  Ltac split_ands_in_goal :=
    repeat match goal with
           | [ |- _ /\ _ ] =>
             split
           end.

  Ltac split_ors_in H:=
    repeat match type of H with
    | _ \/ _ =>
      destruct H as [H | H]; split_ors_in H
    end.

  Ltac split_cases :=
    repeat match goal with
    | |- _ /\ _ => split
    | [ H: _ \/ _ |- _ ] => destruct H
    | _ => progress propositional
    | _ => solve [ eauto ]
    end; try discriminate.

  Ltac consider f := unfold f in *.

  Ltac inversions H :=
    inversion H; subst; clear H.

  Lemma or_false_r :
    forall p, p \/ False -> p.
  Proof.
    intros; split_cases; auto.
  Qed.
  Lemma or_false_l :
    forall p, False \/ p -> p.
  Proof.
    intros; split_cases; auto.
  Qed.


  Ltac simplify_result :=
    repeat match goal with
         | H: (match ?v with
               | Success _ => _
               | Failure _ => False
               end) |- _ =>
           destruct_matches_in_hyp H; [ | contradiction]
        | H: (match ?v with
              | Some _ => _
              | None => Failure _
              end) = Success _ |- _ =>
          destruct_matches_in_hyp H; [ | simpl in H; discriminate]
        | H: match ?v with
             | Some _ => _
             | None => Success None
             end = Success (Some _) |- _ =>
            destruct_matches_in_hyp H; [ | discriminate]
        | H: Success _ = Success _ |- _ =>
          inversions H
        | H: Failure _ = Failure _ |- _ =>
          inversions H
        | H : is_success (Failure _) = true |- _ =>
          simpl in H; discriminate
        | H: is_success (let/res _ := _ in _) = true |- _ =>
          destruct_matches_in_hyp H
        | H: is_success (if _ then _ else Failure _) = true |- _ =>
          destruct_matches_in_hyp H
        | H: (if _ then _ else Failure _) = Success _ |- _ =>
          destruct_matches_in_hyp H
        | H: (let/res _ := _ in _) = Success _ |- _ =>
          destruct_matches_in_hyp H
        | H: (match _ with | Success _ => _ | Failure _ => Failure _ end) = Success _ |- _ =>
          destruct_matches_in_hyp H; [| discriminate]
        | H: (let/res _ := _ in Success _) = Failure _ |- _ =>
          destruct_matches_in_hyp H; [discriminate | ]
        | H: Success _ = Failure _ |- _ => clear - H; discriminate
        | H: Failure _ = Success _ |- _ => clear - H; discriminate
        end.

  Lemma simple_tuple_inversion:
    forall {A} {B} (a: A) (b: B) x y,
    (a,b) = (x,y) ->
    a = x /\ b = y.
  Proof.
    intros. inversion H. auto.
  Qed.

  Ltac simplify_tuples :=
    repeat match goal with
    | [ H: (_,_) = (_,_) |- _ ] =>
      apply simple_tuple_inversion in H; destruct H
    end.

  Ltac simplify_tupless := simplify_tuples; subst.

  Ltac simplify_all :=
    simpl in *; simplify_tuples; subst; auto.

  Lemma extra_match_eq:
    forall {A} (opt: option A),
    match opt with
    | Some v => Some v
    | None => None
    end = opt.
  Proof.
    intros. destruct opt; auto.
  Qed.

  Ltac simplify_extra_match :=
    rewrite extra_match_eq.

  Ltac subst_tuple_for t :=
    match goal with
    | H: _ = (t,?b) |- _ =>
      replace t with (fst (t,b)) by auto; setoid_rewrite<-H
    | H: _ = (?a,t) |- _ =>
      replace t with (snd (a,t)) by auto; setoid_rewrite<-H
    | H: _ = (?a,t,?c) |- _ =>
      replace t with (snd (fst(a,t,c))) by auto; setoid_rewrite<-H
    | H: _ = (t,?b,?c) |- _ =>
      replace t with (fst(fst(t,b,c))) by auto; setoid_rewrite<-H
    end.

  Ltac bash_destruct H :=
    repeat destruct_matches_in_hyp H; simpl in H; simplify_tupless; try congruence.


  Ltac option_simpl :=
    repeat match goal with
    | [ H : Some _ = Some _  |- _ ] =>
      apply some_inj in H
    | [ H : Some _ = None |- _ ] =>
      inversion H
    | [ H : None = Some _ |- _ ] =>
      inversion H
    | [ H : None <> None |- _ ] =>
      destruct H
    | [ H : is_none _ |- _ ] =>
        unfold is_none in H
    | [ |- Some _ <> None ] =>
        let H := fresh in
        hnf; intro H; inversion H
    | [ |- Some _ = Some _] =>
        f_equal
    | [ H1: ?x = Some _,
        H2: ?x = Some _ |- _ ] =>
      rewrite H1 in H2; clear H1
    | H: (match ?v with
          | Some _ => _
          | None => False
          end) |- _ =>
      destruct_matches_in_hyp H; [ | contradiction]
    | H: is_some (Some ?a) -> _ |- _ =>
      specialize H with (1 := is_some_Some _)
    | H1: is_some ?v -> _,
      H2: ?v = Some _ |- _ =>
      rewrite H2 in H1
    | H: is_some None |- _ =>
      exfalso; apply is_some_None_False in H; auto
    | H: match _ with | Some _ => _ | None => None end = Some _ |- _ =>
      destruct_matches_in_hyp H; [ | discriminate]
    | H: match _ with | Some _ => false | None => true end = true |- _ =>
      destruct_matches_in_hyp H; [ discriminate| ]
    end.

  Ltac simplify_bool :=
    repeat match goal with
           | H: true = false |- _ => discriminate
           | H: false = true |- _ => discriminate
           | H: (if _ then false else _) = true |- _ =>
             destruct_matches_in_hyp H; [discriminate |]
           | H: (if _ then _ else false) = true |- _ =>
             destruct_matches_in_hyp H; [|discriminate]
           | H: _ && false = _ |- _ => rewrite andb_false_r in H
           end.

  Ltac simplify_nat :=
    repeat match goal with
    | H: Nat.ltb _ _ = false |- _ =>
      apply PeanoNat.Nat.ltb_ge in H
    | H: Nat.ltb _ _ = true |- _ =>
      apply PeanoNat.Nat.ltb_lt in H
    | H: Nat.eqb _ _ = true |- _ =>
      apply PeanoNat.Nat.eqb_eq in H
    | H: Nat.eqb _ _ = false |- _ =>
      apply PeanoNat.Nat.eqb_neq in H
    end.

  Ltac simplify :=
    repeat match goal with
    | _ => progress simplify_tupless
    | _ => progress destruct_match_pairs
    | _ => progress simplify_result
    | _ => progress option_simpl
    | _ => progress simplify_nat
    | _ => progress simplify_bool
    | H: _ \/ False |- _ => apply or_false_r in H
    | H: False \/ _ |- _ => apply or_false_l in H
    end.




  Ltac rewrite_term_from_tuple term :=
    match goal with
    | [H: _ = (term, ?y) |- _ ] =>
      replace term with (fst (term, y)) by auto;
      rewrite<-H
    | [H: _ = (?x, term) |- _ ] =>
      replace term with (snd (x, term)) by auto;
      rewrite<-H
    end.

  Ltac rewrite_in_hyps t :=
    repeat match goal with
           | H: _ |- _ => rewrite t in H
           end.


  Ltac rewrite_in_goal :=
    repeat lazymatch goal with
    | H: ?x = ?x |- _ =>  fail 1
    | H: ?x = _ |- context[?x] =>
        rewrite H
    end.


  Ltac rewrite_solve :=
    match goal with
    | [ H: _ |- _ ] => solve[rewrite H; try congruence; auto]
    end.

  Ltac destruct_tuple :=
    match goal with
    | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
      let a := fresh a in
      let b := fresh b in
      destruct p as [a b]
    | [ |- context[let '(a, b) := ?p in _] ] =>
      let a := fresh a in
      let b := fresh b in
      destruct p as [a b]
    end.

  Ltac safe_intuition_then t :=
    repeat match goal with
           | [ H: _ /\ _ |- _ ] =>
             destruct H
           | [ H: ?P -> _ |- _ ] =>
             lazymatch type of P with
             | Prop => specialize (H ltac:(t))
             | _ => fail
             end
           | [ |- not _ ] =>
             unfold not; intros
           | _ => progress t
           end.

  Tactic Notation "safe_intuition" := safe_intuition_then ltac:(auto).
  Tactic Notation "safe_intuition" tactic(t) := safe_intuition_then t.

  Ltac destruct_ands :=
    repeat match goal with
           | [ H: _ /\ _ |- _ ] =>
             destruct H
           end.

  Ltac deex :=
    match goal with
    | [ H : exists (varname : _), _ |- _ ] =>
      let newvar := fresh varname in
      destruct H as [newvar ?]; destruct_ands; subst
    end.

  Ltac split_or :=
    repeat match goal with
           | [ H: _ \/ _ |- _ ] => destruct H
           end.

  Ltac intuition_with t :=
    repeat match goal with
           | [ H: _ \/ _ |- _ ] => destruct H
           | [ |- not _ ] =>
             unfold not; intros
           | _ => progress propositional_with t
           | |- _ /\ _ => split
           | |- _ <-> _ => split
           | _ => t
           end.

  Tactic Notation "intuition" := intuition_with auto.
  Tactic Notation "intuition" tactic(t) := intuition_with t.

  Tactic Notation "assert_false" :=
    elimtype False.

  Ltac solve_false :=
    solve [ exfalso; eauto with false ].


  #[export] Hint Extern 10 => Equality.is_ground_goal; progress exfalso : core.

  Ltac assert_pre H :=
    match type of H with
    | ?x -> _ => assert x
    end.

  Ltac assert_pre_as Hnew H :=
    match type of H with
    | ?x -> _ => assert x as Hnew
    end.

  Ltac assert_pre_and_specialize H :=
    match type of H with
    | ?x -> _ =>
      let Hnew := fresh in
      assert x as Hnew; [ | specialize H with (1 := Hnew); clear Hnew]
    end.


  Ltac assert_conclusion H V :=
    match V with
    | _ -> ?X => assert_conclusion  H X
    | ?X => assert X as H
    end.

  Ltac assert_conclusion_of H Hnew :=
    match type of H with
    | ?X => assert_conclusion Hnew X
    end.



  Ltac especialize H :=
    match type of H with
    | forall (x:?T), _ =>
      let x := fresh x in
      evar (x:T);
      specialize (H x);
      subst x
    end.

  Ltac rename_by_type type name :=
    match goal with | x : type |- _ => rename x into name end.

  Ltac lia :=
  repeat match goal with
         | [ H: ?a <> ?a |- _ ] =>
           exfalso; apply (H eq_refl)
         | |- _ <> _ => let H := fresh in
                     intro H;
                     try rewrite H in *
         | [ n: ?t |- _ ] => progress change t with nat
         | [ H: @eq ?t _ _ |- _ ] =>
           progress change t with nat in H
         | [ H: ~ (@eq ?t _ _) |- _ ] =>
           progress change t with nat in H
         | [ |- @eq ?t _ _ ] =>
           progress change t with nat
         | [ |- ~ (@eq ?t _ _) ] =>
           progress change t with nat
         end; Lia.lia.

  Ltac dep_destruct E := let x := fresh "x" in
      remember E as x; simpl in x; dependent destruction x;
        try match goal with
              | [ H : _ = E |- _ ] => rewrite <- H in *; clear H
            end.

  Ltac dep_destruct_in_hyp H :=
    match type of H with
    | context[match ?x with _ => _ end] =>
        dep_destruct x
    end.

  Ltac auto_dep_destruct :=
    match goal with
    | H: context[match ?x as _ return _ with _ => _ end] |- _ =>
        dep_destruct x
    | |- context[match ?x as _ return _ with _ => _ end] =>
        dep_destruct x
    end.

End General.

Export General.

Module SimplMatchTests.

  (** test simpl_match failure when match does not go away *)
  Lemma fails_if_match_not_removed :
    forall (vd m: nat -> option nat) a,
      vd a = m a ->
      vd a = match (m a) with
             | Some v => Some v
             | None => None
             end.
  Proof.
    intros.
    (simpl_match; fail "should not work here")
    || idtac.
    rewrite H.
    destruct (m a); auto.
  Qed.

  Lemma removes_match :
    forall (vd m: nat -> option nat) a v v',
      vd a = Some v ->
      m a = Some v' ->
      vd a = match (m a) with
             | Some _ => Some v
             | None => None
             end.
  Proof.
    intros.
    simpl_match; now auto.
  Qed.

  (** hypothesis replacement should remove the match or fail *)
  Lemma fails_on_hyp_if_match_not_removed :
    forall (vd m: nat -> option nat) a,
      vd a = m a ->
      m a = match (m a) with
            | Some v => Some v
            | None => None
            end ->
      True.
  Proof.
    intros.
    (simpl_match; fail "should not work here")
    || idtac.
    trivial.
  Qed.

End SimplMatchTests.

Module DestructMatchesTests.

  Lemma removes_absurdities :
    forall b1 b2,
      b1 = b2 ->
      match b1 with
      | true => match b2 with
               | true => True
               | false => False
               end
      | false => match b2 with
                | true => False
                | false => True
                end
      end.
  Proof.
    intros.
    destruct_all_matches.
  Qed.

  Lemma destructs_innermost_match :
    forall b1 b2,
      match (match b2 with
             | true => b1
             | false => false
             end) with
      | true => b1 = true
      | false => b1 = false \/ b2 = false
      end.
  Proof.
    intros.
    destruct_goal_matches.
  Qed.

End DestructMatchesTests.


Module DeexTests.

  Lemma chooses_name :
    (exists (foo:unit), foo=foo) ->
    True.
  Proof.
    intros.
    deex.
    destruct foo.
    trivial.
  Qed.

  Lemma chooses_fresh_name :
    forall (foo:bool),
      (exists (foo:unit), foo=foo) -> True.
  Proof.
    intros.
    deex.
    (* fresh name for exists witness *)
    destruct foo0.
    trivial.
  Qed.

End DeexTests.
