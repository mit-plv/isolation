Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Export Coq.NArith.BinNat.
Require Export koika.EqDec.

Export ListNotations.
Global Open Scope string_scope.
Global Open Scope list_scope.
Global Open Scope list.

Module Empty.
End Empty.

(*! Debug *)
Definition __debug__ {T U: Type} (t: T) (u: U) : U.
Proof.
  exact u.
Defined.
Opaque __debug__.

Definition debug_id_ty  : Type := string * N.
Definition _id (x: debug_id_ty) := snd x.
Definition strip_debug (id: debug_id_ty) : N := snd id.

#[export] Instance EqDec_debug_id_ty: EqDec debug_id_ty := _.
Definition __Reg (dbg: string) (id: N) : N.
Proof.
  exact id.
Defined.
Definition _Reg (dbg: string) (id: N) : debug_id_ty := (dbg, id).

(* Definition _Var (dbg: string) (id: nat) : nat. *)
(* Proof. *)
(*   exact id. *)
(* Defined. *)

Definition __Fn (dbg: string) (id: N) : N.
Proof.
  exact id.
Defined.
Definition _Fn (dbg: string) (id: N) : debug_id_ty := (dbg, id).

Definition __ExtFn (dbg: string) (id: N) : N.
Proof.
  exact id.
Defined.
Definition _ExtFn (dbg: string) (id: N) : debug_id_ty := (dbg, id).

Definition __Struct (dbg: string) (id: N) : N.
Proof.
  exact id.
Defined.

Definition _Struct (dbg: string) (id: N) : debug_id_ty := (dbg, id).

Definition __StructField (dbg: string) (id: N) : N.
Proof.
  exact id.
Defined.

Definition _StructField (dbg: string) (id: N) : debug_id_ty := (dbg, id).

Definition ErrorT : Type := list (forall T, T).


Opaque _Reg.
Opaque _Fn.
Opaque _ExtFn.
Opaque _Struct.
Opaque _StructField.

(*! Error monad *)

Inductive result {S F} :=
| Success (s: S)
| Failure (f: F).

Arguments result : clear implicits.

Definition is_success {S F} (r: result S F) :=
  match r with
  | Success s => true
  | Failure f => false
  end.

Definition is_success_some {S F} (r: result (option S) F) :=
  match r with
  | Success (Some _) => true
  | _ => false
  end.

Definition extract_success {S F} (r: result S F) (pr: is_success r = true) :=
  match r return is_success r = true -> S with
  | Success s => fun _ => s
  | Failure f => fun pr => match Bool.diff_false_true pr with end
  end pr.

Lemma extract_success_None:
  forall {S F} (term: result S F) (pf: is_success term = true) v,
    term = Success v ->
    extract_success term pf = v.
Proof.
  intros; subst; auto.
Qed.

  Definition success_or_default {A B} (res: result B A) (v: B) : B :=
    match res with
    | Success res => res
    | Failure _ => v
    end.

Lemma Success_inj:
  forall T F v w ,
  @Success T F v = Success w <->
  v = w.
Proof.
  intros. split; intros; subst; auto. inversion H; auto.
Qed.

Notation "'let/res' var ':=' expr 'in' body" :=
  (match expr with
   | Success var => body
   | Failure f => Failure f
   end)
    (at level 200).

Notation "'let/res2' v1 ',' v2 ':=' expr 'in' body" :=
  (match expr with
   | Success (v1,v2) => body
   | Failure f => Failure f
   end)
    (at level 200).

Notation "'let/res3' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
  (match expr with
   | Success (v1,v2,v3) => body
   | Failure f => Failure f
   end)
    (at level 200).

Notation "'let/opt' v1 ':=' expr 'in' body" :=
  (match expr with
   | Some v1 => body
   | None => None
   end)
    (at level 200).

Notation "'let/opt2' v1 ',' v2 ':=' expr 'in' body" :=
  (match expr with
   | Some (v1, v2) => body
   | None => None
   end)
    (at level 200).

Notation "'let/opt3' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
  (match expr with
   | Some (v1, v2, v3) => body
   | None => None
   end)
    (at level 200).

Notation "'let/opt4' v1 ',' v2 ',' v3 ',' v4 ':=' expr 'in' body" :=
  (match expr with
   | Some (v1, v2, v3, v4) => body
   | None => None
   end)
    (at level 200).

Notation "'let/bopt' b ',' v1 ':=' expr 'in' body" :=
  (match expr with
   | (b, Some v1) => body
   | (b, None) => (b, None)
   end) (at level 200).

Notation "'let/bopt2' b ',' v1 ',' v2 ':=' expr 'in' body" :=
  (match expr with
   | (b, Some (v1, v2)) => body
   | (b, None) => (b, None)
   end) (at level 200).

Notation "'let/bopt3' b ',' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
  (match expr with
   | (b, Some (v1, v2, v3)) => body
   | (b, None) => (b, None)
   end) (at level 200).

Notation "'let/bopt4' b ',' v1 ',' v2 ',' v3 ',' v4 ':=' expr 'in' body" :=
  (match expr with
   | (b, Some (v1, v2, v3, v4)) => body
   | (b, None) => (b, None)
   end) (at level 200).

Definition res_opt_bind {A} {B} {C} (res: result (option A) B) (f: A -> result (option C) B) : result (option C) B :=
  match res with
  | Success (Some body) => f body
  | Success None => Success None
  | Failure f => Failure f
  end.
 Notation "'let/resopt' var ':=' expr 'in' body" :=
   (res_opt_bind expr (fun var => body)) (at level 200).

 Notation "'let/resopt2' v1 ',' v2 ':=' expr 'in' body" :=
   (res_opt_bind expr (fun '(v1, v2) => body)) (at level 200).

 Notation "'let/resopt3' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
   (res_opt_bind expr (fun '(v1, v2, v3) => body)) (at level 200).

 Notation "'let/resopt4' v1 ',' v2 ',' v3 ',' v4 ':=' expr 'in' body" :=
   (res_opt_bind expr (fun '(v1, v2, v3, v4) => body)) (at level 200).

 Definition opt_result {S F} (o: option S) (f: F): result S F :=
   match o with
   | Some x => Success x
   | None => Failure f
   end.

  Definition opt_bind_to_res {A B} {C} (c: C) (o: option A) (f: A -> result (option B) C) : result (option B) C :=
    match o with
    | Some x => f x
    | None => Failure c
    end.

  Notation "'let/optres' var ':=' expr 'in' body" :=
    (opt_bind_to_res tt expr (fun var => body)) (at level 200).

  Notation "'let/optres2' v1 ',' v2 ':=' expr 'in' body" :=
    (opt_bind_to_res tt expr (fun '(v1, v2) => body)) (at level 200).

  Notation "'let/optres3' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
    (opt_bind_to_res tt expr (fun '(v1, v2, v3) => body)) (at level 200).

Fixpoint list_find_res {A B} (f: A -> result B unit) (l: list A) : result B unit :=
  match l with
  | [] => Failure tt
  | x :: l =>
    let fx := f x in
    match fx with
    | Success y => Success y
    | Failure tt => list_find_res f l
    end
  end.

Scheme Equality for list.

Section result_list_map.
  Context {A B F: Type}.
  Context (f: A -> result B F).

  (* Written this way to allow use in fixpoints *)
  Fixpoint result_list_map (la: list A): result (list B) F :=
    match la with
    | [] => Success []
    | a :: la => let/res b := f a in
               let/res la := result_list_map la in
               Success (b :: la)
    end.

End result_list_map.

Section result_list_fold.
  Context {A B F: Type}.
  Context (f: A -> B -> result A F).

  Fixpoint result_list_fold_left (lb: list B) (acc: result A F) : result A F :=
    match lb with
    | [] => acc
    | b::lb => let/res acc := acc in
             result_list_fold_left lb (f acc b)
    end.

End result_list_fold.


Section Lists.
  Fixpoint firstn_fill {A: Type} (fill: A) (n: nat) (l: list A) : list A :=
    match n with
    | 0 => nil
    | S n => match l with
            | nil => fill::(firstn_fill fill n l)
            | a :: l => a :: (firstn_fill fill n l)
            end
    end.

  Lemma firstn_fill_length:
    forall {A} (v: A) n vs,
      Datatypes.length (firstn_fill v n vs) = n.
  Proof.
    induction n.
    - simpl. auto.
    - simpl. intros.
      destruct vs.
      + simpl. rewrite IHn. auto.
      + simpl. rewrite IHn. auto.
  Qed.

  Fixpoint find_with_index' {A} (f: A -> bool) (l: list A) (idx: nat): option (nat * A) :=
    match l with
    | [] => None
    | x :: tl => if f x then Some (idx, x) else find_with_index' f tl (S idx)
    end.

  Definition find_with_index {A} (f: A -> bool) (l: list A) : option (nat * A) :=
    find_with_index' f l 0.


  Definition list_sum (l: list nat) :=
    fold_left Nat.add l 0.

  Fixpoint map2 {A B C: Type} (f: A -> B -> C) (l: list A) (l': list B) : result (list C) unit :=
    match l, l' with
    | [], [] =>
      Success []
    | x::tl, y::tl' =>
      let/res tail := map2 f tl tl' in
      Success ((f x y)::tail)
    | _, _ =>
      Failure (__debug__ (l,l',"map2 with different lengths") tt)
    end.

  Fixpoint mapi' {A B} (idx: nat) (f: nat -> A -> B) (l: list A) : list B :=
    match l with
    | [] => []
    | x::tl => (f idx x) :: mapi' (S idx) f tl
    end.

  Definition mapi {A B} (f: nat -> A -> B) (l: list A) : list B :=
    mapi' 0 f l.

  Lemma Forall_single:
    forall {A} (f: A -> Prop) (a: A),
      Forall f [a] <-> f a.
  Proof.
    intros; split; intros; auto.
    apply Forall_inv in H. assumption.
  Qed.

  Section UniqueKeys.
    Context {A B: Type}.
    Context {EqDec_A: EqDec A}.

    Fixpoint unique (xs: list (A * B)) : bool :=
      match xs with
      | [] => true
      | [(a,b)] => true
      | (a,b)::xs =>
          negb (existsb (fun '(a', _) => beq_dec a a') xs) &&
          unique xs
      end.

  End UniqueKeys.
  Lemma In_false:
    forall {A: Type} (EqDec: EqDec A) (x: A) xs,
    (match find (beq_dec x) xs with | Some _ => false | None => true end) = true  ->
    In x xs ->
    False.
  Proof.
    intros. destruct_with_eqn (find (beq_dec x) xs); [discriminate |].
    eapply find_none in Heqo; eauto. rewrite beq_dec_refl in Heqo. discriminate.
  Qed.

End Lists.



Section Option.
  Definition is_someb {A:Type} (opt: option A) : bool :=
    match opt with
    | Some _ => true
    | None => false
    end.

  Definition is_some {A:Type} (opt: option A) : Prop :=
    exists v, opt = Some v.

  Definition is_none {A: Type} (opt: option A) : Prop :=
    opt = None.

  Lemma some_not_none : forall {A: Type} {a: A} {opt},
     opt = Some a -> opt <> None.
  Proof.
    cbv. intros; subst. inversion H0.
  Qed.

  Lemma not_none_is_some: forall {A : Type} {opt: option A},
    opt <> (@None A) -> exists a, opt = Some a.
  Proof.
    intros. destruct opt; eauto. destruct H; auto.
  Qed.

  Lemma some_inj :
    forall A (x: A) (y: A),
    Some x = Some y ->
    x = y.
  Proof.
    intros. inversion H. auto.
  Qed.


  Lemma is_some_Some {A} (v: A):
    is_some (Some v).
  Proof.
    unfold is_some. eauto.
  Qed.

  Lemma is_some_None_False {A: Type} :
    @is_some A None ->
    False.
  Proof.
    unfold is_some. intros. destruct H. discriminate.
  Qed.

End Option.

Section Induction.

Section StrongInduction.
  (* Thanks to tchajed *)
  Variable P:nat -> Prop.

  (** The stronger inductive hypothesis given in strong induction. The standard
  [nat ] induction principle provides only n = pred m, with [P 0] required
  separately. *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

  Lemma P0 : P 0.
  Proof.
    apply IH; intros.
    exfalso; inversion H.
  Qed.

  Hint Resolve P0.

  Lemma pred_increasing : forall n m,
      n <= m ->
      Nat.pred n <= Nat.pred m.
  Proof.
    induction n; cbn; intros.
    apply le_0_n.
    induction H; subst; cbn; eauto.
    destruct m; eauto.
  Qed.

  Hint Resolve le_S_n.

  (** * Strengthen the induction hypothesis. *)

  Local Lemma strong_induction_all : forall n,
      (forall m, m <= n -> P m).
  Proof.
    induction n; intros;
      match goal with
      | [ H: _ <= _ |- _ ] =>
        inversion H
      end; eauto.
  Qed.

  Theorem strong_induction : forall n, P n.
  Proof.
    eauto using strong_induction_all.
  Qed.

End StrongInduction.

Tactic Notation "strong" "induction" ident(n) := induction n using strong_induction.
End Induction.
Global Set Nested Proofs Allowed.
