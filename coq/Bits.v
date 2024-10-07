Require Import Koika.Common.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

(* Purge state machine *)
Declare Scope bits.

Notation "bs '~' b" := (b::bs) (at level 7, left associativity, format "bs '~' b") : bits.
Notation "bs '~' 0" := (false::bs) (at level 7, left associativity, format "bs '~' 0") : bits.
Notation "bs '~' 1" := (true::bs) (at level 7, left associativity, format "bs '~' 1") : bits.
Notation "'Ob'" := [] (at level 7) : bits.

Definition vect_t : Type := list bool.

Fixpoint to_N (bv: vect_t) : N :=
  match bv with
  | [] => 0
  | x::xs => (if x then 1 else 0) + 2 * (to_N (xs))
  end.

Definition to_nat (bv: vect_t) : nat :=
  N.to_nat (to_N bv).

Fixpoint of_positive (p: positive) : vect_t :=
  match p with
  | xI p => true::(of_positive p)
  | xO p => false::(of_positive p)
  | xH => [true]
  end.

Definition of_N (n: N) : vect_t :=
  match n with
  | N0 => []
  | Npos p => of_positive p
  end.

Definition of_nat (sz: nat) (n: nat) : vect_t :=
  firstn_fill false sz (of_N (N.of_nat n)).

Definition lsb (bs: vect_t) := List.hd false bs.
Definition msb (bs: vect_t) := List.last bs false.

Definition neg (arg: vect_t) : vect_t := map negb arg.

Section Z.
  Local Open Scope Z_scope.

  Definition to_2cZ (bs: vect_t) : Z :=
    if msb bs then
      match to_N (neg bs) with
      | N0 => -1%Z
      | Npos x => Zneg (Pos.succ x)
      end
    else
      match to_N bs with
      | N0 => 0%Z
      | Npos x => Zpos x
      end.
End Z.

Definition slice (offset: nat) (width: nat) (arg: vect_t) : vect_t :=
  firstn_fill false width (List.skipn offset arg).

Definition slice_subst (offset: nat) (new: vect_t) (bs: vect_t) : vect_t :=
  let front := firstn offset bs in
  let tail := skipn (offset + List.length new) bs in
  front ++ new ++ tail.


Definition and (arg1 arg2: vect_t) : result (vect_t) unit :=
  map2 andb arg1 arg2.

Definition or (arg1 arg2: vect_t) : result (vect_t) unit :=
  map2 orb arg1 arg2.

Definition xor (arg1 arg2: vect_t) : result (vect_t) unit :=
  map2 xorb arg1 arg2.

Definition concat (arg1 arg2: vect_t) : vect_t :=
  arg2 ++ arg1. (* reversed! *)

Definition sel (arg1 arg2: vect_t) : result bool unit :=
  if Nat.ltb (to_nat arg2) (List.length arg1) then
    opt_result (List.nth_error arg1 (to_nat arg2)) (__debug__ ("BV.sel:index out of bounds", arg1, arg2) tt)
  else Success false.

Section Npow2.
  Open Scope N_scope.

  Lemma N_lt_pow2_succ_1 :
    forall n m,
      1 + 2 * n < 2 ^ N.succ m ->
      n < 2 ^ m.
  Proof.
    intros * Hlt.
    rewrite N.pow_succ_r' in Hlt.
    rewrite N.mul_lt_mono_pos_l with (p := 2).
    rewrite N.add_1_l in Hlt.
    apply N.lt_succ_l.
    eassumption.
    econstructor.
  Qed.

  Lemma N_lt_pow2_succ :
    forall n m,
      2 * n < 2 ^ N.succ m ->
      n < 2 ^ m.
  Proof.
    intros * Hlt.
    rewrite N.pow_succ_r' in Hlt.
    rewrite N.mul_lt_mono_pos_l with (p := 2).
    eassumption.
    econstructor.
  Qed.

  Lemma N_pow_Nat_pow :
    forall n m,
      N.pow (N.of_nat m) (N.of_nat n) =
      N.of_nat (Nat.pow m n).
  Proof.
    induction n; intros.
    - reflexivity.
    - rewrite Nat2N.inj_succ; cbn; rewrite Nat2N.inj_mul, <- IHn.
      rewrite N.pow_succ_r'; reflexivity.
  Qed.
  Lemma to_N_bounded:
    forall (bs: vect_t),
      (Bits.to_N bs < 2 ^ N.of_nat (Datatypes.length bs))%N.
  Proof.
    induction bs; cbn -[N.pow N.mul]; auto.
    - constructor.
    - setoid_rewrite Nat2N.inj_succ; rewrite N.pow_succ_r';
      destruct a; cbn -[N.pow N.mul N.add]; lia.
  Qed.

End Npow2.

Section pow2.
  Definition pow2 n :=
    S (pred (Nat.pow 2 n)).
  Lemma pow2_correct : forall n, pow2 n = Nat.pow 2 n.
  Proof.
    unfold pow2; induction n; simpl.
    - reflexivity.
    - destruct (Nat.pow 2 n); simpl; (discriminate || reflexivity).
  Qed.

  Lemma le_pow2_log2 :
    forall sz, sz <= pow2 (Nat.log2_up sz).
  Proof.
    intros; rewrite pow2_correct.
    destruct sz; [ | apply Nat.log2_log2_up_spec ]; auto with arith.
  Qed.

  Lemma pred_lt_pow2_log2 :
    forall sz, pred sz < pow2 (Nat.log2_up sz).
  Proof.
    destruct sz; cbn; auto using le_pow2_log2 with arith.
  Qed.

  Lemma to_nat_bounded:
    forall (bs: vect_t), Bits.to_nat bs < pow2 (Datatypes.length bs).
  Proof.
    unfold Bits.to_nat; intros.
    rewrite pow2_correct, <- Nat.compare_lt_iff.
    rewrite Nat2N.inj_compare, N2Nat.id, <- N_pow_Nat_pow, N.compare_lt_iff.
    apply to_N_bounded.
  Qed.

End pow2.

Lemma to_N_of_N :
  forall n , to_N (of_N n) = n.
Proof.
  destruct n; simpl.
  - reflexivity.
  - induction p; eauto; cbn - [N.mul N.add]; rewrite IHp; eauto.
Qed.

Lemma neg_involutive :
  forall bs, neg (neg bs) = bs.
Proof.
  unfold neg. intros; rewrite map_map.
  rewrite<-map_id.
  apply map_ext. intros. rewrite negb_involutive.
  reflexivity.
Qed.

Definition plus (arg1 arg2: vect_t) : result (vect_t) unit :=
  if Nat.eqb (List.length arg1) (List.length arg2) then
    Success (firstn_fill false (List.length arg1) (of_N (to_N arg1 + to_N arg2)))
  else Failure (__debug__ ("BV.plus: different arg length", arg1, arg2) tt).

Definition zeroes (sz: nat) := firstn_fill false sz [].
Definition ones (sz: nat) := firstn_fill true sz [].

Lemma zeroes_length:
  forall n,
  Datatypes.length (zeroes n) = n.
Proof.
  unfold zeroes.
  intros. apply firstn_fill_length.
Qed.

Definition one (sz: nat) := firstn_fill false sz (of_N N.one).

Definition minus (arg1 arg2: vect_t) : result (vect_t) unit :=
  let/res x := plus arg1 (neg arg2) in
  plus x (one (List.length x)).

Definition bitfun_of_predicate
           (p: vect_t -> vect_t -> result bool unit )
           (bs1 bs2: vect_t) : result (vect_t) unit :=
  let/res res := p bs1 bs2 in
  Success [res].

Section Comparisons.
  Scheme Equality for comparison.
  Infix "==c" := comparison_beq (at level 0).
  Local Open Scope bool_scope.
  Definition is_lt (cmp: comparison) : bool :=
    cmp ==c Lt.
  Definition is_le (cmp: comparison) : bool :=
    cmp ==c Lt || cmp ==c Eq.
  Definition is_gt (cmp: comparison) : bool :=
    cmp ==c Gt.
  Definition is_ge (cmp: comparison) : bool :=
    cmp ==c Gt || cmp ==c Eq.

  Definition lift_comparison {A}
             (cast: vect_t -> A) (compare: A -> A -> comparison)
             (cmp: comparison -> bool)
             (bs1 bs2: vect_t) : bool :=
    cmp (compare (cast bs1) (cast bs2)).

  Definition unsigned_lt (bs1 bs2: vect_t) : result bool unit :=
    if Nat.eqb (List.length bs1) (List.length bs2) then
      Success (lift_comparison to_N N.compare is_lt bs1 bs2)
    else Failure (__debug__ ("BV.unsigned_lt: different arg length", bs1, bs2) tt).
  Definition unsigned_le (bs1 bs2: vect_t) : result bool unit :=
    if Nat.eqb (List.length bs1) (List.length bs2) then
      Success (lift_comparison to_N N.compare is_le bs1 bs2)
    else Failure (__debug__ ("BV.unsigned_le: different arg length", bs1, bs2) tt).
  Definition unsigned_gt (bs1 bs2: vect_t) : result bool unit :=
    if Nat.eqb (List.length bs1) (List.length bs2) then
      Success (lift_comparison to_N N.compare is_gt bs1 bs2)
    else Failure (__debug__ ("BV.unsigned_gt: different arg length", bs1, bs2) tt).
  Definition unsigned_ge (bs1 bs2: vect_t) : result bool unit :=
    if Nat.eqb (List.length bs1) (List.length bs2) then
      Success (lift_comparison to_N N.compare is_ge bs1 bs2)
    else Failure (__debug__ ("BV.unsigned_ge: different arg length", bs1, bs2) tt).

  Definition signed_lt (bs1 bs2: vect_t) : result bool unit :=
    if Nat.eqb (List.length bs1) (List.length bs2) then
      Success (lift_comparison to_2cZ Z.compare is_lt bs1 bs2)
    else Failure (__debug__ ("BV.signed_lt: different arg length", bs1, bs2) tt).

  Definition signed_le (bs1 bs2: vect_t) : result bool unit :=
    if Nat.eqb (List.length bs1) (List.length bs2) then
      Success (lift_comparison to_2cZ Z.compare is_le bs1 bs2)
    else Failure (__debug__ ("BV.signed_le: different arg length", bs1, bs2) tt).

  Definition signed_gt (bs1 bs2: vect_t) : result bool unit :=
    if Nat.eqb (List.length bs1) (List.length bs2) then
      Success (lift_comparison to_2cZ Z.compare is_gt bs1 bs2)
    else Failure (__debug__ ("BV.signed_gt: different arg length", bs1, bs2) tt).

  Definition signed_ge (bs1 bs2: vect_t) : result bool unit :=
    if Nat.eqb (List.length bs1) (List.length bs2) then
      Success (lift_comparison to_2cZ Z.compare is_ge bs1 bs2)
    else Failure (__debug__ ("BV.signed_ge: different arg length", bs1, bs2) tt).

  Definition bits_eq (bs1 bs2: vect_t) :=
    list_beq _ Bool.eqb bs1 bs2.
End Comparisons.
