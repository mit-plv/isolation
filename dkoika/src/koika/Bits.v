Require Import koika.Common.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import koika.Tactics.

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

Definition of_N_sz (sz: nat) (n: N) : vect_t :=
  firstn_fill false sz (of_N n).


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

Fixpoint vect_dotimes {A} (f: A -> A) n (v: A) : A :=
  match n with
  | 0 => v
  | S n => vect_dotimes f n (f v)
  end.

Definition vect_snoc (b: bool) (v: vect_t) : vect_t :=
  v ++ [b].

Fixpoint vect_unsnoc (b: vect_t) : bool * vect_t :=
  match b with
  | nil => (false,[]) (* should not occur *)
  | [x] => (x, [])
  | x::xs => let '(t,v') := vect_unsnoc xs in
           (t, x::v')
  end.

Definition asr1 (b: vect_t) : vect_t :=
  match b with
  | nil => nil
  | _ => vect_snoc (msb b) (tl b)
  end.

Definition lsr1 (b: vect_t) : vect_t :=
  match b with
  | nil => nil
  | _ => vect_snoc (false) (tl b)
  end.

Definition lsl1 (b: vect_t) : vect_t :=
  match b with
  | nil => nil
  | _ => (false)::(snd(vect_unsnoc b))
  end.


Definition asr (nplaces: nat) (b: vect_t) : vect_t :=
  vect_dotimes asr1 nplaces b.

Definition lsr (nplaces: nat) (b: vect_t) : vect_t :=
  vect_dotimes lsr1 nplaces b.

Definition lsl (nplaces: nat) (b: vect_t) : vect_t :=
  vect_dotimes lsl1 nplaces b.
Definition vect_const (b: bool) (sz: nat) : vect_t :=
  firstn_fill b sz [].

Definition extend_end (bs: vect_t) (sz: nat) (b: bool) : vect_t :=
  bs ++ (vect_const b (sz - (List.length bs))).

Lemma vect_snoc_length:
  forall bs b, Datatypes.length (vect_snoc b bs) = S (Datatypes.length bs).
Proof.
  unfold vect_snoc. intros. rewrite app_length. simpl. lia.
Qed.

Lemma asr_length :
  forall places b, Datatypes.length (asr places b) = Datatypes.length b.
Proof.
  induction places; simpl; auto.
  induction b; simpl; eauto.
  - unfold asr in *. simpl.
    rewrite IHplaces.
    rewrite vect_snoc_length. reflexivity.
Qed.
Lemma vect_unsnoc_length:
  forall bs b, Datatypes.length (snd (vect_unsnoc (b::bs))) = Datatypes.length bs.
Proof.
  induction bs.
  - simpl. auto.
  - cbn. simpl in *. intros. destruct bs; auto.
    destruct_match; simpl. simpl in IHbs. propositional.
Qed.

Lemma lsr_length :
  forall places b, Datatypes.length (lsr places b) = Datatypes.length b.
Proof.
  induction places; simpl; auto.
  induction b; simpl; eauto.
  - unfold lsr in *. simpl.
    rewrite IHplaces.
    rewrite vect_snoc_length. reflexivity.
Qed.

Lemma lsl_length :
  forall places b, Datatypes.length (lsl places b) = Datatypes.length b.
Proof.
  induction places; simpl; auto.
  induction b; simpl; eauto.
  - unfold lsl in *. cbn - [vect_unsnoc].
    rewrite IHplaces. cbn - [vect_unsnoc].
    rewrite vect_unsnoc_length. reflexivity.
Qed.

  Lemma bits_slice_length:
    forall offset width bs,
    Datatypes.length (slice offset width bs) = width.
  Proof.
    unfold slice. intros.  rewrite firstn_fill_length; auto.
  Qed.

Lemma slice_subst_length:
  forall vect n arg,
  Datatypes.length vect >= n + Datatypes.length arg ->
  Datatypes.length (slice_subst n arg vect) = Datatypes.length vect.
Proof.
  unfold slice_subst. intros. repeat rewrite app_length.
  rewrite firstn_length. rewrite skipn_length. lia.
Qed.

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
Lemma bitfun_unsigned_le_iff:
  forall base data,
  Datatypes.length base = Datatypes.length data ->
  (to_N base <= to_N data)%N <->
    success_or_default (bitfun_of_predicate unsigned_le base  data) [] = [true].
Proof.
  intros * hlen.
  unfold bitfun_of_predicate.
  unfold unsigned_le. rewrite hlen. rewrite PeanoNat.Nat.eqb_refl.
  simpl. unfold lift_comparison. unfold is_le. unfold comparison_beq.
  destruct_match; auto.
  - rewrite N.compare_eq_iff in Heqc. simpl. rewrite Heqc.
    split; auto. lia.
  - rewrite N.compare_lt_iff in Heqc. simpl. split; auto; lia.
  - rewrite N.compare_gt_iff in *. simpl. split; propositional; try lia.
    discriminate.
Qed.
Lemma bitfun_unsigned_lt_plus:
  forall data base size,
  Datatypes.length base = Datatypes.length size ->
  Datatypes.length base = Datatypes.length data ->
  (to_N data < match (Bits.plus base size) with
               | Success v => Bits.to_N v
               | Failure _ => 0
               end)%N <->
    success_or_default (bitfun_of_predicate unsigned_lt data
      (success_or_default (plus base size) [])) [] = [true].
Proof.
  intros * hlen_size hlen_data.
  unfold bitfun_of_predicate.
  unfold unsigned_lt. unfold plus. rewrite<-hlen_size. rewrite<-hlen_data.
  rewrite PeanoNat.Nat.eqb_refl. simpl. rewrite firstn_fill_length.
  rewrite PeanoNat.Nat.eqb_refl. simpl.
  unfold lift_comparison. unfold is_lt. unfold comparison_beq.
  destruct_match; auto.
  - rewrite N.compare_eq_iff in Heqc. rewrite<-Heqc.
    split; propositional; try discriminate.  lia.
  - rewrite N.compare_lt_iff in *. split; auto; lia.
  - rewrite N.compare_gt_iff in *. split; auto; try lia. discriminate.
Qed.
Lemma plus_success:
  forall v1 v2,
  Datatypes.length v1 = Datatypes.length v2 ->
  exists v, (plus v1 v2) =  Success v.
Proof.
  consider plus. intros. rewrite H. rewrite PeanoNat.Nat.eqb_refl. eauto.
Qed.
Lemma plus_success':
  forall v1 v2 default v,
  Datatypes.length v1 = Datatypes.length v2 ->
  success_or_default (plus v1 v2) default = v ->
  plus v1 v2 = Success v.
Proof.
  intros. consider @success_or_default. apply plus_success in H. propositional. simpl_match. auto.
Qed.
Lemma or_zeroes:
  forall v,
  or v (zeroes (Datatypes.length v)) = Success v.
Proof.
  unfold or. induction v; auto.
  simpl. setoid_rewrite IHv. rewrite orb_false_r. auto.
Qed.
Lemma plus_length_r:
  forall x1 x2 v,
  plus x1 x2 = Success v ->
  Datatypes.length v = Datatypes.length x2.
Proof.
  consider plus. intros. bash_destruct H. simplify.
  rewrite firstn_fill_length. auto.
Qed.
    Lemma to_N_zeroes {sz} :
      to_N (zeroes sz) = 0%N.
    Proof. induction sz; consider zeroes; simpl; try rewrite IHsz; auto. Qed.
    Lemma of_N_double sz n:
      of_N_sz (S sz) (N.double n) = cons false (of_N_sz sz n).
    Proof. destruct n; reflexivity. Qed.
    Lemma of_N_succ_double sz n:
      of_N_sz (S sz) (N.succ_double n) = cons true (of_N_sz sz n).
    Proof. destruct n; reflexivity. Qed.
    Lemma to_N_cons hd tl:
      to_N (cons hd tl) = ((if hd then 1 else 0) + 2 * to_N tl)%N.
    Proof. reflexivity. Qed.
    Lemma N_double_div_2 n :
      (N.double n / 2 = n)%N.
    Proof.
      replace (N.double n) with (N.b2n false + 2 * n)%N by reflexivity.
      apply N.add_b2n_double_div2.
    Qed.
    Lemma N_succ_double_div_2 n :
      (N.succ_double n / 2 = n)%N.
    Proof.
      replace (N.succ_double n) with (N.b2n true + 2 * n)%N
        by (simpl N.b2n; rewrite N.succ_double_spec; lia).
      apply N.add_b2n_double_div2.
    Qed.


    Lemma to_N_of_N_mod :
      forall n sz,
        to_N (of_N_sz sz n) = (n mod 2 ^ N.of_nat sz)%N.
    Proof.
      (* consider of_N_sz. *)
      induction n using N.binary_ind.
      1: solve [simpl; intros; apply to_N_zeroes].
      all: destruct sz; [ rewrite N.mod_1_r; reflexivity | ].
      all: rewrite ?of_N_double, ?of_N_succ_double, ?to_N_cons, ?IHn.
      all: rewrite ?Nat2N.inj_succ, ?N.pow_succ_r'.
      all: set (N.of_nat sz) as nz.
      all: pose proof N.pow_nonzero 2 nz ltac:(lia).
      all: rewrite !N.mod_eq, <- !N.div_div, ?N_double_div_2, ?N_succ_double_div_2 by lia.
      all: rewrite ?(N.double_spec n), ?(N.succ_double_spec n).
      - lia.
      - pose proof N.mul_div_le n (2 ^ nz).
        rewrite N.mul_sub_distr_l, N.add_sub_assoc; lia.
    Qed.
Lemma length_of_N_sz:
  forall n v,
  Datatypes.length (of_N_sz n v) = n.
Proof.
  consider of_N_sz. intros. rewrite firstn_fill_length. auto.
Qed.
Lemma length_one:
  forall sz,
  Datatypes.length (one sz) = sz.
Proof.
  unfold one. intros. rewrite firstn_fill_length. reflexivity.
Qed.
Lemma to_N_inj :
  forall sz bs1 bs2,
    sz = Datatypes.length bs1 ->
    sz = Datatypes.length bs2 ->
    to_N bs1 = to_N bs2 ->
    bs1 = bs2.
Proof.
  induction sz; destruct bs1, bs2; simpl; subst; intros; try lia.
  - reflexivity.
  - destruct b, b0, (to_N bs1) eqn:?, (to_N bs2) eqn:?; cbn in *;
      discriminate || (rewrite (IHsz bs1 bs2) by congruence; reflexivity).
Qed.


Lemma exists_of_N_sz:
  forall v,
  (to_N v < 2 ^ N.of_nat (Datatypes.length v))%N ->
  v = of_N_sz (Datatypes.length v) (to_N v).
Proof.
  intros.  eapply to_N_inj; eauto; try rewrite length_of_N_sz; [reflexivity | ].
  rewrite to_N_of_N_mod. rewrite N.mod_small;auto.
Qed.

 Lemma success_or_default_plus:
  forall x x' y,
  Datatypes.length x = Datatypes.length y ->
  Datatypes.length x' = Datatypes.length y ->
  success_or_default (plus x y) [] = success_or_default (plus x' y) []  ->
  x = x'.
Proof.
  intros * hlen_x hlen_x' hplus.
  specialize plus_success with (v1 := x) (v2 := y). propositional. rewrite H0 in *.
  specialize plus_success with (v1 := x') (v2 := y). propositional. rewrite H1 in *.  simpl in hplus. subst.
  consider plus. simplify.
  fold (of_N_sz (Datatypes.length x) (to_N x + to_N y)) in H1.
  fold (of_N_sz (Datatypes.length x') (to_N x' + to_N y)) in H1.
  apply f_equal with (f := to_N) in H1.
  repeat rewrite to_N_of_N_mod in H1.
  rewrite (exists_of_N_sz x) in H1.
  rewrite (exists_of_N_sz x') in H1.
  rewrite (exists_of_N_sz y) in H1.
  all: try eapply to_N_bounded.
  repeat rewrite to_N_of_N_mod in H1.
  repeat rewrite length_of_N_sz in H1.
  rewrite hlen_x in *. rewrite hlen_x' in *. set (N.of_nat (Datatypes.length y)) in *.
  assert (((to_N x mod 2 ^ n + to_N y mod 2 ^ n + ((2 ^ n - to_N y) mod 2 ^ n)) mod 2 ^ n)%N
          = (((to_N x' mod 2 ^ n + to_N y mod 2 ^ n+ ((2 ^ n - to_N y) mod 2 ^ n))) mod 2 ^ n)%N).
  { rewrite<-N.Div0.add_mod_idemp_l. rewrite H1.
    rewrite N.Div0.add_mod_idemp_l.  reflexivity.
  }
  assert (to_N y < 2^n)%N by (eapply to_N_bounded).
  rewrite<-N.add_assoc in H.
  rewrite<-N.add_assoc in H.
  rewrite<-N.Div0.add_mod_idemp_r in H.
  rewrite<-N.Div0.add_mod_idemp_r with (a :=  (to_N x' mod 2^n)%N) in H.
  replace (((to_N y mod 2 ^ n + (2 ^ n - to_N y) mod 2 ^ n) mod 2^ n)%N) with (0 mod 2 ^ n)%N in H.
  { repeat rewrite N.Div0.mod_0_l in *. repeat rewrite N.add_0_r in *.
    rewrite N.mod_mod in H by lia.
    rewrite N.mod_mod in H by lia.
    rewrite N.mod_small in H.
    2: { unfold n. rewrite<-hlen_x. eapply to_N_bounded. }
    rewrite N.mod_small in H.
    2: { unfold n. rewrite<-hlen_x'. eapply to_N_bounded. }
    eapply to_N_inj; eauto. rewrite_solve.
  }
  { rewrite N.Div0.mod_0_l.
    rewrite N.Div0.add_mod_idemp_l.
    rewrite N.Div0.add_mod_idemp_r.
    rewrite N.add_sub_assoc by lia.
    rewrite N.add_comm. rewrite<-N.add_sub_assoc by lia.
    rewrite N.sub_diag. rewrite N.add_0_r.
    rewrite N.Div0.mod_same. reflexivity.
  }
Qed.
Lemma of_N_sz_eq:
  forall sz v x,
  (v < 2 ^ N.of_nat sz)%N ->
  of_N_sz sz v = x ->
  v = to_N x.
Proof.
  intros. subst. rewrite to_N_of_N_mod.
  rewrite N.mod_small;auto.
Qed.
Lemma to_N_of_N_sz_idem:
  forall sz v,
  (v < 2 ^ (N.of_nat sz))%N ->
  to_N (of_N_sz sz v) = v.
Proof.
  intros. rewrite to_N_of_N_mod.
  rewrite N.mod_small; auto.
Qed.
