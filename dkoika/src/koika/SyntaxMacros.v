Require Import koika.Common.
Require Export koika.Syntax.
Require Import koika.Bits.
Require Import Coq.NArith.BinNat.


Section Macros.
  Context {id_ty: Type}.
  Context {EqDec_id_ty: EqDec id_ty}.

  Notation action := (@action id_ty).
  Notation dstruct_field_t := (@dstruct_field_t id_ty).
  Notation struct_t := (@struct_t id_ty).
  Notation dstruct_name_t := (@dstruct_name_t id_ty).


  (* Definition mk_action (a': action') : action := *)
  (*   Action a' []. *)
  Definition action_init (sz: nat) : action :=
    (Const (Bits.zeroes sz)) .

  Definition struct_sz' (st: list (dstruct_field_t * nat)) : nat :=
    list_sum (List.map snd st).

  Definition struct_sz (st: struct_t) : nat :=
    struct_sz' st.(dstruct_fields).

  Definition action_struct_init (dstruct_name: dstruct_name_t) (fields: list (dstruct_field_t * action)) : action :=
    let empty := (Zop (StructInit dstruct_name)) in
    let asubst f := fun x y => (Binop (Struct2 (SubstField dstruct_name f)) x y) in
    List.fold_left (fun acc '(f,a) => (asubst f) acc a) fields empty.

  Definition element_offset (s: list (dstruct_field_t * nat)) (field: dstruct_field_t) : result nat unit :=
    match find_with_index (fun '(f, _) => beq_dec field f) s with
    | Some (i, _) => Success (list_sum (map snd (List.firstn i s)))
    | None => Failure (__debug__ ("element_offset/not found", field) tt)
    end.

  Definition get_field_width (s: list (dstruct_field_t * nat)) (field: dstruct_field_t) : result nat unit :=
    match find (fun '(f, _) => beq_dec field f) s with
    | Some (_, width) => Success width
    | None => Failure (__debug__ ("get_field_width/not found", field) tt)
    end.

  Section Switches.
    Inductive switch_style :=
    | OrTreeSwitch (nbits: nat)
    | SequentialSwitchTt.

    Open Scope bits.

    Fixpoint ortree (sz: nat) (bodies: list bool -> action) : action :=
      match sz return (list bool -> action) -> action with
      | 0 => fun bodies => bodies Ob
      | S n =>
          fun bodies =>
          (Binop (Bits2 Or) (ortree n (fun bs => bodies bs~1))
                            (ortree n (fun bs => bodies bs~0)))
      end bodies.

    Definition gen_branches label_sz (branch_bodies: nat -> action) : list (action * action) :=
      let label_of_nat idx := (Const (Bits.of_nat label_sz idx)) in
      map (fun idx => (label_of_nat idx, branch_bodies idx))
          (seq 0 (pow2 label_sz)).

    Fixpoint switch_stateful (v: action) (branches: list (action * action)) : action :=
      match branches with
      | [] => (Const [])
      | b::bs => let (label,action) := b in
               (Seq ((If ((Binop (Bits2 (EqBits false)) v label))
                       action ((Const []))))
                   (switch_stateful v bs))
      end.

    Fixpoint switch (var: action) (default: action) (branches: list (action * action)) : action :=
      match branches with
      | nil => default
      | (label, action)::branches =>
          (If ((Binop (Bits2 (EqBits false)) var label)) action (switch var default branches))
      end.

    Definition CompleteOrTree (sz: nat) (nbits: nat) (v:var_t) (branch_bodies: vect_t -> action) : action :=
      ortree sz (fun bs => (If ((Binop (Bits2 (EqBits false)) ((Const bs)) ((Var v))))
                           (branch_bodies bs)
                           ((Const (Bits.zeroes nbits))))).

    Definition CompleteSwitch
        (style: switch_style) (sz: nat) (v: var_t)
        (branch_bodies: nat -> action) :=
      let branches bodies :=
        gen_branches sz bodies in
      match style with
      | OrTreeSwitch nbits =>
          CompleteOrTree sz nbits v (fun bs => branch_bodies (Bits.to_nat bs))
      | SequentialSwitchTt =>
          switch_stateful ((Var v)) (branches branch_bodies)
      end.

    (* Eval compute in (CompleteSwitch (OrTreeSwitch 32) (5) "idx" (fun n => Const (Bits.of_nat 32 n))). *)
    (* Eval compute in (CompleteSwitch (SequentialSwitchTt) (5) "idx" (fun n => Const (Bits.of_nat 32 n))). *)

  End Switches.
End Macros.
