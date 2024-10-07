Require Import Koika.Common.
Require Import Koika.Syntax.
Require Import Koika.Bits.

Definition action_init (sz: nat) : action :=
  Const (Bits.zeroes sz).

Definition struct_sz' (st: list (struct_field_t * nat)) : nat :=
  list_sum (List.map snd st).

Definition struct_sz (st: struct_t) : nat :=
  struct_sz' st.(struct_fields).

Definition action_struct_init (struct_name: struct_name_t) (fields: list (struct_field_t * action)) : action :=
  let empty := Zop (StructInit struct_name) in
  let asubst f := Binop (Struct2 (SubstField struct_name f)) in
  List.fold_left (fun acc '(f,a) => (asubst f) acc a) fields empty.

Definition element_offset (s: list (struct_field_t * nat)) (field: struct_field_t) : result nat unit :=
  match find_with_index (fun '(f, _) => Nat.eqb field f) s with
  | Some (i, _) => Success (list_sum (map snd (List.firstn i s)))
  | None => Failure (__debug__ ("element_offset/not found", field) tt)
  end.

Definition get_field_width (s: list (struct_field_t * nat)) (field: struct_field_t) : result nat unit :=
  match find (fun '(f, _) => Nat.eqb field f) s with
  | Some (_, width) => Success width
  | None => Failure (__debug__ ("get_field_width/not found", field) tt)
  end.
