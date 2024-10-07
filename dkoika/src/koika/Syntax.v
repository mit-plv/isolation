(*! Koika, without dependent types *)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.

Section Syntax.
  Context {id_ty: Type}.

  Inductive Port :=
  | P0
  | P1.

  Definition reg_t := id_ty.
  Definition var_t := string.
  Definition fn_name_t := id_ty.
  Definition ext_fn_t := id_ty.
  Definition dstruct_name_t := id_ty.
  Definition dstruct_field_t := id_ty.

  Record struct_t :=
    { dstruct_name: dstruct_name_t;
      dstruct_fields: list (dstruct_field_t * nat)
    }.


  Inductive bits1 :=
  | Not
  | Slice (offset: nat) (width: nat)
  | SExt (width: nat)
  | ZExtL (width: nat)
  .

  Inductive struct1 :=
  | GetField (name: dstruct_name_t) (f: dstruct_field_t).

  Inductive bits_comparison :=
  | cLt | cGt | cLe | cGe.

  Inductive bits2 :=
  | And
  | Or
  | Xor
  | Lsl
  | Lsr
  | Asr
  | Concat
  | Sel
  | Plus
  | Minus
  | EqBits (negate: bool)
  | Compare (signed: bool) (c : bits_comparison)
  | IndexedSlice (width: nat)
  .

  Inductive fn0 :=
  | StructInit (sname: dstruct_name_t).

  Inductive fn1 :=
  | Bits1 (fn: bits1)
  | Struct1 (fn: struct1)
  | Ignore
  .

  Inductive struct2 :=
  | SubstField (sname: dstruct_name_t) (fname: dstruct_field_t).

  Inductive fn2 :=
  | Bits2 (fn: bits2)
  | Struct2 (fn: struct2)
  .

  Inductive action :=
  | Fail (ty_hint: nat)
  | Var (var: var_t)
  | Const (cst: list bool)
  | Assign (var: var_t) (ex: action)
  | Seq (a1 a2: action)
  | If (cond: action) (tbranch: action) (fbranch: action)
  | Bind (v: string) (ex: action) (body: action)
  | Read (port: Port) (idx: reg_t)
  | Write (port: Port) (idx: reg_t) (value: action)
  | Zop (fn: fn0)
  | Unop (fn: fn1) (arg1: action)
  | Binop (fn: fn2) (arg1: action) (arg2: action)
  | InternalCall (fn: fn_name_t) (arg: action)
  | ExternalCall (fn: ext_fn_t) (arg: action).

  Definition rule := action.

  Section Scheduler.
    Context {rule_name_t: Type}.

    Inductive scheduler :=
    | Done
    | Cons (r: rule_name_t) (s: scheduler)
    .

    Fixpoint schedule_app (sched1 sched2: scheduler) : scheduler :=
      match sched1 with
      | Done => sched2
      | Cons r s => Cons r (schedule_app s sched2)
      end.

  End Scheduler.
End Syntax.
Notation "r '|>' s" :=
  (Cons r s)
    (at level 99, s at level 99, right associativity).
Notation "'done'" :=
  Done (at level 99).
