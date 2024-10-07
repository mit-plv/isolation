Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.


Inductive Port :=
| P0
| P1.

Definition reg_t := nat.
Definition var_t := string.
Definition fn_name_t := nat.
Definition ext_fn_t := nat.
Definition struct_name_t := nat.
Definition struct_field_t := nat.

Record struct_t :=
  { struct_name: struct_name_t;
    struct_fields: list (struct_field_t * nat)
  }.


Inductive bits1 :=
| Not
| Slice (offset: nat) (width: nat)
.

Inductive struct1 :=
| GetField (name: struct_name_t) (f: struct_field_t).

Inductive bits_comparison :=
| cLt | cGt | cLe | cGe.

Inductive bits2 :=
| And
| Or
| Xor
| Concat
| Sel
| Plus
| Minus
| EqBits (negate: bool)
| Compare (signed: bool) (c : bits_comparison)
.

Inductive fn0 :=
| StructInit (sname: struct_name_t).

Inductive fn1 :=
| Bits1 (fn: bits1)
| Struct1 (fn: struct1)
.

Inductive struct2 :=
| SubstField (sname: struct_name_t) (fname: struct_field_t).

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
| ExternalCall (fn: ext_fn_t) (arg: action)
.

Definition rule := action.

Section Scheduler.
  Context {rule_name_t: Type}.

  Inductive scheduler :=
  | Done
  | Cons (r: rule_name_t) (s: scheduler)
  .

End Scheduler.

Notation "r '|>' s" :=
  (Cons r s)
    (at level 99, s at level 99, right associativity).
Notation "'done'" :=
  Done (at level 99).
