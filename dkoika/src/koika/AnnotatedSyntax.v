Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.
Require Import koika.Syntax.

Inductive annot_t :=
| Annot_ty (sz: nat)
| Annot_id (id: nat).

Section Syntax.
  Context {id_ty: Type}.

  Notation reg_t := (@reg_t id_ty).
  Definition fn_name_t := (@fn_name_t id_ty).
  Definition ext_fn_t := (@ext_fn_t id_ty).
  Definition dstruct_name_t := (@dstruct_name_t id_ty).
  Definition dstruct_field_t := (@dstruct_field_t id_ty).

  Inductive aaction' :=
  | Fail (ty_hint: nat)
  | Var (var: var_t)
  | Const (cst: list bool)
  | Assign (var: var_t) (ex: aaction)
  | Seq (a1 a2: aaction)
  | If (cond: aaction) (tbranch: aaction) (fbranch: aaction)
  | Bind (v: string) (ex: aaction) (body: aaction)
  | Read (port: Port) (idx: reg_t)
  | Write (port: Port) (idx: reg_t) (value: aaction)
  | Zop (fn: @fn0 id_ty)
  | Unop (fn: @fn1 id_ty) (arg1: aaction)
  | Binop (fn: @fn2 id_ty) (arg1: aaction) (arg2: aaction)
  | InternalCall (fn: fn_name_t) (arg: aaction)
  | ExternalCall (fn: ext_fn_t) (arg: aaction)
  with aaction :=
       | AnnotAction (action: aaction') (annots: list annot_t).

  Fixpoint strip_annots (a: aaction) : @action id_ty :=
    match a with
    | AnnotAction a _ =>
        match a with
        | Fail ty => koika.Syntax.Fail ty
        | Var v => koika.Syntax.Var v
        | Const cst => koika.Syntax.Const cst
        | Assign var ex => koika.Syntax.Assign var (strip_annots ex)
        | Seq a1 a2 => koika.Syntax.Seq (strip_annots a1) (strip_annots a2)
        | If cond tbranch fbranch => koika.Syntax.If (strip_annots cond) (strip_annots tbranch) (strip_annots fbranch)
        | Bind v ex body => koika.Syntax.Bind v (strip_annots ex) (strip_annots body)
        | Read port idx => koika.Syntax.Read port idx
        | Write port idx value => koika.Syntax.Write port idx (strip_annots value)
        | Zop fn => koika.Syntax.Zop fn
        | Unop fn arg1 => koika.Syntax.Unop fn (strip_annots arg1)
        | Binop fn arg1 arg2 => koika.Syntax.Binop fn (strip_annots arg1) (strip_annots arg2)
        | InternalCall fn arg => koika.Syntax.InternalCall fn (strip_annots arg)
        | ExternalCall fn arg => koika.Syntax.ExternalCall fn (strip_annots arg)
        end
    end.
End Syntax.
