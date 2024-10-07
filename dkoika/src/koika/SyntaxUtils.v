Require Import koika.Common.
Require Import koika.Syntax.
Require Import koika.Environments.

Section Transform.
  Context {ty1 ty2: Type}.
  Context (id_f: ty1 -> ty2).

  Definition id_transform_reg_types: @reg_types_t ty1 -> @reg_types_t ty2 :=
    fun reg_tys => List.map (fun '(reg, ty) => (id_f reg, ty)) reg_tys.

  Definition id_transform_ext_fn_types: @ext_fn_types_t ty1 -> @ext_fn_types_t ty2 :=
    fun ext_fn_tys => List.map (fun '(ext_fn, ty) => (id_f ext_fn, ty)) ext_fn_tys.

  Definition id_transform_struct: @struct_t ty1 -> @struct_t ty2 :=
    fun s => {| dstruct_name := id_f s.(dstruct_name);
             dstruct_fields := List.map (fun '(name, ty) => (id_f name, ty)) s.(dstruct_fields)
          |}.

  Definition id_transform_struct_env: @struct_env_t ty1 -> @struct_env_t ty2 :=
    fun s => List.map id_transform_struct s.

  Definition id_transform_fn0: @fn0 ty1 -> @fn0 ty2 :=
    fun fn => match fn with
           | StructInit sname => StructInit (id_f sname)
           end.

  Definition id_transform_struct1: @struct1 ty1 -> @struct1 ty2 :=
    fun s => match s with
          | GetField name f => GetField (id_f name) (id_f f)
          end.

  Definition id_transform_fn1: @fn1 ty1 -> @fn1 ty2 :=
    fun fn => match fn with
           | Bits1 fn => Bits1 fn
           | Struct1 fn => Struct1 (id_transform_struct1 fn)
           | Ignore => Ignore
           end.
  Definition id_transform_struct2: @struct2 ty1 -> @struct2 ty2 :=
    fun s => match s with
          | SubstField name fname => SubstField (id_f name) (id_f fname)
          end.

  Definition id_transform_fn2: @fn2 ty1 -> @fn2 ty2 :=
    fun fn => match fn with
           | Bits2 fn => Bits2 fn
           | Struct2 fn => Struct2 (id_transform_struct2 fn)
           end.

  Fixpoint id_transform_action (a: @action ty1) : @action ty2 :=
    (* match a with *)
    (* | Action action annots => *)
    (*   Action *)
        (match a with
         | Fail ty => Fail ty
         | Var v => Var v
         | Const cst => Const cst
         | Assign var ex => Assign var (id_transform_action ex)
         | Seq a1 a2 => Seq (id_transform_action a1) (id_transform_action a2)
         | If cond tbranch fbranch =>
             If (id_transform_action cond) (id_transform_action tbranch) (id_transform_action fbranch)
         | Bind v ex body => Bind v (id_transform_action ex) (id_transform_action body)
         | Read p idx => Read p (id_f idx)
         | Write p idx value => Write p (id_f idx) (id_transform_action value)
         | Zop fn => Zop (id_transform_fn0 fn)
         | Unop fn arg1 => Unop (id_transform_fn1 fn) (id_transform_action arg1)
         | Binop fn arg1 arg2 => Binop (id_transform_fn2 fn) (id_transform_action arg1) (id_transform_action arg2)
         | InternalCall fn arg => InternalCall (id_f fn) (id_transform_action arg)
         | ExternalCall fn arg => ExternalCall (id_f fn) (id_transform_action arg)
         end) .

  Definition id_transform_int_fn_spec:
    @int_fn_spec_t ty1 (@action ty1) -> @int_fn_spec_t ty2 (@action ty2):=
    fun spec =>
      {| fn_name := id_f spec.(fn_name);
         fn_reg_tys := id_transform_reg_types spec.(fn_reg_tys);
         fn_ext_fn_tys := id_transform_ext_fn_types spec.(fn_ext_fn_tys);
         fn_struct_defs := id_transform_struct_env spec.(fn_struct_defs);
         fn_arg_ty := spec.(fn_arg_ty);
         fn_arg_name := spec.(fn_arg_name);
         fn_ret_ty := spec.(fn_ret_ty);
         fn_body := id_transform_action spec.(fn_body)|}.

  Definition id_transform_int_fn_env: @int_fn_env_t ty1 (@action ty1) -> @int_fn_env_t ty2 (@action ty2) :=
    fun env => List.map id_transform_int_fn_spec env.


End Transform.

(* Section ConvertAnnotate. *)
(*   Context {id_ty: Type}. *)
(*   Fixpoint convert_syntax (a: @action id_ty) : action := *)
(*     match a with *)
(*     | Action a annots => *)
(*         Action *)
(*           (match a with *)
(*            | koika.Syntax.Fail hint => Fail hint *)
(*            | koika.Syntax.Var var => Var var *)
(*            | koika.Syntax.Const cst => Const cst *)
(*            | koika.Syntax.Assign var ex => Assign var (convert_syntax ex) *)
(*            | koika.Syntax.Seq a1 a2 => Seq (convert_syntax a1) (convert_syntax a2) *)
(*            | koika.Syntax.If cond tbranch fbranch => *)
(*                If (convert_syntax cond) (convert_syntax tbranch) (convert_syntax fbranch ) *)
(*            | koika.Syntax.Bind v ex body => *)
(*                Bind v (convert_syntax ex) (convert_syntax body) *)
(*            | koika.Syntax.Read port reg => *)
(*                Read port reg *)
(*            | koika.Syntax.Write port reg value => Write port reg (convert_syntax value) *)
(*            | koika.Syntax.Zop fn => Zop fn *)
(*            | koika.Syntax.Unop fn arg1 => Unop fn (convert_syntax arg1) *)
(*            | koika.Syntax.Binop fn arg1 arg2 => Binop fn (convert_syntax arg1) (convert_syntax arg2) *)
(*            | koika.Syntax.InternalCall fn arg => InternalCall fn (convert_syntax arg) *)
(*            | koika.Syntax.ExternalCall fn arg => ExternalCall fn (convert_syntax arg) *)
(*            end *)
(*           ) annots *)
(*     end. *)

(*   Definition convert_int_fn_spec (spec: @int_fn_spec_t id_ty (@action id_ty)) *)
(*                                  : @int_fn_spec_t id_ty (@action id_ty) := *)
(*     {| fn_name := spec.(fn_name); *)
(*        fn_reg_tys := spec.(fn_reg_tys); *)
(*        fn_ext_fn_tys := spec.(fn_ext_fn_tys); *)
(*        fn_struct_defs := spec.(fn_struct_defs); *)
(*        fn_arg_ty := spec.(fn_arg_ty); *)
(*        fn_arg_name := spec.(fn_arg_name); *)
(*        fn_ret_ty := spec.(fn_ret_ty); *)
(*        fn_body := convert_syntax spec.(fn_body) *)
(*     |}. *)

(*   Definition convert_int_fn_env (env: @int_fn_env_t id_ty (@action id_ty)) *)
(*                                 : @int_fn_env_t id_ty (@action id_ty) := *)
(*     map convert_int_fn_spec env. *)

(* End ConvertAnnotate. *)
(* Compute action depth for well-formedness *)
Section Height.
  Context {id_ty: Type}.
  Context (int_fn_env: @int_fn_env_t id_ty (@action id_ty)).

  Fixpoint height (a: @action id_ty) : nat :=
      match a with
      | Fail _ => 1
      | Var _ => 1
      | Const _ => 1
      | Assign _ ex => S (height ex)
      | Seq a1 a2 => S (max (height a1) (height a2))
      | If cond tbranch fbranch => S (max (height cond) (max (height tbranch) (height fbranch)))
      | Bind _ ex body => S (max (height ex) (height body))
      | Read _ _ => 1
      | Write _ _ v => S (height v)
      | Zop _ => 1
      | Unop _ a => S (height a)
      | Binop _ a1 a2 => S (max (height a1) (height a2))
      | InternalCall _ arg => S (height arg)
      | ExternalCall _ a => S (height a)
    end.

  Definition max_fn_height : nat :=
    fold_left max (map (fun fn => height fn.(fn_body)) int_fn_env) 0.

  Definition safe_fuel (a: @action id_ty) : nat :=
    (max_fn_height * (List.length int_fn_env)) + (height a).

End Height.

Section Inline.
  Context {id_ty: Type}.
  Context {EqDec_id_ty: EqDec id_ty}.
  Context (int_fn_env: @int_fn_env_t id_ty (@action id_ty)).

  Fixpoint inline_action (fuel: nat) (a: @action id_ty) : @action id_ty :=
    match fuel with
    | S fuel =>
      let inline_action := inline_action fuel in
      (* match a with *)
      (* | Action a annots => *)
          (* let a := *)
            match a with
            | Fail ty => Fail ty
            | Var var => Var var
            | Const cst => Const cst
            | Assign var ex => Assign var (inline_action ex)
            | Seq a1 a2 => Seq (inline_action a1) (inline_action a2)
            | If cond tbranch fbranch =>
                If (inline_action cond) (inline_action tbranch) (inline_action fbranch)
            | Bind v ex body =>
                Bind v (inline_action ex) (inline_action body)
            | Read p idx => Read p idx
            | Write p idx value => Write p idx (inline_action value)
            | Zop fn => Zop fn
            | Unop fn arg1 => Unop fn (inline_action arg1)
            | Binop fn arg1 arg2 => Binop fn (inline_action arg1) (inline_action arg2)
            | InternalCall fn arg =>
                match lookup_int_fn int_fn_env fn tt  with
                | Success (_, spec) =>
                    Bind spec.(fn_arg_name) (inline_action arg)
                         (inline_action spec.(fn_body))
                | _ => InternalCall fn (inline_action arg)
                end
            | ExternalCall fn arg => ExternalCall fn (inline_action arg)
            end
    | 0 => a
    end.

  Definition inline_rule (a: @action id_ty) : @action id_ty :=
    inline_action (safe_fuel int_fn_env a) a.
End Inline.
