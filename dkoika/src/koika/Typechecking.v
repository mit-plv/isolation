(* Require Import koika.Syntax.  *)
Require Import koika.SyntaxMacros.
Require Import koika.Common.
Require Import koika.Environments.
Require koika.Parsing.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import koika.AnnotatedSyntax.

Section Typecheck.

  Section Action.
    Context {id_ty: Type}.
    Context {EqDec_id_ty: EqDec id_ty}.

    Context (reg_types : @reg_types_t id_ty).
    Context (ext_fn_types : @ext_fn_types_t id_ty).
    Context (int_fns: @int_fn_env_t id_ty (@action id_ty)).
    Context (struct_env: @struct_env_t id_ty).

    Definition lookup_var_type {A} (var_types: var_types_t) (var: var_t) (msg: A) : result nat A :=
      varenv_lookup_var var_types var msg.
    Definition lookup_reg_type {A} (reg: @reg_t id_ty) (msg: A) : result nat A :=
      match Environments.lookup_reg_type reg_types reg with
      | Some t => Success t
      | None => Failure msg
      end.

    Definition lookup_ext_fn_type {A} (ext_fn_types: ext_fn_types_t) (ext_fn: ext_fn_t) (msg: A)
                                  : result (nat * nat) A :=
      match Environments.lookup_ext_fn ext_fn_types ext_fn with
      | Some t => Success t
      | None => Failure msg
      end.


    Definition GenericGammaTEmpty : var_types_t := [].


    Definition typechecking_error_t : Type := string * @action id_ty * var_types_t.

    Definition typecheck_fn0 (fn: fn0) : result nat unit :=
      match fn with
      | StructInit sname =>
          let/res s := lookup_struct struct_env sname
                                     (__debug__ ("typecheck_fn0/StructInit/struct not found", sname) tt) in
          Success (struct_sz s)
      end.

    Definition typecheck_bits1 (fn: bits1) (arg_ty: nat) : result nat unit :=
      match fn with
      | Not => Success arg_ty
      | Slice offset width => Success width
      | SExt width => Success (Nat.max arg_ty width)
      | ZExtL width => Success (Nat.max arg_ty width)
      end.

    (* Definition get_field_width (s: list (dstruct_field_t * nat)) (field: dstruct_field_t) : result nat unit := *)
    (*   match find (fun '(f, _) => beq_dec field f) s with *)
    (*   | Some (_, width) => Success width *)
    (*   | None => Failure (__debug__ ("get_field_width/not found", field) tt) *)
    (*   end. *)

    Definition typecheck_struct1 (fn: struct1) (arg_ty: nat) : result nat unit :=
      match fn with
      | GetField name f =>
          let/res s := lookup_struct struct_env name
                                     (__debug__ ("typecheck_struct1/GetField/struct not found", name) tt) in
          let/res width := get_field_width s.(dstruct_fields) f in
          if Nat.eqb arg_ty (struct_sz s) then
            Success width
          else Failure (__debug__ ("typecheck_struct1/GetField/Invalid arg size", name, arg_ty) tt)
      end.

    Definition typecheck_fn1 (fn: fn1) (arg_ty: nat) : result nat unit :=
      match fn with
      | Bits1 fn => typecheck_bits1 fn arg_ty
      | Struct1 fn => typecheck_struct1 fn arg_ty
      | Ignore => Success 0
      end.

    Definition typecheck_bits2 (fn: bits2) (arg_ty1 arg_ty2: nat) : result nat unit :=
      match fn with
      | And => if Nat.eqb arg_ty1 arg_ty2
              then Success arg_ty1
              else Failure (__debug__ ("typecheck_bits2/And: tys not equal", arg_ty1, arg_ty2) tt)
      | Or =>
        if Nat.eqb arg_ty1 arg_ty2
        then Success arg_ty1
        else Failure (__debug__ ("typecheck_bits2/Or: tys not equal", arg_ty1, arg_ty2) tt)
      | Xor =>
        if Nat.eqb arg_ty1 arg_ty2
        then Success arg_ty1
        else Failure (__debug__ ("typecheck_bits2/Xor: tys not equal", arg_ty1, arg_ty2) tt)
      | Lsl => Success arg_ty1
      | Lsr => Success arg_ty1
      | Asr => Success arg_ty1
      | Concat => Success (arg_ty1 + arg_ty2)
      | Sel =>
        if Nat.eqb (PeanoNat.Nat.log2_up arg_ty1) arg_ty2 && Nat.ltb 0 arg_ty1
        then Success 1
        else Failure (__debug__ ("typecheck_bits2/Sel", arg_ty1, arg_ty2) tt)
      | Plus =>
        if Nat.eqb arg_ty1 arg_ty2
        then Success arg_ty1
        else Failure (__debug__ ("typecheck_bits2/Plus: tys not equal", arg_ty1, arg_ty2) tt)
      | Minus =>
        if Nat.eqb arg_ty1 arg_ty2
        then Success arg_ty1
        else Failure (__debug__ ("typecheck_bits2/Minus: tys not equal", arg_ty1, arg_ty2) tt)
      | EqBits n =>
        if Nat.eqb arg_ty1 arg_ty2
        then Success 1
        else Failure (__debug__ ("typecheck_bits2/EqBits: tys not equal", arg_ty1, arg_ty2) tt)
      | Compare signed c =>
        if Nat.eqb arg_ty1 arg_ty2
        then Success 1
        else Failure (__debug__ ("typecheck_bits2/Compare: tys not equal", arg_ty1, arg_ty2) tt)
      | IndexedSlice width =>
        if Nat.eqb (PeanoNat.Nat.log2_up arg_ty1) arg_ty2
        then Success width
        else Failure (__debug__ ("typecheck_bits2/IndexedSlice", arg_ty1, arg_ty2) tt)
      end.

    Definition typecheck_struct2 (fn: struct2) (arg_ty1 arg_ty2: nat) : result nat unit :=
      match fn with
      | SubstField sname fname =>
         let/res s := lookup_struct struct_env sname
                                   (__debug__ ("typecheck_struct2/SubstField/struct not found", sname) tt) in
         let/res width := get_field_width s.(dstruct_fields) fname in
         if Nat.eqb arg_ty1 (struct_sz s) then
           if Nat.eqb arg_ty2 width then
             Success (struct_sz s)
           else Failure (__debug__ ("typecheck_struct2/SubstField/invalid argty2", arg_ty2) tt)
         else
           Failure (__debug__ ("typecheck_struct2/SubstField/invalid argty1", arg_ty1) tt)
      end.

    Definition typecheck_fn2 (fn: fn2) (arg_ty1 arg_ty2: nat) : result nat unit :=
      match fn with
      | Bits2 fn => typecheck_bits2 fn arg_ty1 arg_ty2
      | Struct2 fn => typecheck_struct2 fn arg_ty1 arg_ty2
      end.

    Fixpoint typecheck' (max_fn_id: nat) (var_types: var_types_t) (a: @action id_ty)
      : result (@aaction id_ty * nat) unit :=
      let failure_msg (msg: string) : unit
          := __debug__ (msg, a, var_types) tt in
      let typecheck' := typecheck' max_fn_id in
      let/res2 a, sz :=
        match a with
        | Syntax.Fail ty_hint => Success (Fail ty_hint, ty_hint)
        | Syntax.Var var =>
          let/res sz := lookup_var_type var_types var (failure_msg ("Var untyped: " ++ var)) in
          Success (Var var, sz)
        | Syntax.Const cst => Success (Const cst, List.length cst)
        | Syntax.Assign var ex =>
          let/res var_type :=
             lookup_var_type var_types var (failure_msg ("Var untyped: " ++ var)) in
          let/res2 ex, ex_type := typecheck' var_types ex in
          if Nat.eqb var_type ex_type then
            Success (Assign var ex, 0)
          else Failure (failure_msg (__debug__ (var_type, ex_type) "Assign/Types do not match" ))
        | Syntax.Seq a1 a2 =>
          let/res2 a1, ty1 := typecheck' var_types a1 in
          if Nat.eqb ty1 0 then
            let/res2 a2, ty2 := typecheck' var_types a2 in
            Success ((Seq a1 a2), ty2)
          else Failure (failure_msg (__debug__ ty1 "Seq1/Type not zero" ))
        | Syntax.If cond tbranch fbranch =>
          let/res2 cond, ty_cond := typecheck' var_types cond in
          let/res2 tbranch, ty_tbranch := typecheck' var_types tbranch in
          let/res2 fbranch, ty_fbranch := typecheck' var_types fbranch in
          if Nat.eqb ty_cond 1 then
            if Nat.eqb ty_tbranch ty_fbranch then
              Success (If cond tbranch fbranch, ty_tbranch)
            else Failure (failure_msg (__debug__ (ty_tbranch, ty_fbranch) "If/Types do not match"))
          else Failure (failure_msg (__debug__ ty_cond "If/Cond type not 1"))
        | Syntax.Bind v ex body =>
          let/res2 ex, ty_ex := typecheck' var_types ex in
          let var_types' := varenv_bind var_types v ty_ex in
          let/res2 body, ty_body := typecheck' var_types' body in
          Success (Bind v ex body, ty_body)
        | Syntax.Read p idx =>
          let/res sz := lookup_reg_type idx (failure_msg (__debug__ idx "Read/reg not found")) in
          Success (Read p idx, sz)
        | Syntax.Write p idx value =>
          let/res idx_ty := lookup_reg_type idx
                                            (failure_msg (__debug__ idx "Write/reg not found")) in
          let/res2 value, value_ty := typecheck' var_types value in
          if Nat.eqb idx_ty value_ty then
            Success (Write p idx value, 0)
          else
            Failure (failure_msg (__debug__ (idx_ty, value_ty) "Write/Types do not match"))
        | Syntax.Zop fn0 =>
          let/res sz := typecheck_fn0 fn0 in
          Success (Zop fn0, sz)
        | Syntax.Unop fn1 arg1 =>
          let/res2 arg1, ty1 := typecheck' var_types arg1 in
          let/res sz := typecheck_fn1 fn1 ty1 in
          Success (Unop fn1 arg1, sz)
        | Syntax.Binop fn2 arg1 arg2 =>
          let/res2 arg1, ty1 := typecheck' var_types arg1 in
          let/res2 arg2, ty2 := typecheck' var_types arg2 in
          let/res sz := typecheck_fn2 fn2 ty1 ty2 in
          Success (Binop fn2 arg1 arg2, sz)
        | Syntax.ExternalCall fn arg =>
          let/res2 arg, arg_ty := typecheck' var_types arg in
          let/res2 expected_arg_ty, res_ty :=
             lookup_ext_fn_type ext_fn_types fn (failure_msg (__debug__ fn "Ext fn not found")) in
          if Nat.eqb arg_ty expected_arg_ty
          then Success (ExternalCall fn arg, res_ty)
          else Failure (failure_msg (__debug__ (fn, arg_ty, expected_arg_ty) "Ext fn: wrong arg type"))
        | Syntax.InternalCall fn arg =>
          let/res2 arg, arg_ty := typecheck' var_types arg in
          let/res2 fn_id, fn_spec :=
             lookup_int_fn int_fns fn (failure_msg (__debug__ fn "Int fn not found")) in
          if Nat.ltb fn_id max_fn_id then
            if Nat.eqb arg_ty fn_spec.(fn_arg_ty)
            then Success (InternalCall fn arg, fn_spec.(fn_ret_ty))
            else Failure (failure_msg (__debug__ (fn, arg_ty, fn_spec) "Int fn: wrong arg type"))
          else Failure (failure_msg (__debug__ (fn, fn_id, fn_spec.(fn_name)) "Int fn: int call too large"))
        end in
      Success (AnnotAction a [Annot_ty sz], sz).

    Definition typecheck_action (var_types: var_types_t) (a: action) : result (aaction * nat) unit :=
      typecheck' (List.length int_fns) var_types a.

    Definition typecheck_rule (a: action) : result (aaction * nat) unit :=
      typecheck' (List.length int_fns) empty_var_t a.

    Fixpoint typecheck_schedule
             {rule_name_t: Type}
             (s: scheduler) (rls: rule_name_t -> action) : result unit unit :=
      match s with
      | Done => Success tt
      | Cons r0 s =>
          match typecheck_rule (rls r0) with
          | Success (_, 0) => typecheck_schedule s rls
          | Success (_, n) => Failure (__debug__ (n, r0, "typecheck_schedule: rl not type 0") tt)
          | Failure s => Failure s
          end
      end.

  End Action.

  Section TypecheckFns.
    Context {id_ty: Type}.
    Context {EqDec_id_ty: EqDec id_ty}.

    Definition typecheck_int_fns (int_fns: @int_fn_env_t id_ty (@action id_ty)) : result int_fn_env_t unit :=
      let fns := mapi (fun i v => (i,v)) int_fns in
      result_list_map
                     (fun '(i,fn) =>
                        match typecheck' fn.(fn_reg_tys) fn.(fn_ext_fn_tys)
                                         int_fns fn.(fn_struct_defs)
                                         i (fn_var_types fn.(fn_arg_name) fn.(fn_arg_ty))
                                         fn.(fn_body) with
                        | Success (body, n) =>
                            if Nat.eqb n fn.(fn_ret_ty) then
                              Success {| fn_name := fn.(fn_name);
                                fn_reg_tys := fn.(fn_reg_tys);
                                fn_ext_fn_tys := fn.(fn_ext_fn_tys);
                                fn_struct_defs := fn.(fn_struct_defs);
                                fn_arg_ty := fn.(fn_arg_ty);
                                fn_arg_name := fn.(fn_arg_name);
                                fn_ret_ty := fn.(fn_ret_ty);
                                fn_body := body
                              |}
                            else Failure (__debug__ ("Invalid return type", fn.(fn_ret_ty), n) tt)
                        | Failure f => Failure f
                        end
                     ) fns.

    Definition typecheck_int_fns'
               (reg_types: @reg_types_t id_ty) (ext_fn_types: ext_fn_types_t)
               (int_fns: int_fn_env_t) (struct_defs: @struct_env_t id_ty)
      : result int_fn_env_t unit :=
      let fns := mapi (fun i v => (i,v)) int_fns in
      result_list_map
                     (fun '(i,fn) =>
                        match typecheck' reg_types ext_fn_types
                                         int_fns struct_defs i
                                         (fn_var_types fn.(fn_arg_name) fn.(fn_arg_ty))
                                         fn.(fn_body) with
                        | Success (body,n) =>
                            if Nat.eqb n fn.(fn_ret_ty) then
                              Success {| fn_name := fn.(fn_name);
                                fn_reg_tys := fn.(fn_reg_tys);
                                fn_ext_fn_tys := fn.(fn_ext_fn_tys);
                                fn_struct_defs := fn.(fn_struct_defs);
                                fn_arg_ty := fn.(fn_arg_ty);
                                fn_arg_name := fn.(fn_arg_name);
                                fn_ret_ty := fn.(fn_ret_ty);
                                fn_body := body
                              |}
                            else Failure (__debug__ ("Invalid return type", fn.(fn_ret_ty), n) tt)
                        | Failure f => Failure f
                        end) fns.

  End TypecheckFns.

  Definition typecheck_total_action
             (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t)
             (int_fns: int_fn_env_t) (struct_defs: struct_env_t)
             (action: action) : result unit unit :=
    let/res _ := typecheck_int_fns' reg_types ext_fn_types int_fns struct_defs in
    let/res _ := typecheck_rule reg_types ext_fn_types int_fns struct_defs action in
    Success tt.

End Typecheck.

Module Tests.
  Import koika.Parsing.
  Import koika.Parsing.Tests.
  Require Import koika.SyntaxUtils.
  Definition test_reg_types : reg_types_t :=
    [ (snd Reg0, 0); (snd Reg1, 1); (snd Reg2, 2); ( snd Reg3, 3)
    ].

  Definition typecheck (rule: action ) := (typecheck_rule test_reg_types empty_ext_fn_t empty_int_fn_env empty_struct_env_t (id_transform_action snd (rule))).
  Example test_fail__success: is_success (typecheck test_fail) = true := ltac:(auto).
  Example test_pass__success: is_success (typecheck test_pass) = true := ltac:(auto).
  Example test_const1__success: is_success (typecheck test_const1) = true := ltac:(auto).
  Example test_const0__success: is_success (typecheck test_const0) = true := ltac:(auto).
  Example test_let__success: is_success (typecheck test_let) = true := ltac:(auto).
  Example test_let2__success: is_success (typecheck test_let2) = true := ltac:(auto).
  Example test_seq__success: is_success (typecheck test_seq) = true := ltac:(auto).
  Example test_set__fail: is_success (typecheck test_set__fail) = false := ltac:(auto).
  Example test_read0__success: is_success (typecheck test_read0) = true:= ltac:(auto).
  Example test_read1__success: is_success (typecheck test_read1) = true:= ltac:(auto).
  Example test_write0__success: is_success (typecheck test_write0) = true:= ltac:(auto).
  Example test_write1__success: is_success (typecheck test_write1) = true:= ltac:(auto).
  Example test_write1__fail: is_success (typecheck test_write1__fail) = false := ltac:(auto).

End Tests.
