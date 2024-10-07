Require Import Koika.Syntax.
Require Import Koika.SyntaxMacros.
Require Import Koika.Common.
Require Import Koika.Environments.
Require Koika.Parsing.
Require Import Coq.Strings.String.
Open Scope string_scope.

Definition lookup_var_type {A} (var_types: var_types_t) (var: var_t) (msg: A) : result nat A :=
  varenv_lookup_var var_types var msg.

Definition lookup_reg_type {A} (reg_types: reg_types_t) (reg: reg_t) (msg: A) : result nat A :=
  match reg_types reg with
  | Some t => Success t
  | None => Failure msg
  end.

Definition lookup_ext_fn_type {A} (ext_fn_types: ext_fn_types_t) (ext_fn: ext_fn_t) (msg: A)
                              : result (nat * nat) A :=
  match ext_fn_types ext_fn with
  | Some t => Success t
  | None => Failure msg
  end.


Definition GenericGammaTEmpty : var_types_t := [].

Section Typecheck.

  Section Action.
    Context (reg_types : reg_types_t).
    Context (ext_fn_types : ext_fn_types_t).
    Context (int_fns: int_fn_env_t).
    Context (struct_env: struct_env_t).

    Definition typechecking_error_t : Type := string * action * var_types_t.

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
      end.

    Definition typecheck_struct1 (fn: struct1) (arg_ty: nat) : result nat unit :=
      match fn with
      | GetField name f =>
          let/res s := lookup_struct struct_env name
                                     (__debug__ ("typecheck_struct1/GetField/struct not found", name) tt) in
          let/res width := get_field_width s.(struct_fields) f in
          if Nat.eqb arg_ty (struct_sz s) then
            Success width
          else Failure (__debug__ ("typecheck_struct1/GetField/Invalid arg size", name, arg_ty) tt)
      end.

    Definition typecheck_fn1 (fn: fn1) (arg_ty: nat) : result nat unit :=
      match fn with
      | Bits1 fn => typecheck_bits1 fn arg_ty
      | Struct1 fn => typecheck_struct1 fn arg_ty
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
      end.

    Definition typecheck_struct2 (fn: struct2) (arg_ty1 arg_ty2: nat) : result nat unit :=
      match fn with
      | SubstField sname fname =>
         let/res s := lookup_struct struct_env sname
                                   (__debug__ ("typecheck_struct2/SubstField/struct not found", sname) tt) in
         let/res width := get_field_width s.(struct_fields) fname in
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


    Fixpoint typecheck' (max_fn_id: nat) (var_types: var_types_t) (a: action) : result nat unit :=
      let failure_msg (msg: string) : unit
          := __debug__ (msg, a, var_types) tt in
      let typecheck' := typecheck' max_fn_id in
      match a with
      | Fail ty_hint => Success ty_hint
      | Var var => lookup_var_type var_types var (failure_msg ("Var untyped: " ++ var))
      | Const cst => Success (List.length cst)
      | Assign var ex =>
        let/res var_type :=
           lookup_var_type var_types var (failure_msg ("Var untyped: " ++ var)) in
        let/res ex_type :=
           typecheck' var_types ex in
        if Nat.eqb var_type ex_type then
          Success 0
        else Failure (failure_msg (__debug__ (var_type, ex_type) "Assign/Types do not match" ))
      | Seq a1 a2 =>
        let/res ty1 := typecheck' var_types a1 in
        typecheck' var_types a2
      | If cond tbranch fbranch =>
        let/res ty_cond := typecheck' var_types cond in
        let/res ty_tbranch := typecheck' var_types tbranch in
        let/res ty_fbranch := typecheck' var_types fbranch in
        if Nat.eqb ty_cond 1 then
          if Nat.eqb ty_tbranch ty_fbranch then
            Success ty_tbranch
          else Failure (failure_msg (__debug__ (ty_tbranch, ty_fbranch) "If/Types do not match"))
        else Failure (failure_msg (__debug__ ty_cond "If/Cond type not 1"))
      | Bind v ex body =>
        let/res ty_ex := typecheck' var_types ex in
        let var_types' := varenv_bind var_types v ty_ex in
        typecheck' var_types' body
      | Read p idx =>
        lookup_reg_type reg_types idx (failure_msg (__debug__ idx "Read/reg not found"))
      | Write p idx value =>
        let/res idx_ty := lookup_reg_type reg_types idx
                                          (failure_msg (__debug__ idx "Write/reg not found")) in
        let/res value_ty := typecheck' var_types value in
        if Nat.eqb idx_ty value_ty then
          Success 0
        else
          Failure (failure_msg (__debug__ (idx_ty, value_ty) "Write/Types do not match"))
      | Zop fn0 =>
        typecheck_fn0 fn0
      | Unop fn1 arg1 =>
        let/res ty1 := typecheck' var_types arg1 in
        typecheck_fn1 fn1 ty1
      | Binop fn2 arg1 arg2 =>
        let/res ty1 := typecheck' var_types arg1 in
        let/res ty2 := typecheck' var_types arg2 in
        typecheck_fn2 fn2 ty1 ty2
      | ExternalCall fn arg =>
        let/res arg_ty := typecheck' var_types arg in
        let/res2 expected_arg_ty, res_ty :=
           lookup_ext_fn_type ext_fn_types fn (failure_msg (__debug__ fn "Ext fn not found")) in
        if Nat.eqb arg_ty expected_arg_ty
        then Success res_ty
        else Failure (failure_msg (__debug__ (fn, arg_ty, expected_arg_ty) "Ext fn: wrong arg type"))
      | InternalCall fn arg =>
        let/res arg_ty := typecheck' var_types arg in
        let/res2 fn_id, fn_spec :=
           lookup_int_fn int_fns fn (failure_msg (__debug__ fn "Int fn not found")) in
        if Nat.ltb fn_id max_fn_id then
          if Nat.eqb arg_ty fn_spec.(fn_arg_ty)
          then Success fn_spec.(fn_ret_ty)
          else Failure (failure_msg (__debug__ (fn, arg_ty, fn_spec) "Int fn: wrong arg type"))
        else Failure (failure_msg (__debug__ (fn, fn_id, fn_spec.(fn_name)) "Int fn: int call too large"))
      end.

    Definition typecheck_action (var_types: var_types_t) (a: action) : result nat unit :=
      typecheck' (List.length int_fns) var_types a.

    Definition typecheck_rule (a: action) : result nat unit :=
      typecheck' (List.length int_fns) empty_var_t a.

    Fixpoint typecheck_schedule
             {rule_name_t: Type}
             (s: scheduler) (rls: rule_name_t -> action) : result unit unit :=
      match s with
      | Done => Success tt
      | Cons r0 s =>
          match typecheck_rule (rls r0) with
          | Success 0 => typecheck_schedule s rls
          | Success n => Failure (__debug__ (n, r0, "typecheck_schedule: rl not type 0") tt)
          | Failure s => Failure s
          end
      end.

  End Action.

  Section TypecheckFns.
    Definition typecheck_int_fns (int_fns: int_fn_env_t) : result unit unit :=
      let fns := mapi (fun i v => (i,v)) int_fns in
      let/res _ := result_list_map
                     (fun '(i,fn) =>
                        match typecheck' fn.(fn_reg_tys) fn.(fn_ext_fn_tys)
                                         int_fns fn.(fn_struct_defs)
                                         i (fn_var_types fn.(fn_arg_name) fn.(fn_arg_ty))
                                         fn.(fn_body) with
                        | Success n => if Nat.eqb n fn.(fn_ret_ty) then
                                        Success n
                                      else Failure (__debug__ ("Invalid return type", fn.(fn_ret_ty), n) tt)
                        | Failure f => Failure f
                        end
                     ) fns in
      Success tt.

    Definition typecheck_int_fns'
               (reg_types: reg_types_t) (ext_fn_types: ext_fn_types_t)
               (int_fns: int_fn_env_t) (struct_defs: struct_env_t) : result unit unit :=
      let fns := mapi (fun i v => (i,v)) int_fns in
      let/res _ := result_list_map
                     (fun '(i,fn) =>
                        match typecheck' reg_types ext_fn_types
                                         int_fns struct_defs i
                                         (fn_var_types fn.(fn_arg_name) fn.(fn_arg_ty))
                                         fn.(fn_body) with
                        | Success n => if Nat.eqb n fn.(fn_ret_ty) then
                                        Success n
                                      else Failure (__debug__ ("Invalid return type", fn.(fn_ret_ty), n) tt)
                        | Failure f => Failure f
                        end) fns in
      Success tt.

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
  Import Koika.Parsing.
  Import Koika.Parsing.Tests.

  Definition test_reg_types : reg_types_t :=
    fun reg => Some reg.


  Notation typecheck := (typecheck_rule test_reg_types empty_ext_fn_t empty_int_fn_env empty_struct_env_t).
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
