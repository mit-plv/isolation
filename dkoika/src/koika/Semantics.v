Require Import koika.Common.
Require Import koika.Syntax.
Require Import koika.SyntaxMacros.
Require Import koika.Environments.
Require Import koika.Typechecking.
Require Import koika.Bits.
Require Import Coq.Init.Nat.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import koika.SyntaxUtils.
Import List.ListNotations.

Section Utils.
  Context {id_ty: Type}.
  Context {EqDec_id_ty: EqDec id_ty}.

  Definition subst_field (fields: list (@dstruct_field_t id_ty * nat))
                         (fname: @dstruct_field_t id_ty) (arg1 arg2: list bool)
                         : result (list bool) unit :=
     let/res offset := element_offset fields fname in
     let/res width := get_field_width fields fname in
     if Nat.eqb (Datatypes.length arg1) (struct_sz' fields) then
       if Nat.eqb (Datatypes.length arg2) width then
         Success (Bits.slice_subst offset arg2 arg1)
       else Failure (__debug__ ("subst_field/invalid arg2", arg2) tt)
     else
       Failure (__debug__ ("subst_field/Invalid arg size", fname, arg1) tt).

  Definition struct_init (struct_def: @struct_t id_ty) (fields: list (dstruct_field_t * vect_t)) : result vect_t unit :=
    let empty := Bits.zeroes (struct_sz struct_def) in
    result_list_fold_left (fun acc '(f,v) => subst_field struct_def.(dstruct_fields) f acc v)
                          fields (Success empty).

  Definition get_field fields (f: @dstruct_field_t id_ty) (arg: list bool) : result (list bool) unit :=
    let/res offset := element_offset fields f in
    let/res width := get_field_width fields f in
    if Nat.eqb (Datatypes.length arg) (struct_sz' fields) then
      Success (Bits.slice offset width arg) (* TODO: do checks in interpreter/rely on typechecker? *)
    else Failure (__debug__ ("GetField/Invalid arg size",  arg) tt).


    Definition ext_sigma_t : Type := @ext_fn_t id_ty -> list bool -> result (list bool) unit.
End Utils.

Section Interp.

    Definition interp_bits1 (fn: bits1) (arg: list bool) : result (list bool) unit :=
      match fn with
      | Not => Success (Bits.neg arg)
      | Slice offset width => Success (Bits.slice offset width arg)
      | SExt width => Success (Bits.extend_end arg width (Bits.msb arg))
      | ZExtL width => Success (Bits.extend_end arg width false)
      end.

    Definition interp_bits2 (fn: bits2) (arg1 arg2: list bool) : result (list bool) unit :=
      match fn with
      | And => Bits.and arg1 arg2
      | Or => Bits.or arg1 arg2
      | Xor => Bits.xor arg1 arg2
      | Lsl => Success (Bits.lsl (Bits.to_nat arg2) arg1)
      | Lsr => Success (Bits.lsr (Bits.to_nat arg2) arg1)
      | Asr => Success (Bits.asr (Bits.to_nat arg2) arg1)
      | Concat => Success (Bits.concat arg1 arg2)
      | Sel => let/res b := Bits.sel arg1 arg2 in
              Success [b]
      | Plus => Bits.plus arg1 arg2
      | Minus => Bits.minus arg1 arg2
      | EqBits true => Success [negb (beq_dec arg1 arg2)]
      | EqBits false => Success [(beq_dec arg1 arg2)]
      | Compare signed c =>
        match signed, c with
        | true, cLt => Bits.bitfun_of_predicate Bits.signed_lt arg1 arg2
        | true, cGt => Bits.bitfun_of_predicate Bits.signed_gt arg1 arg2
        | true, cLe => Bits.bitfun_of_predicate Bits.signed_le arg1 arg2
        | true, CGe => Bits.bitfun_of_predicate Bits.signed_ge arg1 arg2
        | false, cLt => Bits.bitfun_of_predicate Bits.unsigned_lt arg1 arg2
        | false, cGt => Bits.bitfun_of_predicate Bits.unsigned_gt arg1 arg2
        | false, cLe => Bits.bitfun_of_predicate Bits.unsigned_le arg1 arg2
        | false, cGe => Bits.bitfun_of_predicate Bits.unsigned_ge arg1 arg2
        end
      | IndexedSlice width =>
          Success (Bits.slice (Bits.to_nat arg2) width arg1)
      end.

    (* External modules:
       - ext_fn_t -> state -> read -> value
       - ext_fn_t -> write value -> log it.
     *)
    Section InterpAction.
      Context (ext_sigma: @ext_sigma_t N).
      Context (int_fns: @int_fn_env_t N (@action N)).
      Context (struct_defs: @struct_env_t N).

      Definition interp_zop (fn: @fn0 N) : result (list bool) unit :=
        match fn with
        | StructInit sname =>
          let/res s := lookup_struct struct_defs sname
                                     (__debug__ ("interp_zop/StructInit/struct not found", sname) tt) in
          Success (Bits.zeroes (struct_sz s))
        end.

      Definition interp_struct1 (fn: struct1) (arg: list bool) : result (list bool) unit :=
        match fn with
        | GetField name f =>
           let/res s := lookup_struct struct_defs name
                                     (__debug__ ("interp_struct1/GetField/struct not found", name) tt) in
           get_field s.(dstruct_fields) f arg
        end.

      Definition interp_unop (fn: fn1) (arg: list bool) : result (list bool) unit :=
        match fn with
        | Bits1 fn => interp_bits1 fn arg
        | Struct1 fn => interp_struct1 fn arg
        | Ignore => Success []
        end.


      Definition interp_struct2 (fn: struct2) (arg1 arg2: list bool) : result (list bool) unit :=
        match fn with
        | SubstField sname fname =>
         let/res s := lookup_struct struct_defs sname
                                   (__debug__ ("interp_struct2/SubstField/struct not found", sname) tt) in
         subst_field s.(dstruct_fields) fname arg1 arg2
        end.

      Definition interp_binop (fn: fn2) (arg1 arg2: list bool) : result (list bool) unit :=
        match fn with
        | Bits2 fn => interp_bits2 fn arg1 arg2
        | Struct2 fn => interp_struct2 fn arg1 arg2
        end.

      Record Log_t : Type := MkLog
      { Log__koika: log_t;
        Log__ext: ext_log_t
      }.

      Fixpoint interp_action
               (fuel: nat)
               (max_fn_depth: nat)
               (r: state_t)
               (gamma: gamma_t)
               (sched_log: Log_t)
               (action_log: Log_t)
               (a: @action N)
               : result (option (gamma_t * Log_t * vect_t )) unit :=
        let __debug__ {A} (v: A) := __debug__ v tt in
        match fuel with
        | 0 => Failure (__debug__ "Out of fuel")
        | S fuel =>
          (* match a with *)
          (* | Action a annots => *)
            match a with
            | Fail ty_hint => Success None
            | Var var =>
              let/res var_value := varenv_lookup_var gamma var (__debug__ ("Var not found", gamma,var)) in
              Success (Some (gamma, action_log, var_value))
            | Const cst => (Success (Some (gamma, action_log, cst)))
            | Assign var ex =>
              let/resopt3 gamma, action_log, v_ex := interp_action fuel max_fn_depth r gamma sched_log action_log ex in
              let/res _ := varenv_lookup_var gamma var (__debug__ ("Assign/var not found", var)) in
              (Success (Some (varenv_update gamma var v_ex, action_log, [])))
            | Seq a1 a2 =>
              let/resopt3 gamma, action_log, v1 := interp_action fuel max_fn_depth r gamma sched_log action_log a1 in
              interp_action fuel max_fn_depth r gamma sched_log action_log a2
            | If cond tbranch fbranch =>
              let/resopt3 gamma, action_log, v_cond := interp_action fuel max_fn_depth r gamma sched_log action_log cond in
              match v_cond with
              | [true] => interp_action fuel max_fn_depth r gamma sched_log action_log tbranch
              | [false] => interp_action fuel max_fn_depth r gamma sched_log action_log fbranch
              | _ => (Failure (__debug__ ("If: cond not single bit", v_cond)))
              end
            | Bind var ex body =>
               let/resopt3 gamma, action_log, v_ex := interp_action fuel max_fn_depth r gamma sched_log action_log ex in
               let/resopt3 gamma', action_log, v_body :=
                  interp_action fuel max_fn_depth r (varenv_bind gamma var v_ex) sched_log action_log body in
               Success (Some (tl gamma', action_log, v_body))
            | Read P0 idx =>
                let sched_le := log_get sched_log.(Log__koika) idx in
                if LE_may_read0 sched_le then
                  let/res v := r_get_reg r idx in
                  let action_le := log_get action_log.(Log__koika) idx in
                  let le' := LE_set_read0 action_le in
                  Success (Some (gamma, MkLog (log_set action_log.(Log__koika) idx le')
                                                     action_log.(Log__ext), v))
                else Success None
            | Read P1 idx =>
                let/res v0 := r_get_reg r idx  in
                let sched_le := log_get sched_log.(Log__koika) idx in
                if LE_may_read1 sched_le then
                  let action_le := log_get action_log.(Log__koika) idx in
                  let le' := LE_set_read1 action_le in
                  let/res v :=
                      match action_le.(lwrite0), sched_le.(lwrite0) with
                      | Some v, _ => Success v
                      | _, Some v => Success v
                      | _, _ => Success v0
                      end in
                  Success (Some (gamma, MkLog (log_set action_log.(Log__koika) idx le')
                                                    action_log.(Log__ext), v))
                else Success None
            | Write P0 idx value =>
                let/resopt3 gamma, action_log, v_value := interp_action fuel max_fn_depth r gamma sched_log action_log value in
                let sched_le := log_get sched_log.(Log__koika) idx in
                let action_le := log_get action_log.(Log__koika) idx in
                if LE_may_write0 sched_le && LE_may_write0 action_le then
                  let le' := LE_set_write0 action_le v_value in
                  Success (Some (gamma, MkLog (log_set action_log.(Log__koika) idx le')
                                                    action_log.(Log__ext), []))
                else Success None
            | Write P1 idx value =>
                let/resopt3 gamma, action_log, v_value := interp_action fuel max_fn_depth r gamma sched_log action_log value in
                let sched_le := log_get sched_log.(Log__koika) idx in
                let action_le := log_get action_log.(Log__koika) idx in
                if LE_may_write1 sched_le && LE_may_write1 action_le then
                  let le' := LE_set_write1 action_le v_value in
                  Success (Some (gamma, MkLog (log_set action_log.(Log__koika) idx le')
                                                    action_log.(Log__ext), []))
                else Success None
            | Zop fn =>
              let/res result := interp_zop fn in
              Success (Some (gamma, action_log, result))
            | Unop fn arg1 =>
                let/resopt3 gamma, action_log, v1 := interp_action fuel max_fn_depth r gamma sched_log action_log arg1 in
                let/res result := interp_unop fn v1 in
                Success (Some (gamma, action_log, result))
            | Binop fn arg1 arg2 =>
              let/resopt3 gamma, action_log, v1 := interp_action fuel max_fn_depth r gamma sched_log action_log arg1 in
              let/resopt3 gamma, action_log, v2 := interp_action fuel max_fn_depth r gamma sched_log action_log arg2 in
              let/res result := interp_binop fn v1 v2 in
              Success (Some (gamma, action_log, result))
            | ExternalCall fn arg =>
              let/resopt3 gamma, action_log, v := interp_action fuel max_fn_depth r gamma sched_log action_log arg in
              if (ext_log_can_call sched_log.(Log__ext) fn && ext_log_can_call action_log.(Log__ext) fn) then
                let/res res := ext_sigma fn v in
                Success (Some (gamma, MkLog action_log.(Log__koika)
                                            (ext_log_update action_log.(Log__ext) fn v), res))
              else
                Success None
            | InternalCall fn arg =>
              let/resopt3 gamma, action_log, v_arg :=
                interp_action fuel max_fn_depth r gamma sched_log action_log arg in
              let/res2 id, fn_spec :=
                lookup_int_fn int_fns fn ((__debug__ ("Int fn not found", fn))) in
              if Nat.ltb id max_fn_depth then
                let/resopt3 _, action_log, res :=
                   interp_action fuel id r (fn_gamma fn_spec.(fn_arg_name) v_arg)
                                 sched_log action_log fn_spec.(fn_body) in
                Success (Some (gamma, action_log, res))
              else
                Failure (__debug__ ("Int fn call out of bounds", fn, id))
            end
          (* end *)
        end.


      Definition interp_rule (st: state_t) (sched_log: Log_t) (rl: rule)
        : result (option Log_t) unit :=
        match interp_action (safe_fuel int_fns rl) (List.length int_fns)
                            st GenericGammaEmpty sched_log (MkLog log_empty SortedExtFnEnv.empty) rl with
        | Success (Some (_, l, _)) => Success (Some ({| Log__koika := l.(Log__koika);
                                                       Log__ext := l.(Log__ext)
                                                    |}))
        | Success None => Success None
        | Failure f => Failure f
        end.

    Section Scheduler.
      Context {rule_name_t: Type}.
      Context (r: state_t).
      Context (rules: rule_name_t -> @rule N).

      Definition ext_log_app (log1 log2: ext_log_t) : ext_log_t :=
        let zipped := SortedExtFnEnv.zip_default log1 log2 None None in
        SortedExtFnEnv.mapV (fun '(le1, le2) =>
                               match le1, le2 with
                               | Some v1, Some v2 => Some (success_or_default (Bits.or v1 v2) [])
                               | Some _, None => le1
                               | _, _ => le2
                               end) zipped.

      Definition Log_app (log1 log2: Log_t) : Log_t :=
        {| Log__koika := log_app log1.(Log__koika) log2.(Log__koika);
           Log__ext := ext_log_app log1.(Log__ext) log2.(Log__ext)
        |}.

      Definition Log_empty : Log_t :=
        {| Log__koika := log_empty;
           Log__ext := SortedExtFnEnv.empty
        |}.

      Fixpoint interp_scheduler' (s: scheduler) (sched_log: Log_t) : result Log_t unit :=
        match s with
        | Done => Success sched_log
        | Cons rl s =>
          let/res opt_action_log := interp_rule r sched_log (rules rl) in
          match opt_action_log with
          | Some action_log => interp_scheduler' s (Log_app action_log sched_log)
          | None => interp_scheduler' s sched_log
          end
        end.
      Definition interp_scheduler (s: scheduler) : result Log_t unit :=
        interp_scheduler' s Log_empty.

      Fixpoint interp_scheduler_list' (s: list rule) (sched_log: Log_t) : result Log_t unit :=
        match s with
        | [] => Success sched_log
        | rl::s =>
          let/res opt_action_log := interp_rule r sched_log rl in
          match opt_action_log with
          | Some action_log => interp_scheduler_list' s (Log_app action_log sched_log)
          | None => interp_scheduler_list' s sched_log
          end
        end.

      Definition interp_scheduler_list (s: list rule) : result Log_t unit :=
         interp_scheduler_list' s Log_empty.

      Definition interp_cycle (s: scheduler) : result state_t unit :=
        match interp_scheduler s with
        | Success log => Success (commit_update r log.(Log__koika))
        | Failure f => Failure f
        end.

      Definition interp_cycle' (s: scheduler) : result (state_t * ext_log_t) unit :=
        match interp_scheduler s with
        | Success log => Success (commit_update r log.(Log__koika), log.(Log__ext))
        | Failure f => Failure f
        end.

      Definition interp_cycle_list' (s: list rule) : result (state_t * ext_log_t) unit :=
        match interp_scheduler_list s with
        | Success log => Success (commit_update r log.(Log__koika), log.(Log__ext))
        | Failure f => Failure f
        end.

    End Scheduler.

  End InterpAction.

End Interp.

Section CPS.
  Definition action_interpreter A := forall (gamma: gamma_t) (log: Log_t), A.
  Definition interp_continuation T A := result (option (gamma_t * Log_t * list bool)) T -> A.
  Definition action_continuation T A := interp_continuation T A.
  Definition rule_continuation T A := result (option Log_t) T -> A.
  Definition scheduler_continuation T A := result Log_t T -> A.
  Definition cycle_continuation T A := result state_t T -> A.

  Definition interpreter T A := forall (log: result Log_t T), A.

  Section InterpAction.
    Context (ext_sigma: @ext_sigma_t N).
    Context (int_fns: @int_fn_env_t N (@action N)).
    Context (struct_defs: @struct_env_t N).

    Definition restore_gamma {A} (res: result (option (gamma_t * Log_t * list bool)) A)
                             (gamma: gamma_t)
                             : result (option (gamma_t * Log_t * list bool)) A :=
      let/res opt := res in
      match opt with
      | Some (gamma', log, v) =>
        Success (Some (gamma, log, v))
      | None => Success None
      end.

    Fixpoint interp_action_cps
             (fuel: nat)
             (max_fn_depth: nat)
             (r: state_t)
             (log: Log_t) (a: action)
             {A} (k: action_continuation unit A)
    : action_interpreter A :=
      match fuel with
      | 0 => fun gamma l => k (Failure (__debug__ "Fn depth exceeded" tt))
      | S fuel =>
        let cps a {A} k := @interp_action_cps fuel max_fn_depth r log a A k in
        (* match a with *)
        (* | Action a annots => *)
          match a with
          | Fail ty_hint => fun k gamma l => k (Success None)
          | Var var => fun k gamma l =>
                        k (let/res var_value := varenv_lookup_var gamma var
                                                                 (__debug__ ("Var not found", gamma,var) tt) in
                           (Success (Some (gamma, l , var_value))))
          | Const cst => fun k gamma l =>
                          k (Success (Some (gamma, l , cst)))
          | Assign var ex => fun k =>
                              cps ex (fun res =>
                                        k (let/res opt := res in
                                           match opt with
                                           | Some (gamma, log, v) =>
                                             let/res _ := varenv_lookup_var gamma var (__debug__ ("Assign/var not found", var) tt) in
                                             (Success (Some (varenv_update gamma var v, log, [])))
                                           | None => (Success None)
                                           end))
          | Seq a1 a2 => fun k =>
                          cps a1 (fun res =>
                                    match res with
                                    | Success (Some (gamma, log, v)) =>
                                      cps a2 k gamma log
                                    | _ => k res
                                    end)
          | If cond tbranch fbranch =>
            fun k =>
              cps cond (fun res =>
                          match res with
                          | Success (Some (gamma, log, v)) =>
                            match v with
                            | [true] => cps tbranch k gamma log
                            | [false] => cps fbranch k gamma log
                            | _ => k (Failure (__debug__ ("If: cond not single bit", v) tt))
                            end
                          | _ => k res
                          end)
          | Bind var ex body => fun k =>
                                 cps ex (fun res =>
                                           match res with
                                           | Success (Some (gamma, log, v)) =>
                                             cps body (fun res =>
                                                         k (let/res opt := res in
                                                             match opt with
                                                            | (Some (gamma', log, v)) =>
                                                              (Success (Some (tl gamma', log, v)))
                                                            | _ => res
                                                            end))
                                                            (varenv_bind gamma var v) log
                                           | _ => k res
                                           end)
          | Read P0 idx =>
            fun k gamma l =>
              k (let sched_le := log_get log.(Log__koika) idx in
                 if LE_may_read0 sched_le then
                   let/res v := r_get_reg r idx in
                   let action_le := log_get l.(Log__koika) idx in
                   let le' := LE_set_read0 action_le in
                   Success (Some (gamma, MkLog (log_set l.(Log__koika) idx le') l.(Log__ext), v))
                 else Success None)
          | Read P1 idx =>
            fun k gamma l =>
              k (let/res v0 := r_get_reg r idx in
                 let sched_le := log_get log.(Log__koika) idx in
                 if LE_may_read1 sched_le then
                   let action_le := log_get l.(Log__koika) idx in
                   let le' := LE_set_read1 action_le in
                   let/res v :=
                       match action_le.(lwrite0), sched_le.(lwrite0) with
                       | Some v, _ => Success v
                       | _, Some v => Success v
                       | _, _ => Success v0
                       end in
                   Success (Some (gamma, MkLog (log_set l.(Log__koika) idx le') l.(Log__ext), v))
                 else Success None
                )
          | Write P0 idx value =>
            fun k =>
              cps value (fun res =>
                           match res with
                           | Success (Some (gamma, l, v)) =>
                               k (let sched_le := log_get log.(Log__koika) idx in
                                  let action_le := log_get l.(Log__koika) idx in
                                  if LE_may_write0 sched_le && LE_may_write0 action_le then
                                    let le' := LE_set_write0 action_le v in
                                    Success (Some (gamma, MkLog (log_set l.(Log__koika) idx le') l.(Log__ext), []))
                                  else Success None)
                           | _ => k res
                           end)
          | Write P1 idx value =>
            fun k =>
              cps value (fun res =>
                           match res with
                           | Success (Some (gamma, l, v)) =>
                               k (let sched_le := log_get log.(Log__koika) idx in
                                  let action_le := log_get l.(Log__koika) idx in
                                  if LE_may_write1 sched_le && LE_may_write1 action_le then
                                    let le' := LE_set_write1 action_le v in
                                    Success (Some (gamma, MkLog (log_set l.(Log__koika) idx le') l.(Log__ext), []))
                                  else Success None)
                           | _ => k res
                           end)
          | Zop fn =>
            fun k gamma l =>
              k (let/res result := interp_zop struct_defs fn in
                 Success (Some (gamma, l, result)))
          | Unop fn arg1 =>
            fun k =>
            cps arg1 (fun res =>
                        match res with
                        | Success (Some (gamma, l, v)) =>
                          k (let/res result := interp_unop struct_defs fn v in
                             Success (Some (gamma, l, result)))
                        | _ => k res
                        end)
          | Binop fn arg1 arg2 =>
            fun k =>
              cps arg1 (fun res =>
                          match res with
                          | Success (Some (gamma, l, v1)) =>
                            cps arg2 (fun res =>
                                        match res with
                                        | Success (Some (gamma, l, v2)) =>
                                          k (let/res result := interp_binop struct_defs fn v1 v2 in
                                             Success (Some (gamma, l, result)))
                                        | _ => k res
                                        end) gamma l
                          | _ => k res
                          end)
          | InternalCall fn arg =>
            fun k =>
              cps arg (fun res =>
                         match res with
                         | Success (Some (gamma, l, v)) =>
                           match lookup_int_fn int_fns fn ((__debug__ ("Int fn not found", fn) tt)) with
                           | Success (id, fn_spec) =>
                               if Nat.ltb id max_fn_depth then
                                 @interp_action_cps fuel id r log
                                              fn_spec.(fn_body) _
                                               (fun res =>
                                                  match res with
                                                  | Success (Some (_, l, v)) =>
                                                    k (Success (Some (gamma, l, v)))
                                                  | _ => k res
                                                  end) (fn_gamma fn_spec.(fn_arg_name) v) l
                               else k (Failure (__debug__ ("Int fn call out of bounds", fn, id) tt))
                           | Failure f => k (Failure f)
                           end
                         | _ => k res
                         end)
          | ExternalCall fn arg =>
            fun k =>
              cps arg (fun res =>
                         match res with
                         | Success (Some (gamma, l, v)) =>
                           k (if (ext_log_can_call log.(Log__ext) fn && ext_log_can_call l.(Log__ext) fn) then
                               let/res res := ext_sigma fn v in
                               Success (Some (gamma, MkLog l.(Log__koika)
                                                           (ext_log_update l.(Log__ext) fn v), res))
                              else
                                Success None
                             )
                         | _ => k res
                         end)
          end k
        (* end *)
      end.

    Definition rule := @action N.

    Definition interp_rule_cps (st: state_t) (rl: rule) {A} (k: rule_continuation unit A)
      : interpreter unit A :=
      fun L_res =>
        match L_res with
        | Success L =>
          interp_action_cps (safe_fuel int_fns rl)
                            (List.length int_fns)
                            st L rl (fun res =>
                                       match res with
                                       | Success (Some (_, l, _)) => k (Success (Some l))
                                       | Success None => k (Success None)
                                       | Failure f => k (Failure f)
                                       end) GenericGammaEmpty Log_empty
        | Failure f => k (Failure f)
        end.

    Section Scheduler.
      Context {rule_name_t: Type}.
      Context (r: state_t).
      Context (rules: rule_name_t -> rule).

      Fixpoint interp_scheduler'_cps
               (s: scheduler)
               {A} (k: scheduler_continuation unit A)
               {struct s} : interpreter unit A :=
        match s with
        | Done => k
        | Cons rl1 s =>
          fun L_res =>
            match L_res with
            | Success L =>
              interp_rule_cps r (rules rl1)
                              (fun res => match res with
                                       | Success (Some l) => interp_scheduler'_cps s k (Success (Log_app l L))
                                       | Success None  => interp_scheduler'_cps s k (Success L)
                                       | Failure f => k (Failure f)
                                       end) (Success L)
            | Failure f => k (Failure f)
            end
        end.


      Definition interp_scheduler_cps
                 (s: scheduler)
                 {A} (k: scheduler_continuation unit A) : A :=
        interp_scheduler'_cps s k (Success Log_empty).

      Definition interp_cycle_cps (s: scheduler)
                 {A} (k: cycle_continuation unit A) : A :=
        interp_scheduler_cps s (fun res_L => k (let/res L := res_L in
                                               Success (commit_update r L.(Log__koika)))).


    End Scheduler.

    Definition action_precondition := action_interpreter Prop.
    Definition action_postcondition := action_continuation unit Prop.
    Definition precondition := interpreter unit Prop.
    Definition rule_postcondition := rule_continuation unit Prop.
    Definition scheduler_postcondition := scheduler_continuation unit Prop.
    Definition cycle_postcondition := cycle_continuation unit Prop.

    Definition wp_action (fuel: nat) (fn_depth: nat) (r: state_t) (L: Log_t) (a: action)
               (post: action_postcondition) : action_precondition :=
      interp_action_cps fuel fn_depth r L a post.

    Definition wp_rule (r: state_t) (rl: rule) (post: rule_postcondition) : precondition :=
      interp_rule_cps r rl post.

    Definition wp_scheduler {rule_name_t: Type} (r: state_t) (rules: rule_name_t -> rule) (s: scheduler) (post: scheduler_postcondition) : Prop :=
      interp_scheduler_cps r rules s post.

    Definition wp_cycle {rule_name_t: Type} (r: state_t) (rules: rule_name_t -> rule)
               (s: scheduler) (post: cycle_postcondition) : Prop :=
      interp_cycle_cps r rules s post.

  End InterpAction.

End CPS.

Section CPS2.
  Definition action_interpreter2 A := forall (gamma1: gamma_t) (log1: Log_t) (gamma2: gamma_t) (log2: Log_t), A.
  Definition interp_continuation2 T A :=
    result (option (gamma_t * Log_t * list bool)) T ->
    result (option (gamma_t * Log_t * list bool)) T ->
    A.

  Definition action_continuation2 T A := interp_continuation2 T A.
  Definition rule_continuation2 T A := result (option Log_t) T -> result (option Log_t) T -> A.
  Definition scheduler_continuation2 T A := result Log_t T -> result Log_t T -> A.
  Definition cycle_continuation2 T A := result state_t T -> result state_t T -> A.

  Definition interpreter2 T A := forall (log1 log2: result Log_t T), A.

End CPS2.

Section TypecheckedInterp.

    Section InterpAction.
      Context (ext_sigma: @ext_sigma_t N).
      Context (int_fns: @int_fn_env_t N (@action N)).
      Context (struct_defs: @struct_env_t N).

      Definition unsafe_interp_zop (fn: fn0) : list bool :=
        match interp_zop struct_defs fn with
        | Success bs => bs
        | Failure _ => []
        end.

      Definition unsafe_interp_unop (fn: fn1) (arg: list bool) : list bool :=
        match interp_unop struct_defs fn arg with
        | Success bs => bs
        | Failure _ => []
        end.

      Definition unsafe_interp_binop (fn: fn2) (arg1 arg2: list bool) : list bool :=
        match interp_binop struct_defs fn arg1 arg2 with
        | Success bs => bs
        | Failure _ => []
        end.

      Definition unsafe_varenv_lookup_var (gamma: gamma_t) (v: var_t) : list bool :=
        match varenv_lookup_var gamma v tt with
        | Success res => res
        | Failure _ => []
        end.

      Definition unsafe_call_ext (fn: ext_fn_t) (arg: list bool) : list bool :=
        match ext_sigma fn arg with
        | Success bs => bs
        | Failure _ => []
        end.

      Definition unsafe_r_get_reg (st: state_t) (reg: reg_t) : list bool :=
        match r_get_reg st reg with
        | Success bs => bs
        | Failure _ => []
        end.

      Definition unsafe_get_fn_arg_and_body (fn: fn_name_t) : var_t * action :=
        match lookup_int_fn int_fns fn tt with
        | Success (_, fn_spec) => (fn_spec.(fn_arg_name), fn_spec.(fn_body))
        | Failure _ => ("", Fail 0)
        end.

      Definition unsafe_read1 (action_log: Log_t) (sched_log: Log_t) (r: state_t) (reg: reg_t) : list bool :=
        let sched_le := log_get sched_log.(Log__koika) reg in
        let action_le := log_get action_log.(Log__koika) reg in
        match action_le.(lwrite0), sched_le.(lwrite0) with
        | Some v, _ => v
        | _, Some v => v
        | _, _ => unsafe_r_get_reg r reg
        end.

      Fixpoint unsafe_interp_action
               (fuel: nat)
               (r: state_t)
               (gamma: gamma_t)
               (sched_log: Log_t)
               (action_log: Log_t)
               (a: action)
               : option (gamma_t * Log_t * list bool) :=
        let __debug__ {A} (v: A) := __debug__ v tt in
        match fuel with
        | 0 => None
        | S fuel =>
          (* match a with *)
          (* | Action a annots => *)
            match a with
            | Fail ty_hint => None
            | Var var => Some (gamma, action_log, unsafe_varenv_lookup_var gamma var)
            | Const cst => Some (gamma, action_log, cst)
            | Assign var ex =>
              let/opt3 gamma, action_log, v_ex := unsafe_interp_action fuel r gamma sched_log action_log ex in
              Some (varenv_update gamma var v_ex, action_log, [])
            | Seq a1 a2 =>
              let/opt3 gamma, action_log, v1 := unsafe_interp_action fuel r gamma sched_log action_log a1 in
              unsafe_interp_action fuel r gamma sched_log action_log a2
            | If cond tbranch fbranch =>
              let/opt3 gamma, action_log, v_cond := unsafe_interp_action fuel r gamma sched_log action_log cond in
              match v_cond with
              | [true] => unsafe_interp_action fuel r gamma sched_log action_log tbranch
              | _ (* [false] *) => unsafe_interp_action fuel r gamma sched_log action_log fbranch
              end
            | Bind var ex body =>
               let/opt3 gamma, action_log, v_ex := unsafe_interp_action fuel r gamma sched_log action_log ex in
               let/opt3 gamma', action_log, v_body :=
                  unsafe_interp_action fuel r (varenv_bind gamma var v_ex) sched_log action_log body in
               Some (tl gamma', action_log, v_body)
            | Read P0 idx =>
                let sched_le := log_get sched_log.(Log__koika) idx in
                let action_le := log_get action_log.(Log__koika) idx in
                if LE_may_read0 sched_le then
                  let le' := {|lread0 := true; lread1 := action_le.(lread1);
                               lwrite0 := action_le.(lwrite0); lwrite1 := action_le.(lwrite1) |} in
                  Some (gamma, MkLog (log_set action_log.(Log__koika) idx le')
                                     (action_log.(Log__ext)), unsafe_r_get_reg r idx)
                else None
            | Read P1 idx =>
                let sched_le := log_get sched_log.(Log__koika) idx in
                let action_le := log_get action_log.(Log__koika) idx in
                if LE_may_read1 sched_le then
                  let le' := {| lread0 := action_le.(lread0); lread1 := true;
                                lwrite0 := action_le.(lwrite0); lwrite1 := action_le.(lwrite1) |} in
                  let v := unsafe_read1 action_log sched_log r idx in
                  Some (gamma, MkLog (log_set action_log.(Log__koika) idx le') action_log.(Log__ext), v)
                else None
            | Write P0 idx value =>
                let/opt3 gamma, action_log, v_value := unsafe_interp_action fuel r gamma sched_log action_log value in
                let sched_le := log_get sched_log.(Log__koika) idx in
                let action_le := log_get action_log.(Log__koika) idx in
                if LE_may_write0 sched_le && LE_may_write0 action_le then
                  let le' := {| lread0 := action_le.(lread0);
                                lread1 := action_le.(lread1);
                                lwrite0 := Some v_value;
                                lwrite1 := action_le.(lwrite1) |} in
                  Some (gamma, MkLog (log_set action_log.(Log__koika) idx le') action_log.(Log__ext), [])
                else None
            | Write P1 idx value =>
                let/opt3 gamma, action_log, v_value := unsafe_interp_action fuel r gamma sched_log action_log value in
                let sched_le := log_get sched_log.(Log__koika) idx in
                let action_le := log_get action_log.(Log__koika) idx in
                if LE_may_write1 sched_le && LE_may_write1 action_le then
                  let le' := {| lread0 := action_le.(lread0);
                                lread1 := action_le.(lread1);
                                lwrite0 := action_le.(lwrite0);
                                lwrite1 := Some v_value |} in
                  Some (gamma, MkLog (log_set action_log.(Log__koika) idx le') action_log.(Log__ext), [])
                else None
            | Zop fn =>
              Some (gamma, action_log, unsafe_interp_zop fn)
            | Unop fn arg1 =>
              let/opt3 gamma, action_log, v1 := unsafe_interp_action fuel r gamma sched_log action_log arg1 in
              Some (gamma, action_log, unsafe_interp_unop fn v1)
            | Binop fn arg1 arg2 =>
              let/opt3 gamma, action_log, v1 := unsafe_interp_action fuel r gamma sched_log action_log arg1 in
              let/opt3 gamma, action_log, v2 := unsafe_interp_action fuel r gamma sched_log action_log arg2 in
              Some (gamma, action_log, unsafe_interp_binop fn v1 v2)
            | ExternalCall fn arg =>
              let/opt3 gamma, action_log, v := unsafe_interp_action fuel r gamma sched_log action_log arg in
              if (ext_log_can_call sched_log.(Log__ext) fn && ext_log_can_call action_log.(Log__ext) fn) then
                (Some (gamma, MkLog action_log.(Log__koika)
                              (ext_log_update action_log.(Log__ext) fn v), unsafe_call_ext fn v))
              else None
            | InternalCall fn arg =>
              let/opt3 gamma, action_log, v_arg := unsafe_interp_action fuel r gamma sched_log action_log arg in
              let '(arg_name, body) := unsafe_get_fn_arg_and_body fn in
              let/opt3 _, action_log, res :=
                   unsafe_interp_action fuel r (fn_gamma arg_name v_arg)
                                 sched_log action_log body in
                Some (gamma, action_log, res)
            end
          (* end *)
        end.

      Definition unsafe_interp_rule (st: state_t) (sched_log: Log_t) (rl: rule)
        : option Log_t :=
        match unsafe_interp_action (safe_fuel int_fns rl)
                            st GenericGammaEmpty sched_log Log_empty rl with
        | Some (_, l, _) => (Some l)
        | None => None
        end.

    Section Scheduler.
      Context {rule_name_t: Type}.
      Context (r: state_t).
      Context (rules: rule_name_t -> rule).

      Fixpoint unsafe_interp_scheduler' (s: scheduler) (sched_log: Log_t) : Log_t :=
        match s with
        | Done => sched_log
        | Cons rl s =>
          let opt_action_log := unsafe_interp_rule r sched_log (rules rl) in
          match opt_action_log with
          | Some action_log => unsafe_interp_scheduler' s (Log_app action_log sched_log)
          | None => unsafe_interp_scheduler' s sched_log
          end
        end.

      Definition unsafe_interp_scheduler (s: scheduler) : Log_t :=
        unsafe_interp_scheduler' s Log_empty.

      (* Definition unsafe_interp_cycle (s: scheduler) : state_t := *)
      (*   commit_update r (unsafe_interp_scheduler s). *)
    End Scheduler.

  End InterpAction.

End TypecheckedInterp.


Section OneRuleAtATime.
  Context (ext_sigma: @ext_sigma_t N).
  Context (int_fns: @int_fn_env_t N (@action N)).
  Context (struct_defs: @struct_env_t N).


  Definition varenv_lookup_var' (gamma: gamma_t) (v: var_t) : bool * list bool :=
    let res := varenv_lookup_var gamma v tt in
    (is_success res, success_or_default res []).

  Definition r_get_reg' (st: state_t) (reg: reg_t) : bool * list bool :=
    let res := r_get_reg st reg in
    (is_success res, success_or_default res []).

  Definition interp_zop' (fn: fn0) : bool * list bool :=
    let res := interp_zop struct_defs fn  in
    (is_success res, success_or_default res []).

  Definition interp_unop' (fn: fn1) (arg: list bool) : bool * list bool :=
    let res := interp_unop struct_defs fn arg in
    (is_success res, success_or_default res []).

  Definition interp_binop' (fn: fn2) (arg1 arg2: list bool) : bool * list bool :=
    let res := interp_binop struct_defs fn arg1 arg2 in
    (is_success res, success_or_default res []).

  Definition call_ext' (fn: ext_fn_t) (arg: list bool) : bool * list bool :=
    let res := ext_sigma fn arg in
    (is_success res, success_or_default res []).

  Definition get_fn_arg_and_body'' (fn: fn_name_t) :=
    let/res2 _, fn_spec := lookup_int_fn int_fns fn tt in
    Success (fn_spec.(fn_arg_name), fn_spec.(fn_body)).

  Definition get_fn_arg_and_body' (fn: fn_name_t) : bool * (var_t * action) :=
    let res := get_fn_arg_and_body'' fn in
    (is_success res, success_or_default res ("", Fail 0)).

  Fixpoint oraat_interp_action
           (fuel: nat)
           (r: state_t)
           (r_acc: state_t)
           (ext_log: ext_log_t)
           (is_safe: bool)
           (gamma: gamma_t)
           (a: action)
           : bool * option (gamma_t * state_t * ext_log_t * list bool) :=
    match fuel with
    | 0 => (__debug__ "Out of fuel" false, None)
    | S fuel =>
      (* match a with *)
      (* | Action a annots => *)
        match a with
        | Fail ty_hint => (is_safe, None)
        | Var var =>
            let '(safe, v) := varenv_lookup_var' gamma var in
            (is_safe && safe, Some (gamma, r_acc, ext_log, v))
        | Const cst => (is_safe, (Some (gamma, r_acc, ext_log, cst)))
        | Assign var ex =>
            let/bopt4 is_safe, gamma, r_acc, ext_log, v_ex := oraat_interp_action fuel r r_acc ext_log is_safe gamma ex in
            let is_safe' := is_success (varenv_lookup_var gamma var tt) in
            (is_safe && is_safe', Some (varenv_update gamma var v_ex, r_acc, ext_log, []))
        | Seq a1 a2 =>
          let/bopt4 is_safe, gamma, r_acc, ext_log, v1 := oraat_interp_action fuel r r_acc ext_log is_safe gamma a1 in
          oraat_interp_action fuel r r_acc ext_log is_safe gamma a2
        | If cond tbranch fbranch =>
          let/bopt4 is_safe, gamma, r_acc, ext_log, v_cond := oraat_interp_action fuel r r_acc ext_log is_safe gamma cond in
          let is_safe := ((Nat.eqb (Datatypes.length v_cond) 1) && is_safe) in
          if bits_eq v_cond [true] then
            oraat_interp_action fuel r r_acc ext_log is_safe gamma tbranch
          else
            oraat_interp_action fuel r r_acc ext_log is_safe gamma fbranch
     |   Bind var ex body =>
          let/bopt4 is_safe, gamma, r_acc, ext_log, v_ex := oraat_interp_action fuel r r_acc ext_log is_safe gamma ex in
          let/bopt4 is_safe, gamma', r_acc, ext_log, v_body := oraat_interp_action fuel r r_acc ext_log is_safe (varenv_bind gamma var v_ex) body in
          (is_safe, Some (tl gamma', r_acc, ext_log, v_body))
        | Read P0 idx =>
          let '(safe, v) := r_get_reg' r idx in
          (is_safe && safe, Some (gamma, r_acc, ext_log, v))
        | Read P1 idx =>
          (* No Write0/Read1? *)
          let '(safe, v) := r_get_reg' r_acc idx in
          (is_safe && safe, Some (gamma, r_acc, ext_log, v))
        | Write _ idx value =>
          let/bopt4 is_safe, gamma, r_acc, ext_log, v_value := oraat_interp_action fuel r r_acc ext_log is_safe gamma value in
          (is_safe, Some (gamma, state_set r_acc idx v_value, ext_log, []))
        | Zop fn =>
          let '(safe, v) := interp_zop' fn in
          (is_safe && safe, Some (gamma, r_acc, ext_log, v))
        | Unop fn arg1 =>
          let/bopt4 is_safe, gamma, r_acc, ext_log, v_arg1 := oraat_interp_action fuel r r_acc ext_log is_safe gamma arg1 in
          let '(safe, v) := interp_unop' fn v_arg1 in
          (is_safe && safe, Some (gamma, r_acc, ext_log, v))
        | Binop fn arg1 arg2 =>
          let/bopt4 is_safe, gamma, r_acc, ext_log, v_arg1 := oraat_interp_action fuel r r_acc ext_log is_safe gamma arg1 in
          let/bopt4 is_safe, gamma, r_acc, ext_log, v_arg2 := oraat_interp_action fuel r r_acc ext_log is_safe gamma arg2 in
          let '(safe, v) := interp_binop' fn v_arg1 v_arg2 in
          (is_safe && safe, Some (gamma, r_acc, ext_log, v))
        | ExternalCall fn arg =>
            (* TODO: OR VALUE *)
          let/bopt4 is_safe, gamma, r_acc, ext_log, v_arg := oraat_interp_action fuel r r_acc ext_log is_safe gamma arg in
          let '(safe, v) := call_ext' fn v_arg in
          (is_safe && safe, Some (gamma, r_acc, ext_log_update ext_log fn v_arg, v))
        | InternalCall fn arg =>
          let/bopt4 is_safe, gamma, r_acc, ext_log, v_arg := oraat_interp_action fuel r r_acc ext_log is_safe gamma arg in
          let '(safe, (arg_name, body)) := get_fn_arg_and_body' fn in
          let is_safe := safe && is_safe in
          let/bopt4 is_safe, _, r_acc, ext_log, res :=
             oraat_interp_action fuel r r_acc ext_log is_safe (fn_gamma arg_name v_arg) body in
          (is_safe, Some (gamma, r_acc, ext_log, res))
        end
      (* end *)
    end.

  Definition oraat_interp_rule (st: state_t) (rl: rule) : bool * state_t * ext_log_t:=
    match oraat_interp_action (safe_fuel int_fns rl)
                              st st SortedExtFnEnv.empty true GenericGammaEmpty rl with
    | (is_safe, Some (_, st', ext_log, _)) => (is_safe, st', ext_log)
    | (is_safe, None) => (is_safe, st, SortedExtFnEnv.empty)
    end.

  Section Scheduler.
    Context {rule_name_t: Type}.
    Context (rules: rule_name_t -> rule).

    Fixpoint oraat_interp_scheduler' (st: state_t) (ext_log: ext_log_t) (is_safe: bool) (s: scheduler)  : bool * state_t * ext_log_t :=
      match s with
      | Done => (is_safe, st, ext_log)
      | Cons rl s =>
        let '(is_safe', st', ext_log') := oraat_interp_rule st (rules rl) in
        oraat_interp_scheduler' st' (ext_log_app ext_log' ext_log) (is_safe && is_safe') s
      end.

    Definition oraat_interp_scheduler (st: state_t) (s: scheduler) : bool * state_t * ext_log_t:=
      oraat_interp_scheduler' st SortedExtFnEnv.empty true s.

    Definition unsafe_oraat_interp_cycle (st: state_t) (s: scheduler) : state_t * ext_log_t:=
      let '(_, st', log') := oraat_interp_scheduler st s in
      (st', log').

  End Scheduler.

  Fixpoint oraat_interp_scheduler_list' (st: state_t) (ext_log: ext_log_t) (is_safe: bool) (s: list rule) : bool * state_t * ext_log_t :=
      match s with
      | [] => (is_safe, st, ext_log)
      | rl::s =>
        let '(is_safe', st', ext_log') := oraat_interp_rule st (rl) in
        oraat_interp_scheduler_list' st' (ext_log_app ext_log' ext_log) (is_safe && is_safe') s
      end.

  Definition oraat_interp_scheduler_list (st: state_t) (s: list rule) : bool * state_t * ext_log_t:=
    oraat_interp_scheduler_list' st SortedExtFnEnv.empty true s.



  Definition oraat_interp_rule2 (st1 st2: state_t) (rl: rule) : bool * (state_t * ext_log_t) * (state_t * ext_log_t) :=
    let '(is_safe1, st1', ext_log1') := oraat_interp_rule st1 rl in
    let '(is_safe2, st2', ext_log2') := oraat_interp_rule st2 rl in
    (is_safe1 && is_safe2, (st1', ext_log1'), (st2', ext_log2')).


  Section CPS.
    Definition oraat_action_interpreter A := forall (gamma: gamma_t) (st': state_t) (ext_log': ext_log_t) (is_safe: bool), A.
    Definition oraat_interp_continuation A := bool * (option (gamma_t * state_t * ext_log_t * list bool)) -> A.
    Definition oraat_action_continuation A := oraat_interp_continuation A.
    Definition oraat_rule_continuation A := bool * state_t * ext_log_t -> A.
    Definition oraat_scheduler_continuation A := bool * state_t * ext_log_t -> A.
    Definition oraat_cycle_continuation A := state_t -> A.

    Definition oraat_interpreter A := forall (st: state_t), A.

    Section InterpAction.
      Fixpoint oraat_interp_action_cps
               (fuel: nat)
               (r: state_t)
               (a: action)
               {A} (k: oraat_action_continuation A)
               : oraat_action_interpreter A :=
        match fuel with
        | 0 => fun gamma r_acc ext_log is_safe => k (__debug__ "Out of fuel" false, None)
        | S fuel =>
         let cps a {A} k := @oraat_interp_action_cps fuel r a A k in
         (* match a with *)
         (* | Action a annots => *)
           match a with
           | Fail ty_hint => fun k gamma r_acc ext_log is_safe => k (is_safe, None)
           | Var var =>
             fun k gamma r_acc ext_log is_safe =>
               k (let '(safe, v) := varenv_lookup_var' gamma var in
                  (is_safe && safe, Some (gamma, r_acc, ext_log, v)))
           | Const cst =>
             fun k gamma r_acc ext_log is_safe =>
               k (is_safe, (Some (gamma, r_acc, ext_log, cst)))
           | Assign var ex =>
             fun k => cps ex (fun res =>
                             k (let/bopt4 is_safe, gamma, r_acc, ext_log, v_ex := res in
                                let is_safe' := is_success (varenv_lookup_var gamma var tt) in
                                (is_safe && is_safe', Some (varenv_update gamma var v_ex, r_acc, ext_log, []))))
           | Seq a1 a2 =>
             fun k => cps a1 (fun res =>
                             match res with
                             | (is_safe, Some (gamma, r_acc, ext_log, v_ex)) =>
                               cps a2 k gamma r_acc ext_log is_safe
                             | _ => k res
                             end)
           | If cond tbranch fbranch =>
             fun k =>
               cps cond (fun res =>
                           match res with
                           | (is_safe, Some (gamma, r_acc, ext_log, v_cond)) =>
                             let is_safe := ((Nat.eqb (Datatypes.length v_cond) 1) && is_safe)in
                             if bits_eq v_cond [true] then
                               cps tbranch k gamma r_acc ext_log is_safe
                             else cps fbranch k gamma r_acc ext_log is_safe
                           | _ => k res
                           end)
           | Bind var ex body =>
            fun k => cps ex (fun res =>
                            match res with
                            | (is_safe, Some (gamma, r_acc, ext_log, v_ex)) =>
                              cps body (fun res =>
                                          k (let/bopt4 is_safe, gamma', r_acc, ext_log, v := res in
                                             (is_safe, Some (tl gamma', r_acc, ext_log, v))))
                                  (varenv_bind gamma var v_ex) r_acc ext_log is_safe
                            | _ => k res
                            end)
           | Read P0 idx =>
             fun k gamma r_acc ext_log is_safe =>
               k (let '(safe, v) := r_get_reg' r idx in
                  (is_safe && safe, Some (gamma, r_acc, ext_log, v)))
           | Read P1 idx =>
             fun k gamma r_acc ext_log is_safe =>
               k ( let '(safe, v) := r_get_reg' r_acc idx in
                   (is_safe && safe, Some (gamma, r_acc, ext_log, v)))
           | Write _ idx value =>
             fun k =>
               cps value (fun res =>
                            match res with
                            | (is_safe, Some (gamma, r_acc, ext_log, v_value)) =>
                              k (is_safe, Some (gamma, state_set r_acc idx v_value, ext_log, []))
                            | _ => k res
                            end)
           | Zop fn =>
              fun k gamma r_acc ext_log is_safe =>
               k (let '(safe, v) := interp_zop' fn in
                  (is_safe && safe, Some (gamma, r_acc, ext_log, v)))
           | Unop fn arg1 =>
             fun k =>
               cps arg1 (fun res =>
                         match res with
                         | (is_safe, Some (gamma, r_acc, ext_log, v_arg1)) =>
                           k (let '(safe, v) := interp_unop' fn v_arg1 in
                              (is_safe && safe, Some (gamma, r_acc, ext_log, v)))
                         | _ => k res
                         end)
           | Binop fn arg1 arg2 =>
             fun k =>
               cps arg1 (fun res =>
                           match res with
                           | (is_safe, Some (gamma, r_acc, ext_log, v_arg1)) =>
                             cps arg2 (fun res =>
                                         match res with
                                         | (is_safe, Some (gamma, r_acc, ext_log, v_arg2)) =>
                                           k (let '(safe, v) := interp_binop' fn v_arg1 v_arg2 in
                                              (is_safe && safe, Some (gamma, r_acc, ext_log, v)))
                                         | _ => k res
                                         end) gamma r_acc ext_log is_safe
                           | _ => k res
                           end)
           | ExternalCall fn arg =>
             fun k => cps arg (fun res =>
                              match res with
                              | (is_safe, Some (gamma, r_acc, ext_log, v_arg)) =>
                                k (let '(safe, v) := call_ext' fn v_arg in
                                   (is_safe && safe, Some (gamma, r_acc, ext_log_update ext_log fn v_arg, v)))
                              | _ => k res
                              end)
           | InternalCall fn arg =>
             fun k => cps arg (fun res =>
                              match res with
                              | (is_safe, Some (gamma, r_acc, ext_log, v_arg)) =>
                                let '(safe, (arg_name, body)) := get_fn_arg_and_body' fn in
                                let is_safe := safe && is_safe in
                                cps body (fun res =>
                                            match res with
                                            | (is_safe, Some (_, r_acc, ext_log, v)) =>
                                              k (is_safe, Some (gamma, r_acc, ext_log, v))
                                            | _ => k res
                                            end) (fn_gamma arg_name v_arg) r_acc ext_log is_safe
                              | _ => k res
                              end)
           end k
         (* end *)
      end.

      Definition oraat_action_precondition := oraat_action_interpreter Prop.
      Definition oraat_action_postcondition := oraat_action_continuation Prop.
      Definition oraat_precondition := oraat_interpreter Prop.
      Definition oraat_rule_postcondition := oraat_rule_continuation Prop.

      Definition oraat_wp_action (fuel: nat) (r: state_t) (a: action)
                 (post: oraat_action_postcondition) : oraat_action_precondition :=
        oraat_interp_action_cps fuel r a post.

    End InterpAction.

   End CPS.

End OneRuleAtATime.
