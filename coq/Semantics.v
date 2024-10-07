Require Import Koika.Common.
Require Import Koika.Syntax.
Require Import Koika.SyntaxMacros.
Require Import Koika.Environments.
Require Import Koika.Typechecking.
Require Import Koika.Bits.
Require Import Coq.Init.Nat.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.

Import List.ListNotations.

(* Compute action depth for well-formedness *)
Section Height.
  Fixpoint height (a: action) : nat :=
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

  (* Definition max_height_int_fns  *)
End Height.

Section Interp.
    Definition interp_bits1 (fn: bits1) (arg: list bool) : result (list bool) unit :=
      match fn with
      | Not => Success (Bits.neg arg)
      | Slice offset width => Success (Bits.slice offset width arg)
      end.

    Definition interp_bits2 (fn: bits2) (arg1 arg2: list bool) : result (list bool) unit :=
      match fn with
      | And => Bits.and arg1 arg2
      | Or => Bits.or arg1 arg2
      | Xor => Bits.xor arg1 arg2
      | Concat => Success (Bits.concat arg1 arg2)
      | Sel => let/res b := Bits.sel arg1 arg2 in
              Success [b]
      | Plus => Bits.plus arg1 arg2
      | Minus => Bits.minus arg1 arg2
      | EqBits true => Success [negb (bits_eq arg1 arg2)]
      | EqBits false => Success [(bits_eq arg1 arg2)]
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
      end.


    Definition ext_sigma_t : Type := ext_fn_t -> list bool -> result (list bool) unit.

    Section InterpAction.
      Context (ext_sigma: ext_sigma_t).
      Context (int_fns: int_fn_env_t).
      Context (struct_defs: struct_env_t).

      Definition interp_zop (fn: fn0) : result (list bool) unit :=
        match fn with
        | StructInit sname =>
          let/res s := lookup_struct struct_defs sname
                                     (__debug__ ("interp_zop/StructInit/struct not found", sname) tt) in
          Success (Bits.zeroes (struct_sz s))
        end.

      Definition get_field fields f (arg: list bool) : result (list bool) unit :=
        let/res offset := element_offset fields f in
        let/res width := get_field_width fields f in
        if Nat.eqb (Datatypes.length arg) (struct_sz' fields) then
          Success (Bits.slice offset width arg) (* TODO: do checks in interpreter/rely on typechecker? *)
        else Failure (__debug__ ("GetField/Invalid arg size",  arg) tt).

      Definition interp_struct1 (fn: struct1) (arg: list bool) : result (list bool) unit :=
        match fn with
        | GetField name f =>
           let/res s := lookup_struct struct_defs name
                                     (__debug__ ("interp_struct1/GetField/struct not found", name) tt) in
           get_field s.(struct_fields) f arg
        end.

      Definition interp_unop (fn: fn1) (arg: list bool) : result (list bool) unit :=
        match fn with
        | Bits1 fn => interp_bits1 fn arg
        | Struct1 fn => interp_struct1 fn arg
        end.

      Definition subst_field (fields: list (struct_field_t * nat))
                             (fname: struct_field_t) (arg1 arg2: list bool)
                             : result (list bool) unit :=
         let/res offset := element_offset fields fname in
         let/res width := get_field_width fields fname in
         if Nat.eqb (Datatypes.length arg1) (struct_sz' fields) then
           if Nat.eqb (Datatypes.length arg2) width then
             Success (Bits.slice_subst offset arg2 arg1)
           else Failure (__debug__ ("subst_field/invalid arg2", arg2) tt)
         else
           Failure (__debug__ ("subst_field/Invalid arg size", fname, arg1) tt).

      Definition interp_struct2 (fn: struct2) (arg1 arg2: list bool) : result (list bool) unit :=
        match fn with
        | SubstField sname fname =>
         let/res s := lookup_struct struct_defs sname
                                   (__debug__ ("interp_struct2/SubstField/struct not found", sname) tt) in
         subst_field s.(struct_fields) fname arg1 arg2
        end.

      Definition interp_binop (fn: fn2) (arg1 arg2: list bool) : result (list bool) unit :=
        match fn with
        | Bits2 fn => interp_bits2 fn arg1 arg2
        | Struct2 fn => interp_struct2 fn arg1 arg2
        end.

      Fixpoint interp_action
               (fuel: nat)
               (max_fn_depth: nat)
               (r: state_t)
               (gamma: gamma_t)
               (sched_log: log_t)
               (action_log: log_t)
               (a: action)
               : result (option (gamma_t * log_t * list bool)) unit :=
        let __debug__ {A} (v: A) := __debug__ v tt in
        match fuel with
        | 0 => Failure (__debug__ "Out of fuel")
        | S fuel =>
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
              let sched_le := log_get sched_log idx in
              if LE_may_read0 sched_le then
                let/res v := r_get_reg r idx in
                let action_le := log_get action_log idx in
                let le' := LE_set_read0 action_le in
                Success (Some (gamma, log_set action_log idx le', v))
              else Success None
          | Read P1 idx =>
              let/res v0 := r_get_reg r idx  in
              let sched_le := log_get sched_log idx in
              if LE_may_read1 sched_le then
                let action_le := log_get action_log idx in
                let le' := LE_set_read1 action_le in
                let/res v :=
                    match action_le.(lwrite0), sched_le.(lwrite0) with
                    | Some v, _ => Success v
                    | _, Some v => Success v
                    | _, _ => Success v0
                    end in
                Success (Some (gamma, log_set action_log idx le', v))
              else Success None
          | Write P0 idx value =>
              let/resopt3 gamma, action_log, v_value := interp_action fuel max_fn_depth r gamma sched_log action_log value in
              let sched_le := log_get sched_log idx in
              let action_le := log_get action_log idx in
              if LE_may_write0 sched_le && LE_may_write0 action_le then
                let le' := LE_set_write0 action_le v_value in
                Success (Some (gamma, log_set action_log idx le', []))
              else Success None
          | Write P1 idx value =>
              let/resopt3 gamma, action_log, v_value := interp_action fuel max_fn_depth r gamma sched_log action_log value in
              let sched_le := log_get sched_log idx in
              let action_le := log_get action_log idx in
              if LE_may_write1 sched_le && LE_may_write1 action_le then
                let le' := LE_set_write1 action_le v_value in
                Success (Some (gamma, log_set action_log idx le', []))
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
            let/res res := ext_sigma fn v in
            Success (Some (gamma, action_log, res))
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
        end.

      Definition max_fn_height : nat :=
        fold_left max (map (fun fn => height fn.(fn_body)) int_fns) 0.

      Definition safe_fuel (fn_depth: nat) (a: action) : nat :=
        (max_fn_height * fn_depth) + (height a).

      Definition safe_fuel' (a: action) : nat :=
        safe_fuel (List.length int_fns) a.

      Definition interp_rule (st: state_t) (sched_log: log_t) (rl: rule)
        : result (option log_t) unit :=
        match interp_action (safe_fuel (List.length int_fns) rl) (List.length int_fns)
                            st GenericGammaEmpty sched_log log_empty rl with
        | Success (Some (_, l, _)) => Success (Some l)
        | Success None => Success None
        | Failure f => Failure f
        end.

    Section Scheduler.
      Context {rule_name_t: Type}.
      Context (r: state_t).
      Context (rules: rule_name_t -> rule).

      Fixpoint interp_scheduler' (s: scheduler) (sched_log: log_t) : result log_t unit :=
        match s with
        | Done => Success sched_log
        | Cons rl s =>
          let/res opt_action_log := interp_rule r sched_log (rules rl) in
          match opt_action_log with
          | Some action_log => interp_scheduler' s (log_app action_log sched_log)
          | None => interp_scheduler' s sched_log
          end
        end.

      Definition interp_scheduler (s: scheduler) : result log_t unit :=
        interp_scheduler' s log_empty.

      Definition interp_cycle (s: scheduler) : result state_t unit :=
        match interp_scheduler s with
        | Success log => Success (commit_update r log)
        | Failure f => Failure f
        end.
    End Scheduler.

  End InterpAction.

End Interp.

Section CPS.
  Definition action_interpreter A := forall (gamma: gamma_t) (log: log_t), A.
  Definition interp_continuation T A := result (option (gamma_t * log_t * list bool)) T -> A.
  Definition action_continuation T A := interp_continuation T A.
  Definition rule_continuation T A := result (option log_t) T -> A.
  Definition scheduler_continuation T A := result log_t T -> A.
  Definition cycle_continuation T A := result state_t T -> A.

  Definition interpreter T A := forall (log: result log_t T), A.

  Section InterpAction.
    Context (ext_sigma: ext_sigma_t).
    Context (int_fns: int_fn_env_t).
    Context (struct_defs: struct_env_t).

    Definition restore_gamma {A} (res: result (option (gamma_t * log_t * list bool)) A)
                             (gamma: gamma_t)
                             : result (option (gamma_t * log_t * list bool)) A :=
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
             (log: log_t) (a: action)
             {A} (k: action_continuation unit A)
    : action_interpreter A :=
      match fuel with
      | 0 => fun gamma l => k (Failure (__debug__ "Fn depth exceeded" tt))
      | S fuel =>
        let cps a {A} k := @interp_action_cps fuel max_fn_depth r log a A k in
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
            k (let sched_le := log_get log idx in
               if LE_may_read0 sched_le then
                 let/res v := r_get_reg r idx in
                 let action_le := log_get l idx in
                 let le' := LE_set_read0 action_le in
                 Success (Some (gamma, log_set l idx le', v))
               else Success None)
        | Read P1 idx =>
          fun k gamma l =>
            k (let/res v0 := r_get_reg r idx in
               let sched_le := log_get log idx in
               if LE_may_read1 sched_le then
                 let action_le := log_get l idx in
                 let le' := LE_set_read1 action_le in
                 let/res v :=
                     match action_le.(lwrite0), sched_le.(lwrite0) with
                     | Some v, _ => Success v
                     | _, Some v => Success v
                     | _, _ => Success v0
                     end in
                 Success (Some (gamma, log_set l idx le', v))
               else Success None
              )
        | Write P0 idx value =>
          fun k =>
            cps value (fun res =>
                         match res with
                         | Success (Some (gamma, l, v)) =>
                             k (let sched_le := log_get log idx in
                                let action_le := log_get l idx in
                                if LE_may_write0 sched_le && LE_may_write0 action_le then
                                  let le' := LE_set_write0 action_le v in
                                  Success (Some (gamma, log_set l idx le', []))
                                else Success None)
                         | _ => k res
                         end)
        | Write P1 idx value =>
          fun k =>
            cps value (fun res =>
                         match res with
                         | Success (Some (gamma, l, v)) =>
                             k (let sched_le := log_get log idx in
                                let action_le := log_get l idx in
                                if LE_may_write1 sched_le && LE_may_write1 action_le then
                                  let le' := LE_set_write1 action_le v in
                                  Success (Some (gamma, log_set l idx le', []))
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
                         k (let/res result := ext_sigma fn v in
                            Success (Some (gamma, l, result)))
                       | _ => k res
                       end)
        end k
      end.

    Definition rule := action.

    Definition interp_rule_cps (st: state_t) (rl: rule) {A} (k: rule_continuation unit A)
      : interpreter unit A :=
      fun L_res =>
        match L_res with
        | Success L =>
          interp_action_cps (safe_fuel int_fns (List.length int_fns) rl)
                            (List.length int_fns)
                            st L rl (fun res =>
                                       match res with
                                       | Success (Some (_, l, _)) => k (Success (Some l))
                                       | Success None => k (Success None)
                                       | Failure f => k (Failure f)
                                       end) GenericGammaEmpty log_empty
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
                                       | Success (Some l) => interp_scheduler'_cps s k (Success (log_app l L))
                                       | Success None  => interp_scheduler'_cps s k (Success L)
                                       | Failure f => k (Failure f)
                                       end) (Success L)
            | Failure f => k (Failure f)
            end
        end.


      Definition interp_scheduler_cps
                 (s: scheduler)
                 {A} (k: scheduler_continuation unit A) : A :=
        interp_scheduler'_cps s k (Success log_empty).

      Definition interp_cycle_cps (s: scheduler)
                 {A} (k: cycle_continuation unit A) : A :=
        interp_scheduler_cps s (fun res_L => k (let/res L := res_L in
                                               Success (commit_update r L))).


    End Scheduler.

    Definition action_precondition := action_interpreter Prop.
    Definition action_postcondition := action_continuation unit Prop.
    Definition precondition := interpreter unit Prop.
    Definition rule_postcondition := rule_continuation unit Prop.
    Definition scheduler_postcondition := scheduler_continuation unit Prop.
    Definition cycle_postcondition := cycle_continuation unit Prop.

    Definition wp_action (fuel: nat) (fn_depth: nat) (r: state_t) (L: log_t) (a: action)
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
  Definition action_interpreter2 A := forall (gamma1: gamma_t) (log1: log_t) (gamma2: gamma_t) (log2: log_t), A.
  Definition interp_continuation2 T A :=
    result (option (gamma_t * log_t * list bool)) T ->
    result (option (gamma_t * log_t * list bool)) T ->
    A.

  Definition action_continuation2 T A := interp_continuation2 T A.
  Definition rule_continuation2 T A := result (option log_t) T -> result (option log_t) T -> A.
  Definition scheduler_continuation2 T A := result log_t T -> result log_t T -> A.
  Definition cycle_continuation2 T A := result state_t T -> result state_t T -> A.

  Definition interpreter2 T A := forall (log1 log2: result log_t T), A.

End CPS2.

Section TypecheckedInterp.

    Section InterpAction.
      Context (ext_sigma: ext_sigma_t).
      Context (int_fns: int_fn_env_t).
      Context (struct_defs: struct_env_t).

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

      Definition unsafe_read1 (action_log: log_t) (sched_log: log_t) (r: state_t) (reg: reg_t) : list bool :=
        let sched_le := log_get sched_log reg in
        let action_le := log_get action_log reg in
        match action_le.(lwrite0), sched_le.(lwrite0) with
        | Some v, _ => v
        | _, Some v => v
        | _, _ => unsafe_r_get_reg r reg
        end.

      Fixpoint unsafe_interp_action
               (fuel: nat)
               (r: state_t)
               (gamma: gamma_t)
               (sched_log: log_t)
               (action_log: log_t)
               (a: action)
               : option (gamma_t * log_t * list bool) :=
        let __debug__ {A} (v: A) := __debug__ v tt in
        match fuel with
        | 0 => None
        | S fuel =>
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
              let sched_le := log_get sched_log idx in
              let action_le := log_get action_log idx in
              if LE_may_read0 sched_le then
                let le' := {|lread0 := true; lread1 := action_le.(lread1);
                             lwrite0 := action_le.(lwrite0); lwrite1 := action_le.(lwrite1) |} in
                Some (gamma, log_set action_log idx le', unsafe_r_get_reg r idx)
              else None
          | Read P1 idx =>
              let sched_le := log_get sched_log idx in
              let action_le := log_get action_log idx in
              if LE_may_read1 sched_le then
                let le' := {| lread0 := action_le.(lread0); lread1 := true;
                              lwrite0 := action_le.(lwrite0); lwrite1 := action_le.(lwrite1) |} in
                let v := unsafe_read1 action_log sched_log r idx in
                Some (gamma, log_set action_log idx le', v)
              else None
          | Write P0 idx value =>
              let/opt3 gamma, action_log, v_value := unsafe_interp_action fuel r gamma sched_log action_log value in
              let sched_le := log_get sched_log idx in
              let action_le := log_get action_log idx in
              if LE_may_write0 sched_le && LE_may_write0 action_le then
                let le' := {| lread0 := action_le.(lread0);
                              lread1 := action_le.(lread1);
                              lwrite0 := Some v_value;
                              lwrite1 := action_le.(lwrite1) |} in
                Some (gamma, log_set action_log idx le', [])
              else None
          | Write P1 idx value =>
              let/opt3 gamma, action_log, v_value := unsafe_interp_action fuel r gamma sched_log action_log value in
              let sched_le := log_get sched_log idx in
              let action_le := log_get action_log idx in
              if LE_may_write1 sched_le && LE_may_write1 action_le then
                let le' := {| lread0 := action_le.(lread0);
                              lread1 := action_le.(lread1);
                              lwrite0 := action_le.(lwrite0);
                              lwrite1 := Some v_value |} in
                Some (gamma, log_set action_log idx le', [])
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
            Some (gamma, action_log, unsafe_call_ext fn v)
          | InternalCall fn arg =>
            let/opt3 gamma, action_log, v_arg := unsafe_interp_action fuel r gamma sched_log action_log arg in
            let '(arg_name, body) := unsafe_get_fn_arg_and_body fn in
            let/opt3 _, action_log, res :=
                 unsafe_interp_action fuel r (fn_gamma arg_name v_arg)
                               sched_log action_log body in
              Some (gamma, action_log, res)
          end
        end.

      Definition unsafe_interp_rule (st: state_t) (sched_log: log_t) (rl: rule)
        : option log_t :=
        match unsafe_interp_action (safe_fuel int_fns (List.length int_fns) rl)
                            st GenericGammaEmpty sched_log log_empty rl with
        | Some (_, l, _) => (Some l)
        | None => None
        end.

    Section Scheduler.
      Context {rule_name_t: Type}.
      Context (r: state_t).
      Context (rules: rule_name_t -> rule).

      Fixpoint unsafe_interp_scheduler' (s: scheduler) (sched_log: log_t) : log_t :=
        match s with
        | Done => sched_log
        | Cons rl s =>
          let opt_action_log := unsafe_interp_rule r sched_log (rules rl) in
          match opt_action_log with
          | Some action_log => unsafe_interp_scheduler' s (log_app action_log sched_log)
          | None => unsafe_interp_scheduler' s sched_log
          end
        end.

      Definition unsafe_interp_scheduler (s: scheduler) : log_t :=
        unsafe_interp_scheduler' s log_empty.

      Definition unsafe_interp_cycle (s: scheduler) : state_t :=
        commit_update r (unsafe_interp_scheduler s).
    End Scheduler.

  End InterpAction.

End TypecheckedInterp.

(* Section OnlyDynamicFailInterp. *)
(*   Context (ext_sigma: ext_sigma_t). *)
(*   Context (int_fns: int_fn_env_t). *)
(*   Context (struct_defs: struct_env_t). *)

(*   Fixpoint odf_interp_action *)
(*            (fuel: nat) *)
(*            (r: state_t) *)
(*            (gamma: gamma_t) *)
(*            (sched_log: log_t) *)
(*            (action_log: log_t) *)
(*            (a: action) *)
(*            : option (gamma_t * log_t * list bool) := *)
(*     let __debug__ {A} (v: A) := __debug__ v tt in *)
(*     match fuel with *)
(*     | 0 => None *)
(*     | S fuel => *)
(*       match a with *)
(*       | Fail ty_hint => None *)
(*       | Var var => Some (gamma, action_log, unsafe_varenv_lookup_var gamma var) *)
(*       | Const cst => Some (gamma, action_log, cst) *)
(*       | Assign var ex => *)
(*         let/opt3 gamma, action_log, v_ex := odf_interp_action fuel r gamma sched_log action_log ex in *)
(*         Some (gamma_set gamma var v_ex, action_log, []) *)
(*       | Seq a1 a2 => *)
(*         let/opt3 gamma, action_log, v1 := odf_interp_action fuel r gamma sched_log action_log a1 in *)
(*         odf_interp_action fuel r gamma sched_log action_log a2 *)
(*       | If cond tbranch fbranch => *)
(*         let/opt3 gamma, action_log, v_cond := odf_interp_action fuel r gamma sched_log action_log cond in *)
(*         match v_cond with *)
(*         | [true] => odf_interp_action fuel r gamma sched_log action_log tbranch *)
(*         | _ (* [false] *) => odf_interp_action fuel r gamma sched_log action_log fbranch *)
(*         end *)
(*       | Bind var ex body => *)
(*          let/opt3 gamma, action_log, v_ex := odf_interp_action fuel r gamma sched_log action_log ex in *)
(*          let/opt3 gamma', action_log, v_body := *)
(*             odf_interp_action fuel r (gamma_set gamma var v_ex) sched_log action_log body in *)
(*          Some (gamma, action_log, v_body) *)
(*       | Read P0 idx => *)
(*           let sched_le := log_get sched_log idx in *)
(*           let action_le := log_get action_log idx in *)
(*           let le' := LE_set_read0 action_le in *)
(*           Some (gamma, log_set action_log idx le', unsafe_r_get_reg r idx) *)
(*       | Read P1 idx => *)
(*           let sched_le := log_get sched_log idx in *)
(*           let action_le := log_get action_log idx in *)
(*           let le' := LE_set_read1 action_le in *)
(*           let v := unsafe_read1 action_log sched_log r idx in *)
(*           Some (gamma, log_set action_log idx le', v) *)
(*       | Write P0 idx value => *)
(*           let/opt3 gamma, action_log, v_value := odf_interp_action fuel r gamma sched_log action_log value in *)
(*           let sched_le := log_get sched_log idx in *)
(*           let action_le := log_get action_log idx in *)
(*           let le' := LE_set_write0 action_le v_value in *)
(*           Some (gamma, log_set action_log idx le', []) *)
(*       | Write P1 idx value => *)
(*           let/opt3 gamma, action_log, v_value := odf_interp_action fuel r gamma sched_log action_log value in *)
(*           let sched_le := log_get sched_log idx in *)
(*           let action_le := log_get action_log idx in *)
(*           let le' := LE_set_write1 action_le v_value in *)
(*           Some (gamma, log_set action_log idx le', []) *)
(*       | Zop fn => *)
(*         Some (gamma, action_log, unsafe_interp_zop struct_defs fn) *)
(*       | Unop fn arg1 => *)
(*         let/opt3 gamma, action_log, v1 := odf_interp_action fuel r gamma sched_log action_log arg1 in *)
(*         Some (gamma, action_log, unsafe_interp_unop struct_defs fn v1) *)
(*       | Binop fn arg1 arg2 => *)
(*         let/opt3 gamma, action_log, v1 := odf_interp_action fuel r gamma sched_log action_log arg1 in *)
(*         let/opt3 gamma, action_log, v2 := odf_interp_action fuel r gamma sched_log action_log arg2 in *)
(*         let result := unsafe_interp_binop struct_defs fn v1 v2 in *)
(*         Some (gamma, action_log, result) *)
(*       | ExternalCall fn arg => *)
(*         let/opt3 gamma, action_log, v := odf_interp_action fuel r gamma sched_log action_log arg in *)
(*         Some (gamma, action_log, unsafe_call_ext ext_sigma fn v) *)
(*       | InternalCall fn arg => *)
(*         let/opt3 gamma, action_log, v_arg := odf_interp_action fuel r gamma sched_log action_log arg in *)
(*         let '(arg_name, body) := unsafe_get_fn_arg_and_body int_fns fn in *)
(*         let/opt3 _, action_log, res := *)
(*              odf_interp_action fuel r (fn_gamma arg_name v_arg) *)
(*                            sched_log action_log body in *)
(*           Some (gamma, action_log, res) *)
(*       end *)
(*     end. *)

(*   Definition odf_interp_rule (st: state_t) (sched_log: log_t) (rl: rule) *)
(*     : option log_t := *)
(*     match odf_interp_action (safe_fuel int_fns (List.length int_fns) rl) *)
(*                         st GenericGammaEmpty sched_log log_empty rl with *)
(*     | Some (_, l, _) => (Some l) *)
(*     | None => None *)
(*     end. *)

(*   Section Scheduler. *)
(*     Context {rule_name_t: Type}. *)
(*     Context (r: state_t). *)
(*     Context (rules: rule_name_t -> rule). *)

(*     Fixpoint odf_interp_scheduler' (s: scheduler) (sched_log: log_t) : log_t := *)
(*       match s with *)
(*       | Done => sched_log *)
(*       | Cons rl s => *)
(*         let opt_action_log := odf_interp_rule r sched_log (rules rl) in *)
(*         match opt_action_log with *)
(*         | Some action_log => odf_interp_scheduler' s (log_app action_log sched_log) *)
(*         | None => odf_interp_scheduler' s sched_log *)
(*         end *)
(*       end. *)

(*     Definition odf_interp_scheduler (s: scheduler) : log_t := *)
(*       odf_interp_scheduler' s log_empty. *)

(*     Definition odf_interp_cycle (s: scheduler) : state_t := *)
(*       commit_update r (odf_interp_scheduler s). *)
(*   End Scheduler. *)

(* End OnlyDynamicFailInterp. *)
Section OneRuleAtATime.
  Context (ext_sigma: ext_sigma_t).
  Context (int_fns: int_fn_env_t).
  Context (struct_defs: struct_env_t).


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

  Notation "'let/bopt' b ',' v1 ':=' expr 'in' body" :=
    (match expr with
     | (b, Some v1) => body
     | (b, None) => (b, None)
     end) (at level 200).

  Notation "'let/bopt2' b ',' v1 ',' v2 ':=' expr 'in' body" :=
    (match expr with
     | (b, Some (v1, v2)) => body
     | (b, None) => (b, None)
     end) (at level 200).

  Notation "'let/bopt3' b ',' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
    (match expr with
     | (b, Some (v1, v2, v3)) => body
     | (b, None) => (b, None)
     end) (at level 200).


  Fixpoint oraat_interp_action
           (fuel: nat)
           (r: state_t)
           (r_acc: state_t)
           (is_safe: bool)
           (gamma: gamma_t)
           (a: action)
           : bool * option (gamma_t * state_t * list bool) :=
    match fuel with
    | 0 => (__debug__ "Out of fuel" false, None)
    | S fuel =>
      match a with
      | Fail ty_hint => (is_safe, None)
      | Var var =>
          let '(safe, v) := varenv_lookup_var' gamma var in
          (is_safe && safe, Some (gamma, r_acc, v))
      | Const cst => (is_safe, (Some (gamma, r_acc, cst)))
      | Assign var ex =>
          let/bopt3 is_safe, gamma, r_acc, v_ex := oraat_interp_action fuel r r_acc is_safe gamma ex in
          let is_safe' := is_success (varenv_lookup_var gamma var tt) in
          (is_safe && is_safe', Some (varenv_update gamma var v_ex, r_acc, []))
      | Seq a1 a2 =>
        let/bopt3 is_safe, gamma, r_acc, v1 := oraat_interp_action fuel r r_acc is_safe gamma a1 in
        oraat_interp_action fuel r r_acc is_safe gamma a2
      | If cond tbranch fbranch =>
        let/bopt3 is_safe, gamma, r_acc, v_cond := oraat_interp_action fuel r r_acc is_safe gamma cond in
        let is_safe := ((Nat.eqb (Datatypes.length v_cond) 1) && is_safe) in
        if bits_eq v_cond [true] then
          oraat_interp_action fuel r r_acc is_safe gamma tbranch
        else
          oraat_interp_action fuel r r_acc is_safe gamma fbranch
     | Bind var ex body =>
        let/bopt3 is_safe, gamma, r_acc, v_ex := oraat_interp_action fuel r r_acc is_safe gamma ex in
        let/bopt3 is_safe, gamma', r_acc, v_body := oraat_interp_action fuel r r_acc is_safe (varenv_bind gamma var v_ex) body in
        (is_safe, Some (tl gamma', r_acc, v_body))
      | Read P0 idx =>
        let '(safe, v) := r_get_reg' r idx in
        (is_safe && safe, Some (gamma, r_acc, v))
      | Read P1 idx =>
        let '(safe, v) := r_get_reg' r_acc idx in
        (is_safe && safe, Some (gamma, r_acc, v))
      | Write _ idx value =>
        let/bopt3 is_safe, gamma, r_acc, v_value := oraat_interp_action fuel r r_acc is_safe gamma value in
        (is_safe, Some (gamma, state_set r_acc idx v_value, []))
      | Zop fn =>
        let '(safe, v) := interp_zop' fn in
        (is_safe && safe, Some (gamma, r_acc, v))
      | Unop fn arg1 =>
        let/bopt3 is_safe, gamma, r_acc, v_arg1 := oraat_interp_action fuel r r_acc is_safe gamma arg1 in
        let '(safe, v) := interp_unop' fn v_arg1 in
        (is_safe && safe, Some (gamma, r_acc, v))
      | Binop fn arg1 arg2 =>
        let/bopt3 is_safe, gamma, r_acc, v_arg1 := oraat_interp_action fuel r r_acc is_safe gamma arg1 in
        let/bopt3 is_safe, gamma, r_acc, v_arg2 := oraat_interp_action fuel r r_acc is_safe gamma arg2 in
        let '(safe, v) := interp_binop' fn v_arg1 v_arg2 in
        (is_safe && safe, Some (gamma, r_acc, v))
      | ExternalCall fn arg =>
        let/bopt3 is_safe, gamma, r_acc, v_arg := oraat_interp_action fuel r r_acc is_safe gamma arg in
        let '(safe, v) := call_ext' fn v_arg in
        (is_safe && safe, Some (gamma, r_acc, v))
      | InternalCall fn arg =>
        let/bopt3 is_safe, gamma, r_acc, v_arg := oraat_interp_action fuel r r_acc is_safe gamma arg in
        let '(safe, (arg_name, body)) := get_fn_arg_and_body' fn in
        let is_safe := safe && is_safe in
        let/bopt3 is_safe, _, r_acc, res :=
           oraat_interp_action fuel r r_acc is_safe (fn_gamma arg_name v_arg) body in
        (is_safe, Some (gamma, r_acc, res))
      end
    end.

  Definition oraat_interp_rule (st: state_t) (rl: rule) : bool * state_t :=
    match oraat_interp_action (safe_fuel int_fns (List.length int_fns) rl)
                              st st true GenericGammaEmpty rl with
    | (is_safe, Some (_, st', _)) => (is_safe, st')
    | (is_safe, None) => (is_safe, st)
    end.

  Section Scheduler.
    Context {rule_name_t: Type}.
    Context (rules: rule_name_t -> rule).

    Fixpoint oraat_interp_scheduler' (st: state_t) (is_safe: bool) (s: scheduler)  : bool * state_t :=
      match s with
      | Done => (is_safe, st)
      | Cons rl s =>
        let '(is_safe', st') := oraat_interp_rule st (rules rl) in
        oraat_interp_scheduler' st' (is_safe && is_safe') s
      end.

    Definition oraat_interp_scheduler (st: state_t) (s: scheduler) : bool * state_t :=
      oraat_interp_scheduler' st true s.

    Definition unsafe_oraat_interp_cycle (st: state_t) (s: scheduler) : state_t :=
      snd (oraat_interp_scheduler st s).

  End Scheduler.

  Definition oraat_interp_rule2 (st1 st2: state_t) (rl: rule) : bool * state_t * state_t :=
    let '(is_safe1, st1') := oraat_interp_rule st1 rl in
    let '(is_safe2, st2') := oraat_interp_rule st2 rl in
    (is_safe1 && is_safe2, st1', st2).


  Section CPS.
    Definition oraat_action_interpreter A := forall (gamma: gamma_t) (st': state_t) (is_safe: bool), A.
    Definition oraat_interp_continuation A := bool * (option (gamma_t * state_t * list bool)) -> A.
    Definition oraat_action_continuation A := oraat_interp_continuation A.
    Definition oraat_rule_continuation A := bool * state_t -> A.
    Definition oraat_scheduler_continuation A := bool * state_t  -> A.
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
        | 0 => fun gamma r_acc is_safe => k (__debug__ "Out of fuel" false, None)
        | S fuel =>
         let cps a {A} k := @oraat_interp_action_cps fuel r a A k in
         match a with
         | Fail ty_hint => fun k gamma r_acc is_safe => k (is_safe, None)
         | Var var =>
           fun k gamma r_acc is_safe =>
             k (let '(safe, v) := varenv_lookup_var' gamma var in
                (is_safe && safe, Some (gamma, r_acc, v)))
         | Const cst =>
           fun k gamma r_acc is_safe =>
             k (is_safe, (Some (gamma, r_acc, cst)))
         | Assign var ex =>
           fun k => cps ex (fun res =>
                           k (let/bopt3 is_safe, gamma, r_acc, v_ex := res in
                              let is_safe' := is_success (varenv_lookup_var gamma var tt) in
                              (is_safe && is_safe', Some (varenv_update gamma var v_ex, r_acc, []))))
         | Seq a1 a2 =>
           fun k => cps a1 (fun res =>
                           match res with
                           | (is_safe, Some (gamma, r_acc, v_ex)) =>
                             cps a2 k gamma r_acc is_safe
                           | _ => k res
                           end)
        | If cond tbranch fbranch =>
          fun k =>
            cps cond (fun res =>
                        match res with
                        | (is_safe, Some (gamma, r_acc, v_cond)) =>
                          let is_safe := ((Nat.eqb (Datatypes.length v_cond) 1) && is_safe)in
                          if bits_eq v_cond [true] then
                            cps tbranch k gamma r_acc is_safe
                          else cps fbranch k gamma r_acc is_safe
                        | _ => k res
                        end)
        | Bind var ex body =>
          fun k => cps ex (fun res =>
                          match res with
                          | (is_safe, Some (gamma, r_acc, v_ex)) =>
                            cps body (fun res =>
                                        k (let/bopt3 is_safe, gamma', r_acc, v := res in
                                           (is_safe, Some (tl gamma', r_acc, v))))
                                (varenv_bind gamma var v_ex) r_acc is_safe
                          | _ => k res
                          end)
         | Read P0 idx =>
           fun k gamma r_acc is_safe =>
             k (let '(safe, v) := r_get_reg' r idx in
                (is_safe && safe, Some (gamma, r_acc, v)))
         | Read P1 idx =>
           fun k gamma r_acc is_safe =>
             k ( let '(safe, v) := r_get_reg' r_acc idx in
                 (is_safe && safe, Some (gamma, r_acc, v)))
         | Write _ idx value =>
           fun k =>
             cps value (fun res =>
                          match res with
                          | (is_safe, Some (gamma, r_acc, v_value)) =>
                            k (is_safe, Some (gamma, state_set r_acc idx v_value, []))
                          | _ => k res
                          end)
        | Zop fn =>
           fun k gamma r_acc is_safe =>
            k (let '(safe, v) := interp_zop' fn in
               (is_safe && safe, Some (gamma, r_acc, v)))
        | Unop fn arg1 =>
          fun k =>
            cps arg1 (fun res =>
                      match res with
                      | (is_safe, Some (gamma, r_acc, v_arg1)) =>
                        k (let '(safe, v) := interp_unop' fn v_arg1 in
                           (is_safe && safe, Some (gamma, r_acc, v)))
                      | _ => k res
                      end)
        | Binop fn arg1 arg2 =>
          fun k =>
            cps arg1 (fun res =>
                        match res with
                        | (is_safe, Some (gamma, r_acc, v_arg1)) =>
                          cps arg2 (fun res =>
                                      match res with
                                      | (is_safe, Some (gamma, r_acc, v_arg2)) =>
                                        k (let '(safe, v) := interp_binop' fn v_arg1 v_arg2 in
                                           (is_safe && safe, Some (gamma, r_acc, v)))
                                      | _ => k res
                                      end) gamma r_acc is_safe
                        | _ => k res
                        end)
        | ExternalCall fn arg =>
          fun k => cps arg (fun res =>
                           match res with
                           | (is_safe, Some (gamma, r_acc, v_arg)) =>
                             k (let '(safe, v) := call_ext' fn v_arg in
                                (is_safe && safe, Some (gamma, r_acc, v)))
                           | _ => k res
                           end)
        | InternalCall fn arg =>
          fun k => cps arg (fun res =>
                           match res with
                           | (is_safe, Some (gamma, r_acc, v_arg)) =>
                             let '(safe, (arg_name, body)) := get_fn_arg_and_body' fn in
                             let is_safe := safe && is_safe in
                             cps body (fun res =>
                                         match res with
                                         | (is_safe, Some (_, r_acc, v)) =>
                                           k (is_safe, Some (gamma, r_acc, v))
                                         | _ => k res
                                         end) (fn_gamma arg_name v_arg) r_acc is_safe
                           | _ => k res
                           end)
         end k
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

(* Section OneRuleAtATime2. *)
(*   Context (ext_sigma1 ext_sigma2: ext_sigma_t). *)
(*   Context (int_fns: int_fn_env_t). *)
(*   Context (struct_defs: struct_env_t). *)

(*   Inductive action2 := *)
(*   | Lockstep (a: action) *)
(*   | Alive1 (a: action) *)
(*   | Alive2 (a: action). *)

(*   Fixpoint oraat_interp_action2 *)
(*            (fuel: nat) *)
(*            (r1 r_acc1 r2 r_acc2: state_t) *)
(*            (is_safe: bool) *)
(*            (gamma1 gamma2: gamma_t) *)
(*            (a: action2) *)
(*            : bool * option (gamma_t * state_t * list bool) * option (gamma_t * state_t * list bool) := *)
(*     match fuel with *)
(*     | 0 => (__debug__ "Out of fuel" false, None, None) *)
(*     | S fuel => *)
(*       match a with *)
(*       | Lockstep a => *)
(*         match a with *)
(*         | Fail ty_hint => (is_safe, None, None) *)
(*         | Var var => *)
(*             let '(safe1, v1) := varenv_lookup_var' gamma1 var in *)
(*             let '(safe2, v2) := varenv_lookup_var' gamma2 var in *)
(*             (is_safe && safe1 && safe2, Some (gamma1, r_acc1, v1), Some (gamma2, r_acc2, v2)) *)
(*         | Const cst => (is_safe, (Some (gamma1, r_acc1, cst)), (Some (gamma2, r_acc2, cst))) *)
(*         | Assign var ex => *)
(*             let '(is_safe, res1, res2) := oraat_interp_action2 fuel r1 r_acc1 r2 r_acc2 is_safe gamma1 gamma2 (Lockstep ex) in *)
(*             let res1' := let/opt3 gamma1, r_acc1, v_ex1 := res1 in *)
(*                          Some (varenv_update gamma1 var v_ex1, r_acc1, []) in *)
(*             let res2' := let/opt3 gamma2, r_acc2, v_ex2 := res2 in *)
(*                          Some (varenv_update gamma2 var v_ex2, r_acc2, []) in *)
(*             (is_safe, res1', res2') *)
(*         | Seq a1 a2 => *)
(*             let '(is_safe, res1, res2) := oraat_interp_action2 fuel r1 r_acc1 r2 r_acc2 is_safe gamma1 gamma2 (Lockstep a1) in *)
(*             match res1, res2 with *)
(*             | Some (gamma1, r_acc1, _), Some (gamma2, r_acc2, _) => *)

(*                 oraat_interp_action2 fuel r1 r_acc1 r2 r_acc2 is_safe gamma1 gamma2 (Lockstep a2) *)
(*             | Some (gamma1, r_acc1, _), None => *)
(*                 oraat_interp_action2 fuel r1 r_acc1 r2 r_acc2 is_safe gamma1 gamma2 (Alive1 a2) *)
(*             | None, Some (gamma2, r_acc2, _) => *)
(*                 oraat_interp_action2 fuel r1 r_acc1 r2 r_acc2 is_safe gamma1 gamma2 (Alive2 a2) *)
(*             | None, None => (is_safe, None, None) *)
(*             end *)
(*         | Bind var ex body => *)
(*            let '(is_safe, res1, res2) := oraat_interp_action2 fuel r1 r_acc1 r2 r_acc2 is_safe gamma1 gamma2 (Lockstep ex) in *)
(*            let '(is_safe, res1, res2) := *)
(*              match res1, res2 with *)
(*              | Some (gamma1, r_acc1, v_ex1), Some (gamma2, r_acc2, v_ex2) => *)
(*                  oraat_interp_action2 fuel r1 r_acc1 r2 r_acc2 is_safe *)
(*                    (varenv_bind gamma1 var v_ex1) (varenv_bind gamma2 var v_ex2) (Lockstep body) *)
(*              | Some (gamma1, r_acc1, v_ex1), None => *)
(*                  oraat_interp_action2 fuel r1 r_acc1 r2 r_acc2 is_safe *)
(*                    (varenv_bind gamma1 var v_ex1) gamma2 (Alive1 body) *)
(*              | None, Some (gamma2, r_acc2, v_ex2) => *)
(*                  oraat_interp_action2 fuel r1 r_acc1 r2 r_acc2 is_safe gamma1 *)
(*                    (varenv_bind gamma2 var v_ex2) (Alive2 body) *)
(*              | None, None => (is_safe, None, None) *)
(*              end in *)
(*            (is_safe, let/opt3 gamma1, r_acc1, v_body1 := res1 in Some (tl gamma1, r_acc1, v_body1), *)
(*                        let/opt3 gamma2, r_acc2, v_body2 := res2 in Some (tl gamma2, r_acc2, v_body2)) *)
(*         | Read P0 idx => *)
(*           let '(safe1, v1) := r_get_reg' r1 idx in *)
(*           let '(safe2, v2) := r_get_reg' r2 idx in *)
(*           (is_safe && safe1 && safe2, Some (gamma1, r_acc1, v1), Some (gamma2, r_acc2, v2)) *)
(*         | Write _ idx value => *)
(*             let '(is_safe, res1, res2) := oraat_interp_action2 fuel r1 r_acc1 r2 r_acc2 is_safe gamma1 gamma2 (Lockstep value) in *)
(*             let res1' := let/opt3 gamma1, r_acc1, v_value1 := res1 in *)
(*                          Some (gamma1, state_set r_acc1 idx v_value1, []) in *)
(*             let res2' := let/opt3 gamma2, r_acc2, v_value2 := res2 in *)
(*                          Some (gamma2, state_set r_acc2 idx v_value2, []) in *)
(*             (is_safe, res1', res2') *)
(*         | Zop fn => *)
(*           let '(safe, v) := interp_zop' struct_defs fn in *)
(*           (is_safe && safe, Some (gamma1, r_acc1, v), Some (gamma2, r_acc2, v)) *)
(*         | Unop fn arg1 => *)
(*             let '(is_safe, res1, res2) := oraat_interp_action2 fuel r1 r_acc1 r2 r_acc2 is_safe gamma1 gamma2 (Lockstep arg1) in *)
(*             let (safe1, res1') := match res1 with *)
(*                                   | Some (gamma1, r_acc1, v_value1) =>  *)
(*                                       interp_unop' fn arg1 *)
(*                                   | None => *)
(*                                   end  *)
(* let/bopt3 gamma1, r_acc1, v_value1 := (res1 in *)
(*                                   Some (gamma1, state_set r_acc1 idx v_value1, []) in *)
(*             let res2' := let/opt3 gamma2, r_acc2, v_value2 := res2 in *)
(*                          Some (gamma2, state_set r_acc2 idx v_value2, []) in *)
(*             (is_safe, res1', res2') *)

(*           let/bopt3 is_safe, gamma, r_acc, v_arg1 := oraat_interp_action fuel r r_acc is_safe gamma arg1 in *)
(*           let '(safe, v) := interp_unop' fn v_arg1 in *)
(*           (is_safe && safe, Some (gamma, r_acc, v)) *)
(*         | _ => (__debug__ "TODO" false, None, None) *)
(*         end *)
(*       | Alive1 a => *)
(*           let '(is_safe, res1) := oraat_interp_action ext_sigma1 int_fns struct_defs fuel *)
(*                                                       r1 r_acc1 is_safe gamma1 a in *)
(*           (is_safe, res1, None) *)
(*       | Alive2 a => *)
(*           let '(is_safe, res2) := oraat_interp_action ext_sigma2 int_fns struct_defs fuel *)
(*                                                       r2 r_acc2 is_safe gamma2 a in *)
(*           (is_safe, res2, None) *)
(*       end *)
(*    end. *)

(*       | If cond tbranch fbranch => *)
(*         let/bopt3 is_safe, gamma, r_acc, v_cond := oraat_interp_action fuel r r_acc is_safe gamma cond in *)
(*         let is_safe := ((Nat.eqb (Datatypes.length v_cond) 1) && is_safe) in *)
(*         if bits_eq v_cond [true] then *)
(*           oraat_interp_action fuel r r_acc is_safe gamma tbranch *)
(*         else *)
(*           oraat_interp_action fuel r r_acc is_safe gamma fbranch *)
(*       | Binop fn arg1 arg2 => *)
(*         let/bopt3 is_safe, gamma, r_acc, v_arg1 := oraat_interp_action fuel r r_acc is_safe gamma arg1 in *)
(*         let/bopt3 is_safe, gamma, r_acc, v_arg2 := oraat_interp_action fuel r r_acc is_safe gamma arg2 in *)
(*         let '(safe, v) := interp_binop' fn v_arg1 v_arg2 in *)
(*         (is_safe && safe, Some (gamma, r_acc, v)) *)
(*       | ExternalCall fn arg => *)
(*         let/bopt3 is_safe, gamma, r_acc, v_arg := oraat_interp_action fuel r r_acc is_safe gamma arg in *)
(*         let '(safe, v) := call_ext' fn v_arg in *)
(*         (is_safe && safe, Some (gamma, r_acc, v)) *)
(*       | InternalCall fn arg => *)
(*         let/bopt3 is_safe, gamma, r_acc, v_arg := oraat_interp_action fuel r r_acc is_safe gamma arg in *)
(*         let '(safe, (arg_name, body)) := get_fn_arg_and_body' fn in *)
(*         let is_safe := safe && is_safe in *)
(*         let/bopt3 is_safe, _, r_acc, res := *)
(*            oraat_interp_action fuel r r_acc is_safe (fn_gamma arg_name v_arg) body in *)
(*         (is_safe, Some (gamma, r_acc, res)) *)
(*       end *)
(*     end. *)

(* End OneRuleAtATime2. *)
