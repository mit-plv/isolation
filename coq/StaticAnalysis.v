Require Import Koika.Common.
Require Import Koika.Utils.
Require Import Koika.Syntax.
Require Import Koika.Semantics.
Require Import Koika.Environments.
Require Import Koika.Typechecking.
Require Import Koika.Tactics.
Require Import Koika.Bits.

Section TaintAnalysis.
  Record taint_t :=
    { taint_read0 : bool;
      taint_read1: bool;
      taint_write0: bool;
      taint_write1: bool;
    }.

  Definition empty_taint : taint_t :=
    {| taint_read0 := false;
       taint_read1 := false;
       taint_write0 := false;
       taint_write1 := false
    |}.

  Definition set_taint_read0 (t: taint_t) : taint_t :=
    {| taint_read0 := true;
       taint_read1 := t.(taint_read1);
       taint_write0 := t.(taint_write0);
       taint_write1 := t.(taint_write1);
    |}.

  Definition set_taint_read1 (t: taint_t) : taint_t :=
    {| taint_read0 := t.(taint_read0);
       taint_read1 := true;
       taint_write0 := t.(taint_write0);
       taint_write1 := t.(taint_write1);
    |}.

  Definition set_taint_write0 (t: taint_t) : taint_t :=
    {| taint_read0 := t.(taint_read0);
       taint_read1 := t.(taint_read1);
       taint_write0 := true;
       taint_write1 := t.(taint_write1);
    |}.

  Definition set_taint_write1 (t: taint_t) : taint_t :=
    {| taint_read0 := t.(taint_read0);
       taint_read1 := t.(taint_read1);
       taint_write0 := t.(taint_write0);
       taint_write1 := true;
    |}.

  (* if not in taint_env, assume empty. *)
  Definition taint_env_t := @SortedRegEnv.EnvT taint_t.

  Definition get_reg_taint_default (env: taint_env_t) (reg: reg_t) : taint_t :=
    match SortedRegEnv.opt_get env reg with
    | Some t => t
    | None => empty_taint
    end.

  Definition set_reg_taint (env: taint_env_t) (reg: reg_t) (fn: taint_t -> taint_t) : taint_env_t :=
    SortedRegEnv.update env reg fn (empty_taint).

  Definition conflicts_with_read0 (t: taint_t) : bool :=
    t.(taint_write0) || t.(taint_write1).

  Definition conflicts_with_read1 (t: taint_t) : bool :=
    t.(taint_write1).

  Definition conflicts_with_write0 (t: taint_t) : bool :=
    t.(taint_read1) || t.(taint_write0) || t.(taint_write1).

  Definition conflicts_with_write1 (t: taint_t) : bool :=
    t.(taint_write1).

  Definition taint_conflicts (t1 t2: taint_t) : bool :=
    (t2.(taint_read0) && (conflicts_with_read0 t1)) ||
    (t2.(taint_read1) && (conflicts_with_read1 t1)) ||
    (t2.(taint_write0) && (conflicts_with_write0 t1)) ||
    (t2.(taint_write1) && (conflicts_with_write1 t1)).

  Definition merge_taints (t1 t2: taint_t) : taint_t :=
    {| taint_read0 := t1.(taint_read0) || t2.(taint_read0);
       taint_read1 := t1.(taint_read1) || t2.(taint_read1);
       taint_write0 := t1.(taint_write0) || t2.(taint_write0);
       taint_write1 := t1.(taint_write1) || t2.(taint_write1)
    |}.

  Definition does_not_conflict (env1: taint_env_t) (env2: taint_env_t) : bool :=
    let zipped := SortedRegEnv.zip_default env1 env2 empty_taint empty_taint in
    forallb (fun '(r, (t1, t2)) => (negb (taint_conflicts t1 t2))) (SortedRegEnv.to_list zipped).


  (* (* Semantics: *)
  (*    - shouldn't write1 then read1 that write *)
  (*  *) *)
  (* Definition no_internal_rule_conflict (env: taint_env_t) : bool := *)
  (*   forallb (fun '(r, t) => (negb t.(taint_write1) || negb t.(taint_read1)) && *)
  (*                        (negb t.(taint_write0) && ()) *)
  (*           ) (SortedRegEnv.to_list env). *)

  Definition merge_taint_env (env1: taint_env_t) (env2: taint_env_t) : taint_env_t :=
    let zipped := SortedRegEnv.zip_default env1 env2 empty_taint empty_taint in
    SortedRegEnv.mapV (fun '(t1,t2) => merge_taints t1 t2) zipped.

  Section Interp.
    Context (int_fns: int_fn_env_t).

    (* - failure if out of fuel
       - Success None if may internally conflict
       - Success (Some taint) if guaranteed to not internally conflict and taint is a safe approximation *)
    Fixpoint taint_action (fuel: nat)
             (taint: taint_env_t)
             (a: action)
      : result (option taint_env_t) unit :=
      match fuel with
      | 0 => Failure (__debug__ "Out of fuel" tt)
      | S fuel =>
        let taint_action := taint_action fuel in
        match a with
        | Fail _ => Success (Some taint)
        | Var _ => Success (Some taint)
        | Const _ => Success (Some taint)
        | Assign _ ex => taint_action taint ex
        | Seq a1 a2 =>
          let/resopt taint := taint_action taint a1 in
          taint_action taint a2
        | If cond tbranch fbranch =>
          let/resopt taint := taint_action taint cond in
          (* different branches can conflict *)
          let/resopt taint1 := taint_action taint tbranch in
          let/resopt taint2 := taint_action taint fbranch in
          Success (Some (merge_taint_env taint1 taint2))
        | Bind _ ex body =>
          let/resopt taint := taint_action taint ex in
          taint_action taint body
        | Read P0 idx => Success (Some (set_reg_taint taint idx set_taint_read0))
        | Read P1 idx =>
           if conflicts_with_read1 (get_reg_taint_default taint idx) then
             Success (__debug__ ("read1_conflict", idx) None)
           else
             Success (Some (set_reg_taint taint idx set_taint_read1))
        | Write P0 idx value =>
           let/resopt taint := taint_action taint value in
           if conflicts_with_write0 (get_reg_taint_default taint idx) then
             Success (__debug__ ("write0_conflict", idx) None)
           else
             Success (Some (set_reg_taint taint idx set_taint_write0))
        | Write P1 idx value =>
           let/resopt taint := taint_action taint value in
           if conflicts_with_write1 (get_reg_taint_default taint idx) then
             Success (__debug__ ("write1_conflict", idx) None)
           else
             Success (Some (set_reg_taint taint idx set_taint_write1))
        | Zop _ => Success (Some taint)
        | Unop _ arg => taint_action taint arg
        | Binop _ arg1 arg2 =>
          let/resopt taint := taint_action taint arg1 in
          taint_action taint arg2
        | ExternalCall _ arg =>
          taint_action taint arg
        | InternalCall fn arg =>
          let/resopt taint := taint_action taint arg in
          let/res2 _, fn_spec :=
             lookup_int_fn int_fns fn (__debug__ ("Int fn not found", fn) tt) in
          taint_action taint fn_spec.(fn_body)
        end
      end.

    Definition taint_empty : taint_env_t := SortedRegEnv.empty.

    (* For proof only. If taint_action = Success (Some res), then taint_action_rec returns same result *)
    Fixpoint taint_action_rec
        (fuel: nat)
        (a: action)
      : result (option taint_env_t) unit :=
      match fuel with
      | 0 => Failure (__debug__ "Out of fuel" tt)
      | S fuel =>
        let taint_action := taint_action_rec fuel in
        match a with
        | Fail _ => Success (Some taint_empty)
        | Var _ => Success (Some taint_empty)
        | Const _ => Success (Some taint_empty)
        | Assign _ ex => taint_action ex
        | Seq a1 a2 =>
          let/resopt taint1 := taint_action a1 in
          let/resopt taint2 := taint_action a2 in
          Success (Some (merge_taint_env taint1 taint2))
        | If cond tbranch fbranch =>
          let/resopt cond_taint := taint_action cond in
          let/resopt ttaint := taint_action tbranch in
          let/resopt ftaint := taint_action fbranch in
          Success (Some (merge_taint_env cond_taint (merge_taint_env ttaint ftaint)))
        | Bind _ ex body =>
          let/resopt ex_taint := taint_action ex in
          let/resopt body_taint := taint_action body in
          Success (Some (merge_taint_env ex_taint body_taint))
        | Read P0 idx => Success (Some (set_reg_taint taint_empty idx set_taint_read0))
        | Read P1 idx => Success (Some (set_reg_taint taint_empty idx set_taint_read1))
        | Write P0 idx value =>
           let/resopt value_taint := taint_action value in
           Success (Some (set_reg_taint value_taint idx set_taint_write0))
        | Write P1 idx value =>
           let/resopt value_taint := taint_action value in
           Success (Some (set_reg_taint value_taint idx set_taint_write1))
        | Zop _ => Success (Some taint_empty)
        | Unop _ arg => taint_action arg
        | Binop _ arg1 arg2 =>
          let/resopt taint1 := taint_action arg1 in
          let/resopt taint2 := taint_action arg2 in
          Success (Some (merge_taint_env taint1 taint2))
        | ExternalCall _ arg => taint_action arg
        | InternalCall fn arg =>
          let/resopt arg_taint := taint_action arg in
          let/res2 _, fn_spec :=
             lookup_int_fn int_fns fn (__debug__ ("Int fn not found", fn) tt) in
          let/resopt body_taint := taint_action fn_spec.(fn_body) in
          Success (Some (merge_taint_env arg_taint body_taint))
        end
      end.

    Definition taint_rule (base: taint_env_t) (a: rule) : result (option taint_env_t) unit :=
      taint_action (safe_fuel int_fns (List.length int_fns) a) base a.

    Definition taint_rule_from_empty (a: rule) : result (option taint_env_t) unit :=
      taint_rule SortedRegEnv.empty a.

    Section Scheduler.
      Context {rule_name_t: Type}.
      Context (rules: rule_name_t -> rule).

      Fixpoint interp_taint_scheduler' (s: @scheduler rule_name_t) (env: taint_env_t)
        : result (option taint_env_t) unit :=
        match s with
        | Done => Success (Some env)
        | Cons rl s =>
          let/resopt rule_taint := taint_rule_from_empty (rules rl) in
          if does_not_conflict env rule_taint then
            interp_taint_scheduler' s (merge_taint_env env rule_taint)
          else
            Success None
        end.

      Definition interp_taint_schedule (s: @scheduler rule_name_t)
        : result (option taint_env_t) unit :=
        interp_taint_scheduler' s SortedRegEnv.empty.

      Definition schedule_does_not_conflict (s: @scheduler rule_name_t) : result bool unit :=
        match interp_taint_schedule s with
        | Success (Some _) => Success true
        | Success None => Success false
        | Failure f => Failure f
        end.
    End Scheduler.

  End Interp.

  Definition taint_set_to_prop
             (st0 st1: state_t) (taint_set: result (option taint_env_t) unit) : Prop :=
    match taint_set with
    | Success (Some env) =>
        forall reg, match SortedRegEnv.opt_get env reg with
                | Some t => if t.(taint_write0) || t.(taint_write1) then
                             True
                           else get_reg st0 reg = get_reg st1 reg
                | None => get_reg st0 reg = get_reg st1 reg
                end
    | _ => False
    end.

    Definition no_writes_in_taint_set (res_taint_set: result (option taint_env_t) unit) reg : bool :=
      match res_taint_set with
      | Success (Some env)  =>
         match SortedRegEnv.opt_get env reg with
         | Some t => negb (taint_write0 t  || taint_write1 t)
         | None => true
         end
      | _ => false
      end.

End TaintAnalysis.

Section FailAnalysis.

  Section Interp.
    Context (int_fns: int_fn_env_t).
    Fixpoint action_contains_fail (fuel: nat) (a: action) : result bool unit :=
      match fuel with
      | 0 => Failure (__debug__ "Out of fuel" tt)
      | S fuel =>
        let action_contains_fail := action_contains_fail fuel in
        match a with
        | Fail _ => Success true
        | Var _ => Success false
        | Const _ => Success false
        | Assign _ ex => action_contains_fail ex
        | Seq a1 a2 =>
          let/res b1 := action_contains_fail a1 in
          let/res b2 := action_contains_fail a2 in
          Success (b1 || b2)
        | If cond tbranch fbranch =>
          let/res bcond := action_contains_fail cond in
          let/res btrue := action_contains_fail tbranch in
          let/res bfalse := action_contains_fail fbranch in
          Success (bcond || btrue || bfalse)
        | Bind _ ex body =>
            let/res bex := action_contains_fail ex in
            let/res bbody := action_contains_fail body in
            Success (bex || bbody)
        | Read _ _ => Success false
        | Write _ _ v => action_contains_fail v
        | Zop _ => Success false
        | Unop _ arg => action_contains_fail arg
        | Binop _ arg1 arg2 =>
            let/res b1 := action_contains_fail arg1 in
            let/res b2 := action_contains_fail arg2 in
            Success (b1 || b2)
        | ExternalCall _ arg => action_contains_fail arg
        | InternalCall fn arg =>
            let/res barg := action_contains_fail arg in
            let/res2 _, fn_spec :=
              lookup_int_fn int_fns fn (__debug__ ("Int fn not found", fn) tt) in
            let/res bfn := action_contains_fail fn_spec.(fn_body) in
            Success (barg || bfn)
        end
      end.
    Definition rule_contains_fail (rl: rule) : result bool unit :=
      action_contains_fail (safe_fuel int_fns (List.length int_fns) rl) rl.
  End Interp.
End FailAnalysis.

Module BoxSimAnalysis.
    (* Static analysis:
       - assume:
         + value does not fail
       - input:
         + list of sim regs, list of box sims
         + functions to abstract: associated with a box sim (preserves, does not taint non-box regs)
       - guarantee:
         + list of sim regs, list of box sims
         + box sim

        - tag value with safe or not
        - maintain list of sim regs, list of (disjoint) box sims
        - at branches: check branch condition is related
        - at each fn: expand or check box sim preserved
        - at a set: merge gammas and sim lists conservatively
        - writes: add to set
        - fails?
     *)


  Section Analysis.
    Context (int_fns: int_fn_env_t).
    Context {box_t: Type}.
    Context {box_t_eq_dec: EqDec box_t}.
    Context (box_defs: list (box_t * list reg_t)).
    Context (box_fns: list (fn_name_t * (box_t * list ext_fn_t))).

    Definition sim_gamma_t := @varenv_t bool.
    (* Definition sim_state_t := SortedRegEnv.EnvT bool. *)

    Record sim_state_t :=
      { sim_regs: SortedRegEnv.EnvT bool;
        sim_boxes: list box_t
      }.

    Definition merge_sim_regs (st1 st2: SortedRegEnv.EnvT bool) : SortedRegEnv.EnvT bool :=
      let zipped := SortedRegEnv.zip_default st1 st2 false false in
      SortedRegEnv.mapV (fun '(a,b) => andb a b) zipped.

    Definition merge_sim_boxes (boxes1 boxes2: list box_t) : list box_t :=
      filter (fun box => existsb (beq_dec box) boxes2) boxes1 .

    Definition merge_sim_state (st1 st2: sim_state_t) : sim_state_t :=
      {| sim_regs := merge_sim_regs st1.(sim_regs) st2.(sim_regs);
         sim_boxes := merge_sim_boxes st1.(sim_boxes) st2.(sim_boxes)
      |}.

    (* assume gamma vars are equal? *)

    Definition merge_sim_gamma (gamma1 gamma2: sim_gamma_t) : result sim_gamma_t unit :=
      let/res zipped := map2 pair gamma1 gamma2 in
      result_list_map (fun '((v1,b1),(v2,b2)) => if String.eqb v1 v2 then Success (v1, b1 && b2)
                                              else Failure (__debug__ ((v1,v2), "merge_sim_gamma") tt))
                      zipped.

    Definition update_sim_reg' (st: SortedRegEnv.EnvT bool) (r: reg_t) (v: bool) : SortedRegEnv.EnvT bool :=
      SortedRegEnv.update st r (fun _ => v) false.

    Definition update_sim_reg (st: sim_state_t) (r: reg_t) (v: bool) : sim_state_t :=
      {| sim_regs := update_sim_reg' st.(sim_regs) r v;
         sim_boxes := st.(sim_boxes)
      |}.

    Definition reg_in_box_defs (idx: reg_t) : bool :=
      existsb (fun regs => existsb (reg_t_beq idx) regs) (map snd box_defs).

    Definition remove_box (st: sim_state_t) (box: box_t) : sim_state_t :=
      {| sim_regs := st.(sim_regs);
         sim_boxes := filter (fun box2 => negb (beq_dec box box2)) st.(sim_boxes)
      |}.

    Section Action.
      Context (ext_fn_sim: list ext_fn_t).
      Context (sim_r: SortedRegEnv.EnvT bool).
      Context (sim_boxes0: list box_t).

      Fixpoint remove_tainted_action'
                 (fuel: nat)
                 (st: sim_state_t)
                 (gamma: sim_gamma_t)
                 (a: action)
                 : result (option (sim_gamma_t * sim_state_t)) unit :=
        let __debug__ {A} (v: A) := __debug__ v tt in
        match fuel with
        | 0 => Failure (__debug__ "Out of fuel")
        | S fuel =>
            match a with
            | Fail _ => Success None
            | Var _ => Success (Some (gamma, st))
            | Const _ => Success (Some (gamma, st))
            | Assign var ex =>
                let/resopt2 gamma, st := remove_tainted_action' fuel st gamma ex in
                let/res _ := varenv_lookup_var gamma var (__debug__ ("Var not found", gamma, var)) in
                Success (Some (varenv_update gamma var false, st))
            | Seq a1 a2 =>
                let/resopt2 gamma, st := remove_tainted_action' fuel st gamma a1 in
                remove_tainted_action' fuel st gamma a2
            | If cond tbranch fbranch =>
                let/resopt2 gamma, st := remove_tainted_action' fuel st gamma cond in
                match remove_tainted_action' fuel st gamma tbranch with
                | Success (Some (gamma, st)) =>
                    match remove_tainted_action' fuel st gamma fbranch with
                    | Success (Some (gamma, st)) => Success (Some (gamma, st))
                    | Success None => Success (Some (gamma, st))
                    | Failure f => Failure f
                    end
                | Success (None) => remove_tainted_action' fuel st gamma fbranch
                | Failure f => Failure f
                end
            | Bind var ex body =>
                let/resopt2 gamma, st := remove_tainted_action' fuel st gamma ex in
                let/resopt2 gamma, st := remove_tainted_action' fuel st (varenv_bind gamma var false) body in
                Success (Some (tl gamma, st))
            | Read _ _ =>
                Success (Some (gamma, st))
            | Write _ idx value =>
                let/resopt2 gamma, st := remove_tainted_action' fuel st gamma value in
                if reg_in_box_defs idx then
                  (* TODO: can remove box sim from list instead of failing; but for now we assume this is a misuse *)
                  Failure (__debug__ (idx, "write to reg in box"))
                else
                Success (Some (gamma, update_sim_reg st idx false))
            | Zop _ =>
                Success (Some (gamma, st))
            | Unop _ arg =>
                remove_tainted_action' fuel st gamma arg
            | Binop _ arg1 arg2 =>
                let/resopt2 gamma, st := remove_tainted_action' fuel st gamma arg1 in
                remove_tainted_action' fuel st gamma arg2
            | ExternalCall _ arg =>
                remove_tainted_action' fuel st gamma arg
            | InternalCall fn arg =>
                let/resopt2 gamma, st := remove_tainted_action' fuel st gamma arg in
                match find (fun '(f, _) => Nat.eqb fn f) box_fns with
                | Some (_, (box, ext_fns)) =>
                    Success (Some (gamma, remove_box st box))
                | None =>
                    let/res2 arg_name, body := get_fn_arg_and_body'' int_fns fn in
                    let/resopt2 _, st := remove_tainted_action' fuel st [(arg_name, false)] body in
                    Success (Some (gamma, st))
                end
            end
        end.

      Definition remove_tainted_action
                 (fuel: nat)
                 (st: sim_state_t)
                 (gamma: sim_gamma_t)
                 (a: action)
                 : result (sim_gamma_t * sim_state_t) unit :=
        let/res res := remove_tainted_action' fuel st gamma a in
        match res with
        | Some (gamma', st') => Success (gamma', st')
        | None => Success (gamma, st)
        end.

      (* if fail, remove nothing *)

      (* Assume no fail, so can ignore those branches *)
      Fixpoint analyze_action
                 (fuel: nat)
                 (st: sim_state_t)
                 (gamma: sim_gamma_t)
                 (a: action)
                 : result (option (sim_gamma_t * sim_state_t * bool)) unit :=
        let __debug__ {A} (v: A) := __debug__ v tt in
        match fuel with
        | 0 => Failure (__debug__ "Out of fuel")
        | S fuel =>
          match a with
          | Fail hint => Success None
          | Var var =>
              let/res var_sim := varenv_lookup_var gamma var (__debug__ ("Var not found", gamma,var)) in
              Success (Some (gamma, st, var_sim))
          | Const cst =>
              Success (Some (gamma, st, true))
          | Assign var ex =>
              let/resopt3 gamma, st, v_ex := analyze_action fuel st gamma ex in
              Success (Some (varenv_update gamma var v_ex, st, true))
          | Seq a1 a2 =>
              let/resopt3 gamma, st, _ := analyze_action fuel st gamma a1 in
              analyze_action fuel st gamma a2
          | If cond tbranch fbranch =>
              (* TODO: Check !!!!
                 - Case with two branches:
                   + if cond_sim then merge sim gamma, merge sim regs, and merge sim boxes
                   * else:
                     + remove any taints
               *)
              let/resopt3 gamma, st, v_cond := analyze_action fuel st gamma cond in
              if v_cond then
                let/res opt_t := analyze_action fuel st gamma tbranch in
                let/res opt_f := analyze_action fuel st gamma fbranch in
                match opt_t, opt_f with
                | Some (gamma_t, st_t, v_t), Some (gamma_f, st_f, v_f) =>
                    let/res gamma := merge_sim_gamma gamma_t gamma_f in
                    Success (Some (gamma, merge_sim_state st_t st_f, v_t && v_f))
                | Some (gamma_t, st_t, v_t), None => Success (Some (gamma_t, st_t, v_t))
                | None, Some (gamma_f, st_f, v_f) => Success (Some (gamma_f, st_f, v_f))
                | None, None => Success None
                end
              else
                let/res2 gamma, st := remove_tainted_action fuel st gamma tbranch in
                let/res2 gamma, st := remove_tainted_action fuel st gamma fbranch in
                Success (Some (gamma, st, false))
          | Bind var ex body =>
              let/resopt3 gamma, st, v_ex := analyze_action fuel st gamma ex in
              let/resopt3 gamma, st, v_body := analyze_action fuel st (varenv_bind gamma var v_ex) body in
              Success (Some (tl gamma, st, v_body))
          | Read P0 idx =>
              if reg_in_box_defs idx then
                (* TODO: can remove box sim from list instead of failing; but for now we assume this is a misuse *)
                Failure (__debug__ (idx, "read to reg in box"))
              else
                let/optres v_reg := SortedRegEnv.opt_get sim_r idx in
                Success (Some (gamma, st, v_reg))
          | Read P1 idx =>
              if reg_in_box_defs idx then
                (* TODO: can remove box sim from list instead of failing; but for now we assume this is a misuse *)
                Failure (__debug__ (idx, "read to reg in box"))
              else
                let/optres v_reg := SortedRegEnv.opt_get st.(sim_regs) idx in
                Success (Some (gamma, st, v_reg))
          | Write _ idx value =>
              let/resopt3 gamma, st, v_value := analyze_action fuel st gamma value in
              if reg_in_box_defs idx then
                (* TODO: can remove box sim from list instead of failing; but for now we assume this is a misuse *)
                Failure (__debug__ (idx, "write to reg in box"))
              else
                Success (Some (gamma, update_sim_reg st idx v_value, true))
          | Zop _ =>
              Success (Some (gamma, st, true))
          | Unop _ arg1 =>
              analyze_action fuel st gamma arg1
          | Binop _ arg1 arg2 =>
              let/resopt3 gamma, st, v1 := analyze_action fuel st gamma arg1 in
              let/resopt3 gamma, st, v2 := analyze_action fuel st gamma arg2 in
              Success (Some (gamma, st, v1 && v2))
          | ExternalCall fn arg =>
              let/resopt3 gamma, st, v_arg := analyze_action fuel st gamma arg in
              Success (Some (gamma, st, (existsb (Nat.eqb fn) ext_fn_sim) && v_arg))
          | InternalCall fn arg =>
              let/resopt3 gamma, st, v_arg := analyze_action fuel st gamma arg in
              match find (fun '(f, _) => Nat.eqb fn f) box_fns with
              | Some (_, (box, ext_fns)) =>
                  let box_sim := existsb (beq_dec box) st.(sim_boxes) in
                  let ext_fn_sim := forallb (fun f => existsb (Nat.eqb f) ext_fn_sim) ext_fns in
                  (* NB *)
                  let st' :=
                    if v_arg && ext_fn_sim
                    then st
                    else remove_box st box
                  in Success (Some (gamma, st', box_sim && ext_fn_sim && v_arg))
              | None => let/res2 arg_name, body := get_fn_arg_and_body'' int_fns fn in
                       let/resopt3 _, st, v_fn := analyze_action fuel st [(arg_name, v_arg)] body in
                       Success (Some (gamma, st, v_fn))
              end
          end
        end.

        Definition analyze_rule (rl: action) : result (option sim_state_t) unit :=
          let/resopt3 _, st, _ := analyze_action (safe_fuel int_fns (Datatypes.length int_fns) rl)
                                                 {| sim_regs := sim_r;
                                                    sim_boxes := sim_boxes0
                                                 |} [] rl in
          Success (Some st).

      End Action.
  End Analysis.
End BoxSimAnalysis.

Module BoxSimPreserved.

  Record box_def :=
    { box_valid_regs : list (reg_t * list bool);
      box_data_regs : list reg_t
    }.
  Definition get_box_regs (box: box_def) : list reg_t :=
    map fst box.(box_valid_regs) ++ box.(box_data_regs).
    Definition box_data_sim
      (box: box_def)
      (impl_st spec_st: state_t) : Prop :=
      Forall (fun '(r, v) => impl_st.[r] = v) box.(box_valid_regs) ->
      forall reg, existsb (Nat.eqb reg) box.(box_data_regs) = true ->
             impl_st.[reg] = spec_st.[reg].

    Record box_sim (box: box_def) (impl_st spec_st: state_t) : Prop :=
      { pf_box_valid_sim: forall r, In r (map fst box.(box_valid_regs)) -> impl_st.[r] = spec_st.[r];
        pf_box_data_sim: box_data_sim box impl_st spec_st
      }.

  Section Boxes.
    Context {box_t: Type}.
    Context {box_t_eq_dec: EqDec box_t}.
    Context (box_defs: list (box_t * box_def)).

    Definition reg_box_defs : list (box_t * list reg_t) := (map (fun '(box, def) => (box, get_box_regs def)) box_defs).

    (* TODO: fix naming *)
    Definition BoxRegsUnique (boxes: list (box_t * box_def)) : Prop :=
      forall box def1 def2,
      In (box, def1) boxes ->
      In (box, def2) boxes ->
      def1 = def2.

    Definition BoxRegsDisjoint (boxes: list (box_t * box_def)) : Prop :=
      forall b1 b2 def1 def2 r,
      In (b1, def1) boxes ->
      In (b2, def2) boxes ->
      In r (get_box_regs def1) ->
      In r (get_box_regs def2) ->
      b1 = b2.

    Record WF_boxes (boxes: list (box_t * box_def)) : Prop :=
      { WFBoxes_Unique: BoxRegsUnique boxes;
        WFBoxes_Disjoint: BoxRegsDisjoint boxes
      }.

    Definition RegsNotInBoxes (env: SortedRegEnv.EnvT bool) (boxes: list (box_t * list reg_t)) : Prop :=
      forall reg box def,
        SortedRegEnv.opt_get env reg = Some true ->
        In (box, def) boxes ->
        In reg def ->
        False.

    Definition computable_RegsNotInBoxes (env: SortedRegEnv.EnvT bool) (boxes: list (box_t * list reg_t)) : bool :=
      forallb (fun '(r, _) => forallb (fun '(_, rs) => negb (existsb (reg_t_beq r) rs)) boxes) (SortedRegEnv.to_list env).


    Definition computable_BoxRegsUnique (boxes: list (box_t * box_def)) : bool :=
      unique boxes.

    Fixpoint computable_BoxRegsDisjoint (boxes: list (box_t * box_def)) : bool :=
      match boxes with
      | [] => true
      | [(a,def)] => true
      | (a,def)::boxes =>
          forallb (fun r => negb (existsb (fun '(b, bdef) => existsb (reg_t_beq r) (get_box_regs bdef)) boxes))
                  (get_box_regs def) && (computable_BoxRegsDisjoint boxes)
      end.

    Definition computable_WF_boxes (boxes: list (box_t * box_def)) : bool :=
      computable_BoxRegsDisjoint boxes && computable_BoxRegsUnique boxes.

  End Boxes.
End BoxSimPreserved.

(*   Section FIFOs. *)

(*     Record fifo_def := *)
(*       { fifo_valid_reg: (reg_t * bool); *)
(*         fifo_data_regs: list reg_t *)
(*       }. *)

(*     Definition fifo_to_box_def (fifo: fifo_def): box_def := *)
(*       {| box_valid_regs := let '(r, b) := fifo.(fifo_valid_reg) in *)
(*                            [(r,[b])]; *)
(*          box_data_regs := fifo.(fifo_data_regs) *)
(*       |}. *)

(*     Inductive SimValue := *)
(*     | Concrete (v: list bool) (* and related *) *)
(*     | Symbolic *)
(*     | Related. *)

(*     (* assume inputs are related. *)
(*        - assume valid reg is equal to negated bit. *)
(*        - state: map from reg -> Concrete/Unrelated/Related values *)
(*        - start: valid bit is concrete (and related) *)
(*        - need to check: *)
(*          + valid bits at end is concrete or related *)
(*          + if concrete and equal to 1, then the rest of the data regs must be concrete or related *)
(*      *) *)

(*     Definition symb_state_t := SortedRegEnv.EnvT SimValue. *)
(*     Definition symb_gamma_t := @varenv_t SimValue. *)


(*     Section FifoBox. *)
(*       Context (int_fns: int_fn_env_t). *)
(*       Context (struct_defs: struct_env_t). *)
(*       Context (fifo: fifo_def). *)
(*       Context (symb_r: symb_state_t). *)

(*       Definition eager_interp_concrete_binop1 (fn: fn2) (v: list bool) : option vect_t := *)
(*         match fn with *)
(*         | Bits2 And => if bits_eq v (zeroes (List.length v)) then *)
(*                   Some (zeroes (List.length v)) *)
(*                 else None *)
(*         | Bits2 Or => if bits_eq v (ones (List.length v)) then *)
(*                  Some (ones (List.length v)) *)
(*                else None *)
(*         | _ => None *)
(*         end. *)

(*       Definition interp_sim_binop (fn: fn2) (v1: SimValue) (v2: SimValue) : result SimValue unit := *)
(*         match v1, v2 with *)
(*         | Concrete v1, Concrete v2 => *)
(*             let/res ret := interp_binop struct_defs fn v1 v2 in *)
(*             Success (Concrete ret) *)
(*         | Concrete v1, _ => *)
(*             match eager_interp_concrete_binop1 fn v1 with *)
(*             | Some res => Success (Concrete res) *)
(*             | None => Success v2 *)
(*             end *)
(*         | _, Concrete v2 => *)
(*             match eager_interp_concrete_binop1 fn v2 with *)
(*             | Some res => Success (Concrete res) *)
(*             | None => Success v1 *)
(*             end *)
(*         | Related, Symbolic => Success Symbolic *)
(*         | Symbolic, Related => Success Symbolic *)
(*         | Related, Related => Success Related *)
(*         | _, _ => Failure (__debug__ "TODO" tt) *)
(*         end. *)

(*       (* - condition: valid bits at end are concrete /\ *)
(*                       if valid bit is equal to 1, then the rest of the data must be concrete/related *)
(*          - so: generate paths appropriately *)
(*          - soundness: all resulting states are in some path *)
(*        *) *)
(*       (* NB: simplified; for generality should deal with paths. *) *)

(*       Section ResultListMaps. *)
(*           Context {A B F: Type}. *)
(*           Context (f: A -> result (list (option B)) F). *)

(*           Fixpoint result_option_list_maps (la: list (option A)): result (list (list (option B))) F := *)
(*             match la with *)
(*             | [] => Success [] *)
(*             | a :: la => let/res b := match a with *)
(*                                     | Some a => f a *)
(*                                     | None => Success [None] *)
(*                                     end in *)
(*                        let/res la := result_option_list_maps la in *)
(*                        Success (b::la) *)
(*             end. *)

(*       End ResultListMaps. *)

(*       Fixpoint analyze_action *)
(*                  (fuel: nat) *)
(*                  (st: symb_state_t) *)
(*                  (gamma: symb_gamma_t) *)
(*                  (a: action) *)
(*                  : result (list (option (symb_gamma_t * symb_state_t * SimValue))) unit := *)
(*         let __debug__ {A} (v: A) := __debug__ v tt in *)
(*         match fuel with *)
(*         | 0 => Failure (__debug__ "Out of fuel") *)
(*         | S fuel => *)
(*             match a with *)
(*             | Fail _ => Success [None] *)
(*             | Var var => *)
(*                 let/res var_sim := varenv_lookup_var gamma var (__debug__ ("Var not found", gamma,var)) in *)
(*                 Success [Some (gamma, st, var_sim)] *)
(*             | Const cst => *)
(*                 Success [Some (gamma, st, Concrete cst)] *)
(*             | Assign var ex => *)
(*                 let/res paths_ex := analyze_action fuel st gamma ex in *)
(*                 Success (map (option_map (fun '(gamma, st, v_ex) => (varenv_update gamma var v_ex, st, Concrete []))) *)
(*                              paths_ex) *)
(*             | Seq a1 a2 => *)
(*                 let/res paths1 := analyze_action fuel st gamma a1 in *)
(*                 let/res paths2 := *)
(*                   result_option_list_maps (fun '(gamma, st, _) => analyze_action fuel st gamma a2) paths1 in *)
(*                 Success (List.concat paths2) *)
(*             | If cond tbranch fbranch => *)
(*                 let/res paths_cond := analyze_action fuel st gamma cond in *)
(*                 let/res paths2 := *)
(*                   result_option_list_maps ( *)
(*                       fun '(gamma, st, v_cond) => *)
(*                         match v_cond with *)
(*                         | Concrete [value] => *)
(*                             if value then analyze_action fuel st gamma tbranch *)
(*                             else analyze_action fuel st gamma fbranch *)
(*                         | Concrete _ => Failure (__debug__ ("Unexpected branch condition", v_cond)) *)
(*                         | Related => Failure (__debug__ "TODO" ) *)
(*                         | Symbolic => *)
(*                             (* Symbolic branch condition -> safe to path explode: *)
(*                                -  *)
(*                              *) *)
(*                             Failure (__debug__ "TODO" ) *)
(*                                              (* Symbolic branch condition -> could just path explode *)  *)
(*       (* - condition: valid bits at end are concrete /\ *) *)
(*                       if valid bit is equal to 1, then the rest of the data must be concrete/related *)
(*          - so: generate paths appropriately *)
(*          - soundness: all resulting states are in some path *)

(*                         end) paths_cond in *)
(*                 Success (List.concat paths2) *)


(*               (* | Related => *) *)
(*               (*     let/res opt_t := analyze_action fuel st gamma tbranch in *) *)
(*               (*     let/res opt_f := analyze_action fuel st gamma fbranch in *) *)
(*               (*     match opt_t, opt_f with *) *)
(*               (*     | Some (gamma_t, st_t, v_t), Some (gamma_f, st_f, v_f) => *) *)
(*               (*         Failure (__debug__ "TODO") *) *)
(*               (*     | Some (gamma_t, st_t, v_t), None => *) *)
(*               (*         Success (Some (gamma_t, st_t, v_t)) *) *)
(*               (*     | None, Some (gamma_f, st_f, v_f) => *) *)
(*               (*          Success (Some (gamma_f, st_f, v_f)) *) *)
(*               (*     | None, None => Success None *) *)
(*               (*     end *) *)
(*               (* | Symbolic => Failure (__debug__ "TODO") *) *)
(*               (* end *) *)
(*             | Bind var ex body => *)
(*                 let/res paths_ex := analyze_action fuel st gamma ex in *)
(*                 let/res paths_ret := *)
(*                   result_option_list_maps (fun '(gamma, st, v_ex) => *)
(*                     let/res paths := analyze_action fuel st (varenv_bind gamma var v_ex) body in *)
(*                     Success (map (option_map (fun '(gamma, st, v) => (tl gamma, st, v))) paths)) paths_ex in *)
(*                 Success (List.concat paths_ret) *)
(*             | Read P0 idx => *)
(*                 match SortedRegEnv.opt_get symb_r idx with *)
(*                 | Some v_reg =>  Success [Some (gamma, st, v_reg)] *)
(*                 | None => Failure tt *)
(*                 end *)
(*             | Read P1 idx => *)
(*                 match SortedRegEnv.opt_get st idx with *)
(*                 | Some v_reg =>  Success [Some (gamma, st, v_reg)] *)
(*                 | None => Failure tt *)
(*                 end *)
(*             | Write _ idx value => *)
(*                 let/res paths := analyze_action fuel st gamma value in *)
(*                 Success (map (option_map (fun '(gamma, st, v_value) => *)
(*                                  (gamma, SortedRegEnv.update st idx (fun _ => v_value) v_value, Concrete []))) paths) *)
(*             | Zop fn => *)
(*                 let/res v := interp_zop struct_defs fn in *)
(*                 Success [Some (gamma, st, Concrete v)] *)
(*             | Unop fn arg1 => *)
(*                 let/res paths := analyze_action fuel st gamma arg1 in *)
(*                 result_list_map (fun opt => *)
(*                                    let/optres3 gamma, st, v1 := opt in *)
(*                                             match v1 with *)
(*                                             | Concrete v => *)
(*                                                 let/res v := interp_unop struct_defs fn v in *)
(*                                                 Success (Some (gamma, st, Concrete v)) *)
(*                                             | Related => Success (Some (gamma, st, Related)) *)
(*                                             | Symbolic => Success (Some (gamma, st, Symbolic)) *)
(*                                             end *)
(*                                 ) paths *)
(*             | Binop fn arg1 arg2 => *)
(*                 let/res paths1 := analyze_action fuel st gamma arg1 in *)
(*                 let/res paths2 := *)
(*                   result_option_list_maps (fun '(gamma, st, v1) => *)
(*                       let/res paths := analyze_action fuel st gamma arg2 in *)
(*                       result_list_map (fun opt => *)
(*                                          let/optres3 gamma, st, v2 := opt in *)
(*                                          let/res ret := interp_sim_binop fn v1 v2 in *)
(*                                          Success (Some (gamma, st, ret))) paths) paths1 in *)
(*                 Success (List.concat paths2) *)
(*            | ExternalCall fn arg => *)
(*                 let/res paths := analyze_action fuel st gamma arg in *)
(*                  Success (map (option_map (fun '(gamma, st, v_arg) => *)
(*                                              match v_arg with *)
(*                                              | Concrete _ => (gamma, st, Related) (* weaken b/c sigma not concrete necessarily *) *)
(*                                              | Related => (gamma, st, Related) *)
(*                                              | Symbolic => (gamma, st, Symbolic) *)
(*                                              end)) paths) *)
(*             | InternalCall fn arg => *)
(*                 (* Just expand *) *)
(*                 let/res paths := analyze_action fuel st gamma arg in *)
(*                 let/res2 id, fn_spec := lookup_int_fn int_fns fn (__debug__ ("Int fn not found", fn)) in *)
(*                 let/res paths2 := *)
(*                   result_option_list_maps (fun '(gamma, st, v_arg) => *)
(*                                             let/res paths := analyze_action fuel st [(fn_spec.(fn_arg_name),v_arg)] fn_spec.(fn_body) in *)
(*                                             Success (map (option_map(fun '(_, st, v_ret) => (gamma, st, v_ret))) paths)) *)
(*                                           paths in *)
(*                 Success (List.concat paths2) *)
(*             end *)
(*         end. *)

(*     End FifoBox. *)
(*   End FIFOs. *)
(*     (* - assume box reads/writes box registers only *)
(*        - pf_valid_bits_sim: *)
(*          + case 1: valid regs are equal to designated value *)
(*            * then all box registers are related *)
(*            * so all reads/writes must be equal, so we stay related -- ez case *)
(*          + case 2: valid regs are not equal to given value; no guarantee. *)
(*            * static analysis specialized for one valid bit; simplify ands if need be: *)
(*              check when there's no guarantee... *)
(*            * (but valid bits must still be equal) *)
(*            * then if write valid bits, must write everything with constant/related value *)
(*            * symbolic eval not *)
(*        - return true/false/don't know *)
(*      *) *)

(* End BoxSimPreserved. *)
