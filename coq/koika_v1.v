Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Koika.Tactics.
Require Import Koika.Common.
Import List.ListNotations.
Open Scope string_scope.

Inductive Port :=
| P0
| P1.

Definition reg_t := string.
Definition var_t := string.
Definition fn_name_t := string.
Definition ext_fn_t := string.

(* Inductive fn1 := *)
(* | Not *)
(* | Slice (offset: nat) (width: nat). *)

(* Inductive bits_comparison := *)
(* | cLt | cGt | cLe | cGe. *)

(* Inductive fn2 := *)
(* | And *)
(* | Or *)
(* | Xor *)
(* | Concat *)
(* | Sel *)
(* | Plus *)
(* | Minus *)
(* | Compare (signed: bool) (c: bits_comparison). *)

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
(* | Unop (fn: fn1) (arg1: action) *)
(* | Binop (fn: fn2) (arg1: action) (arg2: action) *)
(* | InternalCall (fn: fn_name_t) (args: list action) *)
(* | ExternalCall (fn: ext_fn_t) (arg: action) *)
.

Declare Custom Entry koika.
Declare Custom Entry koika_var.
Declare Custom Entry koika_args.
Declare Custom Entry koika_consts.
Declare Custom Entry koika_reg.

(* Koika_consts *)
Notation "'0'" :=
  ([false])
    (in custom koika_consts at level 0).
Notation "'1'" :=
  ([true])
    (in custom koika_consts at level 0).
Notation "bs '~' '0'" := (cons false bs) (in custom koika_consts at level 7, left associativity, format "bs '~' '0'").
Notation "bs '~' '1'" := (cons true bs) (in custom koika_consts at level 7, left associativity, format "bs '~' '1'").
Notation "'Ob' '~' number" :=
  (Const number)
    (in custom koika at level 7, number custom koika_consts at level 99, format "'Ob' '~' number").

Notation "'{{' e '}}'" := (e) (e custom koika at level 200, format "'{{' '[v' '/' e '/' ']' '}}'").
Notation "'fail' '(' t ')'" :=
  (Fail t) (in custom koika, t constr at level 0, format "'fail' '(' t ')'").
Notation "'pass'" := (Const nil) (in custom koika).
Notation "'let' a ':=' b 'in' c" := (Bind a b c) (in custom koika at level 91, a custom koika_var at level 1, right associativity, format "'[v' 'let'  a  ':='  b  'in' '/' c ']'").
Notation "a" := (a%string) (in custom koika_var at level 0, a constr at level 0, format "'[' a ']'").
Notation "a" := (a%string) (in custom koika_reg at level 0, a constr at level 0, format "'[' a ']'").
Notation "a ';' b" := (Seq a b) (in custom koika at level 90, format "'[v' a ';' '/' b ']'" ).
Notation "'set' a ':=' b" := (Assign a b) (in custom koika at level 89, a custom koika_var at level 1, format "'set'  a  ':='  b").
Notation "'read0' '(' reg ')' " := (Read P0 reg) (in custom koika, reg custom koika_reg, format "'read0' '(' reg ')'").
Notation "'read1' '(' reg ')' " := (Read P1 reg) (in custom koika, reg custom koika_reg, format "'read1' '(' reg ')'").
Notation "'write0' '(' reg ',' value ')'" :=
  (Write P0 reg value)
    (in custom koika, reg custom koika_reg at level 13, format "'write0' '(' reg ',' value ')'").
Notation "'write1' '(' reg ',' value ')'" :=
  (Write P1 reg value)
    (in custom koika, reg custom koika_reg at level 13, format "'write1' '(' reg ',' value ')'").
Notation "a" := (Var (a)) (in custom koika at level 1, a constr at level 0).

Notation "'if' a 'then' t 'else' f" := (If a t f) (in custom koika at level 86, right associativity, format "'[v' 'if'  a '/' 'then'  t '/' 'else'  f ']'").
(* Notation "'guard' '(' a ')' " := (UIf (UUnop (UBits1 UNot) a) (UFail (bits_t 0)) (USugar (UConstBits Ob))) (in custom koika at level 86, right associativity, format "'guard' '(' a ')'"). *)

Definition gamma_t : Type := var_t -> option (list bool).

Inductive result {S F} :=
| Success (s: S)
| Failure (f: F).



Arguments result : clear implicits.
Definition is_success {S F} (r: result S F) :=
  match r with
  | Success s => true
  | Failure f => false
  end.

Definition extract_success {S F} (r: result S F) (pr: is_success r = true) :=
  match r return is_success r = true -> S with
  | Success s => fun _ => s
  | Failure f => fun pr => match Bool.diff_false_true pr with end
  end pr.

Lemma extract_success_None:
  forall {S F} (term: result S F) (pf: is_success term = true) v,
    term = Success v ->
    extract_success term pf = v.
Proof.
  intros; subst; auto.
Qed.

Notation "'let/res' var ':=' expr 'in' body" :=
  (match expr with
   | Success var => body
   | Failure f => Failure f
   end)
    (at level 200).

Notation "'let/res2' v1 ',' v2 ':=' expr 'in' body" :=
  (match expr with
   | Success (v1,v2) => body
   | Failure f => Failure f
   end)
    (at level 200).


Fixpoint list_find_res {A B} (f: A -> result B unit) (l: list A) : result B unit :=
  match l with
  | [] => Failure tt
  | x :: l =>
    let fx := f x in
    match fx with
    | Success y => Success y
    | Failure tt => list_find_res f l
    end
  end.
Definition __debug__ {T U: Type} (t: T) (u: U) : U.
Proof.
  exact u.
Defined.
Opaque __debug__.

Section Typecheck.

  Definition reg_types_t := reg_t -> option nat.
  Definition var_types_t := var_t -> option nat.

  Definition lookup_var_type {A} (var_types: var_types_t) (var: var_t) (msg: A) : result nat A :=
    match var_types var with
    | Some t => Success t
    | None => Failure msg
    end.

  Definition lookup_reg_type {A} (reg_types: reg_types_t) (reg: reg_t) (msg: A) : result nat A :=
    match reg_types reg with
    | Some t => Success t
    | None => Failure msg
    end.

  Section Typecheck.
    Context (reg_types : reg_types_t).

    Definition typechecking_error_t : Type := string * action * var_types_t.

    Fixpoint type_check (var_types: var_types_t) (a: action) : result nat string :=
      let failure_msg (msg: string) : string
          := __debug__ (msg, a, var_types) msg in
      match a with
      | Fail ty_hint => Success ty_hint
      | Var var => lookup_var_type var_types var (failure_msg ("Var untyped: " ++ var))
      | Const cst => Success (List.length cst)
      | Assign var ex =>
        let/res var_type :=
           lookup_var_type var_types var (failure_msg ("Var untyped: " ++ var)) in
        let/res ex_type :=
           type_check var_types ex in
        if Nat.eqb var_type ex_type then
          Success 0
        else Failure (failure_msg (__debug__ (var_type, ex_type) "Assign/Types do not match" ))
      | Seq a1 a2 =>
        let/res ty1 := type_check var_types a1 in
        type_check var_types a2
      | If cond tbranch fbranch =>
        let/res ty_cond := type_check var_types cond in
        let/res ty_tbranch := type_check var_types tbranch in
        let/res ty_fbranch := type_check var_types fbranch in
        if Nat.eqb ty_cond 1 then
          if Nat.eqb ty_tbranch ty_fbranch then
            Success ty_tbranch
          else Failure (failure_msg (__debug__ (ty_tbranch, ty_fbranch) "If/Types do not match"))
        else Failure (failure_msg (__debug__ ty_cond "If/Cond type not 1"))
      | Bind v ex body =>
        let/res ty_ex := type_check var_types ex in
        let var_types' := fun v' => if String.eqb v v' then Some ty_ex else var_types v' in
        type_check var_types' body
      | Read p idx =>
        lookup_reg_type reg_types idx (failure_msg (__debug__ idx "Read/reg not found"))
      | Write p idx value =>
        let/res idx_ty := lookup_reg_type reg_types idx (failure_msg (__debug__ idx "Write/reg not found")) in
        let/res value_ty := type_check var_types value in
        if Nat.eqb idx_ty value_ty then
          Success 0
        else
          Failure (failure_msg (__debug__ (idx_ty, value_ty) "Write/Types do not match"))
      (* | _ => Failure (failure_msg "TODO") *)
      end.

  End Typecheck.

End Typecheck.

Section Tests.
  Section Notations.
    Definition test_fail := {{ fail(2)}}. Print test_fail.
    Definition test_pass := {{ pass }}. Print test_pass.
    Definition test_const1 := {{ Ob~1 }}. Print test_const1.
    Definition test_const0 := {{ Ob~0 }}. Print test_const0.
    Definition test_const := {{ Ob~1~0 }}. Print test_const. (* Note: reversed *)
    Definition test_let := {{ let "v" := Ob~1~0 in pass }}. Print test_let.
    Definition test_let2 := {{ let "v" := Ob~1~0 in "v" }}. Print test_let2.
    Definition test_seq := {{ Ob~1~0; let "v" := Ob~1 in pass }}. Print test_seq.
    Definition test_set__fail := {{ set "a" := Ob~1 }}. Print test_set__fail.
    Definition test_read0 := {{ read0("reg0") }}. Print test_read0.
    Definition test_read1 := {{ read1("reg1") }}. Print test_read1.
    Definition test_write0 := {{ write0("reg2", Ob~0~1) }}. Print test_write0.
    Definition test_write1 := {{ write1("reg3", Ob~1~0~0) }}. Print test_write1.
    Definition test_write1__fail := {{ write1("reg3", Ob~1~0) }}. Print test_write1.

  End Notations.

  Section Typechecking.
    Definition test_reg_types : reg_types_t :=
      fun reg =>
        match reg with
        | "reg0" => Some 0
        | "reg1" => Some 1
        | "reg2" => Some 2
        | "reg3" => Some 3
        | _ => None
        end.

    Definition empty_var_t : var_types_t := fun _ => None.

    Notation type_check := (type_check test_reg_types empty_var_t).

    Compute type_check test_fail.
    Compute type_check test_pass.
    Compute type_check test_const1.
    Compute type_check test_const0.
    Compute type_check test_let.
    Compute type_check test_let2.
    Compute type_check test_seq.
    Compute type_check test_set__fail.
    Compute type_check test_read0.
    Compute type_check test_read1.
    Compute type_check test_write0.
    Compute type_check test_write1.
    Compute type_check test_write1__fail.
  End Typechecking.

End Tests.
Ltac simplify_result :=
  repeat match goal with
      | H: (match ?v with
            | Some _ => _
            | None => Failure _
            end) = Success _ |- _ =>
        destruct_matches_in_hyp H; [ | simpl in H; discriminate]
      | H: Success _ = Success _ |- _ =>
        inversions H
      | H : is_success (Failure _) = true |- _ =>
        simpl in H; discriminate
      | H: is_success (let/res _ := _ in _) = true |- _ =>
        destruct_matches_in_hyp H
      | H: is_success (if _ then Success _ else Failure _) = true |- _ =>
        destruct_matches_in_hyp H
      | H: (if _ then Success _ else Failure _) = Success _ |- _ =>
        destruct_matches_in_hyp H
      | H: (let/res _ := _ in _) = Success _ |- _ =>
        destruct_matches_in_hyp H
      | H: Success _ = Failure _ |- _ => clear - H; discriminate
      | H: Failure _ = Success _ |- _ => clear - H; discriminate
      end.


Section Logs.
  Record LogEntry :=
    LE { lread0: bool;
         lread1: bool;
         lwrite0: option (list bool);
         lwrite1: option (list bool) }.
  Definition LE_empty :=
    {| lread0 := false;
       lread1 := false;
       lwrite0 := None;
       lwrite1 := None |}.

End Logs.

Section Interp.
  (* Context (int_fn_defs: fn_name_t -> list (list bool) -> option (list bool)). *)
  (* Context (ext_fn_defs: fn_name_t -> (list bool) -> option (list bool)). *)

  (* Weakest precondition:
     given statement S and poscondition R,
     predicate Q such that for any precondition P, {P} S {R} <==> P => Q;
   *)
  Definition state_t := string -> option (list bool).
  Definition log_t := string -> option LogEntry.

  Definition GenericLogEmpty : log_t :=
    fun idx => Some LE_empty.
  Definition GenericGammaEmpty : gamma_t :=
    fun var => None.
  Definition GenericGammaTEmpty : var_types_t :=
    fun var => None.

  Definition action_interpreter A := forall (gamma: gamma_t) (log: log_t), A.
  Definition interp_continuation T A := result (option (gamma_t * log_t * list bool)) T -> A.
  Definition action_continuation T A := interp_continuation T A.
  Definition rule_continuation T A := result (option log_t) T -> A.
  Definition scheduler_continuation T A := result log_t T -> A.
  Definition cycle_continuation T A := result state_t T -> A.

  Definition interpreter T A := forall (log: result log_t T), A.

  Definition action_interpreter2 A :=
    forall (gamma1: gamma_t) (log1: log_t) (gamma2: gamma_t) (log2: log_t), A.

  (* result (option (gamma_t * log_t * list bool)) T ->
     (option action) T ->
     A *)
(*   Definition fun_fn_1: *)
(*       | If cond tbranch fbranch => *)
(*         fun k => *)
(*           cps cond (fun res action2 => *)
(*                       match res with *)
(*                       | Success (Some (gamma, log, v)) => *)
(*                          match v with *)
(*                         | [true] => k (Some (gamma, log, true)) (Some tbranch) *)
(*                         | [false] => k (Some (gamma, log, false)) (Some fbranch) *)
(*                         | _ => k (Failure (__debug__ v "If: cond not single bit")) *)
(*                         end *)
(*                       | _ => k res None *)
(*                       end) *)
(* Fixpoint lolz:= *)
(*   fun_fn_1 r log a (fun res opt_action => *)
(*                       match res with *)
(*                       | Success (Some (gamma, l, _)) => *)
(*                         match opt_action with *)
(*                         | Some action => lolz r log action k gamma l *)

(* Fixpoint lolz2 := *)
(*    fun_fn_1 r log a (fun res opt_action => *)
(*                       match res with *)
(*                       | Success (Some (gamma, l, _)) => *)
(*                         match opt_action with *)
(*                         | Some action => fun_fn_1 r2 log2 a2 (fun res' opt_action' => *)
(*                                                                lolz2 *)
(*     Fixpoint partial_interp_action *)
(*              (r: state_t) *)
(*              (gamma: gamma_t) *)
(*              (sched_log: log_t) *)
(*              (action_log: log_t) *)
(*              (a: action) *)
(*              : result (option (gamma_t * log_t * list bool) * option action) string := *)
(*       match a with *)
(*       | Fail ty_hint => Success None *)
(*       | Var var => *)
(*         let/res var_value := gamma_lookup_var gamma var (__debug__ (gamma,var) "Var not found") in *)
(*         Success (Some (gamma, action_log, var_value)) *)
(*       | Const cst => (Success (Some (gamma, action_log, cst))) *)
(*       | Assign var ex => *)
(*         let/resopt3 gamma, action_log, v_ex := interp_action r gamma sched_log action_log ex in *)
(*         (Success (Some (gamma_set gamma var v_ex, action_log, []))) *)
(*       | Seq a1 a2 => *)
(*         let/resopt3 gamma, action_log, v1 := interp_action r gamma sched_log action_log a1 in *)
(*         interp_action r gamma sched_log action_log a2 *)
(*       | If cond tbranch fbranch => *)
(*         let/resopt3 gamma, action_log, v_cond := interp_action r gamma sched_log action_log cond in *)
(*         match v_cond with *)
(*         | [true] => interp_action r gamma sched_log action_log tbranch *)
(*         | [false] => interp_action r gamma sched_log action_log fbranch *)
(*         | _ => (Failure (__debug__ v_cond "If: cond not single bit")) *)
(*         end *)

(* lolz r log action k gamma l *)

(* (Success (Some l)) action *)
(*                       match opt_action with *)


(*           cps cond (fun res action2 => *)
(*                       match res with *)
(*                       | Success (Some (gamma, log, v)) => *)
(*                         match v with *)
(*                         | [true] => cps tbranch k gamma log *)
(*                         | [false] => cps fbranch k gamma log *)
(*                         | _ => k (Failure (__debug__ v "If: cond not single bit")) *)
(*                         end *)
(*                       | _ => k res *)
(*                       end) *)


  Definition interp_continuation2 T A :=
    result (option (gamma_t * log_t * list bool)) T ->
    result (option (gamma_t * log_t * list bool)) T ->
    A.

  Definition action_continuation2 T A := interp_continuation2 T A.
  Definition rule_continuation2 T A := result (option log_t) T -> result (option log_t) T -> A.
  Definition scheduler_continuation2 T A := result log_t T -> result log_t T -> A.
  Definition cycle_continuation2 T A := result state_t T -> result state_t T -> A.

  Definition interpreter2 T A := forall (log1 log2: result log_t T), A.

  Definition gamma_lookup_var {A} (gamma: gamma_t) (var: var_t) (msg: A) : result (list bool) A :=
    match gamma var with
    | Some t => Success t
    | None => Failure msg
    end.

  Definition gamma_set (gamma: gamma_t) (var: var_t) (v: list bool) : gamma_t :=
    fun var' => if var =? var' then
               Some v
             else gamma var'.

  Definition LE_may_read0 (le: LogEntry) : bool :=
    match le.(lwrite0), le.(lwrite1) with
    | None, None => true
    | _, _ => false
    end.

  Definition LE_may_read1 (le: LogEntry) : bool :=
    match le.(lwrite1) with
    | None => true
    | _ => false
    end.

  Definition LE_may_write0 (le: LogEntry) : bool :=
    match le.(lread1), le.(lwrite0), le.(lwrite1) with
    | false, None, None => true
    | _, _, _ => false
    end.

  Definition LE_may_write1 (le: LogEntry) : bool :=
    match le.(lwrite1) with
    | None => true
    | _ => false
    end.

  Definition r_get_reg (r: state_t) (idx: reg_t) : result (list bool) string :=
    match r idx with
    | Some v => Success v
    | None => Failure (__debug__ (r,idx) "r_get_reg: not found")
    end.

  Definition log_set (log: log_t) (idx: reg_t) (le: LogEntry) : log_t :=
    fun idx' => if String.eqb idx idx' then Some le
             else log idx'.

  Definition log_get (log: log_t) (idx: reg_t) : result LogEntry string :=
    match log idx with
    | Some le => Success le
    | None => Failure (__debug__ (log,idx) "log_get: idx not found")
    end.

  Definition commit_update (st: state_t) (log: log_t) : result state_t string :=
    Success (fun reg =>
               match st reg, log reg with
               | Some v, Some le =>
                 match le.(lwrite1), le.(lwrite0) with
                 | Some w, _ => Some w
                 | _, Some w => Some w
                 | _, _ => Some v
                 end
               | _, _ => None
               end).

  Definition opt_or {A} (o1 o2: option A) :=
    match o1 with
    | Some _ => o1
    | None => o2
    end.

  Definition logentry_app (l1 l2: LogEntry) :=
    {| lread0 := l1.(lread0) || l2.(lread0);
       lread1 := l1.(lread1) || l2.(lread1);
       lwrite0 := opt_or l1.(lwrite0) l2.(lwrite0);
       lwrite1 := opt_or l1.(lwrite1) l2.(lwrite1) |}.

  Definition log_app (l1: log_t) (l2: log_t) : log_t :=
    (fun reg =>
       match l1 reg, l2 reg with
       | Some le1, Some le2 => Some (logentry_app le1 le2)
       | _, _ => None
       end).

   Definition res_opt_bind {A} {B} {C} (res: result (option A) B) (f: A -> result (option C) B) : result (option C) B :=
     match res with
     | Success (Some body) => f body
     | Success None => Success None
     | Failure f => Failure f
     end.
    Notation "'let/resopt' var ':=' expr 'in' body" :=
      (res_opt_bind expr (fun var => body)) (at level 200).

    Notation "'let/resopt2' v1 ',' v2 ':=' expr 'in' body" :=
      (res_opt_bind expr (fun '(v1, v2) => body)) (at level 200).

    Notation "'let/resopt3' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
      (res_opt_bind expr (fun '(v1, v2, v3) => body)) (at level 200).

    Notation "'let/resopt4' v1 ',' v2 ',' v3 ',' v4 ':=' expr 'in' body" :=
      (res_opt_bind expr (fun '(v1, v2, v3, v4) => body)) (at level 200).

  Section Interp.
    Fixpoint interp_action
             (r: state_t)
             (gamma: gamma_t)
             (sched_log: log_t)
             (action_log: log_t)
             (a: action)
             : result (option (gamma_t * log_t * list bool)) string :=
      match a with
      | Fail ty_hint => Success None
      | Var var =>
        let/res var_value := gamma_lookup_var gamma var (__debug__ (gamma,var) "Var not found") in
        Success (Some (gamma, action_log, var_value))
      | Const cst => (Success (Some (gamma, action_log, cst)))
      | Assign var ex =>
        let/resopt3 gamma, action_log, v_ex := interp_action r gamma sched_log action_log ex in
        (Success (Some (gamma_set gamma var v_ex, action_log, [])))
      | Seq a1 a2 =>
        let/resopt3 gamma, action_log, v1 := interp_action r gamma sched_log action_log a1 in
        interp_action r gamma sched_log action_log a2
      | If cond tbranch fbranch =>
        let/resopt3 gamma, action_log, v_cond := interp_action r gamma sched_log action_log cond in
        match v_cond with
        | [true] => interp_action r gamma sched_log action_log tbranch
        | [false] => interp_action r gamma sched_log action_log fbranch
        | _ => (Failure (__debug__ v_cond "If: cond not single bit"))
        end
      | Bind var ex body =>
         let/resopt3 gamma, action_log, v_ex := interp_action r gamma sched_log action_log ex in
         let/resopt3 gamma', action_log, v_body :=
            interp_action r (gamma_set gamma var v_ex) sched_log action_log body in
         Success (Some (gamma, action_log, v_body))
      | Read P0 idx =>
          let/res sched_le := log_get sched_log idx in
          let/res action_le := log_get action_log idx in
          if LE_may_read0 sched_le then
            let/res v := r_get_reg r idx in
            let le' := {|lread0 := true; lread1 := action_le.(lread1);
                                    lwrite0 := action_le.(lwrite0); lwrite1 := action_le.(lwrite1) |} in
            Success (Some (gamma, log_set action_log idx le', v))
          else Success None
      | Read P1 idx =>
          let/res sched_le := log_get sched_log idx in
          let/res action_le := log_get action_log idx in
          if LE_may_read1 sched_le then
            let le' := {| lread0 := action_le.(lread0); lread1 := true;
                          lwrite0 := action_le.(lwrite0); lwrite1 := action_le.(lwrite1) |} in
            let/res v :=
                match action_le.(lwrite0), sched_le.(lwrite0) with
                | Some v, _ => Success v
                | _, Some v => Success v
                | _, _ => r_get_reg r idx
                end in
            Success (Some (gamma, log_set action_log idx le', v))
          else Success None
      | Write P0 idx value =>
          let/resopt3 gamma, action_log, v_value := interp_action r gamma sched_log action_log value in
          let/res sched_le := log_get sched_log idx in
          let/res action_le := log_get action_log idx in
          if LE_may_write0 sched_le && LE_may_write0 action_le then
            let le' := {| lread0 := action_le.(lread0);
                          lread1 := action_le.(lread1);
                          lwrite0 := Some v_value;
                          lwrite1 := action_le.(lwrite1) |} in
            Success (Some (gamma, log_set action_log idx le', []))
          else Success None
      | Write P1 idx value =>
          let/resopt3 gamma, action_log, v_value := interp_action r gamma sched_log action_log value in
          let/res sched_le := log_get sched_log idx in
          let/res action_le := log_get action_log idx in
          if LE_may_write1 sched_le && LE_may_write1 action_le then
            let le' := {| lread0 := action_le.(lread0);
                          lread1 := action_le.(lread1);
                          lwrite0 := action_le.(lwrite0);
                          lwrite1 := Some v_value |} in
            Success (Some (gamma, log_set action_log idx le', []))
          else Success None
      end.

    Definition interp_rule (st: state_t) (sched_log: log_t) (rl: action)
      : result (option log_t) string :=
      match interp_action st GenericGammaEmpty sched_log GenericLogEmpty rl with
      | Success (Some (_, l, _)) => Success (Some l)
      | Success None => Success None
      | Failure f => Failure f
      end.

  End Interp.


  Section LocalInterp.
    Definition restore_gamma {A} (res: result (option (gamma_t * log_t * list bool)) A)
                             (gamma: gamma_t)
                             : result (option (gamma_t * log_t * list bool)) A :=
      let/resopt3 gamma', log, v := res in
      Success (Some (gamma, log, v)).

    Fixpoint interp_action_cps
             (r: state_t)
             (log: log_t) (a: action)
             {A} (k: action_continuation string A)
    : action_interpreter A :=
      let cps a {A} k := @interp_action_cps r log a A k in
      match a with
      | Fail ty_hint => fun k gamma l => k (Success None)
      | Var var => fun k gamma l =>
                    k (let/res var_value := gamma_lookup_var gamma var (__debug__ (gamma,var) "Var not found") in
                       (Success (Some (gamma, l , var_value))))
      | Const cst => fun k gamma l =>
                      k (Success (Some (gamma, l , cst)))
      | Assign var ex => fun k =>
                          cps ex (fun res =>
                                    k (let/res opt := res in
                                       match opt with
                                       | Some (gamma, log, v) => (Success (Some (gamma_set gamma var v, log, [])))
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
                        | _ => k (Failure (__debug__ v "If: cond not single bit"))
                        end
                      | _ => k res
                      end)
      | Bind var ex body => fun k =>
                             cps ex (fun res =>
                                       match res with
                                       | Success (Some (gamma, log, v)) =>
                                         cps body (fun res =>
                                                     k (restore_gamma res gamma))
                                                        (gamma_set gamma var v) log
                                       | _ => k res
                                       end)
      | Read P0 idx =>
        fun k gamma l =>
          k (let/res sched_le := log_get log idx in
             let/res action_le := log_get l idx in
             if LE_may_read0 sched_le then
               let/res v := r_get_reg r idx in
               let le' := {|lread0 := true; lread1 := action_le.(lread1);
                                       lwrite0 := action_le.(lwrite0); lwrite1 := action_le.(lwrite1) |} in
               Success (Some (gamma, log_set l idx le', v))
             else Success None)
      | Read P1 idx =>
        fun k gamma l =>
          k (let/res sched_le := log_get log idx in
             let/res action_le := log_get l idx in
             if LE_may_read1 sched_le then
               let le' := {| lread0 := action_le.(lread0); lread1 := true;
                             lwrite0 := action_le.(lwrite0); lwrite1 := action_le.(lwrite1) |} in
               let/res v :=
                   match action_le.(lwrite0), sched_le.(lwrite0) with
                   | Some v, _ => Success v
                   | _, Some v => Success v
                   | _, _ => r_get_reg r idx
                   end in
               Success (Some (gamma, log_set l idx le', v))
             else Success None
            )
      | Write P0 idx value =>
        fun k =>
          cps value (fun res =>
                       match res with
                       | Success (Some (gamma, l, v)) =>
                           k (let/res sched_le := log_get log idx in
                              let/res action_le := log_get l idx in
                              if LE_may_write0 sched_le && LE_may_write0 action_le then
                                let le' := {| lread0 := action_le.(lread0);
                                              lread1 := action_le.(lread1);
                                              lwrite0 := Some v;
                                              lwrite1 := action_le.(lwrite1) |} in
                                Success (Some (gamma, log_set l idx le', []))
                              else Success None)
                       | _ => k res
                       end)
      | Write P1 idx value =>
        fun k =>
          cps value (fun res =>
                       match res with
                       | Success (Some (gamma, l, v)) =>
                           k (let/res sched_le := log_get log idx in
                              let/res action_le := log_get l idx in
                              if LE_may_write1 sched_le && LE_may_write1 action_le then
                                let le' := {| lread0 := action_le.(lread0);
                                              lread1 := action_le.(lread1);
                                              lwrite0 := action_le.(lwrite0);
                                              lwrite1 := Some v |} in
                                Success (Some (gamma, log_set l idx le', []))
                              else Success None)
                       | _ => k res
                       end)

      (* | _ => fun k gamma l => k (Failure (__debug__ a "TODO")) *)
      end k.
  End LocalInterp.

  Definition rule := action.

  Definition interp_rule_cps (st: state_t) (rl: rule) {A} (k: rule_continuation string A)
    : interpreter string A :=
    fun L_res =>
      match L_res with
      | Success L =>
        interp_action_cps st L rl (fun res =>
                                     match res with
                                     | Success (Some (_, l, _)) => k (Success (Some l))
                                     | Success None => k (Success None)
                                     | Failure f => k (Failure f)
                                     end) GenericGammaEmpty GenericLogEmpty
      | Failure f => k (Failure f)
      end.
  Section Scheduler.
    Context {rule_name_t: Type}.
    Context (r: state_t).
    Context (rules: rule_name_t -> rule).

    Inductive scheduler :=
    | Done
    | Cons (r: rule_name_t) (s: scheduler)
    .

    Fixpoint interp_scheduler' (s: scheduler) (sched_log: log_t) : result log_t string :=
      match s with
      | Done => Success sched_log
      | Cons rl s =>
        let/res opt_action_log := interp_rule r sched_log (rules rl) in
        match opt_action_log with
        | Some action_log => interp_scheduler' s (log_app action_log sched_log)
        | None => interp_scheduler' s sched_log
        end
      end.

    Definition interp_scheduler (s: scheduler) : result log_t string :=
      interp_scheduler' s GenericLogEmpty.

    Fixpoint typecheck_schedule
             (reg_types: reg_types_t)
             (s: scheduler) (rls: rule_name_t -> action) : result unit string :=
      match s with
      | Done => Success tt
      | Cons r0 s =>
          match type_check reg_types GenericGammaTEmpty (rls r0) with
          | Success 0 => typecheck_schedule reg_types s rls
          | Success n => Failure (__debug__ (n, r0) "typecheck_schedule: rl not type 0")
          | Failure s => Failure s
          end
      end.


    Fixpoint interp_scheduler'_cps
             (s: scheduler)
             {A} (k: scheduler_continuation string A)
             {struct s} : interpreter string A :=
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
               {A} (k: scheduler_continuation string A) : A :=
      interp_scheduler'_cps s k (Success GenericLogEmpty).
  End Scheduler.

  Definition interp_cycle {rule_name_t: Type} (rules: rule_name_t -> rule)
           (s: scheduler) (r: state_t) : result state_t string :=
    match interp_scheduler r rules s with
    | Success log => commit_update r log
    | Failure f => Failure f
    end.

  Section Interp2.
    Definition interp_action2 (st1: state_t) (gamma1: gamma_t) (sched_log1: log_t) (action_log1: log_t) (a1: action)
                              (st2: state_t) (gamma2: gamma_t) (sched_log2: log_t) (action_log2: log_t) (a2: action)
                              : result (option (gamma_t * log_t * list bool)) string *
                                result (option (gamma_t * log_t * list bool)) string :=
      (interp_action st1 gamma1 sched_log1 action_log1 a1,
       interp_action st2 gamma2 sched_log2 action_log2 a2).


    Definition interp_rule2 (st1: state_t) (sched_log1: log_t) (rl1: action)
                            (st2: state_t) (sched_log2: log_t) (rl2: action)
                            : result (option log_t) string * result (option log_t) string :=
      (interp_rule st1 sched_log1 rl1, interp_rule st2 sched_log2 rl2).

  Definition interp_scheduler2
            {rule_name_t1: Type} (rules1: rule_name_t1 -> rule)
            (s1: scheduler) (r1: state_t)
            {rule_name_t2: Type} (rules2: rule_name_t2 -> rule)
            (s2: scheduler) (r2: state_t) :=
    (interp_scheduler r1 rules1 s1, interp_scheduler r2 rules2 s2).

    Definition interp_cycle2
               {rule_name_t1: Type} (rules1: rule_name_t1 -> rule)
               (s1: scheduler) (r1: state_t)
               {rule_name_t2: Type} (rules2: rule_name_t2 -> rule)
               (s2: scheduler) (r2: state_t)
      : result state_t string * result state_t string :=
      (interp_cycle rules1 s1 r1, interp_cycle rules2 s2 r2).
  End Interp2.

  Section Cps2.
    Definition interp_action_cps2
               (r1: state_t) (sched_log1: log_t) (a1: action)
               (r2: state_t) (sched_log2: log_t) (a2: action)
               {A} (k: action_continuation2 string A)
               : action_interpreter2 A :=
      fun gamma1 log1 gamma2 log2 =>
        interp_action_cps r2 sched_log2 a2
                          (fun res1 => interp_action_cps r1 sched_log1 a1 (fun res0 => k res0 res1) gamma1 log1) gamma2 log2.

        (* interp_action_cps r1 sched_log1 a1 (fun res1 => *)
        (*   interp_action_cps r2 sched_log2 a2 (fun res2 => k res1 res2)). *)

    Definition interp_action_cps2'
               (r1: state_t) (sched_log1: log_t) (a1: action)
               (r2: state_t) (sched_log2: log_t) (a2: action)
               {A} (k: action_continuation2 string A)
               : action_interpreter2 A :=
      fun gamma1 log1 gamma2 log2 =>
        interp_action_cps r1 sched_log1 a1 (fun res0 => interp_action_cps r2 sched_log2 a2 (k res0) gamma2 log2) gamma1 log1.



    Definition extract_res_log {A} (res: result (option (gamma_t * log_t * list bool)) A)
                               : result (option log_t) A :=
      match res with
      | Success (Some (_, l, _)) => Success (Some l)
      | Success None => Success None
      | Failure f => Failure f
      end.

    Definition interp_rule_cps2 (st1: state_t) (rl1: rule)
                                (st2: state_t) (rl2: rule)
                                {A} (k: rule_continuation2 string A)
                                : interpreter2 string A :=
      fun L_res1 L_res2 =>
        match L_res1, L_res2 with
        | Success L1, Success L2 =>
          interp_action_cps2 st1 L1 rl1 st2 L2 rl2
                             (fun res1 res2 => k (extract_res_log res1) (extract_res_log res2))
                             GenericGammaEmpty GenericLogEmpty GenericGammaEmpty GenericLogEmpty
        | Success L1, Failure f2 =>
          interp_action_cps st1 L1 rl1 (fun res1 => k (extract_res_log res1) (Failure f2))
                            GenericGammaEmpty GenericLogEmpty
        | Failure f1, Success L2 =>
           interp_action_cps st2 L2 rl2 (fun res2 => k (Failure f1) (extract_res_log res2))
                             GenericGammaEmpty GenericLogEmpty
        | Failure f1, Failure f2 =>
          k (Failure f1) (Failure f2)
        end.

    (* Definition interp_scheduler_cps2 *)
    (*            (st1: state_t) {rule_name_t1: Type} (rules1: rule_name_t1 -> rule) *)
    (*            (s1: @scheduler rule_name_t1) *)
    (*            (st2: state_t) {rule_name_t2: Type} (rules2: rule_name_t2 -> rule) *)
    (*            (s2: @scheduler rule_name_t2) *)
    (*            {A} (k: scheduler_continuation2 string A) *)
    (*            : A := *)
    (*   interp_scheduler_cps st1 rules1 s1 (fun log1 => *)
    (*     interp_scheduler_cps st2 rules2 s2 (fun log2 => k log1 log2)). *)
  End Cps2.

    Definition WF_state (types: reg_types_t) (st: state_t) : Prop :=
      forall reg, match types reg, st reg with
             | Some n, Some v => List.length v = n
             | None, _ => True
             | _, _ => False
             end.

    Definition WF_LE (le: LogEntry) (n: nat) : Prop :=
      (match le.(lwrite0) with
       | Some v => List.length v = n
       | _ => True
       end) /\
      (match le.(lwrite1) with
       | Some v => List.length v = n
       | _ => True
       end).

    Lemma WF_LE_empty: forall n,
        WF_LE LE_empty n.
    Proof.
      consider WF_LE. intros. simpl. auto.
    Qed.

    Definition WF_log (types: reg_types_t) (log: log_t) : Prop :=
      forall reg, match types reg, log reg with
             | Some n, Some le => WF_LE le n
             | None, _ => True
             | _, _ => False
             end.

    Lemma WF_LE_app: forall l1 l2 n,
        WF_LE l1 n ->
        WF_LE l2 n ->
        WF_LE (logentry_app l1 l2) n.
    Proof.
      intros. consider WF_LE. propositional.
      unfold logentry_app. simpl. unfold opt_or.
      split_ands_in_goal; destruct_all_matches; auto.
    Qed.

    Definition WF_gamma (var_types: var_types_t) (gamma: gamma_t) : Prop :=
      forall var, match var_types var, gamma var with
             | Some n, Some v => List.length v = n
             | None, _ => True
             | _, _ => False
             end.

    Lemma WF_gamma_GenericGammaEmpty (gamma: gamma_t):
      WF_gamma GenericGammaTEmpty gamma.
    Proof.
      unfold WF_gamma, GenericGammaTEmpty. auto.
    Qed.

    Lemma WF_log_GenericLogEmpty:
      forall (reg_types: reg_types_t),
        WF_log reg_types GenericLogEmpty.
    Proof.
      intros. unfold WF_log. intros. unfold is_some in *.
      propositional. unfold GenericLogEmpty.
      destruct_match; auto.
      apply WF_LE_empty.
    Qed.

    Lemma WF_log_app:
      forall (reg_types: reg_types_t) (l1 l2: log_t),
        WF_log reg_types l1 ->
        WF_log reg_types l2 ->
        WF_log reg_types (log_app l1 l2).
    Proof.
      intros. unfold WF_log in *. intros. unfold is_some, log_app in *.
      specialize H with (reg := reg). specialize H0 with (reg := reg).
      destruct_match; auto.
      destruct_match; auto.
      destruct_match; auto.
      apply WF_LE_app; auto.
    Qed.
Set Nested Proofs Allowed.
    Lemma is_some_Some {A} (v: A):
      is_some (Some v).
    Proof.
      unfold is_some. eauto.
    Qed.

    Lemma is_some_None_False {A: Type} :
      @is_some A None ->
      False.
    Proof.
      unfold is_some. propositional. discriminate.
    Qed.

    Lemma is_some_gamma_set:
      forall gamma var1 var2 v,
        is_some (gamma var2) ->
        is_some (gamma_set gamma var1 v var2).
    Proof.
      intros. consider @is_some. consider gamma_set. propositional.
      destruct_match; eauto.
    Qed.

Lemma gamma_set_var :
  forall gamma var v,
    gamma_set gamma var v var = Some v.
Proof.
  intros. unfold gamma_set.
  rewrite String.eqb_refl. reflexivity.
Qed.
Lemma gamma_set_neq_var :
  forall gamma var var' v,
    var' <> var ->
    gamma_set gamma var' v var = gamma var.
Proof.
  intros. unfold gamma_set.
  destruct_match.
  - apply String.eqb_eq in Heqb. subst. congruence.
  - reflexivity.
Qed.
Lemma is_some_log_set:
  forall log reg reg' le,
    is_some (log reg) ->
    is_some (log_set log reg' le reg).
Proof.
  intros. consider @is_some. consider log_set. propositional.
  destruct_match; eauto.
Qed.

Lemma log_set_eq (log: log_t) (idx: reg_t) (le: LogEntry) :
  log_set log idx le idx = Some le.
Proof.
  consider log_set. destruct_match; auto.
  rewrite String.eqb_refl in Heqb. discriminate.
Qed.

Lemma log_set_neq (log: log_t) (idx idx': reg_t) (le: LogEntry) :
  idx' <> idx ->
  log_set log idx' le idx = log idx.
Proof.
  consider log_set. destruct_match; auto.
  apply String.eqb_eq in Heqb. congruence.
Qed.

    Ltac solve_typecheck_action_correct:=
      repeat match goal with
      | _ => progress simplify_result
      | H: (match ?v with
            | Some _ => _
            | None => False
            end) |- _ =>
        destruct_matches_in_hyp H; [ | contradiction]
      | H: Some _ = Some _ |- _ =>
        inversions H
      | H: is_some (Some ?a) -> _ |- _ =>
        specialize H with (1 := is_some_Some _)
      | H1: is_some ?v -> _,
        H2: ?v = Some _ |- _ =>
        rewrite H2 in H1
      | H: is_some None |- _ =>
        exfalso; apply is_some_None_False in H; auto
     | H: is_some (?gamma ?var2) |- is_some (gamma_set ?gamma ?var1 _ ?var2) =>
        apply is_some_gamma_set; assumption
      | H : String.eqb _ _ = true|- _ =>
        apply String.eqb_eq in H; subst
      | H : String.eqb _ _ = false|- _ =>
        apply String.eqb_neq in H; subst
      | H : Nat.eqb _ _ = true |- _ =>
        apply PeanoNat.Nat.eqb_eq in H; subst
      | |- context[gamma_set ?gamma ?var _ ?var] =>
        rewrite gamma_set_var
      | H : ?var' <> ?var
        |- context[gamma_set _ ?var' _ ?var] =>
        rewrite gamma_set_neq_var
      | H : ?idx' <> ?idx
       |- context[log_set _ ?idx' _ ?idx] =>
        rewrite log_set_neq
      | H: is_some (?log ?reg)
        |- is_some (log_set ?log _ _ ?reg) =>
        apply is_some_log_set; assumption
      | |- context[log_set ?log ?idx _ ?idx] =>
        rewrite log_set_eq
      | |- _ => progress propositional
      | |- _ => progress simpl_match
      | |- _ => auto
      end.
    Ltac destruct_one_interp_action :=
        match goal with
        | [  |- context[interp_action] ] =>
          destruct interp_action as [[((?, ?), ?) | ] | ]; simpl; auto
        end.

    Lemma typecheck_action_correct:
      forall (reg_types: reg_types_t) (st: state_t) (sched_log: log_t)
        action (var_types: var_types_t) (action_log: log_t) (gamma: gamma_t) (n: nat),
        WF_state reg_types st ->
        WF_log reg_types sched_log ->
        WF_log reg_types action_log ->
        WF_gamma var_types gamma ->
        type_check reg_types var_types action = Success n ->
        match interp_action st gamma sched_log action_log action with
        | Success (Some (gamma', log, value)) =>
          WF_log reg_types log /\ WF_gamma var_types gamma' /\ List.length value = n
        | Success None => True
        | _ => False
        end.
    Proof.
      unfold interp_rule.
      consider WF_gamma. consider WF_log. consider WF_state.
      induction action0; cbn; intros * Hstate Hsched Haction Hgamma Htype.
      all: consider @lookup_var_type; solve_typecheck_action_correct.
      - pose proof (Hgamma var) as Hgamma_var.
        unfold gamma_lookup_var. destruct_match; solve_typecheck_action_correct; auto.
      - specialize IHaction0 with
            (var_types := var_types) (action_log := action_log) (gamma := gamma).
        specialize IHaction0 with (5 := Heqr). propositional.
        destruct_one_interp_action; propositional.
        split_ands_in_goal; auto.
        intros. specialize IHaction0 with (var := var0).
        bash_destruct IHaction0; auto.
        unfold gamma_set. rewrite Heqo1. destruct_match; auto.
        solve_typecheck_action_correct.
        rewrite Heqo0 in Heqo. solve_typecheck_action_correct.
      - specialize IHaction0_1 with
            (var_types := var_types) (action_log := action_log) (gamma := gamma).
        specialize IHaction0_1 with (5 := Heqr). propositional.
        destruct_one_interp_action; propositional;
          split_ands_in_goal; solve_typecheck_action_correct.
        specialize IHaction0_2 with
            (var_types := var_types) (action_log := l) (gamma := g).
        specialize IHaction0_2 with (5 := Htype). propositional.
      - bash_destruct Htype.
        specialize IHaction0_1 with
            (var_types := var_types) (action_log := action_log) (gamma := gamma).
        specialize IHaction0_1 with (5 := Heqr). propositional.
        destruct_one_interp_action; propositional; solve_typecheck_action_correct.
        destruct l0; simpl in Heqb; try discriminate.
        destruct b; destruct l0; simpl in Heqb; try discriminate.
        * specialize IHaction0_2 with
            (var_types := var_types) (action_log := l) (gamma := g).
          specialize IHaction0_2 with (5 := Heqr0). propositional.
        * specialize IHaction0_3 with
            (var_types := var_types) (action_log := l) (gamma := g).
          specialize IHaction0_3 with (5 := Heqr1). propositional.
      - specialize IHaction0_1 with
            (var_types := var_types) (action_log := action_log) (gamma := gamma).
        specialize IHaction0_1 with (5 := Heqr). propositional.
        destruct_one_interp_action; propositional; solve_typecheck_action_correct.
        specialize IHaction0_2 with
            (action_log := l) (gamma := gamma_set g v l0).
          specialize IHaction0_2 with (5 := Htype). propositional.
        assert_pre IHaction0_2.
        { intros. destruct_match; solve_typecheck_action_correct.
          apply eqb_neq in Heqb.
          pose proof (IHaction0_1 var) as Hvar.
          destruct_match; auto.
        }
        { propositional.
          destruct_one_interp_action; propositional; solve_typecheck_action_correct.
        }
      - consider @lookup_reg_type. solve_typecheck_action_correct.
        pose proof Hsched idx as Hsched__idx.
        pose proof Hstate idx as Hstate__idx.
        pose proof Haction idx as Haction__idx.
        rewrite Heqo in *. solve_typecheck_action_correct.
        unfold log_get, r_get_reg. repeat simpl_match.
        solve_typecheck_action_correct.
        destruct_match.
        + destruct_match; auto.
          split_ands_in_goal; eauto.
          intros. propositional.
          destruct_match; auto.
          pose proof Haction reg as Haction__reg. repeat simpl_match.
          destruct_matches_in_hyp Haction__reg; auto.
          destruct_with_eqn (idx =? reg); solve_typecheck_action_correct.
          rewrite Heqo0 in Heqo4. solve_typecheck_action_correct.
        + destruct_match; auto.
          destruct_match; auto.
          * split_ands_in_goal; eauto.
            { intros. propositional.
              destruct_match; auto.
              pose proof Haction reg as Haction__reg. repeat simpl_match.
              destruct_matches_in_hyp Haction__reg; auto.
              destruct_with_eqn (idx =? reg); solve_typecheck_action_correct.
              rewrite Heqo0 in Heqo5. solve_typecheck_action_correct.
              unfold WF_LE in Haction__reg, Haction__idx. repeat simpl_match. propositional.
              unfold WF_LE; simpl; split; auto.
            }
            { unfold WF_LE in Haction__idx. repeat simpl_match. propositional. }
          * destruct_match; auto.
            { split_ands_in_goal; subst; eauto.
              { intros. destruct_match; auto.
                pose proof Haction reg as Haction__reg. repeat simpl_match.
                destruct_matches_in_hyp Haction__reg; auto.
                destruct_with_eqn (idx =? reg); solve_typecheck_action_correct.
                rewrite Heqo0 in Heqo6. solve_typecheck_action_correct.
                unfold WF_LE in Haction__reg, Haction__idx. repeat simpl_match. propositional.
                unfold WF_LE; simpl; split; auto.
              }
              { unfold WF_LE in Hsched__idx; repeat simpl_match; propositional. }
            }
            { split_ands_in_goal; auto. intros. destruct_match; auto.
              pose proof Haction reg as Haction__reg. repeat simpl_match.
              destruct_matches_in_hyp Haction__reg; auto.
              destruct_with_eqn (idx =? reg); solve_typecheck_action_correct.
              rewrite Heqo0 in Heqo6. solve_typecheck_action_correct.
              unfold WF_LE in Haction__reg, Haction__idx. repeat simpl_match. propositional
              unfold WF_LE; simpl; split; auto.
            }
      - consider @lookup_reg_type. solve_typecheck_action_correct.
        pose proof Hsched idx as Hsched__idx.
        pose proof Hstate idx as Hstate__idx.
        pose proof Haction idx as Haction__idx.
        rewrite Heqo in *. solve_typecheck_action_correct.
        unfold log_get, r_get_reg. repeat simpl_match.
        solve_typecheck_action_correct.
        destruct port.
        + specialize IHaction0 with
            (var_types := var_types) (action_log := action_log) (gamma := gamma).
          specialize IHaction0 with (5 := Heqr0). propositional.
          destruct_one_interp_action; auto. propositional.
          pose proof IHaction1 idx. simpl_match.
          solve_typecheck_action_correct.
          destruct_match; auto.
          split_ands_in_goal; auto.
          intros. destruct_match; auto.
          pose proof Haction reg as Haction__reg. repeat simpl_match.
          destruct_matches_in_hyp Haction__reg; auto.
          destruct_with_eqn (idx =? reg); solve_typecheck_action_correct.
          * rewrite Heqo0 in Heqo5. unfold WF_LE; simpl. solve_typecheck_action_correct.
            rewrite IHaction3. rewrite Heqo in Heqo4. solve_typecheck_action_correct. split; auto.
            destruct_match; auto.
            unfold WF_LE in H. propositional. simpl_match. auto.
          * pose proof IHaction1 reg. simpl_match. solve_typecheck_action_correct.
        + specialize IHaction0 with
            (var_types := var_types) (action_log := action_log) (gamma := gamma).
          specialize IHaction0 with (5 := Heqr0). propositional.
          destruct_one_interp_action; auto. propositional.
          pose proof IHaction1 idx. simpl_match.
          solve_typecheck_action_correct.
          destruct_match; auto.
          split_ands_in_goal; auto.
          intros. destruct_match; auto.
          pose proof Haction reg as Haction__reg. repeat simpl_match.
          destruct_matches_in_hyp Haction__reg; auto.
          destruct_with_eqn (idx =? reg); solve_typecheck_action_correct.
          * rewrite Heqo0 in Heqo5. unfold WF_LE; simpl. solve_typecheck_action_correct.
            rewrite IHaction3. rewrite Heqo in Heqo4. solve_typecheck_action_correct. split; auto.
            destruct_match; auto.
            unfold WF_LE in H. propositional. simpl_match. auto.
          * pose proof IHaction1 reg. simpl_match. solve_typecheck_action_correct.
    Qed.

    Lemma typecheck_rule_correct:
      forall (reg_types: reg_types_t) (st: state_t) (sched_log: log_t) action,
        WF_state reg_types st ->
        WF_log reg_types sched_log ->
        type_check reg_types GenericGammaTEmpty action = Success 0 ->
        match interp_rule st sched_log action with
        | Success (Some log) => WF_log reg_types log
        | Success None => True
        | _ => False
        end.
    Proof.
      intros * Hstate Hlog Htype.
      unfold interp_rule.
      specialize typecheck_action_correct with
          (1 := Hstate) (2 := Hlog) (3 := WF_log_GenericLogEmpty _)
          (4 := WF_gamma_GenericGammaEmpty GenericGammaEmpty) (5 := Htype).
      destruct_one_interp_action. propositional.
    Qed.

    Lemma typecheck_schedule_correct':
      forall {rule_name_t: Type} (reg_types: reg_types_t)
        (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t) (sched_log: log_t),
        is_success (typecheck_schedule reg_types s rls) = true ->
        WF_state reg_types st ->
        WF_log reg_types sched_log ->
        match (let/res log := interp_scheduler' st rls s sched_log in commit_update st log) with
        | Success st' => WF_state reg_types st'
        | _ => False
        end.
    Proof.
      induction s.
      - intros * Htype Hstate Hlog. simpl interp_scheduler'. simpl.
        consider WF_state. consider WF_log. intros *.
        specialize Hstate with (reg := reg).
        specialize Hlog with (reg := reg).
        repeat destruct_match; propositional; unfold is_some; eauto.
        + consider @WF_LE. simpl_match. propositional.
        + consider @WF_LE. simpl_match. propositional.
      - intros * Htype Hstate Hlog. simpl.
        simpl in Htype.
        destruct_matches_in_hyp Htype.
        + specialize typecheck_rule_correct with
              (1 := Hstate) (action := rls r) (sched_log := sched_log).
          rewrite Heqr0. simpl. propositional.
          destruct_matches_in_hyp Htype; simplify_result; subst; propositional.
          destruct_match.
          * destruct s0; auto.
            { apply IHs; auto. apply WF_log_app; auto. }
            { apply IHs; auto. }
          * auto.
        + simpl in Htype. discriminate.
    Qed.

    Lemma typecheck_schedule_correct:
      forall {rule_name_t: Type} (reg_types: reg_types_t)
        (s: @scheduler rule_name_t) (rls: rule_name_t -> action) (st: state_t),
        is_success (typecheck_schedule reg_types s rls) = true ->
        WF_state reg_types st ->
        match interp_cycle rls s st with
        | Success st' => WF_state reg_types st'
        | _ => False
        end.
    Proof.
      unfold interp_cycle. unfold interp_scheduler.
      intros. apply typecheck_schedule_correct'; auto.
      apply WF_log_GenericLogEmpty.
    Qed.

    Section DoSteps.
      Context {rule_name_t: Type}.
      Context (rules: rule_name_t -> rule).
      Context (schedule: @scheduler rule_name_t).
      Context {tau: Type}.
      Context (get_obs: state_t -> result tau string).

      Definition trace : Type := list tau.

      Definition step (st: state_t) : result (state_t * tau) string :=
        let/res st' := interp_cycle rules schedule st in
        let/res t := get_obs st' in
        Success (st',t).

      Fixpoint step_n' (n: nat) (st: state_t) : result (state_t * trace) string :=
        match n with
        | 0 => Success (st, [])
        | S n =>
          let/res2 st',t := step st in
          let/res2 st'', tr := step_n' n st' in
          Success (st'', (t)::tr)
        end.

      Definition step_n (n: nat) (st: state_t) : result trace string :=
        let/res2 st,tr := step_n' n st in
        Success tr.

      Definition WF_get_obs (reg_types: reg_types_t): Prop :=
        forall st, WF_state reg_types st -> is_success (get_obs st) = true.

      Lemma step_n_success:
        forall (n: nat) (st: state_t) (reg_types: reg_types_t),
          WF_state reg_types st ->
          is_success (typecheck_schedule reg_types schedule rules) = true ->
          WF_get_obs (reg_types) ->
          is_success (step_n n st) = true.
      Proof.
        unfold step_n.
        induction n; intros * Hwf Htype Hobs; auto. simpl.
        unfold step.
        specialize @typecheck_schedule_correct with (rule_name_t := rule_name_t) (1 := Htype) (2 := Hwf).
        intros Hwf'.
        destruct_match; propositional.
        specialize IHn with (1 := Hwf') (2 := Htype).
        propositional.
        consider WF_get_obs. pose proof Hobs _ Hwf' as Hobs_succ.
        destruct_match; simplify_result.
          destruct_match_pairs; subst; auto.
      Qed.

    End DoSteps.

  Definition interp_cycle_cps {rule_name_t: Type} (rules: rule_name_t -> rule)
           (s: scheduler) (r: state_t)
           {A} (k: cycle_continuation string A) : A :=
  interp_scheduler_cps r rules s (fun res_L => k (let/res L := res_L in
                                               commit_update r L)).

  (* Definition interp_cycle_cps2 *)
  (*            {rule_name_t1: Type} (rules1: rule_name_t1 -> rule) *)
  (*            (s1: @scheduler rule_name_t1) (r1: state_t) *)
  (*            {rule_name_t2: Type} (rules2: rule_name_t2 -> rule) *)
  (*            (s2: @scheduler rule_name_t2) (r2: state_t) *)
  (*            {A} (k: cycle_continuation2 string A) : A := *)
  (* interp_scheduler_cps2 r1 rules1 s1 *)
  (*                       r2 rules2 s2 *)
  (*                       (fun res_L1 res_L2 => k (let/res L := res_L1 in commit_update r1 L) *)
  (*                                            (let/res L := res_L2 in commit_update r2 L)). *)

  Section WP.
    Definition action_precondition := action_interpreter Prop.
    Definition action_postcondition := action_continuation string Prop.
    Definition precondition := interpreter string Prop.
    Definition rule_postcondition := rule_continuation string Prop.
    Definition scheduler_postcondition := scheduler_continuation string Prop.
    Definition cycle_postcondition := cycle_continuation string Prop.

    Definition wp_action (r: state_t) (L: log_t) (a: action)
               (post: action_postcondition) : action_precondition :=
      interp_action_cps r L a post.

    Definition wp_rule (r: state_t) (rl: rule) (post: rule_postcondition) : precondition :=
      interp_rule_cps r rl post.

    Definition wp_scheduler {rule_name_t: Type} (r: state_t) (rules: rule_name_t -> rule) (s: scheduler) (post: scheduler_postcondition) : Prop :=
      interp_scheduler_cps r rules s post.

    Definition wp_cycle {rule_name_t: Type} (r: state_t) (rules: rule_name_t -> rule)
               (s: scheduler) r (post: cycle_postcondition) : Prop :=
      interp_cycle_cps rules s r post.

    Definition action_precondition2 := action_interpreter2 Prop.
    Definition action_postcondition2 := action_continuation2 string Prop.
    Definition precondition2 := interpreter2 string Prop.
    Definition rule_postcondition2 := rule_continuation2 string Prop.
    Definition scheduler_postcondition2 := scheduler_continuation2 string Prop.
    Definition cycle_postcondition2 := cycle_continuation2 string Prop.

    Definition wp_action2 (r1: state_t) (L1: log_t) (a1: action)
                          (r2: state_t) (L2: log_t) (a2: action)
                          (post: action_postcondition2) : action_precondition2 :=
      interp_action_cps2 r1 L1 a1 r2 L2 a2 post.

    Definition wp_action2' (r1: state_t) (L1: log_t) (a1: action)
                           (r2: state_t) (L2: log_t) (a2: action)
                           (post: action_postcondition2) : action_precondition2 :=
      interp_action_cps2' r1 L1 a1 r2 L2 a2 post.

    Definition wp_rule2 (r1: state_t) (rl1: rule)
                        (r2: state_t) (rl2: rule)
                        (post: rule_postcondition2) : precondition2 :=
      interp_rule_cps2 r1 rl1 r2 rl2 post.

    (* Definition wp_scheduler2 {rule_name_t1: Type} (r1: state_t) (rules1: rule_name_t1 -> rule) (s1: scheduler) *)
    (*                          {rule_name_t2: Type} (r2: state_t) (rules2: rule_name_t2 -> rule) (s2: scheduler) *)
    (*                          (post: scheduler_postcondition2) : Prop := *)
    (*   interp_scheduler_cps2 r1 rules1 s1 r2 rules2 s2 post. *)

    (* Definition wp_cycle2 {rule_name_t1: Type} (r1: state_t) (rules1: rule_name_t1 -> rule) (s1: @scheduler rule_name_t1) *)
    (*                      {rule_name_t2: Type} (r2: state_t) (rules2: rule_name_t2 -> rule) (s2: @scheduler rule_name_t2) *)
    (*                      (post: cycle_postcondition2) : Prop := *)
    (*   interp_cycle_cps2 rules1 s1 r1 rules2 s2 r2 post. *)

  End WP.

  Section Proofs.
    Lemma interp_action_cps_correct:
      forall (r: state_t) (sched_log: log_t) (a: action)
        {A} (k: action_continuation string A) (gamma: gamma_t) (action_log: log_t),
        interp_action_cps r sched_log a k gamma action_log =
        k (interp_action r gamma sched_log action_log a).
    Proof.
      fix IHa 3; destruct a; cbn; intros;
      repeat match goal with
             | _ => progress simpl
             | [ H: context[_ = _] |- _ ] => rewrite H
             | [  |- context[interp_action] ] => destruct interp_action as [((?, ?), ?) | ]
             | [  |- context[match ?x with _ => _ end] ] => destruct x
             | _ => reflexivity || assumption
             end.
    Qed.

    Lemma interp_action_cps_correct_rev:
      forall (r: state_t)
        (sched_log: log_t)
        (a: action)
        (gamma: gamma_t)
        (action_log: log_t),
        interp_action r gamma sched_log action_log a =
        interp_action_cps r sched_log a id gamma action_log.
    Proof.
      intros; rewrite interp_action_cps_correct; reflexivity.
    Qed.

    Lemma interp_rule_cps_correct:
      forall (r: state_t)
        (L: log_t)
        (a: action )
        {A} (k: _ -> A),
        interp_rule_cps r a k (Success L) =
        k (interp_rule r L a).
    Proof.
      unfold interp_rule, interp_rule_cps; intros.
      rewrite interp_action_cps_correct.
      destruct interp_action as [[((?, ?), ?) | ] | ]; reflexivity.
    Qed.

    Lemma interp_rule_cps_correct_rev:
      forall (r: state_t)
        (L: log_t)
        (a: action),
        interp_rule r L a =
        interp_rule_cps r a id (Success L).
    Proof.
      intros; rewrite interp_rule_cps_correct; reflexivity.
    Qed.

    Lemma interp_scheduler'_cps_correct:
      forall {rule_name_t: Type} (r: state_t)
        (rules: rule_name_t -> rule)
        (s: scheduler)
        (L: log_t )
        {A} (k: _ -> A),
        interp_scheduler'_cps r rules s k (Success L) =
        k (interp_scheduler' r rules s L).
    Proof.
      induction s; cbn; intros.
      - reflexivity.
      - all: repeat match goal with
             | _ => progress simpl
             | _ => rewrite interp_action_cps_correct
             | [ H: context[_ = _] |- _ ] => rewrite H
             | [  |- context[interp_rule] ] => unfold interp_rule; destruct interp_action as [[((?, ?), ?) | ] | ]
             | [  |- context[match ?x with _ => _ end] ] => destruct x
             | _ => reflexivity
             end.
    Qed.

    Lemma interp_scheduler_cps_correct:
      forall {rule_name_t: Type} (r: state_t) (rules: rule_name_t -> rule)
        (s: scheduler)
        {A} (k: _ -> A),
        interp_scheduler_cps r rules s k =
        k (interp_scheduler r rules s).
    Proof.
      intros; apply interp_scheduler'_cps_correct.
    Qed.

    Lemma interp_cycle_cps_correct:
      forall {rule_name_t: Type} (r: state_t) (rules: rule_name_t -> rule)
        (s: scheduler)
        {A} (k: _ -> A),
        interp_cycle_cps rules s r k =
        k (interp_cycle rules s r).
    Proof.
      unfold interp_cycle, interp_cycle_cps; intros; rewrite interp_scheduler_cps_correct.
      reflexivity.
    Qed.

    Lemma interp_cycle_cps_correct_rev:
      forall {rule_name_t: Type} (r: state_t) (rules: rule_name_t -> rule)
        (s: scheduler),
        interp_cycle rules s r =
        interp_cycle_cps rules s r id.
    Proof.
      intros; rewrite interp_cycle_cps_correct; reflexivity.
    Qed.

    Lemma interp_action_cps2_correct:
      forall (r1: state_t) (sched_log1: log_t) (a1: action)
        (r2: state_t) (sched_log2: log_t) (a2: action)
        {A} (k: action_continuation2 string A)
        (gamma1: gamma_t) (action_log1: log_t)
        (gamma2: gamma_t) (action_log2: log_t),
        interp_action_cps2 r1 sched_log1 a1
                           r2 sched_log2 a2
                           k gamma1 action_log1 gamma2 action_log2 =
        k (fst (interp_action2 r1 gamma1 sched_log1 action_log1 a1
                               r2 gamma2 sched_log2 action_log2 a2))
          (snd (interp_action2 r1 gamma1 sched_log1 action_log1 a1
                               r2 gamma2 sched_log2 action_log2 a2)).
    Proof.
      intros. unfold interp_action_cps2. unfold interp_action2.
      repeat rewrite interp_action_cps_correct. simpl.  reflexivity.
    Qed.

    Lemma interp_action_cps2'_correct:
      forall (r1: state_t) (sched_log1: log_t) (a1: action)
        (r2: state_t) (sched_log2: log_t) (a2: action)
        {A} (k: action_continuation2 string A)
        (gamma1: gamma_t) (action_log1: log_t)
        (gamma2: gamma_t) (action_log2: log_t),
        interp_action_cps2' r1 sched_log1 a1
                            r2 sched_log2 a2
                            k gamma1 action_log1 gamma2 action_log2 =
        k (fst (interp_action2 r1 gamma1 sched_log1 action_log1 a1
                               r2 gamma2 sched_log2 action_log2 a2))
          (snd (interp_action2 r1 gamma1 sched_log1 action_log1 a1
                               r2 gamma2 sched_log2 action_log2 a2)).
    Proof.
      intros. unfold interp_action_cps2'. unfold interp_action2.
      repeat rewrite interp_action_cps_correct. simpl.  reflexivity.
    Qed.

    Lemma interp_action_cps2_correct':
      forall (r1: state_t) (sched_log1: log_t) (a1: action)
        (r2: state_t) (sched_log2: log_t) (a2: action)
        {A} (k: action_continuation2 string A)
        (gamma1: gamma_t) (action_log1: log_t)
        (gamma2: gamma_t) (action_log2: log_t),
        interp_action_cps2 r1 sched_log1 a1
                           r2 sched_log2 a2
                           k gamma1 action_log1 gamma2 action_log2 =
        k (interp_action r1 gamma1 sched_log1 action_log1 a1)
          (interp_action r2 gamma2 sched_log2 action_log2 a2).
    Proof.
      intros. unfold interp_action_cps2. unfold interp_action2.
      repeat rewrite interp_action_cps_correct. simpl.  reflexivity.
    Qed.

    Lemma interp_action_cps2_correct_rev:
      forall (r1: state_t) (sched_log1: log_t) (a1: action)
        (r2: state_t) (sched_log2: log_t) (a2: action)
        (gamma1: gamma_t) (action_log1: log_t)
        (gamma2: gamma_t) (action_log2: log_t),
        interp_action2 r1 gamma1 sched_log1 action_log1 a1
                       r2 gamma2 sched_log2 action_log2 a2 =
        interp_action_cps2 r1 sched_log1 a1
                           r2 sched_log2 a2
                           pair gamma1 action_log1 gamma2 action_log2.
    Proof.
      intros. rewrite interp_action_cps2_correct. simpl. auto.
    Qed.

    Lemma wp_action2_commute :
      forall r1 L1 a1 r2 L2 a2 post gamma1 log1 gamma2 log2,
        wp_action2 r1 L1 a1 r2 L2 a2 post gamma1 log1 gamma2 log2 <->
        wp_action2' r1 L1 a1 r2 L2 a2 post gamma1 log1 gamma2 log2.
    Proof.
      intros. unfold wp_action2, wp_action2'.
      rewrite interp_action_cps2_correct, interp_action_cps2'_correct.
      reflexivity.
    Qed.

    Lemma interp_rule_cps2_correct:
      forall (r1: state_t) (L1: log_t) (a1: action)
        (r2: state_t) (L2: log_t) (a2: action)
        {A} (k: rule_continuation2 string A),
        interp_rule_cps2 r1 a1 r2 a2 k (Success L1) (Success L2) =
        k (fst (interp_rule2 r1 L1 a1 r2 L2 a2))
          (snd (interp_rule2 r1 L1 a1 r2 L2 a2)).
    Proof.
      intros. unfold interp_rule2.
      unfold interp_rule_cps2.
      rewrite interp_action_cps2_correct'.
      auto.
    Qed.

    Lemma interp_rule_cps2_correct':
      forall (r1: state_t) (L1: log_t) (a1: action)
        (r2: state_t) (L2: log_t) (a2: action)
        {A} (k: rule_continuation2 string A),
        interp_rule_cps2 r1 a1 r2 a2 k (Success L1) (Success L2) =
        k (interp_rule r1 L1 a1)
          (interp_rule r2 L2 a2).
    Proof.
      unfold interp_rule2, interp_rule_cps2; intros.
      rewrite interp_action_cps2_correct'.
      auto.
    Qed.

    Lemma interp_rule_cps2_correct_rev:
      forall (r1: state_t) (L1: log_t) (a1: action)
        (r2: state_t) (L2: log_t) (a2: action),
        interp_rule2 r1 L1 a1 r2 L2 a2 =
        interp_rule_cps2 r1 a1 r2 a2 pair (Success L1) (Success L2).
    Proof.
      intros; rewrite interp_rule_cps2_correct; reflexivity.
    Qed.

    (* Lemma interp_scheduler_cps2_correct: *)
    (*   forall (st1: state_t) {rule_name_t1: Type} (rules1: rule_name_t1 -> rule) *)
    (*     (s1: @scheduler rule_name_t1) *)
    (*     (st2: state_t) {rule_name_t2: Type} (rules2: rule_name_t2 -> rule) *)
    (*     (s2: @scheduler rule_name_t2) *)
    (*     {A} (k: scheduler_continuation2 string A), *)
    (*     interp_scheduler_cps2 st1 rules1 s1 st2 rules2 s2 k = *)
    (*     k (fst (interp_scheduler2 rules1 s1 st1 rules2 s2 st2)) *)
    (*       (snd (interp_scheduler2 rules1 s1 st1 rules2 s2 st2)). *)
    (* Proof. *)
    (*   intros. unfold interp_scheduler_cps2, interp_scheduler2. *)
    (*   repeat rewrite interp_scheduler_cps_correct. auto. *)
    (* Qed. *)

    (* Lemma interp_scheduler_cps2_correct': *)
    (*   forall (st1: state_t) {rule_name_t1: Type} (rules1: rule_name_t1 -> rule) *)
    (*     (s1: @scheduler rule_name_t1) *)
    (*     (st2: state_t) {rule_name_t2: Type} (rules2: rule_name_t2 -> rule) *)
    (*     (s2: @scheduler rule_name_t2) *)
    (*     {A} (k: scheduler_continuation2 string A), *)
    (*     interp_scheduler_cps2 st1 rules1 s1 st2 rules2 s2 k = *)
    (*     k (interp_scheduler st1 rules1 s1) *)
    (*       (interp_scheduler st2 rules2 s2). *)
    (* Proof. *)
    (*   intros. unfold interp_scheduler_cps2, interp_scheduler2. *)
    (*   repeat rewrite interp_scheduler_cps_correct. auto. *)
    (* Qed. *)

    (* Lemma interp_cycle_cps2_correct: *)
    (*   forall (st1: state_t) {rule_name_t1: Type} (rules1: rule_name_t1 -> rule) *)
    (*     (s1: @scheduler rule_name_t1) *)
    (*     (st2: state_t) {rule_name_t2: Type} (rules2: rule_name_t2 -> rule) *)
    (*     (s2: @scheduler rule_name_t2) *)
    (*     {A} (k: cycle_continuation2 string A), *)
    (*     interp_cycle_cps2 rules1 s1 st1 rules2 s2 st2 k = *)
    (*     k (fst (interp_cycle2 rules1 s1 st1 rules2 s2 st2)) *)
    (*       (snd (interp_cycle2 rules1 s1 st1 rules2 s2 st2)). *)
    (* Proof. *)
    (*   unfold interp_cycle2, interp_cycle_cps2; intros; repeat rewrite interp_scheduler_cps2_correct. *)
    (*   reflexivity. *)
    (* Qed. *)

    (* Lemma interp_cycle_cps2_correct': *)
    (*   forall (st1: state_t) {rule_name_t1: Type} (rules1: rule_name_t1 -> rule) *)
    (*     (s1: @scheduler rule_name_t1) *)
    (*     (st2: state_t) {rule_name_t2: Type} (rules2: rule_name_t2 -> rule) *)
    (*     (s2: @scheduler rule_name_t2) *)
    (*     {A} (k: cycle_continuation2 string A), *)
    (*     interp_cycle_cps2 rules1 s1 st1 rules2 s2 st2 k = *)
    (*     k (interp_cycle rules1 s1 st1) *)
    (*       (interp_cycle rules2 s2 st2). *)
    (* Proof. *)
    (*   unfold interp_cycle2, interp_cycle_cps2; intros; repeat rewrite interp_scheduler_cps2_correct. *)
    (*   reflexivity. *)
    (* Qed. *)


    (* Lemma interp_cycle_cps2_correct_rev: *)
    (*   forall (st1: state_t) {rule_name_t1: Type} (rules1: rule_name_t1 -> rule) *)
    (*     (s1: @scheduler rule_name_t1) *)
    (*     (st2: state_t) {rule_name_t2: Type} (rules2: rule_name_t2 -> rule) *)
    (*     (s2: @scheduler rule_name_t2), *)
    (*     interp_cycle2 rules1 s1 st1 rules2 s2 st2 = *)
    (*     interp_cycle_cps2 rules1 s1 st1 rules2 s2 st2 pair. *)
    (* Proof. *)
    (*   intros; rewrite interp_cycle_cps2_correct; reflexivity. *)
    (* Qed. *)

    Section WP.
      Lemma wp_action_correct:
        forall (r: state_t)
          (gamma: gamma_t)
          (sched_log: log_t)
          (action_log: log_t)
          (a: action )
          (post: action_postcondition),
          wp_action r sched_log a post gamma action_log <->
          post (interp_action r gamma sched_log action_log a).
      Proof.
        intros; unfold wp_action; rewrite interp_action_cps_correct; reflexivity.
      Qed.

      Lemma wp_rule_correct:
        forall (r: state_t) (L: log_t)
          (rl: rule)
          (post: rule_postcondition),
          wp_rule r rl post (Success L) <->
          post (interp_rule r L rl).
      Proof.
        intros; unfold wp_rule; rewrite interp_rule_cps_correct; reflexivity.
      Qed.

      Lemma wp_scheduler_correct:
        forall {rule_name_t: Type} (rules: rule_name_t -> rule)
          (r: state_t)
          (s: scheduler)
          (post: scheduler_postcondition),
          wp_scheduler r rules s post <->
          post (interp_scheduler r rules s).
      Proof.
        intros; unfold wp_scheduler; rewrite interp_scheduler_cps_correct; reflexivity.
      Qed.

      Lemma wp_cycle_correct:
        forall {rule_name_t: Type} (rules: rule_name_t -> rule)
          (r: state_t)
          (s: scheduler)
          (post: cycle_postcondition),
          wp_cycle r rules s r post <->
          post (interp_cycle rules s r).
      Proof.
        intros; unfold wp_cycle; rewrite interp_cycle_cps_correct; reflexivity.
      Qed.

      Lemma wp_action2_correct:
        forall (r1: state_t) (gamma1: gamma_t)
          (sched_log1: log_t) (action_log1: log_t)
          (a1: action )
          (r2: state_t) (gamma2: gamma_t)
          (sched_log2: log_t) (action_log2: log_t)
          (a2: action)
          (post: action_postcondition2),
          wp_action2 r1 sched_log1 a1 r2 sched_log2 a2
                     post gamma1 action_log1 gamma2 action_log2 <->
          post (fst (interp_action2 r1 gamma1 sched_log1 action_log1 a1
                                    r2 gamma2 sched_log2 action_log2 a2
                    ))
               (snd (interp_action2 r1 gamma1 sched_log1 action_log1 a1
                                    r2 gamma2 sched_log2 action_log2 a2
                    )).
      Proof.
        intros; unfold wp_action2; rewrite interp_action_cps2_correct; reflexivity.
      Qed.

      Lemma wp_action2_correct':
        forall (r1: state_t) (gamma1: gamma_t)
          (sched_log1: log_t) (action_log1: log_t)
          (a1: action )
          (r2: state_t) (gamma2: gamma_t)
          (sched_log2: log_t) (action_log2: log_t)
          (a2: action)
          (post: action_postcondition2),
          wp_action2 r1 sched_log1 a1 r2 sched_log2 a2
                     post gamma1 action_log1 gamma2 action_log2 <->
          post (interp_action r1 gamma1 sched_log1 action_log1 a1)
               (interp_action r2 gamma2 sched_log2 action_log2 a2).
      Proof.
        intros; unfold wp_action2; rewrite interp_action_cps2_correct; reflexivity.
      Qed.

      Lemma wp_rule2_correct:
        forall (r1: state_t) (sched_log1: log_t) (rl1: rule)
          (r2: state_t) (sched_log2: log_t) (rl2: rule)
          (post: rule_postcondition2),
          wp_rule2 r1 rl1 r2 rl2 post (Success sched_log1) (Success sched_log2)<->
          post (fst (interp_rule2 r1 sched_log1 rl1 r2 sched_log2 rl2))
               (snd (interp_rule2 r1 sched_log1 rl1 r2 sched_log2 rl2)).
      Proof.
        intros; unfold wp_rule2; rewrite interp_rule_cps2_correct; reflexivity.
      Qed.

      Lemma wp_rule2_correct':
        forall (r1: state_t) (sched_log1: log_t) (rl1: rule)
          (r2: state_t) (sched_log2: log_t) (rl2: rule)
          (post: rule_postcondition2),
          wp_rule2 r1 rl1 r2 rl2 post (Success sched_log1) (Success sched_log2)<->
          post (interp_rule r1 sched_log1 rl1)
               (interp_rule r2 sched_log2 rl2).
      Proof.
        intros; unfold wp_rule2; rewrite interp_rule_cps2_correct; reflexivity.
      Qed.

      (* Lemma wp_scheduler2_correct: *)
      (* forall (st1: state_t) {rule_name_t1: Type} (rules1: rule_name_t1 -> rule) *)
      (*   (s1: @scheduler rule_name_t1) *)
      (*   (st2: state_t) {rule_name_t2: Type} (rules2: rule_name_t2 -> rule) *)
      (*   (s2: @scheduler rule_name_t2) *)
      (*   (post: scheduler_postcondition2), *)
      (*   wp_scheduler2 st1 rules1 s1 st2 rules2 s2 post <-> *)
      (*   post (fst (interp_scheduler2 rules1 s1 st1 rules2 s2 st2)) *)
      (*        (snd (interp_scheduler2 rules1 s1 st1 rules2 s2 st2)). *)
      (* Proof. *)
      (*   intros; unfold wp_scheduler2; rewrite interp_scheduler_cps2_correct; reflexivity. *)
      (* Qed. *)

      (* Lemma wp_scheduler2_correct': *)
      (* forall (st1: state_t) {rule_name_t1: Type} (rules1: rule_name_t1 -> rule) *)
      (*   (s1: @scheduler rule_name_t1) *)
      (*   (st2: state_t) {rule_name_t2: Type} (rules2: rule_name_t2 -> rule) *)
      (*   (s2: @scheduler rule_name_t2) *)
      (*   (post: scheduler_postcondition2), *)
      (*   wp_scheduler2 st1 rules1 s1 st2 rules2 s2 post <-> *)
      (*   post (interp_scheduler st1 rules1 s1) *)
      (*        (interp_scheduler st2 rules2 s2). *)
      (* Proof. *)
      (*   intros; unfold wp_scheduler2; rewrite interp_scheduler_cps2_correct; reflexivity. *)
      (* Qed. *)

      (* Lemma wp_cycle2_correct: *)
      (* forall (st1: state_t) {rule_name_t1: Type} (rules1: rule_name_t1 -> rule) *)
      (*   (s1: @scheduler rule_name_t1) *)
      (*   (st2: state_t) {rule_name_t2: Type} (rules2: rule_name_t2 -> rule) *)
      (*   (s2: @scheduler rule_name_t2) *)
      (*   (post: cycle_postcondition2), *)
      (*     wp_cycle2 st1 rules1 s1 st2 rules2 s2 post <-> *)
      (*     post (fst (interp_cycle2 rules1 s1 st1 rules2 s2 st2)) *)
      (*          (snd (interp_cycle2 rules1 s1 st1 rules2 s2 st2)). *)
      (* Proof. *)
      (*   intros; unfold wp_cycle2; rewrite interp_cycle_cps2_correct; reflexivity. *)
      (* Qed. *)

      (* Lemma wp_cycle2_correct': *)
      (* forall (st1: state_t) {rule_name_t1: Type} (rules1: rule_name_t1 -> rule) *)
      (*   (s1: @scheduler rule_name_t1) *)
      (*   (st2: state_t) {rule_name_t2: Type} (rules2: rule_name_t2 -> rule) *)
      (*   (s2: @scheduler rule_name_t2) *)
      (*   (post: cycle_postcondition2), *)
      (*     wp_cycle2 st1 rules1 s1 st2 rules2 s2 post <-> *)
      (*     post (interp_cycle rules1 s1 st1) *)
      (*          (interp_cycle rules2 s2 st2). *)
      (* Proof. *)
      (*   intros; unfold wp_cycle2; rewrite interp_cycle_cps2_correct; reflexivity. *)
      (* Qed. *)

    End WP.

  End Proofs.

End Interp.
Notation "r '|>' s" :=
  (Cons r s)
    (at level 99, s at level 99, right associativity).
Notation "'done'" :=
  Done (at level 99).

Section Examples.
    Definition RegClk := "rclk".
    Definition RegR0 := "r0".
    Definition RegR1 := "r1".
    Definition RegRshared:= "rshared".
    Definition RegR0':= "r0'".
    Definition RegR1':= "r1'".

    Definition pipeline_reg_types : reg_types_t :=
      (fun r =>      if r =? RegClk then Some 1
             else if r =? RegR0 then Some 1
             else if r =? RegR1 then Some 1
             else if r =? RegRshared then Some 1
             else if r =? RegR0' then Some 1
             else if r =? RegR1' then Some 1
             else None).

    Notation type_check := (type_check pipeline_reg_types empty_var_t).


    Definition do_test :=
      {{ let "clk" := read0(RegClk) in
         if "clk" then
           let "v" := read0(RegR0) in
           if "clk" then
             if "clk" then
               if "clk" then
                 let "v" := read0(RegR0) in
                 write0(RegRshared, "v")
               else write0(RegRshared, Ob~1)
             else write0(RegRshared, Ob~1)
           else write0(RegRshared, Ob~1)
         else
           fail(0)
      }}.



    Definition do_rule0 :=
      {{ let "clk" := read0(RegClk) in
         if "clk" then
           let "v" := read0(RegR0) in
           write0(RegRshared, "v")
         else
           fail(0)
      }}.

    Definition do_rule1 :=
      {{ let "clk" := read0(RegClk) in
         if "clk" then
           fail(0)
         else
           let "v" := read0(RegR1) in
           write0(RegRshared, "v")
      }}.

    Definition do_shared :=
       {{ let "clk" := read0(RegClk) in
          let "v" := read1(RegRshared) in
          if "clk" then
            write0(RegR0', "v")
          else
            write0(RegR1', "v")
      }}.

    Definition do_clk :=
      {{ let "clk" := read0(RegClk) in
         if "clk" then
           write0(RegClk, Ob~0)
         else
           write0(RegClk, Ob~1)
      }}.

    Compute type_check do_test.
    Compute type_check do_rule0.
    Compute type_check do_rule1.
    Compute type_check do_shared.
    Compute type_check do_clk.

    Inductive rule_name_t :=
    | DoTest
    | DoRl0
    | DoRl1
    | DoShared
    | DoClk.

    Definition schedule : @scheduler rule_name_t :=
      DoRl0 |> DoRl1 |> DoShared |> DoClk |> Done.


    Definition rules : rule_name_t -> action :=
      fun rl => match rl with
             | DoTest => do_test
             | DoRl0 => do_rule0
             | DoRl1 => do_rule1
             | DoShared => do_shared
             | DoClk => do_clk
             end.

    Compute typecheck_schedule pipeline_reg_types schedule rules.


    Definition tau0 : Type := list bool.
    Definition tau1 : Type := list bool.
    Definition impl_tau : Type := tau0 * tau1.

    Definition impl_trace : Type := list impl_tau.


    Definition get_obs (st: state_t) : result impl_tau string :=
      match st RegR0', st RegR1' with
      | Some v0, Some v1 => Success (v0,v1)
      | _, _ => Failure (__debug__ (st RegR0', st RegR1') "Can't get obs: error state")
      end.

    Definition impl_step (st: state_t) : result (state_t * impl_tau) string :=
      step rules schedule get_obs st.

    Definition impl_step_n' (n: nat) (st: state_t) : result (state_t * impl_trace) string :=
      step_n' rules schedule get_obs n st.

    Definition impl_step_n (n: nat) (st: state_t) : result impl_trace string :=
      step_n rules schedule get_obs n st.

    Definition test_st : state_t :=
      fun reg => match reg with
              | "r0" => Some [true]
              | "r1" => Some [false]
              | "rshared" => Some [true]
              | "r0'" => Some [true]
              | "r1'" => Some [true]
              | "rclk" => Some [false]
              | _ => None
              end.

    Eval compute in impl_step_n 5 test_st.

    Section Spec.
      Context {clk_t: Type}.
      Context {local_st0: Type}.
      Context {local_st1: Type}.

      Context (init_clk: clk_t).
      Context (init_st0: bool).
      Context (init_st1: bool).

      Context (f0: local_st0 -> clk_t -> result (local_st0 * tau0) unit).
      Context (f1: local_st1 -> clk_t -> result (local_st1 * tau1) unit).
      Context (f__clk: clk_t -> result clk_t unit).

      Record spec_st_t : Type :=
        { state0 : local_st0;
          state1: local_st1;
          state__clk : clk_t;
        }.


      Definition spec_step (st: spec_st_t) : result (spec_st_t * (tau0 * tau1)) unit :=
        let/res2 st0', t0 := f0 st.(state0) st.(state__clk) in
        let/res2 st1', t1 := f1 st.(state1) st.(state__clk) in
        let/res clk' := f__clk st.(state__clk) in
        Success (({| state0 := st0';
                     state1 := st1';
                     state__clk := clk';
                  |}, (t0,t1))).

      Fixpoint spec_step_n' (n: nat) (st: spec_st_t) : result (spec_st_t * impl_trace) unit :=
        match n with
        | 0 => Success (st, [])
        | S n =>
          let/res2 st', t := spec_step st in
          let/res2 st'', tr := spec_step_n' n st' in
          Success (st'', t::tr)
        end.

      Definition spec_step_n (n: nat) (st: spec_st_t) : result impl_trace unit :=
        let/res2 _, tr := spec_step_n' n st in
        Success tr.

    End Spec.

    Definition valid_impl_state (st: state_t) :=
      WF_state pipeline_reg_types st.

    Definition valid_impl_log (log: log_t) :=
      WF_log pipeline_reg_types log.


    Record spec_local_st :=
      { local_st: option (list bool);
        local_st': option (list bool)
      }.

    Definition _spec_st_t := (@spec_st_t (option (list bool)) spec_local_st spec_local_st).

    Definition impl_st_to_spec_st (st: state_t) (pf: valid_impl_state st) : _spec_st_t :=
      {| state0 := {| local_st := st RegR0;
                      local_st' := st RegR0' |};
         state1 := {| local_st := st RegR1;
                      local_st' := st RegR1'
                   |};
         state__clk := st RegClk
      |}.


    Definition mk_st0 (st: spec_local_st) (clk: option (list bool)) : state_t :=
      (fun r =>      if r =? RegClk then clk
             else if r =? RegR0 then st.(local_st)
             else if r =? RegR1 then Some [false]
             else if r =? RegRshared then Some [false]
             else if r =? RegR0' then st.(local_st')
             else if r =? RegR1' then Some [false]
             else None).

    Definition mk_st1 (st: spec_local_st) (clk: option (list bool)) : state_t :=
      (fun r =>      if r =? RegClk then clk
             else if r =? RegR0 then Some [false]
             else if r =? RegR1 then st.(local_st)
             else if r =? RegRshared then Some [false]
             else if r =? RegR0' then Some [false]
             else if r =? RegR1' then st.(local_st')
             else None).

    Definition mk_st__clk (clk: option (list bool)) : state_t :=
      (fun r =>      if r =? RegClk then clk
             else if r =? RegR0 then Some [false]
             else if r =? RegR1 then Some [false]
             else if r =? RegRshared then Some [false]
             else if r =? RegR0' then Some [false]
             else if r =? RegR1' then Some [false]
             else None).


    Definition spec_f0 (st: spec_local_st) (clk: option (list bool)) : result (spec_local_st * tau0) unit :=
      match interp_cycle rules (DoRl0 |> DoShared |> Done) (mk_st0 st clk)  with
      | Success st' =>
          let spec_st' := {| local_st := st' "r0";
                             local_st' := st' "r0'"
                          |} in
        match st' "r0'" with
        | Some v => Success (spec_st', v)
        | None => Failure tt
        end
      | Failure _ => Failure tt
      end.

    Definition spec_f1 (st: spec_local_st) (clk: option (list bool)) : result (spec_local_st * tau0) unit :=
      match interp_cycle rules (DoRl1 |> DoShared |> Done) (mk_st1 st clk)  with
      | Success st' =>
          let spec_st' := {| local_st := st' RegR1;
                             local_st' := st' RegR1';
                          |} in
        match st' RegR1' with
        | Some v => Success (spec_st', v)
        | None => Failure tt
        end
      | Failure _ => Failure tt
      end.

    Definition spec_f__clk (clk: option (list bool)) : result (option (list bool)) unit :=
      match interp_cycle rules (DoClk |> Done) (mk_st__clk clk)  with
      | Success st' => Success (st' RegClk )
      | Failure _ => Failure tt
      end.

    Lemma typecheck_correct:
      is_success (typecheck_schedule pipeline_reg_types schedule rules) = true.
    Proof.
      auto.
    Qed.

    Lemma WF_get_obs__pipeline:
      WF_get_obs get_obs pipeline_reg_types.
    Proof.
      unfold WF_get_obs. intros. consider get_obs.
      consider WF_state. repeat destruct_match; auto.
      - pose proof H RegR1'. simpl in *. simpl_match. auto.
      - pose proof H RegR0'. simpl in *. simpl_match. auto.
    Qed.

    Lemma impl_step_n_success:
      forall (n: nat) (st: state_t),
        WF_state pipeline_reg_types st ->
        is_success (impl_step_n n st) = true.
    Proof.
      intros. unfold impl_step_n. eapply @step_n_success; eauto.
      apply WF_get_obs__pipeline.
    Qed.

    Definition _spec_step := spec_step spec_f0 spec_f1 spec_f__clk.
    Definition _spec_step_n := spec_step_n spec_f0 spec_f1 spec_f__clk.

    Record ImplInvariant (st: state_t): Prop :=
      { impl_wf: WF_state pipeline_reg_types st
      }.

    Definition WF_spec_local_st (st: spec_local_st) : Prop :=
      match st.(local_st), st.(local_st') with
      | Some v1, Some v2 => List.length v1 = 1 /\ List.length v2 = 1
      | _, _ => False
      end.

    Definition WF_spec_clk (clk: option (list bool)) : Prop :=
      match clk with
      | Some v => List.length v = 1
      | _ => False
      end.

    Record WF_spec_state (st: _spec_st_t) : Prop :=
      { WF_spec__clk : WF_spec_clk st.(state__clk);
        WF_spec0: WF_spec_local_st st.(state0);
        WF_spec1: WF_spec_local_st st.(state1);
      }.

    Record SpecInvariant (st: _spec_st_t) : Prop :=
      { spec_wf: WF_spec_state st }.

    Record Sim0 (impl_st: state_t) (spec_st: spec_local_st) : Prop :=
      { sim__r0: impl_st RegR0 = spec_st.(local_st);
        sim__r0': impl_st RegR0' = spec_st.(local_st');
      }.

    Record Sim1 (impl_st: state_t) (spec_st: spec_local_st) : Prop :=
      { sim__r1: impl_st RegR1 = spec_st.(local_st);
        sim__r1': impl_st RegR1' = spec_st.(local_st');
      }.

    Record Sim' (impl_st: state_t) (spec_st: _spec_st_t) : Prop :=
      { sim__clk: impl_st RegClk = spec_st.(state__clk);
        sim0: Sim0 impl_st spec_st.(state0);
        sim1: Sim1 impl_st spec_st.(state1);
      }.

    Record Sim (impl_st: state_t) (spec_st: _spec_st_t) : Prop :=
      { impl_invariant: ImplInvariant impl_st;
        spec_invariant: SpecInvariant spec_st;
        sim: Sim' impl_st spec_st
      }.

    Lemma InitialSim :
      forall (impl_st: state_t)
        (pf: valid_impl_state impl_st),
      Sim impl_st (impl_st_to_spec_st impl_st pf).
    Proof.
      constructor.
      - constructor.
        + auto.
      - constructor.
        + unfold impl_st_to_spec_st. consider valid_impl_state.
          unfold WF_state in *.
          constructor; simpl.
          * specialize pf with (reg := RegClk). auto.
          * consider WF_spec_local_st.
            pose proof pf RegR0. pose proof pf RegR0'. simpl in *.
            destruct_all_matches.
          * consider WF_spec_local_st.
            pose proof pf RegR1. pose proof pf RegR1'. simpl in *.
            destruct_all_matches.
      - constructor; auto.
        + constructor; auto.
        + constructor; auto.
    Qed.

    Lemma impl_invariant_preserved__step:
      forall (impl_st: state_t),
        ImplInvariant impl_st ->
        match impl_step impl_st with
        | Success (impl_st', impl_tau) =>
            ImplInvariant impl_st' /\
            get_obs impl_st' = Success impl_tau
        | _ => False
        end.
    Admitted.

    Lemma spec_invariant_preserved__step:
      forall (spec_st: _spec_st_t),
        SpecInvariant spec_st ->
        match _spec_step spec_st with
        | Success (spec_st', (t0,t1)) =>
            SpecInvariant spec_st' /\
            spec_st'.(state0).(local_st') = Some t0 /\
            spec_st'.(state1).(local_st') = Some t1
        | _ => False
        end.
    Proof.
      intros * Hinv. consider _spec_step.
      consider @spec_step. consider spec_f0.
    Admitted.

    Lemma interp_scheduler'_cons:
      forall {rule_name_t: Type}
      (st: state_t) (rules: rule_name_t -> action) rl s (input_log output_log: log_t),
      interp_scheduler' st rules (Cons rl s) input_log = Success output_log ->
      match interp_rule st input_log (rules rl) with
      | Success (Some rule_log) =>
        interp_scheduler' st rules s (log_app rule_log input_log) = Success output_log
      | Success None =>
        interp_scheduler' st rules s input_log = Success output_log
      | _ => False
      end.
    Proof.
      intros * Hsched.
      simpl in Hsched.
      bash_destruct Hsched; auto.
    Qed.
    Definition LE_read0_only (le: LogEntry) : Prop :=
      match le.(lread1), le.(lwrite0), le.(lwrite1) with
      | false, None, None => True
      | _, _, _ => False
      end.

    Definition log_read0_only (log: log_t) (reg: reg_t) : Prop :=
      match log reg with
      | Some le => LE_read0_only le
      | _ => False
      end.

    Record rule_spec_t :=
      { Pre: state_t -> log_t -> Prop;
        Post: state_t -> log_t -> log_t -> Prop;
      }.

    Record sim_spec_t :=
      { PreSim: state_t -> state_t -> log_t -> log_t -> Prop;
        PostSim: state_t -> state_t -> log_t -> log_t -> log_t -> log_t -> Prop;
      }.

    Definition rule_satisfies_spec (spec: rule_spec_t) (rl: action) : Prop :=
      forall st log,
      spec.(Pre) st log ->
      match interp_rule st log rl with
      | Success (Some rule_log) => spec.(Post) st log (log_app rule_log log)
      | Success None => spec.(Post) st log log
      | Failure _ => False
      end.

    Definition rules_satisfy_sim_spec (spec: sim_spec_t) (rl0 rl1: action) : Prop :=
      forall st0 st1 log0 log1,
      spec.(PreSim) st0 st1 log0 log1 ->
      match interp_rule st0 log0 rl0, interp_rule st1 log1 rl1 with
      | Success (Some rule_log0), Success (Some rule_log1) =>
          PostSim spec st0 st1 log0 log1 (log_app rule_log0 log0) (log_app rule_log1 log1)
      | Success (Some rule_log0), Success None =>
          PostSim spec st0 st1 log0 log1 (log_app rule_log0 log0) log1
      | Success None, Success (Some rule_log1) =>
          PostSim spec st0 st1 log0 log1 log0 (log_app rule_log1 log1)
      | Success None, Success None =>
          PostSim spec st0 st1 log0 log1 log0 log1
      | _, _ => False
      end.
    Definition st_eq_at_reg (st0 st1: state_t) (reg: reg_t) : Prop :=
      match st0 reg, st1 reg with
      | Some v1, Some v2 => v1 = v2
      | _, _ => False
      end.
    Definition LE_latest_write (le: LogEntry) : option (list bool) :=
      match lwrite1 le, lwrite0 le with
      | Some v, _ => Some v
      | _, Some v => Some v
      | _, _ => None
      end.
    Definition latest_write_eq_at_reg (log0 log1: log_t) (reg: reg_t) : Prop :=
      match log0 reg, log1 reg with
      | Some le0, Some le1 =>
          LE_latest_write le0 = LE_latest_write le1
      | _, _ => False
      end.

    Definition log_eq_at_reg (log0 log1: log_t) (reg: reg_t) : Prop :=
      match log0 reg, log1 reg with
      | Some le0, Some le1 =>
          le0 = le1
      | _, _ => False
      end.

    Definition log_effectively_eq_at_reg (log0 log1: log_t) (reg: reg_t) : Prop :=
      match log0 reg, log1 reg with
      | Some le0, Some le1 =>
        le0.(lread1) = le1.(lread1) /\
        le0.(lwrite0) = le1.(lwrite0) /\
        le0.(lwrite1) = le1.(lwrite1)
      | _, _ => False
      end.

    Record DoRl0__Pre (st: state_t) (log: log_t) : Prop :=
      { rl0_pre_valid_st: valid_impl_state st;
        rl0_pre_valid_log: WF_log pipeline_reg_types log;
        rl0_pre_log_empty: log = GenericLogEmpty;
      }.

    Record Taint0Untouched (input_log: log_t) (output_log: log_t) : Prop :=
      { taint0_untouched_r0: log_eq_at_reg input_log output_log RegR0;
        taint0_untouched_r0': log_eq_at_reg input_log output_log RegR0'
      }.

    Record Taint1Untouched (input_log: log_t) (output_log: log_t) : Prop :=
      { taint1_untouched_r1: log_eq_at_reg input_log output_log RegR1;
        taint1_untouched_r1': log_eq_at_reg input_log output_log RegR1'
      }.

    Record DoRl0__Post (st: state_t) (input_log: log_t) (log: log_t) : Prop :=
      { rl0_post_valid_log: WF_log pipeline_reg_types log;
        rl0_post_clk_read0_only: log_read0_only log RegClk;
        rl0_taint1_untouched: Taint1Untouched input_log log;
        rl0_clk_impl_shared_untouched:
          st RegClk = Some [false] -> log_eq_at_reg input_log log RegRshared
      }.

    Definition DoRl0__spec : rule_spec_t :=
      {| Pre := DoRl0__Pre;
         Post := DoRl0__Post
      |}.

    Record GenericStSim0 (st0 st1: state_t) : Prop :=
      { stsim0_eq_clk: st_eq_at_reg st0 st1 RegClk;
        stsim0_eq_r0: st_eq_at_reg st0 st1 RegR0;
        stsim0_eq_r0': st_eq_at_reg st0 st1 RegR0';
      }.
    Record GenericLogSim0 (log0 log1: log_t) : Prop :=
      { logsim0_eq_clk: log_effectively_eq_at_reg log0 log1 RegClk;
        logsim0_eq_r0: log_eq_at_reg log0 log1 RegR0;
        logsim0_eq_r0': log_eq_at_reg log0 log1 RegR0';
      }.

    Record GenericStSim1 (st0 st1: state_t) : Prop :=
      { stsim1_eq_clk: st_eq_at_reg st0 st1 RegClk;
        stsim1_eq_r1: st_eq_at_reg st0 st1 RegR1;
        stsim1_eq_r1': st_eq_at_reg st0 st1 RegR1';
      }.
    Record GenericLogSim1 (log0 log1: log_t) : Prop :=
      { logsim1_eq_clk: log_effectively_eq_at_reg log0 log1 RegClk;
        logsim1_eq_r1: log_eq_at_reg log0 log1 RegR1;
        logsim1_eq_r1': log_eq_at_reg log0 log1 RegR1';
      }.

    Record GenericSim0 (st0 st1: state_t) (log0 log1: log_t) : Prop :=
      { sim_st0: GenericStSim0 st0 st1;
        sim_log0: GenericLogSim0 log0 log1;
      }.

    Record GenericSim1 (st0 st1: state_t) (log0 log1: log_t) : Prop :=
      { sim_st1: GenericStSim1 st0 st1;
        sim_log1: GenericLogSim1 log0 log1;
      }.
Ltac simplify_pipeline_reg_types :=
  match goal with
  | |- context[pipeline_reg_types RegClk] =>
    replace (pipeline_reg_types RegClk) with (Some 1) by auto
  | |- context[pipeline_reg_types RegR0] =>
    replace (pipeline_reg_types RegR0) with (Some 1) by auto
  | |- context[pipeline_reg_types RegR1] =>
    replace (pipeline_reg_types RegR1) with (Some 1) by auto
  | |- context[pipeline_reg_types RegRshared] =>
    replace (pipeline_reg_types RegRshared) with (Some 1) by auto
  | |- context[pipeline_reg_types RegR0'] =>
    replace (pipeline_reg_types RegR0') with (Some 1) by auto
  | |- context[pipeline_reg_types RegR1'] =>
    replace (pipeline_reg_types RegR1') with (Some 1) by auto

  end.
Ltac simplify :=
  repeat match goal with
         | _ => progress simplify_result
         | H: (match ?v with
               | Some _ => _
               | None => False
               end) |- _ =>
           destruct_matches_in_hyp H; [ | contradiction]
         | H: if ?v then False else _ |- _ =>
           destruct_matches_in_hyp H; [ contradiction | ]
         | H: if ?v then _ else False |- _ =>
           destruct_matches_in_hyp H; [ | contradiction ]
         | H: None = Some _ |- _ =>
           clear - H; discriminate
         | H: Some _ = None |- _ =>
           clear - H; discriminate
         | H: Some _ = Some _ |- _ =>
           inversions H
         | H: is_some (Some ?a) -> _ |- _ =>
           specialize H with (1 := is_some_Some _)
         | H1: is_some ?v -> _,
               H2: ?v = Some _ |- _ =>
           rewrite H2 in H1
         | H: is_some None |- _ =>
           exfalso; apply is_some_None_False in H; auto
         | H : String.eqb _ _ = true|- _ =>
           apply String.eqb_eq in H; subst
         | H : String.eqb _ _ = false|- _ =>
           apply String.eqb_neq in H; subst
         | H : Nat.eqb _ _ = true |- _ =>
           apply PeanoNat.Nat.eqb_eq in H; subst
         | _ => progress propositional
         (* | _ => progress simpl_match *)
         end.

    Record DoRl0__SimPre (st0 st1: state_t) (log0 log1: log_t) : Prop :=
      { rl0_sim_pre0: DoRl0__Pre st0 log0;
        rl0_sim_pre1: DoRl0__Pre st1 log1;
        rl0_sim_pre_sim: GenericSim0 st0 st1 log0 log1
      }.

    Record DoRl0__SimPost' (st0 st1: state_t) (log0 log1: log_t) (log0' log1': log_t) : Prop :=
      { rl0_sim_post_sim: GenericLogSim0 log0' log1'
      }.

    Record DoRl0__SimPost (st0 st1: state_t) (log0 log1: log_t) (log0' log1': log_t) : Prop :=
      { rl0_sim_post0: DoRl0__Post st0 log0 log0';
        rl0_sim_post1: DoRl0__Post st1 log1 log1';
        rl0_sim_post : DoRl0__SimPost' st0 st1 log0 log1 log0' log1'
      }.

    Definition DoRl0__SimSpec : sim_spec_t :=
      {| PreSim := DoRl0__SimPre;
         PostSim := DoRl0__SimPost
      |}.

    Lemma wp_fail:
      forall st sched_log ty_hint (post: action_postcondition) (gamma: gamma_t) (action_log: log_t),
       post (Success None) ->
       wp_action st sched_log (Fail ty_hint) post gamma action_log.
    Proof.
      auto.
    Qed.
    Lemma wp_var:
      forall st sched_log (var: var_t) (post: action_postcondition)
        (gamma: gamma_t) (action_log: log_t),
      post (let/res var_value := gamma_lookup_var gamma var (__debug__ (gamma,var) "Var not found") in
            (Success (Some (gamma, action_log , var_value)))) ->
      wp_action st sched_log (Var var) post gamma action_log.
   Proof.
     auto.
   Qed.

    Lemma wp_const:
      forall st sched_log (cst: list bool) (post: action_postcondition)
        (gamma: gamma_t) (action_log: log_t),
      post (Success (Some (gamma, action_log, cst))) ->
      wp_action st sched_log (Const cst) post gamma action_log.
    Proof.
      auto.
    Qed.

    Lemma wp_assign:
      forall st sched_log (var: var_t) (ex: action) (post: action_postcondition)
        (gamma: gamma_t) (action_log: log_t),
      wp_action st sched_log ex (fun res =>
                                   post (let/res opt := res in
                                         match opt with
                                         | Some (gamma, log, v) => (Success (Some (gamma_set gamma var v, log, [])))
                                         | None => (Success None)
                                         end)) gamma action_log ->
      wp_action st sched_log (Assign var ex) post gamma action_log.
    Proof.
      auto.
    Qed.

    Lemma wp_seq:
      forall st sched_log (a1 a2: action) (post: action_postcondition)
        (gamma: gamma_t) (action_log: log_t),
      wp_action st sched_log a1 (fun res =>
                                   match res with
                                   | Success (Some (gamma, log, _)) =>
                                     wp_action st sched_log a2 post gamma log
                                   | _ => post res
                                   end) gamma action_log ->
      wp_action st sched_log (Seq a1 a2) post gamma action_log.
    Proof.
      auto.
    Qed.


    Lemma wp_if:
      forall st sched_log (cond tbranch fbranch: action) (post: action_postcondition)
        (gamma: gamma_t) (action_log: log_t),
      wp_action st sched_log cond (fun res => match res with
                                   | Success (Some (gamma, log,v)) =>
                                     match v with
                                     | [true] => wp_action st sched_log tbranch post gamma log
                                     | [false] => wp_action st sched_log fbranch post gamma log
                                     | _ => post (Failure (__debug__ v "If: cond not single bit"))
                                     end
                                   | _ => post res
                                   end) gamma action_log ->
      wp_action st sched_log (If cond tbranch fbranch) post gamma action_log.
   Proof.
     auto.
   Qed.

    Lemma wp_bind:
      forall st sched_log (var: var_t) (ex: action) (body: action) (post: action_postcondition)
        (gamma: gamma_t) (action_log: log_t),
      wp_action st sched_log ex (fun res => match res with
                                   | Success (Some (gamma, log,v)) =>
                                     wp_action st sched_log body
                                               (fun res =>
                                                     post (let/res opt := res in
                                                        match opt with
                                                        | Some (gamma', log, v) =>
                                                          Success (Some (gamma, log, v))
                                                        | None => Success None
                                                        end)) (gamma_set gamma var v) log
                                   | _ => post res
                                   end) gamma action_log ->
      wp_action st sched_log (Bind var ex body) post gamma action_log.
   Proof.
     auto.
   Qed.
    Lemma wp_read0:
      forall st sched_log (idx: reg_t) (post: action_postcondition)
        (gamma: gamma_t) (action_log: log_t),
      post (let/res sched_le := log_get sched_log idx in
             let/res action_le := log_get action_log idx in
             if LE_may_read0 sched_le then
               let/res v := r_get_reg st idx in
               let le' := {|lread0 := true; lread1 := action_le.(lread1);
                                       lwrite0 := action_le.(lwrite0); lwrite1 := action_le.(lwrite1) |} in
               Success (Some (gamma, log_set action_log idx le', v))
             else Success None) ->
      wp_action st sched_log (Read P0 idx) post gamma action_log.
   Proof.
     auto.
   Qed.

    Lemma wp_read1:
      forall st sched_log (idx: reg_t) (post: action_postcondition)
        (gamma: gamma_t) (action_log: log_t),
      post (let/res sched_le := log_get sched_log idx in
             let/res action_le := log_get action_log idx in
             if LE_may_read1 sched_le then
                  let le' := {| lread0 := action_le.(lread0); lread1 := true;
                                lwrite0 := action_le.(lwrite0); lwrite1 := action_le.(lwrite1) |} in
                  let/res v :=
                     match action_le.(lwrite0), sched_le.(lwrite0) with
                     | Some v, _ => Success v
                     | _, Some v => Success v
                     | _, _ => r_get_reg st idx
                     end in
               Success (Some (gamma, log_set action_log idx le', v))
             else Success None) ->
      wp_action st sched_log (Read P1 idx) post gamma action_log.
   Proof.
     auto.
   Qed.

   Lemma wp_write0:
     forall st sched_log (idx: reg_t) (value: action) (post: action_postcondition)
       (gamma: gamma_t) (action_log: log_t),
     wp_action st sched_log value (fun res =>
                                     match res with
                                     | Success (Some (gamma, l, v)) =>
                                       post (let/res sched_le := log_get sched_log idx in
                                             let/res action_le := log_get l idx in
                                             if LE_may_write0 sched_le && LE_may_write0 action_le then
                                               let le' := {| lread0 := action_le.(lread0);
                                                             lread1 := action_le.(lread1);
                                                             lwrite0 := Some v;
                                                             lwrite1 := action_le.(lwrite1) |} in
                                               Success (Some (gamma, log_set l idx le', []))
                                             else Success None)
                                     | _ => post res
                                     end) gamma action_log ->
     wp_action st sched_log (Write P0 idx value) post gamma action_log.
   Proof.
     auto.
   Qed.

    Lemma wp_write1:
      forall st sched_log (idx: reg_t) (value: action) (post: action_postcondition)
        (gamma: gamma_t) (action_log: log_t),
      wp_action st sched_log value (fun res =>
                                      match res with
                                      | Success (Some (gamma, l, v)) =>
                                        post (let/res sched_le := log_get sched_log idx in
                                              let/res action_le := log_get l idx in
                                              if LE_may_write1 sched_le && LE_may_write1 action_le then
                                                let le' := {| lread0 := action_le.(lread0);
                                                              lread1 := action_le.(lread1);
                                                              lwrite0 := action_le.(lwrite0);
                                                              lwrite1 := Some v |} in
                                                Success (Some (gamma, log_set l idx le', []))
                                              else Success None)
                                      | _ => post res
                                      end) gamma action_log ->
      wp_action st sched_log (Write P1 idx value) post gamma action_log.
   Proof.
     auto.
   Qed.

   Lemma wp_action_post_equiv:
     forall st sched_log action post1 post2 gamma action_log,
       (forall res, post1 res <-> post2 res) ->
       wp_action st sched_log action post1 gamma action_log <->
       wp_action st sched_log action post2 gamma action_log.
   Proof.
     induction action0; intros* Hpost; cbn; try reflexivity; auto.
     - apply IHaction0. auto.
     - apply IHaction0_1; auto.
       intros; repeat destruct_match; auto.
       apply IHaction0_2. auto.
     - apply IHaction0_1; auto.
       intros; repeat destruct_match; auto.
       + apply IHaction0_2; auto.
       + apply IHaction0_3; auto.
     - apply IHaction0_1; auto.
       intros; repeat destruct_match; auto.
       + apply IHaction0_2; auto.
     - destruct_match; auto.
     - destruct_match; auto.
       + apply IHaction0; auto.
         intros; repeat destruct_match; auto.
       + apply IHaction0; auto.
         intros; repeat destruct_match; auto.
   Qed.

   Lemma wp_action2_post_equiv:
     forall st0 sched_log0 action0
       st1 sched_log1 action1 post1 post2 gamma0 action_log0 gamma1 action_log1,
       (forall res0 res1, post1 res0 res1 <-> post2 res0 res1) ->
       wp_action2 st0 sched_log0 action0
                  st1 sched_log1 action1 post1 gamma0 action_log0 gamma1 action_log1 <->
       wp_action2 st0 sched_log0 action0
                  st1 sched_log1 action1 post2 gamma0 action_log0 gamma1 action_log1.
   Proof.
     intros.
     consider wp_action2. unfold interp_action_cps2.
     apply wp_action_post_equiv.
     intros.
     apply wp_action_post_equiv.
     auto.
   Qed.

   Lemma wp2_fail0:
      forall st0 sched_log0 (ty_hint: nat)
        st1 sched_log1 (a1: action)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
     wp_action st1 sched_log1 a1 (post (Success None)) gamma1 action_log1 ->
     wp_action2 st0 sched_log0 (Fail ty_hint)
                st1 sched_log1 a1
                post gamma0 action_log0 gamma1 action_log1.
   Proof.
     intros *. rewrite wp_action2_commute. auto.
   Qed.

   Lemma wp2_fail1:
      forall st0 sched_log0 (a0: action)
        st1 sched_log1 (ty_hint: nat)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
     wp_action st0 sched_log0 a0 (fun res0 => post res0 (Success None)) gamma0 action_log0 ->
     wp_action2 st0 sched_log0 a0
                st1 sched_log1 (Fail ty_hint)
                post gamma0 action_log0 gamma1 action_log1.
   Proof.
     auto.
   Qed.

   Lemma wp2_var0:
      forall st0 sched_log0 (var: var_t)
        st1 sched_log1 (a1: action)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
     wp_action st1 sched_log1 a1
               (post
                  (let/res var_value := gamma_lookup_var gamma0 var (__debug__ (gamma0,var) "Var not found") in
                   (Success (Some (gamma0, action_log0 , var_value)))))
               gamma1 action_log1 ->
     wp_action2 st0 sched_log0 (Var var)
                st1 sched_log1 a1
                post gamma0 action_log0 gamma1 action_log1.
   Proof.
     auto.
   Qed.

   Lemma wp2_var1:
      forall st0 sched_log0 (a0: action)
        st1 sched_log1 (var: var_t)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
        wp_action st0 sched_log0 a0
                  (fun res0 => post res0
                     (let/res var_value := gamma_lookup_var gamma1 var (__debug__ (gamma1,var) "Var not found") in
                      (Success (Some (gamma1, action_log1 , var_value)))))
                  gamma0 action_log0 ->
        wp_action2 st0 sched_log0 a0
                st1 sched_log1 (Var var)
                post gamma0 action_log0 gamma1 action_log1.
   Proof.
     intros *. auto.
   Qed.

   Lemma wp2_const0:
      forall st0 sched_log0 (cst: list bool)
        st1 sched_log1 (a1: action)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
     wp_action st1 sched_log1 a1 (post (Success (Some (gamma0, action_log0, cst))))
                   gamma1 action_log1 ->
     wp_action2 st0 sched_log0 (Const cst)
                st1 sched_log1 a1
                post gamma0 action_log0 gamma1 action_log1.
   Proof.
     auto.
   Qed.

   Lemma wp2_const1:
      forall st0 sched_log0 (a0: action)
        st1 sched_log1 (cst: list bool)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
     wp_action st0 sched_log0 a0 (fun res0 => post res0 (Success (Some (gamma1, action_log1, cst))))
                   gamma0 action_log0 ->
     wp_action2 st0 sched_log0 a0
                st1 sched_log1 (Const cst)
                post gamma0 action_log0 gamma1 action_log1.
   Proof.
     auto.
   Qed.

    Lemma wp2_bind0:
      forall st0 sched_log0 (var: var_t) (ex: action) (body: action)
        st1 sched_log1 (a1: action)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
      wp_action2 st0 sched_log0 ex
                 st1 sched_log1 a1 (fun res0 res1 =>
                                     match res0 with
                                     | Success (Some (gamma, log, v)) =>
                                       wp_action st0 sched_log0 body
                                                 (fun res => post (restore_gamma res gamma) res1)
                                                 (gamma_set gamma var v) log
                                     | _ => post res0 res1
                                     end)
                 gamma0 action_log0 gamma1 action_log1 ->
      wp_action2 st0 sched_log0 (Bind var ex body)
                 st1 sched_log1 a1 post gamma0 action_log0 gamma1 action_log1.
   Proof.
     auto.
   Qed.

    Lemma wp2_bind1:
      forall st0 sched_log0 (a0: action)
        st1 sched_log1 (var: var_t) (ex: action) (body: action)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
      wp_action2 st0 sched_log0 a0
                 st1 sched_log1 ex (fun res0 res1 =>
                                     match res1 with
                                     | Success (Some (gamma, log, v)) =>
                                       wp_action st1 sched_log1 body
                                                 (fun res => post res0 (restore_gamma res gamma))
                                                 (gamma_set gamma var v) log
                                     | _ => post res0 res1
                                     end)
                 gamma0 action_log0 gamma1 action_log1 ->
      wp_action2 st0 sched_log0 a0
                 st1 sched_log1 (Bind var ex body)
                 post gamma0 action_log0 gamma1 action_log1.
   Proof.
     intros. rewrite wp_action2_commute.
     rewrite wp_action2_commute in H. auto.
   Qed.

   (*  Lemma wp2_bind: *)
   (*    forall st0 sched_log0 *)
   (*      st1 sched_log1 *)
   (*      (var: var_t) (ex: action) (body: action) *)
   (*      (post: action_postcondition2) *)
   (*      (gamma0: gamma_t) (action_log0: log_t) *)
   (*      (gamma1: gamma_t) (action_log1: log_t), *)
   (*    wp_action2 st0 sched_log0 ex *)
   (*               st1 sched_log1 ex (fun res0 res1 => *)
   (*                 match res0, res1 with *)
   (*                 | Success (Some (gamma0, log0, v0)), *)
   (*                   Success (Some (gamma1, log1, v1)) => *)
   (*                   wp_action2 st0 sched_log0 body *)
   (*                              st1 sched_log1 body *)
   (*                              (fun res0' res1' => *)
   (*                                 post (restore_gamma res0' gamma0) *)
   (*                                      (restore_gamma res1' gamma1)) *)
   (*                              (gamma_set gamma0 var v0) log0 *)
   (*                              (gamma_set gamma1 var v1) log1 *)
   (*                 | Success (Some (gamma0, log0, v0)), _ => *)
   (*                   wp_action st0 sched_log0 body *)
   (*                             (fun res0' => post (restore_gamma res0' gamma0) res1) *)
   (*                             (gamma_set gamma0 var v0) log0 *)
   (*                 | _, Success (Some (gamma1, log1, v1)) => *)
   (*                   wp_action st1 sched_log1 body *)
   (*                             (fun res1' => post res0 (restore_gamma res1' gamma1)) *)
   (*                             (gamma_set gamma1 var v1) log1 *)
   (*                 | _, _ => post res0 res1 *)
   (*                 end) *)
   (*               gamma0 action_log0 gamma1 action_log1 -> *)
   (*    wp_action2 st0 sched_log0 (Bind var ex body) *)
   (*               st1 sched_log1 (Bind var ex body) post gamma0 action_log0 gamma1 action_log1. *)
   (* Proof. *)
   (* Admitted. *)


    Lemma wp2_read00:
      forall st0 sched_log0 (idx: reg_t)
        st1 sched_log1 (a1: action)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
      wp_action st1 sched_log1 a1
                (post (let/res sched_le := log_get sched_log0 idx in
                      let/res action_le := log_get action_log0 idx in
                      if LE_may_read0 sched_le then
                        let/res v := r_get_reg st0 idx in
                        let le' := {|lread0 := true; lread1 := action_le.(lread1);
                                     lwrite0 := action_le.(lwrite0); lwrite1 := action_le.(lwrite1) |} in
                        Success (Some (gamma0, log_set action_log0 idx le', v))
                      else Success None))
                gamma1 action_log1 ->
      wp_action2 st0 sched_log0 (Read P0 idx)
                 st1 sched_log1 a1 post gamma0 action_log0 gamma1 action_log1.
   Proof.
     auto.
   Qed.

   Lemma wp2_read01:
     forall st0 sched_log0 (a0: action)
       st1 sched_log1 (idx: reg_t)
       (post: action_postcondition2)
       (gamma0: gamma_t) (action_log0: log_t)
       (gamma1: gamma_t) (action_log1: log_t),
     wp_action st0 sched_log0 a0
               (fun res0 =>
                  post res0
                       (let/res sched_le := log_get sched_log1 idx in
                        let/res action_le := log_get action_log1 idx in
                        if LE_may_read0 sched_le then
                          let/res v := r_get_reg st1 idx in
                          let le' := {|lread0 := true; lread1 := action_le.(lread1);
                                       lwrite0 := action_le.(lwrite0);
                                       lwrite1 := action_le.(lwrite1) |} in
                          Success (Some (gamma1, log_set action_log1 idx le', v))
                        else Success None))
               gamma0 action_log0 ->
     wp_action2 st0 sched_log0 a0
                st1 sched_log1 (Read P0 idx) post gamma0 action_log0 gamma1 action_log1.
    Proof.
      auto.
    Qed.

    Lemma wp2_write00:
      forall st0 sched_log0 (idx: reg_t) (value: action)
        st1 sched_log1 (a1: action)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
    wp_action2 st0 sched_log0 value
               st1 sched_log1 a1
               (fun res0 res1 =>
                  match res0 with
                  | Success (Some (gamma, l, v)) =>
                    post
                      (let/res sched_le := log_get sched_log0 idx in
                       let/res action_le := log_get l idx in
                       if LE_may_write0 sched_le && LE_may_write0 action_le then
                         let le' := {| lread0 := action_le.(lread0);
                                       lread1 := action_le.(lread1);
                                       lwrite0 := Some v;
                                       lwrite1 := action_le.(lwrite1) |} in
                         Success (Some (gamma, log_set l idx le', []))
                       else Success None) res1
                  | _ => post res0 res1
                  end)
               gamma0 action_log0 gamma1 action_log1 ->
     wp_action2 st0 sched_log0 (Write P0 idx value)
                st1 sched_log1 a1 post gamma0 action_log0 gamma1 action_log1.
    Proof.
      auto.
    Qed.

    Lemma wp2_write01:
      forall st0 sched_log0 (a0: action)
        st1 sched_log1 (idx: reg_t) (value: action)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
    wp_action2 st0 sched_log0 a0
               st1 sched_log1 value
               (fun res0 res1 =>
                  match res1 with
                  | Success (Some (gamma, l, v)) =>
                    post res0
                      (let/res sched_le := log_get sched_log1 idx in
                       let/res action_le := log_get l idx in
                       if LE_may_write0 sched_le && LE_may_write0 action_le then
                         let le' := {| lread0 := action_le.(lread0);
                                       lread1 := action_le.(lread1);
                                       lwrite0 := Some v;
                                       lwrite1 := action_le.(lwrite1) |} in
                         Success (Some (gamma, log_set l idx le', []))
                       else Success None)
                  | _ => post res0 res1
                  end)
               gamma0 action_log0 gamma1 action_log1 ->
     wp_action2 st0 sched_log0 a0
                st1 sched_log1 (Write P0 idx value)
                post gamma0 action_log0 gamma1 action_log1.
    Proof.
      intros. rewrite wp_action2_commute in *.
      auto.
    Qed.

    Lemma wp2_if0:
      forall st0 sched_log0 (cond tbranch fbranch: action)
        st1 sched_log1 (a1: action)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
    wp_action2 st0 sched_log0 cond
               st1 sched_log1 a1 (fun res0 res1 =>
                   match res0 with
                   | Success (Some (gamma, log, v)) =>
                     match v with
                     | [true] => wp_action st0 sched_log0 tbranch (fun res0' => post res0' res1) gamma log
                     | [false] => wp_action st0 sched_log0 fbranch (fun res0' => post res0' res1) gamma log
                     | _ => post (Failure (__debug__ v "If: cond not single bit")) res1
                     end
                   | _ => post res0 res1
                   end) gamma0 action_log0 gamma1 action_log1 ->
     wp_action2 st0 sched_log0 (If cond tbranch fbranch)
                st1 sched_log1 a1 post gamma0 action_log0 gamma1 action_log1.
    Proof.
      auto.
    Qed.

    Lemma wp2_if1:
      forall st0 sched_log0 (a0: action)
        st1 sched_log1 (cond tbranch fbranch: action)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
     wp_action2 st0 sched_log0 a0
               st1 sched_log1 cond (fun res0 res1 =>
                   match res1 with
                   | Success (Some (gamma, log, v)) =>
                     match v with
                     | [true] => wp_action st1 sched_log1 tbranch (post res0) gamma log
                     | [false] => wp_action st1 sched_log1 fbranch (post res0) gamma log
                     | _ => post res0 (Failure (__debug__ v "If: cond not single bit"))
                     end
                   | _ => post res0 res1
                   end) gamma0 action_log0 gamma1 action_log1 ->
     wp_action2 st0 sched_log0 a0
                st1 sched_log1 (If cond tbranch fbranch) post gamma0 action_log0 gamma1 action_log1.
   Proof.
     intros. rewrite wp_action2_commute in *. auto.
   Qed.

    Lemma wp2_if:
      forall st0 sched_log0 (cond0 tbranch0 fbranch0: action)
        st1 sched_log1 (cond1 tbranch1 fbranch1: action)
        (post: action_postcondition2)
        (gamma0: gamma_t) (action_log0: log_t)
        (gamma1: gamma_t) (action_log1: log_t),
    wp_action2 st0 sched_log0 cond0
               st1 sched_log1 cond1 (fun res0 res1 =>
                   match res0, res1 with
                   | Success (Some (gamma0', log0', [v0])), Success (Some (gamma1', log1', [v1])) =>
                     let a0 := match v0 with
                               | true => tbranch0
                               | false => fbranch0
                               end in
                     let a1 := match v1 with
                               | true => tbranch1
                               | false => fbranch1
                               end in
                     wp_action2 st0 sched_log0 a0
                                st1 sched_log1 a1
                                post gamma0' log0' gamma1' log1'
                   | Success (Some (gamma0', log0', [v0])), _ =>
                     let res1' := match res1 with
                                  | Success (Some (_, _, _)) => Failure "If: cond not single bit"
                                  | _ => res1
                                  end in
                     match v0 with
                     | true => wp_action st0 sched_log0 tbranch0 (fun res0' => post res0' res1') gamma0' log0'
                     | false => wp_action st0 sched_log0 fbranch0 (fun res0' => post res0' res1') gamma0' log0'
                     end
                   | _, Success (Some (gamma1', log1', [v1])) =>
                     let res0' := match res0 with
                                  | Success (Some (_, _, _)) => Failure "If: cond not single bit"
                                  | _ => res0
                                  end in
                     match v1 with
                     | true => wp_action st1 sched_log1 tbranch1 (post res0') gamma1' log1'
                     | false => wp_action st1 sched_log1 fbranch1 (post res0') gamma1' log1'
                     end
                  | _, _ =>
                     let res0' := match res0 with
                                  | Success (Some (_, _, _)) => Failure "If: cond not single bit"
                                  | _ => res0
                                  end in
                     let res1' := match res1 with
                                 | Success (Some (_, _, _)) => Failure "If: cond not single bit"
                                 | _ => res1
                                 end in
                     post res0' res1'
                  end) gamma0 action_log0 gamma1 action_log1 ->
     wp_action2 st0 sched_log0 (If cond0 tbranch0 fbranch0)
                st1 sched_log1 (If cond1 tbranch1 fbranch1)
                post gamma0 action_log0 gamma1 action_log1.
    Proof.
      intros. apply wp2_if0. apply wp2_if1.
      revert H.
      apply wp_action2_post_equiv.
      intros.
      destruct res1 as [ [ [ [ ? ?] ? ] | ] | ];
        destruct res0 as [ [ [ [ ? ?] ? ] | ] | ]; simpl; try reflexivity.
      all: destruct_match; try reflexivity.
      all: destruct_match; try reflexivity.
      all: destruct_match; try reflexivity.
      all: destruct_match; try reflexivity.
      all: destruct_match; try reflexivity.
      all: destruct_match; try reflexivity.
    Qed.

 Ltac set_match_as v :=
   match goal with
   | |- match ?d with | _ => _ end =>
     set d as v in *
   end.
      Lemma r_get_reg_subst:
        forall st reg v,
        st reg = Some v ->
        r_get_reg st reg = Success (v).
      Proof.
        intros. unfold r_get_reg. simpl_match. auto.
      Qed.
Lemma log_get_empty:
  forall r,
  log_get GenericLogEmpty r = Success (LE_empty).
Proof.
  auto.
Qed.
Lemma LE_may_read0_empty_true:
  LE_may_read0 LE_empty = true.
Proof.
  auto.
Qed.
Lemma LE_may_read1_empty_true:
  LE_may_read1 LE_empty = true.
Proof.
  auto.
Qed.

Lemma LE_may_write0_empty_true:
  LE_may_write0 LE_empty = true.
Proof.
  auto.
Qed.
Lemma LE_may_write1_empty_true:
  LE_may_write1 LE_empty = true.
Proof.
  auto.
Qed.

Ltac rewrite_r_get_reg st reg :=
  match goal with
  | H: st reg = Some _ |- _ =>
    rewrite r_get_reg_subst with (1 := H)
  end.
Declare Scope wp_notations.
Notation "'wp_action' st log action '[...]'" := (wp_action st log action _)
                                             (at level 200, only printing) : wp_notations.

Open Scope wp_notations.

Lemma gamma_set_lookup:
  forall A gamma var v (dbg: A),
  gamma_lookup_var (gamma_set gamma var v) var dbg = Success v.
Proof.
  intros. consider @gamma_lookup_var.
  unfold gamma_set. rewrite String.eqb_refl. reflexivity.
Qed.
Lemma case_singleton_bool_list:
  forall l,
  Datatypes.length l = 1 ->
  l = [true] \/ l = [false].
Proof.
  intros. destruct l; try discriminate.
  destruct l; try discriminate.
  destruct b; auto.
Qed.
Ltac case_singleton l:=
  match goal with
  | H: Datatypes.length l = 1 |- _ =>
    destruct (case_singleton_bool_list _ H); subst l
  end.
      Lemma log_read0_only_empty:
        forall reg, log_read0_only GenericLogEmpty reg.
      Proof.
        intros. consider log_read0_only.
        simpl. consider LE_read0_only. consider LE_empty. simpl. auto.
      Qed.
Lemma log_eq_at_reg_sym:
  forall log1 log2 reg,
  log_eq_at_reg log1 log2 reg ->
  log_eq_at_reg log2 log1 reg.
Proof.
  intros. consider log_eq_at_reg.
  destruct_all_matches; auto.
Qed.

Lemma log_effectively_eq_at_reg_sym:
  forall log1 log2 reg,
  log_effectively_eq_at_reg log1 log2 reg ->
  log_effectively_eq_at_reg log2 log1 reg.
Proof.
  intros. consider log_effectively_eq_at_reg.
  destruct_all_matches; auto; propositional.
Qed.

Lemma log_read0_only_impl_effectively_empty:
  forall log reg,
    log_read0_only log reg ->
    log_effectively_eq_at_reg log GenericLogEmpty reg.
Proof.
  intros. consider log_read0_only. consider log_effectively_eq_at_reg.
  consider LE_read0_only. unfold GenericLogEmpty. destruct_all_matches; auto.
Qed.
  Lemma Taint1Untouched_empty:
    Taint1Untouched GenericLogEmpty GenericLogEmpty .
  Proof.
    constructor; unfold log_eq_at_reg; simpl; auto.
  Qed.
Ltac simplify_pipeline_logs :=
  match goal with
  | |- Taint1Untouched GenericLogEmpty GenericLogEmpty =>
    apply Taint1Untouched_empty
  end.
  Lemma log_eq_at_reg_empty:
    forall reg,
    log_eq_at_reg GenericLogEmpty GenericLogEmpty reg.
  Proof.
    intros. consider log_eq_at_reg. simpl. auto.
  Qed.
Lemma log_set_get_eq:
  forall log le r,
  log_get (log_set log r le) r = Success le.
Proof.
  intros. unfold log_set. unfold log_get. rewrite String.eqb_refl.
  reflexivity.
Qed.

Lemma log_set_get_neq:
  forall log le r0 r1,
  String.eqb r0 r1 = false ->
  log_get (log_set log r0 le) r1 = log_get log r1.
Proof.
  intros. consider log_get. unfold log_set. simpl_match.
  Transparent __debug__.
  unfold __debug__.
  Opaque __debug__.
  auto.
Qed.
Lemma gamma_set_lookup_eq:
  forall {A} gamma v value (msg: A),
  gamma_lookup_var (gamma_set gamma v value) v msg = Success value.
Proof.
  intros.
  unfold gamma_lookup_var. unfold gamma_set. rewrite String.eqb_refl. reflexivity.
Qed.

Ltac solve_rules:=
  repeat match goal with
    | H: ImplInvariant ?impl_st
      |- valid_impl_state ?impl_st =>
      apply impl_wf; assumption
    | |- WF_log _ GenericLogEmpty =>
      apply WF_log_GenericLogEmpty
    | |- log_read0_only GenericLogEmpty _ =>
      apply log_read0_only_empty
    | H: log_eq_at_reg ?log1 ?log2 ?reg
      |- log_eq_at_reg ?log2 ?log1 ?reg =>
      apply log_eq_at_reg_sym
    | H: log_effectively_eq_at_reg ?log1 ?log2 ?reg
      |- log_effectively_eq_at_reg ?log2 ?log1 ?reg =>
      apply log_effectively_eq_at_reg_sym
    | H: log_read0_only ?log ?reg
      |- log_effectively_eq_at_reg ?log GenericLogEmpty ?reg =>
      apply log_read0_only_impl_effectively_empty
    | |- log_eq_at_reg GenericLogEmpty GenericLogEmpty ?reg =>
      apply log_eq_at_reg_empty
    | |- WF_log _ GenericLogEmpty =>
      apply WF_log_GenericLogEmpty
    | _ => simplify_pipeline_reg_types
    | _ => simplify_pipeline_logs
    | _ => progress auto
  end.
Lemma WF_log_set:
  forall types log reg le n,
  WF_log types log ->
  types reg = Some n ->
  WF_LE le n ->
  WF_log types (log_set log reg le).
Proof.
  intros. consider WF_log. intros. specialize H with (reg := reg0).
  destruct_match; auto. simplify.
  destruct_with_eqn (String.eqb reg reg0); simplify.
  - rewrite log_set_eq. rewrite Heqo in *. simplify.
  - rewrite log_set_neq by auto. simpl_match. auto.
Qed.
 Lemma LE_read0_only_app:
   forall le0 le1,
   LE_read0_only le0 ->
   LE_read0_only le1 ->
   LE_read0_only (logentry_app le0 le1).
 Proof.
   intros. consider logentry_app. consider LE_read0_only. simplify.
 Qed.

Lemma log_read0_only_app:
  forall log1 log2 reg,
  log_read0_only log1 reg ->
  log_read0_only log2 reg ->
  log_read0_only (log_app log1 log2) reg.
Proof.
  intros. consider log_read0_only. consider log_app. simplify.
  apply LE_read0_only_app; auto.
Qed.
Lemma log_read0_only_set_neq:
  forall log le reg0 reg1,
  String.eqb reg0 reg1 = false ->
  log_read0_only log reg1 ->
  log_read0_only (log_set log reg0 le) reg1.
Proof.
  intros. consider log_read0_only. consider log_set.
  rewrite H. simplify.
Qed.
Lemma log_read0_only_set_eq:
  forall log reg le,
  LE_read0_only le ->
  log_read0_only (log_set log reg le) reg.
Proof.
  consider log_read0_only. intros. unfold log_set. rewrite String.eqb_refl. auto.
Qed.
Lemma logentry_app_empty_l:
  forall l,
  logentry_app LE_empty l = l.
Proof.
  intros. consider logentry_app. simpl. destruct l; reflexivity.
Qed.

Lemma Taint1Untouched_log_app2:
  forall log log2,
  WF_log pipeline_reg_types log ->
  Taint1Untouched log2 GenericLogEmpty ->
  Taint1Untouched log (log_app log2 log).
Proof.
  intros * Hwf Htaint.
  consider WF_log.
  destruct Htaint. constructor; consider log_eq_at_reg; simplify.
  - specialize Hwf with (reg := RegR1). simpl in *. simplify. unfold log_app. repeat simpl_match.
    consider GenericLogEmpty. simplify.
    rewrite logentry_app_empty_l. auto.
  - specialize Hwf with (reg := RegR1'). simpl in *. simplify. unfold log_app. repeat simpl_match.
    consider GenericLogEmpty. simplify.
    rewrite logentry_app_empty_l. auto.
Qed.
Lemma Taint1Untouched_set1_neq:
  forall log1 log2 reg le,
  String.eqb reg RegR1 = false ->
  String.eqb reg RegR1' = false ->
  Taint1Untouched log1 log2 ->
  Taint1Untouched (log_set log1 reg le) log2.
Proof.
  intros * Hr1 Hr1' Htaint. destruct Htaint.
  constructor; solve_rules.
  - unfold log_eq_at_reg. unfold log_set. rewrite Hr1. auto.
  - unfold log_eq_at_reg. unfold log_set. rewrite Hr1'. auto.
Qed.
Lemma log_eq_at_reg_app2:
  forall reg log log2 v,
  log reg = Some v ->
  log_eq_at_reg GenericLogEmpty log2 reg ->
  log_eq_at_reg log (log_app log2 log) reg.
Proof.
  unfold log_eq_at_reg, log_app, GenericLogEmpty; intros; simplify.
  simpl_match.
  rewrite logentry_app_empty_l.
  auto.
Qed.
Lemma log_eq_at_reg_set2_neq:
  forall log1 log2 r1 le r2,
  String.eqb r1 r2 = false ->
  log_eq_at_reg log1 log2 r2 ->
  log_eq_at_reg log1 (log_set log2 r1 le) r2.
Proof.
  intros; consider log_eq_at_reg; consider log_set. rewrite H. simplify.
Qed.

(* (interp_action_cps st0,interp_action st1)
 *)
    Lemma Rl0_satisfies_spec:
      rule_satisfies_spec DoRl0__spec do_rule0.
    Proof.
      consider rule_satisfies_spec.
      intros * Hpre. destruct Hpre.
      apply wp_rule_correct.
      unfold wp_rule.
      apply wp_bind.
      apply wp_read0.
      subst.
      consider valid_impl_state. consider WF_state.
      pose proof (rl0_pre_valid_st0 RegClk) as wf_clk; simpl in wf_clk; simplify.
      pose proof (rl0_pre_valid_st0 RegR0) as wf_r0; simpl in wf_r0; simplify.

      rewrite_r_get_reg st RegClk.
      rewrite log_get_empty.
      rewrite LE_may_read0_empty_true.
      simpl.
      apply wp_if.
      apply wp_var.
      rewrite gamma_set_lookup.
      case_singleton l.
      - apply wp_bind.
        apply wp_read0.
        rewrite log_get_empty.
        rewrite log_set_get_neq by auto.
        rewrite log_get_empty.
        rewrite LE_may_read0_empty_true.
        rewrite_r_get_reg st RegR0.
        simpl.
        apply wp_write0.
        apply wp_var.
        rewrite gamma_set_lookup_eq by auto.
        rewrite log_get_empty.
        rewrite log_set_get_neq by auto.
        rewrite log_set_get_neq by auto.
        rewrite log_get_empty.
        rewrite LE_may_write0_empty_true.
        simpl.
        constructor.
        + apply WF_log_app; [ | solve[solve_rules]].
          eapply WF_log_set; simpl; eauto;
            [ | unfold pipeline_reg_types; simpl; eauto | constructor; simpl; auto].
          eapply WF_log_set; simpl; eauto;
           [ | unfold pipeline_reg_types; simpl; eauto | constructor; simpl; auto].
           eapply WF_log_set; simpl; eauto; [ unfold pipeline_reg_types; simpl; eauto| constructor; simpl; auto].
        + apply log_read0_only_app; solve_rules.
          apply log_read0_only_set_neq; [ solve[auto] | ].
          apply log_read0_only_set_neq; [ solve[auto] | ].
          apply log_read0_only_set_eq. consider LE_read0_only; simpl; auto.
        + constructor.
          * apply Taint1Untouched_log_app2; auto.
            apply Taint1Untouched_set1_neq; auto.
            apply Taint1Untouched_set1_neq; auto.
            apply Taint1Untouched_set1_neq; auto.
            solve_rules.
          * eapply log_eq_at_reg_app2; [ unfold GenericLogEmpty; eauto | ].
            apply log_eq_at_reg_set2_neq; auto.
            apply log_eq_at_reg_set2_neq; auto.
            apply log_eq_at_reg_set2_neq; auto.
            solve_rules.
        + intros Hclk. congruence.
     - apply wp_fail.
        constructor; solve_rules.
        intros; solve_rules.
    Qed.

Lemma wp_action2__reform:
  forall (r1: state_t) (L1: log_t) (a1: action)
    (r2: state_t) (L2: log_t) (a2: action)
    (post: action_postcondition2)
    gamma1 log1 gamma2 log2,
    wp_action2  r1 L1 a1
                r2 L2 a2
                post gamma1 log1 gamma2 log2 <->
    interp_action_cps r2 L2 a2
        (fun res2 => interp_action_cps r1 L1 a1 (fun res1 => post res1 res2) gamma1 log1)
        gamma2 log2.
Proof.
  reflexivity.
Qed.
      Transparent __debug__.
Require Import Koika.Magic.
Notation "'wp_action2' st1 log1 action1 st2 log2 action2 '[...]'"
  := (wp_action2 st1 log1 action1 st2 log2 action2 _)
       (at level 200, only printing) : wp_notations.


    Lemma Rl0_satisfies_sim_spec:
      rules_satisfy_sim_spec DoRl0__SimSpec do_rule0 do_rule0.
    Proof.
      pose proof Rl0_satisfies_spec as Inv0.
      pose proof Rl0_satisfies_spec as Inv1.
      consider rule_satisfies_spec.
      consider rules_satisfy_sim_spec. intros * HPreSim.
      destruct HPreSim as [DoRl0Pre0 DoRl0Pre1 DoRl0PreSim].
      specialize Inv0 with (1 := DoRl0Pre0).
      specialize Inv1 with (1 := DoRl0Pre1).
      destruct DoRl0Pre0.
      destruct DoRl0Pre1. subst.

      revert Inv1. revert Inv0.
      unfold interp_rule.

      hnf.

      apply wp_action2_correct' with (r1 := st0) (r2 := st1).
      apply wp2_bind0.
      apply wp2_bind1.

      apply wp2_read00.
      apply wp_read0.
      rewrite log_get_empty.
      rewrite LE_may_read0_empty_true.

      pose proof (rl0_pre_valid_st0 RegClk) as wf_clk_0; simpl in wf_clk_0; simplify.
      pose proof (rl0_pre_valid_st0 RegR0) as wf_r0_0; simpl in wf_r0_0; simplify.
      pose proof (rl0_pre_valid_st1 RegClk) as wf_clk_1; simpl in wf_clk_1; simplify.
      pose proof (rl0_pre_valid_st1 RegR0) as wf_r0_1; simpl in wf_r0_1; simplify.
      rewrite_r_get_reg st1 RegClk.
      rewrite_r_get_reg st0 RegClk.

      simpl.
      apply wp2_if.
      apply wp2_var0.

      apply wp_var; simpl.
      assert (l = l1).
      { destruct DoRl0PreSim. destruct sim_st2.
        consider st_eq_at_reg. repeat simpl_match. auto.
      }
      destruct (case_singleton_bool_list l1); [ auto | | ]; subst.
      - apply wp2_bind0; apply wp2_bind1.
        apply wp2_read00; apply wp_read0.
        simpl.
        rewrite_r_get_reg st1 RegR0.
        simpl.
        rewrite_r_get_reg st0 RegR0.
        apply wp2_write00.
        apply wp2_write01.

        apply wp2_var0.
        apply wp_var.
        simpl.
        intros * Hlog0 Hlog1.
        constructor; auto.
        destruct Hlog0.

        destruct Hlog1.
        repeat constructor; auto.
      - apply wp2_fail0.
        apply wp_fail. simpl.
        intros * Hlog0 Hlog1.
        constructor; auto.
        repeat constructor; auto.
    Time Qed.

    Lemma Test_satisfies_sim_spec:
      rules_satisfy_sim_spec DoRl0__SimSpec do_test do_test.
    Proof.
      consider rules_satisfy_sim_spec. intros * HPreSim.
      destruct HPreSim as [DoRl0Pre0 DoRl0Pre1 DoRl0PreSim].
      destruct DoRl0Pre0.
      destruct DoRl0Pre1. subst.

      unfold interp_rule.

      hnf.

      apply wp_action2_correct' with (r1 := st0) (r2 := st1).
      apply wp2_bind0.
      apply wp2_bind1.

      apply wp2_read00.
      apply wp_read0.
      rewrite log_get_empty.
      rewrite LE_may_read0_empty_true.

      pose proof (rl0_pre_valid_st0 RegClk) as wf_clk_0; simpl in wf_clk_0; simplify.
      pose proof (rl0_pre_valid_st0 RegR0) as wf_r0_0; simpl in wf_r0_0; simplify.
      pose proof (rl0_pre_valid_st1 RegClk) as wf_clk_1; simpl in wf_clk_1; simplify.
      pose proof (rl0_pre_valid_st1 RegR0) as wf_r0_1; simpl in wf_r0_1; simplify.
      rewrite_r_get_reg st1 RegClk.
      rewrite_r_get_reg st0 RegClk.

      simpl.
      apply wp2_if.
      apply wp2_var0.

      apply wp_var; simpl.
      assert (l = l1).
      { destruct DoRl0PreSim. destruct sim_st2.
        consider st_eq_at_reg. repeat simpl_match. auto.
      }
      destruct (case_singleton_bool_list l1); [ auto | | ]; subst.
      - apply wp2_bind0; apply wp2_bind1.
        apply wp2_read00; apply wp_read0.
        simpl.
        rewrite_r_get_reg st1 RegR0.
        simpl.
        rewrite_r_get_reg st0 RegR0.
        apply wp2_if.
        apply wp2_var0. apply wp_var; simpl.
        apply wp2_if.
        apply wp2_var0. apply wp_var; simpl.
        apply wp2_bind1.
        apply wp2_if0.
        apply wp2_var0.
        apply wp_read0.

        apply __magic__.
      - apply wp2_fail0.
        apply wp_fail. simpl.
        apply __magic__.
    Time Qed.


    Record DoRl1__Pre (st: state_t) (log: log_t) : Prop :=
      { rl1_pre_valid_st: valid_impl_state st;
        rl1_pre_valid_log: WF_log pipeline_reg_types log;
        rl1_pre_clk_read0_only: log_read0_only log RegClk
      }.

    Record DoRl1__Post (st: state_t) (input_log: log_t) (log: log_t) : Prop :=
      { rl1_post_valid_log: WF_log pipeline_reg_types log;
        rl1_post_clk_read0_only: log_read0_only log RegClk;
        rl1_taint0_untouched: Taint0Untouched input_log log;
        rl1_clk_impl_shared_untouched:
          st RegClk = Some [true] -> log_eq_at_reg input_log log RegRshared
      }.

    Definition DoRl1__spec : rule_spec_t :=
      {| Pre := DoRl1__Pre;
         Post := DoRl1__Post
      |}.

    Record DoRl1__SimPre (st0 st1: state_t) (log0 log1: log_t) : Prop :=
      { rl1_sim_pre0: DoRl1__Pre st0 log0;
        rl1_sim_pre1: DoRl1__Pre st1 log1;
        rl1_sim_pre_sim: GenericSim1 st0 st1 log0 log1
      }.

    Record DoRl1__SimPost' (st0 st1: state_t) (log0 log1: log_t) (log0' log1': log_t) : Prop :=
      { rl1_sim_post_sim: GenericLogSim1 log0' log1'
      }.

    Record DoRl1__SimPost (st0 st1: state_t) (log0 log1: log_t) (log0' log1': log_t) : Prop :=
      { rl1_sim_post0: DoRl0__Post st0 log0 log0';
        rl1_sim_post1: DoRl0__Post st1 log1 log1';
        rl1_sim_post : DoRl1__SimPost' st0 st1 log0 log1 log0' log1'
      }.

    Definition DoRl1__SimSpec : sim_spec_t :=
      {| PreSim := DoRl1__SimPre;
         PostSim := DoRl1__SimPost
      |}.

    Lemma Rl1_satisfies_spec:
      rule_satisfies_spec DoRl1__spec do_rule1.
    Admitted.

    Lemma Rl1_satisfies_sim_spec:
      rules_satisfy_sim_spec DoRl1__SimSpec do_rule1 do_rule1.
    Admitted.

    Record DoShared__Pre (st: state_t) (log: log_t) : Prop :=
      { rlshared_pre_valid_st: valid_impl_state st;
        rlshared_pre_valid_log: WF_log pipeline_reg_types log;
        rlshared_pre_clk_read0_only: log_read0_only log RegClk
      }.

    Record DoShared__Post (st: state_t) (input_log: log_t) (log: log_t) : Prop :=
      { rlshared_post_valid_log: WF_log pipeline_reg_types log;
        rlshared_post_clk_read0_only: log_read0_only log RegClk;
        rlshared_post_clk_taint0:
          st RegClk = Some [true] -> Taint1Untouched input_log log;
        rlshared_post_clk_taint1:
          st RegClk = Some [false] -> Taint0Untouched input_log log;
      }.

    Definition DoShared__spec : rule_spec_t :=
      {| Pre := DoShared__Pre;
         Post := DoShared__Post
      |}.

    Record DoShared__SimPre' (st0 st1: state_t) (log0 log1: log_t) : Prop :=
      { rlshared_sim_pre'__clk_st: st_eq_at_reg st0 st1 RegClk;
      }.

    Record DoShared__SimPre (st0 st1: state_t) (log0 log1: log_t) : Prop :=
      { rlshared_sim_pre0: DoShared__Pre st0 log0;
        rlshared_sim_pre1: DoShared__Pre st1 log1;
        rlshared_sim_pre': DoShared__SimPre' st0 st1 log0 log1
      }.

    Record DoShared__SimPost' (st0 st1: state_t) (log0 log1: log_t) (log0' log1': log_t) : Prop :=
      { rlshared_sim_post'_clk0: st0 RegClk = Some [true] ->
                                 GenericStSim0 st0 st1 ->
                                 GenericLogSim0 log0 log1 ->
                                 GenericLogSim0 log0' log1';
        rlshared_sim_post'_clk1: st0 RegClk = Some [false] ->
                                 GenericStSim1 st0 st1 ->
                                 GenericLogSim1 log0 log1 ->
                                 GenericLogSim1 log0' log1';
      }.

    Record DoShared__SimPost (st0 st1: state_t) (log0 log1: log_t) (log0' log1': log_t) : Prop :=
      { rlshared_sim_post0: DoShared__Post st0 log0 log0';
        rlshared_sim_post1: DoShared__Post st1 log1 log1';
        rlshared_sim_post' : DoShared__SimPost' st0 st1 log0 log1 log0' log1'
      }.


    Definition DoShared__SimSpec : sim_spec_t :=
      {| PreSim := DoShared__SimPre;
         PostSim := DoShared__SimPost
      |}.


    Lemma RlShared_satisfies_spec:
      rule_satisfies_spec DoShared__spec do_shared.
    Admitted.


    Lemma RlShared_satisfies_sim_spec:
      rules_satisfy_sim_spec DoShared__SimSpec do_shared do_shared.
    Admitted.


    Record DoClk__Pre (st: state_t) (log: log_t) : Prop :=
      { rlclk_pre_valid_st: valid_impl_state st;
        rlclk_pre_valid_log: WF_log pipeline_reg_types log;
        rlclk_pre_clk_read0_only: log_read0_only log RegClk
      }.

    Record DoClk__Post (st: state_t) (input_log: log_t) (log: log_t) : Prop :=
      { rlclk_post_valid_log: WF_log pipeline_reg_types log;
        rlclk_untainted0: Taint0Untouched input_log log;
        rlclk_untainted1: Taint1Untouched input_log log
      }.

    Definition DoClk__spec : rule_spec_t :=
      {| Pre := DoClk__Pre;
         Post := DoClk__Post
      |}.



    Record DoClk__SimPre (st0 st1: state_t) (log0 log1: log_t) : Prop :=
      { rlclk_sim_pre0: DoClk__Pre st0 log0;
        rlclk_sim_pre1: DoClk__Pre st1 log1;
        rlclk_sim_eq_st: st_eq_at_reg st0 st1 RegClk
      }.

    Record DoClk__SimPost (st0 st1: state_t) (log0 log1: log_t) (log0' log1': log_t) : Prop :=
      { rlclk_sim_post0: DoClk__Post st0 log0 log0';
        rlclk_sim_post1: DoClk__Post st1 log1 log1';
        rlclk_sim_eq_clk: latest_write_eq_at_reg log0' log1' RegClk
      }.

    Definition DoClk__SimSpec : sim_spec_t :=
      {| PreSim := DoClk__SimPre;
         PostSim := DoClk__SimPost
      |}.

    Lemma RlClk_satisfies_spec:
      rule_satisfies_spec DoClk__spec do_clk.
    Proof.
      consider rule_satisfies_spec.
      intros * Hpre. destruct Hpre.
      apply wp_rule_correct.
      unfold wp_rule.
      set do_clk as rl. unfold do_clk in *.
      unfold interp_rule_cps. unfold rl. simpl.
      unfold interp_action_cps.

    Admitted.

    Lemma RlClk_satisfies_sim_spec:
      rules_satisfy_sim_spec DoClk__SimSpec do_clk do_clk.
    Proof.
      pose proof RlClk_satisfies_spec as Hstep.
      consider rules_satisfy_sim_spec.
      intros * HPreSim.
      destruct HPreSim.
      consider rule_satisfies_spec.
      pose proof (Hstep _ _ rlclk_sim_pre2) as Hstep0.
      pose proof (Hstep _ _ rlclk_sim_pre3) as Hstep1.
      set (interp_rule st0 _ _) as interp0 in *.
      set (interp_rule st1 _ _) as interp1 in *.

      simplify.
    Admitted.

    Lemma interp_scheduler'_cons__spec:
      forall {rule_name_t: Type}
      (st: state_t) (rules: rule_name_t -> action) rl s (input_log output_log: log_t)
      (rl_spec: rule_spec_t),
      rule_satisfies_spec rl_spec (rules rl) ->
      rl_spec.(Pre) st input_log ->
      interp_scheduler' st rules (Cons rl s) input_log = Success output_log ->
      exists log, rl_spec.(Post) st input_log log /\
        interp_scheduler' st rules s log = Success output_log.
    Proof.
      intros * Hspec Hpre Hsched. simpl in *.
      consider rule_satisfies_spec. specialize Hspec with (1 := Hpre).
      bash_destruct Hsched.
      - exists (log_app l input_log). split; auto.
      - exists input_log; auto.
    Qed.

    Lemma interp_scheduler'_cons__sim_spec:
      forall {rule_name_t: Type}
      (st0 st1: state_t) (rules: rule_name_t -> action) rl0 rl1 s0 s1
      (input_log0 input_log1 output_log0 output_log1: log_t)
      (rl_spec: sim_spec_t),
      rules_satisfy_sim_spec rl_spec (rules rl0) (rules rl1)->
      PreSim rl_spec st0 st1 input_log0 input_log1 ->
      interp_scheduler' st0 rules (Cons rl0 s0) input_log0 = Success output_log0 ->
      interp_scheduler' st1 rules (Cons rl1 s1) input_log1 = Success output_log1 ->
      exists log0 log1,
        PostSim rl_spec st0 st1 input_log0 input_log1 log0 log1 /\
        interp_scheduler' st0 rules s0 log0 = Success output_log0 /\
        interp_scheduler' st1 rules s1 log1 = Success output_log1.
    Proof.
      intros * HSpec Hpre Hsched0 Hsched1. simpl in *.
      consider rules_satisfy_sim_spec. specialize HSpec with (1 := Hpre).
      bash_destruct Hsched0; bash_destruct Hsched1; auto.
      all: eexists; eexists; split_ands_in_goal; eauto.
    Qed.

  Lemma solve_rl0_precondition:
    forall impl_st,
    valid_impl_state impl_st ->
    Pre DoRl0__spec impl_st GenericLogEmpty.
  Proof.
    intros * Hst. constructor; auto.
    apply WF_log_GenericLogEmpty.
  Qed.

  Lemma solve_rl1_precondition:
    forall impl_st log,
    valid_impl_state impl_st ->
    Post DoRl0__spec impl_st GenericLogEmpty log ->
    Pre DoRl1__spec impl_st log.
  Proof.
    intros * Hst Hpost.
    destruct Hpost. constructor; auto.
  Qed.

  Lemma solve_rlshared_precondition:
    forall impl_st input_log log,
    valid_impl_state impl_st ->
    Post DoRl1__spec impl_st input_log log ->
    Pre DoShared__spec impl_st log.
  Proof.
    intros * Hst Hpost.
    destruct Hpost. constructor; auto.
  Qed.

      Ltac step_interp_rule Hinterp spec PfSpec NewLog NewPost NewInterp SolvePre :=
        eapply interp_scheduler'_cons__spec with (rl_spec := spec) in Hinterp;
        [ | apply PfSpec | eapply SolvePre; solve_rules; eauto];
        destruct Hinterp as (NewLog & NewPost & NewInterp).


Lemma wf_mk_st__clk:
  forall clk, pipeline_reg_types RegClk = Some (Datatypes.length clk) ->
         valid_impl_state (mk_st__clk (Some clk)).
Proof.
  intros * Ht. consider valid_impl_state. consider mk_st__clk. consider pipeline_reg_types.
  unfold WF_state. intros.
  destruct_match; auto; simplify; simpl in Ht; simplify.
  destruct_match; simplify.
  destruct_match; simplify.
  destruct_match; simplify.
  destruct_match; simplify.
  destruct_match; simplify.
Qed.


Lemma ClkPreSim:
  forall impl_st LogRl1 LogRl__Shared clk,
  ImplInvariant impl_st ->
  Post DoShared__spec impl_st LogRl1 LogRl__Shared ->
  pipeline_reg_types RegClk = Some (Datatypes.length clk) ->
  impl_st RegClk = Some clk ->
  PreSim DoClk__SimSpec impl_st (mk_st__clk (Some clk)) LogRl__Shared GenericLogEmpty.
Proof.
  intros * Hinv Hpost Hclk.
  destruct Hpost.
  repeat constructor; solve_rules.
  - apply wf_mk_st__clk. unfold pipeline_reg_types. auto.
  -  unfold st_eq_at_reg, mk_st__clk. simpl.
     simpl_match. auto.
Qed.
      Ltac step_interp_rule_sim Hinterp0 Hinterp1 spec PfSpec PfPreSim
                                NewLog0 NewLog1 NewPost NewInterp0 NewInterp1 :=
      eapply interp_scheduler'_cons__sim_spec with (rl_spec := spec) in Hinterp1;
      [ | | | apply Hinterp0 ];
      [ | apply PfSpec | eapply PfPreSim; eauto; solve_rules];
      destruct Hinterp1 as (NewLog0 & NewLog1 & NewPost & NewInterp0 & NewInterp1).

      Lemma wf_mk_st0:
        forall impl_st spec_st,
          valid_impl_state impl_st ->
          WF_spec_local_st spec_st ->
          valid_impl_state (mk_st0 spec_st (impl_st RegClk)).
      Proof.
        intros * Hvalid Hvalid_spec.
        consider valid_impl_state. consider mk_st0. consider WF_state. consider WF_spec_local_st.
        bash_destruct Hvalid_spec; auto.
        intros. specialize Hvalid with (reg := reg).
        destruct_match; simplify.  consider pipeline_reg_types.
        destruct_match; simplify.
        destruct_match; simplify.
        destruct_match; simplify.
        destruct_match; simplify.
        destruct_match; simplify.
        destruct_match; simplify.
        destruct_match; simplify.
      Qed.

      Lemma wf_mk_st1:
        forall impl_st spec_st,
          valid_impl_state impl_st ->
          WF_spec_local_st spec_st ->
          valid_impl_state (mk_st1 spec_st (impl_st RegClk)).
      Proof.
        intros * Hvalid Hvalid_spec.
        consider valid_impl_state. consider mk_st1. consider WF_state. consider WF_spec_local_st.
        bash_destruct Hvalid_spec; auto.
        intros. specialize Hvalid with (reg := reg).
        destruct_match; simplify.  consider pipeline_reg_types.
        destruct_match; simplify.
        destruct_match; simplify.
        destruct_match; simplify.
        destruct_match; simplify.
        destruct_match; simplify.
        destruct_match; simplify.
        destruct_match; simplify.
      Qed.
    Ltac rewrite_match :=
      match goal with
      | H: ?t = _
        |- match ?t with | _ => _ end =>
        rewrite H
      end.
      Lemma Rl0PreSim:
        forall impl_st spec_st,
        ImplInvariant impl_st ->
        WF_spec_local_st spec_st ->
        Sim0 impl_st spec_st ->
        PreSim DoRl0__SimSpec impl_st (mk_st0 spec_st (impl_st RegClk)) GenericLogEmpty GenericLogEmpty.
      Proof.
        intros * Hinv Hspec HSim.
        constructor; solve_rules.
        - constructor; solve_rules.
        - constructor; solve_rules.
          apply wf_mk_st0; solve_rules.
        - constructor.
          + destruct HSim.
            assert (valid_impl_state impl_st) as Hvalid by solve_rules.
            consider WF_spec_local_st. simplify. consider valid_impl_state. consider WF_state.
            constructor; unfold st_eq_at_reg, mk_st1; simpl; try rewrite_match.
            * specialize Hvalid with (reg := RegClk). simpl in *. simplify. simpl. auto.
            * specialize Hvalid with (reg := RegR0). unfold mk_st0. simpl in *. simplify. simpl_match. auto.
            * specialize Hvalid with (reg := RegR0'). unfold mk_st0. simpl in *. simplify. simpl_match. auto.
          + constructor; unfold log_effectively_eq_at_reg, log_eq_at_reg; simpl; propositional.
      Qed.
      Lemma RlSharedPreSim0:
        forall impl_st spec_st spec_log impl_log impl_log' impl_log'' spec_log',
        ImplInvariant impl_st ->
        WF_spec_local_st spec_st ->
        Sim0 impl_st spec_st ->
        PostSim DoRl0__SimSpec impl_st (mk_st0 spec_st (impl_st RegClk))
                impl_log spec_log impl_log' spec_log' ->
        Post DoRl1__spec impl_st impl_log' impl_log'' ->
        PreSim DoShared__SimSpec impl_st (mk_st0 spec_st (impl_st RegClk)) impl_log'' spec_log'.
      Proof.
        intros * Hinv Hspec Hsim Hrl0 Hrl1.
        destruct Hrl0.
        constructor.
        - constructor; destruct rl0_sim_post2; destruct Hrl1; solve_rules.
        - constructor; solve_rules.
          + apply wf_mk_st0; solve_rules.
          + destruct rl0_sim_post3; auto.
          + destruct rl0_sim_post3; auto.
        - assert (valid_impl_state impl_st) as Hvalid by solve_rules.
          consider valid_impl_state. consider WF_state.
          assert (st_eq_at_reg impl_st (mk_st0 spec_st (impl_st RegClk)) RegClk) as Hclk_sim.
          { destruct Hsim; auto.
            specialize Hvalid with (reg := RegClk). simpl in Hvalid.
              unfold mk_st0. unfold st_eq_at_reg. simpl. destruct_match; auto.
          }
          constructor; auto.
      Qed.

    Lemma solve_rlclk_precondition:
      forall st log log',
      valid_impl_state st ->
      DoShared__Post st log log' ->
      Pre DoClk__spec st log'.
    Proof.
      intros * Hvalid Hshared.
      destruct Hshared.
      constructor; auto.
    Qed.
    Lemma solve_rlclk_precondition_postSim:
      forall impl_st spec_st impl_log spec_log impl_log' spec_log',
      valid_impl_state impl_st ->
      PostSim DoShared__SimSpec impl_st spec_st impl_log spec_log impl_log' spec_log' ->
      Pre DoClk__spec impl_st impl_log'.
    Proof.
      intros * Hvalid Hpost. destruct Hpost.
      eapply solve_rlclk_precondition; eauto.
    Qed.
    Lemma Sim0_impl_tau_eq:
      forall impl_st' local_spec_st' impl_tau spec_tau,
        Sim0 impl_st' local_spec_st' ->
        get_obs impl_st' = Success impl_tau ->
        local_spec_st'.(local_st') = Some spec_tau ->
        fst impl_tau = spec_tau.
    Proof.
      intros * Hsim Hobs Hspec.
      destruct Hsim. consider get_obs.
      simplify_result. simpl in *.
      rewrite Hspec in *. simplify.
    Qed.

    Lemma Sim1_impl_tau_eq:
      forall impl_st' local_spec_st' impl_tau spec_tau,
        Sim1 impl_st' local_spec_st' ->
        get_obs impl_st' = Success impl_tau ->
        local_spec_st'.(local_st') = Some spec_tau ->
        snd impl_tau = spec_tau.
    Proof.
      intros * Hsim Hobs Hspec.
      destruct Hsim. consider get_obs.
      simplify_result. simpl in *.
      rewrite Hspec in *. simplify.
    Qed.
    Lemma clk_true_or_false:
      forall impl_st,
      valid_impl_state impl_st ->
      impl_st RegClk = Some [true] \/ impl_st RegClk = Some [false].
    Proof.
      intros * Himpl. consider valid_impl_state. consider WF_state.
      specialize Himpl with (reg := RegClk). simpl in *.
      simplify. destruct l; simpl in *; try discriminate.
      destruct l; simpl in *; try discriminate.
      destruct b; auto.
    Qed.

    Lemma log_read0_only_still_eq:
      forall impl_log spec_log reg,
      log_read0_only impl_log reg ->
      log_read0_only spec_log reg ->
      log_effectively_eq_at_reg impl_log spec_log reg.
    Proof.
      intros * Himpl Hspec.
      consider log_effectively_eq_at_reg.
      consider log_read0_only.
      simplify. consider LE_read0_only. simplify.
    Qed.
    Lemma log_eq_trans2:
      forall ilog1 slog1 ilog2 slog2 reg,
      log_eq_at_reg ilog1 slog1 reg ->
      log_eq_at_reg ilog1 ilog2 reg ->
      log_eq_at_reg slog1 slog2 reg ->
      log_eq_at_reg ilog2 slog2 reg.
    Proof.
      intros. consider log_eq_at_reg.
      simplify.
    Qed.

    Lemma log_eq_at_reg_trans__1:
      forall log1 log1' log2 reg,
        log_eq_at_reg log1 log1' reg ->
        log_eq_at_reg log1 log2 reg ->
        log_eq_at_reg log1' log2 reg.
    Proof.
      intros. consider log_eq_at_reg. simplify.
    Qed.

    Lemma solve_sim0:
        forall impl_st spec_st impl_st' spec_st'
          ilog__shared slog__shared ilog__clk ilog__rl0 slog__rl0 ilog__rl1,
        ImplInvariant impl_st ->
        WF_spec_local_st spec_st ->
        Sim0 impl_st spec_st ->
        PostSim DoRl0__SimSpec impl_st (mk_st0 spec_st (impl_st RegClk))
                              GenericLogEmpty GenericLogEmpty ilog__rl0 slog__rl0 ->
        Post DoRl1__spec impl_st ilog__rl0 ilog__rl1 ->
        PostSim DoShared__SimSpec impl_st (mk_st0 spec_st (impl_st RegClk))
                ilog__rl1 slog__rl0
                ilog__shared slog__shared ->
        Post DoClk__spec impl_st ilog__shared ilog__clk ->
        commit_update impl_st ilog__clk = Success impl_st' ->
        commit_update (mk_st0 spec_st (impl_st RegClk)) slog__shared = Success spec_st' ->
        Sim0 impl_st' {| local_st := spec_st' RegR0; local_st' := spec_st' RegR0' |}.
    Proof.
      intros * Hinv Hwf_spec Hsim Hrl0 Hrl1 Hshared Hclk Himpl Hspec.

      cut (log_eq_at_reg ilog__clk slog__shared RegR0 /\
           log_eq_at_reg ilog__clk slog__shared RegR0').
      { intros (HR0 & HR0').
        consider commit_update. simplify. unfold mk_st0; simpl.
        destruct Hsim. consider log_eq_at_reg.
        constructor; simpl; auto.
        - rewrite sim__r2. destruct_match; simplify.
        - rewrite sim__r0'0. destruct_match; simplify.
      }

      cut (GenericLogSim0 ilog__shared slog__shared).
      { intros HLogSim. destruct Hshared.
        destruct Hclk. destruct rlclk_untainted2.
        destruct HLogSim.
        split.
        - eapply log_eq_at_reg_trans__1; eauto.
        - eapply log_eq_at_reg_trans__1; eauto.
      }

      cut (GenericLogSim0 ilog__rl1 slog__rl0).
      { intros HLogSim. destruct Hshared. destruct rlshared_sim_post'0; propositional.
        assert (valid_impl_state impl_st) as Hvalid_impl by solve_rules.
        pose proof (clk_true_or_false _  Hvalid_impl) as Hclk_disj.
        destruct Hclk_disj as [Hclk__true | Hclk__false].
        { propositional.
          apply rlshared_sim_post'_clk2; auto.
          destruct Hsim.
          constructor; unfold mk_st0, st_eq_at_reg; simpl; auto;
            consider WF_spec_local_st; rewrite_match; auto; destruct_match; auto.
          simplify.
        }
        { propositional.
          constructor.
          - destruct rlshared_sim_post2.
            destruct rlshared_sim_post3.
            apply log_read0_only_still_eq; auto.
          - destruct rlshared_sim_post2.
            destruct rlshared_sim_post3. propositional.
            destruct HLogSim.
            destruct rlshared_post_clk_taint3.
            destruct rlshared_post_clk_taint5.
            apply log_eq_trans2 with (1 := logsim0_eq_r1); auto.
          - destruct rlshared_sim_post2.
            destruct rlshared_sim_post3. propositional.
            destruct HLogSim.
            destruct rlshared_post_clk_taint3.
            destruct rlshared_post_clk_taint5.
            apply log_eq_trans2 with (1 := logsim0_eq_r0'0); auto.
        }
      }

      cut (GenericLogSim0 ilog__rl0 slog__rl0).
      { intros HLogSim. destruct Hrl1.
        destruct rl1_taint0_untouched0.
        constructor.
        - destruct Hrl0. destruct rl0_sim_post3.
          apply log_read0_only_still_eq; auto.
        - destruct Hrl0. destruct rl0_sim_post4. destruct rl0_sim_post_sim0.
          eapply log_eq_at_reg_trans__1; eauto.
        - destruct Hrl0. destruct rl0_sim_post4. destruct rl0_sim_post_sim0.
          eapply log_eq_at_reg_trans__1; eauto.
      }

      { destruct Hrl0. destruct rl0_sim_post4. auto. }
    Qed.

    Lemma sim_step0: forall impl_st spec_st spec__clk impl_st' impl_tau spec_st' spec_tau,
      ImplInvariant impl_st ->
      WF_spec_clk spec__clk ->
      WF_spec_local_st spec_st ->
      ImplInvariant impl_st' ->
      WF_spec_local_st spec_st' ->
      Sim0 impl_st spec_st ->
      impl_st RegClk = spec__clk ->
      impl_step impl_st = Success (impl_st', impl_tau) ->
      spec_f0 spec_st spec__clk = Success (spec_st', spec_tau) ->
      Sim0 impl_st' spec_st' /\ fst(impl_tau) = spec_tau.
    Proof.
      intros * HInv Hwf_clk Hspec HInv' Hspec' Hsim Hclk Himpl_step Hspec_step.
      consider impl_step.
      consider spec_f0.
      unfold step in *. simplify_result.
      bash_destruct Hspec_step; simplify_result.
      consider commit_update. simplify_result. simpl.
      unfold schedule in *.
      unfold interp_cycle in *. simplify_result.
      consider @interp_scheduler.
      rename Heqr3 into ImplInterp0.
      rename Heqr2 into SpecInterp0.
      step_interp_rule_sim ImplInterp0 SpecInterp0 DoRl0__SimSpec Rl0_satisfies_sim_spec
                           Rl0PreSim
                           LogRl0 LogSpec0 PostRl0 ImplInterp1 SpecInterp1. clear ImplInterp0.
      pose proof (rl0_sim_post0 _ _ _ _ _ _ PostRl0) as PostRl0__0.
      step_interp_rule ImplInterp1 DoRl1__spec Rl1_satisfies_spec
                       Log__Rl1 Post__Rl1 ImplInterp2 solve_rl1_precondition.
      step_interp_rule_sim ImplInterp2 SpecInterp1 DoShared__SimSpec RlShared_satisfies_sim_spec
                           RlSharedPreSim0
                           LogRl__Shared LogSpec__Shared PostRl__Shared ImplInterp3 SpecInterp2;
                           clear ImplInterp2.
      step_interp_rule ImplInterp3 DoClk__spec RlClk_satisfies_spec
                       Log__RlClk Post__RlClk ImplInterp4 solve_rlclk_precondition_postSim.
      simpl in ImplInterp4. simpl in SpecInterp2. simplify.

      assert_left_as HSim'.
      - rewrite<-Heqo.
        eapply solve_sim0 with (2 := Hspec) (impl_st := impl_st) (spec_st := spec_st); eauto.
      - eapply Sim0_impl_tau_eq; eauto.
    Qed.

      Lemma Rl1PreSim:
        forall impl_st spec_st impl_log,
        ImplInvariant impl_st ->
        Post DoRl0__spec impl_st GenericLogEmpty impl_log ->
        WF_spec_local_st spec_st ->
        Sim1 impl_st spec_st ->
        PreSim DoRl1__SimSpec impl_st (mk_st1 spec_st (impl_st RegClk)) impl_log GenericLogEmpty.
      Proof.
        intros * Hinv Hpost Hspec Hsim. destruct Hpost.
        constructor.
        - constructor; solve_rules.
        - constructor; solve_rules.
          apply wf_mk_st1; solve_rules.
        - destruct Hsim. assert (valid_impl_state impl_st) as Hvalid by solve_rules.
          consider valid_impl_state. consider WF_state.
          constructor.
          + constructor.
            * specialize Hvalid with (reg := RegClk). simpl in Hvalid.
              unfold mk_st1. unfold st_eq_at_reg. simpl. destruct_match; auto.
            * specialize Hvalid with (reg := RegR1). simpl in Hvalid.
              unfold mk_st1. unfold st_eq_at_reg. simpl. destruct_match; auto.
              simpl_match. reflexivity.
            * specialize Hvalid with (reg := RegR1'). simpl in Hvalid.
              unfold mk_st1. unfold st_eq_at_reg. simpl. destruct_match; auto.
              simpl_match. reflexivity.
         + destruct rl0_taint1_untouched0.
           constructor; auto; solve_rules.
      Qed.
      Lemma RlSharedPreSim1:
        forall impl_st spec_st spec_log impl_log impl_log' spec_log',
        ImplInvariant impl_st ->
        WF_spec_local_st spec_st ->
        Sim1 impl_st spec_st ->
        PostSim DoRl1__SimSpec impl_st (mk_st1 spec_st (impl_st RegClk))
                impl_log spec_log impl_log' spec_log' ->
        PreSim DoShared__SimSpec impl_st (mk_st1 spec_st (impl_st RegClk)) impl_log' spec_log'.
      Proof.
        intros * Hinv Hspec Hsim Hpost.
        destruct Hpost.
        constructor.
        - constructor; destruct rl1_sim_post2; solve_rules.
        - constructor; solve_rules.
          + apply wf_mk_st1; solve_rules.
          + destruct rl1_sim_post3; auto.
          + destruct rl1_sim_post3; auto.
        - assert (valid_impl_state impl_st) as Hvalid by solve_rules.
          consider valid_impl_state. consider WF_state.
          assert (st_eq_at_reg impl_st (mk_st1 spec_st (impl_st RegClk)) RegClk) as Hclk_sim.
          { destruct Hsim; auto.
            specialize Hvalid with (reg := RegClk). simpl in Hvalid.
              unfold mk_st1. unfold st_eq_at_reg. simpl. destruct_match; auto.
          }
          constructor; auto.
      Qed.



    Lemma solve_sim1:
        forall impl_st spec_st impl_st' spec_st'
          ilog__shared slog__shared ilog__clk ilog__rl1 slog__rl1 ilog__rl0 ,
        ImplInvariant impl_st ->
        WF_spec_local_st spec_st ->
        Sim1 impl_st spec_st ->
        Post DoRl0__spec impl_st GenericLogEmpty ilog__rl0 ->
        PostSim DoRl1__SimSpec impl_st (mk_st1 spec_st (impl_st RegClk))
                             ilog__rl0 GenericLogEmpty ilog__rl1 slog__rl1 ->
        PostSim DoShared__SimSpec impl_st (mk_st1 spec_st (impl_st RegClk))
                ilog__rl1 slog__rl1
                ilog__shared slog__shared ->
        Post DoClk__spec impl_st ilog__shared ilog__clk ->
        commit_update impl_st ilog__clk = Success impl_st' ->
        commit_update (mk_st1 spec_st (impl_st RegClk)) slog__shared = Success spec_st' ->
        Sim1 impl_st' {| local_st := spec_st' RegR1; local_st' := spec_st' RegR1' |}.
    Proof.
      intros * Hinv Hwf_spec Hsim Hrl0 Hrl1 Hshared Hclk Himpl Hspec.

      cut (log_eq_at_reg ilog__clk slog__shared RegR1 /\
           log_eq_at_reg ilog__clk slog__shared RegR1').
      { intros Hlogsim.
        propositional.
        consider log_eq_at_reg. simplify.
        consider commit_update. simplify.

        destruct Hsim.
        constructor; simpl.
        + unfold mk_st1. simpl. rewrite sim__r2. destruct_match; auto.
          repeat simpl_match; auto.
        + unfold mk_st1. simpl. rewrite sim__r1'0. destruct_match; auto.
          repeat simpl_match; auto.
      }

      cut (GenericLogSim1 ilog__shared slog__shared).
      { intros HLogSim.
        destruct HLogSim. destruct Hclk. destruct rlclk_untainted3.
        consider log_eq_at_reg. simplify.
      }

      cut (GenericLogSim1 ilog__rl1 slog__rl1).
      { intros HLogSim. destruct HLogSim.
        destruct Hshared. destruct rlshared_sim_post'0. destruct rlshared_sim_post3; propositional.
        assert (valid_impl_state impl_st) as Hvalid_impl by solve_rules.
        pose proof (clk_true_or_false _  Hvalid_impl) as Hclk_disj.
        destruct Hclk_disj as [Hclk__true | Hclk__false].
        { propositional.
          constructor.
          - apply log_read0_only_still_eq; auto. destruct rlshared_sim_post2; auto.
          - destruct rlshared_post_clk_taint2.
            apply log_eq_trans2 with (1 := logsim1_eq_r2); auto.
            destruct rlshared_sim_post2; propositional.
            destruct rlshared_post_clk_taint2; auto.
          - destruct rlshared_post_clk_taint2.
            apply log_eq_trans2 with (1 := logsim1_eq_r1'0); auto.
            destruct rlshared_sim_post2; propositional.
            destruct rlshared_post_clk_taint2; auto.
        }
        { propositional.
          assert_pre_as Hstsim rlshared_sim_post'_clk3; propositional.
          { unfold mk_st1.
            destruct Hsim. constructor; unfold st_eq_at_reg; simpl; repeat simpl_match; auto.
            * rewrite_match. destruct_match; auto. consider WF_spec_local_st. simplify.
            * rewrite_match. destruct_match; auto. consider WF_spec_local_st. simplify.
          }
          assert_pre_as Hlogsim rlshared_sim_post'_clk3; propositional.
          { constructor; auto. }
        }
      }
      { destruct Hrl1.
        destruct rl1_sim_post4. auto.
      }
    Qed.

    Lemma sim_step1: forall impl_st spec_st spec__clk impl_st' impl_tau spec_st' spec_tau,
      ImplInvariant impl_st ->
      WF_spec_clk spec__clk ->
      WF_spec_local_st spec_st ->
      ImplInvariant impl_st' ->
      WF_spec_local_st spec_st' ->
      Sim1 impl_st spec_st ->
      impl_st RegClk = spec__clk ->
      impl_step impl_st = Success (impl_st', impl_tau) ->
      spec_f1 spec_st spec__clk = Success (spec_st', spec_tau) ->
      Sim1 impl_st' spec_st' /\ snd(impl_tau) = spec_tau.
    Proof.
      intros * HInv Hwf_clk Hspec HInv' Hspec' Hsim Hclk Himpl_step Hspec_step.
      consider impl_step.
      consider spec_f1.
      unfold step in *. simplify_result.
      bash_destruct Hspec_step; simplify_result.
      consider commit_update. simplify_result. simpl.
      unfold schedule in *.
      unfold interp_cycle in *. simplify_result.
      consider @interp_scheduler.
      rename Heqr3 into ImplInterp0.
      rename Heqr2 into SpecInterp0.

      step_interp_rule ImplInterp0 DoRl0__spec Rl0_satisfies_spec
                       Log__Rl0 Post__Rl0 ImplInterp1 solve_rl0_precondition.
      step_interp_rule_sim ImplInterp1 SpecInterp0 DoRl1__SimSpec Rl1_satisfies_sim_spec
                           Rl1PreSim
                           LogRl1 LogSpec1 PostRl1 ImplInterp2 SpecInterp1. clear ImplInterp1.
      step_interp_rule_sim ImplInterp2 SpecInterp1 DoShared__SimSpec RlShared_satisfies_sim_spec
                           RlSharedPreSim1
                           LogRl__Shared LogSpec__Shared PostRl__Shared ImplInterp3 SpecInterp2; clear ImplInterp2.
      step_interp_rule ImplInterp3 DoClk__spec RlClk_satisfies_spec
                       Log__RlClk Post__RlClk ImplInterp4 solve_rlclk_precondition_postSim.
      simpl in ImplInterp4. simpl in SpecInterp2. simplify.

      assert_left_as HSim'.
      - rewrite<-Heqo. eapply solve_sim1 with (2 := Hspec) (impl_st := impl_st) (spec_st := spec_st); eauto.
      - eapply Sim1_impl_tau_eq; eauto.
    Qed.

    Lemma sim_step__clk: forall impl_st spec__clk impl_st' impl_tau spec__clk',
      ImplInvariant impl_st ->
      WF_spec_clk spec__clk ->
      ImplInvariant impl_st' ->
      WF_spec_clk spec__clk' ->
      impl_st RegClk = spec__clk ->
      impl_step impl_st = Success (impl_st', impl_tau) ->
      spec_f__clk spec__clk = Success (spec__clk') ->
      impl_st' RegClk = spec__clk'.
    Proof.
      intros * HInv Hclk HInv' Hclk' Hsim Himpl Hspec.
      consider impl_step.
      consider spec_f__clk.
      unfold step in *. simplify_result.
      bash_destruct Hspec. simplify_result.
      unfold interp_cycle in Heqr1. simplify_result.
      consider commit_update. simplify_result. simpl.
      consider WF_spec_clk.
      bash_destruct Hclk; auto. simpl in *.
      unfold interp_cycle in Heqr. simplify_result.
      unfold schedule in *.
      consider @interp_scheduler.

      step_interp_rule Heqr1 DoRl0__spec Rl0_satisfies_spec
                       Log__Rl0 Post__Rl0 Interp1 solve_rl0_precondition.
      step_interp_rule Interp1 DoRl1__spec Rl1_satisfies_spec
                       LogRl1 Post__Rl1 Interp2 solve_rl1_precondition.
      step_interp_rule Interp2 DoShared__spec RlShared_satisfies_spec
                       LogRl__Shared Post__RlShared Interp3 solve_rlshared_precondition.

      step_interp_rule_sim Interp3 Heqr2 DoClk__SimSpec RlClk_satisfies_sim_spec ClkPreSim
                           LogRl__Clk LogSpec__Clk PostRl__Clk Interp4 Interp__Spec.

      simpl in Interp__Spec. simpl in Interp4. simplify_result.

      consider commit_update. simplify_result.
      simpl_match.
      destruct PostRl__Clk.
      consider latest_write_eq_at_reg. bash_destruct rlclk_sim_eq_clk0; auto.
      consider LE_latest_write.
      bash_destruct rlclk_sim_eq_clk0.
    Qed.

    Lemma simulation_preserved__step:
      forall (impl_st: state_t) (spec_st: _spec_st_t),
      Sim impl_st spec_st ->
      match impl_step impl_st, _spec_step spec_st with
      | Success (impl_st', impl_tau), Success (spec_st', spec_tau) =>
          Sim impl_st' spec_st' /\ impl_tau = spec_tau
      | _, _ => False
      end.
    Proof.
      intros * HSim.
      pose proof impl_invariant_preserved__step _ (impl_invariant _ _ HSim) as Himpl.
      pose proof spec_invariant_preserved__step _ (spec_invariant _ _ HSim) as Hspec.
      bash_destruct Himpl. bash_destruct Hspec. propositional.
      consider impl_step. consider _spec_step.
      unfold spec_step in *.
      repeat (simplify_result; destruct_match_pairs; subst).
      destruct HSim. destruct sim2.

      assert (Sim0 s0 s2 /\ fst i = t).
      { destruct spec_invariant0. destruct spec_wf0.
        destruct Hspec0. destruct spec_wf0; simpl in *.
        eapply sim_step0 with
            (impl_st := impl_st) (spec_st := state0 spec_st) (spec__clk := state__clk spec_st); eauto.
      }

      assert (Sim1 s0 s3 /\ snd i = t0).
      { destruct spec_invariant0. destruct spec_wf0.
        destruct Hspec0. destruct spec_wf0; simpl in *.
        eapply sim_step1 with
            (impl_st := impl_st) (spec_st := state1 spec_st) (spec__clk := state__clk spec_st); eauto.
      }

      assert (s0 RegClk = s).
      { destruct spec_invariant0. destruct spec_wf0.
        destruct Hspec0. destruct spec_wf0; simpl in *.
        eapply sim_step__clk with (impl_st := impl_st) (spec__clk := state__clk spec_st); eauto.
      }
      propositional. split.
      - constructor; auto. constructor; auto.
      - destruct i; auto.
    Qed.


    Lemma secure_helper':
       forall (n: nat) (impl_st: state_t) (spec_st: spec_st_t),
         Sim impl_st spec_st ->
         match impl_step_n' n impl_st,
               spec_step_n' spec_f0 spec_f1 spec_f__clk n spec_st with
         | Success (impl_st', impl_tr), Success (spec_st', spec_tr) =>
             Sim impl_st' spec_st' /\ impl_tr = spec_tr
         | _, _ => False
         end.
    Proof.
      induction n; simpl; auto.
      intros * HSim.
      specialize simulation_preserved__step with (1 := HSim).
      intros * Hstep. consider impl_step. consider _spec_step.
      bash_destruct Hstep; propositional.
      specialize IHn with (1 := Hstep0).
      bash_destruct IHn. propositional.
    Qed.

    Lemma secure_helper:
       forall (n: nat) (impl_init: state_t)
         (pf: valid_impl_state impl_init),
         match impl_step_n n impl_init,
               spec_step_n spec_f0 spec_f1 spec_f__clk n (impl_st_to_spec_st impl_init pf) with
         | Success impl, Success spec => impl = spec
         | _, _ => False
         end.
    Proof.
      intros.
      specialize secure_helper' with (1 := InitialSim impl_init pf) (n := n). intros.
      unfold impl_step_n, step_n, impl_step_n' in *. unfold spec_step_n.
      destruct_all_matches; propositional.
    Qed.

    Theorem secure:
      exists (spec_clk_t: Type)
        (local_st0: Type)
        (local_st1: Type)
        (f0: local_st0 -> spec_clk_t -> result (local_st0 * tau0) unit)
        (f1: local_st1 -> spec_clk_t -> result (local_st1 * tau1) unit)
        (f__clk: spec_clk_t -> result spec_clk_t unit),
        forall (n: nat) (impl_init: state_t) (pf: valid_impl_state impl_init),
        exists (init_clk: spec_clk_t)
          (init_st0: local_st0)
          (init_st1: local_st1),
          match impl_step_n n impl_init,
                spec_step_n f0 f1 f__clk n {| state0 := init_st0;
                                            state1 := init_st1;
                                            state__clk := init_clk |} with
          | Success impl_tr, Success spec_tr => impl_tr = spec_tr
          | _, _ => False
          end.
     Proof.
       exists (option (list bool)).
       exists spec_local_st.
       exists spec_local_st.
       exists spec_f0.
       exists spec_f1.
       exists spec_f__clk.
       intros. eexists. eexists. eexists.
       eapply secure_helper.
       Unshelve. assumption.
     Qed.

End Examples.
