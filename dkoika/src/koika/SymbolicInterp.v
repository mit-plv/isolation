Require Import koika.Common.
Require Import koika.Syntax.
Require Import koika.SyntaxUtils.
Require Import koika.Symbolic.
Require Import koika.SemanticUtils.
Require Import koika.Environments.
Require Import koika.Semantics.
Require Import koika.AnnotatedSyntax.
Require Import koika.Tactics.
Require Import koika.Bits.
Require Import koika.Utils.

Require Import FunctionalExtensionality.
Definition preprocess_rule
  (typecheck_fn: @action debug_id_ty -> result (@aaction debug_id_ty * nat) unit) (rl: action) : aaction :=
  match typecheck_fn rl with
  | Success (a, _) => a
  | _ => AnnotAction (Fail 0) []
  end.

Definition preprocess_schedule {rule_name_t : Type}
  (typecheck_fn: @action debug_id_ty -> result (@aaction debug_id_ty * nat) unit)
  (rule_map: rule_name_t -> action)
  (sched: list (rule_name_t * string)) : list (string * aaction) :=
  (map (fun '(rl, srl)=> (srl, preprocess_rule typecheck_fn (rule_map rl))) sched).

Definition preprocess_schedule_success
  {rule_name_t : Type}
  (typecheck_fn: @action debug_id_ty -> result (@aaction debug_id_ty * nat) unit)
  (rule_map: rule_name_t -> action )
  (sched: list (rule_name_t * string)) : bool :=
  forallb Datatypes.id ((map (fun '(rl, _) => is_success (typecheck_fn (rule_map rl))) sched)).

Notation reg_t := (@Syntax.reg_t debug_id_ty).
  Definition mk_init_reg (machine_id: machine_id_t) (reg: reg_t) : sval :=
    SInitReg machine_id reg.
  Definition mk_mid_reg (machine_id: machine_id_t) (reg: reg_t) : sval :=
    SMidReg machine_id reg.

  Definition mk_final_reg (machine_id: machine_id_t) (reg: reg_t) : sval :=
    SFinalReg machine_id reg.
  Definition mk_get_field (machine_id: machine_id_t) (sname fname: debug_id_ty) (v: sval) :=
    SGetField machine_id sname fname v.

  Definition mk_mid_ext (machine_id: machine_id_t) fn : sval :=
    SMidExtLog machine_id fn.
  Definition mk_final_ext (machine_id: machine_id_t) fn : sval :=
    SFinalExtLog machine_id fn.
  Definition mk_committed_ext (machine_id: machine_id_t) fn : sval :=
    SCommittedExtLog machine_id fn.

Definition impl_init := mk_init_reg MachineImpl.
Definition impl_mid := mk_mid_reg MachineImpl.
Definition impl_final := mk_final_reg MachineImpl.
Definition impl_get_field := mk_get_field MachineImpl.
Definition impl_mid_ext := mk_mid_ext MachineImpl.
Definition impl_final_ext := mk_final_ext MachineImpl.
Definition impl_committed_ext := mk_committed_ext MachineImpl.
Definition impl_ext_app := SExtCallApp MachineImpl.

Definition spec_init := mk_init_reg MachineSpec.
Definition spec_mid := mk_mid_reg MachineSpec.
Definition spec_final := mk_final_reg MachineSpec.
Definition spec_get_field := mk_get_field MachineSpec.
Definition spec_ext_app := SExtCallApp MachineSpec.
Definition spec_final_ext := mk_final_ext MachineSpec.
Definition spec_committed_ext := mk_committed_ext MachineSpec.

Lemma interp_scheduler_list_equiv':
  forall {rule_name_t: Type} sigma int_fns struct_env (rules: rule_name_t -> rule) schedule st sched_log log,
  interp_scheduler' sigma int_fns struct_env st rules schedule sched_log = Success log ->
  interp_scheduler_list' sigma int_fns struct_env st
    (map rules (list_of_schedule schedule)) sched_log = Success log.
Proof.
  induction schedule; simpl; auto.
  intros. bash_destruct H; eauto.
Qed.

Lemma interp_scheduler_list_equiv:
  forall {rule_name_t: Type} sigma int_fns struct_env (rules: rule_name_t -> rule) schedule st log,
  interp_scheduler sigma int_fns struct_env st
    rules schedule = Success log ->
  interp_cycle_list' sigma int_fns struct_env st
    (map rules  (list_of_schedule schedule)) =
    Success (commit_update st (Log__koika log), Log__ext log).
Proof.
  unfold interp_scheduler. unfold interp_cycle_list'. unfold interp_scheduler_list.
  intros.
  apply interp_scheduler_list_equiv' in H.
  rewrite H. reflexivity.
Qed.



Definition strip_dbg_struct_inv := id_transform_struct_env _id.
Definition strip_dbg_sched_list (sched: list (string * @action debug_id_ty)) :=
  map (fun '(_, rl) => id_transform_action _id rl) sched.
Definition strip_dbg_ext_types := id_transform_ext_fn_types _id.
Definition strip_dbg_reg_types := id_transform_reg_types _id.

Definition strip_annots_schedule (sched: list (string * @aaction debug_id_ty)) :=
  map (fun '(name,rl) => (name, strip_annots rl)) sched.

Definition machine_to_prop (machine: Symbolic.machine_t) (schedule: list (string * aaction)) (sigma: ext_sigma_t) (st st' : state_t) (ext_log': ext_log_t) : Prop :=
  WF_ext_sigma (strip_dbg_ext_types machine.(file_ext_sigma)) sigma /\
  WF_state (strip_dbg_reg_types machine.(file_registers)) st /\
  interp_cycle_list' sigma [] (strip_dbg_struct_inv machine.(file_struct_defs)) st
    (strip_dbg_sched_list (map (fun '(name,rl) => (name, strip_annots rl)) schedule))
    = Success (st', ext_log').

  (* oraat_interp_scheduler_list sigma [] *)
  (*   (strip_dbg_struct_inv machine.(file_struct_defs)) st *)
  (*   (strip_dbg_sched_list (map (fun '(name,rl) => (name, strip_annots rl)) schedule)) = (true, st', ext_log'). *)
Record machine_pkg :=
  { pkg_machine: Symbolic.machine_t;
    pkg_init_st: state_t;
    pkg_sigma: @ext_sigma_t N;
    pkg_mid_st : option state_t;
    pkg_final_st: state_t;
    pkg_mid_ext_log: option ext_log_t;
    pkg_ext_log': ext_log_t
  }.
Definition choose_pkg (id: machine_id_t) (impl_pkg spec_pkg: machine_pkg) : machine_pkg :=
  match id with
  | MachineImpl => impl_pkg
  | MachineSpec => spec_pkg
  end.

Fixpoint sval_uses_mid_only (mid: machine_id_t) (v: sval) : bool :=
  let sval_uses_mid_only := sval_uses_mid_only mid in
  match v with
  | SConst _ => true
  | SInitReg machine _ => beq_dec machine mid
  | SMidReg machine _ => beq_dec machine mid
  | SFinalReg machine _ => beq_dec machine mid
  | SMidExtLog machine _ => beq_dec machine mid
  | SFinalExtLog machine _ => beq_dec machine mid
  | SCommittedExtLog machine _ => beq_dec machine mid
  | SBits1 fn1 v => sval_uses_mid_only v
  | SBits2 fn2 v1 v2 => sval_uses_mid_only v1 && sval_uses_mid_only v2
  | SGetField machine sname fname v => sval_uses_mid_only v && beq_dec machine mid
  | SExtCallApp machine extfn v => sval_uses_mid_only v && beq_dec machine mid
  | SBound arg => true
  end.

Fixpoint spred_uses_mid_only (mid: machine_id_t) (p: spred) : bool :=
  let spred_uses_mid_only := spred_uses_mid_only mid in
  match p with
  | PConst _ => true
  | PAnd b1 b2 => spred_uses_mid_only b1 && spred_uses_mid_only b2
  | POr b1 b2 => spred_uses_mid_only b1 && spred_uses_mid_only b2
  | PNot b => spred_uses_mid_only b
  | PImpl p1 p2 => spred_uses_mid_only p1 && spred_uses_mid_only p2
  | PEq v1 v2 => sval_uses_mid_only mid v1 && sval_uses_mid_only mid v2
  | PNEq v1 v2 => sval_uses_mid_only mid v1 && sval_uses_mid_only mid v2
  | PForallArg1 arg body => spred_uses_mid_only body
  | PForallArg2 arg1 arg2 body => spred_uses_mid_only body
  | PExtFnEq fn => false
  | PFancy p => fancy_spred_uses_mid_only mid p
  end with
  fancy_spred_uses_mid_only (mid: machine_id_t)
                            (p: fancy_spred)
                            : bool :=
    match p with
    | PBase e => spred_uses_mid_only mid e
    | PForallRegs fn regs => forallb (fun reg => fancy_spred_uses_mid_only mid (fn reg)) regs
    | PForallRegs2 fn regs => forallb (fun reg => fancy_spred_uses_mid_only mid (fn reg)) regs
    end.

Fixpoint replace_sval_base (f: sval -> sval) (v: sval) : sval :=
  match v with
  | SConst _ => v
  | SInitReg _ _ => f v
  | SMidReg _ _ => f v
  | SFinalReg _ _ => f v
  | SMidExtLog _ _ => f v
  | SFinalExtLog _ _ => f v
  | SCommittedExtLog _ _ => f v
  | SBits1 fn v => SBits1 fn (replace_sval_base f v)
  | SBits2 fn2 v1 v2 => SBits2 fn2 (replace_sval_base f v1) (replace_sval_base f v2)
  | SGetField machine sname fname v =>
      SGetField machine sname fname (replace_sval_base f v)
  | SExtCallApp mid extfn v =>
      SExtCallApp mid extfn (replace_sval_base f v)
  | SBound arg => SBound arg
  end.

Fixpoint replace_sval_in_spred_base (f: sval -> sval) (p: spred) : spred :=
 let replace_sval_in_spred_base  := replace_sval_in_spred_base f in
  match p with
  | PConst cst => PConst cst
  | PAnd b1 b2 =>
      PAnd (replace_sval_in_spred_base b1) (replace_sval_in_spred_base b2)
  | POr b1 b2 =>
      POr (replace_sval_in_spred_base b1) (replace_sval_in_spred_base b2)
  | PNot b =>
      PNot (replace_sval_in_spred_base b)
  | PImpl p1 p2 =>
      PImpl (replace_sval_in_spred_base p1)
            (replace_sval_in_spred_base p2)
  | PEq v1 v2 =>
      PEq (replace_sval_base f v1)
          (replace_sval_base f v2)
  | PNEq v1 v2 =>
      PNEq (replace_sval_base f v1)
           (replace_sval_base f v2)
  | PForallArg1 arg body =>
      PForallArg1 arg (replace_sval_in_spred_base body)
  | PForallArg2 arg1 arg2 body =>
      PForallArg2 arg1 arg2 (replace_sval_in_spred_base body)
  | PExtFnEq fn =>
      PExtFnEq fn
  | PFancy p =>
      PFancy (replace_sval_in_fancy_spred_base f p)
  end with
  replace_sval_in_fancy_spred_base  (f: sval -> sval) (p: fancy_spred)
                            : fancy_spred :=
    match p with
    | PBase e => PBase (replace_sval_in_spred_base f e)
    | PForallRegs fn regs =>
        PForallRegs (fun id => replace_sval_in_fancy_spred_base f (fn id)) regs
    | PForallRegs2 fn regs =>
        PForallRegs2 (fun id => replace_sval_in_fancy_spred_base f (fn id)) regs
    end.

Definition fn_replace_final_reg_with_init (v: sval) : sval :=
  match v with
  | SFinalReg machine reg => SInitReg machine reg
  | _ => v
  end.
Definition fn_replace_impl_final_reg_with_init (v: sval) : sval :=
  match v with
  | SFinalReg MachineImpl reg => SInitReg MachineImpl reg
  | _ => v
  end.
Definition fn_replace_spec_final_reg_with_init (v: sval) : sval :=
  match v with
  | SFinalReg MachineSpecg reg => SInitReg MachineImpl reg
  | _ => v
  end.

Definition fn_replace_init_reg_with_final (v: sval) : sval :=
  match v with
  | SInitReg machine reg => SFinalReg machine reg
  | _ => v
  end.
Definition fn_replace_impl_init_reg_with_final (v: sval) : sval :=
  match v with
  | SInitReg MachineImpl reg => SFinalReg MachineImpl reg
  | _ => v
  end.
Definition fn_replace_spec_init_reg_with_final (v: sval) : sval :=
  match v with
  | SInitReg MachineSpec reg => SFinalReg MachineSpec reg
  | _ => v
  end.

Definition fn_replace_init_reg_with_mid (v: sval) : sval :=
  match v with
  | SInitReg machine reg => SMidReg machine reg
  | _ => v
  end.
Definition fn_replace_impl_init_reg_with_mid (v: sval) : sval :=
  match v with
  | SInitReg MachineImpl reg => SMidReg MachineImpl reg
  | _ => v
  end.
Definition fn_replace_spec_init_reg_with_mid (v: sval) : sval :=
  match v with
  | SInitReg MachineSpec reg => SMidReg MachineSpec reg
  | _ => v
  end.

Definition fn_replace_mid_reg_with_final (v: sval) : sval :=
  match v with
  | SMidReg machine reg => SFinalReg machine reg
  | _ => v
  end.
Definition fn_replace_impl_mid_reg_with_final (v: sval) : sval :=
  match v with
  | SMidReg MachineImpl reg => SFinalReg MachineImpl reg
  | _ => v
  end.
Definition fn_replace_spec_mid_reg_with_final (v: sval) : sval :=
  match v with
  | SMidReg MachineSpec reg => SFinalReg MachineSpec reg
  | _ => v
  end.


Definition fn_replace_mid_ext_with_final (v: sval) : sval :=
  match v with
  | SMidExtLog machine reg => SFinalExtLog machine reg
  | _ => v
  end.

Definition fn_replace_final_ext_with_committed (v: sval) : sval :=
  match v with
  | SFinalExtLog  machine reg => SCommittedExtLog machine reg
  | _ => v
  end.
Definition fn_replace_impl_final_ext_with_committed (v: sval) : sval :=
  match v with
  | SFinalExtLog  MachineImpl reg => SCommittedExtLog MachineImpl reg
  | _ => v
  end.
Definition fn_replace_spec_final_ext_with_committed (v: sval) : sval :=
  match v with
  | SFinalExtLog  MachineSpec reg => SCommittedExtLog MachineSpec reg
  | _ => v
  end.



(* Definition replace_sval_final_reg_with_init (v: sval) : sval := *)
(*   replace_sval_base fn_replace_final_reg_with_init v. *)
Definition replace_sval_final_reg_with_init (p: sval) : sval :=
  replace_sval_base fn_replace_final_reg_with_init p.
Definition replace_spred_final_reg_with_init (p: spred) : spred :=
  replace_sval_in_spred_base fn_replace_final_reg_with_init p.
Definition replace_fancy_spred_final_reg_with_init (p: fancy_spred) : fancy_spred :=
  replace_sval_in_fancy_spred_base fn_replace_final_reg_with_init p.

Definition replace_sval_init_reg_with_final (p: sval) : sval :=
  replace_sval_base fn_replace_init_reg_with_final p.
Definition replace_spred_init_reg_with_final (p: spred) : spred :=
  replace_sval_in_spred_base fn_replace_init_reg_with_final p.
Definition replace_fancy_spred_init_reg_with_final (p: fancy_spred) : fancy_spred :=
  replace_sval_in_fancy_spred_base fn_replace_init_reg_with_final p.

Definition replace_sval_init_reg_with_mid (p: sval) : sval :=
  replace_sval_base fn_replace_init_reg_with_mid p.
Definition replace_spred_init_reg_with_mid (p: spred) : spred :=
  replace_sval_in_spred_base fn_replace_init_reg_with_mid p.
Definition replace_fancy_spred_init_reg_with_mid (p: fancy_spred) : fancy_spred :=
  replace_sval_in_fancy_spred_base fn_replace_init_reg_with_mid p.

Definition replace_sval_mid_reg_with_final (p: sval) : sval :=
  replace_sval_base fn_replace_mid_reg_with_final p.
Definition replace_spred_mid_reg_with_final (p: spred) : spred :=
  replace_sval_in_spred_base fn_replace_mid_reg_with_final p.
Definition replace_fancy_spred_mid_reg_with_final (p: fancy_spred) : fancy_spred :=
  replace_sval_in_fancy_spred_base fn_replace_mid_reg_with_final p.

Definition replace_sval_mid_ext_with_final (p: sval) : sval :=
  replace_sval_base fn_replace_mid_ext_with_final p.
Definition replace_spred_mid_ext_with_final (p: spred) : spred :=
  replace_sval_in_spred_base fn_replace_mid_ext_with_final p.
Definition replace_fancy_spred_mid_ext_with_final (p: fancy_spred) : fancy_spred :=
  replace_sval_in_fancy_spred_base fn_replace_mid_ext_with_final p.
Definition replace_sval_final_ext_with_committed (p: sval) : sval :=
  replace_sval_base fn_replace_final_ext_with_committed p.
Definition replace_spred_final_ext_with_committed (p: spred) : spred :=
  replace_sval_in_spred_base fn_replace_final_ext_with_committed p.
Definition replace_fancy_spred_final_ext_with_committed (p: fancy_spred) : fancy_spred :=
  replace_sval_in_fancy_spred_base fn_replace_final_ext_with_committed p.

Fixpoint normalize_mid_sval (v: sval) : sval :=
  match v with
  | SConst b => SConst b
  | SInitReg _ reg => SInitReg MachineImpl reg
  | SMidReg _ reg => SMidReg MachineImpl reg
  | SFinalReg _ reg =>
      SFinalReg MachineImpl reg
  | SMidExtLog _ fn =>
      SMidExtLog MachineImpl fn
  | SFinalExtLog _ fn =>
      SFinalExtLog MachineImpl fn
  | SCommittedExtLog _ fn => SCommittedExtLog MachineImpl fn
  | SBits1 fn1 v =>
      SBits1 fn1 (normalize_mid_sval v)
  | SBits2 fn2 v1 v2 =>
      SBits2 fn2 (normalize_mid_sval v1) (normalize_mid_sval v2)
  | SGetField _ sname fname v =>
      SGetField MachineImpl sname fname (normalize_mid_sval v)
  | SExtCallApp _ extfn v =>
      SExtCallApp MachineImpl extfn (normalize_mid_sval v)
  | SBound arg => SBound arg
  end.

Fixpoint normalize_mid_spred (p: spred) : spred :=
  match p with
  | PConst b => PConst b
  | PAnd b1 b2 => PAnd (normalize_mid_spred b1) (normalize_mid_spred b2)
  | POr b1 b2 => POr (normalize_mid_spred b1) (normalize_mid_spred b2)
  | PNot b => PNot (normalize_mid_spred b)
  | PImpl p1 p2 => PImpl (normalize_mid_spred p1) (normalize_mid_spred p2)
  | PEq v1 v2 => PEq (normalize_mid_sval v1) (normalize_mid_sval v2)
  | PNEq v1 v2 => PNEq (normalize_mid_sval v1) (normalize_mid_sval v2)
  | PForallArg1 arg body => PForallArg1 arg (normalize_mid_spred body)
  | PForallArg2 arg1 arg2 body => PForallArg2 arg1 arg2 (normalize_mid_spred body)
  | PExtFnEq fn => PExtFnEq fn
  | PFancy p => PFancy (normalize_mid_fancy_spred p)
  end with
  normalize_mid_fancy_spred (p: fancy_spred) : fancy_spred :=
    match p with
    | PBase e => PBase (normalize_mid_spred e)
    | PForallRegs fn regs => PForallRegs (fun x => normalize_mid_fancy_spred (fn x)) regs
    | PForallRegs2 fn regs => PForallRegs2 (fun x => normalize_mid_fancy_spred (fn x)) regs
    end.

Fixpoint sval_equiv (v1 v2: sval) : bool :=
  match v1, v2 with
  | SConst bs1, SConst bs2 => beq_dec bs1 bs2
  | SInitReg _ reg1, SInitReg _ reg2 =>
      beq_dec reg1 reg2
  | SMidReg _ reg1, SMidReg _ reg2 =>
      beq_dec reg1 reg2
  | SFinalReg _ reg1, SFinalReg _ reg2 =>
      beq_dec reg1 reg2
  | SMidExtLog _ fn1, SMidExtLog _ fn2 =>
      beq_dec fn1 fn2
  | SFinalExtLog _ fn1, SFinalExtLog _ fn2 =>
      beq_dec fn1 fn2
  | SCommittedExtLog _ fn1, SCommittedExtLog _ fn2 =>
      beq_dec fn1 fn2
  | SBits1 fn1 v1, SBits1 fn2 v2 =>
      beq_dec fn1 fn2 && sval_equiv v1 v2
  | SBits2 fn1 v1 v1', SBits2 fn2 v2 v2'=>
      beq_dec fn1 fn2 && sval_equiv v1 v2 && sval_equiv v1' v2'
  | SGetField _ sname1 fname1 v1, SGetField _ sname2 fname2 v2 =>
      beq_dec sname1 sname2 && beq_dec fname1 fname2 && sval_equiv v1 v2
  | SExtCallApp _ extfn1 v1, SExtCallApp _ extfn2 v2 =>
      beq_dec extfn1 extfn2 && sval_equiv v1 v2
  | SBound arg1, SBound arg2 =>
      beq_dec arg1 arg2
  | _, _ => false
  end.
Fixpoint spred_equiv (p1 p2: spred) : bool :=
  match p1, p2 with
  | PConst true, PConst true => true
  | PConst false, PConst false => true
  | PAnd b1 b2, PAnd c1 c2 =>
      spred_equiv b1 c1 && spred_equiv b2 c2
  | POr b1 b2, POr c1 c2 =>
      spred_equiv b1 c1 && spred_equiv b2 c2
  | PNot b1, PNot c1 => spred_equiv b1 c1
  | PImpl b1 b2, PImpl c1 c2 =>
      spred_equiv b1 c1 && spred_equiv b2 c2
  | PEq v1 v2, PEq x1 x2 =>
      sval_equiv v1 x1 && sval_equiv v2 x2
  | PNEq v1 v2, PNEq x1 x2 =>
      sval_equiv v1 x1 && sval_equiv v2 x2
  | PForallArg1 arg1 body1, PForallArg1 arg2 body2 =>
      beq_dec arg1 arg2 && spred_equiv body1 body2
  | PForallArg2 arg1 arg1' body1, PForallArg2 arg2 arg2' body2 =>
      beq_dec arg1 arg2 && beq_dec arg1' arg2' && spred_equiv body1 body2
  | PExtFnEq fn1, PExtFnEq fn2 =>
      beq_dec fn1 fn2
  | PFancy p1, PFancy p2 =>
      fancy_spred_equiv p1 p2
  | _, _ => false
  end with
  fancy_spred_equiv (p1 p2: fancy_spred)
                    : bool :=
    match p1, p2 with
    | PBase e1, PBase e2 => spred_equiv e1 e2
    | PForallRegs fn1 regs1, PForallRegs fn2 regs2 =>
        beq_dec regs1 regs2  &&
        forallb (fun reg => fancy_spred_equiv (fn1 reg) (fn2 reg)) regs1
    | PForallRegs2 fn1 regs1, PForallRegs2 fn2 regs2 =>
        beq_dec regs1 regs2  &&
        forallb (fun reg => fancy_spred_equiv (fn1 reg) (fn2 reg)) regs1
    | _, _ => false
    end.

Section ListShenanigans.
      Context (unfancy: forall (p : fancy_spred) , spred).
      Context {x:Type}.
      Context (f : x -> fancy_spred).

      Fixpoint unfancy_and_list' (l : list x) :=
                match l with
                | nil => PConst true
                | t :: q => PAnd (unfancy (f t)) (unfancy_and_list' q)
                end.
    Arguments unfancy_and_list' l /. (* The list needs to be in [a,b,c] ... form for this to work *)

    Fixpoint unfancy_e (s : spred) : spred :=
      match s with
      | PConst b => PConst b
      | PAnd p1 p2 => PAnd (unfancy_e p1) (unfancy_e p2)
      | POr p1 p2 => POr (unfancy_e p1) (unfancy_e p2)
      | PNot p => PNot (unfancy_e p)
      | PImpl p1 p2 => PImpl (unfancy_e p1) (unfancy_e p2)
      | PEq v1 v2 => PEq v1 v2
      | PNEq v1 v2 => PNEq v1 v2
      | PForallArg1 arg body => PForallArg1 arg (unfancy_e body)
      | PForallArg2 arg1 arg2 body => PForallArg2 arg1 arg2 (unfancy_e body)
      | PExtFnEq fn => PExtFnEq fn
      | PFancy f => unfancy f
      end.
End ListShenanigans.

Fixpoint flatten_spred_ands (s: spred) :=
  match s with
  | PAnd p1 p2 => flatten_spred_ands p1 ++ flatten_spred_ands p2
  | _ => [s]
  end.

Fixpoint unfancy (sp: fancy_spred) : spred :=
  match sp with
  | PBase base => unfancy_e unfancy base
  | PForallRegs fn regs => unfancy_and_list' unfancy fn regs
  | PForallRegs2 fn regs => unfancy_and_list' unfancy fn regs
  end.
Definition preprocess_fancy_spreds {A} (spreds : list ( A * fancy_spred)) : list spred :=
  List.concat (map (fun '(_, p) => (flatten_spred_ands (unfancy p))) spreds).
Section Taint.
Record se_taint_t' :=
{ se_machine: bool;
  se_init_st: bool;
  se_sigma: bool;
  se_mid_st: bool;
  se_final_st: bool;
  se_mid_ext_log: bool;
  se_ext_log': bool;
  se_committed: bool;
}.
Definition empty_se_taint_t': se_taint_t' :=
  {| se_machine := false;
     se_init_st := false;
     se_sigma := false;
     se_mid_st := false;
     se_final_st := false;
     se_mid_ext_log := false;
     se_ext_log' := false;
     se_committed := false;
  |}.

Record se_taint_t :=
  { se_taint_i : se_taint_t';
    se_taint_s : se_taint_t'
  }.

Definition empty_se_taint_t: se_taint_t :=
  {| se_taint_i := empty_se_taint_t';
     se_taint_s := empty_se_taint_t'
  |}.


Definition taint_set_sigma (t: se_taint_t') : se_taint_t' :=
  {| se_machine := t.(se_machine); se_init_st := t.(se_init_st);
     se_sigma := true; se_mid_st := t.(se_mid_st);
     se_final_st := t.(se_final_st ); se_mid_ext_log := t.(se_mid_ext_log);
     se_ext_log' := t.(se_ext_log'); se_committed := t.(se_committed)
  |}.

Definition taint_set_machine (t: se_taint_t') : se_taint_t' :=
  {| se_machine := true; se_init_st := t.(se_init_st);
     se_sigma := t.(se_sigma ); se_mid_st := t.(se_mid_st);
     se_final_st := t.(se_final_st ); se_mid_ext_log := t.(se_mid_ext_log);
     se_ext_log' := t.(se_ext_log'); se_committed := t.(se_committed)
  |}.

Definition taint_set_init(t: se_taint_t') : se_taint_t' :=
  {| se_machine := t.(se_machine); se_init_st := true;
     se_sigma := t.(se_sigma ); se_mid_st := t.(se_mid_st);
     se_final_st := t.(se_final_st ); se_mid_ext_log := t.(se_mid_ext_log);
     se_ext_log' := t.(se_ext_log'); se_committed := t.(se_committed)
  |}.

Definition taint_set_mid(t: se_taint_t') : se_taint_t' :=
  {| se_machine := t.(se_machine); se_init_st := t.(se_init_st);
     se_sigma := t.(se_sigma ); se_mid_st := true;
     se_final_st := t.(se_final_st ); se_mid_ext_log := t.(se_mid_ext_log);
     se_ext_log' := t.(se_ext_log'); se_committed := t.(se_committed)
  |}.

Definition taint_set_final(t: se_taint_t') : se_taint_t' :=
  {| se_machine := t.(se_machine); se_init_st := t.(se_init_st);
     se_sigma := t.(se_sigma ); se_mid_st := t.(se_mid_st);
     se_final_st := true; se_mid_ext_log := t.(se_mid_ext_log);
     se_ext_log' := t.(se_ext_log'); se_committed := t.(se_committed)
  |}.

Definition taint_set_mid_ext(t: se_taint_t') : se_taint_t' :=
  {| se_machine := t.(se_machine); se_init_st := t.(se_init_st);
     se_sigma := t.(se_sigma ); se_mid_st := t.(se_mid_st);
     se_final_st := t.(se_final_st ); se_mid_ext_log := true;
     se_ext_log' := t.(se_ext_log'); se_committed := t.(se_committed)
  |}.

Definition taint_set_ext'(t: se_taint_t') : se_taint_t' :=
  {| se_machine := t.(se_machine); se_init_st := t.(se_init_st);
     se_sigma := t.(se_sigma ); se_mid_st := t.(se_mid_st);
     se_final_st := t.(se_final_st ); se_mid_ext_log := t.(se_mid_ext_log);
     se_ext_log' := true; se_committed := t.(se_committed)
  |}.

Definition taint_set_committed (t: se_taint_t') : se_taint_t' :=
  {| se_machine := t.(se_machine); se_init_st := t.(se_init_st);
     se_sigma := t.(se_sigma ); se_mid_st := t.(se_mid_st);
     se_final_st := t.(se_final_st ); se_mid_ext_log := t.(se_mid_ext_log);
     se_ext_log' := t.(se_ext_log'); se_committed := true
  |}.

Fixpoint compute_sval_taint' (t : se_taint_t) (v: sval) : se_taint_t :=
  match v with
  | SConst _ => t
  | SInitReg MachineImpl _ =>
      {| se_taint_i := taint_set_init t.(se_taint_i);
         se_taint_s := t.(se_taint_s);
      |}
  | SInitReg MachineSpec _ =>
      {| se_taint_i := t.(se_taint_i);
         se_taint_s := taint_set_init t.(se_taint_s);
      |}
  | SMidReg MachineImpl _ =>
      {| se_taint_i := taint_set_mid t.(se_taint_i);
         se_taint_s := t.(se_taint_s);
      |}
  | SMidReg MachineSpec _ =>
      {| se_taint_i := t.(se_taint_i);
         se_taint_s := taint_set_mid t.(se_taint_s);
      |}
  | SFinalReg MachineImpl _ =>
      {| se_taint_i := taint_set_final t.(se_taint_i);
         se_taint_s := t.(se_taint_s);
      |}
  | SFinalReg MachineSpec _ =>
      {| se_taint_i := t.(se_taint_i);
         se_taint_s := taint_set_final t.(se_taint_s);
      |}
  | SMidExtLog MachineImpl fn =>
      {| se_taint_i := taint_set_mid_ext t.(se_taint_i);
         se_taint_s := t.(se_taint_s);
      |}
  | SMidExtLog MachineSpec fn =>
      {| se_taint_i := t.(se_taint_i);
         se_taint_s := taint_set_mid_ext t.(se_taint_s);
      |}
  | SFinalExtLog MachineImpl fn =>
      {| se_taint_i := taint_set_ext' t.(se_taint_i);
         se_taint_s := t.(se_taint_s);
      |}
  | SFinalExtLog MachineSpec fn =>
      {| se_taint_i := t.(se_taint_i);
         se_taint_s := taint_set_ext' t.(se_taint_s);
      |}
  | SCommittedExtLog MachineImpl fn =>
      {| se_taint_i := taint_set_committed t.(se_taint_i);
         se_taint_s := t.(se_taint_s);
      |}
  | SCommittedExtLog MachineSpec fn =>
      {| se_taint_i := t.(se_taint_i);
         se_taint_s := taint_set_committed t.(se_taint_s);
      |}
  | SBits1 _ v => compute_sval_taint' t v
  | SBits2 _ v1 v2 => compute_sval_taint' (compute_sval_taint' t v1) v2
  | SGetField mid _ _ v =>
      let t := compute_sval_taint' t v in
      match mid with
      | MachineImpl =>
        {| se_taint_i := taint_set_machine t.(se_taint_i);
           se_taint_s := t.(se_taint_s);
        |}
      | MachineSpec =>
        {| se_taint_i := t.(se_taint_i);
           se_taint_s := taint_set_machine t.(se_taint_s);
        |}
      end
  | SExtCallApp mid _ v =>
      let t := compute_sval_taint' t v in
      match mid with
      | MachineImpl =>
        {| se_taint_i := taint_set_sigma t.(se_taint_i);
           se_taint_s := t.(se_taint_s);
        |}
      | MachineSpec =>
        {| se_taint_i := t.(se_taint_i);
           se_taint_s := taint_set_sigma t.(se_taint_s);
        |}
      end
  | SBound _ => t
  end.

Fixpoint compute_spred_taint' (t: se_taint_t) (p: spred) : se_taint_t :=
  match p with
  | PConst _ =>t
  | PAnd b1 b2 => compute_spred_taint' (compute_spred_taint' t b1) b2
  | POr b1 b2 => compute_spred_taint' (compute_spred_taint' t b1) b2
  | PNot b => compute_spred_taint' t b
  | PImpl p1 p2 => compute_spred_taint' (compute_spred_taint' t p1) p2
  | PEq v1 v2 => compute_sval_taint' (compute_sval_taint' t v1) v2
  | PNEq v1 v2 => compute_sval_taint' (compute_sval_taint' t v1) v2
  | PForallArg1 _ body => compute_spred_taint' t body
  | PForallArg2 _ _ body => compute_spred_taint' t body
  | PExtFnEq _ =>
      {| se_taint_i := taint_set_sigma t.(se_taint_i);
         se_taint_s := taint_set_sigma t.(se_taint_s);
      |}
  | PFancy p =>
      compute_fancy_spred_taint' t p
  end with
  compute_fancy_spred_taint' (t: se_taint_t) (p: fancy_spred) : se_taint_t :=
    match p with
    | PBase e => compute_spred_taint' t e
    | PForallRegs fn regs =>
        fold_left (fun acc r => compute_fancy_spred_taint' acc (fn r) ) regs t
    | PForallRegs2 fn regs =>
        fold_left (fun acc r => compute_fancy_spred_taint' acc (fn r) ) regs t
    end.
Definition compute_spred_taint (p: spred) : se_taint_t :=
  compute_spred_taint' empty_se_taint_t p.

Definition compute_fancy_spred_taint (p: fancy_spred) : se_taint_t :=
  compute_fancy_spred_taint' empty_se_taint_t p.

Definition compute_spreds_taint (ps: list spred) : se_taint_t :=
  fold_left (fun acc p => compute_spred_taint' acc p)
            ps empty_se_taint_t.

Definition compute_fancy_spreds_taint (ps: list fancy_spred) : se_taint_t :=
  fold_left (fun acc p => compute_fancy_spred_taint' acc p)
            ps empty_se_taint_t.

Definition get_mid_taint (taint: se_taint_t) (mid: machine_id_t) : se_taint_t' :=
  match mid with
  | MachineImpl => taint.(se_taint_i)
  | MachineSpec => taint.(se_taint_s)
  end.

Definition package_equiv_taint' (taint: se_taint_t') pkg1 pkg2 :=
  (pkg1.(pkg_machine).(file_struct_defs) = pkg2.(pkg_machine).(file_struct_defs) \/ taint.(se_machine) = false) /\
  (pkg1.(pkg_init_st) = pkg2.(pkg_init_st) \/ taint.(se_init_st) = false) /\
  (pkg1.(pkg_sigma) = pkg2.(pkg_sigma) \/ taint.(se_sigma) = false) /\
  (pkg1.(pkg_mid_st) = pkg2.(pkg_mid_st) \/ taint.(se_mid_st) = false) /\
  (pkg1.(pkg_final_st) = pkg2.(pkg_final_st) \/ taint.(se_final_st) = false) /\
  (pkg1.(pkg_mid_ext_log) = pkg2.(pkg_mid_ext_log) \/ taint.(se_mid_ext_log) = false) /\
  (pkg1.(pkg_ext_log') = pkg2.(pkg_ext_log') \/ taint.(se_ext_log') = false) /\
  ((ext_log_app pkg1.(pkg_ext_log') (match pkg1.(pkg_mid_ext_log) with
                                     | Some log => log
                                     | None => SortedExtFnEnv.empty
                                     end) =
    ext_log_app pkg2.(pkg_ext_log') (match pkg2.(pkg_mid_ext_log) with
                                     | Some log => log
                                     | None => SortedExtFnEnv.empty
                                     end)) \/ taint.(se_committed) = false).


Definition package_equiv_taint (taint: se_taint_t) impl1 impl2 spec1 spec2 :=
  package_equiv_taint' (get_mid_taint taint MachineImpl) impl1 impl2 /\
  package_equiv_taint' (get_mid_taint taint MachineSpec) spec1 spec2.

Lemma package_equiv_taint_set_init:
  forall pkg1 pkg2 taint_base,
  package_equiv_taint' (taint_set_init taint_base) pkg1 pkg2 ->
  package_equiv_taint' taint_base pkg1 pkg2.
Proof.
  intros; consider package_equiv_taint'; unfold taint_set_init; simpl in *; propositional; split_ands_in_goal; auto; simplify_ors; auto.
Qed.

Lemma package_equiv_taint_set_mid:
  forall pkg1 pkg2 taint_base,
  package_equiv_taint' (taint_set_mid taint_base) pkg1 pkg2 ->
  package_equiv_taint' taint_base pkg1 pkg2.
Proof.
  intros; consider package_equiv_taint'; unfold taint_set_init; simpl in *; propositional; split_ands_in_goal; auto; simplify_ors; auto.
Qed.
Lemma package_equiv_taint_set_final:
  forall pkg1 pkg2 taint_base,
  package_equiv_taint' (taint_set_final taint_base) pkg1 pkg2 ->
  package_equiv_taint' taint_base pkg1 pkg2.
Proof.
  intros; consider package_equiv_taint'; unfold taint_set_init; simpl in *; propositional; split_ands_in_goal; auto; simplify_ors; auto.
Qed.
Lemma package_equiv_taint_set_mid_ext:
  forall pkg1 pkg2 taint_base,
  package_equiv_taint' (taint_set_mid_ext taint_base) pkg1 pkg2 ->
  package_equiv_taint' taint_base pkg1 pkg2.
Proof.
  intros; consider package_equiv_taint'; unfold taint_set_init; simpl in *; propositional; split_ands_in_goal; auto; simplify_ors; auto.
Qed.
Lemma package_equiv_taint_set_ext':
  forall pkg1 pkg2 taint_base,
  package_equiv_taint' (taint_set_ext' taint_base) pkg1 pkg2 ->
  package_equiv_taint' taint_base pkg1 pkg2.
Proof.
  intros; consider package_equiv_taint'; unfold taint_set_init; simpl in *; propositional; split_ands_in_goal; auto; simplify_ors; auto.
Qed.
Lemma package_equiv_taint_set_committed:
  forall pkg1 pkg2 taint_base,
  package_equiv_taint' (taint_set_committed taint_base) pkg1 pkg2 ->
  package_equiv_taint' taint_base pkg1 pkg2.
Proof.
  intros; consider package_equiv_taint'; unfold taint_set_init; simpl in *; propositional; split_ands_in_goal; auto; simplify_ors; auto.
Qed.

Lemma package_equiv_taint_set_machine:
  forall pkg1 pkg2 taint_base,
  package_equiv_taint' (taint_set_machine taint_base) pkg1 pkg2 ->
  package_equiv_taint' taint_base pkg1 pkg2.
Proof.
  intros; consider package_equiv_taint'; unfold taint_set_init; simpl in *; propositional; split_ands_in_goal; auto; simplify_ors; auto.
Qed.
Lemma package_equiv_taint_set_sigma:
  forall pkg1 pkg2 taint_base,
  package_equiv_taint' (taint_set_sigma taint_base) pkg1 pkg2 ->
  package_equiv_taint' taint_base pkg1 pkg2.
Proof.
  intros; consider package_equiv_taint'; unfold taint_set_init; simpl in *; propositional; split_ands_in_goal; auto; simplify_ors; auto.
Qed.


Ltac t_package_equiv_base_sval :=
  simpl; try destruct_match; consider package_equiv_taint; propositional; split_ands_in_goal; simpl in *; auto;
  repeat match goal with
  | H: _ \/ true = false |- _ => split_ors_in H; [ | discriminate]
  | H: package_equiv_taint' (taint_set_init ?taint_base) ?pkg1 ?pkg2
    |- package_equiv_taint' ?taint_base ?pkg1 ?pkg2 =>
      apply package_equiv_taint_set_init; auto
  | H: package_equiv_taint' (taint_set_mid ?taint_base) ?pkg1 ?pkg2
    |- package_equiv_taint' ?taint_base ?pkg1 ?pkg2 =>
      apply package_equiv_taint_set_mid; auto
  | H: package_equiv_taint' (taint_set_final ?taint_base) ?pkg1 ?pkg2
    |- package_equiv_taint' ?taint_base ?pkg1 ?pkg2 =>
      apply package_equiv_taint_set_final; auto
  | H: package_equiv_taint' (taint_set_mid_ext ?taint_base) ?pkg1 ?pkg2
    |- package_equiv_taint' ?taint_base ?pkg1 ?pkg2 =>
      apply package_equiv_taint_set_mid_ext; auto
  | H: package_equiv_taint' (taint_set_ext' ?taint_base) ?pkg1 ?pkg2
    |- package_equiv_taint' ?taint_base ?pkg1 ?pkg2 =>
      apply package_equiv_taint_set_ext'; auto
  | H: package_equiv_taint' (taint_set_ext' ?taint_base) ?pkg1 ?pkg2
    |- package_equiv_taint' ?taint_base ?pkg1 ?pkg2 =>
      apply package_equiv_taint_set_ext'; auto
  | H: package_equiv_taint' (taint_set_committed ?taint_base) ?pkg1 ?pkg2
    |- package_equiv_taint' ?taint_base ?pkg1 ?pkg2 =>
      apply package_equiv_taint_set_committed; auto
  | H: package_equiv_taint' (taint_set_machine ?taint_base) ?pkg1 ?pkg2
    |- package_equiv_taint' ?taint_base ?pkg1 ?pkg2 =>
      apply package_equiv_taint_set_machine; auto
  | H: package_equiv_taint' (taint_set_sigma ?taint_base) ?pkg1 ?pkg2
    |- package_equiv_taint' ?taint_base ?pkg1 ?pkg2 =>
      apply package_equiv_taint_set_sigma; auto
  end; auto.


Lemma package_equiv_base_sval:
  forall pkg1 pkg2 pkg1' pkg2' p taint_base ,
  package_equiv_taint (compute_sval_taint' taint_base p) pkg1 pkg2 pkg1' pkg2' ->
  package_equiv_taint taint_base pkg1 pkg2 pkg1' pkg2'.
Proof.
  induction p; auto.
  - t_package_equiv_base_sval; auto.
  - t_package_equiv_base_sval; auto.
  - t_package_equiv_base_sval; auto.
  - t_package_equiv_base_sval; auto.
  - t_package_equiv_base_sval; auto.
  - t_package_equiv_base_sval; auto.
  - t_package_equiv_base_sval; auto;
      apply IHp; split; t_package_equiv_base_sval; auto.
  - t_package_equiv_base_sval; auto;
      apply IHp; split; t_package_equiv_base_sval; auto.
Qed.
Lemma package_equiv_base_fancy_spred:
  forall pkg1 pkg2 pkg1' pkg2' p taint_base ,
  package_equiv_taint (compute_fancy_spred_taint' taint_base p) pkg1 pkg2 pkg1' pkg2' ->
  package_equiv_taint taint_base pkg1 pkg2 pkg1' pkg2'.
Proof.
  intros pkg1 pkg2 pkg1' pkg2'.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall taint_base,
    package_equiv_taint (compute_fancy_spred_taint' taint_base (PBase p1)) pkg1 pkg2 pkg1' pkg2' ->
    package_equiv_taint taint_base pkg1 pkg2 pkg1' pkg2'); simpl in *; auto; intros.
  - repeat apply package_equiv_base_sval in H; auto.
  - repeat apply package_equiv_base_sval in H; auto.
  - t_package_equiv_base_sval.
  - revert H0. revert taint_base. induction l; simpl; auto.
    eauto.
  - revert H0. revert taint_base. induction l; simpl; auto.
    eauto.
Qed.

Lemma package_equiv_base_spred:
  forall pkg1 pkg2 pkg1' pkg2' p taint_base ,
  package_equiv_taint (compute_spred_taint' taint_base p) pkg1 pkg2 pkg1' pkg2' ->
  package_equiv_taint taint_base pkg1 pkg2 pkg1' pkg2'.
Proof.
  intros.
  apply package_equiv_base_fancy_spred with (p := PBase p). eauto.
Qed.

Lemma package_equiv_taint_fold_exists':
  forall (X: Type) l x pkg1 pkg2 pkg1' pkg2' taint_base f,
  package_equiv_taint
         (fold_left (fun (acc : se_taint_t) (r : X) => compute_fancy_spred_taint' acc (f r)) l
            taint_base) pkg1 pkg2 pkg1' pkg2' ->
  In x l ->
  exists taint, package_equiv_taint (compute_fancy_spred_taint' taint (f x)) pkg1 pkg2 pkg1' pkg2'.
Proof.
  induction l using rev_ind; simpl; auto.
  intros. rewrite in_app_iff in H0.  simpl in H0. rewrite fold_left_app in H.
  split_cases. simpl in H.
  apply package_equiv_base_fancy_spred in H. eauto.
Qed.

Lemma package_equiv_taint_fold_exists:
  forall l p pkg1 pkg2 pkg1' pkg2' taint_base ,
  package_equiv_taint
         (fold_left (fun (acc : se_taint_t) p => compute_fancy_spred_taint' acc p) l
            taint_base) pkg1 pkg2 pkg1' pkg2' ->
  In p l ->
  exists taint, package_equiv_taint (compute_fancy_spred_taint' taint p) pkg1 pkg2 pkg1' pkg2'.
Proof.
  induction l using rev_ind; simpl; auto.
  intros. rewrite in_app_iff in H0.  simpl in H0. rewrite fold_left_app in H.
  split_cases. simpl in H.
  apply package_equiv_base_fancy_spred in H. eauto.
Qed.


End Taint.


   Lemma prop_custom_lookup_name:
     forall {T: Type} (EqDec: EqDec T) (ps: list (T * Prop)) name0 prop,
       Forall (fun '(_, p) => p) ps ->
       find (fun '(name, _) => beq_dec name0 name) ps = Some (name0, prop) ->
       prop.
   Proof.
     intros. rewrite Forall_forall in H. apply find_some in H0.
     propositional; simplify. subst. specialize H with (1 := H1). simpl in H. auto.
   Qed.
   Lemma prop_custom_lookup_name':
     forall {T: Type} (EqDec: EqDec T) f (ps: list (T * fancy_spred)) name0 prop,
       Forall (fun '(_, p) => f p) ps ->
       find (fun '(name, _) => beq_dec name0 name) ps = Some (name0, prop) ->
       f prop .
   Proof.
     intros. rewrite Forall_forall in H. apply find_some in H0.
     propositional; simplify. subst. specialize H with (1 := H1). simpl in H. auto.
   Qed.
      Ltac prop_pose_with_custom  H' name h :=
        let foo := constr:(prop_custom_lookup_name' _ _ _ name _ h eq_refl) in
        pose proof foo as H'.
      Ltac prop_apply_with_custom name h :=
        let foo := constr:(prop_custom_lookup_name' _ _ _ name _ h eq_refl) in
        apply foo.
      Ltac prop_rewrite_with_custom name h :=
        let foo := constr:(prop_custom_lookup_name' _ _ _ name _ h eq_refl) in
        rewrite foo.
      Ltac prop_rewrite_with_custom_in H name h :=
        let foo := constr:(prop_custom_lookup_name' _ _ _ name _ h eq_refl) in
        rewrite foo in H.

      Ltac prop_rev_rewrite_with_custom name h :=
        let foo := constr:(prop_custom_lookup_name' _ _ _ name _ h eq_refl) in
        setoid_rewrite<-foo.
Definition set_machine (p: machine_pkg) (machine: machine_t) : machine_pkg :=
  {| pkg_machine := machine;
     pkg_init_st := p.(pkg_init_st);
     pkg_sigma := p.(pkg_sigma);
     pkg_mid_st := p.(pkg_mid_st);
     pkg_final_st := p.(pkg_final_st);
     pkg_mid_ext_log := p.(pkg_mid_ext_log);
     pkg_ext_log' := p.(pkg_ext_log')
  |}.

Definition set_init_st (p: machine_pkg) init_st : machine_pkg :=
  {| pkg_machine := p.(pkg_machine);
     pkg_init_st := init_st;
     pkg_sigma := p.(pkg_sigma);
     pkg_mid_st := p.(pkg_mid_st);
     pkg_final_st := p.(pkg_final_st);
     pkg_mid_ext_log := p.(pkg_mid_ext_log);
     pkg_ext_log' := p.(pkg_ext_log')
  |}.

Definition set_sigma (p: machine_pkg) sigma : machine_pkg :=
  {| pkg_machine := p.(pkg_machine);
     pkg_init_st := p.(pkg_init_st);
     pkg_sigma := sigma;
     pkg_mid_st := p.(pkg_mid_st);
     pkg_final_st := p.(pkg_final_st);
     pkg_mid_ext_log := p.(pkg_mid_ext_log);
     pkg_ext_log' := p.(pkg_ext_log')
  |}.

Definition set_mid_st (p: machine_pkg) mid_st : machine_pkg :=
  {| pkg_machine := p.(pkg_machine);
     pkg_init_st := p.(pkg_init_st);
     pkg_sigma := p.(pkg_sigma);
     pkg_mid_st := mid_st;
     pkg_final_st := p.(pkg_final_st);
     pkg_mid_ext_log := p.(pkg_mid_ext_log);
     pkg_ext_log' := p.(pkg_ext_log')
  |}.

Definition set_final_st (p: machine_pkg) final_st : machine_pkg :=
  {| pkg_machine := p.(pkg_machine);
     pkg_init_st := p.(pkg_init_st);
     pkg_sigma := p.(pkg_sigma);
     pkg_mid_st := p.(pkg_mid_st);
     pkg_final_st := final_st;
     pkg_mid_ext_log := p.(pkg_mid_ext_log);
     pkg_ext_log' := p.(pkg_ext_log')
  |}.

Definition set_mid_ext_log (p: machine_pkg) mid_ext_log : machine_pkg :=
  {| pkg_machine := p.(pkg_machine);
     pkg_init_st := p.(pkg_init_st);
     pkg_sigma := p.(pkg_sigma);
     pkg_mid_st := p.(pkg_mid_st);
     pkg_final_st := p.(pkg_final_st);
     pkg_mid_ext_log := mid_ext_log;
     pkg_ext_log' := p.(pkg_ext_log')
  |}.


Definition set_ext_log' (p: machine_pkg) ext_log' : machine_pkg :=
  {| pkg_machine := p.(pkg_machine);
     pkg_init_st := p.(pkg_init_st);
     pkg_sigma := p.(pkg_sigma);
     pkg_mid_st := p.(pkg_mid_st);
     pkg_final_st := p.(pkg_final_st);
     pkg_mid_ext_log := p.(pkg_mid_ext_log);
     pkg_ext_log' := ext_log'
  |}.
Fixpoint sval_ignores_fn (fn: debug_id_ty) (v: sval) : bool :=
  match v with
  | SConst _ => true
  | SInitReg machine _ => true
  | SMidReg machine _ => true
  | SFinalReg machine _ => true
  | SMidExtLog machine _ => true
  | SFinalExtLog machine _ => true
  | SCommittedExtLog machine _ => true
  | SBits1 fn1 v => sval_ignores_fn fn v
  | SBits2 fn2 v1 v2 => sval_ignores_fn fn v1 && sval_ignores_fn fn v2
  | SGetField machine sname fname v => sval_ignores_fn fn v
  | SExtCallApp machine extfn v => sval_ignores_fn fn v && negb (beq_dec (_id extfn) (_id fn))
  | SBound arg => true
  end.

Fixpoint spred_ignores_fn (fn: debug_id_ty) (p: spred) : bool :=
  match p with
  | PConst _ => true
  | PAnd b1 b2 => spred_ignores_fn fn b1 && spred_ignores_fn fn b2
  | POr b1 b2 => spred_ignores_fn fn b1 && spred_ignores_fn fn b2
  | PNot b => spred_ignores_fn fn b
  | PImpl p1 p2 => spred_ignores_fn fn p1 && spred_ignores_fn fn p2
  | PEq v1 v2 => sval_ignores_fn fn v1 && sval_ignores_fn fn v2
  | PNEq v1 v2 => sval_ignores_fn fn v1 && sval_ignores_fn fn v2
  | PForallArg1 arg body => spred_ignores_fn fn body
  | PForallArg2 arg1 arg2 body => spred_ignores_fn fn body
  | PExtFnEq fn' => negb (beq_dec (_id fn') (_id fn))
  | PFancy p => fancy_spred_ignores_fn fn p
  end with
  fancy_spred_ignores_fn fn  (p: fancy_spred)
                            : bool :=
    match p with
    | PBase e => spred_ignores_fn fn e
    | PForallRegs fn' regs => forallb (fun reg => fancy_spred_ignores_fn fn (fn' reg)) regs
    | PForallRegs2 fn' regs => forallb (fun reg => fancy_spred_ignores_fn fn (fn' reg)) regs
    end.

Fixpoint sval_taints_only_fns (fns: list debug_id_ty) (v: sval) : bool :=
  match v with
  | SConst _ => true
  | SInitReg machine _ => true
  | SMidReg machine _ => true
  | SFinalReg machine _ => true
  | SMidExtLog machine _ => true
  | SFinalExtLog machine _ => true
  | SCommittedExtLog machine _ => true
  | SBits1 fn1 v => sval_taints_only_fns fns v
  | SBits2 fn2 v1 v2 => sval_taints_only_fns fns v1 && sval_taints_only_fns fns v2
  | SGetField machine sname fname v => sval_taints_only_fns fns v
  | SExtCallApp machine extfn v => sval_taints_only_fns fns v &&  ((existsb (beq_dec extfn) fns))
  | SBound arg => true
  end.

Fixpoint spred_taints_only_fns (fns: list debug_id_ty) (p: spred) : bool :=
  match p with
  | PConst _ => true
  | PAnd b1 b2 => spred_taints_only_fns fns b1 && spred_taints_only_fns fns b2
  | POr b1 b2 => spred_taints_only_fns fns b1 && spred_taints_only_fns fns b2
  | PNot b => spred_taints_only_fns fns b
  | PImpl p1 p2 => spred_taints_only_fns fns p1 && spred_taints_only_fns fns p2
  | PEq v1 v2 => sval_taints_only_fns fns v1 && sval_taints_only_fns fns v2
  | PNEq v1 v2 => sval_taints_only_fns fns v1 && sval_taints_only_fns fns v2
  | PForallArg1 arg body => spred_taints_only_fns fns body
  | PForallArg2 arg1 arg2 body => spred_taints_only_fns fns body
  | PExtFnEq fn' => ((existsb (beq_dec fn') fns))
  | PFancy p => fancy_spred_taints_only_fns fns p
  end with
  fancy_spred_taints_only_fns fns  (p: fancy_spred)
                            : bool :=
    match p with
    | PBase e => spred_taints_only_fns fns e
    | PForallRegs fn' regs => forallb (fun reg => fancy_spred_taints_only_fns fns (fn' reg)) regs
    | PForallRegs2 fn' regs => forallb (fun reg => fancy_spred_taints_only_fns fns (fn' reg)) regs
    end.


Section Interp.
  Context {_ext_fn_tys: list (@Syntax.ext_fn_t N * (nat * nat))}.
  Context {unsafe_lookup_dstruct_fields: @struct_env_t debug_id_ty -> debug_id_ty -> list (@Syntax.dstruct_field_t debug_id_ty * nat)}.

  Notation unsafe_get_ext_call_from_log := (unsafe_get_ext_call_from_log _ext_fn_tys).
  Notation unsafe_get_ext_fn_arg_type :=  (unsafe_get_ext_fn_arg_type _ext_fn_tys).

Fixpoint interp_sval2 (impl_pkg spec_pkg: machine_pkg)
                      (bound_vars: list (string * vect_t))
                      (v: sval): vect_t :=
  let interp_sval2 := interp_sval2 impl_pkg spec_pkg bound_vars in
  match v with
  | SConst bs => bs
  | SInitReg machine reg =>
      let pkg := choose_pkg machine impl_pkg spec_pkg in
      pkg.(pkg_init_st).[_id reg]
  | SMidReg machine reg =>
      let pkg := choose_pkg machine impl_pkg spec_pkg in
      match pkg.(pkg_mid_st) with
      | Some st => st.[_id reg]
      | None => [] (* pkg.(pkg_init_st).[_id reg] *)
      end
  | SFinalReg machine reg =>
      let pkg := choose_pkg machine impl_pkg spec_pkg in
      pkg.(pkg_final_st).[_id reg]
  | SMidExtLog machine fn =>
      let pkg := choose_pkg machine impl_pkg spec_pkg in
      match pkg.(pkg_mid_ext_log) with
      | Some log => unsafe_get_ext_call_from_log log (_id fn)
      | None => zeroes (unsafe_get_ext_fn_arg_type (_id fn))
      end
  | SFinalExtLog machine fn =>
      let pkg := choose_pkg machine impl_pkg spec_pkg in
      unsafe_get_ext_call_from_log pkg.(pkg_ext_log') (_id fn)
  | SCommittedExtLog machine fn =>
      let pkg := choose_pkg machine impl_pkg spec_pkg in
      let mid_log :=
        match pkg.(pkg_mid_ext_log) with
        | Some log => log
        | None => SortedExtFnEnv.empty
        end in
      unsafe_get_ext_call_from_log (ext_log_app pkg.(pkg_ext_log') mid_log) (_id fn)
  | SBits1 fn1 v =>
      let  v := interp_sval2 v in
      (success_or_default (interp_bits1 fn1 v) [])
  | SBits2 fn2 v1 v2 =>
      let v1 := interp_sval2 v1 in
      let v2 := interp_sval2 v2 in
      (success_or_default (interp_bits2 fn2 v1 v2) [])
  | SGetField machine sname fname v =>
      let v := interp_sval2 v in
      let pkg := choose_pkg machine impl_pkg spec_pkg in
      unsafe_get_field (unsafe_lookup_dstruct_fields pkg.(pkg_machine).(file_struct_defs) sname) fname v
  | SExtCallApp mid extfn v =>
      let v := interp_sval2 v in
      let pkg := choose_pkg mid impl_pkg spec_pkg in
      unsafe_call_ext pkg.(pkg_sigma) (_id extfn) v
  | SBound arg =>
      match find (fun '(arg', _) => beq_dec arg' arg) bound_vars with
      | Some (_, v) => v
      | _ => []
      end
  end.
Fixpoint interp_spred2' (impl_pkg spec_pkg: machine_pkg)
                       (bound_vars: list (string * vect_t))
                       (p: spred) : Prop :=
  let interp_spred2'' := interp_spred2' impl_pkg spec_pkg bound_vars in
  match p with
  | PConst true => True
  | PConst false => False
  | PAnd b1 b2 =>
      interp_spred2'' b1 /\ interp_spred2'' b2
  | POr b1 b2 =>
      interp_spred2'' b1 \/ interp_spred2'' b2
  | PNot b =>
      (interp_spred2'' b -> False )
  | PImpl p1 p2 =>
      interp_spred2'' p1 -> interp_spred2'' p2
  | PEq v1 v2 =>
      interp_sval2 impl_pkg spec_pkg bound_vars v1 = interp_sval2 impl_pkg spec_pkg bound_vars v2
  | PNEq v1 v2 =>
      interp_sval2 impl_pkg spec_pkg bound_vars v1 <> interp_sval2 impl_pkg spec_pkg bound_vars v2
  | PForallArg1 (arg,ty) body =>
      forall y, Datatypes.length y = ty -> interp_spred2' impl_pkg spec_pkg ((arg,y)::bound_vars) body
  | PForallArg2 (arg1,ty1) (arg2,ty2) body =>
      forall x y, Datatypes.length x = ty1 ->
             Datatypes.length y = ty2 ->
             interp_spred2' impl_pkg spec_pkg ((arg1,x)::(arg2,y)::bound_vars) body
  | PExtFnEq fn  =>
      let impl_pkg := choose_pkg MachineImpl impl_pkg spec_pkg in
      let spec_pkg := choose_pkg MachineSpec impl_pkg spec_pkg in
      impl_pkg.(pkg_sigma) (_id fn) = spec_pkg.(pkg_sigma) (_id fn)
  | PFancy p =>
      interp_fancy_spred2' impl_pkg spec_pkg bound_vars p
  end with
  interp_fancy_spred2' (impl_pkg spec_pkg: machine_pkg)
                      (bound_vars: list (string * vect_t))
                      (p: fancy_spred)
                      : Prop :=
    let interp_spred2' := interp_spred2' impl_pkg spec_pkg bound_vars in
    let interp_fancy_spred2' := interp_fancy_spred2' impl_pkg spec_pkg bound_vars in
    match p with
    | PBase e => interp_spred2' e
    | PForallRegs fn regs =>
        forall x, In x regs -> interp_fancy_spred2' (fn x)
    | PForallRegs2 fn regs =>
        forall x, In x regs -> interp_fancy_spred2' (fn x)
    end.

Fixpoint interp_sval (pkg: machine_pkg)
                     (bound_vars: list (string * vect_t))
                     (v: sval): vect_t :=
  let interp_sval := interp_sval pkg bound_vars in
  match v with
  | SConst bs => bs
  | SInitReg machine reg =>
      pkg.(pkg_init_st).[_id reg]
  | SMidReg machine reg =>
      match pkg.(pkg_mid_st) with
      | Some st => st.[_id reg]
      | None =>  []
      end
  | SFinalReg machine reg =>
      pkg.(pkg_final_st).[_id reg]
  | SMidExtLog machine fn =>
      match pkg.(pkg_mid_ext_log) with
      | Some log => unsafe_get_ext_call_from_log log (_id fn)
      | None => zeroes (unsafe_get_ext_fn_arg_type (_id fn))
      end
  | SFinalExtLog machine fn =>
      unsafe_get_ext_call_from_log pkg.(pkg_ext_log') (_id fn)
  | SCommittedExtLog machine fn =>
      let mid_log :=
        match pkg.(pkg_mid_ext_log) with
        | Some log => log
        | None => SortedExtFnEnv.empty
        end in
      unsafe_get_ext_call_from_log (ext_log_app pkg.(pkg_ext_log') mid_log) (_id fn)
  | SBits1 fn1 v =>
      let  v := interp_sval v in
      (success_or_default (interp_bits1 fn1 v) [])
  | SBits2 fn2 v1 v2 =>
      let v1 := interp_sval v1 in
      let v2 := interp_sval v2 in
      (success_or_default (interp_bits2 fn2 v1 v2) [])
  | SGetField machine sname fname v =>
      let v := interp_sval v in
      unsafe_get_field (unsafe_lookup_dstruct_fields pkg.(pkg_machine).(file_struct_defs) sname) fname v
  | SExtCallApp mid extfn v =>
      let v := interp_sval v in
      unsafe_call_ext pkg.(pkg_sigma) (_id extfn) v
  | SBound arg =>
      match find (fun '(arg', _) => beq_dec arg' arg) bound_vars with
      | Some (_, v) => v
      | _ => []
      end
  end.

(* TODO: typecheck *)
Fixpoint interp_spred' (pkg : machine_pkg)
                       (bound_vars: list (string * vect_t))
                       (p: spred) : Prop :=
  let interp_spred'' := interp_spred' pkg bound_vars in
  match p with
  | PConst true => True
  | PConst false => False
  | PAnd b1 b2 =>
      interp_spred'' b1 /\ interp_spred'' b2
  | POr b1 b2 =>
      interp_spred'' b1 \/ interp_spred'' b2
  | PNot b =>
      (interp_spred'' b -> False )
  | PImpl p1 p2 =>
      interp_spred'' p1 -> interp_spred'' p2
  | PEq v1 v2 =>
      interp_sval pkg bound_vars v1 = interp_sval pkg bound_vars v2
  | PNEq v1 v2 =>
      interp_sval pkg bound_vars v1 <> interp_sval pkg bound_vars v2
  | PForallArg1 (arg,ty) body =>
      forall y, Datatypes.length y = ty -> interp_spred' pkg ((arg,y)::bound_vars) body
  | PForallArg2 (arg1,ty1) (arg2,ty2) body =>
      forall x y, Datatypes.length x = ty1 ->
             Datatypes.length y = ty2 ->
             interp_spred' pkg ((arg1,x)::(arg2,y)::bound_vars) body
  | PExtFnEq fn  =>
      True
  | PFancy p =>
      interp_fancy_spred' pkg bound_vars p
  end with
  interp_fancy_spred' (pkg : machine_pkg)
                      (bound_vars: list (string * vect_t))
                      (p: fancy_spred)
                      : Prop :=
    let interp_spred' := interp_spred' pkg bound_vars in
    let interp_fancy_spred' := interp_fancy_spred' pkg bound_vars in
    match p with
    | PBase e => interp_spred' e
    | PForallRegs fn regs =>
        forall x, In x regs -> interp_fancy_spred' (fn x)
    | PForallRegs2 fn regs =>
        forall x, In x regs -> interp_fancy_spred' (fn x)
    end.
Definition interp_fancy_spred (impl : machine_pkg) (p: fancy_spred)
                         : Prop :=
  interp_fancy_spred' impl [] p .
Definition interp_spred (impl : machine_pkg) (p: spred)
                         : Prop :=
  interp_spred' impl [] p.
Definition interp_fancy_spred2 (impl spec: machine_pkg) (p: fancy_spred)
                         : Prop :=
  interp_fancy_spred2' impl spec [] p .
Definition interp_spred2 (impl spec: machine_pkg) (p: spred)
                         : Prop :=
  interp_spred2' impl spec [] p .
Definition fn_replace_impl_mid_reg_with_init (v: sval) : sval :=
  match v with
  | SMidReg MachineImpl reg => SInitReg MachineImpl reg
  | _ => v
  end.
Definition fn_replace_spec_mid_reg_with_init (v: sval) : sval :=
  match v with
  | SMidReg MachineSpec reg => SInitReg MachineSpec reg
  | _ => v
  end.


Definition fn_replace_impl_mid_ext_with_final (v: sval) : sval :=
  match v with
  | SMidExtLog MachineImpl reg => SFinalExtLog MachineImpl reg
  | _ => v
  end.
Definition fn_replace_spec_mid_ext_with_final (v: sval) : sval :=
  match v with
  | SMidExtLog MachineSpec reg => SFinalExtLog MachineSpec reg
  | _ => v
  end.
Ltac common_tac :=
  match goal with
  | |- ?x <-> ?x => reflexivity
  | H : _ && _ = true |- _ => rewrite andb_true_iff in H
  | |- (forall _, _) <-> (forall _, _) =>
      split
  | H: forallb _ _ = true |- _ => rewrite forallb_forall in H
  | |- _ => progress (simplify; propositional)
  end.
Lemma replace_sval_final_ext_with_committed_correct:
  forall pkg ext_args v,
  pkg.(pkg_mid_ext_log) = None ->
  interp_sval pkg ext_args v =
  interp_sval pkg ext_args (replace_sval_final_ext_with_committed v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  rewrite heq. rewrite ext_log_app_empty_r. auto.
Qed.
Lemma replace_sval2_final_ext_with_committed_correct:
  forall pkg1 pkg2 ext_args v,
  pkg1.(pkg_mid_ext_log) = None \/ pkg1.(pkg_mid_ext_log) = Some SortedExtFnEnv.empty ->
  interp_sval2 pkg1 pkg2 ext_args v =
  interp_sval2 pkg1 pkg2 ext_args (replace_sval_base fn_replace_impl_final_ext_with_committed v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  destruct machine_id; simpl; unfold unsafe_get_ext_call_from_log, ext_log_app.
  all: try rewrite SortedExtFnEnv.opt_get_mapV; try rewrite SortedExtFnEnv.opt_get_zip_default.
  - repeat destruct_match; propositional; split_cases; simplify; cbn in *; discriminate.
  - repeat destruct_match; propositional; split_cases; simplify; cbn in *; discriminate.
Qed.

Lemma replace_sval2_final_ext_with_committed_correct__spec:
  forall pkg1 pkg2 ext_args v,
  pkg2.(pkg_mid_ext_log) = None \/ pkg2.(pkg_mid_ext_log) = Some SortedExtFnEnv.empty ->
  interp_sval2 pkg1 pkg2 ext_args v =
  interp_sval2 pkg1 pkg2 ext_args (replace_sval_base fn_replace_spec_final_ext_with_committed v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  destruct machine_id; simpl; unfold unsafe_get_ext_call_from_log, ext_log_app.
  all: try rewrite SortedExtFnEnv.opt_get_mapV; try rewrite SortedExtFnEnv.opt_get_zip_default.
  - repeat destruct_match; propositional; split_cases; simplify; cbn in *; try discriminate.
  - repeat destruct_match; propositional; split_cases; simplify; cbn in *; discriminate.
Qed.


Lemma replace_fancy_spred2_impl_final_ext_with_committed_correct:
  forall pkg1 pkg2 p,
  pkg1.(pkg_mid_ext_log) = None \/ pkg1.(pkg_mid_ext_log) = Some SortedExtFnEnv.empty ->
  interp_fancy_spred2 pkg1 pkg2 p <->
  interp_fancy_spred2 pkg1 pkg2 ((replace_sval_in_fancy_spred_base fn_replace_impl_final_ext_with_committed) p).
Proof.
  intros pkg1 pkg2 p hmid. unfold interp_fancy_spred2.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    interp_fancy_spred2' pkg1 pkg2 ext_args (PBase p1) <->
    interp_fancy_spred2' pkg1 pkg2 ext_args ((replace_sval_in_fancy_spred_base fn_replace_impl_final_ext_with_committed) (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred2' _ _ _ _ <-> interp_spred2' _ _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval2 _ _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval2_final_ext_with_committed_correct by auto
    | |- _ => common_tac
    end; auto.
  - rewrite<-H. auto.
  - rewrite H. auto.
  - rewrite<-H. auto.
  - rewrite H. auto.
Qed.

Lemma replace_fancy_spred2_spec_final_ext_with_committed_correct:
  forall pkg1 pkg2 p,
  pkg2.(pkg_mid_ext_log) = None \/ pkg2.(pkg_mid_ext_log) = Some SortedExtFnEnv.empty ->
  interp_fancy_spred2 pkg1 pkg2 p <->
  interp_fancy_spred2 pkg1 pkg2 ((replace_sval_in_fancy_spred_base fn_replace_spec_final_ext_with_committed) p).
Proof.
  intros pkg1 pkg2 p hmid. unfold interp_fancy_spred2.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    interp_fancy_spred2' pkg1 pkg2 ext_args (PBase p1) <->
    interp_fancy_spred2' pkg1 pkg2 ext_args ((replace_sval_in_fancy_spred_base fn_replace_spec_final_ext_with_committed) (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred2' _ _ _ _ <-> interp_spred2' _ _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval2 _ _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval2_final_ext_with_committed_correct__spec by auto
    | |- _ => common_tac
    end; auto.
  - rewrite<-H. auto.
  - rewrite H. auto.
  - rewrite<-H. auto.
  - rewrite H. auto.
Qed.


Lemma replace_spred2_impl_final_ext_with_committed_correct:
  forall pkg1 pkg2 p,
  pkg1.(pkg_mid_ext_log) = None \/ pkg1.(pkg_mid_ext_log) = Some SortedExtFnEnv.empty ->
  interp_spred2 pkg1 pkg2 p <->
  interp_spred2 pkg1 pkg2 ((replace_sval_in_spred_base fn_replace_impl_final_ext_with_committed) p).
Proof.
  intros. apply replace_fancy_spred2_impl_final_ext_with_committed_correct with (p := PBase p); auto.
Qed.

Lemma replace_spred2_spec_final_ext_with_committed_correct:
  forall pkg1 pkg2 p,
  pkg2.(pkg_mid_ext_log) = None \/ pkg2.(pkg_mid_ext_log) = Some SortedExtFnEnv.empty ->
  interp_spred2 pkg1 pkg2 p <->
  interp_spred2 pkg1 pkg2 ((replace_sval_in_spred_base fn_replace_spec_final_ext_with_committed) p).
Proof.
  intros. apply replace_fancy_spred2_spec_final_ext_with_committed_correct with (p := PBase p); auto.
Qed.
Lemma replace_sval2_impl_mid_ext_with_final_correct:
  forall pkg1 pkg2 ext_args v,
  Some pkg1.(pkg_ext_log') = pkg1.(pkg_mid_ext_log) ->
  interp_sval2 pkg1 pkg2 ext_args v =
  interp_sval2 pkg1 pkg2 ext_args (replace_sval_base fn_replace_impl_mid_ext_with_final v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  destruct machine_id; simpl; unfold unsafe_get_ext_call_from_log, ext_log_app.
  all: try rewrite<-heq; auto.
Qed.

Lemma replace_fancy_spred2_impl_mid_ext_with_final_correct:
  forall pkg1 pkg2 p,
  Some pkg1.(pkg_ext_log') = pkg1.(pkg_mid_ext_log) ->
  interp_fancy_spred2 pkg1 pkg2 p <->
  interp_fancy_spred2 pkg1 pkg2 ((replace_sval_in_fancy_spred_base fn_replace_impl_mid_ext_with_final) p).
Proof.
  intros pkg1 pkg2 p hmid. unfold interp_fancy_spred2.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    interp_fancy_spred2' pkg1 pkg2 ext_args (PBase p1) <->
    interp_fancy_spred2' pkg1 pkg2 ext_args ((replace_sval_in_fancy_spred_base fn_replace_impl_mid_ext_with_final) (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred2' _ _ _ _ <-> interp_spred2' _ _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval2 _ _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval2_impl_mid_ext_with_final_correct by auto
    | |- _ => common_tac
    end; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
Qed.

Lemma replace_sval2_spec_mid_ext_with_final_correct:
  forall pkg1 pkg2 ext_args v,
  Some pkg2.(pkg_ext_log') = pkg2.(pkg_mid_ext_log) ->
  interp_sval2 pkg1 pkg2 ext_args v =
  interp_sval2 pkg1 pkg2 ext_args (replace_sval_base fn_replace_spec_mid_ext_with_final v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  destruct machine_id; simpl; unfold unsafe_get_ext_call_from_log, ext_log_app.
  all: try rewrite<-heq; auto.
Qed.


Lemma replace_fancy_spred2_spec_mid_ext_with_final_correct:
  forall pkg1 pkg2 p,
  Some pkg2.(pkg_ext_log') = pkg2.(pkg_mid_ext_log) ->
  interp_fancy_spred2 pkg1 pkg2 p <->
  interp_fancy_spred2 pkg1 pkg2 ((replace_sval_in_fancy_spred_base fn_replace_spec_mid_ext_with_final) p).
Proof.
  intros pkg1 pkg2 p hmid. unfold interp_fancy_spred2.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    interp_fancy_spred2' pkg1 pkg2 ext_args (PBase p1) <->
    interp_fancy_spred2' pkg1 pkg2 ext_args ((replace_sval_in_fancy_spred_base fn_replace_spec_mid_ext_with_final) (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred2' _ _ _ _ <-> interp_spred2' _ _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval2 _ _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval2_spec_mid_ext_with_final_correct by auto
    | |- _ => common_tac
    end; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
Qed.

Lemma replace_spred2_impl_mid_ext_with_final_correct:
  forall pkg1 pkg2 p,
  Some pkg1.(pkg_ext_log') = pkg1.(pkg_mid_ext_log) ->
  interp_spred2 pkg1 pkg2 p <->
  interp_spred2 pkg1 pkg2 ((replace_sval_in_spred_base fn_replace_impl_mid_ext_with_final) p).
Proof.
  intros. apply replace_fancy_spred2_impl_mid_ext_with_final_correct with (p := PBase p); auto.
Qed.

Lemma replace_spred2_spec_mid_ext_with_final_correct:
  forall pkg1 pkg2 p,
  Some pkg2.(pkg_ext_log') = pkg2.(pkg_mid_ext_log) ->
  interp_spred2 pkg1 pkg2 p <->
  interp_spred2 pkg1 pkg2 ((replace_sval_in_spred_base fn_replace_spec_mid_ext_with_final) p).
Proof.
  intros. apply replace_fancy_spred2_spec_mid_ext_with_final_correct with (p := PBase p); auto.
Qed.

Lemma replace_sval2_impl_mid_reg_with_init_correct:
  forall pkg1 pkg2 ext_args v,
  Some pkg1.(pkg_init_st) = pkg1.(pkg_mid_st) ->
  interp_sval2 pkg1 pkg2 ext_args v =
  interp_sval2 pkg1 pkg2 ext_args (replace_sval_base fn_replace_impl_mid_reg_with_init v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  destruct machine_id; simpl; unfold unsafe_get_ext_call_from_log, ext_log_app.
  all: try rewrite<-heq; auto.
Qed.

Lemma replace_fancy_spred2_impl_mid_reg_with_init_correct:
  forall pkg1 pkg2 p,
  Some pkg1.(pkg_init_st) = pkg1.(pkg_mid_st) ->
  interp_fancy_spred2 pkg1 pkg2 p <->
  interp_fancy_spred2 pkg1 pkg2 ((replace_sval_in_fancy_spred_base fn_replace_impl_mid_reg_with_init) p).
Proof.
  intros pkg1 pkg2 p hmid. unfold interp_fancy_spred2.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    interp_fancy_spred2' pkg1 pkg2 ext_args (PBase p1) <->
    interp_fancy_spred2' pkg1 pkg2 ext_args ((replace_sval_in_fancy_spred_base fn_replace_impl_mid_reg_with_init) (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred2' _ _ _ _ <-> interp_spred2' _ _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval2 _ _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval2_impl_mid_reg_with_init_correct by auto
    | |- _ => common_tac
    end; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
Qed.

Lemma replace_sval2_spec_mid_reg_with_init_correct:
  forall pkg1 pkg2 ext_args v,
  Some pkg2.(pkg_init_st) = pkg2.(pkg_mid_st) ->
  interp_sval2 pkg1 pkg2 ext_args v =
  interp_sval2 pkg1 pkg2 ext_args (replace_sval_base fn_replace_spec_mid_reg_with_init v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  destruct machine_id; simpl; unfold unsafe_get_ext_call_from_log, ext_log_app.
  all: try rewrite<-heq; auto.
Qed.


Lemma replace_fancy_spred2_spec_mid_reg_with_init_correct:
  forall pkg1 pkg2 p,
  Some pkg2.(pkg_init_st) = pkg2.(pkg_mid_st) ->
  interp_fancy_spred2 pkg1 pkg2 p <->
  interp_fancy_spred2 pkg1 pkg2 ((replace_sval_in_fancy_spred_base fn_replace_spec_mid_reg_with_init) p).
Proof.
  intros pkg1 pkg2 p hmid. unfold interp_fancy_spred2.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    interp_fancy_spred2' pkg1 pkg2 ext_args (PBase p1) <->
    interp_fancy_spred2' pkg1 pkg2 ext_args ((replace_sval_in_fancy_spred_base fn_replace_spec_mid_reg_with_init) (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred2' _ _ _ _ <-> interp_spred2' _ _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval2 _ _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval2_spec_mid_reg_with_init_correct by auto
    | |- _ => common_tac
    end; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
Qed.

Lemma replace_spred2_impl_mid_reg_with_init_correct:
  forall pkg1 pkg2 p,
  Some pkg1.(pkg_init_st) = pkg1.(pkg_mid_st) ->
  interp_spred2 pkg1 pkg2 p <->
  interp_spred2 pkg1 pkg2 ((replace_sval_in_spred_base fn_replace_impl_mid_reg_with_init) p).
Proof.
  intros. apply replace_fancy_spred2_impl_mid_reg_with_init_correct with (p := PBase p); auto.
Qed.
Lemma replace_spred2_spec_mid_reg_with_init_correct:
  forall pkg1 pkg2 p,
  Some pkg2.(pkg_init_st) = pkg2.(pkg_mid_st) ->
  interp_spred2 pkg1 pkg2 p <->
  interp_spred2 pkg1 pkg2 ((replace_sval_in_spred_base fn_replace_spec_mid_reg_with_init) p).
Proof.
  intros. apply replace_fancy_spred2_spec_mid_reg_with_init_correct with (p := PBase p); auto.
Qed.

Lemma replace_sval2_impl_mid_reg_with_final_correct:
  forall pkg1 pkg2 ext_args v,
  Some pkg1.(pkg_final_st) = pkg1.(pkg_mid_st) ->
  interp_sval2 pkg1 pkg2 ext_args v =
  interp_sval2 pkg1 pkg2 ext_args (replace_sval_base fn_replace_impl_mid_reg_with_final v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  destruct machine_id; simpl; unfold unsafe_get_ext_call_from_log, ext_log_app.
  all: try rewrite<-heq; auto.
Qed.

Lemma replace_fancy_spred2_impl_mid_reg_with_final_correct:
  forall pkg1 pkg2 p,
  Some pkg1.(pkg_final_st) = pkg1.(pkg_mid_st) ->
  interp_fancy_spred2 pkg1 pkg2 p <->
  interp_fancy_spred2 pkg1 pkg2 ((replace_sval_in_fancy_spred_base fn_replace_impl_mid_reg_with_final) p).
Proof.
  intros pkg1 pkg2 p hmid. unfold interp_fancy_spred2.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    interp_fancy_spred2' pkg1 pkg2 ext_args (PBase p1) <->
    interp_fancy_spred2' pkg1 pkg2 ext_args ((replace_sval_in_fancy_spred_base fn_replace_impl_mid_reg_with_final) (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred2' _ _ _ _ <-> interp_spred2' _ _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval2 _ _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval2_impl_mid_reg_with_final_correct by auto
    | |- _ => common_tac
    end; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
Qed.

Lemma replace_spred2_impl_mid_reg_with_final_correct:
  forall pkg1 pkg2 p,
  Some pkg1.(pkg_final_st) = pkg1.(pkg_mid_st) ->
  interp_spred2 pkg1 pkg2 p <->
  interp_spred2 pkg1 pkg2 ((replace_sval_in_spred_base fn_replace_impl_mid_reg_with_final) p).
Proof.
  intros. apply replace_fancy_spred2_impl_mid_reg_with_final_correct with (p := PBase p); auto.
Qed.

Lemma replace_sval2_spec_mid_reg_with_final_correct:
  forall pkg1 pkg2 ext_args v,
  Some pkg2.(pkg_final_st) = pkg2.(pkg_mid_st) ->
  interp_sval2 pkg1 pkg2 ext_args v =
  interp_sval2 pkg1 pkg2 ext_args (replace_sval_base fn_replace_spec_mid_reg_with_final v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  destruct machine_id; simpl; unfold unsafe_get_ext_call_from_log, ext_log_app.
  all: try rewrite<-heq; auto.
Qed.


Lemma replace_fancy_spred2_spec_mid_reg_with_final_correct:
  forall pkg1 pkg2 p,
  Some pkg2.(pkg_final_st) = pkg2.(pkg_mid_st) ->
  interp_fancy_spred2 pkg1 pkg2 p <->
  interp_fancy_spred2 pkg1 pkg2 ((replace_sval_in_fancy_spred_base fn_replace_spec_mid_reg_with_final) p).
Proof.
  intros pkg1 pkg2 p hmid. unfold interp_fancy_spred2.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    interp_fancy_spred2' pkg1 pkg2 ext_args (PBase p1) <->
    interp_fancy_spred2' pkg1 pkg2 ext_args ((replace_sval_in_fancy_spred_base fn_replace_spec_mid_reg_with_final) (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred2' _ _ _ _ <-> interp_spred2' _ _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval2 _ _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval2_spec_mid_reg_with_final_correct by auto
    | |- _ => common_tac
    end; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
Qed.

Lemma replace_spred2_spec_mid_reg_with_final_correct:
  forall pkg1 pkg2 p,
  Some pkg2.(pkg_final_st) = pkg2.(pkg_mid_st) ->
  interp_spred2 pkg1 pkg2 p <->
  interp_spred2 pkg1 pkg2 ((replace_sval_in_spred_base fn_replace_spec_mid_reg_with_final) p).
Proof.
  intros. apply replace_fancy_spred2_spec_mid_reg_with_final_correct with (p := PBase p); auto.
Qed.

Lemma replace_sval2_impl_init_reg_with_final_correct:
  forall pkg1 pkg2 ext_args v,
  pkg1.(pkg_init_st) = pkg1.(pkg_final_st) ->
  interp_sval2 pkg1 pkg2 ext_args v =
  interp_sval2 pkg1 pkg2 ext_args (replace_sval_base fn_replace_impl_init_reg_with_final v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  destruct machine_id; simpl; unfold unsafe_get_ext_call_from_log, ext_log_app.
  all: try rewrite<-heq; auto.
Qed.


Lemma replace_fancy_spred2_impl_init_reg_with_final_correct:
  forall pkg1 pkg2 p,
  pkg1.(pkg_init_st) = pkg1.(pkg_final_st) ->
  interp_fancy_spred2 pkg1 pkg2 p <->
  interp_fancy_spred2 pkg1 pkg2 ((replace_sval_in_fancy_spred_base fn_replace_impl_init_reg_with_final) p).
Proof.
  intros pkg1 pkg2 p hmid. unfold interp_fancy_spred2.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    interp_fancy_spred2' pkg1 pkg2 ext_args (PBase p1) <->
    interp_fancy_spred2' pkg1 pkg2 ext_args ((replace_sval_in_fancy_spred_base fn_replace_impl_init_reg_with_final) (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred2' _ _ _ _ <-> interp_spred2' _ _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval2 _ _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval2_impl_init_reg_with_final_correct by auto
    | |- _ => common_tac
    end; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
Qed.

Lemma replace_spred2_impl_init_reg_with_final_correct:
  forall pkg1 pkg2 p,
  pkg1.(pkg_init_st) = pkg1.(pkg_final_st) ->
  interp_spred2 pkg1 pkg2 p <->
  interp_spred2 pkg1 pkg2 ((replace_sval_in_spred_base fn_replace_impl_init_reg_with_final) p).
Proof.
  intros. apply replace_fancy_spred2_impl_init_reg_with_final_correct with (p := PBase p); auto.
Qed.

Lemma replace_sval2_spec_init_reg_with_final_correct:
  forall pkg1 pkg2 ext_args v,
  pkg2.(pkg_init_st) = pkg2.(pkg_final_st) ->
  interp_sval2 pkg1 pkg2 ext_args v =
  interp_sval2 pkg1 pkg2 ext_args (replace_sval_base fn_replace_spec_init_reg_with_final v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  destruct machine_id; simpl; unfold unsafe_get_ext_call_from_log, ext_log_app.
  all: try rewrite<-heq; auto.
Qed.

Lemma replace_fancy_spred2_spec_init_reg_with_final_correct:
  forall pkg1 pkg2 p,
  pkg2.(pkg_init_st) = pkg2.(pkg_final_st) ->
  interp_fancy_spred2 pkg1 pkg2 p <->
  interp_fancy_spred2 pkg1 pkg2 ((replace_sval_in_fancy_spred_base fn_replace_spec_init_reg_with_final) p).
Proof.
  intros pkg1 pkg2 p hmid. unfold interp_fancy_spred2.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    interp_fancy_spred2' pkg1 pkg2 ext_args (PBase p1) <->
    interp_fancy_spred2' pkg1 pkg2 ext_args ((replace_sval_in_fancy_spred_base fn_replace_spec_init_reg_with_final) (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred2' _ _ _ _ <-> interp_spred2' _ _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval2 _ _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval2_spec_init_reg_with_final_correct by auto
    | |- _ => common_tac
    end; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
Qed.

Lemma replace_spred2_spec_init_reg_with_final_correct:
  forall pkg1 pkg2 p,
  pkg2.(pkg_init_st) = pkg2.(pkg_final_st) ->
  interp_spred2 pkg1 pkg2 p <->
  interp_spred2 pkg1 pkg2 ((replace_sval_in_spred_base fn_replace_spec_init_reg_with_final) p).
Proof.
  intros. apply replace_fancy_spred2_spec_init_reg_with_final_correct with (p := PBase p); auto.
Qed.

Lemma replace_sval_final_reg_with_init_correct:
  forall pkg ext_args v,
  pkg.(pkg_final_st) = pkg.(pkg_init_st) ->
  interp_sval pkg ext_args v =
  interp_sval pkg ext_args (replace_sval_final_reg_with_init v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  rewrite_solve.
Qed.

Lemma replace_fancy_spred_final_reg_with_init_correct:
  forall pkg p,
  pkg.(pkg_final_st) = pkg.(pkg_init_st) ->
  interp_fancy_spred pkg p <->
  interp_fancy_spred pkg (replace_fancy_spred_final_reg_with_init p).
Proof.
  intros pkg p hst_eq. unfold interp_fancy_spred.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
   interp_fancy_spred' pkg ext_args (PBase p1) <->
   interp_fancy_spred' pkg ext_args (replace_fancy_spred_final_reg_with_init (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred' _ _ _ <-> interp_spred' _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval_final_reg_with_init_correct by auto
    | |- _ => common_tac
    end.
  - rewrite<-H. auto.
  - rewrite H. eauto.
  - rewrite<-H. auto.
  - rewrite H. eauto.
Qed.
Lemma replace_sval_init_reg_with_mid_correct:
  forall pkg ext_args v,
  pkg.(pkg_mid_st) = Some pkg.(pkg_init_st) ->
  interp_sval pkg ext_args v =
  interp_sval pkg ext_args (replace_sval_init_reg_with_mid v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  rewrite_solve.
Qed.

Lemma replace_fancy_spred_init_reg_with_mid_correct:
  forall pkg p,
  pkg.(pkg_mid_st) = Some pkg.(pkg_init_st) ->
  interp_fancy_spred pkg p <->
  interp_fancy_spred pkg (replace_fancy_spred_init_reg_with_mid p).
Proof.
  intros pkg p hst_eq. unfold interp_fancy_spred.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
   interp_fancy_spred' pkg ext_args (PBase p1) <->
   interp_fancy_spred' pkg ext_args (replace_fancy_spred_init_reg_with_mid (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred' _ _ _ <-> interp_spred' _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval_init_reg_with_mid_correct by auto
    | |- _ => common_tac
    end.
  - rewrite<-H. auto.
  - rewrite H. eauto.
  - rewrite<-H. auto.
  - rewrite H. eauto.
Qed.

Lemma replace_sval_init_reg_with_final_correct:
  forall pkg ext_args v,
  pkg.(pkg_init_st) = pkg.(pkg_final_st) ->
  interp_sval pkg ext_args v =
  interp_sval pkg ext_args (replace_sval_init_reg_with_final v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  rewrite_solve.
Qed.

Lemma replace_fancy_spred_init_reg_with_final_correct:
  forall pkg p,
  pkg.(pkg_init_st) = pkg.(pkg_final_st) ->
  interp_fancy_spred pkg p <->
  interp_fancy_spred pkg (replace_fancy_spred_init_reg_with_final p).
Proof.
  intros pkg p hst_eq. unfold interp_fancy_spred.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
   interp_fancy_spred' pkg ext_args (PBase p1) <->
   interp_fancy_spred' pkg ext_args (replace_fancy_spred_init_reg_with_final (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred' _ _ _ <-> interp_spred' _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval_init_reg_with_final_correct by auto
    | |- _ => common_tac
    end.
  - rewrite<-H. auto.
  - rewrite H. eauto.
  - rewrite<-H. auto.
  - rewrite H. eauto.
Qed.




Lemma replace_sval_mid_reg_with_final_correct:
  forall pkg ext_args v,
  pkg.(pkg_mid_st) = Some pkg.(pkg_final_st) ->
  interp_sval pkg ext_args v =
  interp_sval pkg ext_args (replace_sval_mid_reg_with_final v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  rewrite_solve.
Qed.

Lemma replace_fancy_spred_mid_reg_with_final_correct:
  forall pkg p,
  pkg.(pkg_mid_st) = Some pkg.(pkg_final_st) ->
  interp_fancy_spred pkg p <->
  interp_fancy_spred pkg (replace_fancy_spred_mid_reg_with_final p).
Proof.
  intros pkg p hst_eq. unfold interp_fancy_spred.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
   interp_fancy_spred' pkg ext_args (PBase p1) <->
   interp_fancy_spred' pkg ext_args (replace_fancy_spred_mid_reg_with_final (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred' _ _ _ <-> interp_spred' _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval_mid_reg_with_final_correct by auto
    | |- _ => common_tac
    end.
  - rewrite<-H. auto.
  - rewrite H. eauto.
  - rewrite<-H. auto.
  - rewrite H. eauto.
Qed.

Lemma replace_sval_mid_ext_with_final_correct:
  forall pkg ext_args v,
  pkg.(pkg_mid_ext_log) = Some pkg.(pkg_ext_log') ->
  interp_sval pkg ext_args v =
  interp_sval pkg ext_args (replace_sval_mid_ext_with_final v).
Proof.
  intros * heq. induction v; simpl; auto; repeat rewrite IHv; repeat rewrite IHv1; repeat rewrite IHv2; auto.
  rewrite_solve.
Qed.

Lemma replace_fancy_spred_mid_ext_with_final_correct:
  forall pkg p,
  pkg.(pkg_mid_ext_log) = Some pkg.(pkg_ext_log') ->
  interp_fancy_spred pkg p <->
  interp_fancy_spred pkg (replace_fancy_spred_mid_ext_with_final p).
Proof.
  intros pkg p hst_eq. unfold interp_fancy_spred.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
   interp_fancy_spred' pkg ext_args (PBase p1) <->
   interp_fancy_spred' pkg ext_args (replace_fancy_spred_mid_ext_with_final (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred' _ _ _ <-> interp_spred' _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval_mid_ext_with_final_correct by auto
    | |- _ => common_tac
    end.
  - rewrite<-H. auto.
  - rewrite H. eauto.
  - rewrite<-H. auto.
  - rewrite H. eauto.
Qed.


Lemma replace_fancy_spred_final_ext_with_committed_correct:
  forall pkg p,
  pkg.(pkg_mid_ext_log) = None ->
  interp_fancy_spred pkg p <->
  interp_fancy_spred pkg (replace_fancy_spred_final_ext_with_committed p).
Proof.
  intros pkg p hst_eq. unfold interp_fancy_spred.
  generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
   interp_fancy_spred' pkg ext_args (PBase p1) <->
   interp_fancy_spred' pkg ext_args (replace_fancy_spred_final_ext_with_committed (PBase p1)));
    simpl in *; auto;
    repeat match goal with
    | H: forall _, interp_spred' _ _ _ <-> interp_spred' _ _ (replace_sval_in_spred_base _  _) |- _ =>
        (rewrite H by auto) || (solve[(rewrite<-H by auto); eauto])
    | |- context[interp_sval _ _ (replace_sval_base _ _)] =>
        rewrite<-replace_sval_final_ext_with_committed_correct by auto
    | |- _ => common_tac
    end.
  - rewrite<-H. auto.
  - rewrite H. eauto.
  - rewrite<-H. auto.
  - rewrite H. eauto.
Qed.
Lemma taint_set_machine_bounded:
  forall i, taint_set_machine (taint_set_machine i) = taint_set_machine i.
Proof.
  reflexivity.
Qed.

Ltac solve_package_equiv_taint :=
  consider package_equiv_taint; consider package_equiv_taint'; simpl in *; propositional; split_ands_in_goal;
    repeat match goal with
    | H: _ \/ true = false |- _ => destruct H; [ | discriminate]
    | _ => rewrite_solve
    end; auto.
Lemma interp_sval2_taint_ok:
  forall pkg1 pkg2 pkg1' pkg2' v ext_args taint_base,
  package_equiv_taint (compute_sval_taint' taint_base v) pkg1 pkg2 pkg1' pkg2' ->
  interp_sval2 pkg1 pkg1' ext_args v =
  interp_sval2 pkg2 pkg2' ext_args v.
Proof.
  induction v; intros ext_args taint_base; simpl in *; auto.
  all: try solve[try destruct machine_id; solve_package_equiv_taint].
  - intros. erewrite IHv; eauto.
  - intros. erewrite IHv2 with (ext_args := ext_args); eauto.
    intros. erewrite IHv1 with (ext_args := ext_args) ; eauto.
    apply package_equiv_base_sval in H. eauto.
  - destruct_match; simpl; auto; intros htaint.
    + rewrite IHv with (taint_base := taint_base); solve_package_equiv_taint.
    + rewrite IHv with (taint_base := taint_base); solve_package_equiv_taint.
  - destruct_match; simpl; auto; intros htaint.
    + rewrite IHv with (taint_base := taint_base); solve_package_equiv_taint.
    + rewrite IHv with (taint_base := taint_base); solve_package_equiv_taint.
Qed.

Lemma interp_sval_taints_only_ok':
  forall pkg sigma' ext_args fns v,
  sval_taints_only_fns fns v = true ->
  Forall (fun fn : debug_id_ty => forall input : list bool, pkg_sigma pkg (_id fn) input = sigma' (_id fn) input) fns ->
  interp_sval pkg ext_args v = interp_sval (set_sigma pkg sigma') ext_args v.
Proof.
  induction v; propositional.
  - destruct op; simpl; rewrite IHv; auto.
  - simpl in H. rewrite andb_true_iff in *. propositional.
    destruct op; simpl; try rewrite IHv1; try rewrite IHv2; auto.
  - simpl in H. simpl. rewrite IHv; auto.
  - simpl in *; rewrite andb_true_iff in *; propositional.
    rewrite IHv; auto.
    rewrite existsb_exists in H2. propositional; simplify.
    rewrite Forall_forall in H0.
    consider unsafe_call_ext. rewrite H0; auto.
Qed.

Lemma interp_sval_taints_only_ok:
  forall pkg sigma' ext_args fns v1 v2,
  sval_taints_only_fns fns v1 = true ->
  sval_taints_only_fns fns v2 = true ->
  Forall (fun fn : debug_id_ty => forall input : list bool, pkg_sigma pkg (_id fn) input = sigma' (_id fn) input) fns ->
  interp_sval pkg ext_args v1 = interp_sval pkg ext_args v2 <->
  interp_sval (set_sigma pkg sigma') ext_args v1 = interp_sval (set_sigma pkg sigma') ext_args v2.
Proof.
  intros. erewrite interp_sval_taints_only_ok' by eauto.
  erewrite interp_sval_taints_only_ok' with (1 := H0) by eauto.
  reflexivity.
Qed.

Ltac step_package_equiv :=
    repeat match goal with
    | H: _ \/ true = false |- _ =>
        let H' := fresh in
        destruct H as [H' | ? ]; [ | discriminate];
        repeat rewrite H' in *
    end; auto.
Lemma interp_fancy_spred_taints_only_ok:
  forall pkg sigma' p fns,
  fancy_spred_taints_only_fns fns p = true ->
  Forall (fun fn => forall input, (pkg.(pkg_sigma) (_id fn)) input = sigma' (_id fn) input ) fns ->
  interp_fancy_spred pkg p <-> interp_fancy_spred (set_sigma pkg sigma') p.
Proof.
  intros pkg sigma' p fns. consider interp_fancy_spred.
  generalize (@nil (string * vect_t)) as ext_args.
  generalize dependent p.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args ,
      fancy_spred_taints_only_fns fns (PBase p1) = true ->
      Forall (fun fn : debug_id_ty => forall input : list bool, pkg_sigma pkg (_id fn) input = sigma' (_id fn) input) fns ->
      interp_fancy_spred' pkg ext_args (PBase p1) <-> interp_fancy_spred' (set_sigma pkg sigma') ext_args (PBase p1)).
  all: propositional; simpl in *;  try rewrite andb_true_iff in *; propositional;
       try rewrite IHf by auto; try rewrite IHf0 by auto; auto; try reflexivity.
  - rewrite interp_sval_taints_only_ok; eauto. reflexivity.
  - rewrite interp_sval_taints_only_ok; eauto. reflexivity.
  - repeat destruct_match; subst. split; intros; try rewrite<-IHf; auto; try rewrite IHf; auto.
  - repeat destruct_match; subst. split; intros; try rewrite<-IHf; auto; try rewrite IHf; auto.
  - repeat destruct_match; subst. split; intros; try rewrite<-IHf; auto; try rewrite IHf; auto;
      rewrite forallb_forall in *.
    + rewrite<-H; eauto.
    + rewrite H; eauto.
  - repeat destruct_match; subst. split; intros; try rewrite<-IHf; auto; try rewrite IHf; auto;
      rewrite forallb_forall in *.
    + rewrite<-H; eauto.
    + rewrite H; eauto.

Qed.

Lemma interp_spred_taints_only_ok:
  forall pkg p sigma' fns,
  spred_taints_only_fns fns p = true ->
  Forall (fun fn => forall input, (pkg.(pkg_sigma) (_id fn)) input = sigma' (_id fn) input ) fns ->
  interp_spred pkg p <-> interp_spred (set_sigma pkg sigma') p.
Proof.
  intros. specialize interp_fancy_spred_taints_only_ok with (p := PBase p).
  intros. simpl in H1.
  eapply H1; eauto.
Qed.


Lemma interp_fancy_spred2_taint_ok:
  forall pkg1 pkg2 pkg1' pkg2' p ext_args taint_base ,
  package_equiv_taint (compute_fancy_spred_taint' taint_base p) pkg1 pkg2 pkg1' pkg2' ->
  interp_fancy_spred2' pkg1 pkg1' ext_args p <->
  interp_fancy_spred2' pkg2 pkg2' ext_args p.
Proof.
  intros pkg1 pkg2 pkg1' pkg2'.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args taint_base,
    package_equiv_taint (compute_fancy_spred_taint' taint_base (PBase p1)) pkg1 pkg2 pkg1' pkg2' ->
    interp_fancy_spred2' pkg1 pkg1' ext_args (PBase p1) <->
    interp_fancy_spred2' pkg2 pkg2' ext_args (PBase p1));
  simpl; propositional; split_ands_in_goal; simpl in *; destruct_match_pairs; split; propositional; split_ands_in_goal.
    Ltac t_interp_fancy_spred2_taint_ok :=
  repeat match goal with
  | H: package_equiv_taint (compute_spred_taint' _ _) _ _ _ _ |- _ =>
      pose_fresh (package_equiv_base_spred _ _ _ _ _ _ H)
  | H: package_equiv_taint (compute_sval_taint' _ _) _ _ _ _ |- _ =>
      pose_fresh (package_equiv_base_sval _ _ _ _ _ _ H)
  | H: forall (ext_args : list (string * vect_t)) (taint_base : se_taint_t),
        package_equiv_taint (compute_spred_taint' taint_base ?p1) ?pkg1 ?pkg2 ?pkg1' ?pkg2' ->
        interp_spred2' ?pkg1 ?pkg1' ext_args ?p1 <-> interp_spred2' ?pkg2 ?pkg2' ext_args ?p1,
    H1: package_equiv_taint (compute_spred_taint' _ ?p1) _ _ _ _ ,
    H2: context[interp_spred2' ?pkg1 ?pkg1' ?ext_args ?p1] |- _ =>
    let H' := fresh in
    pose_fresh_as H' (H ext_args _ H1 ); rewrite H' in H2
  | H: forall (ext_args : list (string * vect_t)) (taint_base : se_taint_t),
        package_equiv_taint (compute_spred_taint' taint_base ?p1) ?pkg1 ?pkg2 ?pkg1' ?pkg2' ->
        interp_spred2' ?pkg1 ?pkg1' ext_args ?p1 <-> interp_spred2' ?pkg2 ?pkg2' ext_args ?p1,
    H1: package_equiv_taint (compute_spred_taint' _ ?p1) _ _ _ _
    |- context[interp_spred2' ?pkg1 ?pkg1' ?ext_args ?p1] =>
    rewrite H with (1 := H1)
  | H: package_equiv_taint (compute_sval_taint' _ ?v) ?pkg1 _ ?pkg1' _,
    H1: context[interp_sval2 ?pkg1 ?pkg1' ?ext_args ?v] |- _ =>
      let H' := fresh in
      pose_fresh_as H' (interp_sval2_taint_ok _ _ _ _ _ ext_args _ H); rewrite H' in H1
  | H: package_equiv_taint (compute_sval_taint' _ ?v) ?pkg1 _ ?pkg1' _
    |-  context[interp_sval2 ?pkg1 ?pkg1' ?ext_args ?v]  =>
      let H' := fresh in
      pose_fresh_as H' (interp_sval2_taint_ok _ _ _ _ _ ext_args _ H); rewrite H'
  | H: forall (ext_args : list (string * vect_t)) (taint_base : se_taint_t),
        package_equiv_taint (compute_fancy_spred_taint' taint_base ?p1) ?pkg1 ?pkg2 ?pkg1' ?pkg2' ->
        interp_fancy_spred2' ?pkg1 ?pkg1' ext_args ?p1 <-> interp_fancy_spred2' ?pkg2 ?pkg2' ext_args ?p1,
    H1: package_equiv_taint (compute_fancy_spred_taint' _ ?p1) _ _ _ _,
    H2: context[interp_fancy_spred2' ?pkg1 ?pkg1' ?ext_args ?p1]  |- _ =>
    rewrite H with (1 := H1) in H2
  | H: forall (ext_args : list (string * vect_t)) (taint_base : se_taint_t),
        package_equiv_taint (compute_fancy_spred_taint' taint_base ?p1) ?pkg1 ?pkg2 ?pkg1' ?pkg2' ->
        interp_fancy_spred2' ?pkg1 ?pkg1' ext_args ?p1 <-> interp_fancy_spred2' ?pkg2 ?pkg2' ext_args ?p1,
    H1: package_equiv_taint (compute_fancy_spred_taint' _ ?p1) _ _ _ _
    |- context[interp_fancy_spred2' ?pkg1 ?pkg1' ?ext_args ?p1] =>
    rewrite H with (1 := H1)
  | H: _ \/ _ |- _ => destruct H
  end; eauto.
  all: t_interp_fancy_spred2_taint_ok.
  - specialize (H0 y). t_interp_fancy_spred2_taint_ok.
  - specialize (H0 x y). t_interp_fancy_spred2_taint_ok.
  - consider package_equiv_taint. simpl in H. consider package_equiv_taint'. propositional.
    simpl in *. step_package_equiv.
  - consider package_equiv_taint. simpl in H. consider package_equiv_taint'. propositional.
    simpl in *. step_package_equiv.
  - eapply package_equiv_taint_fold_exists' in H0; eauto. propositional; eauto.
    rewrite<-H; eauto.
  - eapply package_equiv_taint_fold_exists' in H0; eauto. propositional; eauto.
    rewrite H; eauto.
  - eapply package_equiv_taint_fold_exists' in H0; eauto. propositional; eauto.
    rewrite<-H; eauto.
  - eapply package_equiv_taint_fold_exists' in H0; eauto. propositional; eauto.
    rewrite H; eauto.
Qed.


Lemma forall_interp_fancy_spred2_package_equiv':
  forall pkg1 pkg2 pkg1' pkg2' (ps: list (fancy_spred)),
  package_equiv_taint (compute_fancy_spreds_taint ps) pkg1 pkg2 pkg1' pkg2' ->
  Forall (fun p => interp_fancy_spred2 pkg1 pkg1' p) ps ->
  Forall (fun p => interp_fancy_spred2 pkg2 pkg2' p) ps.
Proof.
  unfold compute_fancy_spreds_taint. intros *.
  generalize dependent empty_se_taint_t.
  induction ps; simpl; auto.
  intros * hequiv.
  intros. inversions H.
  constructor.
  - unfold interp_fancy_spred2.
    specialize package_equiv_taint_fold_exists with (l := (a::ps)). simpl. intros hfold.
    specialize hfold with (1 := hequiv) (p := a); propositional.
    erewrite<-interp_fancy_spred2_taint_ok; eauto.
  - eapply IHps; eauto.
Qed.


Lemma interp_sval2_same_pkg:
  forall v args pkg , interp_sval2 pkg pkg args v = interp_sval pkg args v.
Proof.
  induction v; intros; simpl; auto; try destruct machine_id; simpl; auto.
  all: repeat rewrite IHv; auto.
  all: repeat rewrite IHv1; repeat rewrite IHv2; auto.
Qed.


Lemma interp_fancy_spred2_same_pkg:
  forall p pkg, interp_fancy_spred2 pkg pkg p <->interp_fancy_spred pkg p.
Proof.
  unfold interp_fancy_spred2. unfold interp_fancy_spred.
  intros *. generalize (@nil (string * vect_t)) as ext_args.
  einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
      interp_fancy_spred2' pkg pkg ext_args (PBase p1) <-> interp_fancy_spred' pkg ext_args (PBase p1));
    simpl; try solve[split; auto]; split; auto; intros; simpl in *; destruct_match_pairs; try split; propositional.
  all: repeat rewrite IHf in *; repeat rewrite IHf0 in *; auto.
  all: repeat rewrite interp_sval2_same_pkg in *; auto.
  - rewrite<-IHf; auto.
  - rewrite<-IHf; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
  - rewrite<-H; auto.
  - rewrite H; auto.
Qed.

Lemma interp_spred2_same_pkg:
  forall p pkg, interp_spred2 pkg pkg p <-> interp_spred pkg p.
Proof.
  intros. specialize interp_fancy_spred2_same_pkg with (p := PBase p).
  unfold interp_fancy_spred2. unfold interp_fancy_spred. simpl.
  unfold interp_spred2, interp_spred. auto.
Qed.


Lemma forall_interp_fancy_spred_package_equiv':
  forall pkg1 pkg2 (ps: list (fancy_spred)),
  package_equiv_taint (compute_fancy_spreds_taint ps) pkg1 pkg2 pkg1 pkg2 ->
  Forall (fun p => interp_fancy_spred pkg1 p) ps ->
  Forall (fun p => interp_fancy_spred pkg2 p) ps.
Proof.
  intros. specialize forall_interp_fancy_spred2_package_equiv' with (1 := H).
  intros. rewrite Forall_forall.
  repeat rewrite Forall_forall in *.
  propositional. rewrite<-interp_fancy_spred2_same_pkg.
  apply H1; auto. propositional.
  rewrite interp_fancy_spred2_same_pkg.
  auto.
Qed.

Lemma package_equiv_taint_implies_fancy:
  forall pkg1 pkg2 pkg1' pkg2' ps,
  package_equiv_taint (compute_spreds_taint ps) pkg1 pkg2 pkg1' pkg2' ->
  package_equiv_taint (compute_fancy_spreds_taint (List.map PBase ps)) pkg1 pkg2 pkg1' pkg2'.
Proof.
  intros pkg1 pkg2 pkg1' pkg2' ps.
  consider compute_spreds_taint. consider compute_fancy_spreds_taint.
  generalize empty_se_taint_t as taint_t.
  induction ps; simpl; auto.
Qed.

Lemma forall_interp_spred2_package_equiv':
  forall pkg1 pkg2 pkg1' pkg2' (ps: list (spred)),
  package_equiv_taint (compute_spreds_taint ps) pkg1 pkg2 pkg1' pkg2' ->
  Forall (fun p => interp_spred2 pkg1 pkg1' p) ps ->
  Forall (fun p => interp_spred2 pkg2 pkg2' p) ps.
Proof.
  intros * hequiv hps.
  apply package_equiv_taint_implies_fancy in hequiv.
  specialize forall_interp_fancy_spred2_package_equiv' with (1 := hequiv); intros.
  assert_pre_and_specialize H.
  { rewrite Forall_map. auto. }
  repeat rewrite Forall_forall in *; propositional.
  specialize (H (PBase x)).
  apply H.
  rewrite in_map_iff. eauto.
Qed.

Lemma forall_interp_spred_package_equiv:
  forall pkg1 pkg2 (ps: list (spred)),
  package_equiv_taint (compute_spreds_taint ps) pkg1 pkg2 pkg1 pkg2 ->
  Forall (fun '(p) => interp_spred pkg1 p) ps ->
  Forall (fun '(p) => interp_spred pkg2 p) ps.
Proof.
  intros. specialize forall_interp_spred2_package_equiv' with (1 := H).
  intros. rewrite Forall_forall.
  repeat rewrite Forall_forall in *.
  propositional. rewrite<-interp_spred2_same_pkg.
  apply H1; auto. propositional.
  rewrite interp_spred2_same_pkg. auto.
Qed.

Lemma unfancy_correct' : forall impl_pkg (p : fancy_spred),
    (interp_fancy_spred impl_pkg p <-> interp_spred impl_pkg (unfancy p)).
Proof.
 intro. unfold interp_fancy_spred. unfold interp_spred.
 intros *. generalize (@nil (string * vect_t)) as ext_args. pattern p.
 einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    (interp_fancy_spred' impl_pkg ext_args (PBase p1) <-> interp_spred' impl_pkg ext_args (unfancy_e unfancy p1))
    ); simpl; try solve[split;auto]; auto; intros.
   - rewrite<-IHf. rewrite<-IHf0. simpl. split; auto.
   - rewrite<-IHf. rewrite<-IHf0. split; auto.
   - rewrite<-IHf. simpl. split; auto.
   - rewrite<-IHf. rewrite<-IHf0. split; auto.
   - split; destruct_match_pairs; subst; intros.
     + rewrite<-IHf. simpl. auto.
     + specialize (H y). rewrite<-IHf in H. propositional.
   - split; destruct_match_pairs; subst; intros.
     + rewrite<-IHf. simpl. auto.
     + specialize (H x y). rewrite<-IHf in H. propositional.
   - generalize dependent f. induction l; simpl; auto.
     + intros. split; auto.
     + intros. rewrite<-IHl; auto. split; intros; propositional.
       * split; auto. rewrite<-H. apply H0. auto.
       * destruct H1; subst; auto. rewrite H. auto.
   - generalize dependent f. induction l; simpl; auto.
     + intros. split; auto.
     + intros. rewrite<-IHl; auto. split; intros; propositional.
       * split; auto. rewrite<-H. apply H0. auto.
       * destruct H1; subst; auto. rewrite H. auto.
Qed.
Lemma unfancy_correct'2 : forall pkg1 pkg2 (p : fancy_spred),
    (interp_fancy_spred2 pkg1 pkg2 p <-> interp_spred2 pkg1 pkg2 (unfancy p)).
Proof.
 intro. unfold interp_fancy_spred2. unfold interp_spred2.
 intros *. generalize (@nil (string * vect_t)) as ext_args. pattern p.
 einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    (interp_fancy_spred2' pkg1 pkg2 ext_args (PBase p1) <-> interp_spred2' pkg1 pkg2 ext_args (unfancy_e unfancy p1))
    ); simpl; try solve[split;auto]; auto; intros.
   - rewrite<-IHf. rewrite<-IHf0. simpl. split; auto.
   - rewrite<-IHf. rewrite<-IHf0. split; auto.
   - rewrite<-IHf. simpl. split; auto.
   - rewrite<-IHf. rewrite<-IHf0. split; auto.
   - split; destruct_match_pairs; subst; intros.
     + rewrite<-IHf. simpl. auto.
     + specialize (H y). rewrite<-IHf in H. propositional.
   - split; destruct_match_pairs; subst; intros.
     + rewrite<-IHf. simpl. auto.
     + specialize (H x y). rewrite<-IHf in H. propositional.
   - generalize dependent f. induction l; simpl; auto.
     + intros. split; auto.
     + intros. rewrite<-IHl; auto. split; intros; propositional.
       * split; auto. rewrite<-H. apply H0. auto.
       * destruct H1; subst; auto. rewrite H. auto.
   - generalize dependent f. induction l; simpl; auto.
     + intros. split; auto.
     + intros. rewrite<-IHl; auto. split; intros; propositional.
       * split; auto. rewrite<-H. apply H0. auto.
       * destruct H1; subst; auto. rewrite H. auto.
Qed.


Lemma forall_unfancy_correct':
  forall {T: Type} impl_pkg (ps: list (T * fancy_spred)),
  Forall (fun '(_, p) => interp_fancy_spred impl_pkg p) ps <->
  Forall (fun '(_, p) => interp_spred impl_pkg (unfancy p)) ps.
Proof.
  intros.
  split.
  - apply Forall_impl. intros; destruct_match_pairs; subst. apply unfancy_correct'. auto.
  - apply Forall_impl. intros; destruct_match_pairs; simplify. apply unfancy_correct'. auto.
Qed.

Lemma forall_unfancy_correct'2:
  forall {T: Type} pkg1 pkg2 (ps: list (T * fancy_spred)),
  Forall (fun '(_, p) => interp_fancy_spred2 pkg1 pkg2 p) ps <->
  Forall (fun '(_, p) => interp_spred2 pkg1 pkg2 (unfancy p)) ps.
Proof.
  intros.
  split.
  - apply Forall_impl. intros; destruct_match_pairs; subst. apply unfancy_correct'2. auto.
  - apply Forall_impl. intros; destruct_match_pairs; simplify. apply unfancy_correct'2. auto.
Qed.

Lemma unfancy_correct : forall impl_pkg spec_pkg (p : fancy_spred),
    (interp_fancy_spred2 impl_pkg spec_pkg p <-> interp_spred2 impl_pkg spec_pkg (unfancy p)).
Proof.
intro. unfold interp_fancy_spred2. unfold interp_spred2.
intros *. generalize (@nil (string * vect_t)) as ext_args. pattern p.
einduction p using fancy_spred_mut with (P:= fun p1 =>
    forall ext_args,
    (interp_fancy_spred2' impl_pkg spec_pkg ext_args (PBase p1) <-> interp_spred2' impl_pkg spec_pkg ext_args (unfancy_e unfancy p1))
    ); simpl; try solve[split;auto]; auto; intros.
   - rewrite<-IHf. rewrite<-IHf0. simpl. split; auto.
   - rewrite<-IHf. rewrite<-IHf0. split; auto.
   - rewrite<-IHf. simpl. split; auto.
   - rewrite<-IHf. rewrite<-IHf0. split; auto.
   - split; destruct_match_pairs; subst; intros.
     + rewrite<-IHf. simpl. auto.
     + specialize (H y). rewrite<-IHf in H. propositional.
   - split; destruct_match_pairs; subst; intros.
     + rewrite<-IHf. simpl. auto.
     + specialize (H x y). rewrite<-IHf in H. propositional.
   - generalize dependent f. induction l; simpl; auto.
     + intros. split; auto.
     + intros. rewrite<-IHl; auto. split; intros; propositional.
       * split; auto. rewrite<-H. apply H0. auto.
       * destruct H1; subst; auto. rewrite H. auto.
   - generalize dependent f. induction l; simpl; auto.
     + intros. split; auto.
     + intros. rewrite<-IHl; auto. split; intros; propositional.
       * split; auto. rewrite<-H. apply H0. auto.
       * destruct H1; subst; auto. rewrite H. auto.
Qed.

Definition symbolic_evaluate_file_success_single
  (machine: machine_t) schedule (assumes asserts: list spred) : Prop :=
  forall sigma st st' ext_log' opt_mid_log,
  let pkg :=
    {| pkg_machine := machine;
       pkg_init_st := st;
       pkg_sigma := sigma;
       pkg_mid_st := None;
       pkg_final_st := st';
       pkg_mid_ext_log := opt_mid_log;
       pkg_ext_log' := ext_log';
    |} in
  (* Forall (fun q => interp_qspred2 (impl_pkg) (spec_pkg) q ) ext_assumptions -> *)
  Forall (fun p => interp_spred (pkg) p ) assumes ->
  machine_to_prop machine schedule sigma st st' ext_log' ->
  Forall (fun p => interp_spred (pkg) p ) asserts.

Definition symbolic_evaluate_file_success_product
  (impl spec: machine_t) impl_sched spec_sched (* (ext_assumptions: list quantified_spred)  *)(assumes asserts: list spred) : Prop :=
  forall impl_sigma spec_sigma impl_st spec_st impl_st' spec_st' impl_ext_log' spec_ext_log',
  let impl_pkg :=
    {| pkg_machine := impl;
       pkg_init_st := impl_st;
       pkg_sigma := impl_sigma;
       pkg_mid_st := None;
       pkg_final_st := impl_st';
       pkg_mid_ext_log := None;
       pkg_ext_log' := impl_ext_log';
    |} in
  let spec_pkg :=
    {| pkg_machine := spec;
       pkg_init_st := spec_st;
       pkg_sigma := spec_sigma;
       pkg_mid_st := None;
       pkg_final_st := spec_st';
       pkg_mid_ext_log := None;
       pkg_ext_log' := spec_ext_log';
    |} in
  (* Forall (fun q => interp_qspred2 (impl_pkg) (spec_pkg) q ) ext_assumptions -> *)
  Forall (fun p => interp_spred2 (impl_pkg) (spec_pkg) p ) assumes ->
  machine_to_prop impl impl_sched impl_sigma impl_st impl_st' impl_ext_log' ->
  machine_to_prop spec spec_sched spec_sigma spec_st spec_st' spec_ext_log' ->
  Forall (fun p => interp_spred2 (impl_pkg) (spec_pkg) p ) asserts.

Axiom WF_single_file : file_t -> bool.
Axiom WF_product_file : file_t -> bool.

Definition WF_abstract_state_set
  (machine: machine_t) (sigma: ext_sigma_t) (st mid_st st': state_t) (mid_ext_log ext_log': ext_log_t) : Prop :=
  WF_ext_sigma (strip_dbg_ext_types machine.(file_ext_sigma)) sigma /\
  WF_state (strip_dbg_reg_types machine.(file_registers)) st /\
  WF_state (strip_dbg_reg_types machine.(file_registers)) mid_st /\
  WF_state (strip_dbg_reg_types machine.(file_registers)) st' /\
  WF_ext_log (strip_dbg_ext_types machine.(file_ext_sigma)) mid_ext_log /\
  WF_ext_log (strip_dbg_ext_types machine.(file_ext_sigma)) ext_log'.


Definition symbolic_evaluate_file_success_abstract_single
  (machine: machine_t) (* (ext_assumptions: list quantified_spred)  *)(assumes asserts: list spred) : Prop :=
  forall sigma st st' ext_log' mid_ext_log mid_st,
  let pkg :=
    {| pkg_machine := machine;
       pkg_init_st := st;
       pkg_sigma := sigma;
       pkg_mid_st := Some mid_st;
       pkg_final_st := st';
       pkg_mid_ext_log := Some mid_ext_log;
       pkg_ext_log' := ext_log';
    |} in
  Forall (fun p => interp_spred (pkg) p ) assumes ->
  WF_abstract_state_set machine sigma st mid_st st' mid_ext_log ext_log' ->
  Forall (fun p => interp_spred (pkg) p ) asserts.

Definition symbolic_evaluate_file_success_abstract_product
  (impl spec: machine_t) (assumes asserts: list spred) : Prop :=
  forall impl_sigma spec_sigma impl_st spec_st impl_st' spec_st' impl_ext_log' spec_ext_log' impl_mid spec_mid impl_ext_mid spec_ext_mid,
  let impl_pkg :=
    {| pkg_machine := impl;
       pkg_init_st := impl_st;
       pkg_mid_st := Some impl_mid;
       pkg_sigma := impl_sigma;
       pkg_final_st := impl_st';
       pkg_mid_ext_log := Some impl_ext_mid;
       pkg_ext_log' := impl_ext_log';
    |} in
  let spec_pkg :=
    {| pkg_machine := spec;
       pkg_init_st := spec_st;
       pkg_sigma := spec_sigma;
       pkg_mid_st := Some spec_mid;
       pkg_final_st := spec_st';
       pkg_mid_ext_log := Some spec_ext_mid;
       pkg_ext_log' := spec_ext_log';
    |} in
  (* Forall (fun q => interp_qspred2 (impl_pkg) (spec_pkg) q ) ext_assumptions -> *)
  Forall (fun p => interp_spred2 (impl_pkg) (spec_pkg) p ) assumes ->
  WF_abstract_state_set impl impl_sigma impl_st impl_mid impl_st' impl_ext_mid impl_ext_log' ->
  WF_abstract_state_set spec spec_sigma spec_st spec_mid spec_st' spec_ext_mid spec_ext_log' ->
  Forall (fun p => interp_spred2 (impl_pkg) (spec_pkg) p ) asserts.

Axiom symbolic_evaluate_file_success :
  forall (file: file_t),
  match file.(file_machines) with
  | Single machine schedule => WF_single_file file = true ->
                   symbolic_evaluate_file_success_single
                    machine
                    schedule
                    file.(file_assumptions)
                    file.(file_assertions)
  | Product impl spec impl_sched spec_sched =>
      WF_product_file file = true ->
      symbolic_evaluate_file_success_product
        impl spec impl_sched spec_sched
        file.(file_assumptions)
        file.(file_assertions)
  | AbstractSingle machine =>
      WF_single_file file = true ->
      symbolic_evaluate_file_success_abstract_single machine file.(file_assumptions) file.(file_assertions)
  | AbstractProduct impl spec =>
      WF_product_file file = true ->
      symbolic_evaluate_file_success_abstract_product
        impl spec file.(file_assumptions) file.(file_assertions)
  end.

  Lemma interp_sval_uses_mid_impl_only_correct:
    forall impl_pkg spec_pkg ext_args v,
    sval_uses_mid_only MachineImpl v = true ->
    interp_sval2 impl_pkg spec_pkg ext_args v = interp_sval impl_pkg ext_args v.
  Proof.
    induction v; simpl in *;  propositional;
      try erewrite IHv; try erewrite IHv1; try erewrite IHv2;
    repeat match goal with
    | H: false = true |- _ => discriminate
    | H: _ && _ = true |- _ => rewrite andb_true_iff in H
    | |- _ => progress (simplify; propositional; eauto)
    end.
  Qed.

  Lemma interp_sval_uses_mid_spec_only_correct:
    forall impl_pkg spec_pkg ext_args v,
    sval_uses_mid_only MachineSpec v = true ->
    interp_sval2 impl_pkg spec_pkg ext_args v = interp_sval spec_pkg ext_args v.
  Proof.
    induction v; simpl in *;  propositional;
      try erewrite IHv; try erewrite IHv1; try erewrite IHv2;
    repeat match goal with
    | H: false = true |- _ => discriminate
    | H: _ && _ = true |- _ => rewrite andb_true_iff in H
    | |- _ => progress (simplify; propositional; eauto)
    end.
  Qed.


  Lemma interp_fancy_spred2_using_impl_only:
    forall impl_pkg spec_pkg p,
    fancy_spred_uses_mid_only MachineImpl p = true ->
    interp_fancy_spred2 impl_pkg spec_pkg p <->
    interp_fancy_spred impl_pkg p.
  Proof.
    intros. unfold interp_fancy_spred. unfold interp_fancy_spred2. revert H.
    generalize (@nil (string * vect_t)) as ext_args.
    pattern p.
    einduction p using fancy_spred_mut with (P:= fun p1 =>
      forall ext_args,
        fancy_spred_uses_mid_only MachineImpl (PBase p1) = true ->
          interp_fancy_spred2' impl_pkg spec_pkg ext_args (PBase p1) <->
          interp_fancy_spred' impl_pkg ext_args (PBase p1)); simpl in *; auto;
    repeat match goal with
    | H: forall _, _ -> interp_spred2' _ _ _ _ <-> interp_spred' _ _ _ |- _ =>
        rewrite<-H in * by auto
    | H: sval_uses_mid_only _ ?v1 = true |- context[interp_sval _ _ ?v1] =>
        rewrite<-interp_sval_uses_mid_impl_only_correct with (1 := H) (spec_pkg := spec_pkg)
    | |- _ => common_tac
    end.
    - rewrite IHf by auto; auto.
    - rewrite IHf by auto. auto.
    - rewrite<-H; auto.
    - rewrite H; auto.
    - rewrite<-H; auto.
    - rewrite H; auto.
  Qed.

  Lemma interp_fancy_spred2_using_spec_only:
    forall impl_pkg spec_pkg p,
    fancy_spred_uses_mid_only MachineSpec p = true ->
    interp_fancy_spred2 impl_pkg spec_pkg p <->
    interp_fancy_spred spec_pkg p.
  Proof.
    intros. unfold interp_fancy_spred. unfold interp_fancy_spred2. revert H.
    generalize (@nil (string * vect_t)) as ext_args.
    pattern p.
    einduction p using fancy_spred_mut with (P:= fun p1 =>
      forall ext_args,
        fancy_spred_uses_mid_only MachineSpec (PBase p1) = true ->
          interp_fancy_spred2' impl_pkg spec_pkg ext_args (PBase p1) <->
          interp_fancy_spred' spec_pkg ext_args (PBase p1)); simpl in *; auto;
    repeat match goal with
    | H: forall _, _ -> interp_spred2' _ _ _ _ <-> interp_spred' _ _ _ |- _ =>
        rewrite<-H in * by auto
    | H: sval_uses_mid_only _ ?v1 = true |- context[interp_sval _ _ ?v1] =>
        rewrite<-interp_sval_uses_mid_spec_only_correct with (1 := H) (impl_pkg := impl_pkg)
    | |- _ => common_tac
    end.
    - rewrite IHf by auto; auto.
    - rewrite IHf by auto. auto.
    - rewrite<-H; auto.
    - rewrite H; auto.
    - rewrite<-H; auto.
    - rewrite H; auto.
  Qed.

  Lemma normalize_sval_equiv : forall v, sval_equiv v (normalize_mid_sval v) = true.
  Proof.
    induction v; simpl;
      repeat match goal with
      | |- _ && _ = true => rewrite andb_true_iff
      | |- _ /\ _ => split
      | |- beq_dec ?x ?x = true => apply beq_dec_refl
      end; auto.
  Qed.

  Lemma normalize_fancy_spred_equiv:
    forall p, fancy_spred_equiv p (normalize_mid_fancy_spred p) = true.
  Proof.
    einduction p using fancy_spred_mut with (P:= fun p1 =>
       fancy_spred_equiv (PBase p1) (normalize_mid_fancy_spred (PBase p1)) = true); simpl; auto;
      repeat match goal with
      | |- _ && _ = true => rewrite andb_true_iff
      | |- _ /\ _ => split
      | |- sval_equiv ?v (normalize_mid_sval ?v) = true =>
          apply normalize_sval_equiv
      | |- beq_dec ?x ?x = true => apply beq_dec_refl
      | |- forallb _ _ = true => rewrite forallb_forall
      | |- _ => common_tac
      end.
    - destruct b; auto.
  Qed.

  Lemma sval_equiv_correct:
    forall v1 pkg ext_args v2,
      sval_equiv v1 v2 = true ->
      interp_sval pkg ext_args v1 = interp_sval pkg ext_args v2.
  Proof.
    induction v1; simpl; intros * hequiv; bash_destruct hequiv; simplify; auto;
      repeat match goal with
             | H: forall _ _ _, sval_equiv ?v1 _ = true -> interp_sval _ _ ?v1 = interp_sval _ _ _,
               H1: sval_equiv ?v1 _ = true
               |- context[interp_sval _ _ ?v1] =>
               rewrite H with (1 := H1)
             | |- _ => common_tac
             end.
  Qed.

  Lemma fancy_spred_equiv_correct:
    forall pkg p1 p2,
    fancy_spred_equiv p1 p2 = true ->
    interp_fancy_spred pkg p1 <-> interp_fancy_spred pkg p2.
  Proof.
    intro pkg.  unfold interp_fancy_spred. intros *.
    generalize (@nil (string * vect_t)) as ext_args.
    generalize dependent p2.
    einduction p1 using fancy_spred_mut with (P:= fun p1 =>
      forall p2 ext_args ,
      fancy_spred_equiv (PBase p1) p2 = true ->
      interp_fancy_spred' pkg ext_args (PBase p1) <-> interp_fancy_spred' pkg ext_args p2); simpl;
      intros * Hequiv; bash_destruct Hequiv; simpl in *; auto; destruct_match_pairs;
      repeat (match goal with
      | H: spred_equiv ?p0 ?p1 = true,
        H1: forall _ _, _ = true -> interp_spred' _ _ ?p0 <-> interp_fancy_spred' _ _ _
        |- interp_spred' _ _ ?p1 =>
        setoid_rewrite<-H1 with (p2 := PBase p1)
      | H: forall _ _, _ = true -> interp_spred' _ _ ?p <-> interp_fancy_spred' _ _ _,
        H1: spred_equiv ?p ?q  = true |- _ =>
          rewrite H with (p2 := PBase q) by auto
      | H: sval_equiv ?v1 _ = true |- context[interp_sval _ _ ?v1] =>
        rewrite sval_equiv_correct with (1 := H)
      (* | H: ?x -> ?y |- ?y => apply H *)
      | |- _ => common_tac
      end; hnf); try reflexivity.
    - split; propositional.
      + setoid_rewrite<-IHf with (p2 := PBase s0); auto.
      + rewrite IHf with (p2 := PBase s0); simpl; auto.
    - split; propositional.
      + setoid_rewrite<-IHf with (p2 := PBase s0); auto.
      + rewrite IHf with (p2 := PBase s0); simpl; auto.
    - split; propositional.
      + setoid_rewrite<-H with (p2 := (f0 x)); eauto.
      + rewrite H; eauto.
    - split; propositional.
      + setoid_rewrite<-H with (p2 := (f0 x)); eauto.
      + rewrite H; eauto.
  Qed.
Lemma interp_fancy_spred'_PBase:
  forall pkg ext_args e,
  interp_fancy_spred' pkg ext_args (PBase e) <-> interp_spred' pkg ext_args e.
Proof.
  reflexivity.
Qed.
Lemma interp_spred'_PImpl:
  forall pkg ext_args e1 e2,
  interp_spred' pkg ext_args (PImpl e1 e2) <-> (interp_spred' pkg ext_args e1 -> interp_spred' pkg ext_args e2).
Proof.
  reflexivity.
Qed.

Lemma interp_spred'_PAnd:
  forall pkg ext_args p1 p2,
    interp_spred' pkg ext_args (PAnd p1 p2) <->
    interp_spred' pkg ext_args p1 /\ interp_spred' pkg ext_args p2.
Proof.
  reflexivity.
Qed.

Lemma interp_spred2'_PAnd:
  forall pkg1 pkg2 ext_args p1 p2,
    interp_spred2' pkg1 pkg2 ext_args (PAnd p1 p2) <->
    interp_spred2' pkg1 pkg2 ext_args p1 /\ interp_spred2' pkg1 pkg2 ext_args p2.
Proof.
  reflexivity.
Qed.

Lemma interp_spred'_PFancy:
  forall pkg ext_args p,
    interp_spred' pkg ext_args (PFancy p) <->
    interp_fancy_spred' pkg ext_args p.
Proof.
  reflexivity.
Qed.

Lemma flatten_spred_ands_correct:
  forall pkg s,
  Forall (fun p : spred => interp_spred pkg p) (flatten_spred_ands s) <->
  interp_spred pkg s.
Proof.
  induction s; simpl; try rewrite Forall_single; try reflexivity.
  setoid_rewrite interp_spred'_PAnd. rewrite Forall_app.
  rewrite IHs1. rewrite IHs2. split; auto.
Qed.

Lemma flatten_spred_ands_correct2:
  forall pkg1 pkg2 s,
  Forall (fun p : spred => interp_spred2 pkg1 pkg2 p) (flatten_spred_ands s) <->
  interp_spred2 pkg1 pkg2 s.
Proof.
  induction s; simpl; try rewrite Forall_single; try reflexivity.
  setoid_rewrite interp_spred2'_PAnd. rewrite Forall_app.
  rewrite IHs1. rewrite IHs2. split; auto.
Qed.


Lemma forall_flatten_spred_ands_correct:
  forall T X pkg (ps: list (T * X)) f,
  Forall (fun p : spred => interp_spred pkg p)
    (List.concat (map (fun '(_, p) => flatten_spred_ands (f p)) ps)) <->
  Forall (fun '(_, p) => interp_spred pkg (f p)) ps.
Proof.
  induction ps.
  - repeat rewrite Forall_forall. simpl. split; propositional.
  - intros. simpl. destruct_match_pairs. subst. rewrite Forall_app.
    rewrite flatten_spred_ands_correct. rewrite IHps.
    rewrite Forall_cons_iff. reflexivity.
Qed.

Lemma forall_flatten_spred_ands_correct2:
  forall T X pkg1 pkg2 (ps: list (T * X)) f,
  Forall (fun p : spred => interp_spred2 pkg1 pkg2 p)
    (List.concat (map (fun '(_, p) => flatten_spred_ands (f p)) ps)) <->
  Forall (fun '(_, p) => interp_spred2 pkg1 pkg2 (f p)) ps.
Proof.
  induction ps.
  - repeat rewrite Forall_forall. simpl. split; propositional.
  - intros. simpl. destruct_match_pairs. subst. rewrite Forall_app.
    rewrite flatten_spred_ands_correct2. rewrite IHps.
    rewrite Forall_cons_iff. reflexivity.
Qed.


Lemma WF_state_length:
  forall (reg_types : reg_types_t) (st : state_t) (idx : Syntax.reg_t) len',
  WF_state reg_types st ->
  match lookup_reg_type reg_types idx with
  | (Some len) =>  beq_dec len len'
  | _ => false
  end = true ->
  Datatypes.length st.[idx] = len'.
Proof.
  consider WF_state. intros. specialize (H idx).
  unfold SortedExtFnEnv.EqDec_KeyT in *. unfold OrderedN.EqDec_T in *.
  bash_destruct H0. simplify. consider get_reg. unfold unsafe_get_reg, r_get_reg.
  simpl_match. auto.
Qed.
Lemma forall_unfancy_correct:
  forall {T: Type} impl_pkg spec_pkg (ps: list (T * fancy_spred)),
  Forall (fun '(_, p) => interp_fancy_spred2 impl_pkg spec_pkg p) ps <->
  Forall (fun '(_, p) => interp_spred2 impl_pkg spec_pkg p) (map (fun '(x,p) => (x, unfancy p)) ps).
Proof.
  intros. rewrite Forall_map.
  split.
  - apply Forall_impl. intros; destruct_match_pairs; subst. apply unfancy_correct. auto.
  - apply Forall_impl. intros; destruct_match_pairs; simplify. apply unfancy_correct. auto.
Qed.
Lemma Forall_interp_fancy2_rewrite:
  forall {A} impl_pkg spec_pkg (asserts: list (A * fancy_spred)),
  Forall (fun p => interp_spred2 (impl_pkg) (spec_pkg) p )
        (map (fun '(_, p) => (unfancy p)) asserts) <->
  Forall (fun '(_, p) => interp_fancy_spred2 impl_pkg spec_pkg p) asserts.
Proof.
  intros. repeat rewrite Forall_forall. split; intros; destruct_match_pairs; subst.
  - rewrite unfancy_correct. apply H. rewrite in_map_iff. exists (a,f); auto.
  - rewrite in_map_iff in *. propositional. specialize (H _ H2).
    destruct_match_pairs; subst. rewrite<-unfancy_correct. auto.
Qed.

Lemma forall_preprocess_fancy_spreds_correct:
  forall T pkg (ps: list (T * fancy_spred)) ,
  Forall (fun p : spred => interp_spred pkg p)
         (preprocess_fancy_spreds ps) <->
  Forall (fun '(_, p) => interp_fancy_spred pkg (p)) ps.
Proof.
  intros. consider @preprocess_fancy_spreds.
  rewrite forall_flatten_spred_ands_correct.
  rewrite forall_unfancy_correct'. reflexivity.
Qed.

Lemma forall_preprocess_fancy_spreds_correct2:
  forall T pkg1 pkg2 (ps: list (T * fancy_spred)) ,
  Forall (fun p : spred => interp_spred2 pkg1 pkg2 p)
         (preprocess_fancy_spreds ps) <->
  Forall (fun '(_, p) => interp_fancy_spred2 pkg1 pkg2 (p)) ps.
Proof.
  intros. consider @preprocess_fancy_spreds.
  rewrite forall_flatten_spred_ands_correct2.
  rewrite forall_unfancy_correct'2. reflexivity.
Qed.
Lemma forall_interp_spred_preprocess_app_iff:
  forall A pkg (xs ys: list (A * fancy_spred)),
  Forall (fun p : spred => interp_spred pkg p) (preprocess_fancy_spreds (xs ++ ys)) <->
  Forall (fun p : spred => interp_spred pkg p)
    (preprocess_fancy_spreds xs ++ preprocess_fancy_spreds ys).
Proof.
  intros. consider @preprocess_fancy_spreds.
  induction xs; simpl; auto.
  - split; auto.
  - destruct_match_pairs; subst.
    repeat rewrite Forall_app.
    rewrite IHxs. rewrite Forall_app. split; propositional; split_ands_in_goal; auto.
Qed.

  Lemma preprocess_fancy_spreds_map_fst_equiv:
    forall {A B: Type} (ps: list (A * fancy_spred)) (f: A -> B),
    preprocess_fancy_spreds (map_fst f ps) = preprocess_fancy_spreds (ps).
  Proof.
    unfold preprocess_fancy_spreds. unfold map_fst.
    intros. rewrite map_map.  f_equal.
    apply map_ext. intros; destruct_match_pairs; auto. subst. simplify. auto.
  Qed.

  Lemma interp_spred2_using_impl_only:
    forall impl_pkg spec_pkg p,
    spred_uses_mid_only MachineImpl p = true ->
    interp_spred2 impl_pkg spec_pkg p <-> interp_spred impl_pkg p.
  Proof.
    intros. eapply interp_fancy_spred2_using_impl_only with (p := PBase p) in H; eauto.
  Qed.

  Lemma Forall_interp_spred2_using_impl_only:
    forall impl_pkg spec_pkg ps,
    forallb (spred_uses_mid_only MachineImpl) ps = true ->
    Forall (interp_spred2 impl_pkg spec_pkg) ps <->
    Forall (interp_spred impl_pkg) ps.
  Proof.
    intros *. rewrite forallb_forall.
    intros; split; repeat rewrite Forall_forall; intros; eapply interp_spred2_using_impl_only; eauto.
  Qed.

End Interp.
Ltac replace_init_st_in H v :=
  match type of H with
  | Forall (fun p => interp_spred ?package p) _ =>
    apply forall_interp_spred_package_equiv with
      (pkg2 := set_init_st package v) in H
  end.
Ltac replace_init_st v :=
  match goal with
  | |- Forall (fun p => interp_spred ?package p) _ =>
    apply forall_interp_spred_package_equiv with
      (pkg1 := set_init_st package v)
  end.

Ltac replace_mid_st_in H v :=
  match type of H with
  | Forall (fun p => interp_spred ?package p) _ =>
    apply forall_interp_spred_package_equiv with
      (pkg2 := set_mid_st package v) in H
  end.
 Ltac replace_final_st_in H v :=
  match type of H with
  | Forall (fun p => interp_spred ?package p) _ =>
    apply forall_interp_spred_package_equiv with
      (pkg2 := set_final_st package v) in H
  end.
Ltac replace_final_st v :=
  match goal with
  | |- Forall (fun p => interp_spred ?package p) _ =>
    apply forall_interp_spred_package_equiv with
      (pkg1 := set_final_st package v)
  end.
Ltac replace_mid_ext_in H v :=
  match type of H with
  | Forall (fun p => interp_spred ?package p) _ =>
    apply forall_interp_spred_package_equiv with
      (pkg2 := set_mid_ext_log package v) in H
  end.
Ltac replace_mid_ext v :=
  match goal with
  | |- Forall (fun p => interp_spred ?package p) _ =>
    apply forall_interp_spred_package_equiv with
      (pkg1 := set_mid_ext_log package v)
  end.
Ltac solve_package_equiv:=
  constructor; unfold package_equiv_taint'; split_ands_in_goal;
    (solve[left;auto] || (right; vm_compute; reflexivity)).

 Ltac replace_final_ext_in H v :=
  match type of H with
  | Forall (fun p => interp_spred ?package p) _ =>
    apply forall_interp_spred_package_equiv with
      (pkg2 := set_ext_log' package v) in H
  end.
Ltac replace_final_ext v :=
  match goal with
  | |- Forall (fun p => interp_spred ?package p) _ =>
    apply forall_interp_spred_package_equiv with
      (pkg1 := set_ext_log' package v)
  end.

Ltac replace_final_st_with_mid :=
  match goal with
  | |- Forall (fun _ => interp_spred ?pkg _) _  =>
      let x := eval hnf in pkg.(pkg_mid_st) in
      match x with
      | Some ?v =>
          replace_final_st v; [solve_package_equiv | ]
      end;
      let q := fresh in
      rewrite Lift_Forall with (g := replace_spred_mid_reg_with_final);
      [ | solve[ intro q; apply replace_fancy_spred_mid_reg_with_final_correct with (p := PBase q); auto] ]
  end.
Ltac replace_final_ext_with_mid :=
  match goal with
  | |- Forall (fun _ => interp_spred ?pkg _) _  =>
      let x := eval hnf in pkg.(pkg_mid_ext_log) in
      match x with
      | Some ?v =>
          replace_final_ext v; [solve_package_equiv | ]
      end;
      let q := fresh in
      rewrite Lift_Forall with (g := replace_spred_mid_ext_with_final);
      [ | solve[ intro q; apply replace_fancy_spred_mid_ext_with_final_correct with (p := PBase q); auto] ]
  end.
Ltac replace_final_ext_with_committed_in H :=
  match type of H with
  | Forall (fun _ => interp_spred ?pkg _) _  =>
      let q := fresh in
      rewrite Lift_Forall with (g := replace_spred_final_ext_with_committed) in H;
      [ | solve[ intro q; apply replace_fancy_spred_final_ext_with_committed_correct with (p := PBase q); auto] ]
  end.

Ltac replace_final_ext_with_committed :=
  match goal with
  | |- Forall (fun _ => interp_spred ?pkg _) _  =>
      let q := fresh in
      rewrite Lift_Forall with (g := replace_spred_final_ext_with_committed);
      [ | solve[ intro q; apply replace_fancy_spred_final_ext_with_committed_correct with (p := PBase q); auto] ]
  end.

Lemma forall_interp_spred2_preprocess_app_iff:
  forall {_ext_fn_tys : list (Syntax.ext_fn_t * (nat * nat))}
    {unsafe_lookup_dstruct_fields : struct_env_t -> debug_id_ty -> list (Syntax.dstruct_field_t * nat)}
    (A : Type) (pkg1 pkg2  : machine_pkg) (xs ys : list (A * fancy_spred)),
  Forall (fun p : spred => @SymbolicInterp.interp_spred2 _ext_fn_tys unsafe_lookup_dstruct_fields pkg1 pkg2 p)
          (preprocess_fancy_spreds (xs ++ ys)) <->
  Forall (fun p : spred => @SymbolicInterp.interp_spred2 _ext_fn_tys unsafe_lookup_dstruct_fields pkg1 pkg2 p)
    (preprocess_fancy_spreds xs ++ preprocess_fancy_spreds ys).
Proof.
  intros. consider @preprocess_fancy_spreds.
  induction xs; simpl; auto.
  - split; auto.
  - destruct_match_pairs; subst.
    repeat rewrite Forall_app.
    rewrite IHxs. rewrite Forall_app. split; propositional; split_ands_in_goal; auto.
Qed.
Ltac replace_final_st2 v1 v2 :=
  match goal with
  | |- Forall (fun p => interp_spred2 ?package1 ?package2 p) _ =>
        apply forall_interp_spred2_package_equiv' with
      (pkg1 := set_final_st package1 v1)
      (pkg1' := set_final_st package2 v2)
  end.
Ltac replace_final_st_with_mid2 :=
  match goal with
  | |- Forall (fun _ => interp_spred2 ?pkg1 ?pkg2  _) _  =>
      let x1 := eval hnf in pkg1.(pkg_mid_st) in
      let x2 := eval hnf in pkg2.(pkg_mid_st) in
      match x1 with
      | Some ?v1 =>
          match x2 with
          | Some ?v2 =>
              replace_final_st2 v1 v2; [solve_package_equiv | ]
          end
      end;
        rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_impl_mid_reg_with_final));
        [ | solve[ intros; apply replace_spred2_impl_mid_reg_with_final_correct; auto] ];
        rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_spec_mid_reg_with_final));
        [ | intros; apply replace_spred2_spec_mid_reg_with_final_correct; auto ]
  end.
Ltac replace_final_ext2 v1 v2 :=
  match goal with
  | |- Forall (fun p => interp_spred2 ?package1 ?package2 p) _ =>
        apply forall_interp_spred2_package_equiv' with
      (pkg1 := set_ext_log'  package1 v1)
      (pkg1' := set_ext_log' package2 v2)
  end.
Ltac replace_final_ext_with_mid2 :=
  match goal with
  | |- Forall (fun _ => interp_spred2 ?pkg1 ?pkg2  _) _  =>
      let x1 := eval hnf in pkg1.(pkg_mid_ext_log) in
      let x2 := eval hnf in pkg2.(pkg_mid_ext_log) in
        match x1 with
        | Some ?v1 =>
            match x2 with
            | Some ?v2 =>
                replace_final_ext2 v1 v2 ; [solve_package_equiv | ];
                rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_impl_mid_ext_with_final));
                [ | solve[ intros; apply replace_spred2_impl_mid_ext_with_final_correct; auto] ];
                rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_spec_mid_ext_with_final));
                [ | intros; apply replace_spred2_spec_mid_ext_with_final_correct; auto ]
            end
         end
  end.
Ltac replace_init_st2 v1 v2 :=
  match goal with
  | |- Forall (fun p => interp_spred2 ?package1 ?package2 p) _ =>
        apply forall_interp_spred2_package_equiv' with
      (pkg1 := set_init_st package1 v1)
      (pkg1' := set_init_st package2 v2)
  end.
Ltac replace_init_st_with_mid2 :=
  match goal with
  | |- Forall (fun _ => interp_spred2 ?pkg1 ?pkg2  _) _  =>
      let x1 := eval hnf in pkg1.(pkg_mid_st) in
      let x2 := eval hnf in pkg2.(pkg_mid_st) in
      match x1 with
      | Some ?v1 =>
          match x2 with
          | Some ?v2 =>
              replace_init_st2 v1 v2; [solve_package_equiv | ]
          end
      end;
      rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_impl_mid_reg_with_init));
      [ | solve[ intros; apply replace_spred2_impl_mid_reg_with_init_correct; auto] ];
      rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_spec_mid_reg_with_init));
      [ | intros; apply replace_spred2_spec_mid_reg_with_init_correct; auto ]
  end.
