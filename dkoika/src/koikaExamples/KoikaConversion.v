Require Import koika.Frontend.
Require Koika.Frontend.
Require Import Koika.Interop.
Require Koika.Syntax.
Require Import koika.Frontend.

Record koika_pkg_t {T: Type} {rule_name_t: Type} :=
{ pkg_reg_types: @reg_types_t T
; pkg_reg_inits: list (T * list bool)
; pkg_ext_fn_tys: @ext_fn_types_t T
; pkg_int_fns: @int_fn_env_t T (@action T)
; pkg_struct_defs: @struct_env_t T
; pkg_rules: rule_name_t -> @Syntax.rule T
; pkg_scheduler: @scheduler rule_name_t
; pkg_rl_external: rule_name_t -> bool
; pkg_module_name: string
}.

  Inductive TC_Strategy := TC_conv | TC_vm | TC_native.
  Ltac _tc_strategy := exact TC_vm.
  Ltac _extract_success r :=
    let strategy := constr:(ltac:(_tc_strategy)) in
    let eq_pr :=
        match strategy with
        | TC_conv => constr:(@eq_refl bool true : is_success r = true)
        | TC_vm => constr:(@eq_refl bool true <: is_success r = true)
        | TC_native => constr:(@eq_refl bool true <<: is_success r = true)
        end in
    exact (extract_success r eq_pr).

Section ExtractStructs.
  Context {reg_t ext_fn_t rule_name_t: Type}.
  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).
  Context (rules: rule_name_t -> Frontend.rule R Sigma).

  Notation taction := (Koika.Frontend.action R Sigma).
  Definition add_tau (tau: type) (structs: list struct_sig) : list struct_sig :=
    match tau with
    | Types.struct_t sig => if existsb (beq_dec sig) structs then structs else sig::structs
    | _ => structs
    end.

  Fixpoint add_structs (structs: list struct_sig) {sig: tsig var_t} {tau: type} (a: taction sig tau)
    : (list struct_sig) :=
    let structs := add_tau tau structs in
    match a with
    | TypedSyntax.Fail _ => structs
    | TypedSyntax.Var _ => structs
    | TypedSyntax.Const _ => structs
    | TypedSyntax.Assign v ex => add_structs structs ex
    | TypedSyntax.Seq a1 a2 =>
        add_structs (add_structs structs a1) a2
    | TypedSyntax.Bind v ex body =>
        add_structs (add_structs structs ex) body
    | TypedSyntax.If cond tbranch fbranch =>
        add_structs (add_structs (add_structs structs cond) tbranch) fbranch
    | TypedSyntax.Read p idx => structs
    | TypedSyntax.Write p idx value =>
        add_structs structs value
    | TypedSyntax.InternalCall fn args body =>
        add_structs (cfoldl (fun k v acc => add_structs acc v) args structs) body
    | TypedSyntax.ExternalCall fn arg =>
        add_structs structs arg
    | TypedSyntax.Unop fn arg => add_structs structs arg
    | TypedSyntax.Binop fn arg1 arg2 => add_structs (add_structs structs arg1) arg2
    | TypedSyntax.APos _ a => add_structs structs a
    end.

  Definition get_schedule_structs (sched: list (Frontend.rule R Sigma)) : list struct_sig :=
    fold_left (fun acc rl => add_structs  acc rl) sched [].

  Fixpoint get_scheduler_structs'
    (acc: list struct_sig) (sched: Syntax.scheduler Frontend.pos_t rule_name_t) : list struct_sig :=
    match sched with
    | Syntax.Done => acc
    | Syntax.Cons r s => get_scheduler_structs' (add_structs acc (rules r)) s
    | Syntax.Try r s1 s2 => get_scheduler_structs' (get_scheduler_structs' (add_structs acc (rules r)) s1) s2
    | Syntax.SPos _ s => get_scheduler_structs' acc s
    end.

  Definition get_scheduler_structs
    (sched: Syntax.scheduler Frontend.pos_t rule_name_t) : list struct_sig :=
    get_scheduler_structs' [] sched.


End ExtractStructs.

Section ConvertAndInline.
  Context {reg_t ext_fn_t rule_name_t: Type}.
  Context (R: reg_t -> type).
  Context (Sigma: ext_fn_t -> ExternalSignature).
  Context (convert_reg: reg_t -> debug_id_ty).
  Context (convert_ext_fn: ext_fn_t -> debug_id_ty).
  Context (struct_list: list struct_sig).
  (* Import Syntax. *)

  Definition convert_port (p: Types.Port) : Port :=
    match p with
    | Types.P0 => P0
    | Types.P1 => P1
    end.

  Definition convert_bits1 (fn: PrimTyped.fbits1) : result (option bits1) unit :=
    match fn with
    | PrimTyped.Not _ => Success (Some Not)
    | PrimTyped.SExt _ width => Success (Some (SExt width))
    | PrimTyped.ZExtL _ width => Success (Some (ZExtL width))
    | PrimTyped.Slice _ offset width => Success (Some (Slice offset width))
    | _ => Failure (__debug__ "convert_bits1" tt)
    end.

  Definition mem_req :=
    {| Types.struct_name := "mem_req";
       Types.struct_fields := [("byte_en" , bits_t 4);
                         ("addr"     , bits_t 32);
                         ("data"     , bits_t 32)] |}.
  Definition mem_resp :=
    {| Types.struct_name := "mem_resp";
       Types.struct_fields := [("byte_en", bits_t 4); ("addr", bits_t 32); ("data", bits_t 32)] |}.

  Definition struct_sig_to_idx (sig: Types.struct_sig) : result nat unit :=
    match find_with_index (beq_dec sig) struct_list with
    | Some (idx, _) => Success idx
    | None => Failure tt
    end.

  Definition struct_sig_to_id (sig: Types.struct_sig) : result debug_id_ty unit :=
    let/res idx := struct_sig_to_idx sig in
    Success (sig.(Types.struct_name), N.of_nat idx).

  Definition dstruct_field_to_id (sig: Types.struct_sig) (fld: struct_index sig) : result debug_id_ty unit :=
    let idx := (Vect.index_to_nat fld) in
    match nth_error sig.(Types.struct_fields) idx with
    | Some fld => Success (fst fld, N.of_nat idx)
    | None => Failure tt
    end.
  Definition struct_sig_to_struct_env : result (@struct_env_t debug_id_ty) unit :=
    result_list_map
      (fun s =>
         let/res name := struct_sig_to_id s in
         Success {| dstruct_name := name;
                    dstruct_fields := mapi (fun idx '(f,t) => ((f, N.of_nat idx), type_sz t)) s.(Types.struct_fields)
                 |}) struct_list.

  Definition convert_fn1 (fn: PrimTyped.fn1) : result (option (@fn1 debug_id_ty)) unit :=
    match fn with
    | PrimTyped.Display _ => Failure (__debug__ "UDisplay" tt)
    | PrimTyped.Conv _ conv =>
        match conv with
        | PrimTyped.Pack => Success None
        | PrimTyped.Unpack => Success None
        | PrimTyped.Ignore => Success (Some Ignore)
        end
    | PrimTyped.Bits1 op =>
        let/resopt op := convert_bits1 op in
        Success (Some (Bits1 op))
    | PrimTyped.Struct1 op sig f  =>
        match op with
        | PrimTyped.GetField =>
            let/res sid := struct_sig_to_id sig in
            let/res fid := dstruct_field_to_id sig f in
            Success (Some (Struct1 (GetField sid fid))) 
        end
    | PrimTyped.Array1 _ _ _ => Failure (__debug__ "Array1" tt)
    end.

  Definition convert_bits_comparison (cmp: Primitives.bits_comparison) : bits_comparison :=
    match cmp with
    | Primitives.cLt => cLt
    | Primitives.cGt => cGt
    | Primitives.cLe => cLe
    | Primitives.cGe => cGe
    end.

  Definition convert_bits2 (fn: PrimTyped.fbits2) : result bits2 unit :=
    match fn with
    | PrimTyped.And _ => Success And
    | PrimTyped.Or _ => Success Or
    | PrimTyped.Xor _ => Success Xor
    | PrimTyped.Lsl _ _ => Success Lsl
    | PrimTyped.Lsr _ _ => Success Lsr
    | PrimTyped.Asr _ _ => Success Asr
    | PrimTyped.Concat _ _ => Success Concat
    | PrimTyped.Sel _ => Success Sel
    | PrimTyped.Plus _ => Success Plus
    | PrimTyped.Minus _ => Success Minus
    | PrimTyped.IndexedSlice _ width => Success (IndexedSlice width)
    | PrimTyped.Compare signed c _ => Success (Compare signed (convert_bits_comparison c))
    | PrimTyped.SliceSubst _ _ _ => Failure (__debug__ "SliceSubst" tt)
    | PrimTyped.Mul _ _ => Failure tt
    | PrimTyped.EqBits _ neg => Success (EqBits neg)
    end.

  Definition convert_fn2 (fn: PrimTyped.fn2) : result (@fn2 debug_id_ty) unit :=
    match fn with
    | PrimTyped.Eq _ neg => Success (Bits2 (EqBits neg))
    | PrimTyped.Bits2 fn =>
        let/res fn := convert_bits2 fn in
        Success (Bits2 fn)
    | PrimTyped.Struct2 fn sig f =>
        let/res sid := struct_sig_to_id sig in
        let/res fid := dstruct_field_to_id sig f in
        match fn with
        | PrimTyped.SubstField => Success (Struct2 (SubstField sid fid))
        end
    | PrimTyped.Array2 _ _ _ => Failure tt
    end.
  Notation taction := (Koika.Frontend.action R Sigma).

  Fixpoint convert {sig: tsig var_t} {tau: type} (a: taction sig tau)
                   : result (@action debug_id_ty) unit :=
    match a with
    | TypedSyntax.Fail tau => Success (Fail (Types.type_sz tau))
    | @TypedSyntax.Var _ _ _ _ _ _ _ _ k _ _ => Success (Var k)
    | TypedSyntax.Const cst => Success (Const (vect_to_list (bits_of_value cst)))
    | @TypedSyntax.Assign _ _ _ _ _ _ _ _ v _ _ ex =>
        let/res ex := convert ex in
        Success (Assign v ex)
    | TypedSyntax.Seq a1 a2 =>
        let/res a1 := convert a1 in
        let/res a2 := convert a2 in
        Success (Seq a1 a2)
    | TypedSyntax.Bind v ex body  =>
        let/res ex := convert ex in
        let/res body := convert body in
        Success (Bind v ex body)
    | TypedSyntax.If cond tbranch fbranch =>
        let/res cond := convert cond in
        let/res tbranch := convert tbranch in
        let/res fbranch := convert fbranch in
        Success (If cond tbranch fbranch)
    | TypedSyntax.Read port idx =>
        Success (Read (convert_port port) (convert_reg idx))
    | TypedSyntax.Write port idx value =>
        let/res value := convert value in
        Success (Write (convert_port port) (convert_reg idx) value)
    | TypedSyntax.ExternalCall ufn arg =>
        let/res arg := convert arg in
        Success (ExternalCall (convert_ext_fn ufn) arg)
    | @TypedSyntax.InternalCall _ _ _ _ _ _ _ _ _ fn argspec args body =>
        match argspec, args with
        | [(arg_name, _)], CtxCons _ arg CtxEmpty =>
            let/res arg := convert arg in
            let/res body := convert body in
            Success (Bind arg_name arg body)
        | [], CtxEmpty =>
            let/res body := convert body in
            Success body
        | _, _ => Failure tt
        end
    | TypedSyntax.Unop ufn1 arg1 =>
        let/res arg1 := convert arg1 in
        let/res opt_fn1 := convert_fn1 ufn1 in
        match opt_fn1 with
        | Some fn1 => Success (Unop fn1 arg1)
        | None => Success arg1 (* noop fns *)
        end
    | TypedSyntax.Binop fn2 arg1 arg2 =>
        let/res arg1 := convert arg1 in
        let/res arg2 := convert arg2 in
        let/res fn2 := convert_fn2 fn2 in
        Success (Binop fn2 arg1 arg2)
    | TypedSyntax.APos _ e => convert e
    end.

  Fixpoint convert_scheduler (sched: Syntax.scheduler Frontend.pos_t rule_name_t)
    : result (@scheduler rule_name_t) unit :=
    match sched with
    | Syntax.Done => Success Done
    | Syntax.Cons r s =>
        let/res s := convert_scheduler s in
        Success (Cons r s)
    | Syntax.Try _ _ _ => Failure tt
    | _ => Failure tt
    end.

  Fixpoint list_of_schedule (rls: rule_name_t -> Frontend.rule R Sigma)
                            (sched: Syntax.scheduler Frontend.pos_t rule_name_t)
                            : result (list (rule_name_t * (Frontend.rule R Sigma))) unit :=
    match sched with
    | Syntax.Done => Success []
    | Syntax.Cons r s =>
        let/res s := list_of_schedule rls s in
        Success ((r, (rls r))::s)
    | Syntax.Try _ _ _ => Failure tt
    | Syntax.SPos _ e => list_of_schedule rls e
    end.

  Definition convert_schedule
    (rls: rule_name_t -> Frontend.rule R Sigma)
    (sched: Syntax.scheduler Frontend.pos_t rule_name_t)
    : result (list (rule_name_t * (@action debug_id_ty))) unit :=
    let/res sched_list := list_of_schedule rls sched in
    result_list_map (fun '(name, rl) => let/res rl := convert rl in Success (name, rl)) sched_list .


End ConvertAndInline.

(*
Module TestConversion.
  Require Import rv_isolation.Common.
  Require Import rv_isolation.Machine.
  Require Import rv_isolation.External.

  Module Import Machine := Machine EnclaveParams.
  Existing Instance Machine.FiniteType_reg_t.
  Existing Instance FiniteType_ext_fn_t.
  Existing Instance Machine.Show_reg_t.
  Existing Instance Machine.Show_ext_fn_t.

  Definition reg_t := Machine._reg_t.
  Definition ext_fn_t := Machine._ext_fn_t.
  Definition reg_to_debug_id (r: reg_t) : debug_id_ty :=
    (Show.show r, N.of_nat (finite_index r)).

  Definition ext_fn_to_debug_id (extfn: ext_fn_t) : debug_id_ty :=
    (Show.show extfn, N.of_nat (finite_index extfn)).

  Definition struct_sigs := get_scheduler_structs R Sigma Machine.rules schedule.
  Definition struct_env := ltac:(_extract_success (struct_sig_to_struct_env struct_sigs)).
  (* Eval vm_compute in (List.length struct_env). *)
  (* Eval (beq_dec (nth struct_env  *)
  (* Eval vm_compute in (struct_env). *)
  (* Eval vm_compute in (add_structs RV32I.R RV32I.Sigma [] (RV32I.rv_rules Writeback)). *)

  Definition rules_list : (list (rule_name_t * (@action debug_id_ty))) :=
    Eval vm_compute in
ltac:(_extract_success (convert_schedule R Sigma reg_to_debug_id ext_fn_to_debug_id struct_sigs Machine.rules schedule)).
  (* Goal False. *)
  (* Proof. *)
  (*   assert (is_success (convert_schedule Machine.lifted_core0_schedule) = true) by vm_reflect. *)
  (*   assert (is_success (convert_schedule Machine.lifted_mem_schedule) = true) by vm_reflect. *)
  (*   assert (is_success (convert_schedule Machine.lifted_sm_schedule) = true) by vm_reflect. *)
  (* Abort. *)

  Definition core0_schedule := ltac:(_extract_success (convert_scheduler Machine.lifted_core0_schedule)).
  Definition core1_schedule := ltac:(_extract_success (convert_scheduler Machine.lifted_core1_schedule)).
  Definition mem_schedule := ltac:(_extract_success (convert_scheduler Machine.lifted_mem_schedule)).
  Definition sm_schedule := ltac:(_extract_success (convert_scheduler Machine.lifted_sm_schedule)).
  Definition schedule := ltac:(_extract_success (convert_scheduler schedule)).

  Definition modular_schedule : list (@scheduler rule_name_t) :=
    [core0_schedule; core1_schedule; mem_schedule; sm_schedule ].

  Definition _id {X Y} (x: X * Y):= snd x.

  Instance EqDec_rule_name_t : EqDec rule_name_t := _.

  Definition rules (rl: rule_name_t) : @action debug_id_ty :=
    match find (fun '(rl', _) => beq_dec rl' rl) rules_list with
    | Some (_, rl) => rl
    | _ => Fail 0
    end.

  Definition id_rules (rl: rule_name_t) : @action N:=
    id_transform_action snd (rules rl).
  Definition id_struct_env := (id_transform_struct_env _id struct_env).

  Lemma impl_interp_modular_schedule :
    forall sigma st log,
        interp_scheduler
          sigma [] id_struct_env (st) id_rules
               schedule = Success log ->
      interp_modular_schedule
          sigma []
               id_struct_env
               id_rules
               (st)
               modular_schedule =
        Success (commit_update st log.(Log__koika), log.(Log__ext)).
  Proof.
    intros. eapply check_modular_conflicts_correct.
    - vm_reflect.
    - assumption.
  Qed.

  Definition reg_env : reg_types_t :=
    map (fun r => (_id (reg_to_debug_id r), type_sz (R r))) (@finite_elements _ FiniteType_reg_t).

  Definition ext_fn_tys : ext_fn_types_t :=
    map (fun ext => (_id (ext_fn_to_debug_id ext),(type_sz (Sigma ext).(arg1Sig), type_sz ((Sigma ext).(retSig)))))
        (@finite_elements _ FiniteType_ext_fn_t).
  Lemma typecheck_schedule_Success :
    typecheck_schedule reg_env ext_fn_tys [] id_struct_env schedule id_rules = Success tt.
  Proof. vm_compute. reflexivity. Qed.


  Goal False.
    assert (oraat_ok [] id_rules (SemanticUtils.list_of_schedule core0_schedule) = true) by vm_reflect.
    assert (oraat_ok [] id_rules (SemanticUtils.list_of_schedule core1_schedule) = true) by vm_reflect.

    assert (oraat_ok [] id_rules (SemanticUtils.list_of_schedule sm_schedule) = true) by vm_reflect.
    assert (oraat_ok [] id_rules (SemanticUtils.list_of_schedule mem_schedule) = true) by vm_reflect.
  Abort.

End TestConversion.
*)
(* Record Koika_package_t (pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t : Type) : Type := Build_koika_package_t *)
(*   { koika_var_names : Show.Show var_t; *)
(*     koika_fn_names : Show.Show fn_name_t; *)
(*     koika_reg_names : Show.Show reg_t; *)
(*     koika_reg_types : reg_t -> type; *)
(*     koika_reg_init : forall r : reg_t, koika_reg_types r; *)
(*     koika_reg_finite : FiniteType reg_t; *)
(*     koika_ext_fn_types : ext_fn_t -> ExternalSignature; *)
(*     koika_rules : rule_name_t -> TypedSyntax.rule pos_t var_t fn_name_t koika_reg_types koika_ext_fn_types; *)
(*     koika_rule_external : rule_name_t -> bool; *)
(*     koika_rule_names : Show.Show rule_name_t; *)
(*     koika_scheduler : Syntax.scheduler pos_t rule_name_t; *)
(*     koika_module_name : string }. *)
