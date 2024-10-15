Require Import rv_isolation.Common.
Require Import rv_isolation.RVCore.
Require Import rv_isolation.Memory.
Require Import rv_isolation.SecurityMonitor.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koikaExamples.Enclaves.ProofUtils.
Require Import koikaExamples.Enclaves.MemoryProofs.
Require Import koikaExamples.Enclaves.SymbSpec.
Require Import koikaExamples.Enclaves.PfSim_sig.
Require Import koika.AnnotatedSyntax.

Definition mk_init_pkg machine st sigma :=
  {|
    pkg_machine := machine;
    pkg_init_st := st;
    pkg_sigma := sigma;
    pkg_mid_st := None;
    pkg_final_st := st;
    pkg_mid_ext_log := None;
    pkg_ext_log' := SortedExtFnEnv.empty
  |}.
Definition mk_post_pkg machine init_st sigma final_st ext_log :=
     {|
       pkg_machine := machine;
       pkg_init_st := init_st;
       pkg_sigma := sigma;
       pkg_mid_st := None;
       pkg_final_st := final_st;
       pkg_mid_ext_log := None;
       pkg_ext_log' := ext_log
     |}.
Ltac do_magic x t :=
  lazymatch x with
  | true => t
  | false => t (* apply __magic__ *)
  | _ => fail
  end.
Ltac t_symb :=
match goal with
| H: strong_WF_state _ ?st |- WF_state _ ?st =>
    solve[apply strong_WF_state_weaken in H; apply H]
end.

Ltac solve_machine_to_prop schedule_ok :=
  unfold machine_to_prop; split_ands_in_goal; [auto| t_symb | (* resolve_oraat_interp_scheduler_list schedule_ok *)].
Ltac solve_spec_machine_to_prop schedule_ok core :=
  unfold machine_to_prop; split_ands_in_goal; [auto| t_symb | ];
     destruct core. (* [resolve_oraat_interp_scheduler_list (schedule_ok CoreId0) | *)
                    (*  resolve_oraat_interp_scheduler_list (schedule_ok CoreId1) ]. *)
Ltac change_and_solve2 H :=
  change_Forall_lists1 H; revert H;
          eapply forall_interp_spred2_package_equiv'; solve_package_equiv.

Module Type SimCoreDefs (EnclaveParams: EnclaveParams_sig)
                        (SecurityParams: SecurityParams_sig EnclaveParams).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.
  Import Utils.PfHelpers.
  Definition spec_core_schedule_list (core: ind_core_id) : list (Machine.rule_name_t * string) :=
      map (fun rl => (rl, show rl)) (list_of_schedule (Machine.core_schedule core)).
  Definition typecheck_fn rl : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl).
  Definition spec_core_schedule core :=
        preprocess_schedule typecheck_fn rules (spec_core_schedule_list core).


  Definition impl_core_schedule_list : list (Machine.rule_name_t * string) :=
    map (fun rl => (rl, show rl)) (list_of_schedule (schedule_app core0_schedule core1_schedule)).
  Definition impl_core_schedule :=
        preprocess_schedule typecheck_fn rules impl_core_schedule_list.

  Definition ext_empty machine_id (extfn: debug_id_ty -> sval): list (sim_custom_t * fancy_spred) :=
    ProofUtils.assert_ext_fns_empty extfn
      (fun x => CustomExtFn machine_id (_id x)) [ext_mainmem; ext_led; ext_uart_write; ext_uart_read; ext_finish].

  Definition post_core_exprs' machine_id
      (reg_init reg_final: reg_t -> sval) (ext_fn: debug_id_ty -> sval)
      : list (sim_custom_t * fancy_spred) :=
      [(CustomSimTaint machine_id, {{{ forall x in (remove_regs reg_list (map reg_to_debug_id ((core_regs CoreId0) ++ (core_regs CoreId1)))),
                 `reg_final x` = `reg_init x`
                     }}})
      ] ++ (ext_empty machine_id ext_fn).

  Definition post_core_exprs ireg_init sreg_init ireg_final sreg_final iext_final sext_final
                             : list (sim_custom_t * fancy_spred) :=
    (post_core_exprs' MachineImpl ireg_init ireg_final iext_final) ++
    (post_core_exprs' MachineSpec sreg_init sreg_final sext_final).

  Definition post_conds  core
     (ireg_init sreg_init : reg_t -> sval)
     (ireg_final sreg_final : reg_t -> sval)
     (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
     (iext_log sext_log: debug_id_ty -> sval) :=
    sim_invariants EnclaveParams.enclave_sig core ireg_final sreg_final
                   iget_field sget_field ++
    post_core_exprs ireg_init sreg_init ireg_final sreg_final  iext_log sext_log.


  Definition sim_core_post core :=
    preprocess_fancy_spreds (
                               sim_invariants EnclaveParams.enclave_sig core impl_final spec_final
                                          impl_get_field spec_get_field
                           ) ++
                          preprocess_fancy_spreds (
                            post_core_exprs impl_init spec_init impl_final spec_final
                                            impl_final_ext spec_final_ext).

  Definition sim_core_pre core :=
    preprocess_fancy_spreds (sim_invariants EnclaveParams.enclave_sig core impl_init spec_init
                                          impl_get_field spec_get_field).

  Definition sim_core_file  core : file_t :=
    {| file_machines := Product impl_machine SymbSpecDefs.spec_machine
                                impl_core_schedule (spec_core_schedule core);
       file_assumptions := sim_core_pre core;
       file_assertions := sim_core_post core;
    |}.
End SimCoreDefs.


Module Type SMT_SimCore_sig (EnclaveParams: EnclaveParams_sig)
                            (SecurityParams: SecurityParams_sig EnclaveParams)
                            (SimCoreDefs: SimCoreDefs EnclaveParams SecurityParams).
  Parameter SMT_file: forall core, SymbolicInterp.WF_product_file (SimCoreDefs.sim_core_file core) = true.
End SMT_SimCore_sig.

Module SimCore (EnclaveParams: EnclaveParams_sig)
               (SecurityParams: SecurityParams_sig EnclaveParams)
               (SimCoreDefs: SimCoreDefs EnclaveParams SecurityParams)
               (SmtOk: SMT_SimCore_sig EnclaveParams SecurityParams SimCoreDefs).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.
  Import Utils.PfHelpers.
  Import SimCoreDefs.
  Import SmtOk.

  Theorem sim_step_correct_core: forall core,
    symbolic_evaluate_file_success_product
      impl_machine SymbSpecDefs.spec_machine impl_core_schedule (spec_core_schedule core)
      (sim_core_pre core) (sim_core_post core).
  Proof.
    intros.
    specialize symbolic_evaluate_file_success with (file := sim_core_file core) .
    unfold sim_core_file in *. unfold file_machines. intros. specialize (H (SMT_file core)). revert H.
    unfold file_assumptions. unfold file_assertions. auto.
  Qed.

  Definition CorePre :=
    fun (enclave_sig : enclave_params_sig) (core : ind_core_id) (impl_st spec_st : state_t)
      (impl_sigma spec_sigma : ext_sigma_t) =>
      Forall (fun p => interp_spred2 (mk_init_pkg impl_machine impl_st impl_sigma)
                      (mk_init_pkg SymbSpecDefs.spec_machine spec_st spec_sigma) p)
        (sim_core_pre core).

  Definition CorePost :=
    fun (enclave_sig : enclave_params_sig) (core : ind_core_id) (impl_st spec_st impl_st' spec_st' : state_t)
      (impl_sigma spec_sigma : ext_sigma_t) (impl_ext_log spec_ext_log : ext_log_t) =>
      Forall (fun p => interp_spred2
                      (mk_post_pkg impl_machine impl_st impl_sigma impl_st' impl_ext_log)
                      (mk_post_pkg SymbSpecDefs.spec_machine spec_st spec_sigma spec_st' spec_ext_log) p)
        (sim_core_post core).
  (* Lemma oraat_schedule_ok_impl_core: *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule (schedule_app core0_schedule core1_schedule)) = true. *)
  (* Proof. *)
  (*   vm_compute. reflexivity. *)
  (* Qed. *)

  (* Lemma oraat_schedule_ok_spec_core: *)
  (*   forall core, *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule ((Machine.core_schedule core))) = true. *)
  (* Proof. *)
  (*   destruct core; vm_reflect. *)
  (* Qed. *)
Ltac solve_sim_interp_scheduler_satisfies_spec oraat_impl oraat_spec file_ok:=
  unfold sim_interp_scheduler_satisfies_spec;
    intros core * _ hwf_impl hwf_spec hwf_impl_sigma hwf_spec_sigma hwf_impl_int hwf_spec_int himpl_sched hspec_sched hpre.
Ltac assert_oraat_types sched htype hwf_st' wf_ext' core :=
  match type of sched with
  | interp_scheduler ?sigma ?int_fns ?struct_defs ?st ?rules ?sched = Success ?log =>
      assert (Typechecking.typecheck_schedule (SortedRegEnv.to_list reg_type_env)
                _ext_fn_tys int_fns struct_defs sched rules = Success tt) as htype by (destruct core; vm_reflect);
      assert (strong_WF_state reg_type_env (commit_update st (Log__koika log)) /\
                WF_ext_log _ext_fn_tys (Log__ext log)) as (hwf_st' & wf_ext') by
          (eapply typecheck_scheduler_correct'' with (ext_sigma := sigma) (1 := htype); eauto)
  end.


  Theorem sim_step_correct_core_sched:
    forall core,
     sim_interp_scheduler_satisfies_spec
        reg_type_env _ext_fn_tys
        id_int_fns id_int_fns
        id_struct_defs id_struct_defs
        id_rules id_rules (schedule_app core0_schedule core1_schedule) (Machine.core_schedule core) unit
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           CorePre EnclaveParams.enclave_sig core impl_st spec_st impl_sigma spec_sigma)
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           CorePost EnclaveParams.enclave_sig core impl_st spec_st impl_st' spec_st' impl_sigma spec_sigma impl_ext spec_ext).
  Proof.
    solve_sim_interp_scheduler_satisfies_spec
      oraat_schedule_ok_impl_core oraat_schedule_ok_spec_core sim_step_correct_core.
    assert_oraat_types himpl_sched himpl_type hwf_impl' hwf_impl_ext' core.
    assert_oraat_types hspec_sched hspec_type hwf_spec' hwf_spec_ext' core.
    (* specialize @oraat_interp_scheduler__conflicts_correct with *)
    (*      (1 := strong_WF_state_weaken _ _ hwf_impl) (2 := hwf_impl_sigma) (3 := hwf_impl_int) (6 := himpl_sched) (4 := himpl_type) (5 := oraat_schedule_ok_impl_core). intros Horaat_impl. *)
    (* specialize @oraat_interp_scheduler__conflicts_correct with *)
    (*      (1 := strong_WF_state_weaken _ _ hwf_spec) (2 := hwf_spec_sigma) (3 := hwf_spec_int) (6 := hspec_sched) (4 := hspec_type) (5 := oraat_schedule_ok_spec_core core). intros Horaat_spec. *)
    split_ands_in_goal; auto.
    specialize (sim_step_correct_core core) as Hfile.
    apply Hfile.
    - revert hpre.
      eapply forall_interp_spred2_package_equiv'; eauto.
      destruct core; solve_package_equiv.
    - solve_machine_to_prop idtac.
      set (strip_dbg_sched_list _ ) as l in *.
      assert (l = (map (fun rl => id_transform_action _id (rules rl))
                     (list_of_schedule (schedule_app core0_schedule core1_schedule)))) as Hl.
      { vm_reflect. }
        rewrite Hl.
        apply interp_scheduler_list_equiv.
        assumption.
    - solve_machine_to_prop idtac.
      set (strip_dbg_sched_list _ ) as l in *.
      assert (l = (map (fun rl => id_transform_action _id (rules rl))
                     (list_of_schedule (Machine.core_schedule core)))) as Hl.
      { destruct core; vm_reflect. }
        rewrite Hl.
        apply interp_scheduler_list_equiv.
        assumption.
  Qed.



End SimCore.
(* Module TestSimCore. *)
(*   Require Import koikaExamples.Enclaves.External. *)

(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module Files := SimCore EnclaveParams SecurityParams . *)

(*   Module File0. *)
(*     Definition file := Eval vm_compute in (Files.sim_core_file CoreId0). *)
(*     Extraction "TestSimCore.File0.ml" struct_sz vect_t file. *)
(*   End File0. *)
(* End TestSimCore. *)

Module Type SimMemDefs (EnclaveParams: EnclaveParams_sig)
                       (SecurityParams: SecurityParams_sig EnclaveParams).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.
  Import Utils.PfHelpers.
   Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.
  Import Utils.PfHelpers.
  Definition spec_mem_schedule_list (core: ind_core_id) : list (Machine.rule_name_t * string) :=
      map (fun rl => (rl, show rl)) (list_of_schedule (map_scheduler Machine.RlMem (Machine.mem_schedule core))).
  Definition typecheck_fn rl : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl).
  Definition spec_mem_schedule core :=
        preprocess_schedule typecheck_fn rules (spec_mem_schedule_list core).

  Definition impl_mem_schedule_list : list (Machine.rule_name_t * string) :=
    map (fun rl => (rl, show rl)) (list_of_schedule Impl.mem_schedule).
  Definition impl_mem_schedule :=
        preprocess_schedule typecheck_fn rules impl_mem_schedule_list.
  Definition ext_empty machine_id (extfn: debug_id_ty -> sval): list (sim_custom_t * fancy_spred) :=
    ProofUtils.assert_ext_fns_empty extfn
      (fun x => CustomExtFn machine_id (_id x)) [ext_led; ext_uart_write; ext_uart_read; ext_finish].

  Definition taint reg_init reg_final :=
    {{{ forall x in (remove_regs reg_list (map reg_to_debug_id ((core_regs CoreId0) ++ (core_regs CoreId1) ++ memory_regs))),
                 `reg_final x` = `reg_init x`
                     }}}.

  Definition pre_conds core ireg_fn sreg_fn iget_field sget_field :=
    sim_invariants EnclaveParams.enclave_sig core ireg_fn sreg_fn
                   iget_field sget_field ++
    sim_mem_pre_conds core ireg_fn sreg_fn iget_field sget_field.
    (* [(CustomRegStateRunning, {{{ `ireg_fn ((_smid (state core)))` <> #(_enum enum_core_state "Waiting") }}} )]. *)


  Definition post_mem_exprs' (core: ind_core_id)
     (ireg_init sreg_init : reg_t -> sval)
     (ireg_final sreg_final : reg_t -> sval)
     (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
     (iext_log sext_log: debug_id_ty -> sval)
     : list (sim_custom_t * fancy_spred) :=
      [(CustomSimTaint MachineImpl, taint ireg_init ireg_final)
      ;(CustomSimTaint MachineSpec, taint sreg_init sreg_final)
      ;(CustomExtMemPushRequest__Sim, mem_push_req_sim core ireg_init ireg_final iext_log sext_log)
      ;(CustomExtMemPushRequest__ImplInvalidOrWriteTurn, mem_push_req_impl_invalid_or_turn core ireg_init iget_field iext_log )
      ;(CustomExtMemPushRequest__SpecInvalidOrWriteTurn, mem_push_req_spec_invalid_or_turn core ireg_init sget_field sext_log)
      ;(CustomExtMemPushRequest__NotInConfig,
         {{{ `ireg_init (_mid Memory.turn)` = #(mem_core_write_turn (other_core core)) ->
             `ireg_init ((_smid (state core)))` <> #(_enum enum_core_state "Waiting") ->
             ``fs_addr_not_in_config EnclaveParams.enclave_sig core ireg_init iget_field iext_log``
         }}})
      ;(CustomExtMemShreqSim,
         {{{ `iget_field (_sid mem_input) (_fld mem_input "put_valid") (iext_log (_extid ext_mainmem))` = Ob~1 ->
             `ireg_final (_mid Memory.turn)` = #(mem_core_read_turn core) ->
             `ireg_final (_mid Memory.SHReq)` = `sreg_final (_mid Memory.SHReq)`
         }}})
      ] ++
        map_fst (CustomMemSim)
        [((MemImplExtCorrectCore CoreId0),
           MemSymbDefs.impl_post_ext_mem_correct_core CoreId0 ireg_final iget_field iext_log)
         ;((MemImplExtCorrectCore CoreId1),
            MemSymbDefs.impl_post_ext_mem_correct_core CoreId1 ireg_final iget_field iext_log)
        ] ++ (ext_empty MachineImpl iext_log) ++ (ext_empty MachineSpec sext_log).


  Definition post_conds (core: ind_core_id)
     (ireg_init sreg_init : reg_t -> sval)
     (ireg_final sreg_final : reg_t -> sval)
     (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
     (iext_log sext_log: debug_id_ty -> sval) :=
    sim_invariants EnclaveParams.enclave_sig core ireg_final sreg_final
                   iget_field sget_field ++
    post_mem_exprs' core ireg_init sreg_init ireg_final sreg_final iget_field sget_field
                    iext_log sext_log.

  Definition sim_mem_pre core :=
    preprocess_fancy_spreds (pre_conds core impl_init spec_init impl_get_field spec_get_field).
  Definition sim_mem_post core :=
    preprocess_fancy_spreds (post_conds core impl_init spec_init impl_final spec_final
                                         impl_get_field spec_get_field impl_final_ext spec_final_ext).

  Definition sim_mem_file  core : file_t :=
    {| file_machines := Product impl_machine SymbSpecDefs.spec_machine
                                impl_mem_schedule (spec_mem_schedule core);
       file_assumptions := sim_mem_pre core;
       file_assertions := sim_mem_post core
    |}.
End SimMemDefs.
Module Type SMT_SimMem_sig (EnclaveParams: EnclaveParams_sig)
                           (SecurityParams: SecurityParams_sig EnclaveParams)
                           (SimMemDefs: SimMemDefs EnclaveParams SecurityParams).
  Parameter SMT_file: forall core, SymbolicInterp.WF_product_file (SimMemDefs.sim_mem_file core) = true.
End SMT_SimMem_sig.

Module SimMem (EnclaveParams: EnclaveParams_sig)
              (SecurityParams: SecurityParams_sig EnclaveParams)
              (SimMemDefs: SimMemDefs EnclaveParams SecurityParams)
              (SmtOk: SMT_SimMem_sig EnclaveParams SecurityParams SimMemDefs).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.
  Import Utils.PfHelpers.
  Import SimMemDefs.
  Theorem sim_step_correct_mem: forall core,
    symbolic_evaluate_file_success_product
      impl_machine SymbSpecDefs.spec_machine impl_mem_schedule (spec_mem_schedule core)
      (sim_mem_pre core) (sim_mem_post core).
  Proof.
    intros.
    intros.
    specialize symbolic_evaluate_file_success with (file := sim_mem_file core) .
    unfold sim_mem_file in *. unfold file_machines. intros. specialize (H (SmtOk.SMT_file core)). revert H.
    unfold file_assumptions. unfold file_assertions. auto.
  Qed.

  Definition MemPre :=
    fun (enclave_sig : enclave_params_sig) (core: ind_core_id) (impl_st spec_st : state_t)
      (impl_sigma spec_sigma : ext_sigma_t) =>
      Forall (fun p => interp_spred2 (mk_init_pkg impl_machine impl_st impl_sigma)
                      (mk_init_pkg SymbSpecDefs.spec_machine spec_st spec_sigma) p)
        (sim_mem_pre core).

  Definition MemPost :=
    fun (enclave_sig : enclave_params_sig) (core : ind_core_id) (impl_st spec_st impl_st' spec_st' : state_t)
      (impl_sigma spec_sigma : ext_sigma_t) (impl_ext_log spec_ext_log : ext_log_t) =>
      Forall (fun p => interp_spred2
                      (mk_post_pkg impl_machine impl_st impl_sigma impl_st' impl_ext_log)
                      (mk_post_pkg SymbSpecDefs.spec_machine spec_st spec_sigma spec_st' spec_ext_log) p)
        (sim_mem_post core).
  (* Lemma oraat_schedule_ok_impl_mem: *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule (Impl.mem_schedule)) = true. *)
  (* Proof. *)
  (*   vm_compute. reflexivity. *)
  (* Qed. *)

  (* Lemma oraat_schedule_ok_spec_mem: *)
  (*   forall core, *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule (map_scheduler Machine.RlMem (Machine.mem_schedule core))) = true. *)
  (* Proof. *)
  (*   destruct core; vm_reflect. *)
  (* Qed. *)

Ltac solve_sim_interp_scheduler_satisfies_spec oraat_impl oraat_spec file_ok:=
  unfold sim_interp_scheduler_satisfies_spec;
    intros core * _ hwf_impl hwf_spec hwf_impl_sigma hwf_spec_sigma hwf_impl_int hwf_spec_int himpl_sched hspec_sched hpre.
Ltac assert_oraat_types sched htype hwf_st' wf_ext' core :=
  match type of sched with
  | interp_scheduler ?sigma ?int_fns ?struct_defs ?st ?rules ?sched = Success ?log =>
      assert (Typechecking.typecheck_schedule (SortedRegEnv.to_list reg_type_env)
                _ext_fn_tys int_fns struct_defs sched rules = Success tt) as htype by (destruct core; vm_reflect);
      assert (strong_WF_state reg_type_env (commit_update st (Log__koika log)) /\
                WF_ext_log _ext_fn_tys (Log__ext log)) as (hwf_st' & wf_ext') by
          (eapply typecheck_scheduler_correct'' with (ext_sigma := sigma) (1 := htype); eauto)
  end.

  Theorem sim_step_correct_mem_sched:
    forall core,
     sim_interp_scheduler_satisfies_spec
        reg_type_env _ext_fn_tys
        id_int_fns id_int_fns
        id_struct_defs id_struct_defs
        id_rules id_rules Impl.mem_schedule (map_scheduler Machine.RlMem (mem_schedule core)) unit
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           MemPre EnclaveParams.enclave_sig core impl_st spec_st impl_sigma spec_sigma)
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           MemPost EnclaveParams.enclave_sig core impl_st spec_st impl_st' spec_st' impl_sigma spec_sigma impl_ext spec_ext).
   Proof.
    solve_sim_interp_scheduler_satisfies_spec
      oraat_schedule_ok_impl_core oraat_schedule_ok_spec_core sim_step_correct_core.
    assert_oraat_types himpl_sched himpl_type hwf_impl' hwf_impl_ext' core.
    assert_oraat_types hspec_sched hspec_type hwf_spec' hwf_spec_ext' core.
    (* specialize @oraat_interp_scheduler__conflicts_correct with *)
    (*      (1 := strong_WF_state_weaken _ _ hwf_impl) (2 := hwf_impl_sigma) (3 := hwf_impl_int) (6 := himpl_sched) (4 := himpl_type) (5 := oraat_schedule_ok_impl_mem). intros Horaat_impl. *)
    (* specialize @oraat_interp_scheduler__conflicts_correct with *)
    (*      (1 := strong_WF_state_weaken _ _ hwf_spec) (2 := hwf_spec_sigma) (3 := hwf_spec_int) (6 := hspec_sched) (4 := hspec_type) (5 := oraat_schedule_ok_spec_mem core). intros Horaat_spec. *)
    split_ands_in_goal; auto.
    specialize (sim_step_correct_mem core) as Hfile.
    apply Hfile.
    - revert hpre.
      eapply forall_interp_spred2_package_equiv'; eauto.
      destruct core; solve_package_equiv.
    - solve_machine_to_prop (oraat_schedule_ok_impl_mem).
      set (strip_dbg_sched_list _ ) as l in *.
      assert (l = (map (fun rl => id_transform_action _id (rules rl))  (list_of_schedule Impl.mem_schedule))) as Hl.
      { vm_reflect. }
        rewrite Hl. apply interp_scheduler_list_equiv. assumption.
    - solve_machine_to_prop idtac.
      set (strip_dbg_sched_list _ ) as l in *.
      assert (l = (map (fun rl => id_transform_action _id (rules rl))
                     (list_of_schedule (map_scheduler Machine.RlMem (Machine.mem_schedule core))))) as Hl.
      { destruct core; vm_reflect. }
        rewrite Hl.
        apply interp_scheduler_list_equiv.
        assumption.
   Qed.

End SimMem.
(* Module TestSimMem. *)
(*   Require Import koikaExamples.Enclaves.External. *)

(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module Files := SimMem EnclaveParams SecurityParams . *)

(*   Module File1. *)
(*     Definition file := Eval vm_compute in (Files.sim_mem_file CoreId1). *)
(*     Extraction "TestSimMem.File1.ml" struct_sz vect_t file. *)
(*   End File1. *)
(* End TestSimMem. *)

Module Type SimSMDefs (EnclaveParams: EnclaveParams_sig)
                      (SecurityParams: SecurityParams_sig EnclaveParams).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.
  Import Utils.PfHelpers.
  Definition spec_sm_schedule_list (core: ind_core_id) : list (Machine.rule_name_t * string) :=
      map (fun rl => (rl, show rl)) (list_of_schedule (map_scheduler Machine.RlSm (Machine.sm_schedule core))).
  Definition typecheck_fn rl : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl).
  Definition spec_sm_schedule core :=
        preprocess_schedule typecheck_fn rules (spec_sm_schedule_list core).

  Definition impl_sm_schedule_list : list (Machine.rule_name_t * string) :=
    map (fun rl => (rl, show rl)) (list_of_schedule Impl.sm_schedule).
  Definition impl_sm_schedule :=
        preprocess_schedule typecheck_fn rules impl_sm_schedule_list.

  Definition pre_conds core ireg_fn sreg_fn iget_field sget_field :=
    sim_invariants EnclaveParams.enclave_sig core ireg_fn sreg_fn
                   iget_field sget_field ++
    sim_sm_pre_conds core ireg_fn sreg_fn iget_field sget_field.

  Definition ext_empty machine_id (extfn: debug_id_ty -> sval): list (sim_custom_t * fancy_spred) :=
    ProofUtils.assert_ext_fns_empty extfn
      (fun x => CustomExtFn machine_id (_id x)) [ext_mainmem].

  Definition post_sm_exprs' machine_id
      (reg_init reg_final: reg_t -> sval) (ext_fn: debug_id_ty -> sval)
      : list (sim_custom_t * fancy_spred) :=
      [(CustomSimTaint machine_id, {{{ forall x in (remove_regs reg_list (map reg_to_debug_id ((sm_regs CoreId0) ++ (sm_regs CoreId1)))),
                 `reg_final x` = `reg_init x`
                     }}})
      ] ++ (ext_empty machine_id ext_fn).


  Definition post_conds (core: ind_core_id)
     (ireg_init sreg_init : reg_t -> sval)
     (ireg_final sreg_final : reg_t -> sval)
     (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
     (iext_log sext_log: debug_id_ty -> sval) :=
    sim_invariants EnclaveParams.enclave_sig core ireg_final sreg_final iget_field sget_field ++
      [(CustomExtLedSim, ext_fn_sim core (_extid ext_led) (_fld enclave_req "ext_led")
                                    ireg_init sget_field iext_log sext_log)
      ;(CustomExtUartReadSim, ext_fn_sim core (_extid ext_uart_read) (_fld enclave_req "ext_uart")
                                         ireg_init sget_field iext_log sext_log)
      ;(CustomExtUartWriteSim, ext_fn_sim core (_extid ext_uart_write) (_fld enclave_req "ext_uart")
                                         ireg_init sget_field iext_log sext_log)
      ;(CustomExtFinishSim, ext_fn_sim core (_extid ext_finish) (_fld enclave_req "ext_finish")
                                    ireg_init sget_field iext_log sext_log)
      ] ++ (map_fst CustomSm (sm_post_conds ireg_init ireg_final iext_log iget_field))
      ++ (post_sm_exprs' MachineImpl ireg_init ireg_final iext_log)
        ++ (post_sm_exprs' MachineSpec sreg_init sreg_final sext_log) .

  Definition sim_sm_pre core :=
    preprocess_fancy_spreds (pre_conds core impl_init spec_init impl_get_field spec_get_field).

  Definition sim_sm_post core :=
    preprocess_fancy_spreds (post_conds core impl_init spec_init impl_final spec_final
                                         impl_get_field spec_get_field impl_final_ext spec_final_ext).

  Definition sim_sm_file  core : file_t :=
    {| file_machines := Product impl_machine SymbSpecDefs.spec_machine
                                impl_sm_schedule (spec_sm_schedule core);
       file_assumptions := sim_sm_pre core;
       file_assertions := sim_sm_post core;
    |}.

End SimSMDefs.

Module Type SMT_SimSM_sig (EnclaveParams: EnclaveParams_sig)
                            (SecurityParams: SecurityParams_sig EnclaveParams)
                            (SimSMDefs: SimSMDefs EnclaveParams SecurityParams).
  Parameter SMT_file: forall core, SymbolicInterp.WF_product_file (SimSMDefs.sim_sm_file core) = true.
End SMT_SimSM_sig.

Module SimSM (EnclaveParams: EnclaveParams_sig)
             (SecurityParams: SecurityParams_sig EnclaveParams)
             (SMDefs: SimSMDefs EnclaveParams SecurityParams)
             (SmtOk: SMT_SimSM_sig EnclaveParams SecurityParams SMDefs).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.
  Import Utils.PfHelpers.
  Import SMDefs.
  Theorem sim_step_correct_sm: forall core,
    symbolic_evaluate_file_success_product
      impl_machine SymbSpecDefs.spec_machine impl_sm_schedule (spec_sm_schedule core)
      (sim_sm_pre core) (sim_sm_post core).
  Proof.
    intros.
    specialize symbolic_evaluate_file_success with (file := sim_sm_file core) .
    unfold sim_sm_file in *. unfold file_machines. intros. specialize (H (SmtOk.SMT_file core)). revert H.
    unfold file_assumptions. unfold file_assertions. auto.
  Qed.

  Definition SMPre :=
    fun (enclave_sig : enclave_params_sig) (core: ind_core_id) (impl_st spec_st : state_t)
      (impl_sigma spec_sigma : ext_sigma_t) =>
      Forall (fun p => interp_spred2 (mk_init_pkg impl_machine impl_st impl_sigma)
                      (mk_init_pkg SymbSpecDefs.spec_machine spec_st spec_sigma) p)
        (sim_sm_pre core).

  Definition SMPost :=
    fun (enclave_sig : enclave_params_sig) (core : ind_core_id) (impl_st spec_st impl_st' spec_st' : state_t)
      (impl_sigma spec_sigma : ext_sigma_t) (impl_ext_log spec_ext_log : ext_log_t) =>
      Forall (fun p => interp_spred2
                      (mk_post_pkg impl_machine impl_st impl_sigma impl_st' impl_ext_log)
                      (mk_post_pkg SymbSpecDefs.spec_machine spec_st spec_sigma spec_st' spec_ext_log) p)
        (sim_sm_post core).
  (* Lemma oraat_schedule_ok_impl_sm: *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule (Impl.sm_schedule)) = true. *)
  (* Proof. *)
  (*   vm_compute. reflexivity. *)
  (* Qed. *)

  (* Lemma oraat_schedule_ok_spec_sm: *)
  (*   forall core, *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule (map_scheduler Machine.RlSm (Machine.sm_schedule core))) = true. *)
  (* Proof. *)
  (*   destruct core; vm_reflect. *)
  (* Qed. *)
Ltac assert_oraat_types sched htype hwf_st' wf_ext' core :=
  match type of sched with
  | interp_scheduler ?sigma ?int_fns ?struct_defs ?st ?rules ?sched = Success ?log =>
      assert (Typechecking.typecheck_schedule (SortedRegEnv.to_list reg_type_env)
                _ext_fn_tys int_fns struct_defs sched rules = Success tt) as htype by (destruct core; vm_reflect);
      assert (strong_WF_state reg_type_env (commit_update st (Log__koika log)) /\
                WF_ext_log _ext_fn_tys (Log__ext log)) as (hwf_st' & wf_ext') by
          (eapply typecheck_scheduler_correct'' with (ext_sigma := sigma) (1 := htype); eauto)
  end.

Ltac solve_sim_interp_scheduler_satisfies_spec oraat_impl oraat_spec file_ok:=
  unfold sim_interp_scheduler_satisfies_spec;
    intros core * _ hwf_impl hwf_spec hwf_impl_sigma hwf_spec_sigma hwf_impl_int hwf_spec_int himpl_sched hspec_sched hpre.

  Theorem sim_step_correct_sm_sched:
    forall core,
     sim_interp_scheduler_satisfies_spec
        reg_type_env _ext_fn_tys
        id_int_fns id_int_fns
        id_struct_defs id_struct_defs
        id_rules id_rules Impl.sm_schedule (map_scheduler Machine.RlSm (sm_schedule core)) unit
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           SMPre EnclaveParams.enclave_sig core impl_st spec_st impl_sigma spec_sigma)
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           SMPost EnclaveParams.enclave_sig core impl_st spec_st impl_st' spec_st' impl_sigma spec_sigma impl_ext spec_ext).
   Proof.
    solve_sim_interp_scheduler_satisfies_spec
      oraat_schedule_ok_impl_core oraat_schedule_ok_spec_core sim_step_correct_core.
    assert_oraat_types himpl_sched himpl_type hwf_impl' hwf_impl_ext' core.
    assert_oraat_types hspec_sched hspec_type hwf_spec' hwf_spec_ext' core.
    (* specialize @oraat_interp_scheduler__conflicts_correct with *)
    (*      (1 := strong_WF_state_weaken _ _ hwf_impl) (2 := hwf_impl_sigma) (3 := hwf_impl_int) (6 := himpl_sched) (4 := himpl_type) (5 := oraat_schedule_ok_impl_sm). intros Horaat_impl. *)
    (* specialize @oraat_interp_scheduler__conflicts_correct with *)
    (*      (1 := strong_WF_state_weaken _ _ hwf_spec) (2 := hwf_spec_sigma) (3 := hwf_spec_int) (6 := hspec_sched) (4 := hspec_type) (5 := oraat_schedule_ok_spec_sm core). intros Horaat_spec. *)
    split_ands_in_goal; auto.
    specialize (sim_step_correct_sm core) as Hfile.
    apply Hfile.
    - revert hpre.
      eapply forall_interp_spred2_package_equiv'; eauto.
      destruct core; solve_package_equiv.
    - solve_machine_to_prop (oraat_schedule_ok_impl_sm).
      set (strip_dbg_sched_list _ ) as l in *.
      assert (l = (map (fun rl => id_transform_action _id (rules rl)) (list_of_schedule Impl.sm_schedule))) as Hl.
      { vm_reflect. }
        rewrite Hl. apply interp_scheduler_list_equiv. assumption.
    - solve_machine_to_prop idtac.
      set (strip_dbg_sched_list _ ) as l in *.
      assert (l = (map (fun rl => id_transform_action _id (rules rl))
                     (list_of_schedule (map_scheduler Machine.RlSm (Machine.sm_schedule core))))) as Hl.
      { destruct core; vm_reflect. }
        rewrite Hl.
        apply interp_scheduler_list_equiv.
        assumption.
   Qed.

End SimSM.

(* Module TestSimSm. *)
(*   Require Import koikaExamples.Enclaves.External. *)

(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module Files := SimSM EnclaveParams SecurityParams . *)

(*   Module File1. *)
(*     Definition file := Eval vm_compute in (Files.sim_sm_file CoreId1). *)
(*     Extraction "TestSimSm.File1.ml" struct_sz vect_t file. *)
(*   End File1. *)
(* End TestSimSm. *)

Module Type AbstractStepsDefs
  (EnclaveParams: EnclaveParams_sig)
  (SecurityParams: SecurityParams_sig EnclaveParams)
  (SimCore: SimCoreDefs EnclaveParams SecurityParams)
  (SimMem: SimMemDefs EnclaveParams SecurityParams)
  (SimSM: SimSMDefs EnclaveParams SecurityParams).

  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.
  Import Utils.PfHelpers.
  Definition spec_mid_ext := mk_mid_ext MachineSpec.

  Module AbstractMemStep.


    Definition abs_mem_step_pre core :=
    preprocess_fancy_spreds (
                                 sim_invariants EnclaveParams.enclave_sig core impl_init spec_init
                                   impl_get_field spec_get_field) ++
                             preprocess_fancy_spreds (
                                SimCore.post_conds core impl_init spec_init impl_mid spec_mid
                                   impl_get_field spec_get_field impl_mid_ext spec_mid_ext) ++
                             preprocess_fancy_spreds (
                                SimMem.post_conds core impl_mid spec_mid impl_final spec_final
                                   impl_get_field spec_get_field impl_final_ext spec_final_ext).
    Definition abs_mem_post_conds
      (core : ind_core_id)       := SimMem.post_conds core impl_init spec_init impl_final spec_final
                             impl_get_field spec_get_field impl_committed_ext spec_committed_ext.

    Definition abs_mem_step_post core :=
      preprocess_fancy_spreds
         (abs_mem_post_conds core).
    Definition sim_mem_step_file core : file_t :=
      {| file_machines := AbstractProduct PfDefs.dummy_machine PfDefs.dummy_machine;
         file_assumptions := abs_mem_step_pre core;
         file_assertions := abs_mem_step_post core
      |}.

  End AbstractMemStep.

  Module AbstractSmStep .

    Definition abs_sm_step_pre core :=
    preprocess_fancy_spreds (
                                 sim_invariants EnclaveParams.enclave_sig core impl_init spec_init
                                   impl_get_field spec_get_field) ++
                             preprocess_fancy_spreds (
                                SimMem.post_conds core impl_init spec_init impl_mid spec_mid
                                   impl_get_field spec_get_field impl_mid_ext spec_mid_ext) ++
                             preprocess_fancy_spreds (
                                SimSM.post_conds core impl_mid spec_mid impl_final spec_final
                                   impl_get_field spec_get_field impl_final_ext spec_final_ext).
    Definition abs_sm_step_post core :=
      preprocess_fancy_spreds
         (sim_post_conds EnclaveParams.enclave_sig core impl_init spec_init impl_final spec_final
                         impl_get_field spec_get_field impl_committed_ext spec_committed_ext).

    Definition sim_sm_step_file core : file_t :=
      {| file_machines := AbstractProduct PfDefs.dummy_machine PfDefs.dummy_machine;
         file_assumptions := abs_sm_step_pre core;
         file_assertions := abs_sm_step_post core
      |}.

  End AbstractSmStep.
End AbstractStepsDefs .

Module Type SMT_AbstractSteps_sig
  (EnclaveParams: EnclaveParams_sig)
  (SecurityParams: SecurityParams_sig EnclaveParams)
  (SimCore: SimCoreDefs EnclaveParams SecurityParams)
  (SimMem: SimMemDefs EnclaveParams SecurityParams)
  (SimSM: SimSMDefs EnclaveParams SecurityParams)
  (AbstractStepsDefs: AbstractStepsDefs EnclaveParams SecurityParams SimCore SimMem SimSM).
  Import AbstractStepsDefs.
  Parameter SMT_MemStep: forall core, SymbolicInterp.WF_product_file (AbstractMemStep.sim_mem_step_file core) = true.
  Parameter SMT_SMStep: forall core, SymbolicInterp.WF_product_file (AbstractSmStep.sim_sm_step_file core) = true.
End SMT_AbstractSteps_sig.

Module AbstractSteps (EnclaveParams: EnclaveParams_sig)
                     (SecurityParams: SecurityParams_sig EnclaveParams)
                     (SimCore: SimCoreDefs EnclaveParams SecurityParams)
                     (SimMem: SimMemDefs EnclaveParams SecurityParams)
                     (SimSM: SimSMDefs EnclaveParams SecurityParams)
                     (AbstractStepsDefs: AbstractStepsDefs EnclaveParams SecurityParams SimCore SimMem SimSM)
                     (SmtOk: SMT_AbstractSteps_sig EnclaveParams SecurityParams SimCore
                                                   SimMem SimSM AbstractStepsDefs).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.
  Import Utils.PfHelpers.
  Import AbstractStepsDefs.
  Module AbstractMemStep.
    Import AbstractMemStep.
    Theorem sim_step_correct_mem: forall core,
      symbolic_evaluate_file_success_abstract_product
        impl_machine SymbSpecDefs.spec_machine
        (abs_mem_step_pre core) (abs_mem_step_post core).
    Proof.
      intros.
      specialize symbolic_evaluate_file_success with (file := sim_mem_step_file core) .
      unfold sim_mem_step_file in *. unfold file_machines. intros. specialize (H (SmtOk.SMT_MemStep core)). revert H.
      unfold file_assumptions. unfold file_assertions. auto.
    Qed.

  End AbstractMemStep.
  Module AbstractSmStep .
    Import AbstractSmStep.
    Theorem sim_step_correct_sm: forall core,
      symbolic_evaluate_file_success_abstract_product
        impl_machine SymbSpecDefs.spec_machine
        (abs_sm_step_pre core) (abs_sm_step_post core).
    Proof.
      intros.
      specialize symbolic_evaluate_file_success with (file := sim_sm_step_file core) .
      unfold sim_sm_step_file in *. unfold file_machines. intros. specialize (H (SmtOk.SMT_SMStep core)). revert H.
      unfold file_assumptions. unfold file_assertions. auto.
    Qed.
  End AbstractSmStep.
End AbstractSteps.
(* Module TestAbstractMemStep. *)
(*   Require Import koikaExamples.Enclaves.External. *)

(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module Files := AbstractSteps.AbstractMemStep EnclaveParams SecurityParams . *)

(*   (* Module File0. *) *)
(*   (*   Definition file := Eval vm_compute in (Files.sim_mem_step_file CoreId0). *) *)
(*   (*   Extraction "../../../../AbstractSim0_Mem.ml" struct_sz vect_t file. *) *)
(*   (* End File0. *) *)

(*   Module File1. *)
(*     Definition file := Eval vm_compute in (Files.sim_mem_step_file CoreId1). *)
(*     Extraction "TestAbstractMemStep.File1.ml" struct_sz vect_t file. *)
(*   End File1. *)

(* End TestAbstractMemStep. *)




(* Module TestAbstractSmStep. *)
(*   Require Import koikaExamples.Enclaves.External. *)

(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module Files := AbstractSmStep EnclaveParams SecurityParams . *)

(*   Module File0. *)
(*     Definition file := Eval vm_compute in (Files.sim_sm_step_file CoreId0). *)
(*     Extraction "../../../../AbstractSim0_Sm.ml" struct_sz vect_t file. *)
(*   End File0. *)
(* End TestAbstractSmStep. *)

(* Module ModularDefs (EnclaveParams: EnclaveParams_sig) *)
(*                (SecurityParams: SecurityParams_sig EnclaveParams) *)
(*                (SymbSpec: SymbSpec EnclaveParams SecurityParams). *)
(*                   (* : PfSimProofs_sig EnclaveParams SecurityParams SymbSpec. *) *)

(*   Import SecurityParams.Machine. *)
(*   Import SecurityParams.Impl. *)
(*   Import SymbSimDefs. *)
(*   (* Definition spec_schedule core := *) *)
(*   (*   match core with *) *)
(*   (*   | CoreId0 => Core0Machine.schedule *) *)
(*   (*   | CoreId1 => Core1Machine.schedule *) *)
(*   (*   end. *) *)

(*   Definition impl_schedule_list : list (Machine.rule_name_t * string) := *)
(*       map (fun rl => (rl, show rl)) (list_of_schedule (FullMachine.schedule)). *)
(*   Definition impl_typecheck_fn rl : result (aaction * nat) unit := *)
(*       typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl). *)

(*   Definition impl_schedule := *)
(*       preprocess_schedule impl_typecheck_fn rules impl_schedule_list. *)


(*   Definition sim0_file : file_t := *)
(*     {| file_machines := Product impl_machine SymbSpecDefs.spec_machine *)
(*                                 impl_schedule SymbSpec.Spec0Machine.spec0_schedule; *)
(*        file_assumptions := preprocess_fancy_spreds *)
(*                              (sim_pre_conds EnclaveParams.enclave_sig CoreId0 impl_init spec_init impl_get_field spec_get_field); *)
(*        file_assertions := preprocess_fancy_spreds *)
(*                              (sim_post_conds EnclaveParams.enclave_sig CoreId0 impl_init spec_init impl_final spec_final *)
(*                                             impl_get_field spec_get_field impl_final_ext spec_final_ext) *)
(*     |}. *)
(*   (* Definition sim0_file: file_t := Eval vm_compute in sim0_file'. *) *)

(*   Definition sim1_file : file_t := *)
(*     {| file_machines := Product impl_machine SymbSpecDefs.spec_machine *)
(*                                 impl_schedule SymbSpec.Spec1Machine.spec1_schedule; *)
(*        file_assumptions := preprocess_fancy_spreds *)
(*                              (sim_pre_conds EnclaveParams.enclave_sig CoreId1 impl_init spec_init impl_get_field spec_get_field); *)
(*        file_assertions := preprocess_fancy_spreds *)
(*                              (sim_post_conds EnclaveParams.enclave_sig CoreId1 impl_init spec_init impl_final spec_final *)
(*                                             impl_get_field spec_get_field impl_final_ext spec_final_ext) *)
(*     |}. *)
(*   Axiom SMT_file0: SymbolicInterp.WF_product_file sim0_file = true. *)


(*   Axiom SMT_file1: SymbolicInterp.WF_product_file sim1_file = true. *)

(*   Definition spec_schedule' core := *)
(*     match core with *)
(*     | CoreId0 => SymbSpec.Spec0Machine.spec0_schedule *)
(*     | CoreId1 => SymbSpec.Spec1Machine.spec1_schedule *)
(*     end. *)
(* End ModularDefs. *)
(* Module Test_Sim. *)
(*   Require Import koikaExamples.Enclaves.External. *)

(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module SymbSpec := Empty <+ SymbSpec.SymbSpec EnclaveParams SecurityParams. *)
(*   Module PfDefs := Empty <+ PfSimDefs EnclaveParams SecurityParams SymbSpec. *)

(*   Module File0. *)
(*     Definition file := Eval vm_compute in PfDefs.sim0_file. *)
(*     Extraction "../../../../Sim0.ml" struct_sz vect_t file. *)
(*   End File0. *)

(*   Module File1. *)
(*     Definition file := Eval vm_compute in PfDefs.sim1_file. *)
(*     Extraction "../../../../Sim1.ml" struct_sz vect_t file. *)
(*   End File1. *)

(* End Test_Sim. *)


Module ModularProof (EnclaveParams: EnclaveParams_sig)
                       (SecurityParams: SecurityParams_sig EnclaveParams)
                       (SymbSpec: SymbSpec EnclaveParams SecurityParams)
                       (SimCoreDefs: SimCoreDefs EnclaveParams SecurityParams)
                       (SimMemDefs: SimMemDefs EnclaveParams SecurityParams)
                       (SimSMDefs: SimSMDefs EnclaveParams SecurityParams)
                       (AbstractStepsDefs: AbstractStepsDefs EnclaveParams SecurityParams
                                             SimCoreDefs SimMemDefs SimSMDefs)
                       (SmtOk_Core: SMT_SimCore_sig EnclaveParams SecurityParams SimCoreDefs)
                       (SmtOk_Mem : SMT_SimMem_sig EnclaveParams SecurityParams SimMemDefs)
                       (SmtOk_SM : SMT_SimSM_sig EnclaveParams SecurityParams SimSMDefs)
                       (SmtOk_AbsDefs: SMT_AbstractSteps_sig EnclaveParams SecurityParams SimCoreDefs
                                                             SimMemDefs SimSMDefs AbstractStepsDefs)
                       : PfSimProofs_sig EnclaveParams SecurityParams SymbSpec.
  (* Module Import ModularDef := ModularDefs EnclaveParams SecurityParams SymbSpec. *)
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SymbSimDefs.
  Module AbsSteps := AbstractSteps EnclaveParams SecurityParams SimCoreDefs SimMemDefs SimSMDefs
                                   AbstractStepsDefs SmtOk_AbsDefs.


  Module AbsSimSM := AbsSteps.AbstractSmStep.
  Module AbsSimMem := AbsSteps.AbstractMemStep.
  Module SimCore := SimCore EnclaveParams SecurityParams SimCoreDefs SmtOk_Core.
  Module SimMem := SimMem EnclaveParams SecurityParams SimMemDefs SmtOk_Mem.
  Module SimSM := SimSM EnclaveParams SecurityParams SimSMDefs SmtOk_SM.

  (* Theorem sim_step_correct: forall core, *)
  (*   symbolic_evaluate_file_success_product *)
  (*     impl_machine SymbSpecDefs.spec_machine impl_schedule (spec_schedule' core) *)
  (*       (preprocess_fancy_spreds (sim_pre_conds EnclaveParams.enclave_sig core impl_init spec_init impl_get_field spec_get_field)) *)
  (*       (preprocess_fancy_spreds (sim_post_conds EnclaveParams.enclave_sig core impl_init spec_init impl_final spec_final *)
  (*                                                impl_get_field spec_get_field *)
  (*                                                impl_final_ext spec_final_ext)). *)
  (* Proof. *)
  (*   destruct core. *)
  (*   - pose proof SMT_file0. *)
  (*     specialize symbolic_evaluate_file_success with (file := sim0_file) . *)
  (*     propositional. *)
  (*   - pose proof SMT_file1. *)
  (*     specialize symbolic_evaluate_file_success with (file := sim1_file) . *)
  (*     propositional. *)
  (* Qed. *)


  (* Lemma impl_schedule_oraat_ok: *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule FullMachine.schedule) = true. *)
  (* Proof. *)
  (*   vm_compute. reflexivity. *)
  (* Qed. *)

  (* Lemma spec_schedule_oraat_ok: *)
  (*   forall core, *)
  (*    oraat_ok id_int_fns id_rules (list_of_schedule (spec_schedule core)) = true. *)
  (* Proof. *)
  (*   destruct core; vm_reflect. *)
  (* Qed. *)
  Import ProofUtils.

  Definition modular_schedule := [schedule_app core0_schedule core1_schedule; Impl.mem_schedule; Impl.sm_schedule].

  Lemma impl_interp_modular_schedule :
    forall sigma st log,
        interp_scheduler
          sigma id_int_fns id_struct_defs st id_rules
               Impl.schedule = Success log ->
      interp_modular_schedule
          sigma id_int_fns id_struct_defs id_rules st
               modular_schedule =
        Success (commit_update st log.(Log__koika), log.(Log__ext)).
  Proof.
    intros. eapply check_modular_conflicts_correct.
    - vm_compute. reflexivity.
    - assumption.
  Qed.

  Definition spec_modular_schedule core : list (scheduler) :=
    [core_schedule core
    ;map_scheduler Machine.RlMem (mem_schedule core)
    ;map_scheduler Machine.RlSm (sm_schedule core)].

  Lemma spec_interp_modular_schedule :
    forall core sigma st log,
        interp_scheduler
          sigma id_int_fns id_struct_defs st id_rules
               (spec_schedule core)= Success log ->
      interp_modular_schedule
          sigma id_int_fns id_struct_defs id_rules st
               (spec_modular_schedule core) =
        Success (commit_update st log.(Log__koika), log.(Log__ext)).
  Proof.
    intros. eapply check_modular_conflicts_correct.
    - destruct core; vm_compute; reflexivity.
    - destruct core; auto.
  Qed.
  (* Lemma oraat_schedule_ok_impl_mem: *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule (Impl.mem_schedule)) = true. *)
  (* Proof. *)
  (*   vm_compute. reflexivity. *)
  (* Qed. *)
  (* Lemma oraat_schedule_ok_impl_sm: *)
  (*   oraat_ok id_int_fns id_rules (list_of_schedule (Impl.sm_schedule)) = true. *)
  (* Proof. *)
  (*   vm_compute. reflexivity. *)
  (* Qed. *)



Lemma Sim_pre_implies_core_pre:
  forall core impl_st spec_st impl_sigma spec_sigma impl_pkg spec_pkg ,
  SimPre EnclaveParams.enclave_sig core impl_st spec_st impl_sigma spec_sigma ->
  impl_machine = impl_pkg.(pkg_machine)  ->
  impl_st = impl_pkg.(pkg_init_st) ->
  SymbSpecDefs.spec_machine = spec_pkg.(pkg_machine) ->
  spec_st = spec_pkg.(pkg_init_st) ->
  Forall (fun p : spred => interp_spred2 impl_pkg spec_pkg  p) (SimCoreDefs.sim_core_pre core).
Proof.
  intros * hpre; intros. subst.
  consider SimPre. consider sim_pre_conds.
  consider SimCoreDefs.sim_core_pre.
  repeat rewrite Forall_app in hpre. propositional.
  rewrite<-forall_preprocess_fancy_spreds_correct2 in hpre0.
  rewrite H in *. rewrite H1 in *.
  eapply forall_interp_spred2_package_equiv'; eauto.
  destruct core; do_magic false solve_package_equiv.
Qed.

(* Ltac specialize_sim fn HPost impl_step spec_step HPre := *)
(*   pose proof fn as HPost; unfold symbolic_evaluate_file_success_product in HPost; *)
(*   match type of impl_step with *)
(*   | interp_scheduler ?sigma _ _ ?st ?rules ?sched  = Success ?log=> *)
(*       specialize HPost  with (impl_sigma := sigma)  (impl_st := st) (impl_ext_log' := Log__ext log) *)
(*                              (impl_st' := commit_update st (Log__koika log)) *)
(*   end; *)
(*   match type of spec_step with *)
(*   | interp_scheduler ?sigma _ _ ?st ?rules ?sched  = Success ?log=> *)
(*       specialize HPost  with (spec_sigma := sigma)  (spec_st := st) (spec_ext_log' := Log__ext log) *)
(*                              (spec_st' := commit_update st (Log__koika log)) *)
(*   end; *)
(*   match type of HPost with *)
(*   | ?pre -> ?x -> ?y -> ?z  => *)
(*       assert pre as HPre; [ | specialize HPost with (1 := HPre); assert_pre_and_specialize  HPost; [ | assert_pre_and_specialize HPost] ] *)
(*   end. *)
Ltac specialize_sim fn HPost impl_step spec_step hwf_impl_st' hwf_spec_st' hwf_impl_ext hwf_spec_ext:=
  pose proof fn as HPost; unfold sim_interp_scheduler_satisfies_spec in HPost;
  match type of impl_step with
  | interp_scheduler ?sigma _ _ ?st ?rules ?sched  = Success ?log=>
      specialize HPost  with (impl_sigma := sigma) (impl_st := st) (impl_log := log)
  end;
  match type of spec_step with
  | interp_scheduler ?sigma _ _ ?st ?rules ?sched  = Success ?log=>
      specialize HPost with (spec_sigma := sigma) (spec_st := st) (spec_log := log)
  end; specialize HPost with (1 := tt);
  repeat (assert_pre_and_specialize HPost; [assumption| ]);
  (* let HNew := fresh in  *)
  (*   assert_conclusion_of HPost HNew; *)
  (*   [ apply HPost; auto | clear HPost ]; *)
    try (destruct HPost as (hwf_impl_st' & hwf_spec_st' & hwf_impl_ext & hwf_spec_ext & HPost)).


Ltac t_symb ::=
match goal with
| H: strong_WF_state _ ?st |- WF_state _ ?st =>
    solve[apply strong_WF_state_weaken in H; apply H]
| |- WF_ext_log _ SortedExtFnEnv.empty =>
      apply WF_ext_log__empty
end.

Ltac solve_In_to_find_remove_regs :=
  let x := fresh in
  set (remove_regs _ _) as x; vm_compute in x; solve_In_to_find.
Lemma SimCorePost_Implies_MemPre:
  forall core impl_st spec_st impl_st' spec_st' impl_ext_log spec_ext_log impl_sigma spec_sigma,
    SimPre EnclaveParams.enclave_sig core impl_st spec_st impl_sigma spec_sigma ->
    SimCore.CorePost EnclaveParams.enclave_sig core impl_st spec_st impl_st' spec_st' impl_sigma spec_sigma
                     impl_ext_log spec_ext_log ->
    SimMem.MemPre EnclaveParams.enclave_sig core impl_st' spec_st' impl_sigma spec_sigma.
Proof.
  consider SimMem.MemPre. consider SimCore.CorePost.
  consider SimMemDefs.sim_mem_pre.
  consider SimMemDefs.pre_conds.
  consider SimCoreDefs.sim_core_post.
  intros * hpre hcore.
  rewrite forall_interp_spred2_preprocess_app_iff.
  rewrite Forall_app.
  rewrite Forall_app in hcore. destruct hcore as (hinv & hpost).
  split.
  - rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_impl_init_reg_with_final)).
    2 : { intros. apply replace_spred2_impl_init_reg_with_final_correct; auto. }
    rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_spec_init_reg_with_final)).
    2 : { intros. apply replace_spred2_spec_init_reg_with_final_correct; auto. }
    destruct core; change_Forall_lists1 hinv.
    + revert hinv. eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
    + revert hinv. eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
  - rewrite forall_preprocess_fancy_spreds_correct2 in hpost. revert hpre. unfold SimPre. intros hpre.
    prop_pose_with_custom himpl_taint (CustomSimTaint MachineImpl) hpost.
    prop_pose_with_custom hspec_taint (CustomSimTaint MachineSpec) hpost.

    repeat constructor; cbn - [_sid _fld _id].
    + prop_pose_with_custom hfoo (CustomMemSim MemSimExtResponse) hpre.
      cbn - [_id _sid _fld] in hfoo.
      intros * hlen' hturn.
      setoid_rewrite himpl_taint.
      setoid_rewrite himpl_taint in hturn.
      setoid_rewrite hspec_taint.
      auto.
      all: do_magic false solve_In_to_find_remove_regs.
    + prop_pose_with_custom hfoo (CustomMemSim MemImplEmpty) hpre.
      intros * hlen'.
      setoid_rewrite himpl_taint.
      apply hfoo; auto.
      all: do_magic false solve_In_to_find_remove_regs.
    + prop_pose_with_custom hfoo (CustomMemSim MemSpecEmpty) hpre.
      intros * hlen'.
      setoid_rewrite hspec_taint.
      apply hfoo; auto.
      all: do_magic false solve_In_to_find_remove_regs.
    + intros * hlen'.
      prop_pose_with_custom hfoo (CustomMemSim (MemImplExtCorrectCore CoreId0)) hpre.
      setoid_rewrite himpl_taint. apply hfoo; auto.
      all: do_magic false solve_In_to_find_remove_regs.
    + intros * hlen'.
      prop_pose_with_custom hfoo (CustomMemSim (MemImplExtCorrectCore CoreId1)) hpre.
      setoid_rewrite himpl_taint. apply hfoo; auto.
      all: do_magic false solve_In_to_find_remove_regs.
Qed.
Lemma SimMemPost_Implies_SMPre:
  forall core impl_st spec_st impl_st' spec_st' impl_ext_log spec_ext_log impl_sigma spec_sigma ,
    SimPre EnclaveParams.enclave_sig core impl_st spec_st impl_sigma spec_sigma ->
    SimMem.MemPost EnclaveParams.enclave_sig core impl_st spec_st impl_st' spec_st' impl_sigma spec_sigma
                     impl_ext_log spec_ext_log ->
    SimSM.SMPre EnclaveParams.enclave_sig core impl_st' spec_st' impl_sigma spec_sigma.
Proof.
  consider SimSM.SMPre. consider SimSMDefs.sim_sm_pre. consider SimSMDefs.pre_conds.
  consider SimMem.MemPost. consider SimMemDefs.sim_mem_post. consider SimMemDefs.post_conds.
  intros * hpre hpost.
  rewrite forall_interp_spred2_preprocess_app_iff.
  rewrite Forall_app.
  rewrite forall_interp_spred2_preprocess_app_iff in hpost.
  rewrite Forall_app in hpost. destruct hpost as (hinv & hpost).
  split.
  - rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_impl_init_reg_with_final)).
    2 : { intros. apply replace_spred2_impl_init_reg_with_final_correct; auto. }
    rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_spec_init_reg_with_final)).
    2 : { intros. apply replace_spred2_spec_init_reg_with_final_correct; auto. }
    destruct core; change_Forall_lists1 hinv.
    + revert hinv. eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
    + revert hinv. eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
  - rewrite forall_preprocess_fancy_spreds_correct2 in hpost.
    unfold sim_sm_pre_conds.
    prop_pose_with_custom himpl_taint (CustomSimTaint MachineImpl) hpost.
    prop_pose_with_custom hspec_taint (CustomSimTaint MachineSpec) hpost.
    repeat constructor.
    + cbn - [_id _fld _sid].
      setoid_rewrite himpl_taint.
      prop_pose_with_custom hfoo CustomRegStateRunning hpre; auto.
      destruct core; do_magic true solve_In_to_find_remove_regs.
    + cbn - [_id _fld _sid].
      prop_pose_with_custom hfoo CustomExtLedSim hpre.
      intro. setoid_rewrite hspec_taint. apply hfoo.
      destruct core; do_magic false solve_In_to_find_remove_regs.
     + cbn - [_id _fld _sid].
       prop_pose_with_custom hfoo CustomExtUartReadSim hpre.
       intro. setoid_rewrite hspec_taint. apply hfoo.
       destruct core; do_magic false solve_In_to_find_remove_regs.
     + cbn - [_id _fld _sid].
       prop_pose_with_custom hfoo CustomExtUartWriteSim hpre.
       intro. setoid_rewrite hspec_taint. apply hfoo.
       destruct core; do_magic false solve_In_to_find_remove_regs.
      + cbn - [_id _fld _sid].
       prop_pose_with_custom hfoo CustomExtFinishSim hpre.
       intro. setoid_rewrite hspec_taint. apply hfoo.
       destruct core; do_magic false solve_In_to_find_remove_regs.
  Qed.
Lemma SimPre_implies_invariants:
  forall core impl_st spec_st impl_sigma spec_sigma pkg1 pkg2 ,
  SimPre EnclaveParams.enclave_sig core impl_st spec_st impl_sigma spec_sigma ->
  pkg1.(pkg_machine).(file_struct_defs) = impl_machine.(file_struct_defs) ->
  pkg2.(pkg_machine).(file_struct_defs) = SymbSpecDefs.spec_machine.(file_struct_defs) ->
  pkg1.(pkg_init_st) = impl_st ->
  pkg2.(pkg_init_st) = spec_st ->
  Forall (fun p => interp_spred2 pkg1 pkg2 p)
    (preprocess_fancy_spreds
       (sim_invariants EnclaveParams.enclave_sig core impl_init spec_init impl_get_field spec_get_field)).
Proof.
  intros * hpre. intros.
  consider SimPre. consider sim_pre_conds.
  rewrite Forall_app in hpre. split_ands_in_hyps.
  rewrite<-forall_preprocess_fancy_spreds_correct2 in hpre0.
  revert hpre0.
  eapply forall_interp_spred2_package_equiv'.
  destruct core.
  - solve_package_equiv.
  - solve_package_equiv.
Qed.
  Theorem step_sim_sched_correct:
    forall core,
     sim_interp_scheduler_satisfies_spec
        reg_type_env _ext_fn_tys
        id_int_fns id_int_fns
        id_struct_defs id_struct_defs
        id_rules id_rules FullMachine.schedule (spec_schedule core) unit
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           SimPre EnclaveParams.enclave_sig core impl_st spec_st impl_sigma spec_sigma)
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           SimPost EnclaveParams.enclave_sig core impl_st spec_st impl_st' spec_st' impl_sigma spec_sigma impl_ext spec_ext).
  Proof.
    unfold sim_interp_scheduler_satisfies_spec.
    intros * ? hwf_impl hwf_spec hwf_impl_sigma hwf_spec_sigma hwf_impl_fns hwf_spec_fns
             himpl_step hspec_step hpre.
    specialize typecheck_scheduler_correct'' with (5 := himpl_step) (2 := hwf_impl) (3 := hwf_impl_sigma) (4 := hwf_impl_fns) (1 := eq_refl); intros (hwf_impl' & wf_impl_ext').

    assert (strong_WF_state reg_type_env (commit_update spec_st (Log__koika spec_log)) /\
            WF_ext_log _ext_fn_tys (Log__ext spec_log)) as (hwf_spec' & wf_spec_ext').
    { destruct core;  eapply typecheck_scheduler_correct'' with (5 := hspec_step) (2 := hwf_spec) (3 := hwf_spec_sigma) (4 := hwf_spec_fns) (1 := eq_refl); auto.
    }
    split_ands_in_goal; auto.

    apply impl_interp_modular_schedule in himpl_step.
    apply spec_interp_modular_schedule in hspec_step.
    revert himpl_step. revert hspec_step.
    unfold modular_schedule. unfold spec_modular_schedule. unfold interp_modular_schedule. intros.
    step_modular_schedule himpl_step impl_step_core impl_st_core impl_log_core.
    step_modular_schedule himpl_step impl_step_mem impl_st_mem impl_log_mem.
    step_modular_schedule himpl_step impl_step_sm impl_st_sm impl_log_sm.
    step_modular_schedule hspec_step spec_step_core spec_st_core spec_log_core.
    step_modular_schedule hspec_step spec_step_mem spec_st_mem spec_log_mem.
    step_modular_schedule hspec_step spec_step_sm spec_st_sm spec_log_sm.

    assert (SimCore.CorePre EnclaveParams.enclave_sig core impl_st spec_st impl_sigma spec_sigma) as HCorePre.
    { clear - hpre. eapply Sim_pre_implies_core_pre; eauto. }
    specialize_sim (SimCore.sim_step_correct_core_sched core)
                   HPost__ImplCore impl_step_core spec_step_core
                   hwf_impl_core' hwf_spec_core' hwf_impl_ext_core hwf_spec_ext_core.
    assert (SimMem.MemPre EnclaveParams.enclave_sig core impl_st_core spec_st_core impl_sigma spec_sigma) as HMemPre.
    { eapply SimCorePost_Implies_MemPre with (1 := hpre) (2 := HPost__ImplCore). }

    specialize_sim (SimMem.sim_step_correct_mem_sched core )
                   HPost__ImplMem impl_step_mem spec_step_mem
                   hwf_impl_mem' hwf_spec_mem' hwf_impl_ext_mem hwf_spec_ext_mem.

    assert (SimMem.MemPost EnclaveParams.enclave_sig core impl_st spec_st impl_st_mem spec_st_mem impl_sigma spec_sigma
                     (ext_log_app (Log__ext impl_log_mem) (Log__ext impl_log_core))
                     (ext_log_app (Log__ext spec_log_mem) (Log__ext spec_log_core))) as HMemPost.
    { revert HPost__ImplMem. revert HMemPre. unfold SimMem.MemPost. unfold SimMemDefs.sim_mem_post. intros.
      match goal with
      | |- context[interp_spred2 ?_impl_pkg ?_spec_pkg] =>
          set (impl_pkg:= _impl_pkg);
          set (spec_pkg:= _spec_pkg)
      end.
      rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_impl_final_ext_with_committed)).
      2 : { intros. apply replace_spred2_impl_final_ext_with_committed_correct; auto. }
      rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_spec_final_ext_with_committed)).
      2 : { intros. apply replace_spred2_spec_final_ext_with_committed_correct; auto. }
      match goal with
      | |- Forall _ ?xs =>
          replace xs with (AbstractStepsDefs.AbstractMemStep.abs_mem_step_post core)
      end.
      2: { destruct core; vm_reflect. }
      (* destruct spec_log as (spec_log__koika & spec_log__ext). *)
      (* destruct impl_log as (impl_log__koika & impl_log__ext). *)
      (* simpl in hspec_step. simpl in himpl_step. *)
      (* rewrite ext_log_app_empty_r in *. *)
      (* apply Success_inj in hspec_step. *)
      (* apply Success_inj in himpl_step. *)
      (* simplify_tupless; subst. simpl in *. *)

      eapply forall_interp_spred2_package_equiv' with
        (pkg1 := set_ext_log' (set_mid_ext_log (set_mid_st impl_pkg (Some impl_st_core))
                                      (Some (Log__ext impl_log_core)))
                                   (Log__ext impl_log_mem))
        (pkg1' := set_ext_log' (set_mid_ext_log (set_mid_st spec_pkg (Some spec_st_core))
                                      (Some (Log__ext spec_log_core)))
                                   (Log__ext spec_log_mem)).
      { destruct core;
        constructor; unfold package_equiv_taint'; split_ands_in_goal;
          (solve [ left; auto; cbn; rewrite ext_log_app_empty_r; reflexivity ]) || (right; vm_compute; reflexivity).
      }
      apply (AbsSimMem.sim_step_correct_mem  core).
      { unfold AbstractStepsDefs.AbstractMemStep.abs_mem_step_pre.
Import AbstractStepsDefs.
      repeat rewrite Forall_app. simpl. split_ands_in_goal.
        - clear - hpre.
          eapply SimPre_implies_invariants; eauto.
        - clear - HPost__ImplCore.
          revert HPost__ImplCore.
          unfold SimCore.CorePost, SimCoreDefs.sim_core_post, SimCoreDefs.post_conds, mk_post_pkg.
          intros.
          destruct core.
          + replace_final_st_with_mid2.
            replace_final_ext_with_mid2.
            change_Forall_lists1 HPost__ImplCore.
            revert HPost__ImplCore.
            eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
          + replace_final_st_with_mid2.
            replace_final_ext_with_mid2.
            change_Forall_lists1 HPost__ImplCore.
            revert HPost__ImplCore.
            eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
        - move HPost__ImplMem at bottom.
          destruct core.
          + replace_init_st_with_mid2.
            change_Forall_lists1 HPost__ImplMem.
            revert HPost__ImplMem.
            eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
          + replace_init_st_with_mid2.
            change_Forall_lists1 HPost__ImplMem.
            revert HPost__ImplMem.
            eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
      }
      { simpl. unfold WF_abstract_state_set; split_ands_in_goal; try t_symb; eauto with modularity.
      }
      { simpl. unfold WF_abstract_state_set; split_ands_in_goal; try t_symb; eauto with modularity.
      }
    }
    assert (SimSM.SMPre EnclaveParams.enclave_sig core impl_st_mem spec_st_mem impl_sigma spec_sigma) as HSMPre.
    { eapply SimMemPost_Implies_SMPre with (1 := hpre) (2 := HMemPost). }

    specialize_sim (SimSM.sim_step_correct_sm_sched core )
                   HPost__ImplSM impl_step_sm spec_step_sm
                   hwf_impl_sm' hwf_spec_sm' hwf_impl_ext_sm hwf_spec_ext_sm.
    unfold SimPost.
    rewrite<-forall_preprocess_fancy_spreds_correct2.
    match goal with
    | |- context[interp_spred2 ?_impl_pkg ?_spec_pkg] =>
        set (impl_pkg:= _impl_pkg);
        set (spec_pkg:= _spec_pkg)
        (* assert (Forall (fun p : spred => interp_spred2 impl_pkg spec_pkg p) (AbsSimSM.abs_sm_step_post core)) *)
    end.
    rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_impl_final_ext_with_committed)).
    2 : { intros. apply replace_spred2_impl_final_ext_with_committed_correct; auto. }
    rewrite Lift_Forall with (g := (replace_sval_in_spred_base fn_replace_spec_final_ext_with_committed)).
    2 : { intros. apply replace_spred2_spec_final_ext_with_committed_correct; auto. }

    match goal with
    | |- Forall _ ?xs =>
        replace xs with (AbstractSmStep.abs_sm_step_post core)
    end.
    2: { destruct core; vm_reflect. }
    destruct spec_log as (spec_log__koika & spec_log__ext).
    destruct impl_log as (impl_log__koika & impl_log__ext).
    simpl in hspec_step. simpl in himpl_step.
    rewrite ext_log_app_empty_r in *.
    apply Success_inj in hspec_step.
    apply Success_inj in himpl_step.
    simplify_tupless; subst. simpl in *.

    eapply forall_interp_spred2_package_equiv' with
      (pkg1 := set_ext_log' (set_mid_ext_log (set_mid_st impl_pkg (Some impl_st_mem))
                                    (Some (ext_log_app (Log__ext impl_log_mem) (Log__ext impl_log_core))))
                                 (Log__ext impl_log_sm))
      (pkg1' := set_ext_log' (set_mid_ext_log (set_mid_st spec_pkg (Some spec_st_mem))
                                    (Some (ext_log_app (Log__ext spec_log_mem) (Log__ext spec_log_core))))
                                 (Log__ext spec_log_sm)).
    { destruct core;
      constructor; unfold package_equiv_taint'; split_ands_in_goal;
        (solve [ left; auto ]) || (right; vm_compute; reflexivity) || idtac;
        left; cbn; rewrite ext_log_app_empty_r; simplify; reflexivity.
    }
    apply (AbsSimSM.sim_step_correct_sm  core).
    { unfold AbstractSmStep.abs_sm_step_pre.
      repeat rewrite Forall_app. simpl. split_ands_in_goal.
      - clear - hpre.
        eapply SimPre_implies_invariants; eauto.
      - clear - HMemPost.
        revert HMemPost. unfold SimMem.MemPost, SimMemDefs.sim_mem_post, SimMemDefs.post_conds; intros.
        destruct core.
        + replace_final_st_with_mid2.
          replace_final_ext_with_mid2.
          change_Forall_lists1 HMemPost.
          revert HMemPost.
          eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
        + replace_final_st_with_mid2.
          replace_final_ext_with_mid2.
          change_Forall_lists1 HMemPost.
          revert HMemPost.
          eapply forall_interp_spred2_package_equiv'; solve_package_equiv.

      - move HPost__ImplSM at bottom.
        revert HPost__ImplSM.
        unfold SimSM.SMPost, SimSMDefs.sim_sm_post, mk_post_pkg. intros.
        assert (commit_update impl_st_mem (Log__koika impl_log_sm) =
                  commit_update impl_st impl_log__koika) as Himpl_final.
        { rewrite<-H. reflexivity. }
        assert (commit_update spec_st_mem (Log__koika spec_log_sm) =
                  commit_update spec_st spec_log__koika) as Hspec_final.
        { rewrite<-H1. reflexivity. }
        rewrite Himpl_final in HPost__ImplSM.
        rewrite Hspec_final in HPost__ImplSM.

        destruct core.
        + replace_init_st_with_mid2.
          change_Forall_lists1 HPost__ImplSM.
          revert HPost__ImplSM.
          eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
        + replace_init_st_with_mid2.
          change_Forall_lists1 HPost__ImplSM.
          revert HPost__ImplSM.
          eapply forall_interp_spred2_package_equiv'; solve_package_equiv.

    }
    { simpl.
      consider WF_abstract_state_set; split_ands_in_goal; try t_symb; eauto with modularity.
      apply WF_ext_log_app; auto.
    }
    { simpl.
      consider WF_abstract_state_set; split_ands_in_goal; try t_symb; eauto with modularity.
      apply WF_ext_log_app; auto.
    }

    Qed.
End ModularProof.
