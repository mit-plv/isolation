Require Import rv_isolation.Common.
Require Import rv_isolation.Memory.
Require Import rv_isolation.SecurityMonitor.

Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.TypeDefs.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koikaExamples.Enclaves.ProofUtils.
Require Import koikaExamples.Enclaves.PfDefs.
(* Require Import koikaExamples.Enclaves.MemoryDefs. *)

Inductive mem_custom_t :=
| Mem_Taint
| Mem_Tick
| Mem_push_zero0
| Mem_push_zero1
| Mem_push_zero_both
| Mem_push_in_range0
| Mem_push_in_range1
| Mem_purged0
| Mem_purged1
| Mem_purged_preserve (core: ind_core_id)
| Mem_purged_frozen (core: ind_core_id)
| Mem_shreq_invalid
| Mem_no_new_reqs (core: ind_core_id)
| MemExtFn (id: N)
| MemImplExtCorrectCore (core: ind_core_id)
| Mem_custom (str: string)
.


  Import Memory.
  Import PfHelpers.
Notation reg_t := (@Syntax.reg_t debug_id_ty).

Module MemSymbDefs.
  Notation reg_t := (@Syntax.reg_t debug_id_ty).

  Definition fs_mem_push_zero (core: ind_core_id) (reg_init: reg_t -> sval) (ext_log: debug_id_ty -> sval): fancy_spred :=
    let (imem_valid, dmem_valid) := ((Memory.toIMem core) MemReq.valid0, (Memory.toDMem core) MemReq.valid0) in
    {{{ `reg_init (_mid turn)` = #(mem_core_write_turn core) ->
        `reg_init (_mid imem_valid)` = Ob~0 ->
        `reg_init (_mid dmem_valid)` = Ob~0 ->
        `impl_get_field (_sid mem_input) (_fld mem_input "put_valid") (ext_log (_extid ext_mainmem))` = Ob~0
    }}}.

  Definition fs_reset_correct (core: ind_core_id) (reg_fn: reg_t -> sval)
                              (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                              : fancy_spred :=
    {{{ `reg_fn (_mid (purge core))` = #(_enum purge_state "Purged") ->
        {forall x in (map reg_to_debug_id (mem_regs_to_reset core)),
         `reg_fn x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
        }
    }}}.
  Definition fs_fifo_no_new_reqs (reg_init reg_final: reg_t -> sval) (reg_data reg_valid: reg_t) : fancy_spred :=
    {{{ `reg_final reg_valid` = Ob~1 ->
        `reg_init reg_valid` = Ob~1 /\
        `reg_init reg_data` = `reg_final reg_data`
    }}}.

  Definition fs_no_new_reqs (core: ind_core_id) reg_init reg_final : fancy_spred :=
    let (to_imem_data, to_imem_valid) := ((Memory.toIMem core) MemReq.data0, (Memory.toIMem core) MemReq.valid0) in
    let (to_dmem_data, to_dmem_valid) := ((Memory.toDMem core) MemReq.data0, (Memory.toDMem core) MemReq.valid0) in
    {{{ ``fs_fifo_no_new_reqs reg_init reg_final (_mid to_imem_data) (_mid to_imem_valid)`` /\
        ``fs_fifo_no_new_reqs reg_init reg_final (_mid to_dmem_data) (_mid to_dmem_valid) ``
    }}}.


  Definition mem_invariant (reg_fn: reg_t -> sval) get_field: list (mem_custom_t * fancy_spred) :=
    [(Mem_shreq_invalid, {{{ `get_field (_sid shreq) (_fld shreq "valid") (reg_fn (_mid SHReq))` = Ob~0 }}})
    ;(Mem_purged0, fs_reset_correct CoreId0 reg_fn get_field)
    ;(Mem_purged1, fs_reset_correct CoreId1 reg_fn get_field)
    ].
  Definition impl_ext_mem_correct_core
    (core: ind_core_id) (ireg_fn: reg_t -> sval)
    (get_field: debug_id_ty -> debug_id_ty -> sval -> sval): fancy_spred :=
    let (core_bit, turn_bits) := match core with
                                 | CoreId0 => (Ob~0, mem_core0_read_turn)
                                 | CoreId1 => (Ob~1, mem_core1_read_turn)
                                 end in
     {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext ext_mainmem)),
         `get_field (_sid mem_output) (_fld mem_output "get_valid")
                    (impl_ext_app (_extid ext_mainmem) (SBound "arg"))` = Ob~1 ->
         `ireg_fn (_mid Memory.turn)` = #turn_bits ->
         `get_field (_sid Memory.shreq) (_fld Memory.shreq "sourceCore") (ireg_fn (_mid Memory.SHReq))` = #core_bit
      }}}.
  Definition impl_post_ext_mem_correct_core
    (core: ind_core_id) (ifinal_fn: reg_t -> sval) iget_field (iext_log: debug_id_ty -> sval): fancy_spred :=
    let (core_bit, turn_bits) := match core with
                                 | CoreId0 => (Ob~0, mem_core0_read_turn)
                                 | CoreId1 => (Ob~1, mem_core1_read_turn)
                                 end in
    {{{ `ifinal_fn (_mid Memory.turn)` = #turn_bits ->
        `iget_field (_sid mem_input) (_fld mem_input "put_valid") (iext_log (_extid ext_mainmem))` = Ob~1 ->
        `iget_field (_sid Memory.shreq) (_fld Memory.shreq "sourceCore") (ifinal_fn (_mid Memory.SHReq))` = #core_bit
    }}}.

  Definition mem_pre_conds' (reg_init : reg_t -> sval) get_field : list (mem_custom_t * fancy_spred) :=
      [(MemImplExtCorrectCore CoreId0, impl_ext_mem_correct_core CoreId0 reg_init get_field)
      ;(MemImplExtCorrectCore CoreId1, impl_ext_mem_correct_core CoreId1 reg_init get_field)
      ].
  Definition mem_pre_conds (reg_init: reg_t -> sval) get_field : list (mem_custom_t * fancy_spred) :=
     (mem_pre_conds' reg_init get_field) ++ (mem_invariant reg_init get_field).

  Definition almost_zeroed_mainmem_call : list bool := Eval vm_compute in (
    success_or_default (let/res s := _lookup_struct mem_input in
                        subst_field s.(dstruct_fields) (_fld mem_input "get_ready")
                                        (zeroes (Types.struct_sz mem_input)) Ob~1) []).

  Definition mem_post_conds'_preserve (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval) get_field
    : list (mem_custom_t * fancy_spred) :=
  [
    (Mem_Tick, {{{ `reg_init (_mid turn)` + Ob~0~1 = `reg_final (_mid turn)` }}});
    (Mem_push_zero0, fs_mem_push_zero CoreId0 reg_init ext_log );
    (Mem_push_zero1, fs_mem_push_zero CoreId1 reg_init ext_log );
    (Mem_push_zero_both, {{{ `reg_init (_mid turn)` <> #mem_core0_write_turn ->
                             `reg_init (_mid turn)` <> #mem_core1_write_turn ->
                             `ext_log (_extid ext_mainmem)` = #(almost_zeroed_mainmem_call)
                         }}} );
    (MemImplExtCorrectCore CoreId0, impl_post_ext_mem_correct_core CoreId0 reg_final get_field ext_log);
    (MemImplExtCorrectCore CoreId1, impl_post_ext_mem_correct_core CoreId1 reg_final get_field ext_log)
  ] ++ (assert_ext_fns_empty ext_log (fun f => MemExtFn (_id f))
          [( ext_uart_write);( ext_uart_read);( ext_led); ( ext_finish)] ).
  Definition fs_impl_purge_preserved (core: ind_core_id)
                                     (reg_init reg_final: reg_t -> sval)
                                     : fancy_spred :=
    let purge_reg := _mid (purge core) in
    {{{ { {`reg_init purge_reg` = #(_enum purge_state "Ready")
          \/ `reg_init (purge_reg)` = #(_enum purge_state "Purged")} ->
         `reg_final (purge_reg)` = `reg_init (purge_reg)`
        } /\
         { `reg_init (purge_reg)` = #(_enum purge_state "Init") ->
           {`reg_final (purge_reg)` = #(_enum purge_state "Ready") \/
            `reg_final (purge_reg)` = #(_enum purge_state "Init")
           }
         }
    }}}.

  Definition fs_mem_purged_frozen (core: ind_core_id)
                                  (reg_init reg_final: reg_t -> sval)
                                  : fancy_spred :=
    {{{ `reg_init (_mid (purge core))` = #(_enum purge_state "Purged") ->
        {forall x in (map reg_to_debug_id ((private_mem_regs core) ++ (sm_to_memory_fifos core) ++ (memory_to_sm_fifos core))),
         `reg_final x` = `reg_init x`
        }
    }}}.

  Definition mem_post_conds' (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval) get_field : list (mem_custom_t * fancy_spred) :=
    mem_post_conds'_preserve reg_init reg_final ext_log get_field
      ++ [(Mem_Taint, {{{ forall x in (remove_regs reg_list (map reg_to_debug_id (memory_regs))),
                          `reg_final x` = `reg_init x`
                      }}})
         ;(Mem_no_new_reqs CoreId0, fs_no_new_reqs CoreId0 reg_init reg_final)
         ;(Mem_no_new_reqs CoreId1, fs_no_new_reqs CoreId1 reg_init reg_final)
         ;(Mem_purged_preserve CoreId0, fs_impl_purge_preserved CoreId0 reg_init reg_final)
         ;(Mem_purged_preserve CoreId1, fs_impl_purge_preserved CoreId1 reg_init reg_final)
         ;(Mem_purged_frozen CoreId0, fs_mem_purged_frozen CoreId0 reg_init reg_final)
         ;(Mem_purged_frozen CoreId1, fs_mem_purged_frozen CoreId1 reg_init reg_final)
         ].

  Definition mem_post_conds (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval) get_field : list (mem_custom_t * fancy_spred) :=
    (mem_post_conds' reg_init reg_final ext_log get_field) ++ (mem_invariant reg_final get_field).
    Definition impl_machine : machine_t :=
      {| file_registers := reg_types;
         file_ext_sigma := ext_fn_tys;
         file_struct_defs := struct_defs;
      |}.
    Definition spec0_machine : machine_t :=
      {| file_registers := reg_types;
         file_ext_sigma := ext_fn_tys;
         file_struct_defs := struct_defs;
      |}.

    Definition spec1_machine : machine_t :=
      {| file_registers := reg_types;
         file_ext_sigma := ext_fn_tys;
         file_struct_defs := struct_defs;
      |}.
  Definition MemPre (st: Environments.state_t) (sigma: @ext_sigma_t N) : Prop :=
        Forall (fun '(_, p) => interp_fancy_spred
                    {| pkg_machine := impl_machine;
                       pkg_init_st := st; pkg_mid_st := None; pkg_final_st := st; (* don't care *)
                       pkg_sigma := sigma; pkg_mid_ext_log := None;
                       pkg_ext_log' := SortedExtFnEnv.empty; (* don't care *)
                    |} p) (mem_pre_conds impl_init impl_get_field).

  Definition MemPost (st st': Environments.state_t) (sigma: @ext_sigma_t N) (ext_log: ext_log_t): Prop :=
      Forall (fun '(_, p) => interp_fancy_spred
                  {| pkg_machine := impl_machine;
                     pkg_init_st := st; pkg_mid_st := None; pkg_final_st := st';
                     pkg_sigma := sigma; pkg_mid_ext_log := None; pkg_ext_log' := ext_log
                  |} p) (mem_post_conds impl_init impl_final impl_final_ext impl_get_field).

End MemSymbDefs.
Require Import koika.AnnotatedSyntax.



Module Type MemoryProofDefs (EnclaveParams: EnclaveParams_sig)
                         (SecurityParams: SecurityParams_sig EnclaveParams).
                         (* (Pfdefs: PfDefs EnclaveParams SecurityParams) *)
                         (* (MemDefs: MemoryDefs EnclaveParams SecurityParams Pfdefs). *)
  Import Memory.
  Import SecurityParams.Impl.
  Import SecurityParams.Machine.
  Import PfHelpers.
  Import MemSymbDefs.
  Section ImplMachine.
    Notation reg_t := (@reg_t debug_id_ty).
    Definition impl_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (rl, show rl)) (list_of_schedule (Impl.mem_schedule)).
    Definition impl_typecheck_fn rl : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl).
    Definition impl_schedule :=
      preprocess_schedule impl_typecheck_fn rules impl_schedule_list.

    (* Goal preprocess_schedule_success impl_typecheck_fn SM.rules impl_schedule_list = true. *)
    (* Proof. vm_compute; reflexivity. Qed. *)
    (* Lemma impl_schedule_oraat_ok: *)
    (* oraat_ok id_int_fns id_rules (list_of_schedule Impl.mem_schedule) = true. *)
    (* Proof. *)
    (*   vm_compute. reflexivity. *)
    (* Qed. *)

  End ImplMachine.
  Section SpecMachine0.

    Definition spec0_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (Machine.RlMem rl, show (Machine.RlMem rl))) (list_of_schedule (mem_schedule CoreId0)).
    Definition spec0_typecheck_fn rl : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl).
    Definition spec0_schedule :=
      preprocess_schedule spec0_typecheck_fn rules spec0_schedule_list.

    (* Goal preprocess_schedule_success impl_typecheck_fn Memory.rules spec0_schedule_list = true. *)
    (* Proof. vm_compute; reflexivity. Qed. *)

  End SpecMachine0.


  Section SpecMachine1.

    Definition spec1_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (Machine.RlMem rl, show (Machine.RlMem rl))) (list_of_schedule (mem_schedule CoreId1)).
    Definition spec1_typecheck_fn rl : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl).
    Definition spec1_schedule :=
      preprocess_schedule spec1_typecheck_fn rules spec1_schedule_list.

    (* Goal preprocess_schedule_success impl_typecheck_fn Memory.rules spec1_schedule_list = true. *)
    (* Proof. vm_compute; reflexivity. Qed. *)

  End SpecMachine1.

  Module ImplStep.
    Definition file: file_t :=
      {| file_machines := Single impl_machine impl_schedule;
         file_assumptions := preprocess_fancy_spreds (mem_pre_conds impl_init impl_get_field);
         file_assertions := preprocess_fancy_spreds (mem_post_conds impl_init impl_final impl_final_ext impl_get_field);
      |}.

  End ImplStep.
End MemoryProofDefs.

Module Type SMT_Mem_sig (EnclaveParams: EnclaveParams_sig)
                       (SecurityParams: SecurityParams_sig EnclaveParams)
                       (MemDefs: MemoryProofDefs EnclaveParams SecurityParams).

  Parameter SMT_file_ok: SymbolicInterp.WF_single_file MemDefs.ImplStep.file = true.

End SMT_Mem_sig.

(* Module TestMemory. *)
(*   Require Import koikaExamples.Enclaves.External. *)

(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module Memdefs := Empty <+ MemoryProofDefs EnclaveParams SecurityParams. *)
(*   Import Memdefs. *)

(*   Definition file := Eval vm_compute in ImplStep.file. *)
(*   Extraction "TestMemory.ml" struct_sz vect_t file. *)

(* End TestMemory. *)

Module MemProofs (EnclaveParams: EnclaveParams_sig)
                 (SecurityParams: SecurityParams_sig EnclaveParams)
                 (MemDefs: MemoryProofDefs EnclaveParams SecurityParams)
                 (SmtOk: SMT_Mem_sig EnclaveParams SecurityParams MemDefs).
  Import SecurityParams.Impl.
  Import SecurityParams.Machine.
  Import MemSymbDefs.
  Import MemDefs.
  Import SmtOk.
  Theorem impl_step_mem_correct:
    symbolic_evaluate_file_success_single
      impl_machine impl_schedule
        (preprocess_fancy_spreds (mem_pre_conds impl_init impl_get_field))
        (preprocess_fancy_spreds (mem_post_conds impl_init impl_final impl_final_ext impl_get_field)).
  Proof.
    pose proof SMT_file_ok.
    specialize symbolic_evaluate_file_success with (file := ImplStep.file).
    propositional.
  Qed.

  Theorem impl_step_mem_sched_correct:
      interp_scheduler_satisfies_spec reg_type_env _ext_fn_tys id_int_fns id_struct_defs
        id_rules Impl.mem_schedule unit
        (fun st sigma _ => MemPre st  sigma)
        (fun st sigma st' ext_log _ => MemPost st st' sigma ext_log).
  Proof.
      unfold interp_scheduler_satisfies_spec.
      intros * _ hwf_st hwf_sigma hwf_fns hinterp hpre.
      specialize typecheck_scheduler_correct'' with
        (5 := hinterp) (2 := hwf_st) (3 := hwf_sigma) (4 := hwf_fns) (1 := eq_refl).
      intros (hwf_impl' & wf_impl_ext').
      split_ands_in_goal; auto.
      consider MemPost.
      specialize impl_step_mem_correct. unfold symbolic_evaluate_file_success_single.
      intros.
      rewrite<-forall_preprocess_fancy_spreds_correct.
      apply H.
      + consider MemPre. revert hpre.
        repeat rewrite<-forall_preprocess_fancy_spreds_correct.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      + unfold machine_to_prop. split_ands_in_goal.
        * auto.
        * apply strong_WF_state_weaken in hwf_st.
          eapply WF_state_subset with (2 := hwf_st). vm_compute; reflexivity.
        * unfold impl_schedule. consider impl_schedule_list.
          move hinterp at bottom. consider impl_typecheck_fn.
          set (strip_dbg_sched_list _ ) as l in *.
          assert (l = (map (fun rl => id_transform_action _id (rules rl)) (list_of_schedule Impl.mem_schedule))) as Hl.
          { vm_reflect. }
          rewrite Hl.
          consider id_rules.
          apply interp_scheduler_list_equiv.
          apply hinterp.
  Qed.
End MemProofs.
