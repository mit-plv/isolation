Require Import rv_cache_isolation.Common.
Require Import rv_cache_isolation.RVCore.
Require Import rv_cache_isolation.Memory.
Require Import rv_cache_isolation.SecurityMonitor.

Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.EnclaveWithCache.ExtractionUtils.
Require Import koikaExamples.EnclaveWithCache.ProofUtils.
Require Import koikaExamples.EnclaveWithCache.PfDefs.
Require Import koikaExamples.EnclaveWithCache.ProofCore_symb.
(* Require Import koikaExamples.EnclaveWithCache.SmDefs. *)
Require Import koikaExamples.EnclaveWithCache.SmProofs.
(* Require Import koikaExamples.EnclaveWithCache.MemoryDefs. *)
Require Import koikaExamples.EnclaveWithCache.MemoryProofs.

Inductive custom_chaining_asserts :=
| CustomTaint
| CustomExtFn (id: N)
| CustomCore0 (id: core_custom_prop_names)
| CustomCore1 (id: core_custom_prop_names)
| CustomMem (id: mem_custom_t)
| CustomSM (id: sm_custom_t)
| Custom_Reset0
| Custom_Reset1
| Custom_PushReq0
| Custom_PushReq1
| Custom_Rf0
| Custom_Rf1
| Custom_MemPushZero0
| Custom_MemPushZero1
| Custom_MemPushZeroBoth
.
Instance EqDec_custom_chaining_asserts  : EqDec custom_chaining_asserts := _.

  Notation reg_t := (@Syntax.reg_t debug_id_ty).
Import Utils.PfHelpers.
Module SymbPfChain.
  Import RV32Core.
  Notation reg_t := (@Syntax.reg_t debug_id_ty).

  Definition ext_empty (extfn: debug_id_ty -> sval): list (custom_chaining_asserts * fancy_spred) :=
    assert_ext_fns_empty extfn (fun x => CustomExtFn (_id x))
      ([ext_mainmem; ext_led; ext_uart_write; ext_uart_read; ext_finish;
        ext_metadata_imem CoreId0;
        ext_metadata_imem CoreId1;
        ext_metadata_dmem CoreId0;
        ext_metadata_dmem CoreId1;
        ext_cache_imem CoreId0;
        ext_cache_imem CoreId1;
        ext_cache_dmem CoreId0;
        ext_cache_dmem CoreId1]).

  Definition core_rf_purge_preserved (core: ind_core_id)
                                     (reg_init reg_final: reg_t -> sval)
                                     : fancy_spred :=
    {{{ `reg_init (_crid core purge)` = #(_enum purge_state "Purged") ->
          forall x in (map reg_to_debug_id (map (core_reg core) (map rf FiniteType.finite_elements ))),
        `reg_final x` = `reg_init x`
    }}}.


  Section WithEnclaveSig.
    Context (enclave_sig: enclave_params_sig).

    Definition invariant_spreds' reg_fn get_field :=
      (map_fst CustomCore0 (CoreSymbDefs.pre_conds CoreId0 reg_fn)) ++
      (map_fst CustomCore1 (CoreSymbDefs.pre_conds CoreId1 reg_fn)) ++
      (map_fst CustomMem (MemSymbDefs.mem_invariant enclave_sig reg_fn get_field)) ++
      (map_fst CustomSM (SMSymbDefs.sm_invariant enclave_sig reg_fn get_field)).
    Definition post_core1_exprs
      (reg_init reg_final: reg_t -> sval) (ext_fn: debug_id_ty -> sval)
      : list (custom_chaining_asserts * fancy_spred) :=
      [(CustomTaint, {{{ forall x in (remove_regs (reg_list) (map reg_to_debug_id ((core_regs CoreId0) ++ (core_regs CoreId1)))),
                         `reg_final x` = `reg_init x`
                     }}})
      ;(Custom_Rf0, core_rf_purge_preserved CoreId0 reg_init reg_final)
      ;(Custom_Rf1, core_rf_purge_preserved CoreId1 reg_init reg_final)
      ] ++ (ext_empty ext_fn).

    (* Definition fs_push_in_range (core: ind_core_id) (reg_init: reg_t -> sval) (ext_log: debug_id_ty -> sval) machine_id : fancy_spred := *)
    (*   let get_field := *)
    (*     match machine_id with *)
    (*     | MachineImpl => impl_get_field *)
    (*     | MachineSpec => spec_get_field *)
    (*     end in *)
    (*   let reg_priv_turn := _mid (Memory.priv_turn core) in *)
    (*   let push_req := *)
    (*       get_field (_sid mem_input) (_fld mem_input "put_request") (ext_log (_extid ext_mainmem)) in *)
    (*   let toMainMem_valid cache := Memory.cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0) in *)
    (*   let toMainMem_data cache := Memory.cache_reg cache core (CacheState.toMainMem MemReqBypass.data0) in *)
    (*   {{{ `reg_init (_mid Memory.turn)` = #(PfHelpers.mem_core_write_turn core) -> *)
    (*       `get_field (_sid mem_input) (_fld mem_input "put_valid") (ext_log (_extid ext_mainmem))` = Ob~1 -> *)
    (*       { `reg_init reg_priv_turn` = Ob~1 -> *)
    (*         ``fs_req_in_fifo push_req reg_init (_mid (toMainMem_data imem)) (_mid (toMainMem_valid imem)) ``} /\ *)
    (*       { `reg_init reg_priv_turn` = Ob~0 -> *)
    (*         ``fs_req_in_fifo push_req reg_init (_mid (toMainMem_data dmem)) (_mid (toMainMem_valid dmem))  ``} *)
    (*   }}}. *)


    Definition post_mem_exprs (reg_init reg_final: reg_t -> sval) (ext_fn: debug_id_ty -> sval) get_field
      : list (custom_chaining_asserts * fancy_spred) :=
      [(CustomTaint, {{{ forall x in (remove_regs reg_list (map reg_to_debug_id ((core_regs CoreId0) ++ (core_regs CoreId1) ++ memory_regs))),
                         `reg_final x` = `reg_init x`
                     }}})
      ;(Custom_Rf0, core_rf_purge_preserved CoreId0 reg_init reg_final)
      ;(Custom_Rf1, core_rf_purge_preserved CoreId1 reg_init reg_final)
      ] ++ (map_fst CustomMem (MemSymbDefs.mem_post_conds'_preserve enclave_sig reg_init reg_final ext_fn get_field)).
                               (* [(Mem_push_in_range0, fs_push_in_range CoreId0 reg_init ext_fn MachineImpl) *)
                               (* ;(Mem_push_in_range1, fs_push_in_range CoreId1 reg_init ext_fn MachineImpl) *)

  Definition fs_mem_push_zero' (core: ind_core_id) (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval): fancy_spred :=
    {{{ `reg_final (_mid Memory.turn)` = #(mem_core_read_turn core) ->
        `reg_init (_smid (state core))` = #(_enum enum_core_state "Waiting") ->
        `impl_get_field (_sid mem_input) (_fld mem_input "put_valid") (ext_log (_extid ext_mainmem))` = Ob~0
    }}}.

    Definition post_sm_exprs (reg_init reg_final: reg_t -> sval) (mid_ext_fn: debug_id_ty -> sval) (committed_ext_fn: debug_id_ty -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      : list (custom_chaining_asserts * fancy_spred) :=
      [(CustomExtFn (_id (_extid ext_mainmem)),
         {{{ `mid_ext_fn (_extid ext_mainmem)` = `committed_ext_fn (_extid ext_mainmem)`}}} )
      ;(CustomExtFn (_id (_extid (ext_cache_imem CoreId0) )),
         {{{ `mid_ext_fn (_extid (ext_cache_imem CoreId0))` = `committed_ext_fn (_extid (ext_cache_imem CoreId0))`}}} )
      ;(CustomExtFn (_id (_extid (ext_cache_imem CoreId1) )),
         {{{ `mid_ext_fn (_extid (ext_cache_imem CoreId1))` = `committed_ext_fn (_extid (ext_cache_imem CoreId1))`}}} )
      ;(CustomExtFn (_id (_extid (ext_cache_dmem CoreId0) )),
         {{{ `mid_ext_fn (_extid (ext_cache_dmem CoreId0))` = `committed_ext_fn (_extid (ext_cache_dmem CoreId0))`}}} )
      ;(CustomExtFn (_id (_extid (ext_cache_dmem CoreId1) )),
         {{{ `mid_ext_fn (_extid (ext_cache_dmem CoreId1))` = `committed_ext_fn (_extid (ext_cache_dmem CoreId1))`}}} )
      ;(CustomExtFn (_id (_extid (ext_metadata_imem CoreId0) )),
         {{{ `mid_ext_fn (_extid (ext_metadata_imem CoreId0))` = `committed_ext_fn (_extid (ext_metadata_imem CoreId0))`}}} )
      ;(CustomExtFn (_id (_extid (ext_metadata_imem CoreId1) )),
         {{{ `mid_ext_fn (_extid (ext_metadata_imem CoreId1))` = `committed_ext_fn (_extid (ext_metadata_imem CoreId1))`}}} )
      ;(CustomExtFn (_id (_extid (ext_metadata_dmem CoreId0) )),
         {{{ `mid_ext_fn (_extid (ext_metadata_dmem CoreId0))` = `committed_ext_fn (_extid (ext_metadata_dmem CoreId0))`}}} )
      ;(CustomExtFn (_id (_extid (ext_metadata_dmem CoreId1) )),
         {{{ `mid_ext_fn (_extid (ext_metadata_dmem CoreId1))` = `committed_ext_fn (_extid (ext_metadata_dmem CoreId1))`}}} )
      ; (Custom_Reset0, SMSymbDefs.sm_reset_post CoreId0 reg_init reg_final get_field)
      ; (Custom_Reset1, SMSymbDefs.sm_reset_post CoreId1 reg_init reg_final get_field)
      (* ; (Custom_PushReq0, SMSymbDefs.push_req_in_config enclave_sig CoreId0 reg_init committed_ext_fn get_field) *)
      (* ; (Custom_PushReq1, SMSymbDefs.push_req_in_config enclave_sig CoreId1 reg_init committed_ext_fn get_field) *)
      ;(Custom_Rf0, core_rf_purge_preserved CoreId0 reg_init reg_final)
      ;(Custom_Rf1, core_rf_purge_preserved CoreId1 reg_init reg_final)
      ;(Custom_MemPushZero0, fs_mem_push_zero' CoreId0 reg_init reg_final committed_ext_fn)
      ;(Custom_MemPushZero1, fs_mem_push_zero' CoreId1 reg_init reg_final committed_ext_fn)
      ;(Custom_MemPushZeroBoth, {{{ `reg_final (_mid Memory.turn)` <> #mem_core0_read_turn ->
                                    `reg_final (_mid Memory.turn)` <> #mem_core1_read_turn ->
                                    `committed_ext_fn (_extid ext_mainmem)` = #(MemSymbDefs.almost_zeroed_mainmem_call)
                                }}})
      ] ++ (map_fst CustomMem (MemSymbDefs.mem_post_conds'_preserve enclave_sig reg_init reg_final committed_ext_fn get_field))
        ++ (map_fst CustomSM (SMSymbDefs.sm_post_conds'_preserve enclave_sig reg_init reg_final committed_ext_fn get_field)).
  Definition impl_core0_step_file : file_t :=
    {| file_machines := AbstractSingle dummy_machine ;
       file_assumptions := preprocess_fancy_spreds
                             ((invariant_spreds' impl_init impl_get_field) ++
                              (map_fst CustomCore0 (CoreSymbDefs.post_conds CoreId0 impl_init
                                 impl_final impl_final_ext)));
       file_assertions := preprocess_fancy_spreds
                             (invariant_spreds' impl_final impl_get_field)
                          (* preprocess_fancy_spreds *)
                          (*  (post_core0_exprs impl_init impl_final impl_committed_ext) *)
    |}.

  Definition impl_core1_step_file : file_t :=
    {| file_machines := AbstractSingle dummy_machine ;
       file_assumptions := preprocess_fancy_spreds
                             ((invariant_spreds' impl_init impl_get_field) ++
                                (invariant_spreds' impl_mid impl_get_field) ++
                              (map_fst CustomCore0 (CoreSymbDefs.post_conds' CoreId0 impl_init
                                 impl_mid impl_mid_ext )) ++
                              (map_fst CustomCore1 (CoreSymbDefs.post_conds CoreId1 impl_mid
                                 impl_final impl_final_ext)));
       file_assertions := preprocess_fancy_spreds (invariant_spreds' impl_final impl_get_field) ++
                          preprocess_fancy_spreds (post_core1_exprs impl_init impl_final impl_committed_ext)
    |}.

  Definition impl_mem_step_file : file_t :=
    {| file_machines := AbstractSingle dummy_machine ;
       file_assumptions :=
                           (preprocess_fancy_spreds (invariant_spreds' impl_init impl_get_field)) ++
                           (preprocess_fancy_spreds (invariant_spreds' impl_mid impl_get_field)) ++
                           (preprocess_fancy_spreds (post_core1_exprs impl_init impl_mid impl_mid_ext)) ++
                           (preprocess_fancy_spreds (MemSymbDefs.mem_post_conds enclave_sig impl_mid impl_final impl_final_ext impl_get_field));
       file_assertions := preprocess_fancy_spreds (invariant_spreds' impl_final impl_get_field) ++
                          preprocess_fancy_spreds (post_mem_exprs impl_init impl_final impl_committed_ext impl_get_field)
    |}.


  Definition impl_sm_step_file : file_t :=
    {| file_machines := AbstractSingle dummy_machine ;
       file_assumptions := preprocess_fancy_spreds (invariant_spreds' impl_init impl_get_field) ++
                           preprocess_fancy_spreds (invariant_spreds' impl_mid impl_get_field) ++
                           (preprocess_fancy_spreds (post_mem_exprs impl_init impl_mid impl_mid_ext impl_get_field)) ++
                           (preprocess_fancy_spreds (SMSymbDefs.sm_post_conds enclave_sig impl_mid impl_final impl_final_ext impl_get_field));
       file_assertions := preprocess_fancy_spreds (invariant_spreds' impl_final impl_get_field) ++
                          preprocess_fancy_spreds (post_sm_exprs impl_init impl_final impl_mid_ext
                                                     impl_committed_ext impl_get_field)
    |}.
  End WithEnclaveSig.
End SymbPfChain.
Module Type SMT_Chain_sig (EnclaveParams: EnclaveParams_sig).

  Parameter SMT_core0_ok: SymbolicInterp.WF_single_file (SymbPfChain.impl_core0_step_file EnclaveParams.enclave_sig)= true.
  Parameter SMT_core1_ok: SymbolicInterp.WF_single_file (SymbPfChain.impl_core1_step_file EnclaveParams.enclave_sig)= true.
  Parameter SMT_mem_ok: SymbolicInterp.WF_single_file (SymbPfChain.impl_mem_step_file EnclaveParams.enclave_sig)= true.
  Parameter SMT_sm_ok: SymbolicInterp.WF_single_file (SymbPfChain.impl_sm_step_file EnclaveParams.enclave_sig)= true.

End SMT_Chain_sig.
Module Type PfChain (EnclaveParams: EnclaveParams_sig)
                    (SecurityParams: SecurityParams_sig EnclaveParams)
                    (SmtOk: SMT_Chain_sig EnclaveParams).

  Definition WF_impl_core0_step_file := SmtOk.SMT_core0_ok.
  Definition WF_impl_core1_step_file := SmtOk.SMT_core1_ok.
  Definition WF_impl_mem_step_file := SmtOk.SMT_mem_ok.
  Definition WF_impl_sm_step_file := SmtOk.SMT_sm_ok.
End PfChain.
