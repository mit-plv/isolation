Require Import rv_isolation.Common.
Require Import rv_isolation.RVCore.
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
Require Import koikaExamples.Enclaves.ProofCore_symb.
(* Require Import koikaExamples.Enclaves.SmDefs. *)
Require Import koikaExamples.Enclaves.SmProofs.
(* Require Import koikaExamples.Enclaves.MemoryDefs. *)
Require Import koikaExamples.Enclaves.MemoryProofs.

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
  Notation reg_t := (@Syntax.reg_t debug_id_ty).
Import Utils.PfHelpers.
Module SymbPfChain.
  Import RV32Core.
  Notation reg_t := (@Syntax.reg_t debug_id_ty).

  Definition ext_empty (extfn: debug_id_ty -> sval): list (custom_chaining_asserts * fancy_spred) :=
    assert_ext_fns_empty extfn (fun x => CustomExtFn (_id x)) [ext_mainmem; ext_led; ext_uart_write; ext_uart_read; ext_finish].
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
      (map_fst CustomMem (MemSymbDefs.mem_invariant reg_fn get_field)) ++
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
    Definition fs_req_in_fifo (req: sval) (reg_fn: reg_t -> sval) (reg_data: reg_t) (reg_valid: reg_t) : fancy_spred :=
      {{{ `reg_fn reg_valid` = Ob~1 /\
          `req` = `reg_fn reg_data`
      }}}.

    Definition fs_push_in_range (core: ind_core_id) (reg_init: reg_t -> sval) (ext_log: debug_id_ty -> sval) machine_id : fancy_spred :=
      let get_field :=
        match machine_id with
        | MachineImpl => impl_get_field
        | MachineSpec => spec_get_field
        end in
      let reg_priv_turn := _mid (Memory.priv_turn core) in
      let push_req :=
          get_field (_sid mem_input) (_fld mem_input "put_request") (ext_log (_extid ext_mainmem)) in
      let (to_imem_data, to_imem_valid) := ((Memory.toIMem core) MemReq.data0, (Memory.toIMem core) MemReq.valid0) in
      let (to_dmem_data, to_dmem_valid) := ((Memory.toDMem core) MemReq.data0, (Memory.toDMem core) MemReq.valid0) in
      {{{ `reg_init (_mid Memory.turn)` = #(PfHelpers.mem_core_write_turn core) ->
          `get_field (_sid mem_input) (_fld mem_input "put_valid") (ext_log (_extid ext_mainmem))` = Ob~1 ->
          { `reg_init reg_priv_turn` = Ob~1 -> ``fs_req_in_fifo push_req reg_init (_mid to_imem_data) (_mid to_imem_valid) ``} /\
          { `reg_init reg_priv_turn` = Ob~0 -> ``fs_req_in_fifo push_req reg_init (_mid to_dmem_data) (_mid to_dmem_valid) ``}
      }}}.


    Definition post_mem_exprs (reg_init reg_final: reg_t -> sval) (ext_fn: debug_id_ty -> sval) get_field
      : list (custom_chaining_asserts * fancy_spred) :=
      [(CustomTaint, {{{ forall x in (remove_regs reg_list (map reg_to_debug_id ((core_regs CoreId0) ++ (core_regs CoreId1) ++ memory_regs))),
                         `reg_final x` = `reg_init x`
                     }}})
      ;(Custom_Rf0, core_rf_purge_preserved CoreId0 reg_init reg_final)
      ;(Custom_Rf1, core_rf_purge_preserved CoreId1 reg_init reg_final)
      ] ++ (map_fst CustomMem ((MemSymbDefs.mem_post_conds'_preserve reg_init reg_final ext_fn get_field) ++
                               [(Mem_push_in_range0, fs_push_in_range CoreId0 reg_init ext_fn MachineImpl)
                               ;(Mem_push_in_range1, fs_push_in_range CoreId1 reg_init ext_fn MachineImpl)
                               ])).

  Definition fs_mem_push_zero' (core: ind_core_id) (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval): fancy_spred :=
    let (imem_valid, dmem_valid) := ((Memory.toIMem core) MemReq.valid0, (Memory.toDMem core) MemReq.valid0) in
    {{{ `reg_final (_mid Memory.turn)` = #(mem_core_read_turn core) ->
        `reg_init (_smid (state core))` = #(_enum enum_core_state "Waiting") ->
        `impl_get_field (_sid mem_input) (_fld mem_input "put_valid") (ext_log (_extid ext_mainmem))` = Ob~0
    }}}.

    Definition post_sm_exprs (reg_init reg_final: reg_t -> sval) (mid_ext_fn: debug_id_ty -> sval) (committed_ext_fn: debug_id_ty -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      : list (custom_chaining_asserts * fancy_spred) :=
      [(CustomExtFn (_id (_extid ext_mainmem)), {{{ `mid_ext_fn (_extid ext_mainmem)` = `committed_ext_fn (_extid ext_mainmem)`}}} )
      ; (Custom_Reset0, SMSymbDefs.sm_reset_post CoreId0 reg_init reg_final get_field)
      ; (Custom_Reset1, SMSymbDefs.sm_reset_post CoreId1 reg_init reg_final get_field)
      ; (Custom_PushReq0, SMSymbDefs.push_req_in_config enclave_sig CoreId0 reg_init committed_ext_fn get_field)
      ; (Custom_PushReq1, SMSymbDefs.push_req_in_config enclave_sig CoreId1 reg_init committed_ext_fn get_field)
      ;(Custom_Rf0, core_rf_purge_preserved CoreId0 reg_init reg_final)
      ;(Custom_Rf1, core_rf_purge_preserved CoreId1 reg_init reg_final)
      ;(Custom_MemPushZero0, fs_mem_push_zero' CoreId0 reg_init reg_final committed_ext_fn)
      ;(Custom_MemPushZero1, fs_mem_push_zero' CoreId1 reg_init reg_final committed_ext_fn)
      ;(Custom_MemPushZeroBoth, {{{ `reg_final (_mid Memory.turn)` <> #mem_core0_read_turn ->
                                    `reg_final (_mid Memory.turn)` <> #mem_core1_read_turn ->
                                    `committed_ext_fn (_extid ext_mainmem)` = #(MemSymbDefs.almost_zeroed_mainmem_call)
                                }}})
      ] ++ (map_fst CustomMem (MemSymbDefs.mem_post_conds'_preserve reg_init reg_final committed_ext_fn get_field))
        ++ (map_fst CustomSM (SMSymbDefs.sm_post_conds'_preserve enclave_sig reg_init reg_final committed_ext_fn get_field)).
  Definition impl_core0_step_file : file_t :=
    {| file_machines := AbstractSingle dummy_machine ;
       file_assumptions := preprocess_fancy_spreds
                             ((invariant_spreds'  impl_init impl_get_field) ++
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
                           (preprocess_fancy_spreds (MemSymbDefs.mem_post_conds impl_mid impl_final impl_final_ext impl_get_field));
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
  (* Import SecurityParams.Machine. *)
  (* Import SecurityParams.Impl. *)
  (* Import RV32Core. *)

  (* Import ExternalMemory. *)
  (* Import Spec. *)
  (* Import SymbPfChain. *)

  (* TODO: MEM PRE CONDS *)

  (* Definition impl_core0_step_file : file_t := impl_core0_step_file'. *)
    (* Eval vm_compute in impl_core0_step_file'. *)

  Definition WF_impl_core0_step_file := SmtOk.SMT_core0_ok.
  Definition WF_impl_core1_step_file := SmtOk.SMT_core1_ok.
  Definition WF_impl_mem_step_file := SmtOk.SMT_mem_ok.
  Definition WF_impl_sm_step_file := SmtOk.SMT_sm_ok.
End PfChain.

(* Module Test_PfChain'. *)
(*   Require Import koikaExamples.Enclaves.External. *)
(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module Pfchain := Empty <+ PfChain EnclaveParams SecurityParams. *)
(*   Import Pfchain. *)
(*   Module Foo_Core0. *)
(*     Definition file := Eval vm_compute in impl_core0_step_file. *)
(*     Extraction "../../../../ImplCore0Step.ml" struct_sz vect_t file. *)
(*   End Foo_Core0. *)
(*   Module Foo_Core1. *)
(*     Definition file := Eval vm_compute in impl_core1_step_file. *)
(*     Extraction "../../../../ImplCore1Step.ml" struct_sz vect_t file. *)

(*   End Foo_Core1. *)

(*   Module Foo_Mem. *)
(*     Definition file := Eval vm_compute in impl_mem_step_file. *)
(* Extraction "../../../../ImplMemStep.ml" struct_sz vect_t file. *)

(*   End Foo_Mem. *)

(*   Module Foo_SM. *)
(*     Definition file := Eval vm_compute in impl_sm_step_file. *)
(*     Extraction "../../../../ImplSmStep.ml" struct_sz vect_t file. *)
(*   End Foo_SM. *)
(* End Test_PfChain'. *)
