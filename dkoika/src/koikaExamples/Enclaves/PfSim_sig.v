Require Import rv_isolation.Common.
Require Import rv_isolation.RVCore.
Require Import rv_isolation.Memory.
Require Import rv_isolation.SecurityMonitor.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
(* Require Import koikaExamples.Enclaves.TypeDefs. *)
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
Require Import koikaExamples.Enclaves.SymbSpec.
Require Import koika.AnnotatedSyntax.
  Import PfHelpers.
  Import Spec.

  Definition impl_machine : machine_t :=
      {| file_registers := reg_types;
         file_ext_sigma := ext_fn_tys;
         file_struct_defs := struct_defs;
      |}.
  Inductive mem_sim_custom_t :=
  | MemSim__Regs
  | MemSim__Fifos
  | MemSpec__SHReq
  | MemSpec__OtherEmpty
  | MemSimExtResponse
  | MemImplEmpty
  | MemSpecEmpty
  | MemImplExtCorrectCore (core: ind_core_id).

  Inductive sm_sim_custom_t :=
  | SmSim__Regs
  | SmSim__Fifos
  | SmSpec__OtherEmpty.

  Inductive core_sim_custom_t :=
  | CoreSimRegs
  | CoreSimFifos.

  Inductive sim_custom_t :=
  | CustomExtUartReadSim
  | CustomExtUartWriteSim
  | CustomExtLedSim
  | CustomExtFinishSim
  | CustomExtMemPushRequest__Sim
  | CustomExtMemPushRequest__ImplInvalidOrWriteTurn
  | CustomExtMemPushRequest__SpecInvalidOrWriteTurn
  | CustomExtMemPushRequest__NotInConfig
  | CustomExtMemShreqSim
  | CustomExtEncDataUnchanged
  | CustomSm (x: sm_custom_t)
  | CustomSmSim (x: sm_sim_custom_t)
  | CustomMem (x: mem_custom_t)
  | CustomMemSim (x: mem_sim_custom_t)
  | CustomCoreSim (x: core_sim_custom_t)
  | CustomRegStateRunning
  | CustomSimTaint (machine_id: machine_id_t)
  | CustomExtFn (machine_id: machine_id_t) (id: N)
  .

Notation reg_t := (@Syntax.reg_t debug_id_ty).
Import Utils.PfHelpers.

Module SymbSimDefs.
  Notation reg_t := (@Syntax.reg_t debug_id_ty).

  Definition core_sim_regs (core: ind_core_id) :=
    remove_regs (core_regs core)
                (map (core_reg core) (map snd (core_fifo_reg_pairs))).

  Definition core_fifo_reg_pairs' (core: ind_core_id) :=
    map (fun '(r1,r2) => (reg_to_debug_id (core_reg core r1), (reg_to_debug_id (core_reg core r2))))
      core_fifo_reg_pairs.

  Definition core_sim_invariants (core: ind_core_id)
                                 (ireg_fn sreg_fn: reg_t -> sval)
                                 (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                 : list (sim_custom_t * fancy_spred) :=
    map_fst CustomCoreSim
      [(CoreSimRegs, {{{ forall x in (map reg_to_debug_id (core_sim_regs core)), `ireg_fn x` = `sreg_fn x` }}})
      ;(CoreSimFifos, {{{ forall (valid,data) in2 (core_fifo_reg_pairs' core),
                          `ireg_fn valid` = Ob~1 ->
                          `ireg_fn data` = `sreg_fn data`
                      }}})
      ].


  Definition other_core_reset (core: ind_core_id) (reg_fn: reg_t -> sval) : fancy_spred :=
    let to_mmio_regs core :=
      map _smid (match core with
               | CoreId0 => map toMMIO0 [MemReqBypass.valid0]
               | CoreId1 => map toMMIO1 [MemReqBypass.valid0]
               end) in
    {{{ forall x in (to_mmio_regs (other_core core) ++ [_smid (enc_data (other_core core))]),
        `reg_fn x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
    }}}.
  Definition sim_sm_pre_conds
    (core: ind_core_id) (ireg_fn sreg_fn: reg_t -> sval)
    (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    : list (sim_custom_t * fancy_spred) :=
    [(CustomRegStateRunning, {{{ `ireg_fn ((_smid (state core)))` <> #(_enum enum_core_state "Waiting") }}} )
    ;(CustomExtLedSim, {{{
               forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext ext_led)),
               `sget_field (_sid enclave_req) (_fld enclave_req "ext_led")
                           (sget_field (_sid enclave_data) (_fld enclave_data "data") (sreg_fn ((_smid (enc_data core)))))` = Ob~1 ->
           `impl_ext_app (_extid ext_led) (SBound "arg")` = `spec_ext_app (_extid ext_led) (SBound "arg")`
       }}})
     ; (CustomExtUartReadSim, {{{
               forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext ext_uart_read)),
               `sget_field (_sid enclave_req) (_fld enclave_req "ext_uart")
                           (sget_field (_sid enclave_data) (_fld enclave_data "data") (sreg_fn ((_smid (enc_data core)))))` = Ob~1 ->
           `impl_ext_app (_extid ext_uart_read) (SBound "arg")` = `spec_ext_app (_extid ext_uart_read) (SBound "arg")`
       }}})
     ; (CustomExtUartWriteSim, {{{
               forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext ext_uart_write)),
               `sget_field (_sid enclave_req) (_fld enclave_req "ext_uart")
                           (spec_get_field (_sid enclave_data) (_fld enclave_data "data") (sreg_fn ((_smid (enc_data core)))))` = Ob~1 ->
           `impl_ext_app (_extid ext_uart_write) (SBound "arg")` = `spec_ext_app (_extid ext_uart_write) (SBound "arg")`
       }}})
     ; (CustomExtFinishSim, {{{
               forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext ext_finish)),
               `sget_field (_sid enclave_req) (_fld enclave_req "ext_finish")
                           (spec_get_field (_sid enclave_data) (_fld enclave_data "data") (sreg_fn ((_smid (enc_data core)))))` = Ob~1 ->
           `impl_ext_app (_extid ext_finish) (SBound "arg")` = `spec_ext_app (_extid ext_finish) (SBound "arg")`
       }}})
    ].


  Definition ext_fn_sim (core: ind_core_id) (extfn: ext_fn_t) fld
                        (reg_init: reg_t -> sval)
                        (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                        (iext_log sext_log: debug_id_ty -> sval) : fancy_spred :=
    let enc_data := senc_data core reg_init get_field in
    {{{
        `get_field (_sid enclave_req) fld (enc_data)` = Ob~1 ->
        `iext_log extfn` = `sext_log extfn`
    }}}.

  Definition mem_push_req_sim (core: ind_core_id)
                              (iinit_reg_fn ifinal_reg_fn: reg_t -> sval)
                              (iext_log sext_log: debug_id_ty -> sval)
                              : fancy_spred :=
    {{{ {`iinit_reg_fn (_mid Memory.turn)` = #(mem_core_write_turn core) \/
         `ifinal_reg_fn (_mid Memory.turn)` = #(mem_core_read_turn core) } ->
        `iext_log (_extid ext_mainmem)` = `sext_log (_extid ext_mainmem)`
    }}}.

  Definition mem_push_req_impl_invalid_or_turn
    (core: ind_core_id)
    (iinit_reg_fn: reg_t -> sval)
    (iget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    (iext_log : debug_id_ty -> sval)
    : fancy_spred :=
    {{{ `iget_field (_sid mem_input) (_fld mem_input "put_valid") (iext_log (_extid ext_mainmem))` = Ob~0 \/
        `iinit_reg_fn (_mid Memory.turn)` = #(mem_core_write_turn core) \/
        `iinit_reg_fn (_mid Memory.turn)` = #(mem_core_write_turn (other_core core))
    }}}.

  Definition mem_push_req_spec_invalid_or_turn
    (core: ind_core_id)
    (iinit_reg_fn: reg_t -> sval)
    (sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    (sext_log: debug_id_ty -> sval)
    : fancy_spred :=
    {{{ `sget_field (_sid mem_input) (_fld mem_input "put_valid") (sext_log (_extid ext_mainmem))` = Ob~0 \/
        `iinit_reg_fn (_mid Memory.turn)` = #(mem_core_write_turn core)
    }}}.



  Definition mem_post_conds
    (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval)
    (get_field: debug_id_ty -> debug_id_ty -> sval -> sval): list (mem_sim_custom_t * fancy_spred) :=
    [(MemImplExtCorrectCore CoreId0 , MemSymbDefs.impl_post_ext_mem_correct_core CoreId0 reg_final get_field ext_log)
    ;(MemImplExtCorrectCore CoreId1, MemSymbDefs.impl_post_ext_mem_correct_core CoreId1 reg_final get_field ext_log)
    ].

  Definition sim_mem_pre_conds
    (core: ind_core_id) (ireg_fn sreg_fn: reg_t -> sval)
    (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    : list (sim_custom_t * fancy_spred) :=
      map_fst CustomMemSim ([
       (MemSimExtResponse,
         {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext ext_mainmem)),
               `ireg_fn (_mid Memory.turn)` = #(mem_core_read_turn core) ->
               `impl_ext_app (_extid ext_mainmem) (SBound "arg")` = `spec_ext_app (_extid ext_mainmem) (SBound "arg")` /\
                 { `sget_field (_sid mem_output) (_fld mem_output "get_valid") (spec_ext_app (_extid ext_mainmem) (SBound "arg"))` = Ob~1 ->
                   `ireg_fn (_mid Memory.SHReq)` = `sreg_fn (_mid Memory.SHReq)`
                 }
         }}})
      ;(MemImplEmpty,
        {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext ext_mainmem)),
              {`ireg_fn (_mid Memory.turn)` <> #(mem_core_read_turn CoreId0) /\
               `ireg_fn (_mid Memory.turn)` <> #(mem_core_read_turn CoreId1)} ->
               `impl_ext_app (_extid ext_mainmem) (SBound "arg")` = #(zeroes (_unsafe_struct_sz mem_output))
        }}})
      ;(MemSpecEmpty,
        {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext ext_mainmem)),
              `sreg_fn (_mid Memory.turn)` <> #(mem_core_read_turn core) ->
              `spec_ext_app (_extid ext_mainmem) (SBound "arg")` = #(zeroes (_unsafe_struct_sz mem_output))
        }}}
       )
      ;(MemImplExtCorrectCore CoreId0, MemSymbDefs.impl_ext_mem_correct_core CoreId0 ireg_fn iget_field)
      ;(MemImplExtCorrectCore CoreId1, MemSymbDefs.impl_ext_mem_correct_core CoreId1 ireg_fn iget_field)
      ]).

  Section WithEnclaveSig.
    Context (enclave_sig: enclave_params_sig).
    Definition sm_impl_invariants (core: ind_core_id) ireg_fn
                                  (iget_field : debug_id_ty -> debug_id_ty -> sval -> sval)
                                  : list (sm_custom_t * fancy_spred) :=
      SMSymbDefs.sm_invariant enclave_sig ireg_fn iget_field.

    Definition sm_sim_regs core :=
      (map SM [state core; enc_req core; enc_data core; sm_reset core; clk]
        ++ to_mmio_regs__valid core ++ from_mmio_regs_valid core)
        ++ (map (core_reg core) (map fst (core_fifo_reg_pairs)))
        ++ ((memory_to_sm_fifos__valid core) ++ (sm_to_memory_fifos__valid core)).

    (* Definition sm_fifo_reg_pairs core := *)
    (*     (map (core_reg core) (map fst (core_fifo_reg_pairs))) *)
    (*     ++ ((memory_to_sm_fifos__valid core) ++ (sm_to_memory_fifos__valid core)). *)
    Definition to_mmio_regs_pairs (core: ind_core_id) :=
      [(toMemMMIO core MemReqBypass.valid0, toMemMMIO core MemReqBypass.data0)].
    Definition from_mmio_regs_pairs (core: ind_core_id) :=
      [(fromMemMMIO core MemRespBypass.valid0, fromMemMMIO core MemRespBypass.data0)].
    Definition mem_fifo_pairs (core: ind_core_id) :=
      (memory_to_sm_reg_pairs core) ++ (sm_to_memory_pairs core).
    Definition mem_fifo_pairs' (core: ind_core_id) :=
      map (fun '(r1,r2) => (reg_to_debug_id (Memory r1), reg_to_debug_id (Memory r2)))
          (mem_fifo_pairs core).

    Definition sm_fifo_reg_pairs core :=
      (map (fun '(r1,r2) => (core_reg core r1, core_reg core r2)) core_fifo_reg_pairs)
      ++ (to_mmio_regs_pairs core)
      ++ (from_mmio_regs_pairs core)
      ++ (map (fun '(r1,r2) => (Memory r1, Memory r2)) (mem_fifo_pairs core)).
    Definition sm_fifo_reg_pairs' core :=
      map (fun '(r1,r2) => (reg_to_debug_id r1, reg_to_debug_id r2)) (sm_fifo_reg_pairs core).

    Definition sm_sim_invariants (core: ind_core_id) (ireg_fn sreg_fn: reg_t -> sval)
                                  (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                  : list (sim_custom_t * fancy_spred) :=
      (map_fst CustomSm (sm_impl_invariants core ireg_fn iget_field)) ++
      [(CustomSmSim SmSim__Regs, {{{ forall x in (map reg_to_debug_id (sm_sim_regs core)), `ireg_fn x` = `sreg_fn x`  }}})
      ;(CustomSmSim SmSim__Fifos, {{{ forall (valid,data) in2 (sm_fifo_reg_pairs' core),
                          `ireg_fn valid` = Ob~1 ->
                          `ireg_fn data` = `sreg_fn data` }}})
      ;(CustomSmSim SmSpec__OtherEmpty, other_core_reset core sreg_fn)
      ].

    Definition sm_post_conds
      (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval)
      (get_field: debug_id_ty -> debug_id_ty -> sval -> sval): list (sm_custom_t * fancy_spred) :=
       [(SM_config_same CoreId0, SMSymbDefs.fs_config_same CoreId0 reg_init reg_final get_field);
        (SM_config_same CoreId1, SMSymbDefs.fs_config_same CoreId1 reg_init reg_final get_field)].

    Definition fs_addr_not_in_config
      (core: ind_core_id) (ireg_fn: reg_t -> sval)
      (iget_field: debug_id_ty -> debug_id_ty -> sval -> sval) (iext_log: debug_id_ty -> sval) : fancy_spred :=
      let push_req := iext_log (_extid ext_mainmem) in
      let push_req_valid := iget_field (_sid mem_input) (_fld mem_input "put_valid") (iext_log (_extid ext_mainmem)) in
      let push_req_req:= iget_field (_sid mem_input) (_fld mem_input "put_request") (iext_log (_extid ext_mainmem)) in
      {{{ `push_req_valid` = Ob~1 ->
          ``SMSymbDefs.fs_req_addrs_in_config enclave_sig
                                         iget_field push_req_req (ireg_fn ((_smid (enc_data core)))) `` ->
          False
      }}}.


    Definition mem_impl_invariants (core: ind_core_id) ireg_fn
      (iget_field : debug_id_ty -> debug_id_ty -> sval -> sval)
      : list (mem_custom_t * fancy_spred) :=
      MemSymbDefs.mem_invariant ireg_fn iget_field.

    Definition mem_spec_invariants (core: ind_core_id) (sreg_fn: reg_t -> sval)
      (sget_field : debug_id_ty -> debug_id_ty -> sval -> sval)
      : list (sim_custom_t * fancy_spred) :=
      map_fst CustomMemSim
        [(MemSpec__SHReq, {{{ `sget_field (_sid Memory.shreq) (_fld Memory.shreq "valid") (sreg_fn (_mid Memory.SHReq))` = Ob~0 }}})].

    Definition mem_sim_regs (core: ind_core_id) :=
      ([(_mid Memory.turn)] ++
       (map reg_to_debug_id
          ((private_mem_regs core)
             ++ [Memory (Memory.purge core)]
             ++ (memory_to_sm_fifos__valid core)
             ++ (sm_to_memory_fifos__valid core)
          ))).

    Definition mem_sim_invariants (core: ind_core_id) (ireg_fn sreg_fn: reg_t -> sval)
                                  (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                  : list (sim_custom_t * fancy_spred) :=
      (map_fst CustomMem (mem_impl_invariants core ireg_fn iget_field)) ++
      (mem_spec_invariants core sreg_fn sget_field) ++
      (map_fst CustomMemSim
        [(MemSim__Regs, {{{ forall x in (mem_sim_regs core), `ireg_fn x` = `sreg_fn x` }}})
        ;(MemSim__Fifos, {{{ forall (valid,data) in2 (mem_fifo_pairs' core),
                          `ireg_fn valid` = Ob~1 ->
                          `ireg_fn data` = `sreg_fn data`
                       }}})
        ]
      ).

    Definition sim_invariants (core: ind_core_id) (ireg_fn sreg_fn: reg_t -> sval)
                              (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                             : list (sim_custom_t * fancy_spred) :=
      (core_sim_invariants core ireg_fn sreg_fn iget_field sget_field) ++
      (sm_sim_invariants core ireg_fn sreg_fn iget_field sget_field) ++
      (mem_sim_invariants core ireg_fn sreg_fn iget_field sget_field).

    Definition sim_pre_conds (core: ind_core_id) (ireg_fn sreg_fn: reg_t -> sval)
                             (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                             : list (sim_custom_t * fancy_spred) :=
      sim_invariants core ireg_fn sreg_fn iget_field sget_field ++
      sim_sm_pre_conds core ireg_fn sreg_fn iget_field sget_field ++
      sim_mem_pre_conds core ireg_fn sreg_fn iget_field sget_field.
    Definition sim_post_conds (core: ind_core_id)
                              (iinit_reg_fn sinit_reg_fn: reg_t -> sval)
                              (ifinal_reg_fn sfinal_reg_fn: reg_t -> sval)
                              (iget_field sget_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                              (iext_log sext_log: debug_id_ty -> sval)
                             : list (sim_custom_t * fancy_spred) :=
      (sim_invariants core ifinal_reg_fn sfinal_reg_fn iget_field sget_field) ++
      (map_fst CustomSm (sm_post_conds iinit_reg_fn ifinal_reg_fn iext_log iget_field)) ++
      (map_fst CustomMemSim (mem_post_conds iinit_reg_fn ifinal_reg_fn iext_log iget_field)) ++
      [(CustomExtLedSim, ext_fn_sim core (_extid ext_led) (_fld enclave_req "ext_led")
                                    iinit_reg_fn sget_field iext_log sext_log)
      ;(CustomExtUartReadSim, ext_fn_sim core (_extid ext_uart_read) (_fld enclave_req "ext_uart")
                                         iinit_reg_fn sget_field iext_log sext_log)
      ;(CustomExtUartWriteSim, ext_fn_sim core (_extid ext_uart_write) (_fld enclave_req "ext_uart")
                                         iinit_reg_fn sget_field iext_log sext_log)
      ;(CustomExtFinishSim, ext_fn_sim core (_extid ext_finish) (_fld enclave_req "ext_finish")
                                    iinit_reg_fn sget_field iext_log sext_log)
      (* ;(CustomExtEncDataUnchanged, SMSymbDefs.fs_config_same core iinit_reg_fn ifinal_reg_fn *)
      (*                                                     iget_field) *)
      ;(CustomExtMemPushRequest__Sim, mem_push_req_sim core iinit_reg_fn ifinal_reg_fn iext_log sext_log)
      ;(CustomExtMemPushRequest__ImplInvalidOrWriteTurn, mem_push_req_impl_invalid_or_turn core iinit_reg_fn iget_field iext_log )
      ;(CustomExtMemPushRequest__SpecInvalidOrWriteTurn, mem_push_req_spec_invalid_or_turn core iinit_reg_fn sget_field sext_log)
      ;(CustomExtMemPushRequest__NotInConfig,
         {{{ `iinit_reg_fn (_mid Memory.turn)` = #(mem_core_write_turn (other_core core)) ->
             `iinit_reg_fn ((_smid (state core)))` <> #(_enum enum_core_state "Waiting") ->
             ``fs_addr_not_in_config core iinit_reg_fn iget_field iext_log``
         }}})
      ;(CustomExtMemShreqSim,
         {{{ `iget_field (_sid mem_input) (_fld mem_input "put_valid") (iext_log (_extid ext_mainmem))` = Ob~1 ->
             `ifinal_reg_fn (_mid Memory.turn)` = #(mem_core_read_turn core) ->
             `ifinal_reg_fn (_mid Memory.SHReq)` = `sfinal_reg_fn (_mid Memory.SHReq)`
         }}})
      ].
  Definition SimPre (core: ind_core_id)
                    (impl_st spec_st: Environments.state_t)
                    (impl_sigma spec_sigma: @ext_sigma_t N) : Prop :=
        Forall (fun '(_, p) => interp_fancy_spred2
                    {| pkg_machine := impl_machine;
                       pkg_init_st := impl_st; pkg_mid_st := None; pkg_final_st := impl_st; (* don't care *)
                       pkg_sigma := impl_sigma; pkg_mid_ext_log := None;
                       pkg_ext_log' := SortedExtFnEnv.empty; (* don't care *)
                    |}
                    {| pkg_machine := SymbSpecDefs.spec_machine;
                       pkg_init_st := spec_st; pkg_mid_st := None; pkg_final_st := spec_st; (* don't care *)
                       pkg_sigma := spec_sigma; pkg_mid_ext_log := None;
                       pkg_ext_log' := SortedExtFnEnv.empty; (* don't care *)
                    |} p) (sim_pre_conds core impl_init spec_init impl_get_field spec_get_field).

  Definition SimPost (core: ind_core_id) (impl_st spec_st impl_st' spec_st': Environments.state_t)
                     (impl_sigma spec_sigma: @ext_sigma_t N)
                     (impl_ext_log spec_ext_log: ext_log_t): Prop :=
      Forall (fun '(_, p) => interp_fancy_spred2
                  {| pkg_machine := impl_machine;
                     pkg_init_st := impl_st; pkg_mid_st := None; pkg_final_st := impl_st';
                     pkg_sigma := impl_sigma; pkg_mid_ext_log := None; pkg_ext_log' := impl_ext_log
                  |}
                  {| pkg_machine := SymbSpecDefs.spec_machine;
                     pkg_init_st := spec_st; pkg_mid_st := None; pkg_final_st := spec_st';
                     pkg_sigma := spec_sigma; pkg_mid_ext_log := None; pkg_ext_log' := spec_ext_log
                  |}
                p) (sim_post_conds core impl_init spec_init
                                             impl_final spec_final
                                             impl_get_field spec_get_field
                                             impl_final_ext spec_final_ext).

  End WithEnclaveSig.

End SymbSimDefs.


Module Type PfSimProofs_sig (EnclaveParams: EnclaveParams_sig)
                   (SecurityParams: SecurityParams_sig EnclaveParams)
                   (Symbspec: SymbSpec EnclaveParams SecurityParams).
                   (* (SimDefs: PfSimDefs EnclaveParams SecurityParams Symbspec). *)
  Import SymbSimDefs.
  Import SecurityParams.Impl.
  Import SecurityParams.Machine.

  Parameter step_sim_sched_correct:
    forall core,
     sim_interp_scheduler_satisfies_spec
        reg_type_env _ext_fn_tys
        id_int_fns id_int_fns
        id_struct_defs id_struct_defs
        id_rules id_rules FullMachine.schedule (spec_schedule core) unit
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           SymbSimDefs.SimPre EnclaveParams.enclave_sig core impl_st spec_st impl_sigma spec_sigma)
        (fun impl_st impl_sigma impl_st' impl_ext spec_st spec_sigma spec_st' spec_ext ghost =>
           SymbSimDefs.SimPost EnclaveParams.enclave_sig core impl_st spec_st impl_st' spec_st' impl_sigma spec_sigma impl_ext spec_ext).

End PfSimProofs_sig.
