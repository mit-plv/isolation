Require Import rv_isolation.Common.
Require Import rv_isolation.RVCore.
Require Import rv_isolation.Memory.
Require Import rv_isolation.SecurityMonitor.

Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koikaExamples.Enclaves.ProofUtils.
Require Import koikaExamples.Enclaves.PfHelpers.
Require Import koikaExamples.Enclaves.PfDefs.
Require Import koikaExamples.Enclaves.SmDefs.

Inductive sm_custom_t :=
| SM_Tick
| SM_Waiting0
| SM_Waiting1
| SM_Enter0
| SM_Enter1
| SM_uart_write_zeroes
| SM_uart_read_zeroes
| SM_led_zeroes
| SM_finish_zeroes
| SM_inv_waiting (core: ind_core_id)
| SM_inv_reset (core: ind_core_id)
| SM_inv_core_reset (core: ind_core_id)
| SM_inv_mem_reset (core: ind_core_id)
| SM_enc_data_valid (core: ind_core_id)
| SM_post_core_purge0
| SM_post_core_purge1
| SM_post_mem_purge0
| SM_post_mem_purge1
| SM_not_running0
| SM_not_running1
| SM_mmio_req_in_range (core: ind_core_id)
| SM_valid_addrs (core: ind_core_id)
(* | SM_base (rl: ProofSm.custom_prop_names) *)
| SM_config_same (core: ind_core_id)
| SM_inv_reset_mem (core: ind_core_id)
| SM_taint
| SM_disjoint_configs
| SM_disjoint_eid
| SM_disjoint_sid
| SM_enc_req (core: ind_core_id)
| SM_custom (str: string)
.
  Import RV32Core.
  Notation reg_t := (@Syntax.reg_t debug_id_ty).
  Import Utils.PfHelpers.
  Import TopLevelModuleHelpers.


Module SMSymbDefs.
  Definition fs_enc_reqs_conflict (req1 req2: sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) : fancy_spred :=
    let eid enc_req := get_field (_sid enclave_req) (_fld enclave_req "eid") enc_req in
    let shared_id enc_req := get_field (_sid enclave_req) (_fld enclave_req "shared_regions") enc_req in
    let uart enc_req := get_field (_sid enclave_req) (_fld enclave_req "ext_uart") enc_req in
    let led enc_req := get_field (_sid enclave_req) (_fld enclave_req "ext_led") enc_req in
    let finish enc_req := get_field (_sid enclave_req) (_fld enclave_req "ext_finish") enc_req in
    {{{ `eid req1` = `eid req2` \/
        { (`shared_id req1` && `shared_id req2`) <> Ob~0~0~0~0~0~0 } \/
        { (`uart req1` && `uart req2`) = Ob~1 } \/
        { (`led req1` && `led req2`) = Ob~1 } \/
        { (`finish req1` && `finish req2`) = Ob~1 }
    }}}.
  Definition _cid core reg := reg_to_debug_id ((core_reg core) reg).

  Definition fs_sm_ext_fn_zero fld fn reg_init ext_log get_field: fancy_spred :=
    let enc_data core := senc_data core reg_init get_field in
    {{{ { `reg_init (_smid (state CoreId0))` = #(_enum enum_core_state "Waiting")  \/
          `get_field (_sid enclave_req) fld (enc_data CoreId0)` = Ob~0
        } ->
        { `reg_init (_smid (state CoreId1))` = #(_enum enum_core_state "Waiting")  \/
          `get_field (_sid enclave_req) fld (enc_data CoreId1)` = Ob~0
        } ->
        `ext_log fn` = #(zeroes (unsafe_get_ext_fn_arg_type (_id fn)))
    }}}.
  Definition sm_to_core_fifos__valid (core: ind_core_id) : list SecurityMonitor.reg_t :=
    (map (core_reg core) (map fst (sm_to_core_fifo_reg_pairs))).

  Definition sm_reset_fifos (core: ind_core_id) :=
    ((map (core_reg core)) (map fst ((core_to_sm_fifo_reg_pairs) ++ (sm_to_core_fifo_reg_pairs))))
      ++ (map Memory (map fst ((memory_to_sm_reg_pairs core) ++ (sm_to_memory_pairs core))))
      ++ (to_mmio_regs__valid core)
      ++ (from_mmio_regs_valid core).


  Definition fs_sm_inv_waiting (core: ind_core_id) (reg_fn: reg_t -> sval): fancy_spred :=
    let mem_purge := _mid (Memory.purge core) in
    {{{ `reg_fn ((_smid (state core)))` = #(_enum enum_core_state "Waiting") ->
        `reg_fn mem_purge` = #(_enum purge_state "Purged") /\
        `reg_fn ((_smid (enc_data core)))` = #(zeroes (Types.struct_sz enclave_data)) /\
        `reg_fn (_cid core purge )` = #(_enum purge_state "Purged") /\
        { forall x in ([(_smid (sm_reset core))] ++
                    (map reg_to_debug_id (sm_reset_fifos core)
                    )
                 ),
          `reg_fn x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
        }
      }}}.


  Definition fs_sm_inv_core_reset (core: ind_core_id) (reg_fn: reg_t -> sval) : fancy_spred :=
    {{{ { {`reg_fn (_cid core purge)` = #(_enum purge_state "Purged") \/
          `reg_fn (_cid core purge)` = #(_enum purge_state "Purging")} ->
         `reg_fn ((_smid (state core)))` <> #(_enum enum_core_state "Running")} /\
        { `reg_fn (_cid core purge)` = #(_enum purge_state "Purged") ->
          {forall x in (map reg_to_debug_id (sm_to_core_fifos__valid core)),
          `reg_fn x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
          }
        }
    }}}.

  Definition fs_sm_inv_mem_reset (core: ind_core_id) (reg_fn: reg_t -> sval) : fancy_spred :=
    {{{ {`reg_fn (_mid (Memory.purge core))` = #(_enum purge_state "Purged") \/
         `reg_fn (_mid (Memory.purge core))` = #(_enum purge_state "Purging")} ->
        `reg_fn ((_smid (state core)))` <> #(_enum enum_core_state "Running")
    }}}.
  Definition fs_reset_mem_correct (core: ind_core_id)
                                  (reg_fn: reg_t -> sval)
                                  (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                   : fancy_spred :=
    {{{ {`senc_data_valid core reg_fn get_field` = Ob~0 \/
          `reg_fn (_mid (Memory.purge core))` = #(_enum purge_state "Purged") } ->
        {forall x in (map reg_to_debug_id (sm_to_memory_fifos__valid core)),
         `reg_fn x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
        }
    }}}.

   Definition fs_sm_inv_enc_data_valid (core: ind_core_id)
                                     (reg_fn: reg_t -> sval)
                                     (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                     : fancy_spred :=
     {{{ `senc_data_valid core reg_fn get_field` = Ob~0 ->
         `reg_fn ((_smid (state core)))` = #(_enum enum_core_state "Waiting")
     }}}.

  Definition fs_sm_inv_reset_correct (core: ind_core_id)
                                     (reg_fn: reg_t -> sval)
                                     (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                     : fancy_spred :=
    let _to_mmio_regs:= map reg_to_debug_id (to_mmio_regs__valid core) in
    {{{
         {`reg_fn ((_smid (state core)))` = #(_enum enum_core_state "Waiting")  ->
          `senc_data_valid core reg_fn get_field` = Ob~0 /\
          {forall x in _to_mmio_regs,
              `reg_fn x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
          } /\
          `reg_fn (_mid (Memory.purge core))` = #(_enum purge_state "Purged")
         } /\
         { `reg_fn ((_smid (sm_reset core)))` = Ob~1 ->
           {forall x in _to_mmio_regs,
               `reg_fn x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
           }
         } /\
         { {`reg_fn ((_smid (state core)))` = #(_enum enum_core_state "Running") \/
           `reg_fn ((_smid (state core)))` = #(_enum enum_core_state "Waiting") } ->
           `reg_fn ((_smid (sm_reset core)))` = Ob~0
         }
    }}}.
  Definition fs_mmio_req_in_range
    (core: ind_core_id) (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval): fancy_spred :=
    let (to_mmio_data, to_mmio_valid) :=
      match core with
      | CoreId0 => (toMMIO0 MemReqBypass.data0, toMMIO0 MemReqBypass.valid0)
      | CoreId1 => (toMMIO1 MemReqBypass.data0, toMMIO1 MemReqBypass.valid0)
      end in
     let sval_enclave_data :=
       get_field (_sid enclave_data) (_fld enclave_data "data") (reg_fn ((_smid (enc_data core))))  in
     let sval_enclave_valid :=
       get_field (_sid enclave_data) (_fld enclave_data "valid") (reg_fn ((_smid (enc_data core))))  in
    {{{ `sval_enclave_valid` = Ob~1 ->
        `reg_fn (_smid to_mmio_valid)` = Ob~1 ->
        { `get_field (_sid mem_req) (_fld mem_req "addr") (reg_fn (_smid to_mmio_data))` = #(Vect.vect_to_list MMIO_UART_ADDRESS) ->
          `get_field (_sid enclave_req) (_fld enclave_req "ext_uart") sval_enclave_data ` = Ob~1
        } /\
        { `get_field (_sid mem_req) (_fld mem_req "addr") (reg_fn (_smid to_mmio_data))` = #(Vect.vect_to_list MMIO_LED_ADDRESS) ->
          `get_field (_sid enclave_req) (_fld enclave_req "ext_led") sval_enclave_data ` = Ob~1
        } /\
        { `get_field (_sid mem_req) (_fld mem_req "addr") (reg_fn (_smid to_mmio_data))` = #(Vect.vect_to_list MMIO_EXIT_ADDRESS) ->
          `get_field (_sid enclave_req) (_fld enclave_req "ext_finish") sval_enclave_data ` = Ob~1
        }
    }}}.

  Definition fs_disjoint_configs (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) : fancy_spred :=
     let sval_enclave_data0 :=
       get_field (_sid enclave_data) (_fld enclave_data "data") (reg_fn (_smid (enc_data CoreId0)))  in
     let sval_enclave_data1 :=
       get_field (_sid enclave_data) (_fld enclave_data "data") (reg_fn (_smid (enc_data CoreId1)))  in
     {{{ { `get_field (_sid enclave_req) (_fld enclave_req "ext_led") sval_enclave_data0` = Ob~0 \/
               `get_field (_sid enclave_req) (_fld enclave_req "ext_led") sval_enclave_data1` = Ob~0} /\
        { `get_field (_sid enclave_req) (_fld enclave_req "ext_uart") sval_enclave_data0` = Ob~0 \/
               `get_field (_sid enclave_req) (_fld enclave_req "ext_uart") sval_enclave_data1` = Ob~0} /\
        { `get_field (_sid enclave_req) (_fld enclave_req "ext_finish") sval_enclave_data0` = Ob~0 \/
               `get_field (_sid enclave_req) (_fld enclave_req "ext_finish") sval_enclave_data1` = Ob~0}

     }}}.
  Definition fs_disjoint_eid (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    : fancy_spred :=
     let sval_enclave_data0 :=
       get_field (_sid enclave_data) (_fld enclave_data "data") (reg_fn (_smid (enc_data CoreId0)))  in
     let sval_enclave_data1 :=
       get_field (_sid enclave_data) (_fld enclave_data "data") (reg_fn (_smid (enc_data CoreId1)))  in
    {{{ `senc_data_valid CoreId0 reg_fn get_field` = Ob~1 ->
        `senc_data_valid CoreId1 reg_fn get_field` = Ob~1 ->
        `get_field (_sid enclave_req) (_fld enclave_req "eid") sval_enclave_data0` <>
        `get_field (_sid enclave_req) (_fld enclave_req "eid") sval_enclave_data1`
    }}}.
  Definition fs_disjoint_sid (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    : fancy_spred :=
     let sval_enclave_data0 :=
       get_field (_sid enclave_data) (_fld enclave_data "data") (reg_fn (_smid (enc_data CoreId0)))  in
     let sval_enclave_data1 :=
       get_field (_sid enclave_data) (_fld enclave_data "data") (reg_fn (_smid (enc_data CoreId1)))  in
    {{{ `senc_data_valid CoreId0 reg_fn get_field` = Ob~1 ->
        `senc_data_valid CoreId1 reg_fn get_field` = Ob~1 ->
        `get_field (_sid enclave_req) (_fld enclave_req "shared_regions") sval_enclave_data0` &&
        `get_field (_sid enclave_req) (_fld enclave_req "shared_regions") sval_enclave_data1` = Ob~0~0~0~0~0~0
    }}}.
  Definition fs_enc_req (core: ind_core_id)
                        (reg_fn: reg_t -> sval)
                        (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                        : fancy_spred :=
    let state := (_smid (state core)) in
    {{{ {`reg_fn state` = #(_enum enum_core_state "Purging") \/
        `reg_fn state` = #(_enum enum_core_state "Waiting")} ->
        `get_field (_sid enclave_data) (_fld enclave_data "valid")  (reg_fn ((_smid (enc_req core))))` = Ob~1
    }}}.
  Definition fs_config_same (core: ind_core_id) (reg_init reg_final: reg_t -> sval)
                            (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                            : fancy_spred :=
    {{{ `senc_data_valid core reg_init get_field` = Ob~1 ->
        `senc_data_valid core reg_final get_field` = Ob~1 ->
        `reg_init ((_smid (enc_data core)))` = `reg_final ((_smid (enc_data core)))` /\
        `reg_final ((_smid (state core)))` <> #(_enum enum_core_state "Waiting")
    }}}.

  Section WithEnclaveSig.
    Context (enclave_sig: enclave_params_sig).

    Definition fs_sm_still_waiting
      (core: ind_core_id) (reg_init reg_final: reg_t -> sval)
      (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) : fancy_spred :=
      let data_other := (senc_data (other_core core) reg_init get_field) in
      let data_this :=  get_field (_sid enclave_data) (_fld enclave_data "data") (reg_init (_smid (enc_req core))) in
      {{{ `reg_init (_smid (state core))` = #(_enum enum_core_state "Waiting") ->
          {`reg_init (_smid clk)` <> #(cid_to_bits core) \/
           {`reg_init (_smid (state (other_core core)))` <> #(_enum enum_core_state "Waiting") /\
            ``fs_enc_reqs_conflict data_this data_other get_field``
           }
          } ->
          {forall x in (map _smid [state core; enc_req core; enc_data core]),
              `reg_final x` = `reg_init x`
          } /\
          {forall x in (map (_cid core) (map rf FiniteType.finite_elements)),
              `reg_final x` = `reg_init x`
          }
      }}}.
    Definition fs_eid_to_assert_init_pc (veid vpc : sval) (eid: enclave_id) : fancy_spred :=
      {{{ `veid` = #(enclave_id_to_vect eid) ->
          `vpc` = #(_enclave_bootloader_addr enclave_sig eid)
      }}}.
    Definition sm_fifo_sims core :=
        (to_mmio_regs__valid core ++ from_mmio_regs_valid core)
        ++ (map (core_reg core) (map fst (core_fifo_reg_pairs)))
        ++ ((memory_to_sm_fifos__valid core) ++ (sm_to_memory_fifos__valid core)).

    Definition fs_sm_enter_enclave__conclusion
      (core: ind_core_id) (reg_init reg_final: reg_t -> sval)
      (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) : fancy_spred :=
      let data_this := get_field (_sid enclave_data) (_fld enclave_data "data") (reg_init (_smid (enc_req core))) in
      let req_eid := get_field (_sid enclave_req) (_fld enclave_req "eid") data_this in
      let final_init_pc := reg_final (_cid core init_pc) in
      {{{
          `reg_final ((_smid (state core)))` = #(_enum enum_core_state "Running") /\
          `reg_final ((_smid (enc_data core)))` = `reg_init ((_smid (enc_req core)))` /\
          { ``fs_eid_to_assert_init_pc req_eid final_init_pc Enclave0`` /\
            ``fs_eid_to_assert_init_pc req_eid final_init_pc Enclave1`` /\
            ``fs_eid_to_assert_init_pc req_eid final_init_pc Enclave2`` /\
            ``fs_eid_to_assert_init_pc req_eid final_init_pc Enclave3``
          } /\
          { forall x in [_cid core purge; _mid (Memory.purge core); (_smid (enc_req core))],
            `reg_final x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
          } /\
          { forall x in (map reg_to_debug_id (sm_fifo_sims core)),
            `reg_final x` = `reg_init x`
          }
      }}}.

    Definition fs_sm_enter_enclave
      (core: ind_core_id) (reg_init reg_final: reg_t -> sval)
      (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) : fancy_spred :=
      let data_other := senc_data (other_core core) reg_init get_field in
      let data_this := get_field (_sid enclave_data) (_fld enclave_data "data") (reg_init ((_smid (enc_req core)))) in
      {{{ `reg_init ((_smid (state core)))` = #(_enum enum_core_state "Waiting") ->
          `reg_init (_smid clk)` = #(cid_to_bits core) ->
          {`reg_init (_smid (state (other_core core)))` = #(_enum enum_core_state "Waiting") \/
            {``fs_enc_reqs_conflict data_this data_other get_field`` -> False}
          } ->
          `` fs_sm_enter_enclave__conclusion core reg_init reg_final get_field ``
      }}}.
  Definition fs_req_addrs_in_range (core: ind_core_id)
                                   (reg_fn: reg_t -> sval)
                                   (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                   : fancy_spred :=
    let (to_imem_data, to_imem_valid) :=
      (_mid ((Memory.toIMem core) MemReq.data0), (_mid ((Memory.toIMem core) MemReq.valid0))) in
    let (to_dmem_data, to_dmem_valid) :=
      (_mid ((Memory.toDMem core) MemReq.data0), (_mid ((Memory.toDMem core) MemReq.valid0))) in
    {{{ `senc_data_valid core reg_fn get_field` = Ob~1 ->
        ``foo_fifo_req_addrs_in_range enclave_sig reg_fn get_field to_imem_valid to_imem_data ((_smid (enc_data core))) `` /\
        ``foo_fifo_req_addrs_in_range enclave_sig reg_fn get_field to_dmem_valid to_dmem_data ((_smid (enc_data core))) ``
    }}}.

  Definition sm_invariant (reg_fn: reg_t -> sval) get_field: list (sm_custom_t * fancy_spred) :=
    [(SM_inv_waiting CoreId0, fs_sm_inv_waiting CoreId0 reg_fn)
    ;(SM_inv_waiting CoreId1, fs_sm_inv_waiting CoreId1 reg_fn)
    ;(SM_inv_core_reset CoreId0, fs_sm_inv_core_reset CoreId0 reg_fn)
    ;(SM_inv_core_reset CoreId1, fs_sm_inv_core_reset CoreId1 reg_fn)
    ;(SM_inv_mem_reset CoreId0, fs_sm_inv_mem_reset CoreId0 reg_fn)
    ;(SM_inv_mem_reset CoreId1, fs_sm_inv_mem_reset CoreId1 reg_fn)
    ;(SM_inv_reset_mem CoreId0, fs_reset_mem_correct CoreId0 reg_fn get_field)
    ;(SM_inv_reset_mem CoreId1, fs_reset_mem_correct CoreId1 reg_fn get_field)
    ;(SM_enc_data_valid CoreId0, fs_sm_inv_enc_data_valid CoreId0 reg_fn get_field)
    ;(SM_enc_data_valid CoreId1, fs_sm_inv_enc_data_valid CoreId1 reg_fn get_field)
    ;(SM_inv_reset CoreId0, fs_sm_inv_reset_correct CoreId0 reg_fn get_field)
    ;(SM_inv_reset CoreId1, fs_sm_inv_reset_correct CoreId1 reg_fn get_field)
    ;(SM_mmio_req_in_range CoreId0, fs_mmio_req_in_range CoreId0 reg_fn get_field)
    ;(SM_mmio_req_in_range CoreId1, fs_mmio_req_in_range CoreId1 reg_fn get_field)
    ;(SM_disjoint_configs, fs_disjoint_configs reg_fn get_field)
    ;(SM_disjoint_eid, fs_disjoint_eid reg_fn get_field)
    ;(SM_disjoint_sid, fs_disjoint_sid reg_fn get_field)
    ;(SM_enc_req CoreId0, fs_enc_req CoreId0 reg_fn get_field)
    ;(SM_enc_req CoreId1, fs_enc_req CoreId1 reg_fn get_field)
    ;(SM_valid_addrs CoreId0, fs_req_addrs_in_range CoreId0 reg_fn get_field)
    ;(SM_valid_addrs CoreId1, fs_req_addrs_in_range CoreId1 reg_fn get_field)
    ].
  Definition sm_pre_conds' (reg_init : reg_t -> sval) : list (sm_custom_t * fancy_spred) := [].
  Definition sm_pre_conds (reg_init: reg_t -> sval) get_field : list (sm_custom_t * fancy_spred) :=
     (sm_pre_conds' reg_init) ++ (sm_invariant reg_init get_field).
  Definition sm_post_conds'_preserve
    (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval)
    (get_field: debug_id_ty -> debug_id_ty -> sval -> sval): list (sm_custom_t * fancy_spred) :=
    [(SM_Tick, {{{ `reg_init (_smid clk)` + Ob~1 = `reg_final (_smid clk)`}}});
     (SM_Waiting0, fs_sm_still_waiting CoreId0 reg_init reg_final get_field);
     (SM_Waiting1, fs_sm_still_waiting CoreId1 reg_init reg_final get_field);
     (SM_Enter0, fs_sm_enter_enclave CoreId0 reg_init reg_final get_field);
     (SM_Enter1, fs_sm_enter_enclave CoreId1 reg_init reg_final get_field);
     (SM_uart_write_zeroes, fs_sm_ext_fn_zero (_fld enclave_req "ext_uart") (_extid ext_uart_write)
                              reg_init ext_log get_field);
     (SM_uart_read_zeroes, fs_sm_ext_fn_zero (_fld enclave_req "ext_uart") (_extid ext_uart_read)
                             reg_init ext_log get_field);
     (SM_led_zeroes, fs_sm_ext_fn_zero (_fld enclave_req "ext_led") (_extid ext_led) reg_init ext_log get_field);
     (SM_finish_zeroes, fs_sm_ext_fn_zero (_fld enclave_req "ext_finish") (_extid ext_finish) reg_init ext_log get_field);
     (SM_config_same CoreId0, fs_config_same CoreId0 reg_init reg_final get_field);
     (SM_config_same CoreId1, fs_config_same CoreId1 reg_init reg_final get_field)
    ].

  Definition fs_post_core_purge (core: ind_core_id) (reg_init reg_final: reg_t -> sval)
                                (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                : fancy_spred :=
    {{{ `reg_final (_cid core purge)` = #(_enum purge_state "Purged") ->
        `reg_init (_cid core purge)` = #(_enum purge_state "Purged")
    }}}.

  Definition fs_post_mem_purge (core: ind_core_id) (reg_init reg_final: reg_t -> sval)
                                (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                : fancy_spred :=
    {{{ `reg_final (_mid (Memory.purge core))` = #(_enum purge_state "Purged") ->
        `reg_init (_mid (Memory.purge core))` = #(_enum purge_state "Purged")
    }}}.


  Definition fs_sm_not_running (core: ind_core_id) (reg_init reg_final: reg_t -> sval)
                               (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                : fancy_spred :=
    {{{ `reg_init ((_smid (state core)) )` <> #(_enum enum_core_state "Running") ->
        {forall x in (map reg_to_debug_id ((sm_to_core_fifos core) ++ (sm_to_memory_fifos core))),
         `reg_final x` = `reg_init x`
        }
    }}}.

  Definition sm_post_conds' (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval)
                            (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      : list (sm_custom_t * fancy_spred) :=
    sm_post_conds'_preserve reg_init reg_final ext_log get_field ++
    [(SM_taint, {{{ forall x in (remove_regs reg_list  (map reg_to_debug_id ((sm_regs CoreId0) ++ (sm_regs CoreId1))%list)),
                     `reg_final x` = `reg_init x`
                 }}})
    ; (SM_post_core_purge0, fs_post_core_purge CoreId0 reg_init reg_final get_field)
    ; (SM_post_core_purge1, fs_post_core_purge CoreId1 reg_init reg_final get_field)
    ; (SM_post_mem_purge0, fs_post_mem_purge CoreId0 reg_init reg_final get_field)
    ; (SM_post_mem_purge1, fs_post_mem_purge CoreId1 reg_init reg_final get_field)
    ; (SM_not_running0, fs_sm_not_running CoreId0 reg_init reg_final get_field)
    ; (SM_not_running1, fs_sm_not_running CoreId1 reg_init reg_final get_field)
    ].

  Definition sm_post_conds
    (reg_init reg_final: reg_t -> sval)
    (ext_log: debug_id_ty -> sval)
    (get_field: debug_id_ty -> debug_id_ty -> sval -> sval): list (sm_custom_t * fancy_spred) :=
    (sm_post_conds' reg_init reg_final ext_log get_field) ++ (sm_invariant reg_final get_field).

  Definition sm_reset_regs (core: ind_core_id) :=
    [(SM (sm_reset core))]
      ++  (core_regs_to_reset core) ++ (sm_reset_fifos core) ++ (mem_regs_to_reset core).
  (* TODO *)
  Definition sm_reset_post (core: ind_core_id)
                         (reg_init reg_final: reg_t -> sval)
                         (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                         : fancy_spred :=
  {{{ `reg_init ((_smid (state core)))` = #(_enum enum_core_state "Waiting") ->
        { forall x in ([(_smid (sm_reset core))] ++
                    (map reg_to_debug_id (sm_reset_regs core)
                    )
                 ),
          `reg_final x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
        }
   }}}.

  Definition fs_req_addrs_in_config enclave_sig
    (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) (reg_data reg_enclave: sval) : fancy_spred :=
    {{{
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Enclave Enclave0) get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Enclave Enclave1) get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Enclave Enclave2) get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Enclave Enclave3) get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared01) get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared02) get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared03) get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared12) get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared13) get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared23) get_field reg_data reg_enclave``
    }}}.

  Definition push_req_in_config (core: ind_core_id)
                                (reg_init: reg_t  -> sval)
                                (committed_ext_fn: debug_id_ty -> sval)
                                (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                : fancy_spred :=
    let push_req_valid := get_field (_sid mem_input) (_fld mem_input "put_valid")
                                                (committed_ext_fn (_extid ext_mainmem)) in
    let req := get_field (_sid mem_input) (_fld mem_input "put_request")
                          (committed_ext_fn (_extid ext_mainmem)) in
    let reg_data := req in
    let reg_enclave := reg_init ((_smid (enc_data core))) in
    {{{ `push_req_valid` = Ob~1 ->
        `reg_init (_mid Memory.turn)` = #(mem_core_write_turn core) ->
        ``fs_req_addrs_in_config enclave_sig get_field reg_data reg_enclave``
    }}}.
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
  Definition SMPre (st: Environments.state_t) (sigma: @ext_sigma_t N) : Prop :=
        Forall (fun '(_, p) =>
                  interp_fancy_spred
                    {| pkg_machine := impl_machine;
                       pkg_init_st := st; pkg_mid_st := None; pkg_final_st := st; (* don't care *)
                       pkg_sigma := sigma; pkg_mid_ext_log := None; pkg_ext_log' := SortedExtFnEnv.empty; (* don't care *)
                    |} p) (sm_pre_conds impl_init impl_get_field).
  Definition SMPost (st st': Environments.state_t) (sigma: @ext_sigma_t N) (ext_log: ext_log_t): Prop :=
        Forall (fun '(_, p) =>
                  interp_fancy_spred
                    {| pkg_machine := impl_machine;
                       pkg_init_st := st; pkg_mid_st := None; pkg_final_st := st';
                       pkg_sigma := sigma; pkg_mid_ext_log := None; pkg_ext_log' := ext_log
                    |} p) (sm_post_conds impl_init impl_final impl_final_ext impl_get_field).

  End WithEnclaveSig.
End SMSymbDefs.
Require Import koika.AnnotatedSyntax.

Module Type SmProofDefs (EnclaveParams: EnclaveParams_sig)
                        (SecurityParams: SecurityParams_sig EnclaveParams).
  Import SecurityMonitor.
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SMSymbDefs.
  Section ImplMachine.
    Notation reg_t := (@reg_t debug_id_ty).
    Definition impl_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (rl, show rl)) (list_of_schedule (Impl.sm_schedule)).
    Definition impl_typecheck_fn rl : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl).
    Definition impl_schedule :=
      preprocess_schedule impl_typecheck_fn rules impl_schedule_list.
    (* Lemma impl_schedule_oraat_ok: *)
    (*   oraat_ok id_int_fns id_rules (list_of_schedule Impl.sm_schedule) = true. *)
    (* Proof. *)
    (*   vm_reflect. *)
    (* Qed. *)

  End ImplMachine.
  Section SpecMachine0.

    Definition spec0_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (Machine.RlSm rl, show (Machine.RlSm rl))) (list_of_schedule (sm_schedule CoreId0)).
    Definition spec0_typecheck_fn rl : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl).
    Definition spec0_schedule :=
      preprocess_schedule spec0_typecheck_fn rules spec0_schedule_list.

  End SpecMachine0.

  Section SpecMachine1.
    Definition spec1_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (Machine.RlSm rl, show (Machine.RlSm rl))) (list_of_schedule (sm_schedule CoreId1)).
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
         file_assumptions := preprocess_fancy_spreds (sm_pre_conds EnclaveParams.enclave_sig impl_init impl_get_field);
         file_assertions := preprocess_fancy_spreds (sm_post_conds EnclaveParams.enclave_sig impl_init impl_final impl_final_ext impl_get_field);
      |}.
    (* Definition file: file_t := *)
      (* Eval vm_compute in file'. *)

  End ImplStep.

End SmProofDefs.

Module Type SMT_SM_sig (EnclaveParams: EnclaveParams_sig)
                       (SecurityParams: SecurityParams_sig EnclaveParams)
                       (SmDefs: SmProofDefs EnclaveParams SecurityParams).

  Parameter SMT_file_ok: SymbolicInterp.WF_single_file SmDefs.ImplStep.file = true.

End SMT_SM_sig.



Module SmProofs (EnclaveParams: EnclaveParams_sig)
                (SecurityParams: SecurityParams_sig EnclaveParams)
                (SmDefs: SmProofDefs EnclaveParams SecurityParams)
                (SmtOk: SMT_SM_sig EnclaveParams SecurityParams SmDefs).
  Import SecurityMonitor.
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Import SMSymbDefs.
  Import SmDefs.
  Import SmtOk.
  Theorem impl_step_sm_correct:
    symbolic_evaluate_file_success_single
      impl_machine impl_schedule
        (preprocess_fancy_spreds (sm_pre_conds EnclaveParams.enclave_sig impl_init impl_get_field))
        (preprocess_fancy_spreds (sm_post_conds EnclaveParams.enclave_sig impl_init impl_final impl_final_ext impl_get_field)).
  Proof.
    pose proof SMT_file_ok.
    specialize symbolic_evaluate_file_success with (file := ImplStep.file).
    eauto.
  Qed.

  Theorem impl_step_sm_sched_correct:
      interp_scheduler_satisfies_spec reg_type_env _ext_fn_tys id_int_fns id_struct_defs
        id_rules Impl.sm_schedule unit
        (fun st sigma _ => SMPre EnclaveParams.enclave_sig st  sigma)
        (fun st sigma st' ext_log _ => SMPost EnclaveParams.enclave_sig st st' sigma ext_log).
  Proof.
      unfold interp_scheduler_satisfies_spec.
      intros * _ hwf_st hwf_sigma hwf_fns hinterp hpre.
      specialize typecheck_scheduler_correct'' with (5 := hinterp) (2 := hwf_st) (3 := hwf_sigma) (4 := hwf_fns) (1 := eq_refl). intros (hwf_impl' & wf_impl_ext').
      (* specialize @oraat_interp_scheduler__conflicts_correct with *)
      (*      (1 := strong_WF_state_weaken _ _ hwf_st) (2 := hwf_sigma) (3 := hwf_fns) (6 := hinterp) (4 := eq_refl) (5 := impl_schedule_oraat_ok). intros Horaat_impl. *)
      split_ands_in_goal; auto.
      consider SMPost.
      specialize impl_step_sm_correct. unfold symbolic_evaluate_file_success_single.
      intros.
      rewrite<-forall_preprocess_fancy_spreds_correct.
      apply H.
      + consider SMPre. revert hpre.
        repeat rewrite<-forall_preprocess_fancy_spreds_correct.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      + unfold machine_to_prop. split_ands_in_goal.
        * auto.
        * apply strong_WF_state_weaken in hwf_st.
          eapply WF_state_subset with (2 := hwf_st). vm_compute; reflexivity.
        * unfold impl_schedule. consider impl_schedule_list.
          move hinterp at bottom. consider impl_typecheck_fn.
          set (strip_dbg_sched_list _ ) as l in *.
          assert (l = (map (fun rl => id_transform_action _id (rules rl)) (list_of_schedule Impl.sm_schedule))) as Hl.
          { vm_reflect. }
          rewrite Hl.
          consider id_rules.
          apply interp_scheduler_list_equiv.
          apply hinterp.
  Qed.

End SmProofs.

(* Module TestSm. *)
(*   Require Import koikaExamples.Enclaves.External. *)

(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module Smdefs := Empty <+ SmProofDefs EnclaveParams SecurityParams. *)

(*   Module SmProof := SmProofs EnclaveParams SecurityParams Smdefs. *)
(*   Import SmProof. *)
(*   Import Smdefs. *)

(*   Definition file := Eval vm_compute in ImplStep.file. *)
(*   Extraction "TestSm.ml" struct_sz vect_t file. *)



(* End TestSm. *)
