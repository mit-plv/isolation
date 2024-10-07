Require Import rv_cache_isolation.Common.
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
(* Require Import koikaExamples.EnclaveWithCache.MemoryDefs. *)

Inductive mem_custom_t :=
| Mem_Taint
| Mem_Tick
| Mem_push_zero0
| Mem_push_zero1
| Mem_push_zero_both
| Mem_push_in_range0
| Mem_push_in_range1
| Mem_push_in_config0
| Mem_push_in_config1
| Mem_purged0
| Mem_purged1
| Mem_addrs_in_range (cache: mem_type) (core: ind_core_id)
| Mem_post_Ready (cache: mem_type) (core: ind_core_id)
| Mem_post_FlushLineReady (cache: mem_type) (core: ind_core_id)
| Mem_post_FlushLineProcess (cache: mem_type) (core: ind_core_id)
| Mem_post_FlushPrivateData (cache: mem_type) (core: ind_core_id)
| Mem_post_ToMem (cache: mem_type) (core: ind_core_id)
| Mem_purged_preserve (core: ind_core_id)
| Mem_purged_frozen (core: ind_core_id)
| Mem_cache_Flushed (cache: mem_type) (core: ind_core_id)
| Mem_cache_FlushPrivateData (cache: mem_type) (core: ind_core_id)
| Mem_cache_FlushLineProcess (cache: mem_type) (core: ind_core_id)
| Mem_cache_FlushLineReady (cache: mem_type) (core: ind_core_id)
| Mem_cache_WaitFillResp (cache: mem_type) (core: ind_core_id)
| Mem_cache_SendFillReq (cache: mem_type) (core: ind_core_id)
| Mem_cache_ProcessRequest (cache: mem_type) (core: ind_core_id)
| Mem_cache_Ready (cache: mem_type) (core: ind_core_id)
| Mem_cache_cacheshreq_resets (cache: mem_type) (core: ind_core_id)
| Mem_cache_metashreq_resets (cache: mem_type) (core: ind_core_id)
| Mem_cache_single_mainmem_req (cache: mem_type) (core: ind_core_id)
| Mem_cache_single_cache_req (cache: mem_type) (core: ind_core_id)
| Mem_cache_single_meta_req (cache: mem_type) (core: ind_core_id)
| Mem_shreq_invalid
| Mem_no_new_reqs (core: ind_core_id)
| MemExtFn (id: N)
| MemImplExtCorrectCore (core: ind_core_id)
| MemMainMemPutIsReadTurn
| MemCacheNoResp (cache: mem_type) (core: ind_core_id)
| MemMetaNoResp (cache: mem_type) (core: ind_core_id)
| MemMetaRespInRange (cache: mem_type) (core: ind_core_id)
| Mem_custom (str: string)
| Mem_PostCacheGetReady__Ext (cache: mem_type) (core: ind_core_id)
| Mem_PostCacheGetReady__Reg (cache: mem_type) (core: ind_core_id)
| Mem_PostMetaGetReady__Ext (cache: mem_type) (core: ind_core_id)
| Mem_PostMetaGetReady__Reg (cache: mem_type) (core: ind_core_id)
| Mem_PostMetacacheSameLine (cache: mem_type) (core: ind_core_id)
| Mem_CacheReqAlwaysEmpty (cache: mem_type) (core: ind_core_id)
| Mem_CachePutReady (cache: mem_type) (core: ind_core_id)
| Mem_MetaReqAlwaysEmpty (cache: mem_type) (core: ind_core_id)
| Mem_MetaPutReady (cache: mem_type) (core: ind_core_id)
| Mem_PostCacheAddr (cache: mem_type) (core: ind_core_id)
| Mem_PostCacheFSM_InvertFlushed (cache: mem_type) (core: ind_core_id)
| Mem_PostCacheFSM_InvertFlushPrivateData (cache: mem_type) (core: ind_core_id)
| Mem_PostCacheFSM_InvertFlushLineReady (cache: mem_type) (core: ind_core_id)
| Mem_PostCacheFSM_InvertFlushLineProcess (cache: mem_type) (core: ind_core_id)
| Mem_PostCacheFSM_InvertPurged (cache: mem_type) (core: ind_core_id)
| Mem_FlushFSM_OnlyInvalidateMetadata (cache: mem_type) (core: ind_core_id)
| Mem_FlushFSM_OnlyInvalidateCache (cache: mem_type) (core: ind_core_id)
| Mem_MetaCacheLockStep (cache: mem_type) (core: ind_core_id)
| Mem_ExtRespLockStep (cache: mem_type) (core: ind_core_id)
| Mem_PurgedArgsZero (cache: mem_type) (core: ind_core_id)
(* | Mem_FlushFSM_OnlyInvalidateMetadata__Inv (cache: mem_type) (core: ind_core_id) *)
.
Instance EqDec_mem_custom_t : EqDec mem_custom_t := _.


  Import Memory.
  Import PfHelpers.
Notation reg_t := (@Syntax.reg_t debug_id_ty).

Module MemSymbDefs.
  Notation reg_t := (@Syntax.reg_t debug_id_ty).

  Definition fs_mem_push_zero (core: ind_core_id) (reg_init: reg_t -> sval) (ext_log: debug_id_ty -> sval): fancy_spred :=
    let (imem_valid, dmem_valid) := ((Memory.coreToCache imem core) MemReq.valid0, (Memory.coreToCache dmem core) MemReq.valid0) in
    let cache_fsm cache := cache_reg cache core CacheState.cache_fsm in
    {{{ `reg_init (_mid turn)` = #(mem_core_write_turn core) ->
        `reg_init (_mid (cache_fsm imem))` = #(_enum cache_fsm_sig "Ready") ->
        `reg_init (_mid (cache_fsm dmem))` = #(_enum cache_fsm_sig "Ready") ->
        (* `reg_init (_mid (cache_fsm imem))` <> #(_enum cache_fsm_sig "SendFillReq") -> *)
        (* `reg_init (_mid (cache_fsm imem))` <> #(_enum cache_fsm_sig "WaitFillResp") -> *)
        (* `reg_init (_mid (cache_fsm imem))` <> #(_enum cache_fsm_sig "ProcessRequest") -> *)
        (* `reg_init (_mid (cache_fsm dmem))` <> #(_enum cache_fsm_sig "SendFillReq") -> *)
        (* `reg_init (_mid (cache_fsm dmem))` <> #(_enum cache_fsm_sig "WaitFillResp") -> *)
        (* `reg_init (_mid (cache_fsm dmem))` <> #(_enum cache_fsm_sig "ProcessRequest") -> *)
        (* `reg_init (_mid imem_valid)` = Ob~0 -> *)
        (* `reg_init (_mid dmem_valid)` = Ob~0 -> *)
        `impl_get_field (_sid mem_input) (_fld mem_input "put_valid") (ext_log (_extid ext_mainmem))` = Ob~0
        (* `impl_get_field (_sid mem_req) (_fld mem_req "byte_en") (impl_get_field (_sid mem_input) (_fld mem_input "put_request") (ext_log (_extid ext_mainmem)))` <> Ob~0~0~0~0 *)
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
    let (to_imem_data, to_imem_valid) := ((Memory.coreToCache imem core) MemReq.data0, (Memory.coreToCache imem core) MemReq.valid0) in
    let (to_dmem_data, to_dmem_valid) := ((Memory.coreToCache dmem core) MemReq.data0, (Memory.coreToCache dmem core) MemReq.valid0) in
    {{{ ``fs_fifo_no_new_reqs reg_init reg_final (_mid to_imem_data) (_mid to_imem_valid)`` /\
        ``fs_fifo_no_new_reqs reg_init reg_final (_mid to_dmem_data) (_mid to_dmem_valid) ``
    }}}.

    (* (map Memory (map (Memory.cache_reg cache core) *)
    (*                ((map CacheState.SH_metadata_req FiniteType.finite_elements) ++ *)
    (*                 (map CacheState.SH_metadata_resp FiniteType.finite_elements) ++ *)
    (*                 (map CacheState.SH_cache_req FiniteType.finite_elements) ++ *)
    (*                 (map CacheState.SH_cache_resp FiniteType.finite_elements) ++ *)
    (*                 (map CacheState.toMainMem FiniteType.finite_elements) ++ *)
    (*                 (map CacheState.fromMainMem FiniteType.finite_elements) ++ *)
    (*                 [CacheState.line_flush_idx; CacheState.cache_fsm]))). *)
  Definition mem_cache_regs_reset_at_Flushed (cache: mem_type) (core: ind_core_id) : list SecurityMonitor.reg_t :=
    (map Memory (map (Memory.cache_reg cache core)
                   ((map CacheState.SH_metadata_req FiniteType.finite_elements) ++
                    (map CacheState.SH_metadata_resp FiniteType.finite_elements) ++
                    (map CacheState.SH_cache_req FiniteType.finite_elements) ++
                    (map CacheState.SH_cache_resp FiniteType.finite_elements) ++
                    (map CacheState.toMainMem [MemReqBypass.valid0]) ++
                    (map CacheState.fromMainMem FiniteType.finite_elements) ++
                    [CacheState.line_flush_idx(* ; CacheState.cache_fsm *)]))).

  Definition no_load_toMainMem (core: ind_core_id) (cache: mem_type)
                               (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                               : fancy_spred :=
    let toMainMem_data := cache_reg cache core (CacheState.toMainMem MemReqBypass.data0) in
    let toMainMem_valid := cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0) in
    let fromMainMem_valid := cache_reg cache core (CacheState.fromMainMem MemResp.valid0) in
    {{{
        `reg_fn (_mid fromMainMem_valid)` = Ob~0 /\
         { `reg_fn (_mid toMainMem_valid)` = Ob~0 \/
             `get_field (_sid mem_req) (_fld mem_req "byte_en") (reg_fn (_mid toMainMem_data))` <> Ob~0~0~0~0 }
    }}}.

  Definition no_load_toMeta (core: ind_core_id) (cache: mem_type)
                            (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                            : fancy_spred :=
   let toMeta_data  := _mid (cache_reg cache core (CacheState.SH_metadata_req MetadataReqBypass.data0)) in
   let toMeta_valid := _mid (cache_reg cache core (CacheState.SH_metadata_req MetadataReqBypass.valid0)) in
   let fromMeta_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in
   {{{ `reg_fn fromMeta_valid` = Ob~0 /\
       { `reg_fn toMeta_valid` = Ob~0 \/
         `get_field (_sid metadata_req_sig) (_fld metadata_req_sig "is_write") (reg_fn toMeta_data)` = Ob~1
       }
   }}}.

  Definition no_load_toCache (core: ind_core_id) (cache: mem_type)
                            (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                            : fancy_spred :=
   let toCache_valid := _mid (cache_reg cache core (CacheState.SH_cache_req CacheReqBypass.valid0)) in
   let toCache_data  := _mid (cache_reg cache core (CacheState.SH_cache_req CacheReqBypass.data0)) in
   let fromCache_valid := _mid (cache_reg cache core (CacheState.SH_cache_resp CacheResp.valid0)) in
   {{{ `reg_fn fromCache_valid` = Ob~0 /\
       { `reg_fn toCache_valid` = Ob~0 \/
         `get_field (_sid cache_req_sig) (_fld cache_req_sig "byte_en") (reg_fn toCache_data)` <> Ob~0~0~0~0
       }
   }}}.

    (* let toMainMem_data := cache_reg cache core (CacheState.toMainMem MemReqBypass.data0) in *)
    (* let toMainMem_valid := cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0) in *)
    (* let fromMainMem_valid := cache_reg cache core (CacheState.fromMainMem MemResp.valid0) in *)
    (* {{{ True }}}. *)
    (*     `reg_fn (_mid fromMainMem_valid)` = Ob~0 /\ *)
    (*      { `reg_fn (_mid toMainMem_valid)` = Ob~0 \/ *)
    (*          `get_field (_sid mem_req) (_fld mem_req "byte_en") (reg_fn (_mid toMainMem_data))` <> Ob~0~0~0~0 } *)
    (* }}}. *)


  Definition cache_Ready (core: ind_core_id) (cache: mem_type)
                           (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                           : fancy_spred :=
    let cache_fsm := cache_reg cache core CacheState.cache_fsm in
    let toMainMem_valid := cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0) in
    let metaResp_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in
    let cacheResp_valid := _mid (cache_reg cache core (CacheState.SH_cache_resp CacheResp.valid0)) in
    let mk_pred pred :=
      {{{ `reg_fn (_mid cache_fsm)` = #(_enum cache_fsm_sig "Ready") ->
          `` pred ``
      }}} in
    {{{ ``mk_pred (no_load_toMainMem core cache reg_fn get_field) `` /\
        ``mk_pred (no_load_toMeta core cache reg_fn get_field) `` /\
        ``mk_pred (no_load_toCache core cache reg_fn get_field) `` /\
        ``mk_pred {{{ `reg_fn (_mid toMainMem_valid)` = Ob~0 }}} ``
        (* ``mk_pred {{{ `reg_fn metaResp_valid` = Ob~0 }}} `` /\ *)
        (* ``mk_pred {{{ `reg_fn cacheResp_valid` = Ob~0 }}} `` *)
    }}}.

  Definition cache_ProcessRequest (core: ind_core_id) (cache: mem_type)
                           (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                           : fancy_spred :=
    let cache_fsm := cache_reg cache core CacheState.cache_fsm in
    let toMainMem_valid := cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0) in
    let coreToCache_valid := Memory.coreToCache cache core MemReq.valid0 in
    let mk_pred pred :=
      {{{ `reg_fn (_mid cache_fsm)` = #(_enum cache_fsm_sig "ProcessRequest") ->
          `` pred ``
      }}} in
    {{{ ``mk_pred (no_load_toMainMem core cache reg_fn get_field) `` /\
        ``mk_pred {{{ `reg_fn (_mid toMainMem_valid)` = Ob~0 }}} `` /\
        ``mk_pred {{{ `reg_fn (_mid coreToCache_valid)` = Ob~1 }}} ``
    }}}.


  Definition cache_SendFillReq (core: ind_core_id) (cache: mem_type)
                           (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                           : fancy_spred :=
    let cache_fsm := cache_reg cache core CacheState.cache_fsm in
    let coreToCache_valid := Memory.coreToCache cache core MemReq.valid0 in
    let mk_pred pred :=
      {{{ `reg_fn (_mid cache_fsm)` = #(_enum cache_fsm_sig "SendFillReq") ->
          `` pred ``
      }}} in
    {{{ ``mk_pred (no_load_toMainMem core cache reg_fn get_field) `` /\
        ``mk_pred {{{ `reg_fn (_mid coreToCache_valid)` = Ob~1 }}} `` /\
        ``mk_pred (no_load_toMeta core cache reg_fn get_field) `` /\
        ``mk_pred (no_load_toCache core cache reg_fn get_field) ``
    }}}.


  Definition cache_WaitFillResp (core: ind_core_id) (cache: mem_type)
                           (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                           : fancy_spred :=
    let cache_fsm := cache_reg cache core CacheState.cache_fsm in
    let coreToCache_valid := Memory.coreToCache cache core MemReq.valid0 in
    let mk_pred pred :=
      {{{ `reg_fn (_mid cache_fsm)` = #(_enum cache_fsm_sig "WaitFillResp") ->
          `` pred ``
      }}} in
    {{{ ``mk_pred {{{ `reg_fn (_mid coreToCache_valid)` = Ob~1 }}} `` /\
        ``mk_pred (no_load_toMeta core cache reg_fn get_field) `` /\
        ``mk_pred (no_load_toCache core cache reg_fn get_field) ``

    }}}
  .

  Definition cache_FlushLineReady (core: ind_core_id) (cache: mem_type)
                           (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                           : fancy_spred :=
    let cache_fsm := cache_reg cache core CacheState.cache_fsm in
    let toMainMem_valid := cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0) in
    let coreToCache_valid := _mid (Memory.coreToCache cache core MemReq.valid0) in
    let purge_reg := _mid (purge core) in
    let mk_pred pred :=
      {{{ `reg_fn (_mid cache_fsm)` = #(_enum cache_fsm_sig "FlushLineReady") ->
          `` pred ``
      }}} in
    {{{ ``mk_pred (no_load_toMainMem core cache reg_fn get_field) `` /\
        ``mk_pred (no_load_toMeta core cache reg_fn get_field) `` /\
        ``mk_pred (no_load_toCache core cache reg_fn get_field) `` /\
        ``mk_pred {{{ `reg_fn (coreToCache_valid)` = Ob~0 }}} `` /\
        ``mk_pred {{{ `reg_fn (coreToCache_valid)` = Ob~0 }}} `` /\
        ``mk_pred {{{ `reg_fn purge_reg` =  #(_enum purge_state "Purging") }}} ``
    }}}.


  Definition cache_FlushLineProcess (core: ind_core_id) (cache: mem_type)
                           (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                           : fancy_spred :=
    let cache_fsm := cache_reg cache core CacheState.cache_fsm in
    let coreToCache_valid := _mid (Memory.coreToCache cache core MemReq.valid0) in
    let purge_reg := _mid (purge core) in
    let mk_pred pred :=
      {{{ `reg_fn (_mid cache_fsm)` = #(_enum cache_fsm_sig "FlushLineProcess") ->
          `` pred ``
      }}} in
    {{{ ``mk_pred (no_load_toMainMem core cache reg_fn get_field) `` /\
        ``mk_pred {{{ `reg_fn (coreToCache_valid)` = Ob~0 }}} `` /\
        ``mk_pred {{{ `reg_fn purge_reg` =  #(_enum purge_state "Purging") }}} ``
    }}}.

  Definition cache_FlushPrivateData (core: ind_core_id) (cache: mem_type)
                           (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                           : fancy_spred :=
    let cache_fsm := cache_reg cache core CacheState.cache_fsm in
    let coreToCache_valid := _mid (Memory.coreToCache cache core MemReq.valid0) in
    let purge_reg := _mid (purge core) in
    let mk_pred pred :=
      {{{ `reg_fn (_mid cache_fsm)` = #(_enum cache_fsm_sig "FlushPrivateData") ->
          `` pred ``
      }}} in
    {{{ ``mk_pred (no_load_toMainMem core cache reg_fn get_field) ``  /\
        ``mk_pred (no_load_toMeta core cache reg_fn get_field) `` /\
        ``mk_pred (no_load_toCache core cache reg_fn get_field) `` /\
        ``mk_pred {{{ `reg_fn (coreToCache_valid)` = Ob~0 }}} `` /\
        ``mk_pred {{{ `reg_fn purge_reg` =  #(_enum purge_state "Purging") }}} ``
    }}}.

  Definition cache_Flushed (core: ind_core_id) (cache: mem_type)
                           (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                           : fancy_spred :=
    let cache_fsm := cache_reg cache core CacheState.cache_fsm in
    let mk_pred pred :=
      {{{ `reg_fn (_mid cache_fsm)` = #(_enum cache_fsm_sig "Flushed") ->
          `` pred ``
      }}} in
    let reset :=
       {{{  forall x in (map reg_to_debug_id (mem_cache_regs_reset_at_Flushed cache core)),
             `reg_fn x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
       }}}   in
    {{{ ``mk_pred reset`` }}}.

  Definition cache_cacheReq_resets (cache: mem_type) (core: ind_core_id)
    (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    : fancy_spred :=
    {{{ `reg_fn (_mid (cache_reg cache core (CacheState.SH_cache_req CacheReqBypass.valid0)))` = Ob~0 ->
        `reg_fn (_mid (cache_reg cache core (CacheState.SH_cache_req CacheReqBypass.data0)))` = #(zeroes (_unsafe_struct_sz cache_req_sig))
    }}}.

  Definition cache_metaReq_resets (cache: mem_type) (core: ind_core_id)
    (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    : fancy_spred :=
    {{{ `reg_fn (_mid (cache_reg cache core (CacheState.SH_metadata_req MetadataReqBypass.valid0)))` = Ob~0 ->
        `reg_fn (_mid (cache_reg cache core (CacheState.SH_metadata_req MetadataReqBypass.data0)))` = #(zeroes (_unsafe_struct_sz metadata_req_sig))
    }}}.

  Definition single_outstanding_mainmem_req
    (cache: mem_type) (core: ind_core_id)
    (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    : fancy_spred :=
    let toMainMem_valid := cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0) in
    let fromMainMem_valid := cache_reg cache core (CacheState.fromMainMem MemResp.valid0) in
    {{{ `reg_fn (_mid toMainMem_valid)` = Ob~0 \/
        `reg_fn (_mid fromMainMem_valid)` = Ob~0
    }}}.

  (* Definition single_outstanding_meta_req *)
  (*   (cache: mem_type) (core: ind_core_id) *)
  (*   (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) *)
  (*   : fancy_spred := *)
  (*   let toMeta_valid := _mid (cache_reg cache core (CacheState.SH_metadata_req MetadataReqBypass.valid0)) in *)
  (*   let fromMeta_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in *)
  (*   {{{ `reg_fn (toMeta_valid)` = Ob~0 \/ `reg_fn (fromMeta_valid)` = Ob~0 *)
  (*   }}}. *)

  (* Definition single_outstanding_cache_req *)
  (*   (cache: mem_type) (core: ind_core_id) *)
  (*   (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) *)
  (*   : fancy_spred := *)
  (*   let toCache_valid := _mid (cache_reg cache core (CacheState.SH_cache_req CacheReqBypass.valid0)) in *)
  (*   let fromCache_valid := _mid (cache_reg cache core (CacheState.SH_cache_resp CacheResp.valid0)) in *)
  (*   {{{ `reg_fn (toCache_valid)` = Ob~0 \/ `reg_fn (fromCache_valid)` = Ob~0 *)
  (*   }}}. *)

   Definition fs_addr_in_region enclave_sig (region: mem_region)
     (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) (sval_addr reg_enclave: sval) : fancy_spred :=
     let sval_enclave_data :=
       get_field (_sid enclave_data) (_fld enclave_data "data") (reg_enclave)  in
     match region with
     | MemRegion_Enclave eid  =>
         {{{ `get_field (_sid enclave_req) (_fld enclave_req "eid") sval_enclave_data` = #(enclave_id_to_vect eid) /\
             (#(enclave_sig.(_enclave_base) eid) <= `sval_addr`) = Ob~1 /\
             (`sval_addr` < (#(enclave_sig.(_enclave_base) eid) + #(enclave_sig.(_enclave_size) eid))) = Ob~1
}}}
     | MemRegion_Shared shared_id =>
         {{{ `get_field (_sid enclave_req) (_fld enclave_req "shared_regions") sval_enclave_data` [[ #(shared_id_index shared_id) ]] = Ob~1 /\
             (#(enclave_sig.(_shared_region_base) shared_id) <= `sval_addr`) = Ob~1 /\
             (`sval_addr` < (#(enclave_sig.(_shared_region_base) shared_id) + #(enclave_sig.(_shared_region_size) ))) = Ob~1
}}}
     | MemRegion_Other => {{{ True }}}
     end.

  Definition fs_addr_in_range
    enclave_sig (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    (reg_enclave: reg_t) (sval_addr: sval) : fancy_spred :=
    let reg_enclave := reg_fn reg_enclave in
    {{{
        ``fs_addr_in_region enclave_sig (MemRegion_Enclave Enclave0)   get_field sval_addr reg_enclave`` \/
        ``fs_addr_in_region enclave_sig (MemRegion_Enclave Enclave1)   get_field sval_addr reg_enclave`` \/
        ``fs_addr_in_region enclave_sig (MemRegion_Enclave Enclave2)   get_field sval_addr reg_enclave`` \/
        ``fs_addr_in_region enclave_sig (MemRegion_Enclave Enclave3)   get_field sval_addr reg_enclave`` \/
        ``fs_addr_in_region enclave_sig (MemRegion_Shared Shared01)   get_field sval_addr reg_enclave`` \/
        ``fs_addr_in_region enclave_sig (MemRegion_Shared Shared02)   get_field sval_addr reg_enclave`` \/
        ``fs_addr_in_region enclave_sig (MemRegion_Shared Shared03)   get_field sval_addr reg_enclave`` \/
        ``fs_addr_in_region enclave_sig (MemRegion_Shared Shared12)   get_field sval_addr reg_enclave`` \/
        ``fs_addr_in_region enclave_sig (MemRegion_Shared Shared13)   get_field sval_addr reg_enclave`` \/
        ``fs_addr_in_region enclave_sig (MemRegion_Shared Shared23)   get_field sval_addr reg_enclave``
    }}}.


  Section WithEnclaveSig.
    Context (enclave_sig: enclave_params_sig).
Notation "'{|{' e '}|}'" := (e) (e custom symb_val at level 200, format "'{|{' '[v' '/' e '/' ']' '}|}'").

    Definition derive_metadata_addr (tag index: sval) : sval :=
      {|{ `tag` ++ `index` ++ Ob~0~0 }|}.

    Definition derive_metadata_addr_from_push_req (tag push_req: sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) : sval :=
      let push_req_addr push_req :=
          get_field (_sid mem_req) (_fld mem_req "addr") push_req in
      derive_metadata_addr tag {|{ `push_req_addr push_req` [2 : log_nlines] }|}.


    Definition metadata_resp_in_range_from_core (cache: mem_type) (core: ind_core_id)
                                      (reg_fn: reg_t -> sval)
                                      (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                      : fancy_spred :=
      let coreToCache_valid := (_mid ((Memory.coreToCache cache core) MemReq.valid0)) in
      let coreToCache_data := (_mid ((Memory.coreToCache cache core) MemReq.data0)) in
      let metaResp_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in
      let metaResp_data := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.data0)) in
      let metaResp_tag := get_field (_sid metadata_sig) (_fld metadata_sig "tag") (reg_fn metaResp_data) in
      let reg_enc_data := (_smid (enc_data core)) in
      {{{ `reg_fn coreToCache_valid` = Ob~1 ->
          `reg_fn metaResp_valid` = Ob~1 ->
          `get_field (_sid metadata_sig) (_fld metadata_sig "valid") (reg_fn metaResp_data)` = Ob~1 ->
          ``fs_addr_in_range enclave_sig reg_fn get_field reg_enc_data
                             (derive_metadata_addr_from_push_req metaResp_tag (reg_fn coreToCache_data) get_field) ``
      }}}.

    Definition metadata_resp_in_range_from_flush (cache: mem_type) (core: ind_core_id)
                                      (reg_fn: reg_t -> sval)
                                      (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                      : fancy_spred :=
      let metaResp_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in
      let metaResp_data := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.data0)) in
      let metaResp_tag := get_field (_sid metadata_sig) (_fld metadata_sig "tag") (reg_fn metaResp_data) in
      let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
      let line_flush_idx := _mid (cache_reg cache core CacheState.line_flush_idx) in
      let reg_enc_data := (_smid (enc_data core)) in
      {{{ `reg_fn cache_fsm` = #(_enum cache_fsm_sig "FlushLineProcess") ->
          `reg_fn metaResp_valid` = Ob~1 ->
          `get_field (_sid metadata_sig) (_fld metadata_sig "valid") (reg_fn metaResp_data)` = Ob~1 ->
          ``fs_addr_in_range enclave_sig reg_fn get_field reg_enc_data
                             (derive_metadata_addr metaResp_tag (reg_fn line_flush_idx) ) ``
      }}}.

  Definition meta_resp_in_range_with_line
    (line: vect_t) (data: vect_t) (cache: mem_type) (core: ind_core_id)
    (reg_fn: reg_t -> sval)
    (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    : fancy_spred :=
    let metaResp_tag := get_field (_sid metadata_sig) (_fld metadata_sig "tag") (SConst data) in
    let metaResp_valid := get_field (_sid metadata_sig) (_fld metadata_sig "valid") (SConst data) in
    let enc_data := (_smid (SecurityMonitor.enc_data core)) in
    {{{ `metaResp_valid` = Ob~1 ->
       ``fs_addr_in_range enclave_sig reg_fn get_field enc_data
           (derive_metadata_addr metaResp_tag (SConst line))``
    }}}.

Definition meta_resp_in_range
  (data: vect_t) (cache: mem_type) (core: ind_core_id)
  (reg_fn: reg_t -> sval)
  (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
  : fancy_spred :=
  let metaResp_tag := get_field (_sid metadata_sig) (_fld metadata_sig "tag") (SConst data) in
  let metaResp_valid := get_field (_sid metadata_sig) (_fld metadata_sig "valid") (SConst data) in
  let coreToCache_valid := (_mid ((Memory.Memory.coreToCache cache core) MemReq.valid0)) in
  let coreToCache_data := (_mid ((Memory.Memory.coreToCache cache core) MemReq.data0)) in
  let enc_data := (_smid (SecurityMonitor.enc_data core)) in
  let cache_fsm := _mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm) in
  let line_flush_idx := _mid (Memory.Memory.cache_reg cache core Memory.CacheState.line_flush_idx) in
  {{{
       `metaResp_valid` = Ob~1 ->
       {`reg_fn cache_fsm` = #(_enum cache_fsm_sig "ProcessRequest") ->
        ``fs_addr_in_range enclave_sig reg_fn get_field
                enc_data
                (derive_metadata_addr_from_push_req metaResp_tag (reg_fn coreToCache_data) get_field)``
       } /\
       {
         `reg_fn cache_fsm` = #(_enum cache_fsm_sig "FlushLineProcess") ->
         ``fs_addr_in_range enclave_sig reg_fn get_field
                enc_data
                (derive_metadata_addr metaResp_tag (reg_fn line_flush_idx))``
       }
  }}}.

(* Flushing /\ N.lt n flush_ghost *)

Definition is_flushed (cache: mem_type) (core: ind_core_id)
                      (reg_fn: reg_t -> sval) : fancy_spred :=
  let cache_fsm := _mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm) in
  let purge_reg := _mid (purge core) in
  {{{ `reg_fn purge_reg` = #(_enum purge_state "Purged") \/
      `reg_fn cache_fsm` = #(_enum cache_fsm_sig "Flushed") \/
      `reg_fn cache_fsm` = #(_enum cache_fsm_sig "FlushPrivateData")
  }}}.

Definition is_flushing (cache: mem_type) (core: ind_core_id)
                      (reg_fn: reg_t -> sval) : fancy_spred :=
  let cache_fsm := _mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm) in
  let purge_reg := _mid (purge core) in
  let line_flush_idx := _mid (Memory.Memory.cache_reg cache core Memory.CacheState.line_flush_idx) in
  {{{
      { {`reg_fn cache_fsm` = #(_enum cache_fsm_sig "FlushLineReady") \/
         `reg_fn cache_fsm` = #(_enum cache_fsm_sig "FlushLineProcess") } /\
        `reg_fn line_flush_idx` <> #(zeroes (log_nlines))
      }
  }}}.

Definition is_in_flush_state
  (cache: mem_type) (core: ind_core_id)
  (reg_fn: reg_t -> sval)
  (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
  : fancy_spred :=
  let cache_fsm := _mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm) in
  let purge_reg := _mid (purge core) in
  let line_flush_idx := _mid (Memory.Memory.cache_reg cache core Memory.CacheState.line_flush_idx) in
  {{{ ``is_flushed cache core reg_fn`` \/ ``is_flushing cache core reg_fn``
  }}}.

Definition flushing_line_eq
  (flush_line: vect_t) (cache: mem_type) (core: ind_core_id)
  (reg_fn: reg_t -> sval)
  (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
  : fancy_spred :=
  let cache_fsm := _mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm) in
  let line_flush_idx := _mid (Memory.Memory.cache_reg cache core Memory.CacheState.line_flush_idx) in
  let purge_reg := _mid (purge core) in
  {{{  {``is_flushed cache core reg_fn`` ->
        `SConst flush_line` = #(Bits.ones log_nlines)
       } /\
       {``is_flushing cache core reg_fn`` ->
        `SConst flush_line` + #(Bits.of_nat log_nlines 1) = `reg_fn line_flush_idx`
       }
  }}}.


    Definition fs_addrs_in_range_cache (cache: mem_type)
                                    (core: ind_core_id)
                                    (reg_fn: reg_t -> sval)
                                    (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                    : fancy_spred :=
      let coreToCache_data := (_mid ((Memory.coreToCache cache core) MemReq.data0)) in
      let coreToCache_valid := (_mid ((Memory.coreToCache cache core) MemReq.valid0)) in
      let toMainMem_data := (_mid ((Memory.toMainMem cache core) MemReqBypass.data0)) in
      let toMainMem_valid := (_mid ((Memory.toMainMem cache core) MemReqBypass.valid0)) in
      let mk_pred pred :=
        {{{ (* `senc_data_valid core reg_fn get_field` = Ob~1 -> *)
            `` pred ``
        }}} in
      {{{ ``mk_pred (foo_fifo_req_addrs_in_range enclave_sig reg_fn get_field
                              coreToCache_valid  coreToCache_data ((_smid (enc_data core)))) `` /\
          ``mk_pred (foo_fifo_req_addrs_in_range enclave_sig reg_fn get_field
                              toMainMem_valid  toMainMem_data ((_smid (enc_data core))))`` /\
          (* Metadata resp with core request *)
          ``mk_pred (metadata_resp_in_range_from_core cache core reg_fn get_field) `` /\
          (* Metadata resp with core request *)
          ``mk_pred (metadata_resp_in_range_from_flush cache core reg_fn get_field) ``
      }}}.

    (* Definition fs_addrs_in_range (core: ind_core_id) *)
    (*                                  (reg_fn: reg_t -> sval) *)
    (*                                  (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) *)
    (*                                  : fancy_spred := *)
    (*   let (to_imem_data, to_imem_valid) := *)
    (*     (_mid ((Memory.coreToCache imem core) MemReq.data0), (_mid ((Memory.coreToCache imem core) MemReq.valid0))) in *)
    (*   let (to_dmem_data, to_dmem_valid) := *)
    (*     (_mid ((Memory.coreToCache dmem core ) MemReq.data0), (_mid ((Memory.coreToCache dmem core) MemReq.valid0))) in *)
    (*   {{{ ``fs_addrs_in_range_cache imem core reg_fn get_field``  /\ *)
    (*       ``fs_addrs_in_range_cache dmem core reg_fn get_field`` *)
    (*   }}}. *)

  Definition cache_req_empty
    (cache: mem_type) (core: ind_core_id)
    (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    : fancy_spred :=
    let toCache_valid := _mid (cache_reg cache core (CacheState.SH_cache_req CacheReqBypass.valid0)) in
    {{{ `reg_fn toCache_valid` = Ob~0
    }}}.

  Definition meta_req_empty
    (cache: mem_type) (core: ind_core_id)
    (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    : fancy_spred :=
    let toMeta_valid := _mid (cache_reg cache core (CacheState.SH_metadata_req MetadataReqBypass.valid0)) in
    {{{ `reg_fn toMeta_valid` = Ob~0
    }}}.

  (* Definition metacache_lockstep *)
  (*   (cache: mem_type) (core: ind_core_id) *)
  (*   (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) *)
  (*   : fancy_spred := *)
  (*   let fromCache_valid := _mid (cache_reg cache core (CacheState.SH_cache_resp CacheResp.valid0)) in *)
  (*   let fromMeta_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in *)
  (*   {{{ *)
  (*         `reg_fn fromCache_valid` = `reg_fn fromMeta_valid` *)
  (*   }}}. *)
    (* Definition inv_cache_flush_only_invalidate_metadata *)
    (*   (cache: mem_type) (core: ind_core_id) *)
    (*   (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) *)
    (*   : fancy_spred := *)
    (*   let cache_fsm := reg_fn (_mid (cache_reg cache core CacheState.cache_fsm)) in *)
    (*   let toMeta_valid := reg_fn (_mid (cache_reg cache core (CacheState.SH_metadata_req MetadataReqBypass.valid0))) in *)
    (*   let toMeta_data  := reg_fn (_mid (cache_reg cache core (CacheState.SH_metadata_req MetadataReqBypass.data0))) in *)
    (*   let meta_is_write :=  get_field (_sid metadata_req_sig) (_fld metadata_req_sig "is_write") *)
    (*                             toMeta_data  in *)
    (*   let meta_data :=  get_field (_sid metadata_req_sig) (_fld metadata_req_sig "data") *)
    (*                             toMeta_data  in *)
    (*   {{{ `cache_fsm` <> #(_enum cache_fsm_sig "WaitFillResp")  -> *)
    (*       `toMeta_valid` = Ob~1 -> *)
    (*       `meta_is_write` = Ob~1 -> *)
    (*       `meta_data` = #(zeroes (_unsafe_struct_sz metadata_sig)) *)
    (*   }}}. *)

  Definition cache_invs (cache: mem_type) (core: ind_core_id)
                        (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                        : list (mem_custom_t * fancy_spred) :=
    [(Mem_cache_Flushed cache core, cache_Flushed core cache reg_fn get_field);
     (Mem_cache_FlushPrivateData cache core, cache_FlushPrivateData core cache reg_fn get_field);
     (Mem_cache_FlushLineProcess cache core, cache_FlushLineProcess core cache reg_fn get_field);
     (Mem_cache_FlushLineReady cache core, cache_FlushLineReady core cache reg_fn get_field);
     (Mem_cache_WaitFillResp cache core, cache_WaitFillResp core cache reg_fn get_field);
     (Mem_cache_SendFillReq cache core, cache_SendFillReq core cache reg_fn get_field);
     (Mem_cache_ProcessRequest cache core, cache_ProcessRequest core cache reg_fn get_field);
     (Mem_cache_Ready cache core, cache_Ready core cache reg_fn get_field);
     (Mem_cache_cacheshreq_resets cache core, cache_cacheReq_resets cache core reg_fn get_field);
     (Mem_cache_metashreq_resets cache core, cache_metaReq_resets cache core reg_fn get_field);
     (Mem_cache_single_mainmem_req cache core, single_outstanding_mainmem_req cache core reg_fn get_field);
     (* (Mem_cache_single_cache_req cache core, single_outstanding_cache_req cache core reg_fn get_field); *)
     (* (Mem_cache_single_meta_req cache core, single_outstanding_meta_req cache core reg_fn get_field); *)
     (Mem_addrs_in_range cache core, fs_addrs_in_range_cache cache core reg_fn get_field);
     (* (Mem_FlushFSM_OnlyInvalidateMetadata__Inv cache core, inv_cache_flush_only_invalidate_metadata cache core reg_fn get_field) *)
     (* Ideally, weaken this. *)
     (Mem_CacheReqAlwaysEmpty cache core, cache_req_empty cache core reg_fn get_field);
     (Mem_MetaReqAlwaysEmpty cache core, meta_req_empty cache core reg_fn get_field);
     (Mem_MetaReqAlwaysEmpty cache core, meta_req_empty cache core reg_fn get_field)

     (* (Mem_MetaCacheLockStep cache core, metacache_lockstep cache core reg_fn get_field) *)
    ].

  Definition mem_invariant (reg_fn: reg_t -> sval) get_field: list (mem_custom_t * fancy_spred) :=
    [(Mem_shreq_invalid, {{{ `get_field (_sid shreq) (_fld shreq "valid") (reg_fn (_mid SHReq))` = Ob~0 }}})
    ;(Mem_purged0, fs_reset_correct CoreId0 reg_fn get_field)
    ;(Mem_purged1, fs_reset_correct CoreId1 reg_fn get_field)
    ] ++ List.concat (map (fun '(cache,core) => cache_invs cache core reg_fn get_field)
                        [(imem, CoreId0); (dmem, CoreId0); (imem, CoreId1); (dmem, CoreId1)]).

  Definition impl_ext_cache_no_resp_core
    (core: ind_core_id) (cache_ty: mem_type)
    (ireg_fn: reg_t -> sval)
    (get_field: debug_id_ty -> debug_id_ty -> sval -> sval): fancy_spred :=
    let cache_fn := ext_cache cache_ty core in
    let toCache_valid := _mid (cache_reg cache_ty core (CacheState.SH_cache_req CacheReqBypass.valid0)) in
    let fromCache_valid := _mid (cache_reg cache_ty core (CacheState.SH_cache_resp CacheResp.valid0)) in
    {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext cache_fn)),
         `get_field (_sid cache_output_sig) (_fld cache_output_sig "get_valid")
                    (impl_ext_app (_extid cache_fn) (SBound "arg"))` = Ob~1 ->
         {`ireg_fn (_mid (cache_reg cache_ty core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "ProcessRequest")  \/
            `ireg_fn (_mid (cache_reg cache_ty core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "FlushLineProcess")      } /\
         (* `get_field (_sid cache_input_sig) (_fld cache_input_sig "get_ready") *)
         (*            ((SBound "arg"))` = Ob~1 *)
         {`ireg_fn toCache_valid` = Ob~0 /\
          `ireg_fn fromCache_valid` = Ob~0
         }
    }}}.

  Definition impl_post_ext_cache_no_resp_core
    (core: ind_core_id) (cache_ty: mem_type)
    (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    (ext_log: debug_id_ty -> sval) : fancy_spred :=
    let cache_fn := ext_cache cache_ty core in
    let toCache_valid := _mid (cache_reg cache_ty core (CacheState.SH_cache_req CacheReqBypass.valid0)) in
    let fromCache_valid := _mid (cache_reg cache_ty core (CacheState.SH_cache_resp CacheResp.valid0)) in
    let cache_put_valid := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid")
                             (ext_log (_extid (ext_cache cache_ty core))) in
    let cache_put_request := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_request")
                             (ext_log (_extid (ext_cache cache_ty core))) in
    let cache_byte_en := get_field (_sid cache_req_sig) (_fld cache_req_sig "byte_en") cache_put_request in
    {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext cache_fn)),
          `cache_put_valid` = Ob~1 ->
          `cache_byte_en` = Ob~0~0~0~0 ->
         {`reg_final (_mid (cache_reg cache_ty core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "ProcessRequest")  \/
            `reg_final (_mid (cache_reg cache_ty core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "FlushLineProcess")      } /\
         {`reg_final toCache_valid` = Ob~0 /\
          `reg_final fromCache_valid` = Ob~0
         }
    }}}.

  Definition impl_ext_meta_no_resp_core
    (core: ind_core_id) (cache_ty: mem_type)
    (ireg_fn: reg_t -> sval)
    (get_field: debug_id_ty -> debug_id_ty -> sval -> sval): fancy_spred :=
    let meta_fn := ext_metadata cache_ty core in
    let toMeta_valid := _mid (cache_reg cache_ty core (CacheState.SH_metadata_req MetadataReqBypass.valid0)) in
    let fromMeta_valid := _mid (cache_reg cache_ty core (CacheState.SH_metadata_resp MetadataResp.valid0)) in
    {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext meta_fn)),
         `get_field (_sid metadata_output_sig) (_fld metadata_output_sig "get_valid")
                    (impl_ext_app (_extid meta_fn) (SBound "arg"))` = Ob~1 ->
         {`ireg_fn (_mid (cache_reg cache_ty core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "ProcessRequest") \/
         `ireg_fn (_mid (cache_reg cache_ty core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "FlushLineProcess")
         } /\
         (* `get_field (_sid metadata_input_sig) (_fld metadata_input_sig "get_ready") *)
         (*            ((SBound "arg"))` = Ob~1 *)
         {`ireg_fn toMeta_valid` = Ob~0 /\
          `ireg_fn fromMeta_valid` = Ob~0
         }
    }}}.

  Definition impl_post_ext_meta_no_resp_core
    (core: ind_core_id) (cache_ty: mem_type)
    (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
    (ext_log: debug_id_ty -> sval) : fancy_spred :=
    let meta_fn := ext_metadata cache_ty core in
    let toMeta_valid := _mid (cache_reg cache_ty core (CacheState.SH_metadata_req MetadataReqBypass.valid0)) in
    let fromMeta_valid := _mid (cache_reg cache_ty core (CacheState.SH_metadata_resp MetadataResp.valid0)) in
    let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                           (ext_log (_extid (ext_metadata cache_ty core))) in
    let meta_put_request := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_request")
                           (ext_log (_extid (ext_metadata cache_ty core))) in
     let meta_is_write :=  get_field (_sid metadata_req_sig) (_fld metadata_req_sig "is_write")
                             meta_put_request in
    {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext meta_fn)),
          `meta_put_valid` = Ob~1 ->
          `meta_is_write` = Ob~0 ->
         {`reg_final (_mid (cache_reg cache_ty core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "ProcessRequest") \/
         `reg_final (_mid (cache_reg cache_ty core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "FlushLineProcess")
         } /\
         (* `get_field (_sid metadata_input_sig) (_fld metadata_input_sig "get_ready") *)
         (*            ((SBound "arg"))` = Ob~1 *)
         {`reg_final toMeta_valid` = Ob~0 /\
          `reg_final fromMeta_valid` = Ob~0
         }
    }}}.

  (* If get a valid response from meta, then
     - the response must be in range wrt cached line or FlushLineProcess
   *)
  Definition impl_ext_meta_resp_in_range
    (core: ind_core_id) (cache: mem_type)
    (ireg_fn: reg_t -> sval)
    (get_field: debug_id_ty -> debug_id_ty -> sval -> sval): fancy_spred :=
    let meta_fn := ext_metadata cache core in
    let coreToCache_valid := (_mid ((Memory.coreToCache cache core) MemReq.valid0)) in
    let coreToCache_data := (_mid ((Memory.coreToCache cache core) MemReq.data0)) in
    let metaResp_data :=
      get_field (_sid metadata_output_sig) (_fld metadata_output_sig "get_response")
                    (impl_ext_app (_extid meta_fn) (SBound "arg")) in
    let coreToCache_valid := (_mid ((Memory.coreToCache cache core) MemReq.valid0)) in
    let coreToCache_data := (_mid ((Memory.coreToCache cache core) MemReq.data0)) in
    let reg_enc_data := (_smid (enc_data core)) in
    let metaResp_tag := get_field (_sid metadata_sig) (_fld metadata_sig "tag") (metaResp_data) in
    let metaResp_valid := get_field (_sid metadata_sig) (_fld metadata_sig "valid") (metaResp_data) in
    let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
    let line_flush_idx := _mid (cache_reg cache core CacheState.line_flush_idx) in
    let reg_enc_data := (_smid (enc_data core)) in
    {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext meta_fn)),
         `get_field (_sid metadata_output_sig) (_fld metadata_output_sig "get_valid")
                    (impl_ext_app (_extid meta_fn) (SBound "arg"))` = Ob~1 ->
         `metaResp_valid` = Ob~1 ->
          {`ireg_fn cache_fsm` = #(_enum cache_fsm_sig "ProcessRequest") ->
           ``fs_addr_in_range enclave_sig ireg_fn get_field reg_enc_data
             (derive_metadata_addr_from_push_req metaResp_tag (ireg_fn coreToCache_data) get_field) ``
          } /\
          {`ireg_fn cache_fsm` = #(_enum cache_fsm_sig "FlushLineProcess") ->
           ``fs_addr_in_range enclave_sig ireg_fn get_field reg_enc_data
             (derive_metadata_addr metaResp_tag (ireg_fn line_flush_idx)) ``
          }
    }}}.

  (* If push a response to meta, then
     - the resp must be in range wrt the req addr, which is also where it's stored
     - then as long as we have the invariant that the req addr corresponds to the lines...
   *)
    Definition impl_post_ext_meta_req_in_range
      (cache: mem_type) (core: ind_core_id)
      (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let meta_fn := ext_metadata cache core in
      let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                           (ext_log (_extid (ext_metadata cache core))) in
      let meta_put_request := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_request")
                           (ext_log (_extid (ext_metadata cache core))) in
      let meta_is_write :=  get_field (_sid metadata_req_sig) (_fld metadata_req_sig "is_write")
                             meta_put_request in
      let metaReq_data := get_field (_sid metadata_req_sig) (_fld metadata_req_sig "data")
                                     meta_put_request in
      let metaReq_addr := get_field (_sid metadata_req_sig) (_fld metadata_req_sig "addr")
                                     meta_put_request in
      let metaReq_tag := get_field (_sid metadata_sig) (_fld metadata_sig "tag") (metaReq_data) in
      let metaReq_valid := get_field (_sid metadata_sig) (_fld metadata_sig "valid") (metaReq_data) in
      let reg_enc_data := (_smid (enc_data core)) in
      {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext meta_fn)),
          `meta_put_valid` = Ob~1 ->
          `meta_is_write` = Ob~1 ->
          `metaReq_valid` = Ob~1 ->
          (* assert cache fsm *)
          ``fs_addr_in_range enclave_sig reg_final get_field reg_enc_data
                            (derive_metadata_addr metaReq_tag metaReq_addr)``
      }}}.

  Definition mem_type_to_bit (ty: mem_type) : vect_t :=
    match ty with
    | imem => Ob~1
    | dmem => Ob~0
    end.
    Definition fs_req_in_fifo (req: sval) (reg_fn: reg_t -> sval) (reg_data: reg_t) (reg_valid: reg_t) : fancy_spred :=
      {{{ `reg_fn reg_valid` = Ob~1 /\
          `req` = `reg_fn reg_data`
      }}}.
    Definition addr_eq_derive_from_metadata (addr: sval) (metadata: sval) (req: sval)
                                            (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                            : fancy_spred :=
      let push_req_addr push_req :=
          get_field (_sid mem_req) (_fld mem_req "addr") push_req in
      {{{ `addr` =  (`get_field (_sid metadata_sig) (_fld metadata_sig "tag") metadata` ++
                     (`push_req_addr req` [2 : log_nlines]) ++
                     Ob~0~0)
      }}}.

  (* Definition post_case_toMainMem (cache: mem_type) (core: ind_core_id) *)
  (*                                (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) *)
  (*                                : fancy_spred := *)
  (*   let toMainMem_valid := _mid (cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0)) in *)
  (*   let toMainMem_data := _mid (cache_reg cache core (CacheState.toMainMem MemReqBypass.data0)) in *)
  (*   let coreToCache_data := _mid (Memory.coreToCache cache core MemReq.data0) in *)
  (*   let coreToCache_valid := _mid (Memory.coreToCache cache core MemReq.valid0) in *)
  (*   let push_req_addr push_req := *)
  (*         get_field (_sid mem_req) (_fld mem_req "addr") push_req in *)
  (*  let metaResp_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in *)
  (*  let metaResp_data  := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.data0)) in *)
  (*  let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in *)
  (*  let line_flush_idx := _mid (cache_reg cache core CacheState.line_flush_idx) in *)
  (*   {{{  `reg_final toMainMem_valid` = Ob~0 \/ *)
  (*        ``fs_req_in_fifo (reg_final toMainMem_data) reg_init toMainMem_data toMainMem_valid`` \/ *)
  (*        { `push_req_addr (reg_final toMainMem_data)` = `push_req_addr (reg_init coreToCache_data)` /\ *)
  (*          `reg_init coreToCache_valid` = Ob~1 *)
  (*        } \/ *)
  (*        { `reg_init coreToCache_valid` = Ob~1 /\ *)
  (*          `reg_init (metaResp_valid)` = Ob~1 /\ *)
  (*          `get_field (_sid metadata_sig) (_fld metadata_sig "valid") (reg_init metaResp_data)` = Ob~1 /\ *)
  (*           `` addr_eq_derive_from_metadata (push_req_addr (reg_final toMainMem_data)) (reg_init (metaResp_data)) *)
  (*                                           (reg_init (coreToCache_data)) get_field `` *)
  (*        } \/ *)
  (*        { `reg_init ((cache_fsm ))` = #(_enum cache_fsm_sig "FlushLineProcess") /\ *)
  (*           `get_field (_sid metadata_sig) (_fld metadata_sig "valid") (reg_init metaResp_data)` = Ob~1 /\ *)
  (*           `push_req_addr (reg_final toMainMem_data) ` = *)
  (*             (`get_field (_sid metadata_sig) (_fld metadata_sig "tag") (reg_init metaResp_data)` ++ *)
  (*             `reg_init line_flush_idx` ++ *)
  (*             Ob~0~0) *)
  (*         } *)
  (*   }}}. *)
  Definition impl_ext_mem_correct_core
    (core: ind_core_id) (ireg_fn: reg_t -> sval)
    (get_field: debug_id_ty -> debug_id_ty -> sval -> sval): fancy_spred :=
    let (core_bit, turn_bits) := match core with
                                 | CoreId0 => (Ob~0, mem_core0_read_turn)
                                 | CoreId1 => (Ob~1, mem_core1_read_turn)
                                 end in
    let toMainMem_valid cache := cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0) in
    let fromMainMem_valid cache := cache_reg cache core (CacheState.fromMainMem MemResp.valid0) in
     {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext ext_mainmem)),
         `get_field (_sid mem_output) (_fld mem_output "get_valid")
                    (impl_ext_app (_extid ext_mainmem) (SBound "arg"))` = Ob~1 ->
          { {`ireg_fn (_mid Memory.turn)` = #mem_core0_read_turn \/
             `ireg_fn (_mid Memory.turn)` = #mem_core1_read_turn
            } /\
           {`ireg_fn (_mid Memory.turn)` = #turn_bits ->
            {
            `get_field (_sid Memory.shreq) (_fld Memory.shreq "sourceCore") (ireg_fn (_mid Memory.SHReq))` = #core_bit /\
            { `get_field (_sid Memory.shreq) (_fld Memory.shreq "sourceType") (ireg_fn (_mid Memory.SHReq))` = #(mem_type_to_bit imem) ->
             { `ireg_fn (_mid (cache_reg imem core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "WaitFillResp") /\
              `ireg_fn (_mid (toMainMem_valid imem))` = Ob~0 /\
              `ireg_fn (_mid (fromMainMem_valid imem))` = Ob~0
             }
            } /\
            { `get_field (_sid Memory.shreq) (_fld Memory.shreq "sourceType") (ireg_fn (_mid Memory.SHReq))` = #(mem_type_to_bit dmem) ->
             { `ireg_fn (_mid (cache_reg dmem core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "WaitFillResp") /\
              `ireg_fn (_mid (toMainMem_valid dmem))` = Ob~0 /\
              `ireg_fn (_mid (fromMainMem_valid dmem))` = Ob~0 } }
            }
           }
          }
     }}}.

  Definition impl_post_ext_mem_correct_core
    (core: ind_core_id) (ifinal_fn: reg_t -> sval) iget_field (iext_log: debug_id_ty -> sval): fancy_spred :=
    let (core_bit, turn_bits) := match core with
                                 | CoreId0 => (Ob~0, mem_core0_read_turn)
                                 | CoreId1 => (Ob~1, mem_core1_read_turn)
                                 end in
    let toMainMem_valid cache := cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0) in
    let fromMainMem_valid cache := cache_reg cache core (CacheState.fromMainMem MemResp.valid0) in
    let push_req_valid := iget_field (_sid mem_input) (_fld mem_input "put_valid")
                                                  (iext_log (_extid ext_mainmem)) in
    let push_req := iget_field (_sid mem_input) (_fld mem_input "put_request")
                                                  (iext_log (_extid ext_mainmem)) in
    let byte_en := iget_field (_sid mem_req) (_fld mem_req "byte_en") push_req in
    {{{ `push_req_valid` = Ob~1 ->
        `ifinal_fn (_mid Memory.turn)` = #turn_bits ->
        `byte_en` = Ob~0~0~0~0 ->
        `iget_field (_sid Memory.shreq) (_fld Memory.shreq "sourceCore") (ifinal_fn (_mid Memory.SHReq))` = #core_bit /\
        { `iget_field (_sid Memory.shreq) (_fld Memory.shreq "sourceType") (ifinal_fn (_mid Memory.SHReq))` = #(mem_type_to_bit imem) ->
         { `ifinal_fn (_mid (cache_reg imem core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "WaitFillResp") /\
           `ifinal_fn (_mid (toMainMem_valid imem))` = Ob~0 /\
           `ifinal_fn (_mid (fromMainMem_valid imem))` = Ob~0
         }
        } /\
        { `iget_field (_sid Memory.shreq) (_fld Memory.shreq "sourceType") (ifinal_fn (_mid Memory.SHReq))` = #(mem_type_to_bit dmem) ->
          { `ifinal_fn (_mid (cache_reg dmem core CacheState.cache_fsm))` = #(_enum cache_fsm_sig "WaitFillResp") /\
            `ifinal_fn (_mid (toMainMem_valid dmem))` = Ob~0 /\
            `ifinal_fn (_mid (fromMainMem_valid dmem))` = Ob~0
          }
        }
    }}}.

  (* TODO *)
  Definition impl_post_main_mem_put_is_read_turn
    (ifinal_fn: reg_t -> sval) iget_field (iext_log: debug_id_ty -> sval): fancy_spred :=
    {{{ `iget_field (_sid mem_input) (_fld mem_input "put_valid") (iext_log (_extid ext_mainmem))` = Ob~1 ->
        { `ifinal_fn (_mid Memory.turn)` = #(mem_core0_read_turn)  \/
          `ifinal_fn (_mid Memory.turn)` = #(mem_core1_read_turn)
        }
    }}}.


  (* TODO *)
  (* Inv: initial enq is always empty;
     - post cond: put_valid=put_ready unless (get_ready=false /\ cache is full; but this should never happen )
if put_valid then get_ready is true
     - also pre_cond: put_ready = put_valid
   *)
  (* TODO: get_ready *)
  Definition mem_cache_put_ready (cache: mem_type) (core: ind_core_id) (ireg_fn: reg_t -> sval)
                                 (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) : fancy_spred :=
    let cache_fn := ext_cache cache  core in
    {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext cache_fn)),
         `get_field (_sid cache_output_sig) (_fld cache_output_sig "put_ready")
                    (impl_ext_app (_extid cache_fn) (SBound "arg"))` = Ob~1 \/
         `get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid")
                    (SBound "arg")` = Ob~0 \/
         `get_field (_sid cache_input_sig) (_fld cache_input_sig "get_ready")
                    (SBound "arg")` = Ob~0
    }}}.
  Definition mem_meta_put_ready (cache: mem_type) (core: ind_core_id) (ireg_fn: reg_t -> sval)
                                 (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) : fancy_spred :=
    let meta_fn := ext_metadata cache  core in
    {{{ forall1 "arg" of (unsafe_get_ext_fn_arg_type (_ext meta_fn)),
         `get_field (_sid metadata_output_sig) (_fld metadata_output_sig "put_ready")
                    (impl_ext_app (_extid meta_fn) (SBound "arg"))` = Ob~1 \/
         `get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                    (SBound "arg")` = Ob~0 \/
         `get_field (_sid metadata_input_sig) (_fld metadata_input_sig "get_ready")
                    (SBound "arg")` = Ob~0
    }}}.

  (* Definition metacache_resp_lock_step *)
  (*   (cache: mem_type) (core: ind_core_id) (ireg_fn: reg_t -> sval) *)
  (*   (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) : fancy_spred := *)
  (*   let meta_fn := ext_metadata cache  core in *)
  (*   let cache_fn := ext_cache cache  core in *)
  (*   {{{ forall2 "meta_arg" of (unsafe_get_ext_fn_arg_type (_ext meta_fn)) and *)
  (*               "cache_arg" of (unsafe_get_ext_fn_arg_type (_ext cache_fn)), *)
  (*        `get_field (_sid metadata_input_sig) (_fld metadata_input_sig "get_ready") *)
  (*                   (SBound "meta_arg")` = *)
  (*        `get_field (_sid cache_input_sig) (_fld cache_input_sig "get_ready") *)
  (*                   (SBound "cache_arg")` *)
  (*         -> *)
  (*        `get_field (_sid metadata_output_sig) (_fld metadata_output_sig "get_valid") *)
  (*                   (impl_ext_app (_extid meta_fn) (SBound "meta_arg"))` = *)
  (*        `get_field (_sid cache_output_sig) (_fld cache_output_sig "get_valid") *)
  (*                   (impl_ext_app (_extid cache_fn) (SBound "cache_arg"))` *)
  (*   }}}. *)

    Definition cache_pre_conds' cache core (reg_init : reg_t -> sval) get_field : list (mem_custom_t * fancy_spred) :=
      [(MemCacheNoResp cache core, impl_ext_cache_no_resp_core core cache reg_init get_field)
      ;(MemMetaNoResp cache core, impl_ext_meta_no_resp_core core cache reg_init get_field);
       (MemMetaRespInRange cache core, impl_ext_meta_resp_in_range core cache reg_init get_field);
       (Mem_CachePutReady cache core, mem_cache_put_ready cache core reg_init get_field);
       (Mem_MetaPutReady cache core, mem_meta_put_ready cache core reg_init get_field)
       (* (Mem_ExtRespLockStep cache core, metacache_resp_lock_step cache core reg_init get_field) *)
      ].

    Definition mem_pre_conds' core (reg_init : reg_t -> sval) get_field : list (mem_custom_t * fancy_spred) :=
        [(MemImplExtCorrectCore CoreId0, impl_ext_mem_correct_core CoreId0 reg_init get_field)
        ;(MemImplExtCorrectCore CoreId1, impl_ext_mem_correct_core CoreId1 reg_init get_field)
        ] ++ List.concat (map (fun '(cache,core) => cache_pre_conds' cache core reg_init get_field)
                            [(imem, core); (dmem, core)]).
    Definition mem_pre_conds (reg_init: reg_t -> sval) get_field : list (mem_custom_t * fancy_spred) :=
       (mem_pre_conds' CoreId0 reg_init get_field) ++ (mem_pre_conds' CoreId1 reg_init get_field) ++
         (mem_invariant reg_init get_field).

    Definition almost_zeroed_mainmem_call : list bool := Eval vm_compute in (
      success_or_default (let/res s := _lookup_struct mem_input in
                          subst_field s.(dstruct_fields) (_fld mem_input "get_ready")
                                          (zeroes (Types.struct_sz mem_input)) Ob~1) []).
      (* TODO! Bypass FIFO...
         -  Push req to mainmem is either
            1) toMainMem
            2) SH_meta_resp tag ++ index (and SH_meta_resp is either cur addr or from ext metadata)
            3) coreToCache addr
         - Invariant that all these addresses are in configuration
       *)
      (* Definition rederive_addr (metadata: sval) (req_addr: sval) *)
      (*                          (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) *)
      (*                          : sval := *)
      (*   {{ `get_field (_sid metadata_sig) (_fld metadata_sig "tag") metadata` ++ *)
      (*       Ob~0 ++ *)
      (*       Ob~0~0 *)
      (*   }}. *)

      Definition fs_mem_push_addrs
        (core: ind_core_id) (cache: mem_type) (reg_init: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
        (push_req: sval) :=
        let reg_priv_turn := _mid (Memory.priv_turn core) in
        let push_req_addr push_req :=
            get_field (_sid mem_req) (_fld mem_req "addr") push_req in
        let toMainMem_valid := _mid (Memory.cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0)) in
        let toMainMem_data := _mid (Memory.cache_reg cache core (CacheState.toMainMem MemReqBypass.data0)) in
        let coreToCache_valid := _mid (Memory.coreToCache cache core MemReq.valid0) in
        let coreToCache_data := _mid (Memory.coreToCache cache core MemReq.data0) in
        let metaResp_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in
        let metaResp_data  := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.data0)) in
        let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
        let line_flush_idx := _mid (cache_reg cache core CacheState.line_flush_idx) in
        {{{ `reg_init reg_priv_turn` = #(mem_type_to_bit cache) ->
            ``fs_req_in_fifo push_req reg_init ((toMainMem_data )) ((toMainMem_valid ))`` \/
            `push_req_addr push_req` = `push_req_addr (reg_init ((coreToCache_data)))` \/
            { `reg_init (metaResp_valid)` = Ob~1 /\
              `reg_init (coreToCache_valid)` = Ob~1 /\
              `get_field (_sid metadata_sig) (_fld metadata_sig "valid") (reg_init metaResp_data)` = Ob~1 /\
              ``addr_eq_derive_from_metadata (push_req_addr push_req) (reg_init (metaResp_data))
                                              (reg_init (coreToCache_data)) get_field ``
            } \/
            { `reg_init ((cache_fsm ))` = #(_enum cache_fsm_sig "FlushLineProcess") /\
              `get_field (_sid metadata_sig) (_fld metadata_sig "valid") (reg_init metaResp_data)` = Ob~1 /\
              `push_req_addr push_req` = (`get_field (_sid metadata_sig) (_fld metadata_sig "tag") (reg_init metaResp_data)` ++
                                          `reg_init line_flush_idx` ++
                                          Ob~0~0)
            }
        }}}.
    Definition push_req_in_config (core: ind_core_id)
                                  (reg_init: reg_t  -> sval)
                                  (ext_log: debug_id_ty -> sval)
                                  (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                                  : fancy_spred :=
      let push_req_valid := get_field (_sid mem_input) (_fld mem_input "put_valid")
                                                  (ext_log (_extid ext_mainmem)) in
      let req := get_field (_sid mem_input) (_fld mem_input "put_request")
                            (ext_log (_extid ext_mainmem)) in
      let reg_enclave := ((_smid (enc_data core))) in
      let push_req_addr := get_field (_sid mem_req) (_fld mem_req "addr") req in
      {{{ `push_req_valid` = Ob~1 ->
          `reg_init (_mid Memory.turn)` = #(mem_core_write_turn core) ->
          ``fs_addr_in_range enclave_sig reg_init get_field reg_enclave push_req_addr ``
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
        let push_req_addr :=
            get_field (_sid mem_req) (_fld mem_req "addr") push_req in
        let toMainMem_valid cache := Memory.cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0) in
        let toMainMem_data cache := Memory.cache_reg cache core (CacheState.toMainMem MemReqBypass.data0) in
        let cache_fsm cache := cache_reg cache core CacheState.cache_fsm in
        let mk_pred pred :=
        {{{ `reg_init (_mid Memory.turn)` = #(PfHelpers.mem_core_write_turn core) ->
            `get_field (_sid mem_input) (_fld mem_input "put_valid") (ext_log (_extid ext_mainmem))` = Ob~1 ->
            `` pred ``
        }}} in
        {{{ ``mk_pred (fs_mem_push_addrs core imem reg_init get_field push_req) `` /\
            ``mk_pred (fs_mem_push_addrs core dmem reg_init get_field push_req) ``
        }}}.
    Definition fifo_no_enq  (reg_data reg_valid: reg_t)
                            (reg_init reg_final: reg_t -> sval)
                             : fancy_spred :=
      {{{ `reg_final reg_valid` = Ob~1 ->
          `reg_final reg_data` = `reg_init reg_data`
          (* `reg_final reg_valid` = Ob~1 /\ *)
          (* `reg_final reg_data` = `reg_init reg_data` *)
      }}}.

    (* Definition mem_post_Ready (cache: mem_type) (core: ind_core_id) *)
    (*                           (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) *)
    (*                           : fancy_spred := *)
    (*   let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in *)
    (*   let toMainMem_data := _mid (cache_reg cache core (CacheState.toMainMem MemReqBypass.data0) )in *)
    (*   let toMainMem_valid := _mid (cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0)) in *)
    (*   let mk_pred pred := *)
    (*     {{{ `reg_init (cache_fsm)` = #(_enum cache_fsm_sig "Ready") -> *)
    (*         `` pred `` *)
    (*     }}} in *)
    (*   {{{ ``mk_pred {{{ `reg_final (cache_fsm)` = #(_enum cache_fsm_sig "ProcessRequest" ) \/ *)
    (*                     `reg_final (cache_fsm)` = #(_enum cache_fsm_sig "FlushLineReady" ) \/ *)
    (*                     `reg_final (cache_fsm)` = #(_enum cache_fsm_sig "Ready" ) *)
    (*                 }}} `` /\ *)
    (*       ``mk_pred (fifo_no_enq toMainMem_data toMainMem_valid reg_init reg_final)`` *)
    (*   }}}. *)
    (* Definition mem_post_FlushLineReady (cache: mem_type) (core: ind_core_id) *)
    (*                           (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) *)
    (*                           : fancy_spred := *)
    (*   let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in *)
    (*   let toMainMem_data := _mid (cache_reg cache core (CacheState.toMainMem MemReqBypass.data0) )in *)
    (*   let toMainMem_valid := _mid (cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0)) in *)
    (*   {{{ `reg_init cache_fsm` = #(_enum cache_fsm_sig "FlushLineReady") -> *)
    (*       `` fifo_no_enq toMainMem_data toMainMem_valid reg_init reg_final `` *)
    (*   }}}. *)

    (* Increment line, invalidate metadata or metadata already invalid *)
    Definition mem_post_FlushLineProcess
      (cache: mem_type) (core: ind_core_id)
      (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
      let fromMeta_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in
      let line_flush_idx := _mid (cache_reg cache core CacheState.line_flush_idx) in
      let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                             (ext_log (_extid (ext_metadata cache core))) in
      let meta_put_request := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_request")
                             (ext_log (_extid (ext_metadata cache core))) in
      let meta_is_write :=  get_field (_sid metadata_req_sig) (_fld metadata_req_sig "is_write")
                             meta_put_request in
      let meta_data := get_field (_sid metadata_req_sig) (_fld metadata_req_sig "data")
                             meta_put_request in
      let meta_line := get_field (_sid metadata_req_sig) (_fld metadata_req_sig "addr")
                             meta_put_request in
      let fromMeta_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in
      let fromMeta_data := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.data0)) in
      let fromMeta_data_valid :=
        get_field (_sid metadata_sig) (_fld metadata_sig "valid") (reg_init fromMeta_data) in
      let cache_put_valid := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid")
                             (ext_log (_extid (ext_cache cache core))) in
      let cache_put_request := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_request")
                             (ext_log (_extid (ext_cache cache core))) in
      let cache_byte_en := get_field (_sid cache_req_sig) (_fld cache_req_sig "byte_en") cache_put_request in
      let cache_line := get_field (_sid cache_req_sig) (_fld cache_req_sig "addr") cache_put_request in
      let cache_data := get_field (_sid cache_req_sig) (_fld cache_req_sig "data") cache_put_request in
      let cache_get_ready := get_field (_sid cache_input_sig) (_fld cache_input_sig "get_ready")
                                 (ext_log (_extid (ext_cache cache core))) in
      let meta_get_ready := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "get_ready")
                                 (ext_log (_extid (ext_metadata cache core))) in
      {{{ `reg_init cache_fsm` = #(_enum cache_fsm_sig "FlushLineProcess") ->
          `reg_final cache_fsm` <> `reg_init cache_fsm` ->
          { `reg_final line_flush_idx` = `reg_init line_flush_idx` + #(Bits.of_nat log_nlines 1) /\
           { {`meta_put_valid` = Ob~1
              /\ `meta_is_write` = Ob~1
              /\ `meta_data` = #(zeroes (_unsafe_struct_sz metadata_sig))
              /\ `meta_line` = `reg_init line_flush_idx`
              /\ `meta_get_ready` = Ob~1
              /\ `cache_put_valid` = Ob~1
              /\ `cache_byte_en` = Ob~1~1~1~1
              /\ `cache_data` = #(Bits.zeroes 32)
              /\ `cache_get_ready` = Ob~1
              /\ `cache_line` = `reg_init line_flush_idx`
             }
             (* { `reg_init fromMeta_valid` = Ob~1 /\ `fromMeta_data_valid` = Ob~0 } *)
            }
          }
          (* ``fifo_no_enq toMainMem_data toMainMem_valid reg_init reg_final `` *)
      }}}.

    (* Definition mem_post_FlushPrivateData *)
    (*     (cache: mem_type) (core: ind_core_id) *)
    (*     (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) *)
    (*     : fancy_spred := *)
    (*   let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in *)
    (*   let toMainMem_data := _mid (cache_reg cache core (CacheState.toMainMem MemReqBypass.data0) )in *)
    (*   let toMainMem_valid := _mid (cache_reg cache core (CacheState.toMainMem MemReqBypass.valid0)) in *)
    (*   {{{ `reg_init cache_fsm` = #(_enum cache_fsm_sig "FlushPrivateData") -> *)
    (*       `` fifo_no_enq toMainMem_data toMainMem_valid reg_init reg_final `` *)
    (*   }}}. *)


(* _get_field cache_input_sig "put_valid" (obs_cache (get_mem_observations (Log__ext log)) cache core) = *)
(*   Success Ob~1 -> *)
(*   _get_field cache_input_sig "get_ready" (obs_cache (get_mem_observations (Log__ext log)) cache core) = *)
(*   Success Ob~1 *)
    Definition cache_obs_put_valid_impl_get_ready__ext
      (cache: mem_type) (core: ind_core_id)
      (reg_final: reg_t -> sval)
      (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let put_valid := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid")
                                 (ext_log (_extid (ext_cache cache core))) in
      let get_ready := get_field (_sid cache_input_sig) (_fld cache_input_sig "get_ready")
                                 (ext_log (_extid (ext_cache cache core))) in
      let fromCache_valid := _mid (cache_reg cache core (CacheState.SH_cache_resp CacheResp.valid0)) in
      {{{ `put_valid` = Ob~1 ->
          { `get_ready` = Ob~1  /\ `reg_final (fromCache_valid)` = Ob~0  }
      }}}.

    Definition cache_obs_get_ready_implied
      (cache: mem_type) (core: ind_core_id)
      (reg_init: reg_t -> sval)
      (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let get_ready := get_field (_sid cache_input_sig) (_fld cache_input_sig "get_ready")
                                 (ext_log (_extid (ext_cache cache core))) in
      let fromCache_valid := _mid (cache_reg cache core (CacheState.SH_cache_resp CacheResp.valid0)) in
      {{{ `reg_init (fromCache_valid)` = Ob~0  ->
          `get_ready` = Ob~1
      }}}.

    Definition meta_obs_put_valid_impl_get_ready__ext
      (cache: mem_type) (core: ind_core_id)
      (reg_final: reg_t -> sval)
      (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                                 (ext_log (_extid (ext_metadata cache core))) in
      let get_ready := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "get_ready")
                                 (ext_log (_extid (ext_metadata cache core))) in
      let fromMeta_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in
      {{{ `put_valid` = Ob~1 ->
          { `get_ready` = Ob~1  /\ `reg_final (fromMeta_valid)` = Ob~0  }
      }}}.


    Definition meta_obs_get_ready_implied
      (cache: mem_type) (core: ind_core_id)
      (reg_init: reg_t -> sval)
      (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let get_ready := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "get_ready")
                                 (ext_log (_extid (ext_metadata cache core))) in
      let fromMeta_valid := _mid (cache_reg cache core (CacheState.SH_metadata_resp MetadataResp.valid0)) in
      {{{ `reg_init (fromMeta_valid)` = Ob~0  ->
          `get_ready` = Ob~1
      }}}.

(* TODO *)
  (* forall line tag : vect_t, *)
  (* get_metadata_valid_write_line_and_tag (obs_meta (get_mem_observations (Log__ext log)) cache core) = *)
  (* Success (line, tag) -> *)
  (* get_cache_valid_write_to_line (obs_cache (get_mem_observations (Log__ext log)) cache core) = Success line *)
(* Definition metacache_same_line *)
(*       (cache: mem_type) (core: ind_core_id) *)
(*       (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) *)
(*       (ext_log: debug_id_ty -> sval) *)
(*       : fancy_spred := *)
(*   let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid") *)
(*                              (ext_log (_extid (ext_metadata cache core))) in *)
(*   let meta_put_request := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_request") *)
(*                              (ext_log (_extid (ext_metadata cache core))) in *)
(*   let meta_is_write :=  get_field (_sid metadata_req_sig) (_fld metadata_req_sig "put_request") *)
(*                              meta_put_request in *)
(*   let meta_data := get_field (_sid metadata_req_sig) (_fld metadata_req_sig "data") *)
(*                              meta_put_request in *)
(*   let meta_line := get_field (_sid metadata_req_sig) (_fld metadata_req_sig "addr") *)
(*                              meta_put_request in *)
(*   let meta_data_valid :=  get_field (_sid metadata_sig) (_fld metadata_sig "valid") *)
(*                              meta_data in *)
(*   let cache_put_valid := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid") *)
(*                              (ext_log (_extid (ext_cache cache core))) in *)
(*   let cache_get_ready := get_field (_sid cache_input_sig) (_fld cache_input_sig "get_ready") *)
(*                              (ext_log (_extid (ext_cache cache core))) in *)
(*   let cache_put_request := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_request") *)
(*                              (ext_log (_extid (ext_cache cache core))) in *)
(*   let cache_line := get_field (_sid cache_req_sig) (_fld cache_req_sig "addr") cache_put_request in *)
(*   let cache_byte_en := get_field (_sid cache_req_sig) (_fld cache_req_sig "byte_en") cache_put_request in *)
(*   {{{ `meta_put_valid` = Ob~1 -> *)
(*       `meta_is_write` = Ob~1 -> *)
(*       `meta_data_valid` = Ob~1 -> *)
(*       `cache_put_valid` = Ob~1 *)
(*       /\ `cache_get_ready` = Ob~1 *)
(*       /\ `cache_byte_en` = Ob~1~1~1~1 *)
(*       /\ `meta_line` = `cache_line` *)
(*   }}}. *)

(* If cache load, addr must be equal *)
(* TODO!!! *)
Definition valid_meta_addr (cache: mem_type) (core: ind_core_id)
                            (reg_init reg_final: reg_t -> sval)
                            (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                            (ext_log: debug_id_ty -> sval)
                            : fancy_spred :=
  let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                             (ext_log (_extid (ext_metadata cache core))) in
  let meta_put_request := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_request")
                             (ext_log (_extid (ext_metadata cache core))) in
  let meta_is_write := get_field (_sid metadata_req_sig) (_fld metadata_req_sig "is_write") meta_put_request in
  let meta_line := get_field (_sid metadata_req_sig) (_fld metadata_req_sig "addr") meta_put_request in
  let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
  let line_flush_idx := _mid (cache_reg cache core CacheState.line_flush_idx) in
  let coreToCache_data := (_mid ((Memory.coreToCache cache core) MemReq.data0)) in
  let coreToCache_valid := (_mid ((Memory.coreToCache cache core) MemReq.valid0)) in
  let coreToCache_addr := get_field (_sid mem_req) (_fld mem_req "addr") (reg_final coreToCache_data) in

  {{{ `meta_put_valid` = Ob~1 ->
      `meta_is_write` = Ob~0 ->
      (* FlushLineReady \/ Process Request *)
      { { `reg_final (cache_fsm)` = #(_enum cache_fsm_sig "FlushLineProcess") /\
          `reg_final (line_flush_idx)` = `meta_line`
        } \/
        { `reg_final (cache_fsm)` = #(_enum cache_fsm_sig "ProcessRequest") /\
          `reg_final (coreToCache_valid)` = Ob~1 /\
          `coreToCache_addr` [2:log_nlines] = `meta_line`
        }
      }
  }}}.

    Definition cache_post_invert_FlushLineReady
      (cache: mem_type) (core: ind_core_id)
      (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
      let line_flush_idx := _mid (cache_reg cache core CacheState.line_flush_idx) in
      let cache_put_valid := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid")
                             (ext_log (_extid (ext_cache cache core))) in
      let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                           (ext_log (_extid (ext_metadata cache core))) in
      let purge_reg := _mid (purge core) in
      {{{ `reg_final cache_fsm` = #(_enum cache_fsm_sig "FlushLineReady") ->
          `reg_init purge_reg` <> #(_enum purge_state "Purged") /\
          {
          {`reg_init cache_fsm` = #(_enum cache_fsm_sig "FlushLineReady") /\
           `reg_init line_flush_idx` = `reg_final line_flush_idx` /\
           `cache_put_valid` = Ob~0 /\
           `meta_put_valid` = Ob~0
          } \/
          `reg_init cache_fsm` = #(_enum cache_fsm_sig "FlushLineProcess") \/
          {`reg_init cache_fsm` = #(_enum cache_fsm_sig "Ready") /\
           `reg_final line_flush_idx` = #(Bits.zeroes log_nlines) /\
           `cache_put_valid` = Ob~0 /\
           `meta_put_valid` = Ob~0

          }
          }
      }}}.

    Definition cache_post_invert_FlushLineProcess
      (cache: mem_type) (core: ind_core_id)
      (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
      let line_flush_idx := _mid (cache_reg cache core CacheState.line_flush_idx) in
      let cache_put_valid := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid")
                             (ext_log (_extid (ext_cache cache core))) in
      let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                           (ext_log (_extid (ext_metadata cache core))) in
      let purge_reg := _mid (purge core) in
      let meta_put_request := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_request")
                           (ext_log (_extid (ext_metadata cache core))) in
      let meta_is_write :=  get_field (_sid metadata_req_sig) (_fld metadata_req_sig "is_write")
                             meta_put_request in
      let cache_put_request := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_request")
                                 (ext_log (_extid (ext_cache cache core))) in
      let cache_byte_en := get_field (_sid cache_req_sig) (_fld cache_req_sig "byte_en") cache_put_request in
      let cache_get_ready := get_field (_sid cache_input_sig) (_fld cache_input_sig "get_ready")
                                 (ext_log (_extid (ext_cache cache core))) in
      let meta_get_ready := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "get_ready")
                                 (ext_log (_extid (ext_metadata cache core))) in
      {{{ `reg_final cache_fsm` = #(_enum cache_fsm_sig "FlushLineProcess") ->
          `reg_init purge_reg` <> #(_enum purge_state "Purged") /\
           {
          {`reg_init cache_fsm` = #(_enum cache_fsm_sig "FlushLineProcess")  /\
           `reg_init line_flush_idx` = `reg_final line_flush_idx` /\
           `cache_put_valid` = Ob~0 /\
           `meta_put_valid` = Ob~0
          } \/
          {`reg_init cache_fsm` = #(_enum cache_fsm_sig "FlushLineReady") /\
           `reg_init line_flush_idx` = `reg_final line_flush_idx` /\
           `cache_byte_en` = Ob~0~0~0~0 /\
           `meta_is_write` = Ob~0 /\
           `cache_get_ready` = Ob~1 /\
           `meta_get_ready` = Ob~1
          }
          }
      }}}.

    Definition cache_post_invert_FlushPrivateData
      (cache: mem_type) (core: ind_core_id)
      (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
      let line_flush_idx := _mid (cache_reg cache core CacheState.line_flush_idx) in
      let cache_put_valid := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid")
                             (ext_log (_extid (ext_cache cache core))) in
      let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                           (ext_log (_extid (ext_metadata cache core))) in
      let purge_reg := _mid (purge core) in
      {{{ `reg_final cache_fsm` = #(_enum cache_fsm_sig "FlushPrivateData") ->
          `reg_init purge_reg` <> #(_enum purge_state "Purged") /\
          { `reg_init cache_fsm` = #(_enum cache_fsm_sig "FlushPrivateData") /\
            `cache_put_valid` = Ob~0 /\
            `meta_put_valid` = Ob~0
          } \/
          { `reg_init cache_fsm` = #(_enum cache_fsm_sig "FlushLineProcess") /\
            `reg_init line_flush_idx` = #(Bits.ones log_nlines)
            (* put zero to metadata at line ones *)
            (* put zero to cache at line ones *)
            (* get_ready = Ob~1 *)
          }
      }}}.

    Definition cache_post_invert_Flushed
      (cache: mem_type) (core: ind_core_id)
      (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
      let cache_put_valid := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid")
                             (ext_log (_extid (ext_cache cache core))) in
      let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                           (ext_log (_extid (ext_metadata cache core))) in
      let purge_reg := _mid (purge core) in
      {{{ `reg_final cache_fsm` = #(_enum cache_fsm_sig "Flushed") ->
          `reg_init purge_reg` <> #(_enum purge_state "Purged") /\
          {`reg_init cache_fsm` = #(_enum cache_fsm_sig "Flushed") \/
           `reg_init cache_fsm` = #(_enum cache_fsm_sig "FlushPrivateData")} /\
          `cache_put_valid` = Ob~0 /\
          `meta_put_valid` = Ob~0
      }}}.

    Definition cache_post_invert_Purged
      (cache: mem_type) (core: ind_core_id)
      (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let purge_reg := _mid (purge core) in
      let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
      let cache_put_valid := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid")
                             (ext_log (_extid (ext_cache cache core))) in
      let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                           (ext_log (_extid (ext_metadata cache core))) in
      {{{ `reg_final purge_reg` = #(_enum purge_state "Purged") ->
          { {`reg_init purge_reg` = #(_enum purge_state "Purged") /\
             `reg_init cache_fsm` = #(_enum cache_fsm_sig "Ready") } \/
           `reg_init cache_fsm` = #(_enum cache_fsm_sig "Flushed")} /\
          `cache_put_valid` = Ob~0 /\
          `meta_put_valid` = Ob~0
      }}}.

    Definition cache_flush_only_invalidate_metadata
      (cache: mem_type) (core: ind_core_id)
      (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
      let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                             (ext_log (_extid (ext_metadata cache core))) in
      let meta_put_request := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_request")
                             (ext_log (_extid (ext_metadata cache core))) in
      let meta_is_write :=  get_field (_sid metadata_req_sig) (_fld metadata_req_sig "is_write")
                             meta_put_request in
      let meta_data := get_field (_sid metadata_req_sig) (_fld metadata_req_sig "data")
                             meta_put_request in
      {{{ `reg_init cache_fsm` <> #(_enum cache_fsm_sig "WaitFillResp") ->
          `meta_put_valid` = Ob~1 ->
          `meta_is_write` = Ob~1 ->
          `meta_data` = #(zeroes (_unsafe_struct_sz metadata_sig))
      }}}.

    Definition cache_flush_only_invalidate_cache
      (cache: mem_type) (core: ind_core_id)
      (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let cache_fsm := _mid (cache_reg cache core CacheState.cache_fsm) in
      let cache_put_valid := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid")
                             (ext_log (_extid (ext_cache cache core))) in
      let cache_put_request := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_request")
                             (ext_log (_extid (ext_cache cache core))) in
      let cache_byte_en := get_field (_sid cache_req_sig) (_fld cache_req_sig "byte_en") cache_put_request in
      let cache_line := get_field (_sid cache_req_sig) (_fld cache_req_sig "addr") cache_put_request in
      let cache_data := get_field (_sid cache_req_sig) (_fld cache_req_sig "data") cache_put_request in
      {{{ `reg_init cache_fsm` <> #(_enum cache_fsm_sig "WaitFillResp") ->
          `reg_init cache_fsm` <> #(_enum cache_fsm_sig "ProcessRequest") ->
          `cache_put_valid` = Ob~1 ->
          `cache_byte_en` <> Ob~0~0~0~0 ->
          `cache_data` = #(zeroes 32)
      }}}.

    Definition cache_purged_args_zero
      (cache: mem_type) (core: ind_core_id)
      (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
      (ext_log: debug_id_ty -> sval)
      : fancy_spred :=
      let meta_put_valid := get_field (_sid metadata_input_sig) (_fld metadata_input_sig "put_valid")
                             (ext_log (_extid (ext_metadata cache core))) in
      let cache_put_valid := get_field (_sid cache_input_sig) (_fld cache_input_sig "put_valid")
                             (ext_log (_extid (ext_cache cache core))) in
      {{{`reg_init (_mid (purge core))` = #(_enum purge_state "Purged") ->
         `meta_put_valid` = Ob~0 /\
         `cache_put_valid` = Ob~0
      }}}.



    Definition cache_post (cache: mem_type) (core: ind_core_id)
                          (reg_init reg_final: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval)
                          (ext_log: debug_id_ty -> sval)
                          : list (mem_custom_t * fancy_spred) :=
      [(MemCacheNoResp cache core, impl_post_ext_cache_no_resp_core core cache reg_init reg_final get_field ext_log)
      ;(MemMetaNoResp cache core, impl_post_ext_meta_no_resp_core core cache reg_init reg_final get_field ext_log)
      ;(Mem_PostMetaGetReady__Ext cache core, meta_obs_put_valid_impl_get_ready__ext cache core reg_final get_field ext_log)
      ;(Mem_PostCacheGetReady__Ext cache core, cache_obs_put_valid_impl_get_ready__ext cache core reg_final get_field ext_log);
      (Mem_PostCacheGetReady__Reg cache core, cache_obs_get_ready_implied cache core reg_init get_field ext_log)
      ;(Mem_PostMetaGetReady__Reg cache core, meta_obs_get_ready_implied cache core reg_init get_field ext_log);
       (* (Mem_PostMetacacheSameLine cache core, metacache_same_line cache core get_field ext_log); *)
       (Mem_PostCacheAddr cache core, valid_meta_addr cache core reg_init reg_final get_field ext_log);
       (MemMetaRespInRange cache core, impl_post_ext_meta_req_in_range cache core reg_init reg_final get_field ext_log);

       (Mem_post_FlushLineProcess cache core, mem_post_FlushLineProcess cache core reg_init reg_final get_field ext_log);
       (Mem_PostCacheFSM_InvertFlushed cache core, cache_post_invert_Flushed cache core reg_init reg_final get_field ext_log);
       (Mem_PostCacheFSM_InvertFlushLineProcess cache core, cache_post_invert_FlushLineProcess cache core reg_init reg_final get_field ext_log);
       (Mem_PostCacheFSM_InvertFlushLineReady cache core, cache_post_invert_FlushLineReady cache core reg_init reg_final get_field ext_log);
       (Mem_PostCacheFSM_InvertFlushPrivateData cache core, cache_post_invert_FlushPrivateData cache core reg_init reg_final get_field ext_log);
       (Mem_PostCacheFSM_InvertPurged cache core, cache_post_invert_Purged cache core reg_init reg_final get_field ext_log);
       (Mem_FlushFSM_OnlyInvalidateMetadata cache core, cache_flush_only_invalidate_metadata cache core reg_init reg_final get_field ext_log);
       (Mem_FlushFSM_OnlyInvalidateCache cache core, cache_flush_only_invalidate_cache cache core reg_init reg_final get_field ext_log);
       (Mem_PurgedArgsZero cache core, cache_purged_args_zero cache core reg_init reg_final get_field ext_log)
      ].


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
      (MemImplExtCorrectCore CoreId1, impl_post_ext_mem_correct_core CoreId1 reg_final get_field ext_log);
      (MemMainMemPutIsReadTurn, impl_post_main_mem_put_is_read_turn reg_final get_field ext_log);
      (Mem_push_in_range0, fs_push_in_range CoreId0 reg_init ext_log MachineImpl);
      (Mem_push_in_range1, fs_push_in_range CoreId1 reg_init ext_log MachineImpl);
      (Mem_push_in_config0, push_req_in_config CoreId0 reg_init ext_log get_field);
      (Mem_push_in_config1, push_req_in_config CoreId1 reg_init ext_log get_field)
    ] ++ (assert_ext_fns_empty ext_log (fun f => MemExtFn (_id f))
            [( ext_uart_write);( ext_uart_read);( ext_led); ( ext_finish)] )
      ++ List.concat (map (fun '(cache,core) => cache_post cache core reg_init reg_final get_field ext_log)
                          [(imem, CoreId0) ; (dmem, CoreId0); (imem, CoreId1); (dmem, CoreId1) ]).
    (* TODO! *)
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
    (* Fascinating, turns out order of asserts matters... *)
    Definition mem_post_conds (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval) get_field : list (mem_custom_t * fancy_spred) :=
      (mem_invariant reg_final get_field) ++ (mem_post_conds' reg_init reg_final ext_log get_field) .
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
  End WithEnclaveSig.
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
         file_assumptions := preprocess_fancy_spreds (mem_pre_conds EnclaveParams.enclave_sig impl_init impl_get_field);
         file_assertions := preprocess_fancy_spreds (mem_post_conds EnclaveParams.enclave_sig impl_init impl_final impl_final_ext impl_get_field);
      |}.
  End ImplStep.
(*   Module TestStep. *)
(*     Definition test_schedule := *)
(* Machine.RlMem (Rl_doCacheReq imem CoreId0) *)
(*          |> Machine.RlMem (Rl_doMemReq CoreId0) *)
(*             (* |> Machine.RlMem (Rl_doMemReq CoreId1) *) *)
(*                |> Machine.RlMem (Rl_doPurge CoreId0) *)
(*                   (* |> Machine.RlMem (Rl_doPurge CoreId1) *) *)
(*                      |> Machine.RlMem (Rl_doExternalMetadata imem CoreId0) *)
(*                                 |> Machine.RlMem (Rl_doExternalCache imem CoreId0) *)
(*                                             |> Machine.RlMem Rl_doExternalMem *)
(*                                                 |> Machine.RlMem (Rl_doMemResp CoreId0) *)
(*                                                    (* |> Machine.RlMem (Rl_doMemResp CoreId1) *) *)
(*                                                       |> Machine.RlMem (Rl_doInit CoreId0) *)
(*                                                          (* |> Machine.RlMem (Rl_doInit CoreId1) *) *)
(*                                                             |> Machine.RlMem (Rl_doFreeze CoreId0) *)
(*                                                                (* |> Machine.RlMem (Rl_doFreeze CoreId1) *) *)
(*                                                                   |> Machine.RlMem Rl_tick |> done. *)
(*     Definition impl_schedule_list : list (Machine.rule_name_t * string) := *)
(*       map (fun rl => (rl, show rl)) (list_of_schedule (test_schedule)). *)
(*     Definition impl_typecheck_fn rl : result (aaction * nat) unit := *)
(*       typecheck_rule reg_types ext_fn_tys int_fns struct_defs (inline_rule int_fns rl). *)
(*     Definition impl_schedule := *)
(*       preprocess_schedule impl_typecheck_fn rules impl_schedule_list. *)
(*     Definition file: file_t := *)
(*       {| file_machines := Single impl_machine impl_schedule; *)
(*          file_assumptions := preprocess_fancy_spreds (mem_pre_conds EnclaveParams.enclave_sig impl_init impl_get_field); *)
(*          file_assertions := preprocess_fancy_spreds (mem_post_conds EnclaveParams.enclave_sig impl_init impl_final impl_final_ext impl_get_field); *)
(*       |}. *)
(*     Axiom SMT_file: SymbolicInterp.WF_single_file file = true. *)
(*   End TestStep. *)
End MemoryProofDefs.

(* Module TestMemory. *)
  (* Require Import koikaExamples.EnclaveWithCache.External. *)
  (* Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
  (* Module Memdefs := Empty <+ MemoryProofDefs EnclaveParams SecurityParams. *)
  (* Import Memdefs. *)
  (* Definition file := Eval vm_compute in ImplStep.file. *)
  (* Extraction "MemStep.ml" struct_sz vect_t file. *)
  (* Definition file := Eval vm_compute in TestStep.file. *)
  (* Extraction "MemStep.ml" struct_sz vect_t file. *)
(* End TestMemory. *)
Module Type SMT_Mem_sig (EnclaveParams: EnclaveParams_sig)
                       (SecurityParams: SecurityParams_sig EnclaveParams)
                       (MemDefs: MemoryProofDefs EnclaveParams SecurityParams).

  Parameter SMT_file_ok: SymbolicInterp.WF_single_file MemDefs.ImplStep.file = true.

End SMT_Mem_sig.

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
        (preprocess_fancy_spreds (mem_pre_conds EnclaveParams.enclave_sig impl_init impl_get_field))
        (preprocess_fancy_spreds (mem_post_conds EnclaveParams.enclave_sig impl_init impl_final impl_final_ext impl_get_field)).
  Proof.
    pose proof SMT_file_ok.
    specialize symbolic_evaluate_file_success with (file := ImplStep.file).
    propositional.
  Qed.

  Theorem impl_step_mem_sched_correct:
      interp_scheduler_satisfies_spec reg_type_env _ext_fn_tys id_int_fns id_struct_defs
        id_rules Impl.mem_schedule unit
        (fun st sigma _ => MemPre EnclaveParams.enclave_sig st  sigma)
        (fun st sigma st' ext_log _ => MemPost EnclaveParams.enclave_sig st st' sigma ext_log).
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

(* Module TestMemory. *)
(*   Require Import koikaExamples.EnclaveWithCache.External. *)

(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)
(*   Module Memdefs := Empty <+ MemoryProofDefs EnclaveParams SecurityParams. *)
(*   Import Memdefs. *)

(*   Definition file := Eval vm_compute in ImplStep.file. *)
(*   Extraction "../../../../MemStep.ml" struct_sz vect_t file. *)

(* End TestMemory. *)
