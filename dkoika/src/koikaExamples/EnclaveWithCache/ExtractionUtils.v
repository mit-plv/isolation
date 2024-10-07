Require Coq.extraction.Extraction.
Extraction Language OCaml.
From Coq.extraction Require Export ExtrOcamlBasic ExtrOcamlNativeString ExtrOcamlNatInt ExtrOcamlZInt.

Require Import koika.Frontend.
Require Import koika.Symbolic.
Require Import koika.AnnotatedSyntax.
Require Import koika.SymbolicInterp.

Require Import FunctionalExtensionality.

Require Import rv_cache_isolation.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.External.
Global Set Extraction KeepSingleton.
Require Import koikaExamples.EnclaveWithCache.Common.


Module Impl' := Empty <+ Impl.Impl EnclaveParams.
Module Machine := Empty <+ TopLevelModule EnclaveParams Impl'.

Module Impl := Machine.FullMachine.
Module Spec0 := Machine.Core0Machine.
Module Spec1 := Machine.Core1Machine.
Definition unsafe_get_ext_call_from_log := unsafe_get_ext_call_from_log _ext_fn_tys.
Definition unsafe_get_ext_fn_arg_type :=  unsafe_get_ext_fn_arg_type _ext_fn_tys.

Definition unsafe_lookup_dstruct_fields (env: @struct_env_t debug_id_ty) (id: debug_id_ty) :=
  match lookup_struct (fst id) with
  | Success sid => sid.(dstruct_fields)
  | _ => []
  end.

Notation interp_fancy_spred := (@interp_fancy_spred _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation interp_fancy_spred2 := (@interp_fancy_spred2 _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation interp_spred := (@interp_spred _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation interp_spred2 := (@interp_spred2 _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation interp_sval := (@interp_sval _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation interp_sval2 := (@interp_sval2 _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation WF_single_file := (@WF_single_file _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation WF_product_file := (@WF_product_file _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation symbolic_evaluate_file_success := (@symbolic_evaluate_file_success _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation symbolic_evaluate_file_success_single := (@symbolic_evaluate_file_success_single _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation symbolic_evaluate_file_success_product := (@symbolic_evaluate_file_success_product _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation symbolic_evaluate_file_success_abstract_single := (@symbolic_evaluate_file_success_abstract_single _ext_fn_tys unsafe_lookup_dstruct_fields).
Notation symbolic_evaluate_file_success_abstract_product := (@symbolic_evaluate_file_success_abstract_product _ext_fn_tys unsafe_lookup_dstruct_fields).


   Definition foo_req_addrs_in_region enclave_sig (region: mem_region)
     (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) (reg_data reg_enclave: sval) : fancy_spred :=
     let sval_enclave_data :=
       get_field (_sid enclave_data) (_fld enclave_data "data") (reg_enclave)  in
     let sval_addr := get_field (_sid mem_req) (_fld mem_req "addr") (reg_data) in
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
Notation reg_t := (@Syntax.reg_t debug_id_ty).

  Definition foo_fifo_req_addrs_in_range enclave_sig (reg_fn: reg_t -> sval) (get_field: debug_id_ty -> debug_id_ty -> sval -> sval) (reg_valid reg_data reg_enclave: reg_t)
              : fancy_spred :=
    let reg_data := reg_fn reg_data in
    let reg_enclave := reg_fn reg_enclave in

    {{{ `reg_fn reg_valid` = Ob~1 ->
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Enclave Enclave0)   get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Enclave Enclave1)   get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Enclave Enclave2)   get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Enclave Enclave3)   get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared01)   get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared02)   get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared03)   get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared12)   get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared13)   get_field reg_data reg_enclave`` \/
        ``foo_req_addrs_in_region enclave_sig (MemRegion_Shared Shared23)   get_field reg_data reg_enclave``
    }}}.


  Ltac _vm_simplify :=
    repeat match goal with
    | _ =>
        let X := fresh in
        (set (unsafe_lookup_dstruct_fields _ _) as X ||
         set (_fld _ _ ) as X
        ); vm_compute in X; subst X
    | _ =>
        let X := fresh in
        (set (_get_field _ _ _) as X; cbn - [nth] in X; subst X)
    end.
