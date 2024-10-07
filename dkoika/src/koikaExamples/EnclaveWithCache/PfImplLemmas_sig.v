Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import FunctionalExtensionality.
Require Import koikaExamples.EnclaveWithCache.PfDefs.
Require Import koikaExamples.EnclaveWithCache.PfImplDefs.

Module Type PfImplLemmas_sig (EnclaveParams: EnclaveParams_sig)
                   (SecurityParams: SecurityParams_sig EnclaveParams)
                   (ImplDefs: PfImplDefs EnclaveParams SecurityParams).

  Import SecurityParams.Machine.
  Import SecurityParams.Impl.

  Import SecurityParams.
  Import ExternalMemory.
  Notation impl_state_t := machine_state_t.
  Import ImplDefs.
  Import TopLevelModuleHelpers.
  Parameter impl_interp_cycle_correct':
    forall impl_st input ,
      ImplInvariant impl_st ->
      match
        interp_scheduler (mk_sigma_fn impl_st.(machine_mem_st) input)
                         id_int_fns id_struct_defs
              impl_st.(machine_koika_st)
             id_rules
             Impl.schedule with
      | Success log => strong_WF_state reg_type_env (commit_update impl_st.(machine_koika_st) log.(Log__koika)) /\
                        WF_ext_log _ext_fn_tys log.(Log__ext)
      | _ => False
      end.

 Parameter impl_step_preserves_impl_inv':
  forall impl_st input ,
      ImplInvariant impl_st ->
      exists res mem_st' ,
      interp_scheduler
        (mk_sigma_fn impl_st.(machine_mem_st) input)
                         id_int_fns id_struct_defs
              impl_st.(machine_koika_st)
             id_rules
             Impl.schedule = Success res /\
        ImplPost impl_st
                 {| machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika res);
                   machine_mem_st := mem_st' |} (Log__ext res).
End PfImplLemmas_sig.
