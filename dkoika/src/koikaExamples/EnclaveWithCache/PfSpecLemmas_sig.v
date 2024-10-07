Require Import rv_cache_isolation.Common.
Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import FunctionalExtensionality.
Require Import koikaExamples.EnclaveWithCache.PfSpecDefs.



Module Type PfSpecLemmas_sig (EnclaveParams: EnclaveParams_sig)
                   (SecurityParams: SecurityParams_sig EnclaveParams)
                   (Spec: Spec_sig EnclaveParams)
                   (SpecDefs: PfSpecDefs EnclaveParams SecurityParams Spec).
  Import SecurityParams.Machine.
  Import SecurityParams.
  Import ExternalMemory.
  Notation impl_state_t := machine_state_t.
  Import Spec.
  Import SpecDefs.
  Parameter spec_running_new_machine:
    forall core new memory cycles rf pc,
      wf_mem_regions memory ->
      Datatypes.length pc = 32 ->
      SpecCoreInvariant__Running core
        (spin_up_machine core cycles
                         {| machine_pc := pc;
                            machine_rf := rf;
                            machine_config := Some new
                         |}
                         (get_enclave_dram EnclaveParams.enclave_sig memory new)) new.

  Parameter spec_step_case_core_state:
      forall spec_st input spec_st' output,
      SpecInvariant spec_st ->
      spec_step SecurityParams.local_step_fn0 SecurityParams.local_step_fn1
        SpecParams.can_start_fn SecurityParams.spin_up_machine SecurityParams.extract_dram SecurityParams.extract_rf spec_st input = (spec_st', output) ->
      exists output0 output1 memory',
      (case_core_state CoreId0 (spec_step_core CoreId0 (machine_state spec_st CoreId0) input)
         (machine_state spec_st CoreId0) (machine_state spec_st' CoreId0) output0
                       (cycles spec_st) (mem_regions spec_st) memory') (get_spec_configs spec_st CoreId1) /\
      (case_core_state CoreId1 (spec_step_core CoreId1 (machine_state spec_st CoreId1) input)
         (machine_state spec_st CoreId1) (machine_state spec_st' CoreId1) output1
                       (cycles spec_st) memory' (mem_regions spec_st'))
        (get_spec_configs spec_st CoreId0)  /\
      (output = merge_external_observations output0 output1).

  Parameter spec_step_core_invariant:
    forall core machine_st config machine_st' local_output input,
    SpecCoreInvariant__Running core machine_st config ->
    spec_step_core core (CoreState_Enclave machine_st config) input
                        machine_st = (machine_st', local_output) ->
    SpecCorePost core machine_st config machine_st' local_output.

  Parameter spec_step_preserves_spec_inv:
        forall spec_st
        (external_world_state_t: Type)
        (input_machine: @i_machine_t external_world_state_t output_t input_t)
        ext_st spec_st' ext_st'__spec output__spec,
        SpecInvariant spec_st ->
        Spec.step
            SecurityParams.local_step_fn0
            SecurityParams.local_step_fn1
        SpecParams.can_start_fn
        SecurityParams.spin_up_machine
        SecurityParams.extract_dram
        SecurityParams.extract_rf
        input_machine spec_st ext_st = (spec_st', ext_st'__spec, output__spec) ->
    SpecInvariant spec_st'.

End PfSpecLemmas_sig.
