(*! Top-level theorem *)
Require Import Koika.Frontend.
Require Import Koika.examples.ResourceIsolation_Util.
Require Import Koika.examples.ResourceIsolation_Impl.
Require Import Koika.examples.ResourceIsolation_Spec.


Import Common.

Module Type Secure_t.
  (* Trace-equivalence between the implementation and specification, for all external functions (including F and G boxes *)
  Parameter secure :
    forall (sigma: input_t -> ext_sigma_t) (pf_WF_ext_sigma: Impl.wf_sigma sigma),
    exists (local_st_t: Type)
      (init_turn: Spec.turn_t)
      (init_hist_ready: option Tag)
      (local_init_state: input_t -> Tag -> Spec.turn_t -> local_st_t)
      (local_observe_output_reg: local_st_t -> Spec.obs_output_reg_t)
      (local_observe_output: Spec.turn_t -> (Tag -> option Spec.local_output_t) -> Spec.obs_output_reg_t)
      (update_ready_for_job: option Tag -> Spec.turn_t -> (Tag -> bool) -> option Tag)
      (output_get_valid: Spec.obs_output_reg_t -> bool)
      (local_step_fn: local_st_t -> local_st_t),
    forall (external_world_state_t: Type)
      (input_machine: @i_machine_t external_world_state_t output_t input_t)
      (n: nat),
      Impl.step_n sigma input_machine n =
        Success (Spec.step_n init_turn init_hist_ready local_init_state
                  local_observe_output_reg  local_observe_output
                  update_ready_for_job output_get_valid local_step_fn
                  input_machine n).
End Secure_t.
