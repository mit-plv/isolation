Require Import rv_isolation.Common.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.

(* Security parameters, optionally audited. *)
Module Type SecurityParams_t.
  Parameter machine_state_t : Type.
  (* Behavior of subsidiary "air-gapped" machines in the spec. *)
  Parameter local_step_fn0: machine_state_t -> input_t -> machine_state_t * local_observations_t.
  Parameter local_step_fn1: machine_state_t -> input_t -> machine_state_t * local_observations_t.
  Parameter extract_dram: machine_state_t -> dram_t.
  Parameter extract_rf: machine_state_t -> ind_core_id -> reg_file_t.
  (* Initial state of a new enclave *)
  Parameter spin_up_machine: ind_core_id -> nat -> core_init_params_t -> dram_t ->  machine_state_t.
End SecurityParams_t.

(* An instantiation for our case-study *)
Module Type SecurityParams_sig (EnclaveParams: EnclaveParams_sig) <: SecurityParams_t.
  Module Impl := Empty <+ Impl.Impl EnclaveParams.
  Module Machine := Empty <+ TopLevelModule EnclaveParams Impl .
  (* Module Implementation := Empty <+ Implementation_sig EnclaveParams Impl ExternalMemory Machine. *)
  Import TopLevelModuleHelpers.
  Import ExternalMemory.

  Definition machine_state_t := machine_state_t.

  Definition extract_dram (st: machine_state_t) :=
    st.(machine_mem_st).(ext_mem).

  Definition extract_rf (st: machine_state_t) (core: ind_core_id) : reg_file_t :=
    fun n =>
      match Vect.index_of_nat RVCore.Core.Rf.sz n with
      | Some idx =>Some (st.(machine_koika_st).[_rid ((SecurityMonitor.core_reg core) (RVCore.Core.rf (RVCore.Core.Rf.rData idx)))])
      | None => Some (Bits.zeroes 32)
      end.

  Definition local_step_fn0 := Machine.Core0Machine.step.
  Definition local_step_fn1 := Machine.Core1Machine.step.

  Definition spin_up_machine: ind_core_id -> nat -> core_init_params_t -> dram_t ->  machine_state_t :=
    fun core_id cycles params dram =>
    match core_id with
    | CoreId0 => Machine.initial_state params
                  dummy_core_init_params
                  (Bits.of_nat 2 (Nat.modulo cycles 4)) [Nat.odd cycles] dram
    | CoreId1 => Machine.initial_state
                  dummy_core_init_params params
                  (Bits.of_nat 2 (Nat.modulo cycles 4)) [Nat.odd cycles] dram
    end.

End SecurityParams_sig.

(* Top-level theorem, parameterised over enclave parameters and security parameters. *)
Module Type Secure_t (EnclaveParams: EnclaveParams_sig)
                     (SecurityParams: SecurityParams_sig EnclaveParams).
  Module Impl := SecurityParams.Machine.FullMachine.
  Module Spec := Empty <+ Spec_sig EnclaveParams.

  (* For any well-formed initial memory, there exists a "can_start_fn" describing when a core can enter an enclave such that for _any_ behavior of the external world, the implementation observably behaves like the spec instantiated with the security parameters. *)
  Parameter secure :
    forall (initial_dram: dram_t),
      exists (can_start_fn: ind_core_id -> nat -> nat -> enclave_config -> option enclave_config -> bool),
      forall (external_world_state_t: Type)
        (input_machine: @i_machine_t external_world_state_t output_t input_t)
        (n: nat),
        WF_dram initial_dram ->
        Impl.step_n initial_dram input_machine n =
          Success (Spec.step_n SecurityParams.local_step_fn0
                               SecurityParams.local_step_fn1
                               can_start_fn
                               SecurityParams.spin_up_machine
                               SecurityParams.extract_dram
                               SecurityParams.extract_rf
                               (dram_to_mem_map EnclaveParams.enclave_sig initial_dram) input_machine n).

End Secure_t.
