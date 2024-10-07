Require Import rv_cache_isolation.Common.
Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import PeanoNat.

Definition can_enter_enclave (config: enclave_config) (other_config: option enclave_config) : bool :=
  negb (configs_conflict config other_config).

Definition filter_input (opt_config: option enclave_config) (input: input_t) : input_t :=
  match opt_config with
  | Some config =>
      {| input_ext_uart_write :=
          if config.(config_ext_uart) then
            input.(input_ext_uart_write)
          else
            fun _ => Bits.zeroes (ext_fn_arg_type ext_uart_write);
         input_ext_uart_read :=
          if config.(config_ext_uart) then
            input.(input_ext_uart_read)
          else
            fun _ => Bits.zeroes (ext_fn_arg_type ext_uart_read);
         input_ext_led :=
          if config.(config_ext_led) then
            input.(input_ext_led)
          else
            fun _ => Bits.zeroes (ext_fn_arg_type ext_led);
         input_ext_finish :=
          if config.(config_ext_finish) then
            input.(input_ext_finish)
          else
            fun _ => Bits.zeroes (ext_fn_arg_type ext_finish);
      |}
  | None => {| input_ext_uart_write := fun _ => Bits.zeroes (ext_fn_arg_type ext_uart_write);
              input_ext_uart_read := fun _ => Bits.zeroes (ext_fn_arg_type ext_uart_read);
              input_ext_led := fun _ => Bits.zeroes (ext_fn_arg_type ext_led);
              input_ext_finish := fun _ => Bits.zeroes (ext_fn_arg_type ext_finish);
           |}
  end.

(* Spec:
 * - implementation behaves as a system that spins up enclaves
 * - an enclave is initialized with a specific memory region, enclave configuration, registers from previous run, and core id
 * - when running, an enclave behaves as if in an air-gapped machine (where "behaves" is defined as ??? memory load stores? enclave exits?)
 * - upon exiting, we save an enclave's register file (do we care what registers these actually are? if so we need to talk about them in the spec) and memory (^same as for register file), and try to switch to new enclave
 * - time it takes to enter a new enclave does depend on whether other core is running the requested enclave (don't need to guarantee only one enclave can enter at a time?)
 * - is it allowed to know the cycle clock?
 * - initialization:
     + guarantee we start at enclave 0? or make no guarantees? what is functional correctness and what is security.
 *)

Module SpecDefs.

  Section WithParams.
    Context {machine_state_t: Type}.

    Inductive core_state_t :=
    | CoreState_Enclave (machine_state: machine_state_t) (config: enclave_config)
                        (* (enclave_state: enclave_state_t) *)
    | CoreState_Waiting (new: enclave_config) (rf: reg_file_t) (exit_cycle: nat).

    Record state_t: Type :=
      { machine_state: ind_core_id -> core_state_t;
        mem_regions: memory_map_t;
        cycles: nat (* TODO? *)
      }. (* history of enclaves needed to switch *)
    (* TODO: try to enter? *)
    Inductive transition_state_t :=
    | Transition_Exit (new: enclave_config) (context: context_switch_data_t) (obs: local_observations_t)
    | Transition_Core (st: core_state_t) (obs: local_observations_t)
    .

  End WithParams.
End SpecDefs.

Module Type Spec_sig (EnclaveParams: EnclaveParams_sig).
  Include SpecDefs.

  Section WithParams.
    Context {machine_state_t: Type}.
    Context (local_step_fn0: machine_state_t -> input_t -> machine_state_t * local_observations_t).
    Context (local_step_fn1: machine_state_t -> input_t -> machine_state_t * local_observations_t).
    Context (can_start_fn: ind_core_id -> nat -> nat -> enclave_config -> option enclave_config -> bool). (* TODO *)
    Context (spin_up_machine: ind_core_id -> nat -> core_init_params_t -> dram_t ->  machine_state_t).
    (* Context (extract_next_rf: machine_state_t -> reg_file_t). *)
    Context (extract_dram: machine_state_t -> dram_t).
    Context (extract_rf: machine_state_t -> ind_core_id -> reg_file_t).
    (* TODO: WF_extract_rf: ensure reg_file_t is some fixed size? *)
    (* TODO: WF_extract_dram *)

    Context (wf_can_start_fn: forall t_exit0 t_exit1 cycles new0 new1,
                configs_conflict new0 (Some new1) = true ->
                can_start_fn CoreId0 t_exit0 cycles new0 None = true  ->
                can_start_fn CoreId1 t_exit1 cycles new1 None = true  ->
                False).

    (* Context (extract_next_enclave_config: machine_state_t -> enclave_config). *)
    Context (initial_mem_map : memory_map_t).
    (* Context (initial_rf0: reg_file_t). *)
    (* Context (initial_rf1: reg_file_t). *)

    (* Inductive enclave_state_t := *)
    (* | EnclaveState_Running *)
    (* | EnclaveState_Switching (next_enclave: enclave_config). *)

    Section Initialised.
      (* TODO: functional correctness vs security? *)

      Definition initial_enclave_config0 :=
        match EnclaveParams.enclave_sig.(_core_init0).(machine_config) with
        | Some config => config
        | None => (* Should not happen *)
                {| config_eid := Enclave0;
                   config_shared_regions := fun _ => false;
                   config_ext_uart := false;
                   config_ext_led := false;
                   config_ext_finish := false;
                 |}
        end.
      Definition initial_enclave_config1 :=
        match EnclaveParams.enclave_sig.(_core_init1).(machine_config) with
        | Some config => config
        | None => (* Should not happen *)
                {| config_eid := Enclave1;
                   config_shared_regions := fun _ => false;
                   config_ext_uart := false;
                   config_ext_led := false;
                   config_ext_finish := false;
                 |}
        end.

      Definition initial_state: state_t :=
        {| machine_state :=
            fun core_id =>
            match core_id with
            | CoreId0 => CoreState_Enclave
                          (spin_up_machine CoreId0 0 (_core_init0 EnclaveParams.enclave_sig)
                             (get_enclave_dram EnclaveParams.enclave_sig initial_mem_map initial_enclave_config0)
                          )
                          initial_enclave_config0
            | CoreId1 => CoreState_Enclave
                          (spin_up_machine CoreId1 0 (_core_init1 EnclaveParams.enclave_sig)
                             (get_enclave_dram EnclaveParams.enclave_sig initial_mem_map initial_enclave_config1)
                          )
                          initial_enclave_config1
            end;
           mem_regions := initial_mem_map;
           cycles := 0
        |}.
    End Initialised.

    (* TODO: can_switch/ distinguish between just exited core step? *)
    Definition local_core_step (core: ind_core_id) (st: core_state_t) (input: input_t) : transition_state_t :=
      match st with
      | CoreState_Enclave machine_state config =>
          let '(machine_state', obs) := match core with
                                        | CoreId0 => local_step_fn0 machine_state input
                                        | CoreId1 => local_step_fn1 machine_state input
                                        end in
          match obs.(obs_exit_enclave) core with
          | Some (new_config) =>
              Transition_Exit new_config {| context_switch_config := config;
                                            context_switch_dram := extract_dram machine_state';
                                            context_switch_rf := extract_rf machine_state' core
                                         |} obs
          | None => Transition_Core (CoreState_Enclave machine_state' config) obs
          end
      | CoreState_Waiting new rf exit_cycle => Transition_Core st empty_local_observations
      end.
    Notation core_state_t := (@core_state_t machine_state_t).
    Notation transition_state_t := (@transition_state_t machine_state_t).

    Definition get_core_config (st: core_state_t) : option enclave_config :=
      match st with
      | CoreState_Enclave _ config => Some config
      | CoreState_Waiting _ _ _ => None
      end.

    (* TODO *)
    Definition get_transition_config (st: transition_state_t) : option enclave_config :=
      match st with
      | Transition_Core st _ => get_core_config st
      | Transition_Exit _ _ _ => None
      end.


    (* TODO: allow exit and enter in same step? *)
    Definition do_exit_step (state: transition_state_t) (mem_regions: memory_map_t) (cycles: nat)
                            : core_state_t * local_observations_t * memory_map_t :=
      match state with
      | Transition_Exit new context obs =>
          let new_regions := update_regions EnclaveParams.enclave_sig
                                            context.(context_switch_config)
                                            context.(context_switch_dram)
                                            mem_regions in
          ((CoreState_Waiting new context.(context_switch_rf) cycles),obs,new_regions)
      | Transition_Core st obs => (st, obs, mem_regions)
      end.

    Definition do_enter_step (core_id: ind_core_id) (trans_state: transition_state_t)
                             (other_core_config: option enclave_config)
                             (cycles: nat)
                             (mem_regions: memory_map_t)
                             : transition_state_t :=
      match trans_state with
      | Transition_Exit new context obs => trans_state
      | Transition_Core (CoreState_Enclave _ _ ) _ =>
          trans_state
      | Transition_Core (CoreState_Waiting new rf t_exit) obs =>
           if can_enter_enclave new other_core_config
             && can_start_fn core_id t_exit cycles new other_core_config (* TODO: nd/state *) then
            let machine := spin_up_machine core_id (cycles +1 )
                                           {| machine_pc := _enclave_bootloader_addr EnclaveParams.enclave_sig (config_eid new);
                                              machine_rf := rf;
                                              machine_config := Some new
                                           |}
                                           (get_enclave_dram EnclaveParams.enclave_sig mem_regions new)  in
            Transition_Core (CoreState_Enclave machine new) obs
           else
             trans_state
      end.

    (* TODO:
       - disjoint memory regions?
       - Exit ordering?
     *)

    (* TODO: check *)
    Definition merge_ext (v1 v2: vect_t) : vect_t :=
      if beq_dec v1 (Bits.zeroes (List.length v1)) then
        v2
      else v1.

    Definition merge_external_observations (obs1 obs2: external_observations_t) : external_observations_t :=
      {| obs_uart_write := merge_ext obs1.(obs_uart_write) obs2.(obs_uart_write);
         obs_uart_read := merge_ext obs1.(obs_uart_read) obs2.(obs_uart_read);
         obs_led := merge_ext obs1.(obs_led) obs2.(obs_led);
         obs_finish := merge_ext obs1.(obs_finish) obs2.(obs_finish);
      |}.

    (* Impl -> one set of observations
     * Spec -> can produce same observations with no interference when running
     *)
    (* Issue: entering is based on state at beginning of cycle *)
    Definition spec_step (st: state_t) (input: input_t) : state_t * output_t :=
      let trans_core0 := local_core_step CoreId0 (st.(machine_state) CoreId0)
                           (filter_input (get_core_config (st.(machine_state) CoreId0)) input) in
      let trans_core1 := local_core_step CoreId1 (st.(machine_state) CoreId1)
                           (filter_input (get_core_config (st.(machine_state) CoreId1)) input) in
      let trans_core0 := do_enter_step CoreId0 trans_core0 (get_core_config (st.(machine_state) CoreId1))
                                       st.(cycles) st.(mem_regions) in
      let trans_core1 := do_enter_step CoreId1 trans_core1 (get_core_config (st.(machine_state) CoreId0))
                                       st.(cycles) st.(mem_regions) in
      let '(exit_core0, obs0, mem0) := do_exit_step trans_core0 st.(mem_regions) st.(cycles) in
      let '(exit_core1, obs1, mem1) := do_exit_step trans_core1 mem0 st.(cycles) in
      let st' := {| machine_state := fun core_id =>
                                     match core_id with
                                     | CoreId0 => exit_core0
                                     | CoreId1 => exit_core1
                                     end;
                    mem_regions := mem1;
                    cycles := st.(cycles) + 1
                 |} in
      (st', merge_external_observations obs0.(obs_ext) obs1.(obs_ext)).

    Section WithExternalWorld.
      Context {external_world_state_t : Type}.
      Context (input_machine: @i_machine_t external_world_state_t output_t input_t).

      Definition step (st: state_t) (input_st: external_world_state_t)
        : state_t * external_world_state_t * output_t :=
        safe_step spec_step input_machine st input_st.

      Definition step_n' (n: nat) (st: state_t) (input_st: external_world_state_t)
        : state_t * external_world_state_t * list output_t :=
        safe_step_n' spec_step input_machine n st input_st .

      Definition step_n (n: nat) : list output_t :=
        safe_step_n initial_state spec_step input_machine n.

    End WithExternalWorld.

  End WithParams.
End Spec_sig.
