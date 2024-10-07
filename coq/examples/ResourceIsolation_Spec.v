(*! Resource isolation specification *)

Require Import Koika.Frontend.
Require Import Koika.examples.ResourceIsolation_Util.

Module Spec.

  Import Common.

  Definition turn_t := bool.
  Definition obs_output_reg_t := list bool.
  Definition local_output_t := obs_output_reg_t. (* maybe sz *)

  Section WithParams.
    Context {local_st: Type}.
    Context (init_turn: turn_t).
    Context (init_hist_ready_for_job: option Tag).
    Context (local_init_state: input_t -> Tag -> turn_t -> local_st).
    Context (local_observe_output_reg: local_st -> obs_output_reg_t).
    Context (local_observe_output: turn_t -> (Tag -> option local_output_t) -> obs_output_reg_t).
    Context (update_ready_for_job : option Tag -> turn_t -> (Tag -> bool) -> option Tag).
    Context (output_get_valid: obs_output_reg_t -> bool).
    Context (local_step_running: local_st -> local_st ).

    (* A machine is running or waiting *)
    Inductive local_machine_state_t :=
    | Running (st: local_st)
    | Waiting.

    Definition is_running (st: local_machine_state_t) : bool :=
      match st with
      | Running _ => true
      | _ => false
      end.

    Record state_t : Type :=
      { state0: local_machine_state_t;
        state1: local_machine_state_t;
        hist_ready_for_job: option Tag;
        turn: turn_t
      }.

    Definition initial_state : state_t :=
      {| state0 := Waiting;
         state1 := Waiting;
         hist_ready_for_job := init_hist_ready_for_job;
         turn := init_turn;
      |}.

    Definition do_local_observations (machine: local_machine_state_t) : option (obs_output_reg_t) :=
      match machine with
      | Running st => Some (local_observe_output_reg st)
      | Waiting => None
      end.

    Definition local_update_after_observations
               (machine: local_machine_state_t)
               : local_machine_state_t :=
        match machine with
        | Running st =>
            let obs := local_observe_output_reg st in
            match output_get_valid obs with
            | true => Waiting
            | false => Running st
            end
        | Waiting => Waiting
        end.
    Scheme Equality for Tag.
    (* Output: do transition at start of next cycle *)
    Definition do_local_step (tag: Tag)
                             (turn: turn_t)
                             (machine: local_machine_state_t)
                             (input: input_t)
                             (ready_for_job: option Tag)
                             : local_machine_state_t :=
      match machine with
      | Running st =>
          let st' := local_step_running st in
          Running st'
      | Waiting =>
          match ready_for_job, input with
          | Some tag', Some req =>
              if Tag_beq tag tag' then
                let st  := local_init_state input tag turn in
                Running st
              else Waiting
          | _, _ => Waiting
          end
      end.

    Definition get_busy (st0 st1: local_machine_state_t) (tag: Tag) : bool :=
      match tag with
      | Tag0 => is_running st0
      | Tag1 => is_running st1
      end.

    Definition get_job_accepted (input: input_t) (ready_for_job: option Tag)
                                : option (Tag * list bool) :=
      match input, ready_for_job with
      | Some req, Some Tag0 => Some (Tag0, req)
      | Some req, Some Tag1 => Some (Tag1, req)
      | _, _ => None
      end.

    Definition ready_for_job_to_maybe (v: option Tag) : list bool :=
      match v with
      | Some Tag0 => [true; false]
      | Some Tag1 => [true; true]
      | None => [false;false]
      end.

    (* Compute ready for job based on state at start of cycle, and history *)
    (* Define moment of exiting as observation at start of cycle *)
    Definition spec_step (st: state_t) (input: input_t)
      : state_t * output_t :=
      let external0 := do_local_observations st.(state0) in
      let external1 := do_local_observations st.(state1) in
      let state0' := local_update_after_observations st.(state0) in
      let state1' := local_update_after_observations st.(state1) in
      let cur_ready_for_job := update_ready_for_job st.(hist_ready_for_job) st.(turn) (get_busy state0' state1') in
      let state0'' := do_local_step Tag0 st.(turn) state0' input cur_ready_for_job in
      let state1'' := do_local_step Tag1 st.(turn) state1' input cur_ready_for_job in
      ({| state0 := state0'';
          state1 := state1'';
          hist_ready_for_job := cur_ready_for_job;
          turn:= negb st.(turn);
       |},
       {| output_observations :=
            {| obs_ready_for_job := ready_for_job_to_maybe cur_ready_for_job;
               obs_output_reg := local_observe_output st.(turn)
                                     (fun tag => match tag with
                                              | Tag0 => external0
                                              | Tag1 => external1
                                              end)
            |};
          output_job_accepted := get_job_accepted input cur_ready_for_job
       |}).


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

End Spec.
