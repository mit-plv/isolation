Require Import koika.Frontend.
Import List.ListNotations.

Module Common.
  Inductive Tag :=
  | Tag0
  | Tag1.

  Definition input_t := option (list bool). (* job_req *)

  Record observations_t : Type :=
    { obs_ready_for_job : list bool; (* TODO: options? *)
      obs_output_reg : list bool (* option? *)
    }.

  Record output_t : Type :=
    { output_observations : observations_t;
      output_job_accepted : option (Tag * list bool (* job_req *) )
    }.

  Definition trace := list output_t.

  Definition reg_in_taint_list' (reg: reg_t) (regs: list reg_t) : Prop :=
    existsb (beq_dec reg) regs = true.

  Definition reg_in_taint_list (tag: Tag) (reg: reg_t) (regs0 regs1: list reg_t) : Prop :=
   match tag with
   | Tag0 => reg_in_taint_list' reg regs0
   | Tag1 => reg_in_taint_list' reg regs1
   end.

End Common.

(*! State machine definitions *)
Section StateMachine.
  Context {state_t: Type}.
  Context {input_t : Type}.
  Context {output_t : Type}.

  (* Main machine *)
  Record machine_t : Type :=
    { m_initial_state: state_t;
      m_step: state_t -> input_t -> state_t * output_t (* Deterministic *)
    }.
End StateMachine.

Section InputMachine.
  Context {state_t: Type}.
  Context {input_t : Type}.
  Context {output_t : Type}.

  Record i_machine_t : Type :=
    { i_initial_state: state_t;
      i_get_output: state_t -> output_t;
      i_step: state_t -> input_t -> state_t
    }.
End InputMachine.

Section FailingIOAutomata.
  Context {state_t: Type}.
  Context {input_t : Type}.
  Context {output_t : Type}.

  Context (machine_initial_state: state_t).
  Context (machine_step: state_t -> input_t -> result (state_t * output_t) unit).
  Context {input_machine_state_t: Type}.
  Context (input_machine: @i_machine_t input_machine_state_t output_t input_t).

  Definition step (st: state_t) (input_st: input_machine_state_t)
                  : result (state_t * input_machine_state_t * output_t) unit :=
    let input := input_machine.(i_get_output) input_st in
    let/res2 st', output := machine_step st input in
    Success (st', input_machine.(i_step) input_st output, output).

  Fixpoint step_n' (n: nat) (st: state_t) (input_st: input_machine_state_t)
    : result (state_t * input_machine_state_t * list output_t) unit  :=
    match n with
    | 0 => Success (st, input_st, [])
    | S n' =>
        let/res3 st', input_st', output_list := step_n' n' st input_st in
        let/res3 st'', input_st'', output := step st' input_st' in
        Success (st'', input_st'', (output_list ++ [output])%list)
    end.

  Definition step_n (n: nat) : result (list output_t) unit :=
    let/res3 _, _, outputs := step_n' n machine_initial_state input_machine.(i_initial_state) in
    Success outputs.

  Lemma rewrite_step_succ_n':
    forall n st input_st,
    step_n' (S n) st input_st =
    let/res3 st', input_st', output_list := step_n' n st input_st in
    let/res3 st'', input_st'', output := step st' input_st' in
    Success (st'', input_st'', (output_list ++ [output])%list).
  Proof.
    auto.
  Qed.

End FailingIOAutomata.

Section SafeIOAutomata.
  Context {state_t: Type}.
  Context {input_t : Type}.
  Context {output_t : Type}.

  Context (machine_initial_state: state_t).
  Context (machine_step: state_t -> input_t -> state_t * output_t).
  Context {input_machine_state_t: Type}.
  Context (input_machine: @i_machine_t input_machine_state_t output_t input_t).

  Definition safe_step (st: state_t) (input_st: input_machine_state_t)
                  : state_t * input_machine_state_t * output_t :=
    let input := input_machine.(i_get_output) input_st in
    let '(st', output) := machine_step st input in
    (st', input_machine.(i_step) input_st output, output).

  Fixpoint safe_step_n' (n: nat) (st: state_t) (input_st: input_machine_state_t)
    : state_t * input_machine_state_t * list output_t :=
    match n with
    | 0 => (st, input_st, [])
    | S n' =>
        let '(st', input_st', output_list) := safe_step_n' n' st input_st in
        let '(st'', input_st'', output) := safe_step st' input_st' in
        (st'', input_st'', (output_list ++ [output])%list)
    end.

  Definition safe_step_n (n: nat) : list output_t :=
    let '(_, _, outputs) := safe_step_n' n machine_initial_state input_machine.(i_initial_state) in
    outputs.

  Lemma rewrite_safe_step_succ_n':
    forall n st input_st,
    safe_step_n' (S n) st input_st =
    let '(st', input_st', output_list) := safe_step_n' n st input_st in
    let '(st'', input_st'', output) := safe_step st' input_st' in
    (st'', input_st'', (output_list ++ [output])%list).
  Proof.
    auto.
  Qed.

End SafeIOAutomata.
