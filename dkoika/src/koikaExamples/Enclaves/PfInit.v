Require Import rv_isolation.Common.
Require Import rv_isolation.RVCore.
Require Import rv_isolation.Memory.
Require Import rv_isolation.SecurityMonitor.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.TypeDefs.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Utils.
Require Import koikaExamples.Enclaves.PfImplDefs.
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koikaExamples.Enclaves.PfInit_sig.
Require Import koikaExamples.Enclaves.PfDefs.
Require Import koikaExamples.Enclaves.PfChain.
Require Import koikaExamples.Enclaves.PfImplHelpers.

Definition reg_pairs :=
  (map (fun x => (reg_to_debug_id x, x)) (@FiniteType.finite_elements _ FiniteType_reg_t)).

Definition invert_reg (reg: debug_id_ty) (default: Impl.reg_t): Impl.reg_t :=
  match find (fun '(rid, _) => beq_dec reg rid) reg_pairs with
  | Some (_, x) => x
  | None => default
  end.

Lemma invert_reg_involutive:
  forall reg default,
  invert_reg (reg_to_debug_id reg) default = reg.
Proof.
  unfold invert_reg. unfold reg_pairs. intros.
  unfold reg_to_debug_id.
  repeat destruct_match; subst.
  - apply find_some in Heqo. propositional; simplify.
    rewrite in_map_iff in Heqo0. propositional; simplify.
    apply Nnat.Nat2N.inj in H1.
    apply FiniteType.finite_index_injective in H1. auto.
  - exfalso. eapply find_none with (x := (reg_to_debug_id reg, reg)) in Heqo.
    + rewrite beq_dec_false_iff in Heqo. auto.
    + rewrite in_map_iff. exists reg. split; auto.
      apply PfHelpers.in_finite_elements.
Qed.
Definition reg_list' := (map reg_to_debug_id (@FiniteType.finite_elements _ FiniteType_reg_t)).

Module SymbPfInit.
  Section WithEnclaveSig.
    Context (enclave_sig: enclave_params_sig).

    Existing Instance SecurityMonitor.FiniteType_reg_t.

    (* Roundabout way for performance *)
    Definition initial_state :=
      TopLevelModuleHelpers.r
        (_core_init0 enclave_sig)
        (_core_init1 enclave_sig)
        Impl.init_mem_turn Impl.init_sm_turn.

    Definition impl_init_file' : file_t :=
      {| file_machines := Single dummy_machine [] ;
        file_assumptions := preprocess_fancy_spreds
                              [(tt,
                                 (* Initialize registers *)
                                {{{ {forall x in reg_list',
                                      impl0.[x] = #(initial_state (invert_reg x (SM SecurityMonitor.clk)))
                                    }
                                }}})];
        file_assertions := preprocess_fancy_spreds
                             ((SymbPfChain.invariant_spreds' enclave_sig impl_final impl_get_field))
      |}.

  End WithEnclaveSig.

End SymbPfInit.

Module Type SMT_ImplInit_sig (EnclaveParams: EnclaveParams_sig).
  Definition file := SymbPfInit.impl_init_file' EnclaveParams.enclave_sig.
  Parameter SMT_ImplInvariant__Init :
    SymbolicInterp.WF_single_file file = true.

End SMT_ImplInit_sig.

(* Module TestImplInit. *)
(*   Require Import koikaExamples.Enclaves.External. *)
(*   Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams. *)

(*   Definition file := Eval vm_compute in (SymbPfInit.impl_init_file' EnclaveParams.enclave_sig). *)
(*   Extraction "TestImplInit.ml" struct_sz vect_t file. *)
(* End TestImplInit. *)

Module PfInit (EnclaveParams: EnclaveParams_sig)
          (SecurityParams: SecurityParams_sig EnclaveParams)
          (* (SimDefs: PfSimDefs EnclaveParams SecurityParams Symbspec) *)
          (ImplDefs: PfImplDefs EnclaveParams SecurityParams)
          (SmtOk: SMT_ImplInit_sig EnclaveParams)
          : PfInit_sig EnclaveParams SecurityParams ImplDefs.
  (* Module Import PfLemmas := PfLemmas EnclaveParams SecurityParams. *)
  Module Import ImplHelpers := ImplHelpers EnclaveParams SecurityParams ImplDefs.
  Import ImplDefs.
  Definition impl_initial_state (dram: dram_t) : impl_state_t :=
    (Machine.initial_state (_core_init0 EnclaveParams.enclave_sig)
                      (_core_init1 EnclaveParams.enclave_sig) Impl.init_mem_turn Impl.init_sm_turn dram).


  Import TopLevelModuleHelpers.
  Lemma WF_initial_mem: forall dram, WF_dram dram -> WF_ext_mem (ExternalMemory.initial_mem dram).
  Proof.
    intros. unfold ExternalMemory.initial_mem.
    constructor; simpl; auto; propositional; try discriminate.
  Qed.

  Ltac basic_cbn :=
    cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat ].
  Lemma WF_init:
    WF_state (SortedRegEnv.to_list reg_type_env)
      (initial_koika_state (_core_init0 EnclaveParams.enclave_sig) (_core_init1 EnclaveParams.enclave_sig)
         Impl.init_mem_turn Impl.init_sm_turn).
  Proof.
    apply PfHelpers.WF_initial_koika_state; auto.
    * apply EnclaveParams.wf_sig.(wf_core_init0 _).
    * apply EnclaveParams.wf_sig.(wf_core_init1 _).
  Qed.
  Lemma init_spec_st_r_eq':
    forall reg init0 init1 mem_turn sm_turn st,
      st.[_id (reg_to_debug_id reg)] = (initial_koika_state init0 init1 mem_turn sm_turn).[_id (reg_to_debug_id reg)] ->
      st.[_id (reg_to_debug_id reg)] = r init0 init1 mem_turn sm_turn reg.
  Proof.
    intros. unfold initial_koika_state in *.
    consider unsafe_get_reg. consider r_get_reg.
    rewrite opt_get_env_from_list in H.
    - rewrite H. auto.
    - eapply nth_error_In. eapply FiniteType.finite_surjective.
  Qed.


  Lemma init_state_eq:
    forall x : debug_id_ty,
    In x reg_list' ->
    (initial_koika_state (_core_init0 EnclaveParams.enclave_sig) (_core_init1 EnclaveParams.enclave_sig)
       Impl.init_mem_turn Impl.init_sm_turn).[_id x] =
    SymbPfInit.initial_state EnclaveParams.enclave_sig (invert_reg x (SM clk)).
  Proof.
    intros * hreg. unfold SymbPfInit.initial_state.
    consider reg_list'. rewrite in_map_iff in hreg. propositional.
    rewrite invert_reg_involutive.
    apply init_spec_st_r_eq'; eauto.
  Qed.

  Lemma init_invariant: forall dram mid_log mem inputs,
    WF_ext_mem mem ->
    Forall
      (fun p : spred =>
       interp_spred
         {|
           pkg_machine := dummy_machine;
           pkg_init_st := machine_koika_st (impl_initial_state dram);
           pkg_sigma := mk_sigma_fn mem inputs;
           pkg_mid_st := None;
           pkg_final_st := machine_koika_st (impl_initial_state dram);
           pkg_mid_ext_log := mid_log;
           pkg_ext_log' := SortedExtFnEnv.empty
         |} p)
      (preprocess_fancy_spreds (SymbPfChain.invariant_spreds' EnclaveParams.enclave_sig impl_final impl_get_field)).
  Proof.
    intros.
    specialize symbolic_evaluate_file_success with (file := SymbPfInit.impl_init_file' EnclaveParams.enclave_sig).
    intros hfile. simpl in hfile.
    unfold symbolic_evaluate_file_success_single in *.
    unfold dummy_interp, dummy_pkg.
    apply hfile; auto.
    - apply SmtOk.SMT_ImplInvariant__Init.
    - clear.
      rewrite forall_preprocess_fancy_spreds_correct.
      constructor; [ | constructor].
      cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat
             SymbPfInit.initial_state invert_reg reg_list].
      apply init_state_eq.
    - constructor.
      + apply WF_mk_sigma_fn; auto.
      + split; auto.
        * apply WF_init.
        * unfold interp_cycle_list'. simpl. rewrite commit_update_empty. reflexivity.
  Qed.


  Theorem ImplInvariant_initial: forall dram,  WF_dram dram -> ImplDefs.ImplInvariant (impl_initial_state dram).
  Proof.
    intros * hdram. unfold impl_initial_state, Machine.initial_state, initial_machine_state.
    consider ExternalMemory.initial_mem.
    assert (ImplInvariant_spreds EnclaveParams.enclave_sig (impl_initial_state dram)) as hspreds.
    { eapply ImplInvariant_spreds_implied with (input := dummy_input_t)
      (mid_st := machine_koika_st (impl_initial_state dram))
      (final_st := machine_koika_st (impl_initial_state dram))
      (ext_log1 := None) (ext_log2 := SortedExtFnEnv.empty).
      - eauto.
      - eapply ImplInvariant_spreds_implies_invariant_spreds'_init'.
        eapply init_invariant.
        eapply WF_initial_mem; eauto.
      - repeat constructor.
        + basic_cbn. intros. vm_compute in H0. clear - H0. discriminate.
        + basic_cbn. intros. vm_compute in H0. clear - H0. discriminate.
    }
    consider ImplInvariant_spreds. destruct hspreds as (core_pre0 & core_pre1 & mem_pre & sm_pre).
    constructor; auto.
    - simpl. unfold strong_WF_state. split.
      + reflexivity.
      + apply  WF_init.
    - simpl. apply WF_initial_mem. auto.
    Unshelve.
    + exact None.
    + exact dummy_input_t.
  Qed.

End PfInit.
