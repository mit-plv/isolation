Require Import rv_cache_isolation.Common.
Require Import rv_cache_isolation.RVCore.
Require Import rv_cache_isolation.Memory.
Require Import rv_cache_isolation.SecurityMonitor.
Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
(* Require Import koikaExamples.EnclaveWithCache.TypeDefs. *)
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.EnclaveWithCache.ExtractionUtils.
Require Import koikaExamples.EnclaveWithCache.ProofUtils.
Require Import koikaExamples.EnclaveWithCache.PfDefs.
Require Import koikaExamples.EnclaveWithCache.ProofCore_symb.
(* Require Import koikaExamples.EnclaveWithCache.SmDefs. *)
Require Import koikaExamples.EnclaveWithCache.SmProofs.
Require Import koikaExamples.EnclaveWithCache.MemoryDefs.
Require Import koikaExamples.EnclaveWithCache.MemoryProofs.
Require Import koikaExamples.EnclaveWithCache.SymbSpec.
Require Import koikaExamples.EnclaveWithCache.PfImplDefs.
Require Import koikaExamples.EnclaveWithCache.PfImplLemmas_sig.
Require Import koikaExamples.EnclaveWithCache.PfSpecDefs.
Require Import koikaExamples.EnclaveWithCache.PfSpecLemmas_sig.
Require Import koikaExamples.EnclaveWithCache.PfSim_sig.
Require Import koikaExamples.EnclaveWithCache.PfSimHelpers.
Require Import koikaExamples.EnclaveWithCache.PfImplHelpers.
Require Import koikaExamples.EnclaveWithCache.PfInit_sig.


Import Utils.PfHelpers.

Ltac custom_unsafe_auto_simplify_structs ::=
  match goal with
  | H: _get_field ?s ?str_fld ?v = Success ?v'
    |- context[unsafe_get_field (unsafe_lookup_dstruct_fields _ (_sid ?s)) (_fld ?s ?str_fld) ?v]  =>
      rewrite _get_field_implies_unsafe_get_field with (1 := H)

  | H :_get_field ?sdef ?_fld ?req = Success ?s
  |- Datatypes.length ?s = _ =>
        let H':= fresh in
        pose proof (_get_field_success sdef _fld req) as H'; simpl in H';
        specialize H' with (2 := eq_refl); assert_pre_and_specialize H'; [ | simplify; auto]
  | H: _get_field ?s ?str_fld ?v = Success ?v',
    H': context[unsafe_get_field (unsafe_lookup_dstruct_fields _ (_sid ?s)) (_fld ?s ?str_fld) ?v] |- _ =>
      rewrite _get_field_implies_unsafe_get_field with (1 := H) in H'
  | H: WF_ext_log _ ?log |- Datatypes.length (unsafe_get_ext_call_from_log ?log ?fn) = _ =>
        solve[eapply WF_ext_log_call_length; eauto]
  end.



Module Pf (EnclaveParams: EnclaveParams_sig)
          (SecurityParams: SecurityParams_sig EnclaveParams)
          (Symbspec: SymbSpec EnclaveParams SecurityParams)
          (* (SimDefs: PfSimDefs EnclaveParams SecurityParams Symbspec) *)
          (ImplDefs: PfImplDefs EnclaveParams SecurityParams)
          (PfImplLemmas: PfImplLemmas_sig EnclaveParams SecurityParams ImplDefs)
          (Spec: Spec_sig EnclaveParams)
          (SpecDefs: PfSpecDefs EnclaveParams SecurityParams Spec)
          (PfSpecLemmas: PfSpecLemmas_sig EnclaveParams SecurityParams Spec SpecDefs)
          (PfSimProofs: PfSimProofs_sig EnclaveParams SecurityParams Symbspec)
          (PfInit: PfInit_sig EnclaveParams SecurityParams ImplDefs).
  (* Module PfSimProofs := PfSimProofs EnclaveParams SecurityParams Symbspec SimDefs. *)

  Module PfLemmas := PfLemmas EnclaveParams SecurityParams .
  Module Import EnclaveParamUtils := EnclaveParamUtils EnclaveParams.
  Module Import ImplHelpers := ImplHelpers EnclaveParams SecurityParams ImplDefs.

  Import SecurityParams.
  Import SecurityParams.Impl.
  Import SecurityParams.Machine.
  Module Impl := FullMachine.

  Import Utils.PfHelpers.
  Import ImplDefs.
  Import SpecDefs.
  Import Spec.
  Import TopLevelModuleHelpers.
  (* Import PfSim. *)

  Theorem impl_step_preserves_impl_inv:
    forall impl_st
    (external_world_state_t: Type)
    (input_machine: @i_machine_t external_world_state_t output_t input_t) ext_st,
    ImplInvariant impl_st ->
    exists impl_st' ext_st' ext_obs' ,
      Impl.step input_machine impl_st  ext_st = Success (impl_st', ext_st', ext_obs') /\
      ImplInvariant impl_st' /\ step_WF_ext_obs impl_st ext_obs' /\
      ext_st' = i_step input_machine ext_st ext_obs'.
  Proof.
    intros * Hinv. unfold Impl.step, ExtractionUtils.Machine.step, StateMachine.step.
    unfold Machine.machine_step_external, Machine.koika_step,
      Machine.koika_step', interp_cycle'.
    eapply PfImplLemmas.impl_step_preserves_impl_inv' with (input := i_get_output input_machine ext_st) in Hinv; propositional; eauto.
    destruct Hinv2. destruct impl_wf_log0.
    unfold SecurityParams.Machine.step. unfold StateMachine.step. unfold SecurityParams.Machine.machine_step_external.
    unfold SecurityParams.Machine.koika_step.
    unfold SecurityParams.Machine.koika_step'.
    unfold interp_cycle'.
    do 3 eexists.
    setoid_rewrite Hinv0. simpl.
    unfold ExternalMemory.update_memory.
    setoid_rewrite impl_mem_update0.
    setoid_rewrite (impl_cache_update0 imem CoreId0).
    setoid_rewrite (impl_cache_update0 dmem CoreId0).
    setoid_rewrite (impl_cache_update0 imem CoreId1).
    setoid_rewrite (impl_cache_update0 dmem CoreId1).
    simpl.
    split_ands_in_goal.
    - eauto.
    - destruct mem_st'.  simpl.
      match goal with
      | |- context[ExternalMemory.Build_external_mem_t _ ?s] =>
          assert (ext_l1_caches = s)
      end.
      { apply functional_extensionality. intro.
        apply functional_extensionality. intro.
        repeat destruct_match; auto.
      }
      rewrite H in impl_invariant_post0.
      auto.
    - auto.
    - auto.
  Qed.

  Definition get_metadata_valid (data: option (list bool)) :=
    match data with
    | Some data =>
      match _get_field (metadata_sig) "valid" data with
      | Success req => req
      | _ => Ob
      end
    | None => Ob
    end.

  (* Stronger than necessary *)
  Definition ext_mem_metadata_sim (impl_meta spec_meta: ExternalMemory.external_metadata_t) : Prop :=
    impl_meta = spec_meta.
    (* { ext_metadata_sim__resp: impl_meta.(ExternalMemory.ext_metadata_resp) = spec_meta.(ExternalMemory.ext_metadata_resp); *)
    (*   ext_metadata_sim__valid: forall n, get_metadata_valid (impl_meta.(ExternalMemory.ext_metadata) n) = *)
    (*                               get_metadata_valid (spec_meta.(ExternalMemory.ext_metadata) n); *)
    (*   ext_metadata_sim__data: forall n, get_metadata_valid (impl_meta.(ExternalMemory.ext_metadata) n) = Ob~1 -> *)
    (*                              impl_meta.(ExternalMemory.ext_metadata) n = *)
    (*                              spec_meta.(ExternalMemory.ext_metadata) n *)
    (* }. *)

  Record cache_ghost_state :=
    { ghost_cache_req_line : option addr_t;
    }.

  Definition cache_resp_sim (impl_cache spec_cache: ExternalMemory.external_cache_pair_t)
                            : Prop :=
        impl_cache.(ExternalMemory.ext_pair_cache).(ExternalMemory.ext_cache_resp) =
        spec_cache.(ExternalMemory.ext_pair_cache).(ExternalMemory.ext_cache_resp).

        (* match impl_cache.(ExternalMemory.ext_pair_cache).(ExternalMemory.ext_cache_resp), *)
        (*       spec_cache.(ExternalMemory.ext_pair_cache).(ExternalMemory.ext_cache_resp) with *)
        (* | Some impl_resp, Some spec_resp => *)
        (*     (* If req /\ addr valid in metadata, then resp must be equal. *) *)
        (*     match ghost_st.(ghost_cache_req_line) with *)
        (*     | Some addr => *)
        (*         get_metadata_valid (impl_cache.(ExternalMemory.ext_pair_meta).(ExternalMemory.ext_metadata) (to_N addr)) = Ob~1 -> *)
        (*         impl_resp = spec_resp *)
        (*     | None => False *)
        (*     end *)
        (* | None, None => True *)
        (* | _, _ => False *)
        (* end. *)

  Record ext_mem_cache_sim (impl_cache spec_cache: ExternalMemory.external_cache_pair_t)
                           (* (ghost_st: cache_ghost_state)  *): Prop :=
    { ext_cache_sim__meta: ext_mem_metadata_sim impl_cache.(ExternalMemory.ext_pair_meta)
                                              spec_cache.(ExternalMemory.ext_pair_meta);
      ext_cache_sim__cache_resp: cache_resp_sim impl_cache spec_cache (* ghost_st *);
      ext_cache_sim__cache:
      forall n,
        impl_cache.(ExternalMemory.ext_pair_cache).(ExternalMemory.ext_cache) n
        = spec_cache.(ExternalMemory.ext_pair_cache).(ExternalMemory.ext_cache) n;

      (* ext_cache_sim__cache: forall n, *)
      (*   get_metadata_valid (impl_cache.(ExternalMemory.ext_pair_meta).(ExternalMemory.ext_metadata) n) = Ob~1 -> *)
      (*   impl_cache.(ExternalMemory.ext_pair_cache).(ExternalMemory.ext_cache) n *)
      (*   = spec_cache.(ExternalMemory.ext_pair_cache).(ExternalMemory.ext_cache) n; *)
    }.

  (*! BEGIN SIM *)
  Record ext_mem_sim (core_id: ind_core_id) (config: enclave_config)
                       (impl_mem spec_mem: ExternalMemory.external_mem_t) (cycles: nat)
                       (* (cache_ghost_st: mem_type -> cache_ghost_state) *)
                       : Prop :=
      { ext_mem_sim__dram: forall addr, addr_in_config EnclaveParams.enclave_sig addr config ->
                                 impl_mem.(ExternalMemory.ext_main_mem).(ExternalMemory.ext_mem) addr
                                  = spec_mem.(ExternalMemory.ext_main_mem).(ExternalMemory.ext_mem) addr;
        ext_mem_sim__ext: is_mem_core_read_turn' core_id cycles = true ->
                        impl_mem.(ExternalMemory.ext_main_mem).(ExternalMemory.ext_resp) = spec_mem.(ExternalMemory.ext_main_mem).(ExternalMemory.ext_resp);
        ext_mem_sim__caches: forall cache, ext_mem_cache_sim (impl_mem.(ExternalMemory.ext_l1_caches) cache core_id)
                                                      (spec_mem.(ExternalMemory.ext_l1_caches) cache core_id)
                                                      (* (cache_ghost_st cache) *);
      }.


  Record running_sim (core_id: ind_core_id) (impl_st: machine_state_t)
                     (config: enclave_config) (spec_machine: machine_state_t) (cycles: nat) : Prop :=
    { running_sim__ghost: machine_st_to_ghost_core (machine_koika_st impl_st) core_id SecurityParams.extract_rf = GhostCoreState_Enclave config
    ; running_sim__pre: forall input, SymbSimDefs.SimPre EnclaveParams.enclave_sig core_id (machine_koika_st impl_st)
                                              (machine_koika_st spec_machine)
                                              (mk_sigma_fn (machine_mem_st impl_st) input)
                                              (mk_sigma_fn (machine_mem_st spec_machine) (filter_input (Some config) input))
      ; running_sim__ext_mem: ext_mem_sim core_id config impl_st.(machine_mem_st) spec_machine.(machine_mem_st) cycles
                                          (* (get_cache_ghost_state core_id (machine_koika_st impl_st)) *)
      ; running_sim__wf_st: strong_WF_state reg_type_env (machine_koika_st spec_machine)
      }.

  Hint Resolve running_sim__wf_st: modularity.
  Definition impl_is_waiting (core_id: ind_core_id) (impl_st: impl_state_t) (new: enclave_config) (rf: reg_file_t) : Prop :=
    machine_st_to_ghost_core (machine_koika_st impl_st) core_id SecurityParams.extract_rf = GhostCoreState_Waiting new rf.

  Definition machine_sim (core_id: ind_core_id) (impl_st: impl_state_t) (st: @core_state_t machine_state_t) (cycles: nat) : Prop :=
      match st with
      | CoreState_Enclave machine_state config => running_sim core_id impl_st config machine_state cycles
      | CoreState_Waiting new rf _ => impl_is_waiting core_id impl_st new rf
      end.
  Definition mem_map_equivalent (impl_dram: dram_t)
                                (spec_configs: ind_core_id -> option enclave_config)
                                (spec_map: memory_map_t) : Prop :=
       forall region addr,
       addr_in_region EnclaveParams.enclave_sig region addr = true ->
       (forall core, region_in_option_config region (spec_configs core) = false) ->
       impl_dram addr = spec_map region addr.
  Definition spec_cycles_to_bits (cycles: nat) : list bool :=
    Bits.of_nat 2 (Nat.modulo cycles 4).

  Record Sim (impl_st: impl_state_t) (spec_st: spec_state_t) : Prop :=
  { Sim_impl_invariant: ImplInvariant impl_st
  ; Sim_spec_invariant: SpecInvariant spec_st
  ; Sim_machine_state: forall core_id, machine_sim core_id impl_st
                                          (spec_st.(machine_state) core_id)
                                          spec_st.(cycles)
  ; Sim_memory_regions: mem_map_equivalent impl_st.(machine_mem_st).(ExternalMemory.ext_main_mem).(ExternalMemory.ext_mem)
                                           (get_spec_configs spec_st)
                                           spec_st.(mem_regions)
  ; Sim_cycles_mem: impl_st.(machine_koika_st).[_rid (Memory Memory.turn)] =
                        spec_cycles_to_bits spec_st.(cycles)
  ; Sim_cycles_sm: impl_st.(machine_koika_st).[_rid (SM SecurityMonitor.clk)] =
                       [Nat.odd spec_st.(cycles)]
  }.
  Definition impl_initial_state (dram: dram_t) : impl_state_t :=
    (Machine.initial_state (_core_init0 EnclaveParams.enclave_sig)
                      (_core_init1 EnclaveParams.enclave_sig) Impl.init_mem_turn Impl.init_sm_turn dram).
  Definition spec_initial_state (dram: dram_t) : spec_state_t :=
    (Spec.initial_state SecurityParams.spin_up_machine (dram_to_mem_map EnclaveParams.enclave_sig dram)).
  Definition initial_params core :=
    match core with
    | CoreId0 => _core_init0 EnclaveParams.enclave_sig
    | CoreId1 => _core_init1 EnclaveParams.enclave_sig
    end.

  Definition initial_config core :=
    match core with
    | CoreId0 => initial_enclave_config0
    | CoreId1 => initial_enclave_config1
    end.
  Definition initial_rf core :=
    match core with
    | CoreId0 => (_core_init0 EnclaveParams.enclave_sig).(machine_rf)
    | CoreId1 => (_core_init1 EnclaveParams.enclave_sig).(machine_rf)
    end.
  Import SymbSimDefs.
  Ltac init_interp ::=
    repeat
      match goal with
      | |- dummy_interp _ _ _ _ _ _ => unfold dummy_interp, dummy_pkg
      | |- Forall (fun '(_, p) => interp_fancy_spred _ _) _ => rewrite <- forall_preprocess_fancy_spreds_correct
      | |- Forall (fun '(_, p) => interp_fancy_spred2 _ _ _) _ => rewrite <- forall_preprocess_fancy_spreds_correct2
      end.
  Ltac basic_cbn :=
    cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat filter_input].
  Lemma ImplInvariant_initial: forall dram,  WF_dram dram -> ImplInvariant (impl_initial_state dram).
  Proof.
    apply PfInit.ImplInvariant_initial.
  Qed.

  Lemma rewrite_init_spec_koika_st:
    forall core cycles spec_dram params,
      (machine_koika_st
         (spin_up_machine core cycles params  spec_dram)) =
        (init_spec_koika_st core params
           (of_nat 2 (Nat.modulo cycles 4)) [Nat.odd cycles] ).
  Proof.
    destruct core; reflexivity.
  Qed.


  Lemma rewrite_init_spec_mem_st:
    forall core cycles spec_dram spec_config,
      (machine_mem_st
         (spin_up_machine core cycles spec_config spec_dram )) =
        ExternalMemory.initial_mem spec_dram.
  Proof.
    destruct core; reflexivity.
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

  Lemma extract_rf_initial:
    forall core dram,
    initial_rf core = extract_rf (impl_initial_state dram) core.
  Proof.
    intros. unfold impl_initial_state, extract_rf.
    apply functional_extensionality. intros.
    assert (initial_rf core = (fun _ => Some (zeroes 32))) as hrf.
    { destruct core.
      - pose proof (EnclaveParams.wf_sig.(wf_rf0 _)). auto.
      - pose proof (EnclaveParams.wf_sig.(wf_rf1 _)). auto.
    }
    rewrite hrf. destruct_match; auto.
    f_equal. unfold Machine.initial_state. unfold initial_machine_state. unfold machine_koika_st.
    consider _rid.
    erewrite init_spec_st_r_eq'; eauto.
    consider initial_rf.
    unfold r. destruct core.
    - unfold core_reg. rewrite hrf. reflexivity.
    - unfold core_reg. rewrite hrf. reflexivity.
  Qed.

  Lemma impl_init_st_r_eq:
    forall reg dram,
      (machine_koika_st (impl_initial_state dram)).[_id (reg_to_debug_id reg)] =
      r (_core_init0 EnclaveParams.enclave_sig) (_core_init1 EnclaveParams.enclave_sig)
        Impl.init_mem_turn Impl.init_sm_turn reg.
  Proof.
    intros. apply init_spec_st_r_eq'. auto.
  Qed.
    Existing Instance SecurityMonitor.FiniteType_reg_t.
  Arguments addr_in_region  : simpl never.
  Lemma addr_in_config_implies_get_enclave_dram:
    forall addr config dram,
    EnclaveParamUtils.addr_in_config addr config ->
    dram addr =
    get_enclave_dram EnclaveParams.enclave_sig (dram_to_mem_map EnclaveParams.enclave_sig dram)
       config addr.
  Proof.
    intros * haddr. unfold EnclaveParamUtils.addr_in_config in *.
    propositional. consider get_enclave_dram.
    pose proof EnclaveParams.pf_disjoint_configs as hdisjoint. consider wf_disjoint_configs.
    repeat destruct_match; auto; simplify;
    repeat match goal with
    | H: addr_in_region _ _ ?addr = true,
      H1: addr_in_region _ _ ?addr = true |- _ => pose proof (hdisjoint _ _ _ H H1); subst; clear H
    | H: _ && _ = true |- _ => rewrite andb_true_iff in H
    | _ => progress propositional
    end; unfold dram_to_mem_map, filter_dram; repeat simpl_match; auto.
    consider region_in_config.
    destruct config; simpl in *.
    destruct region; simpl in *; simplify.
    - congruence.
    - destruct id; rewrite haddr2 in *; simpl in *; congruence.
  Qed.
  Arguments filter_input : simpl never.
  Lemma ext_mem_cache_sim_refl:
    forall c , ext_mem_cache_sim c c.
  Proof.
    intros. constructor; reflexivity.
  Qed.

  Lemma spec_running_sim_init:
    forall core dram,
      WF_dram dram ->
      running_sim core (impl_initial_state dram) (initial_config core)
        (spin_up_machine core 0 (initial_params core)
           (get_enclave_dram EnclaveParams.enclave_sig (dram_to_mem_map EnclaveParams.enclave_sig dram)
              (initial_config core)) ) 0.
  Proof.
    intros * hwf_dram. constructor; auto.
    - unfold machine_st_to_ghost_core. destruct_match; simplify.
      + exfalso.
        destruct core; vm_compute in Heqb; discriminate.
      + f_equal. unfold initial_config.
        unfold impl_initial_state. unfold Machine.initial_state. simpl. unfold initial_koika_state.
        unfold unsafe_get_reg, r_get_reg.
        setoid_rewrite opt_get_env_from_list.
        2: { destruct core; solve_In_to_find. } simpl.
        unfold opt_enclave_config_to_enclave_data.
        pose proof (EnclaveParams.wf_sig.(wf_config0 _ )) as hconfig0.
        pose proof (EnclaveParams.wf_sig.(wf_config1 _ )) as hconfig1. consider @is_some.
        propositional. unfold initial_enclave_config0, initial_enclave_config1. repeat simpl_match.
        destruct core; rewrite PfHelpers.enclave_data_to_config_involutive; auto.
    - intros.
      repeat rewrite rewrite_init_spec_koika_st.
      rewrite rewrite_init_spec_mem_st.
      assert (ImplInvariant (impl_initial_state dram)) as hinv by (apply ImplInvariant_initial; auto).
      apply SimPre__init_spec; auto.
      + rewrite<-extract_rf_initial. destruct core; reflexivity.
      + consider initial_config. unfold _smrid, _rid.
        rewrite impl_init_st_r_eq.
        pose proof (EnclaveParams.wf_sig.(wf_config0 _ )) as hconfig0.
        pose proof (EnclaveParams.wf_sig.(wf_config1 _ )) as hconfig1. consider @is_some.
        simpl. consider opt_enclave_config_to_enclave_data.
        consider initial_enclave_config0. consider initial_enclave_config1.
        propositional. repeat simpl_match. simpl.
        destruct core; rewrite PfHelpers.enclave_data_to_config_involutive; auto.
      + consider initial_config. consider initial_enclave_config0. consider initial_enclave_config1.
        pose proof (EnclaveParams.wf_sig.(wf_config0 _ )) as hconfig0.
        pose proof (EnclaveParams.wf_sig.(wf_config1 _ )) as hconfig1. consider @is_some.
        consider initial_params.
        propositional. destruct core; repeat simpl_match; auto.
      + intros.
        apply in_map_iff in H. propositional.
        setoid_rewrite impl_init_st_r_eq.
        rewrite<-beq_dec_iff with (EQ := EqDec_bits).
        revert H2. revert x. rewrite<-forallb_forall. destruct core; vm_reflect.
      + intros.
        apply in_map_iff in H. propositional.
        setoid_rewrite impl_init_st_r_eq.
        rewrite<-beq_dec_iff with (EQ := EqDec_bits).
        revert H2. revert x. rewrite<-forallb_forall. destruct core; vm_reflect.
      + intros.
        apply in_map_iff in H. propositional.
        setoid_rewrite impl_init_st_r_eq.
        rewrite<-beq_dec_iff with (EQ := EqDec_bits).
        revert H2. revert x. rewrite<-forallb_forall. destruct core; vm_reflect.
      + intros. consider SMSymbDefs._cid. consider _mid. consider _smid. simpl in H.
        split_ors_in H; auto; subst; setoid_rewrite impl_init_st_r_eq; try reflexivity.
        destruct core; reflexivity.
      + unfold _crid. setoid_rewrite impl_init_st_r_eq. destruct core; reflexivity.
      + intros. consider SMSymbDefs._cid. consider _mid. consider _smid. simpl in H.
        split_ors_in H; auto; subst; setoid_rewrite impl_init_st_r_eq; try reflexivity.
        destruct core; reflexivity.
      + setoid_rewrite impl_init_st_r_eq. destruct core; reflexivity.
      + consider _smrid. setoid_rewrite impl_init_st_r_eq. destruct core; vm_reflect.
      + consider _smrid. setoid_rewrite impl_init_st_r_eq. simpl.
        pose proof (EnclaveParams.wf_sig.(wf_config0 _ )) as hconfig0.
        pose proof (EnclaveParams.wf_sig.(wf_config1 _ )) as hconfig1. consider @is_some.
        simpl. consider opt_enclave_config_to_enclave_data. propositional; repeat simpl_match.
        destruct core;
          setoid_rewrite PfHelpers.enclave_config_to_valid_enclave_data_valid; auto.
    - constructor.
      + intros * hconfig; simpl.
        unfold spin_up_machine. destruct core; simpl.
        * simpl in *. apply addr_in_config_implies_get_enclave_dram. auto.
        * simpl in *. apply addr_in_config_implies_get_enclave_dram. auto.
      + destruct core; reflexivity.
      + intros. simpl. rewrite rewrite_init_spec_mem_st.
        simpl.
       apply ext_mem_cache_sim_refl.
    - unfold strong_WF_state. unfold spin_up_machine. split.
      + destruct core; reflexivity.
      + destruct core; simpl;  apply PfHelpers.WF_initial_koika_state; auto; simpl.
        * apply EnclaveParams.wf_sig.(wf_core_init0 _).
        * apply EnclaveParams.wf_sig.(wf_core_init1 _).
  Qed.
  Lemma wf_dram_implies_wf_mem_regions: forall dram,
      WF_dram dram ->
      wf_mem_regions (dram_to_mem_map EnclaveParams.enclave_sig dram).
  Proof.
    intros * hwf_dram. consider WF_dram.
    unfold dram_to_mem_map.
    constructor. unfold filter_dram. intros. auto.
    unfold WF_dram. intros. bash_destruct H; propositional; eauto.
  Qed.
  Lemma spec_disjoint_init_configs: forall dram, disjoint_option_configs' (spec_initial_state dram).
  Proof.
    - unfold disjoint_option_configs'. simpl.
      pose proof (EnclaveParams.wf_sig.(wf_init_configs _))  as hdisjoint. consider wf_opt_disjoint_configs.
      pose proof (EnclaveParams.wf_sig.(wf_config0 _ )) as hconfig0.
      pose proof (EnclaveParams.wf_sig.(wf_config1 _ )) as hconfig1.
      consider initial_enclave_config0. consider initial_enclave_config1.
      consider  @is_some. propositional. repeat simpl_match.  auto.
  Qed.

  Lemma SpecInvariant_initial: forall dram, WF_dram dram -> SpecInvariant (spec_initial_state dram).
  Proof.
    intros * hdram.
    constructor.
    - pose proof PfSpecLemmas.spec_running_new_machine as Hspin. consider spin_up_machine.
      unfold spec_machine_invariant. intros. specialize (Hspin core).
      unfold spec_initial_state, initial_state. simpl.
      destruct core; consider initial_enclave_config0; consider initial_enclave_config1.
      + pose proof (EnclaveParams.wf_sig.(wf_config0 _ )) as hconfig0. consider @is_some.
        pose proof (EnclaveParams.wf_sig.(wf_core_init0 _)) as hpc0. consider @is_some.
        destruct _core_init0. propositional. simpl in hconfig1. subst.
        apply Hspin with (cycles := 0); auto.
        apply wf_dram_implies_wf_mem_regions; auto.
      + pose proof (EnclaveParams.wf_sig.(wf_config1 _ )) as hconfig1. consider @is_some.
        pose proof (EnclaveParams.wf_sig.(wf_core_init1 _)) as hpc1. consider @is_some.
        destruct _core_init1. propositional. simpl in hconfig0. subst.
        apply Hspin with (cycles := 0); auto.
        apply wf_dram_implies_wf_mem_regions; auto.
    - apply spec_disjoint_init_configs.
    - constructor. simpl. intros.
      apply wf_dram_implies_wf_mem_regions. auto.
  Qed.


  Lemma InitialSim : forall dram, WF_dram dram -> Sim (impl_initial_state dram) (spec_initial_state dram).
  Proof.
    intros. constructor.
    - apply ImplInvariant_initial; auto.
    - apply SpecInvariant_initial; auto.
    - intros. unfold machine_sim, spec_initial_state, initial_state, cycles, machine_state.
      destruct core_id; apply spec_running_sim_init; auto.
    - unfold mem_map_equivalent. simpl.
      unfold dram_to_mem_map, filter_dram. intros. simpl_match. reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Hint Resolve @Sim_spec_invariant : solve_invariants.
    Lemma spec_step_increment_cycles:
      forall spec_st input spec_st' output,
      spec_step SecurityParams.local_step_fn0 SecurityParams.local_step_fn1 SpecParams.can_start_fn SecurityParams.spin_up_machine SecurityParams.extract_dram SecurityParams.extract_rf spec_st input = (spec_st', output) ->
      (cycles spec_st')=(cycles spec_st+1).
    Proof.
      unfold spec_step. intros . destruct_match_pairs. simplify. auto.
    Qed.

Record local_output_sim (impl_out spec_out: external_observations_t) (config: option enclave_config):Prop:=
  { local_output_sim_wf_impl: wf_external_observations impl_out;
    local_output_sim_wf_spec: wf_external_observations spec_out;
    local_output_sim_wf_spec_config: wf_spec_output_config spec_out config;
    local_output_sim_sim:
      match config with
        | Some config =>
              (config_ext_uart config = true ->
                 (obs_uart_write impl_out = obs_uart_write spec_out) /\
                     (obs_uart_read impl_out = obs_uart_read spec_out)) /\
              (config_ext_led config = true ->
                     (obs_led impl_out = obs_led spec_out)) /\
              (config_ext_finish config = true ->
                     (obs_finish impl_out = obs_finish spec_out))
        | None => True
        end
  }.
Notation addr_in_config := (addr_in_config EnclaveParams.enclave_sig).

Definition dram_sim_at_config config (impl_mem spec_mem: dram_t) :=
    forall (addr: N), addr_in_config addr config ->
    impl_mem addr = spec_mem addr.

Definition step_memory_update_sim
  {external_world_state_t : Type}
  (core: ind_core_id) (core_st: core_state_t) impl_mem'
  (input_machine: @i_machine_t external_world_state_t output_t input_t)
  (ext_st: external_world_state_t) :=
  match core_st with
  | CoreState_Enclave koika_st config =>
    let '(m, obs) := spec_step_core core (CoreState_Enclave koika_st config)
           (i_get_output input_machine ext_st) koika_st in
    dram_sim_at_config config (ExternalMemory.ext_mem impl_mem')
                     (ExternalMemory.ext_mem ((ExternalMemory.ext_main_mem) (machine_mem_st m)))
  | CoreState_Waiting _ _ _ => True
  end.

Definition machine_step impl_st output schedule :=
  interp_scheduler (mk_sigma_fn (machine_mem_st impl_st) output)
                   id_int_fns id_struct_defs
                   (machine_koika_st impl_st) Impl.id_rules schedule.

Definition impl_step {external_world_state_t : Type} impl_st (ext_st: external_world_state_t)
  (input_machine: @i_machine_t external_world_state_t output_t input_t) :=
  interp_scheduler (mk_sigma_fn (machine_mem_st impl_st) (i_get_output input_machine ext_st))
                   id_int_fns id_struct_defs
                   (machine_koika_st impl_st) Impl.id_rules schedule.

Definition SimPreInvariants
  (core: ind_core_id)
  (impl_st spec_st: Environments.state_t)
  (impl_sigma spec_sigma: @ext_sigma_t N) : Prop :=
        Forall (fun '(_, p) => interp_fancy_spred2
                    {| pkg_machine := impl_machine;
                       pkg_init_st := impl_st; pkg_mid_st := None; pkg_final_st := impl_st; (* don't care *)
                       pkg_sigma := impl_sigma; pkg_mid_ext_log := None;
                       pkg_ext_log' := SortedExtFnEnv.empty; (* don't care *)
                    |}
                    {| pkg_machine := SymbSpecDefs.spec_machine;
                       pkg_init_st := spec_st; pkg_mid_st := None; pkg_final_st := spec_st; (* don't care *)
                       pkg_sigma := spec_sigma; pkg_mid_ext_log := None;
                       pkg_ext_log' := SortedExtFnEnv.empty; (* don't care *)
                    |} p)
    (SymbSimDefs.sim_invariants EnclaveParams.enclave_sig core impl_init spec_init impl_get_field spec_get_field).

Record SimPost (core: ind_core_id)
               (impl_st impl_st': impl_state_t)
               (spec_st spec_st': machine_state_t)
               (config: enclave_config)
               (impl_out: Log_t) (spec_out: local_observations_t) (cycles: nat)
               : Prop :=
  { SimPost__WF_Impl: strong_WF_state reg_type_env (machine_koika_st impl_st');
    SimPost__WF_Spec: strong_WF_state reg_type_env (machine_koika_st spec_st');
    SimPost__Invariants: forall input, SimPreInvariants core (machine_koika_st impl_st') (machine_koika_st spec_st')
                                 (mk_sigma_fn (machine_mem_st impl_st') input)
                                 (mk_sigma_fn (machine_mem_st spec_st') (filter_input (Some config) input));
    SimPost__Pre: forall input, obs_exit_enclave spec_out core = None ->
                         SymbSimDefs.SimPre EnclaveParams.enclave_sig core (machine_koika_st impl_st') (machine_koika_st spec_st')
                                 (mk_sigma_fn (machine_mem_st impl_st') input)
                                 (mk_sigma_fn (machine_mem_st spec_st') (filter_input (Some config) input));
    SimPost__config:
        _unsafe_get_field (enclave_data) ("valid")
                           (machine_koika_st impl_st).[_rid (SM (enc_data core))] = Ob~1 ->
        _unsafe_get_field (enclave_data) ("valid")
                           (machine_koika_st impl_st').[_rid (SM (enc_data core))] = Ob~1 ->
        (machine_koika_st impl_st).[_rid (SM (enc_data core))] = (machine_koika_st impl_st').[_rid (SM (enc_data core))] /\
        (machine_koika_st impl_st').[_rid (SM (state core))] <> (_enum enum_core_state "Waiting");
    (* SimPost__mem: MemProof.custom_SimPostStepMem core (machine_koika_st impl_st') (Log__ext impl_out) *)
    (*                                                 (machine_koika_st spec_st') config; *)
    SimPost__uart: config_ext_uart config = true ->
                 obs_uart_write (get_ext_observations (Log__ext impl_out)) = obs_uart_write (obs_ext spec_out) /\
                 obs_uart_read (get_ext_observations (Log__ext impl_out)) = obs_uart_read (obs_ext spec_out);
    SimPost__led: config_ext_led config = true ->
                obs_led (get_ext_observations (Log__ext impl_out)) = obs_led (obs_ext spec_out);
    SimPost__finish: config_ext_finish config = true ->
                obs_finish (get_ext_observations (Log__ext impl_out)) = obs_finish (obs_ext spec_out);
    SimPost__ext_mem:
      ext_mem_sim core config (machine_mem_st impl_st') (machine_mem_st spec_st') (cycles)
                  (* (get_cache_ghost_state core (machine_koika_st impl_st')) *)
  }.

Definition dummy_input : input_t :=
  {| input_ext_uart_write := fun _ => [];
    input_ext_uart_read := fun _ => [];
    input_ext_led := fun _ => [];
    input_ext_finish := fun _ => []

  |}.
Hint Resolve @Sim_impl_invariant : solve_invariants.
Hint Resolve @Sim_cycles_sm : solve_invariants.
Hint Resolve SpecInv_config : solve_invariants.
Hint Resolve spec_disjoint_configs: solve_invariants.
Import PfDefs.
Import PfSimProofs.
Import Pf.PfLemmas.
Ltac custom_unsafe_auto_simplify_structs ::=
  match goal with
  | H:WF_ext_log _ ?log
    |- Datatypes.length (_unsafe_get_ext_call_from_log ?log ?fn) = _ => solve
    [ eapply WF_ext_log_call_length; eauto ]

  end.
Ltac custom_simplify :=
  repeat match goal with
  | H:match ?v with
      | Success _ => _
      | Failure _ => False
      end |- _ => match_outermost_in H
  | _ => progress simplify
  end.
(*! TODO_MOVE *)

(*! END TODO_MOVE *)
Import SecurityParams.
Hint Resolve SpecInv_ExtMem.
Hint Resolve Sim_impl_invariant: modularity.
Hint Resolve ImplInv_WF_state: modularity.
Hint Resolve ImplInv_WF_ext_mem : modularity.
Hint Resolve WF_mk_sigma_fn: modularity.
Hint Resolve strong_WF_state_weaken: modularity.
Hint Resolve tt: solve_invariants.

Hint Resolve Sim_cycles_mem : modularity.
Ltac specialize_spec_sim _core fn HPre HPost impl_step spec_step _ghost hwf_impl' hwf_spec' hwf_impl_ext' hwf_spec_ext' :=
    pose proof fn as HPost; unfold sim_interp_scheduler_satisfies_spec in HPost;
    specialize HPost with (core := _core);
    match type of impl_step with
    | interp_scheduler ?sigma _ _ ?st ?rules ?sched  = Success ?log=>
        specialize HPost  with (impl_sigma := sigma) (impl_st := st) (impl_log := log)
    end;
    match type of spec_step with
    | interp_scheduler ?sigma _ _ ?st ?rules ?sched  = Success ?log=>
        specialize HPost with (spec_sigma := sigma) (spec_st := st) (spec_log := log)
    end;
    match type of HPost with
    | _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?impl = Success _ -> ?spec = Success _ -> _ =>
      match type of impl_step with
      | ?impl0 = Success ?log=>
          replace (impl) with (impl0) in HPost
              (* by (apply interp_scheduler_setoid_eq; repeat constructor) *)
      end;
      [ match type of spec_step with
        | ?spec0 = Success ?log=>
          replace (spec) with (spec0) in HPost
        end | ];
      [ specialize HPost with (8 := impl_step) (9 := spec_step);
        do 5 (assert_pre_and_specialize HPost; [ solve[eauto with solve_invariants; eauto with modularity] | ]);
        do 2 (assert_pre_and_specialize HPost; [ vm_reflect| ]);
        assert_pre_as HPre HPost;
          [ | specialize HPost with (1 := HPre); destruct HPost as (hwf_impl' & hwf_spec' & hwf_impl_ext' & hwf_spec_ext' & HPost)]
       | | ]
    end.
Lemma machine_st_to_ghost_core_enclave:
  forall st core config,
    machine_st_to_ghost_core st core SecurityParams.extract_rf = GhostCoreState_Enclave config ->
    config = (unsafe_enclave_data_to_config st.[_rid (SM (enc_data core))]).
Proof.
  intros. consider machine_st_to_ghost_core.
  bash_destruct H.
Qed.
Ltac init_interp_in H:=
  repeat match type of H with
  | dummy_interp _ _ _ _ _ _ =>
      unfold dummy_interp, dummy_pkg in H
  | Forall (fun '(_, p) => interp_fancy_spred _ _) _  =>
    rewrite<-forall_preprocess_fancy_spreds_correct in H
  | Forall (fun '(_, p) => interp_fancy_spred2 _ _ _) _  =>
    rewrite<-forall_preprocess_fancy_spreds_correct2 in H
  end.
Ltac init_interp :=
  repeat match goal with
  | |- dummy_interp _ _ _ _ _ _ =>
      unfold dummy_interp, dummy_pkg
  | |- Forall (fun '(_, p) => interp_fancy_spred _ _) _  =>
    rewrite<-forall_preprocess_fancy_spreds_correct
  | |- Forall (fun '(_, p) => interp_fancy_spred2 _ _ _) _  =>
    rewrite<-forall_preprocess_fancy_spreds_correct2
  end.

Import SymbSimDefs.
Lemma SimPost_implies_SimPreInvariants:
  forall core impl_koika spec_koika impl_koika' spec_koika' impl_sigma spec_sigma impl_sigma' spec_sigma' impl_log spec_log,
  SimPost EnclaveParams.enclave_sig core impl_koika spec_koika impl_koika' spec_koika' impl_sigma spec_sigma impl_log spec_log ->
  SimPreInvariants  core impl_koika' spec_koika' impl_sigma' spec_sigma'.
Proof. (* DONE *)
  intros * hpost. consider SymbSimDefs.SimPost.
  consider SimPreInvariants.
  unfold sim_post_conds in *. rewrite Forall_app in *. propositional. clear - hpost0.
  init_interp.
  init_interp_in hpost0.
  rewrite Lift_Forall with (g := replace_sval_in_spred_base (fn_replace_impl_init_reg_with_final)).
  2: { intros. apply replace_spred2_impl_init_reg_with_final_correct. auto. }
  rewrite Lift_Forall with (g := replace_sval_in_spred_base (fn_replace_spec_init_reg_with_final)).
  2: { intros. apply replace_spred2_spec_init_reg_with_final_correct. auto. }
  destruct core; change_Forall_lists1 hpost0;
    revert hpost0; eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
Qed. (* DONE *)
Lemma mem_push_request_sim_preserved:
  forall req impl_mem_st spec_mem_st impl_mem_st' spec_mem_st' config,
  ExternalMemory.mainmem__ext req impl_mem_st = Success impl_mem_st' ->
  ExternalMemory.mainmem__ext req spec_mem_st = Success spec_mem_st' ->
  match get_valid_addr_from_push_req req with
  | Some addr => addr_in_config (to_N addr) config
  | None => True
  end ->
  (forall addr : N, addr_in_config addr config ->
               ExternalMemory.ext_mem impl_mem_st addr = ExternalMemory.ext_mem spec_mem_st  addr) ->
  ExternalMemory.mem_get_response__koika impl_mem_st' = ExternalMemory.mem_get_response__koika spec_mem_st'.
Proof.
  intros * himpl hspec hvalid hconfig.
  consider get_valid_addr_from_push_req.
  consider ExternalMemory.mainmem__ext. simplify.
  bash_destruct himpl; simpl.
  - consider ExternalMemory.update_dram. simplify.
    destruct_matches_in_hyp himpl; simplify; simpl; auto.
    rewrite hconfig; auto.
  - simplify. auto.
Qed.
Lemma mem_get_response_valid:
  forall spec_ext_mem' log spec_ext_mem,
  ExternalMemory.mainmem__ext (unsafe_get_ext_call_from_log log (_ext ext_mainmem))
                 spec_ext_mem = Success spec_ext_mem' ->
  _unsafe_get_field mem_output "get_valid"
    match ExternalMemory.mem_get_response__koika spec_ext_mem' with
    | Success bs => bs
    | Failure _ => Ob
    end = Ob~1 ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid mem_input)) (_fld mem_input "put_valid")
    (unsafe_get_ext_call_from_log log (_ext ext_mainmem)) = Ob~1.
Proof.
  intros * hpush hvalid. consider ExternalMemory.mainmem__ext.
  bash_destruct hvalid; [ | discriminate].
  consider ExternalMemory.mem_get_response__koika.
  bash_destruct hpush; auto.
  - unfold unsafe_get_field. setoid_rewrite Heqr1. auto.
  - simplify. simpl in Heqr0. simplify. discriminate.
Qed.
Lemma mem_get_response_invalid:
  forall spec_ext_mem' log spec_ext_mem,
  ExternalMemory.mainmem__ext (unsafe_get_ext_call_from_log log (_ext ext_mainmem))
                 spec_ext_mem = Success spec_ext_mem' ->
  _unsafe_get_field mem_input "put_valid"
                   (unsafe_get_ext_call_from_log log (_ext ext_mainmem)) = Ob~0 ->
  match ExternalMemory.mem_get_response__koika spec_ext_mem' with
  | Success bs => bs
  | Failure _ => Ob
  end = zeroes (_unsafe_struct_sz mem_output).
Proof.
  intros * hpush hvalid.
  consider ExternalMemory.mainmem__ext.
  consider ExternalMemory.mem_get_response__koika.
  bash_destruct hpush; simplify; auto.
  consider ExternalMemory.update_dram. simplify. destruct_matches_in_hyp hpush; simplify; simpl; auto.
  consider @unsafe_get_field.
  exfalso.
  consider _unsafe_get_field.
  setoid_rewrite Heqr0 in hvalid. discriminate.
Qed.
(* Lemma cache_arg_type: *)
(*   forall cache core, *)
(*   unsafe_get_ext_fn_arg_type (_ext (Memory.Memory.ext_cache cache core)) = _unsafe_struct_sz cache_input_sig. *)
(* Proof. *)
(*   destruct cache; destruct core; reflexivity. *)
(* Qed. *)

(* Lemma meta_arg_type: *)
(*   forall cache core, *)
(*   unsafe_get_ext_fn_arg_type (_ext (Memory.Memory.ext_metadata cache core)) = _unsafe_struct_sz metadata_input_sig. *)
(* Proof. *)
(*   destruct cache; destruct core; reflexivity. *)
(* Qed. *)
Import ExternalMemory.
Lemma rewrite_call_cache_fn:
  forall input cache core arg mem' resp,
    (* cache__ext log cache0 =  Success (ext_pair_cache (ext_l1_caches mem' cache core)) -> *)
    cache_get_response__koika arg (ext_pair_cache (ext_l1_caches mem' cache core)) = Success resp ->
    unsafe_call_ext (mk_sigma_fn mem' input) (_id (_extid (Memory.Memory.ext_cache cache core))) arg = resp.
Proof.
  intros * hresp.
  consider mk_sigma_fn.
  destruct cache; destruct core; unfold unsafe_call_ext; rewrite hresp; auto.
Qed.
Lemma rewrite_call_meta_fn:
  forall input cache core arg mem' resp,
    metadata_get_response__koika arg (ext_pair_meta (ext_l1_caches mem' cache core)) = Success resp ->
    unsafe_call_ext (mk_sigma_fn mem' input) (_id (_extid (Memory.Memory.ext_metadata cache core))) arg = resp.
Proof.
  intros * hresp.
  consider mk_sigma_fn.
  destruct cache; destruct core; unfold unsafe_call_ext; rewrite hresp; auto.
Qed.
Ltac rename_success_var H v :=
  match type of H with
  | _ = Success ?s => rename s into v
  end.

Ltac simplify_metadata_and_cache__ext H :=
  unfold metadata__ext, cache__ext in H;
  let hput_valid := fresh "hput_valid" in
  let hput_req := fresh "hput_req" in
  let hget_rdy := fresh "hget_rdy" in
  let put_valid := fresh "put_valid" in
  let put_req := fresh "put_request" in
  let get_ready := fresh "get_ready" in
  let len_get_ready := fresh "hlen_get_ready" in
  let len_put_valid := fresh "hlen_put_valid" in
  destruct_matches_in_hyp_as H hput_valid; [| discriminate]; rename_success_var hput_valid put_valid;
  destruct_matches_in_hyp_as H hput_req; [| discriminate]; rename_success_var hput_req put_req;
  destruct_matches_in_hyp_as H hget_rdy; [| discriminate]; rename_success_var hget_rdy get_ready;
  assert (Datatypes.length get_ready = 1) as len_get_ready by (clear - H; bash_destruct H; reflexivity);
  assert (Datatypes.length put_valid = 1) as len_put_valid by (clear - H; bash_destruct H; reflexivity).
Ltac wrap_solve_cache_post_implies wrapper name hinvs :=
  let hfoo := fresh in
  match goal with
  | cache: mem_type, core: ind_core_id |- _ =>
  destruct cache; destruct core
  end;
    [prop_pose_with_custom hfoo (wrapper (name imem CoreId0)) hinvs; auto
    |prop_pose_with_custom hfoo (wrapper (name imem CoreId1)) hinvs; auto
    |prop_pose_with_custom hfoo (wrapper (name dmem CoreId0)) hinvs; auto
    |prop_pose_with_custom hfoo (wrapper (name dmem CoreId1)) hinvs ; auto
    ].

Lemma SimPost_implies_cache_eq:
  forall cache core impl_st spec_st impl_sigma spec_sigma impl_st' spec_st' spec_log impl_log,
  SimPost EnclaveParams.enclave_sig core impl_st spec_st
    impl_st' spec_st'
    impl_sigma spec_sigma impl_log spec_log ->
  (obs_cache (get_mem_observations impl_log) cache core) =
  (obs_cache (get_mem_observations spec_log) cache core).
Proof.
  intros * hsim.  wrap_solve_cache_post_implies CustomMemSim MemSimCache hsim.
Qed.
Lemma SimPost_implies_meta_eq:
  forall cache core impl_st spec_st impl_sigma spec_sigma impl_st' spec_st' spec_log impl_log,
  SimPost EnclaveParams.enclave_sig core impl_st spec_st
    impl_st' spec_st'
    impl_sigma spec_sigma impl_log spec_log ->
  (obs_meta (get_mem_observations impl_log) cache core) =
  (obs_meta (get_mem_observations spec_log) cache core).
Proof.
  intros * hsim. wrap_solve_cache_post_implies CustomMemSim MemSimMetadata hsim.
Qed.
Lemma sigma_eq_implies_cache_sim_pre_conds:
  forall impl_pkg spec_pkg cache core impl_mem spec_mem input0 input1,
  pkg_sigma impl_pkg = mk_sigma_fn impl_mem input0 ->
  pkg_sigma spec_pkg = mk_sigma_fn spec_mem input1 ->
  ext_l1_caches impl_mem cache core = ext_l1_caches spec_mem cache core ->
  Forall (fun '(_, p) => interp_fancy_spred2 impl_pkg spec_pkg p)
    (cache_sim_pre_conds cache core impl_init spec_init impl_get_field spec_get_field).
Proof.
  intros * hisigma hssigma hcaches.
  unfold cache_sim_pre_conds. repeat constructor;
  repeat constructor; basic_cbn; unfold unsafe_call_ext; intros *;
    [ setoid_rewrite meta_arg_type | setoid_rewrite cache_arg_type];
    rewrite hisigma; rewrite hssigma.
  - unfold mk_sigma_fn. destruct cache; destruct core; rewrite hcaches;
    intro; cbn - [metadata_get_response__koika]; reflexivity.
  - unfold mk_sigma_fn. destruct cache; destruct core; rewrite hcaches;
    intro; cbn - [cache_get_response__koika]; reflexivity.
Qed.
Lemma ext_mem_cache_sim_implies_eq:
  forall impl_cache spec_cache,
  ext_mem_cache_sim impl_cache spec_cache <->
  impl_cache = spec_cache.
Proof.
  intros; split; intros; subst; auto.
  - destruct H. destruct impl_cache. destruct spec_cache. simpl in *.
    consider ext_mem_metadata_sim. consider cache_resp_sim. simpl in *. subst. f_equal; auto.
    destruct ext_pair_cache0; destruct ext_pair_cache1; simpl in *; subst; auto.
    f_equal; auto. apply functional_extensionality. auto.
  - repeat constructor; auto.
Qed.

Lemma cache_sim_preserved:
  forall cache core impl_st spec_st impl_sigma spec_sigma impl_st' spec_st'
    spec_log impl_log spec_ext_mem' mem_st' impl_mem spec_mem impl_pkg1 spec_pkg1 input0 input1,
  SimPost EnclaveParams.enclave_sig core impl_st spec_st
    impl_st' spec_st'
    impl_sigma spec_sigma impl_log spec_log ->
  ext_mem_cache_sim (ExternalMemory.ext_l1_caches impl_mem cache core)
                    (ExternalMemory.ext_l1_caches spec_mem cache core) ->
  ExternalMemory.update_memory (get_mem_observations (spec_log)) spec_mem =
               Success spec_ext_mem' ->
  ExternalMemory.update_memory (get_mem_observations (impl_log)) impl_mem =
               Success mem_st' ->
  pkg_sigma impl_pkg1 = mk_sigma_fn mem_st' input0 ->
  pkg_sigma spec_pkg1 = mk_sigma_fn spec_ext_mem' input1 ->
  Forall (fun '(_, p) => interp_fancy_spred2 impl_pkg1 spec_pkg1 p)
    (cache_sim_pre_conds cache core impl_init spec_init impl_get_field spec_get_field).
Proof.
  intros * hpost hsim hiupdate hsupdate himpl_sigma hspec_sigma.
  apply (ext_mem_update_memory_implies_cache _ _ _ cache core) in hiupdate.
  apply (ext_mem_update_memory_implies_cache _ _ _ cache core) in hsupdate.
  consider cachepair__ext.
  destruct_matches_in_hyp_as hiupdate hicache; [ | discriminate].
  destruct_matches_in_hyp_as hiupdate himeta; [ | discriminate].
  destruct_matches_in_hyp_as hsupdate hscache; [ | discriminate].
  destruct_matches_in_hyp_as hsupdate hsmeta; [ | discriminate]; simplify.
  repeat rewrite SimPost_implies_cache_eq with (1 := hpost) in *.
  repeat rewrite SimPost_implies_meta_eq with (1 := hpost) in *.
  apply ext_mem_cache_sim_implies_eq in hsim. subst.
  eapply sigma_eq_implies_cache_sim_pre_conds; eauto.
  rewrite<-H0. rewrite<-H1.
  rewrite hsim in *.
  setoid_rewrite hicache in hscache.
  setoid_rewrite himeta in hsmeta. simplify.
  auto.
Qed.

Lemma SimPre_stay_implied:
  forall input machine_st spec_log impl_st core log mem_st' spec_ext_mem'  config,
  WF_state (SortedRegEnv.to_list reg_type_env) (machine_koika_st impl_st) ->
  WF_state (SortedRegEnv.to_list reg_type_env) (commit_update (machine_koika_st impl_st) (Log__koika log))->
  ImplPost impl_st
                 {|
                   machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log);
                   machine_mem_st := mem_st'
                 |} (Log__ext log) ->
  SimPre EnclaveParams.enclave_sig core (machine_koika_st impl_st) (machine_koika_st machine_st)
              (mk_sigma_fn (machine_mem_st impl_st) input)
              (mk_sigma_fn (machine_mem_st machine_st)
                 (filter_input
                    (Some
                       (unsafe_enclave_data_to_config
                          (machine_koika_st impl_st).[_rid (SM (enc_data core))]))
                    input)) ->
  SimPost EnclaveParams.enclave_sig core (machine_koika_st impl_st) (machine_koika_st machine_st)
               (commit_update (machine_koika_st impl_st) (Log__koika log))
               (commit_update (machine_koika_st machine_st) (Log__koika spec_log))
               (mk_sigma_fn (machine_mem_st impl_st) input)
               (mk_sigma_fn (machine_mem_st machine_st)
                  (filter_input
                     (Some (unsafe_enclave_data_to_config
                           (machine_koika_st impl_st).[_rid (SM (enc_data core))]))
                     input)) (Log__ext log) (Log__ext spec_log) ->
  observe_enclave_exit core (machine_koika_st machine_st)
    (commit_update (machine_koika_st machine_st) (Log__koika spec_log)) = None ->
  ExternalMemory.update_memory (get_mem_observations (Log__ext spec_log))
                               (machine_mem_st machine_st) = Success spec_ext_mem' ->
  ExternalMemory.update_memory (get_mem_observations (Log__ext log))
                               (machine_mem_st impl_st) = Success mem_st' ->
  machine_st_to_ghost_core (machine_koika_st impl_st) core extract_rf =
                         GhostCoreState_Enclave config ->
  dram_sim_at_config config (ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st impl_st)))
                            (ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st machine_st))) ->
  (forall cache, ext_mem_cache_sim ((machine_mem_st impl_st).(ExternalMemory.ext_l1_caches) cache core)
                              ((machine_mem_st machine_st).(ExternalMemory.ext_l1_caches) cache core))
                              (* (get_cache_ghost_state core (machine_koika_st impl_st) cache))  *)->
  SimPre EnclaveParams.enclave_sig core (commit_update (machine_koika_st impl_st) (Log__koika log))
    (commit_update (machine_koika_st machine_st) (Log__koika spec_log)) (mk_sigma_fn mem_st' input)
    (mk_sigma_fn spec_ext_mem'
       (filter_input
          (Some (unsafe_enclave_data_to_config (machine_koika_st impl_st).[_rid (SM (enc_data core))]))
          input)).
Proof.
  intros * hwf_impl hwf_impl' HImplPost HSimPre HSimPost hobserve hspec_push himpl_push hconfig hdram hcaches.
  prop_pose_with_custom hsm_sim' (CustomSmSim SmSim__Regs) HSimPost. cbn - [_id sm_regs] in hsm_sim'.
  prop_pose_with_custom hsm_sim (CustomSmSim SmSim__Regs) HSimPre . cbn - [_id sm_regs] in hsm_sim.
  prop_pose_with_custom hmem_sim (CustomMemSim MemSim__Regs) HSimPre. cbn - [_id ext_mem_regs private_mem_regs] in hmem_sim.
  prop_pose_with_custom hmem_sim' (CustomMemSim MemSim__Regs) HSimPost. cbn - [_id ext_mem_regs private_mem_regs] in hmem_sim'.
  assert (unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid enclave_data)) (
           "valid", 1%N) (machine_koika_st impl_st).[_id (reg_to_debug_id (SM (enc_data core)))] = Ob~1) as henc_valid.
    { prop_pose_with_custom hfoo CustomRegStateRunning HSimPre. cbn - [_id _sid] in hfoo.
      destruct core;
        [prop_pose_with_custom henc_data (CustomSm (SM_enc_data_valid CoreId0)) HSimPre; cbn - [_id _sid] in henc_data
        |prop_pose_with_custom henc_data (CustomSm (SM_enc_data_valid CoreId1)) HSimPre; cbn - [_id _sid] in henc_data
        ];
        match goal with
        | |- ?x = _ =>
            assert (Datatypes.length x = 1) as hlen; [ | apply case_singleton_bv in hlen; split_ors_in hlen; auto]
        end;
        unfold unsafe_get_field, success_or_default;
        unsafe_simplify_structs_as hvalid; assert_pre_and_specialize hvalid; simplify;
        try unsafe_auto_simplify_structs.
        setoid_rewrite Heqr0; auto.
        setoid_rewrite Heqr0; auto.
    }
  assert (unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid enclave_data)) (
           "valid", 1%N) (commit_update (machine_koika_st impl_st) (Log__koika log)).[_id (reg_to_debug_id (SM (enc_data core)))] = Ob~1) as henc_valid'.
  { consider observe_enclave_exit.  consider observe_enclave_exit_from_enc_data.
    destruct core; bash_destruct hobserve;
      repeat (setoid_rewrite<-hsm_sim' in Heqb; [ | solve_In_to_find]);
      repeat (setoid_rewrite<-hsm_sim in Heqb; [ | solve_In_to_find]);
      setoid_rewrite henc_valid in Heqb; simpl in Heqb; simplify;
      match goal with
      | |- ?x = _ =>
          assert (Datatypes.length x = 1) as hlen; [ | apply case_singleton_bv in hlen; split_ors_in hlen; auto]
      end;
      unfold unsafe_get_field, success_or_default;
      unsafe_simplify_structs_as hvalid; assert_pre_and_specialize hvalid; simplify;
        try unsafe_auto_simplify_structs;
      setoid_rewrite Heqr0; auto.
  }

  assert (((commit_update (machine_koika_st impl_st) (Log__koika log)).[_rid (SM (enc_data core))]) =
          (machine_koika_st impl_st).[_rid (SM (enc_data core))]) as henc_data_same.
  { symmetry.
    destruct core.
    - prop_pose_with_custom Hfoo (CustomSm (SM_config_same CoreId0)) HSimPost.
      cbn - [_id _sid _fld] in Hfoo.
      apply Hfoo; auto.
    - prop_pose_with_custom Hfoo (CustomSm (SM_config_same CoreId1)) HSimPost.
      cbn - [_id _sid _fld] in Hfoo.
      apply Hfoo; auto.
  }

  assert (forall input, SimPreInvariants core (commit_update (machine_koika_st impl_st) (Log__koika log))
    (commit_update (machine_koika_st machine_st) (Log__koika spec_log)) (mk_sigma_fn mem_st' input)
    (mk_sigma_fn spec_ext_mem'
       (filter_input
          (Some (unsafe_enclave_data_to_config (machine_koika_st impl_st).[_rid (SM (enc_data core))]))
          input))) as Hpre.
  { intros.
    eapply SimPost_implies_SimPreInvariants; eauto.
  }

  unfold SimPre, sim_pre_conds.
  repeat rewrite Forall_app.
  split_ands_in_goal.
  + apply Hpre.
  + unfold sim_sm_pre_conds.
    repeat constructor; cbn - [_id filter_input _sid].
    * destruct core.
      { prop_pose_with_custom hfoo (CustomSm (SM_config_same CoreId0)) HSimPost.
        cbn - [_id _sid _fld] in hfoo. propositional.
      }
      { prop_pose_with_custom hfoo (CustomSm (SM_config_same CoreId1)) HSimPost.
        cbn - [_id _sid _fld] in hfoo. propositional.
      }
    * intros * hlen hled.
      unfold unsafe_enclave_data_to_config.
      unfold filter_input, mk_sigma_fn, unsafe_call_ext.
      cbn - [_sid _rid slice].
      rewrite<-hsm_sim' in hled by (destruct core; solve_In_to_find).
      setoid_rewrite henc_data_same in hled.
      destruct_match; auto.
      setoid_rewrite hled in Heqb. simplify. contradiction.
    * intros * hlen huart.
      unfold unsafe_enclave_data_to_config.
      unfold filter_input, mk_sigma_fn, unsafe_call_ext.
      cbn - [_sid _rid slice].
      rewrite<-hsm_sim' in huart by (destruct core; solve_In_to_find).
      setoid_rewrite henc_data_same in huart.
      destruct_match; auto.
      setoid_rewrite huart in Heqb. simplify. contradiction.
    * intros * hlen huart.
      unfold unsafe_enclave_data_to_config.
      unfold filter_input, mk_sigma_fn, unsafe_call_ext.
      cbn - [_sid _rid slice].
      rewrite<-hsm_sim' in huart by (destruct core; solve_In_to_find).
      setoid_rewrite henc_data_same in huart.
      destruct_match; auto.
      setoid_rewrite huart in Heqb. simplify. contradiction.
    * intros * hlen hfinish.
      unfold unsafe_enclave_data_to_config.
      unfold filter_input, mk_sigma_fn, unsafe_call_ext.
      cbn - [_sid _rid slice].
      rewrite<-hsm_sim' in hfinish by (destruct core; solve_In_to_find).
      setoid_rewrite henc_data_same in hfinish.
      destruct_match; auto.
      setoid_rewrite hfinish in Heqb. simplify. contradiction.
  + unfold sim_mem_pre_conds.
    assert ((commit_update (machine_koika_st impl_st) (Log__koika log)).[_rid (Memory Memory.turn)] = mem_core_read_turn core ->
            (obs_mainmem (get_mem_observations (Log__ext log))) =
            (obs_mainmem (get_mem_observations (Log__ext spec_log)))) as hpush_sim.
    { prop_pose_with_custom hfoo (CustomExtMemPushRequest__Sim) HSimPost.
      cbn - [_id _sid] in hfoo. auto.
    }

    repeat rewrite Forall_app. split_ands_in_goal.
    * repeat constructor; cbn - [_id _sid filter_input]; unfold unsafe_call_ext, mk_sigma_fn; simpl.
      - cbn - [_id _sid filter_input]; unfold unsafe_call_ext, mk_sigma_fn; simpl.
        intros * hlen H. simpl. cbn - [_id _sid] in H.
        propositional.
        apply ext_mem_update_memory_implies_main_mem in hspec_push.
        apply ext_mem_update_memory_implies_main_mem in himpl_push.
        rewrite<-hpush_sim in *.
        specialize wf_mem_push with (1 := impl_wf_log _ _ _ HImplPost).
        unfold mem_push_in_config.
        specialize impl_increment_mem_cycles with (1 := HImplPost); intros hturn.
        setoid_rewrite H in hturn.
        intros haddr.
        split.
        { erewrite mem_push_request_sim_preserved with (1 := himpl_push) (2 := hspec_push); eauto.
          consider is_mem_core0_push_turn. consider is_mem_core1_push_turn.
          assert (Datatypes.length (machine_koika_st impl_st).[_mrid Memory.turn] = 2) as Hlen by unsafe_auto_simplify_structs.
          apply case_doubleton_bits in Hlen.
          bash_destruct hconfig.
          destruct core.
          { split_ors_in Hlen; rewrite Hlen in hturn; try (clear - hturn; discriminate).
            consider _mrid.
            rewrite Hlen in haddr. simpl in haddr.
            rewrite hconfig in haddr. auto.
          }
          { split_ors_in Hlen; rewrite Hlen in hturn; try (clear - hturn; discriminate).
            consider _mrid.
            rewrite Hlen in haddr. simpl in haddr.
            rewrite hconfig in haddr. auto.
          }
        }
        { intros hmem. prop_apply_with_custom CustomExtMemShreqSim HSimPost; auto.
          simpl.
          propositional.
          eapply mem_get_response_valid with (1 := hspec_push); eauto.
        }
      - cbn - [_id _sid filter_input]; unfold unsafe_call_ext, mk_sigma_fn; simpl.
        intros * hlen H; propositional.
        prop_pose_with_custom hfoo CustomExtMemPushRequest__ImplInvalidOrWriteTurn HSimPost.
        cbn - [_id] in hfoo. split_ors_in hfoo.
        { apply ext_mem_update_memory_implies_main_mem in himpl_push.
          eapply mem_get_response_invalid; eauto.
          - setoid_rewrite himpl_push. auto.
          - auto.
        }
        { exfalso.  specialize impl_increment_mem_cycles with (1 := HImplPost); simpl; setoid_rewrite hfoo.
          destruct core; cbn; intros; simplify;
           (setoid_rewrite H3 in H0 || setoid_rewrite H3 in H1); contradiction.
        }
        { exfalso. specialize impl_increment_mem_cycles with (1 := HImplPost); simpl; setoid_rewrite hfoo.
          destruct core; cbn; intros; simplify;
           (setoid_rewrite H3 in H0 || setoid_rewrite H3 in H1); contradiction.
        }
      - cbn - [_id _sid filter_input]; unfold unsafe_call_ext, mk_sigma_fn; simpl.
        intros * hlen H.
        prop_pose_with_custom hfoo CustomExtMemPushRequest__SpecInvalidOrWriteTurn HSimPost.
        cbn - [_id] in hfoo. split_ors_in hfoo.
        { eapply mem_get_response_invalid; eauto.
          apply ext_mem_update_memory_implies_main_mem in hspec_push.
          setoid_rewrite hspec_push. auto.
          auto.
        }
        { exfalso.
          setoid_rewrite<-hmem_sim' with (x := _mid Memory.turn) in H; auto.
          specialize impl_increment_mem_cycles with (1 := HImplPost); simpl; setoid_rewrite hfoo.
          destruct core; cbn; intros; simplify;
            setoid_rewrite H2 in H; contradiction.
        }
    * specialize impl_invariant_post with (1 := HImplPost); intros hmemPost.
      apply ImplInv_MemInvariant with (input := input)in hmemPost. simpl in hmemPost.
      consider MemSymbDefs.MemPre. unfold MemSymbDefs.mem_pre_conds in hmemPost.
      repeat rewrite Forall_app in hmemPost. split_ands_in_hyps.
      init_interp.
      rewrite Forall_interp_spred2_using_impl_only; [ | vm_reflect ].
      rewrite<-forall_preprocess_fancy_spreds_correct in *. auto.
    * specialize impl_invariant_post with (1 := HImplPost); intros hmemPost.
      apply ImplInv_MemInvariant with (input := input)in hmemPost. simpl in hmemPost.
      consider MemSymbDefs.MemPre. unfold MemSymbDefs.mem_pre_conds in hmemPost.
      repeat rewrite Forall_app in hmemPost. split_ands_in_hyps.
      init_interp.
      rewrite Forall_interp_spred2_using_impl_only; [ | vm_reflect ].
      rewrite<-forall_preprocess_fancy_spreds_correct in *. auto.
    * unfold map. unfold List.concat. rewrite Forall_ignore_map_fst.
       repeat rewrite Forall_app; split_ands_in_goal; auto.
       - eapply cache_sim_preserved with (input0 := input); eauto; reflexivity.
       - eapply cache_sim_preserved with (input0 := input); eauto; reflexivity.
Qed.
Lemma Forall_cons_implies:
  forall {X Y} (f: X -> Prop) (g: Y -> Prop) xs ys (x: X) (y: Y),
  (f x -> g y) ->
  (Forall f xs -> Forall g ys) ->
  Forall f (x::xs) ->
  Forall g (y::ys).
Proof.
  intros. inversion H1. constructor; eauto.
Qed.
Lemma SplitImplAnds :
  forall A A' B B',
  (A -> A') -> (B -> B') -> (A /\ B -> A' /\ B').
Proof.
  intros. propositional.
Qed.
Lemma ext_cache_ignores_input:
  forall input0 input1 arg mem cache core,
  unsafe_call_ext (mk_sigma_fn mem input0) (_id (_extid (Memory.ext_cache cache core))) arg  =
  unsafe_call_ext (mk_sigma_fn mem input1) (_id (_extid (Memory.ext_cache cache core))) arg.
Proof.
  destruct cache; destruct core; reflexivity.
Qed.
Lemma ext_meta_ignores_input:
  forall input0 input1 arg mem cache core,
  unsafe_call_ext (mk_sigma_fn mem input0) (_id (_extid (Memory.ext_metadata cache core))) arg  =
  unsafe_call_ext (mk_sigma_fn mem input1) (_id (_extid (Memory.ext_metadata cache core))) arg.
Proof.
  destruct cache; destruct core; reflexivity.
Qed.
Ltac rewrite_ignores_input input input' spec_input spec_input' :=
  try intros * x *;
  try rewrite mainmem_ignores_input with (input0 := input') (input1 := input);
  try rewrite mainmem_ignores_input with (input0 := spec_input') (input1 := spec_input);
  try rewrite ext_cache_ignores_input with (input0 := input') (input1 := input) (cache := imem);
  try rewrite ext_cache_ignores_input with (input0 := input') (input1 := input) (cache := dmem);
  try rewrite ext_cache_ignores_input with (input0 := spec_input') (input1 := spec_input) (cache := imem);
  try rewrite ext_cache_ignores_input with (input0 := spec_input') (input1 := spec_input) (cache := dmem);
  try rewrite ext_meta_ignores_input with (input0 := input') (input1 := input) (cache := imem);
  try rewrite ext_meta_ignores_input with (input0 := input') (input1 := input) (cache := dmem);
  try rewrite ext_meta_ignores_input with (input0 := spec_input') (input1 := spec_input) (cache := imem);
  try rewrite ext_meta_ignores_input with (input0 := spec_input') (input1 := spec_input) (cache := dmem);
  eauto.

Lemma SimPreIgnoresInputs:
  forall core impl_st spec_st input input' config impl_mem_st spec_mem_st,
  Datatypes.length (spec_st.[_rid (SM (enc_data core))]) = _unsafe_struct_sz enclave_data ->
  config = (unsafe_enclave_data_to_config (spec_st).[_rid (SM (enc_data core))]) ->
  SimPre EnclaveParams.enclave_sig core impl_st spec_st (mk_sigma_fn impl_mem_st input) (mk_sigma_fn spec_mem_st (filter_input (Some config) input)) ->
  SimPre EnclaveParams.enclave_sig core impl_st spec_st (mk_sigma_fn impl_mem_st input') (mk_sigma_fn spec_mem_st (filter_input (Some config) input')).
Proof. (* DONE *)
  intros * hlen Hconfig. consider SimPre.
  destruct config. consider unsafe_enclave_data_to_config.
  set (spec_st.[_]) as enc_data in *.

  epose proof (eta_expand_list_correct false _) as hdata_enc.
  erewrite hlen in hdata_enc. cbn in hdata_enc.
  consider _rid.
  consider unsafe_enclave_req_to_config.

  unfold sim_pre_conds. intros.
  - repeat rewrite Forall_app in H. destruct H as (Hinv & Hsm & Hmem).
    repeat rewrite Forall_app. split_ands_in_goal.
    + revert Hinv.
      repeat rewrite<-forall_preprocess_fancy_spreds_correct2. clear.
      destruct core; eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
    + clear Hinv Hmem. revert Hsm.
      repeat (apply Forall_cons_implies; [solve[auto] | ]).
      repeat apply Forall_cons_implies; auto.
      1: eapply f_equal  with (f := Common.config_ext_led) in Hconfig; consider Common.config_ext_led.
      2: eapply f_equal  with (f := Common.config_ext_uart) in Hconfig; consider Common.config_ext_uart.
      3: eapply f_equal  with (f := Common.config_ext_uart) in Hconfig; consider Common.config_ext_uart.
      4: eapply f_equal  with (f := Common.config_ext_finish) in Hconfig; consider Common.config_ext_finish.
      all: rewrite hdata_enc in Hconfig; consider _smid;
           cbn - [_id _sid _fld]; subst enc_data;
           intros _ * hlen' hconfig';
           setoid_rewrite hdata_enc in hconfig';
           set (spec_st.[_]) as enc_data in *;
           clearbody enc_data;
           cbv - [nth] in hconfig'; subst;
           rewrite unit_equiv in hconfig'; rewrite hconfig'; auto.
    + revert Hmem.
       set (filter_input _ input) as spec_input.
       set (filter_input _ input') as spec_input'.
       unfold sim_mem_pre_conds. repeat rewrite Forall_app.
       clearbody spec_input. clearbody spec_input'.
       repeat apply SplitImplAnds; repeat rewrite Forall_ignore_map_fst; split_ands_in_goal.
       { repeat apply Forall_cons_implies; try solve[constructor].
         all: clear; basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
       }
       { repeat apply Forall_cons_implies; try solve[constructor].
         basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - rewrite interp_fancy_spred2_using_impl_only; [ | vm_reflect].
           rewrite interp_fancy_spred2_using_impl_only; [ | vm_reflect].
           apply interp_meta_resp_in_range_eq; auto. (* intros. unfold pkg_sigma. *)
           (* rewrite_ignores_input input input' spec_input spec_input'. *)
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - rewrite interp_fancy_spred2_using_impl_only; [ | vm_reflect].
           rewrite interp_fancy_spred2_using_impl_only; [ | vm_reflect].
           apply interp_meta_resp_in_range_eq; auto. (* intros. unfold pkg_sigma. *)
           (* rewrite_ignores_input input input' spec_input spec_input'. *)
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
       }
       { repeat apply Forall_cons_implies; try solve[constructor].
         basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - rewrite interp_fancy_spred2_using_impl_only; [ | vm_reflect].
           rewrite interp_fancy_spred2_using_impl_only; [ | vm_reflect].
           apply interp_meta_resp_in_range_eq; auto. (* intros. unfold pkg_sigma. *)
           (* rewrite_ignores_input input input' spec_input spec_input'. *)
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - rewrite interp_fancy_spred2_using_impl_only; [ | vm_reflect].
           rewrite interp_fancy_spred2_using_impl_only; [ | vm_reflect].
           apply interp_meta_resp_in_range_eq; auto. (* intros. unfold pkg_sigma. *)
           (* rewrite_ignores_input input input' spec_input spec_input'. *)
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
         - basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
       }
       { unfold map. unfold List.concat. repeat rewrite Forall_app. repeat apply SplitImplAnds. split_ands_in_goal.
         all: repeat apply Forall_cons_implies; try solve[constructor];
              basic_cbn; rewrite_ignores_input input input' spec_input spec_input'.
       }
Qed.
Lemma SimPostIgnoresInputs:
  forall core impl_st spec_st input input' config impl_mem_st spec_mem_st impl_st' spec_st' impl_log spec_log,
  SimPost EnclaveParams.enclave_sig core impl_st spec_st impl_st' spec_st'
    (mk_sigma_fn impl_mem_st input)
    (mk_sigma_fn spec_mem_st (filter_input (Some config) input)) impl_log spec_log <->
  SimPost EnclaveParams.enclave_sig core impl_st spec_st impl_st' spec_st'
    (mk_sigma_fn impl_mem_st input')
    (mk_sigma_fn spec_mem_st (filter_input (Some config) input')) impl_log spec_log.
Proof. (* DONE *)
  intros. consider SimPost.
  repeat rewrite<-forall_preprocess_fancy_spreds_correct2.
  split.
  - destruct core; eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
  - destruct core; eapply forall_interp_spred2_package_equiv'; solve_package_equiv.
Qed. (* DONE *)
Lemma contrad_read_write_turn:
  forall core cycles0,
  is_mem_core_write_turn' (other_core core) cycles0 = true ->
  is_mem_core_read_turn' core (cycles0 + 1) = true ->
  False.
Proof.
  consider is_mem_core_read_turn'. consider is_mem_core_write_turn'. intros.
  destruct core; simpl other_core in H; cbv iota in H; simplify.
  + rewrite<-PeanoNat.Nat.add_mod_idemp_l in H0 by lia.
    rewrite H in H0. cbv in H0. discriminate.
  + rewrite<-PeanoNat.Nat.add_mod_idemp_l in H0 by lia.
    rewrite H in H0. cbv in H0. discriminate.
Qed.


Lemma ext_main_mem_sim_preserved:
  forall core config impl_main_mem impl_main_mem' spec_main_mem spec_main_mem' cycles impl_log spec_log,
  dram_sim_at_config config (ExternalMemory.ext_mem impl_main_mem)
                   (ExternalMemory.ext_mem spec_main_mem) ->
  (is_mem_core_read_turn' core cycles = true ->
   ExternalMemory.ext_resp impl_main_mem = ExternalMemory.ext_resp spec_main_mem) ->
  (is_mem_core_write_turn' core cycles = true ->
   (obs_mainmem (get_mem_observations impl_log)) = (obs_mainmem (get_mem_observations spec_log))) ->
  (_unsafe_get_field mem_input "put_valid"
                        (obs_mainmem (get_mem_observations impl_log)) = Ob~0 \/
    is_mem_core_write_turn' core cycles = true \/
    is_mem_core_write_turn' (other_core core) cycles = true)  ->
  (_unsafe_get_field mem_input "put_valid" (obs_mainmem (get_mem_observations spec_log))) = Ob~0 \/
    is_mem_core_write_turn' core cycles = true ->
  (is_mem_core_write_turn' (other_core core) cycles = true ->
   match get_valid_addr_from_push_req (obs_mainmem (get_mem_observations impl_log)) with
   | Some addr => addr_in_config (to_N addr) config -> False
   | None => True
   end ) ->
  (is_mem_core_write_turn' (core) cycles = true ->
   match get_valid_addr_from_push_req (obs_mainmem (get_mem_observations impl_log))  with
   | Some addr => addr_in_config (to_N addr) config
   | None => True
   end ) ->
  ExternalMemory.mainmem__ext (obs_mainmem (get_mem_observations impl_log)) impl_main_mem = Success impl_main_mem' ->
  ExternalMemory.mainmem__ext (obs_mainmem (get_mem_observations spec_log)) spec_main_mem = Success spec_main_mem' ->
  dram_sim_at_config config (ExternalMemory.ext_mem impl_main_mem') (ExternalMemory.ext_mem spec_main_mem') /\
  (is_mem_core_read_turn' core (cycles + 1) = true ->
   ExternalMemory.ext_resp impl_main_mem' = ExternalMemory.ext_resp spec_main_mem').
Proof.
  intros * hdram_sim hresp_sim hpush_sim himpl_zeroes hspec_zeroes haddr hcore_addr himpl hspec.
  consider ExternalMemory.mainmem__ext.
  destruct (beq_dec (_unsafe_get_field mem_input "put_valid"
                       (obs_mainmem (get_mem_observations impl_log))) Ob~0) eqn:himpl_valid;
  destruct (beq_dec (_unsafe_get_field mem_input "put_valid"
                       ((obs_mainmem (get_mem_observations spec_log)))) Ob~0 ) eqn:hspec_valid;
            simplify;
    consider @_unsafe_get_field; consider @success_or_default; bash_destruct himpl_valid;
    bash_destruct hspec_valid; simplify; propositional.
  - split_ors_in hspec_zeroes; [subst; contradiction | ]. propositional. simpl.
    rewrite hpush_sim in *.
    bash_destruct hspec.
  - split_ors_in himpl_zeroes; split_ors_in hspec_zeroes; simplify; try contradiction; auto.
    + rewrite hpush_sim in * by auto. congruence.
    + rewrite hpush_sim in * by auto. rewrite Heqr1 in *. simplify. congruence.
    + propositional. consider get_valid_addr_from_push_req.
      rewrite Heqr4 in haddr.
      rewrite Heqr3 in haddr.
      bash_destruct himpl.
      consider ExternalMemory.update_dram. simplify.
      constructor.
      { destruct_matches_in_hyp himpl; simplify; simpl; intros.
        - eauto.
        - unfold dram_sim_at_config.  intros.
          destruct_match; simplify; auto.
      }
      { intros; exfalso; eapply contrad_read_write_turn; eauto. }
    + rewrite hpush_sim in * by auto. rewrite Heqr1 in *. simplify. congruence.
  - bash_destruct hspec. bash_destruct himpl. simplify.
    split_ors_in hspec_zeroes; [discriminate |]. propositional.
    repeat rewrite hpush_sim in *. rewrite Heqr3 in *. simplify.
    consider dram_sim_at_config.
    consider ExternalMemory.update_dram. simplify.
    destruct_matches_in_hyp himpl; simplify; simpl; split; propositional.
    + rewrite hdram_sim; auto.
      unfold get_valid_addr_from_push_req in hcore_addr.
      simpl_match. simpl_match. rewrite Heqr0 in hcore_addr.
      auto.
    + destruct_match; auto.
Qed.

(* update should be the same in impl and spec? *)
Lemma ext_cache_metadata_sim_preserved:
  forall impl_meta spec_meta impl_meta' spec_meta' obs,
  ext_mem_metadata_sim impl_meta spec_meta ->
  ExternalMemory.metadata__ext obs impl_meta = Success impl_meta' ->
  ExternalMemory.metadata__ext obs spec_meta = Success spec_meta' ->
  ext_mem_metadata_sim impl_meta' spec_meta'.
Proof.
  intros * hsim himpl hspec.
  consider ExternalMemory.metadata__ext.
  destruct_matches_in_hyp_as himpl hput_valid; [ | discriminate].
  destruct_matches_in_hyp_as himpl hput_req; [ | discriminate].
  destruct_matches_in_hyp_as himpl hget_ready; [ | discriminate].

  consider ext_mem_metadata_sim. subst.
  bash_destruct himpl.
Qed.

(* Ghost: Some -> None
   Ghost: None -> Some
   Ghost: unchanged
 *)
Lemma _get_field_length_implied :
  forall sig fld data ret,
  _get_field sig  fld data = Success ret ->
  Datatypes.length data = _unsafe_struct_sz sig.
Proof.
  intros. consider _get_field. consider get_field. simplify.
  unfold Semantics.get_field in *. simplify.
  consider _unsafe_struct_sz.
  unfold struct_sz. unfold _lookup_struct. simpl_match. auto.
Qed.

Lemma metadata_ext_update_now_valid:
  forall obs meta meta' n,
  ExternalMemory.metadata__ext obs meta = Success meta' ->
  get_metadata_valid (ExternalMemory.ext_metadata meta n) <> Ob~1 ->
  get_metadata_valid (ExternalMemory.ext_metadata meta' n) = Ob~1 ->
  _get_field metadata_input_sig "put_valid" obs  = Success Ob~1 /\
  match _get_field metadata_input_sig "put_request" obs with
  | Success req => _get_field metadata_req_sig "is_write" req = Success Ob~1 /\
                  match _get_field metadata_req_sig "data" req with
                  | Success data => _get_field metadata_sig "valid" data = Success Ob~1
                  | _ => False
                  end /\
                  match _get_field metadata_req_sig "addr" req with
                  | Success addr => n = to_N addr
                  | _ => False
                  end
  | Failure _ => False
  end.
Proof.
  intros * hmeta hvalid hvalid'.
  consider get_metadata_valid.
  consider ExternalMemory.metadata__ext. simplify.
  consider ExternalMemory.update_metadata.

  bash_destruct hmeta; simplify; auto.
  - simpl in hvalid'. bash_destruct hvalid'; simplify; auto.
    assert (Datatypes.length s2 = 1).
    {  pose proof (_get_field_success metadata_req_sig "is_write" s0 1) as hsuccess.
       simpl_match. apply hsuccess; cbn; auto.
       erewrite _get_field_length_implied; eauto; reflexivity.
    }
    destruct s2; [discriminate | ].
    destruct s2; [|  discriminate].
    destruct b; auto.
  -
    assert (Datatypes.length s2 = 1).
    {  pose proof (_get_field_success metadata_req_sig "is_write" s0 1) as hsuccess.
       simpl_match. apply hsuccess; cbn; auto.
       erewrite _get_field_length_implied; eauto; reflexivity.
    }
    destruct s2; [discriminate | ].
    destruct s2; [|  discriminate].
    destruct b; auto.
    simpl in hvalid'.
    bash_destruct hvalid'; simplify. auto.
Qed.
Lemma update_cache_still_eq_at_addr:
  forall impl_cache spec_cache impl_cache' spec_cache' n obs,
  impl_cache n = spec_cache n ->
  ExternalMemory.update_cache obs impl_cache = Success impl_cache' ->
  ExternalMemory.update_cache obs spec_cache = Success spec_cache' ->
  ExternalMemory.ext_cache impl_cache' n = ExternalMemory.ext_cache spec_cache' n.
Proof.
  consider ExternalMemory.update_cache.
  intros * heq himpl hspec. simplify. bash_destruct himpl; simplify; simpl; rewrite heq; auto.
Qed.

(* Definition get_metadata_valid_write_line_and_tag (obs_meta: vect_t) : result (vect_t * vect_t) unit := *)
(*   let/res put_valid := _get_field metadata_input_sig "put_valid" obs_meta in *)
(*   let/res put_request := _get_field metadata_input_sig "put_request" obs_meta in *)
(*   let/res is_write := _get_field metadata_req_sig "is_write" put_request in *)
(*   let/res data := _get_field metadata_req_sig "data" put_request in *)
(*   let/res line := _get_field metadata_req_sig "addr" put_request in *)
(*   let/res tag := _get_field metadata_sig "tag" data in *)
(*   let/res valid := _get_field metadata_sig "valid" data in *)
(*   match put_valid, valid, is_write with *)
(*   | Ob~1, Ob~1, Ob~1 => Success (line, tag) *)
(*   | _, _, _ => Failure tt *)
(*   end. *)
(* (* Need invariant about get_ready *) *)
(* Definition get_cache_valid_write_to_line (obs_cache: vect_t) : result vect_t unit := *)
(*   let/res put_valid := _get_field cache_input_sig "put_valid" obs_cache in *)
(*   let/res put_request := _get_field cache_input_sig "put_request" obs_cache in *)
(*   let/res get_ready := _get_field cache_input_sig "get_ready" obs_cache in *)
(*   let/res line := _get_field cache_req_sig "addr" put_request in *)
(*   let/res byte_en := _get_field cache_req_sig "byte_en" put_request in *)
(*   match put_valid, get_ready, byte_en with *)
(*   | Ob~1, Ob~1, Ob~0~0~0~0 => Failure tt *)
(*   | Ob~1, Ob~1, Ob~1~1~1~1 => Success line *)
(*   | _, _, _ => Failure tt *)
(*   end. *)
(* Simplifying: If write valid to metadata, then also write to cache with the appropriate line
 *)

Record valid_cache_pair_obs (obs_meta obs_cache: vect_t) : Prop :=
  { WF_obs_meta_len : Datatypes.length obs_meta = _unsafe_struct_sz metadata_input_sig;
    WF_obs_cache_len : Datatypes.length obs_cache = _unsafe_struct_sz cache_input_sig;
    (* WF_meta_write: forall line tag, get_metadata_valid_write_line_and_tag obs_meta = Success (line, tag) -> *)
    (*                            get_cache_valid_write_to_line obs_cache = Success line; *)
    (* WF_single_cache_req: _get_field cache_input_sig "put_valid" obs_cache = Success Ob~1 -> *)
    (*                      _get_field cache_input_sig "get_ready" obs_cache = Success Ob~1; *)
    (* WF_single_meta_req: _get_field metadata_input_sig "put_valid" obs_meta = Success Ob~1 -> *)
    (*                     _get_field metadata_input_sig "get_ready" obs_meta = Success Ob~1; *)
  }.
Definition unblocked_cache cache obs :=
  match ExternalMemory.ext_cache_resp cache with
  | Some resp =>
      _get_field cache_input_sig "get_ready" obs = Success Ob~1
  | None => True
  end.
Definition valid_ghost_st (obs_cache: vect_t) (ghost_st: cache_ghost_state) : Prop :=
  _get_field cache_input_sig "put_valid" obs_cache = Success Ob~1 ->
  match _get_field cache_input_sig "put_request" obs_cache with
  | Success cache_put_request =>
      _get_field cache_req_sig "byte_en" cache_put_request = Success Ob~0~0~0~0 ->
      match ghost_cache_req_line ghost_st with
      | Some line =>
          _get_field cache_req_sig "addr" cache_put_request = Success line
      | None => False
      end
  | _ => False
  end.
Lemma _get_field_success':
  forall (struct_def : Types.struct_sig' Types.type) (fld : string) (v : list bool) (width : nat) value,
  match _lookup_struct struct_def with
  | Success s => Datatypes.length v = struct_sz' (dstruct_fields s)
  | Failure _ => False
  end ->
  match _lookup_struct struct_def with
  | Success s => get_field_width (dstruct_fields s) (unsafe_lookup_field_idx s fld) = Success width
  | Failure _ => False
  end ->
  _get_field struct_def fld v = Success value ->
  Datatypes.length value = width.
Proof.
  intros. specialize _get_field_success with (1 := H) (2 := H0).
  simpl_match; auto.
Qed.
Lemma update_cache_resp_still_eq_at_addr:
  forall impl_cache spec_cache impl_cache' spec_cache' obs,
  (forall n : N, impl_cache n = spec_cache n) ->
  ExternalMemory.update_cache obs impl_cache = Success impl_cache' ->
  ExternalMemory.update_cache obs spec_cache = Success spec_cache' ->
  ExternalMemory.ext_cache_resp impl_cache' = ExternalMemory.ext_cache_resp spec_cache'.
Proof.
  consider ExternalMemory.update_cache.
  intros. destruct_all_matches; simplify; simpl; auto.
  rewrite H in *. simplify. auto.
Qed.

(* Key property: impl and spec obs to cache are the same!
 *)
Lemma ext_mem_cache_sim_preserved:
  forall impl_cache spec_cache obs_meta obs_cache impl_cache' spec_cache',
  ext_mem_cache_sim impl_cache spec_cache ->
  ExternalMemory.cachepair__ext obs_meta obs_cache impl_cache = Success impl_cache' ->
  ExternalMemory.cachepair__ext obs_meta obs_cache spec_cache = Success spec_cache' ->
  valid_cache_pair_obs obs_meta obs_cache ->
  (* unblocked_cache (ExternalMemory.ext_pair_cache impl_cache) obs_cache -> *)
  (* valid_ghost_st obs_cache ghost_st' -> *)
  (* ghost_transition_ok ghost_st ghost_st' -> *)
  ext_mem_cache_sim impl_cache' spec_cache' .
Proof. (* DONE *)
  intros * hsim impl_pair spec_pair hvalid (* hunblocked_cache hghost *).
  apply ext_mem_cache_sim_implies_eq in hsim. subst.
  (* destruct hsim.  *)destruct hvalid.
  consider unblocked_cache. consider valid_ghost_st.
  consider ExternalMemory.cachepair__ext.
  destruct_matches_in_hyp_as impl_pair himpl_cache; [ | discriminate].
  destruct_matches_in_hyp_as impl_pair himpl_meta; [ | discriminate].
  (* destruct_matches_in_hyp_as spec_pair hspec_cache; [ | discriminate]. *)
  (* destruct_matches_in_hyp_as spec_pair hspec_meta; [ | discriminate]. *)
  simplify.

  consider ExternalMemory.cache__ext.
  destruct_matches_in_hyp_as himpl_cache obs_put_valid; [ | discriminate].
  destruct_matches_in_hyp_as himpl_cache obs_put_req; [ | discriminate].
  destruct_matches_in_hyp_as himpl_cache obs_get_ready; [ | discriminate].
  destruct_matches_in_hyp himpl_cache; [ discriminate | ].
  propositional.

  rename s into impl_cache'. rename s0 into impl_meta'.
  (* rename s1 into spec_cache'. rename s2 into spec_meta'. *)
  destruct v; [ | bash_destruct himpl_cache].
  rename s1 into cache_put_valid.
  rename s2 into cache_put_request.
  rename b into cache_get_ready.
  destruct cache_put_valid; [ bash_destruct himpl_cache | ].
  destruct cache_put_valid; [ | bash_destruct himpl_cache ].
  rename b into cache_put_valid.
  (* assert (impl_meta' = spec_meta'); subst. *)
  (* (* { eapply ext_cache_metadata_sim_preserved; eauto. } *) *)

  constructor; simpl; auto; [reflexivity |].
  - consider cache_resp_sim. simpl.
    auto.
    (* destruct_with_eqn cache_put_valid. *)
    (* { propositional. simplify. *)
    (*   eapply update_cache_resp_still_eq_at_addr; eauto. *)
    (* } *)
    (* { bash_destruct himpl_cache; simplify; auto. } *)
    (* consider ext_mem_metadata_sim. rewrite ext_cache_sim__meta0 in *. *)
    (* destruct_with_eqn cache_put_valid. *)
    (* { consider ExternalMemory.metadata__ext. simplify. *)
    (*   (* consider get_metadata_valid_write_line_and_tag. *) *)
    (*   consider get_cache_valid_write_to_line. repeat simpl_match. *)
    (*   rename s into meta_put_valid. *)
    (*   rename s0 into meta_put_request. *)
    (*   rename s1 into meta_get_ready. *)
    (*   destruct meta_get_ready; [ bash_destruct hspec_meta | ]. *)
    (*   destruct meta_get_ready; [ | bash_destruct hspec_meta ]. *)
    (*   rename b into meta_get_ready. *)
    (*   destruct meta_put_valid; [ bash_destruct hspec_meta | ]. *)
    (*   destruct meta_put_valid; [ | bash_destruct hspec_meta ]. *)
    (*   rename b into meta_put_valid. *)
    (*   consider get_metadata_valid. *)
    (*   propositional. simplify. *)
    (*   consider ExternalMemory.update_cache. simplify. *)
    (*   destruct (is_success (get_metadata_valid_write_line_and_tag obs_meta)) eqn:hmeta_update. *)
    (*   + consider @is_success. simplify. destruct s2. specialize WF_meta_write0 with (1 := eq_refl). *)
    (*     bash_destruct himpl_cache; simplify; simpl; auto. *)
    (*   + unfold get_metadata_valid_write_line_and_tag in hmeta_update. *)
    (*     consider @is_success. repeat simpl_match. *)
    (*     destruct meta_put_valid; propositional; simplify. *)
    (*     { consider ExternalMemory.update_metadata. simplify. *)
    (*       destruct_matches_in_hyp himpl_meta; simplify; simpl in *; repeat simpl_match; propositional. *)
    (*       { bash_destruct himpl_cache; simplify; propositional; simpl; simplify; auto; *)
    (*           specialize (ext_cache_sim__cache0 (to_N a)); *)
    (*           intros hmeta; bash_destruct hmeta; propositional; rewrite<-ext_cache_sim__cache0; *)
    (*           simpl_match; auto. *)
    (*       } *)
    (*       { destruct_matches_in_hyp himpl_cache; simplify; propositional; simpl; auto. *)
    (*         simplify. *)
    (*         specialize (ext_cache_sim__cache0 (to_N a)). intros hmeta. *)
    (*         assert_pre_and_specialize ext_cache_sim__cache0. *)
    (*         { bash_destruct hmeta; simplify. *)
    (*           assert (s2 = Ob~1); subst. *)
    (*           { assert (Datatypes.length s2 = 1). *)
    (*             { eapply _get_field_success'; eauto; simpl; [ | vm_reflect]. *)
    (*               eapply _get_field_success'; eauto; simpl; [ | vm_reflect]. *)
    (*               auto. *)
    (*             } *)
    (*             destruct s2; [ discriminate | ]. *)
    (*             destruct s2; [ | discriminate]. *)
    (*             destruct b; [ | congruence]. auto. *)
    (*           } *)
    (*           exfalso. *)
    (*           revert hmeta_update. *)
    (*           repeat unsafe_auto_simplify_structs; auto; [ | |discriminate]; *)
    (*             erewrite _get_field_length_implied; eauto; reflexivity. *)
    (*         } *)
    (*         rewrite ext_cache_sim__cache0; auto. *)
    (*       } *)
    (*     } *)
    (*     { assert (ExternalMemory.ext_metadata spec_meta' = *)
    (*                 ExternalMemory.ext_metadata (ExternalMemory.ext_pair_meta spec_cache)) as hmeta_eq. *)
    (*         { bash_destruct hspec_meta; simplify; auto. } *)
    (*         rewrite hmeta_eq. *)
    (*         destruct_matches_in_hyp himpl_cache; simplify; propositional; simpl; auto. *)
    (*         simplify. *)
    (*         specialize (ext_cache_sim__cache0 (to_N a)); *)
    (*         intros hmeta; bash_destruct hmeta; propositional. *)
    (*         rewrite<-ext_cache_sim__cache0. auto. *)
    (*      } *)
    (*   } *)
    (* { destruct_with_eqn cache_get_ready; simplify; simpl; auto. *)
    (*   bash_destruct ext_cache_sim__cache_resp0. *)
    (* } *)
  (* - destruct_with_eqn cache_put_valid. *)
  (*   { propositional. simplify. *)
  (*     eapply update_cache_still_eq_at_addr; eauto. *)
  (*   } *)
  (*   { bash_destruct himpl_cache; simplify; auto. } *)

    (* consider ext_mem_metadata_sim. rewrite ext_cache_sim__meta0 in *. *)
    (* intros * hvalid. *)
    (* destruct_with_eqn (beq_dec (get_metadata_valid (ExternalMemory.ext_metadata (ExternalMemory.ext_pair_meta spec_cache) n)) Ob~1); simplify. *)
    (* + specialize ext_cache_sim__cache0 with (1 := Heqb). *)
    (*   bash_destruct hspec_cache; simplify; auto. *)
    (*   * eapply update_cache_still_eq_at_addr; eauto. *)
    (*   * bash_destruct ext_cache_sim__cache_resp0; auto. propositional. *)
    (*     rewrite<-ext_cache_sim__cache0 in *. *)
    (*     bash_destruct hunblocked_cache. *)
    (*   * propositional. bash_destruct hunblocked_cache. *)
    (* + rewrite himpl_meta in hspec_meta. simplify. *)
    (*   consider get_metadata_valid. bash_destruct hvalid. *)
    (*   consider ExternalMemory.metadata__ext. simplify. *)
    (*   rename s into meta_put_valid. *)
    (*   rename s0 into meta_put_request. *)
    (*   rename s1 into meta_get_ready. *)

    (*   assert (Datatypes.length meta_put_valid = 1) as Hmeta_put_valid_len. *)
    (*   { eapply _get_field_success'; eauto; simpl; [ | vm_reflect]. auto. } *)

    (*   destruct meta_put_valid; [discriminate | ]. *)
    (*   destruct meta_put_valid; [| discriminate ]. *)
    (*   destruct (is_success (get_metadata_valid_write_line_and_tag obs_meta)) eqn:hmeta_update. *)
    (*   { consider @is_success. simplify. destruct s. specialize WF_meta_write0 with (1 := eq_refl). *)
    (*     consider get_cache_valid_write_to_line. simplify. propositional. *)
    (*     consider ExternalMemory.update_cache. simplify. *)
    (*     destruct_matches_in_hyp himpl_cache; simplify; simpl. *)
    (*     assert (n = to_N s); subst. *)
    (*     { destruct b; propositional; simplify. *)
    (*       - consider ExternalMemory.update_metadata. simplify. *)
    (*         bash_destruct himpl_meta; simplify; simpl in *. *)
    (*         + repeat simpl_match. congruence. *)
    (*         + repeat simpl_match. congruence. *)
    (*         + bash_destruct Heqo; simplify; auto. *)
    (*           2: { repeat simpl_match. congruence. } *)
    (*           assert (s0 = Ob~1~1~1~1); subst. *)
    (*           { bash_destruct WF_meta_write0. } *)
    (*           simplify. *)
    (*           consider get_metadata_valid_write_line_and_tag. *)
    (*           simplify. *)
    (*           bash_destruct Heqr4. *)
    (*       - bash_destruct himpl_meta; simplify; simpl in *; repeat simpl_match; try congruence. *)
    (*     } *)
    (*     rewrite beq_dec_refl. *)
    (*     assert (s0 = Ob~1~1~1~1); subst. *)
    (*     { bash_destruct WF_meta_write0. } *)
    (*     repeat rewrite compute_with_byte_en_store. reflexivity. *)
    (*   } *)
    (*   { assert (ExternalMemory.ext_metadata spec_meta' = *)
    (*                 ExternalMemory.ext_metadata (ExternalMemory.ext_pair_meta spec_cache)) as hmeta_eq. *)
    (*     { destruct b; propositional; simplify. *)
    (*       - unfold get_metadata_valid_write_line_and_tag in hmeta_update. *)
    (*         unfold ExternalMemory.update_metadata in himpl_meta. *)
    (*         repeat simpl_match. simplify. *)
    (*         destruct_matches_in_hyp himpl_meta; simplify; simpl in *; repeat simpl_match; auto. *)
    (*         apply functional_extensionality. intros. *)
    (*         destruct_match; simplify; auto. *)
    (*         bash_destruct Heqo; simplify; simpl_match; auto. *)
    (*         { exfalso. *)
    (*           revert hmeta_update. *)
    (*           unsafe_auto_simplify_structs. *)
    (*           { erewrite _get_field_length_implied; eauto; reflexivity. } *)
    (*           unsafe_auto_simplify_structs. *)
    (*           { erewrite _get_field_length_implied; eauto; reflexivity. } *)
    (*           assert (Datatypes.length s = 1). *)
    (*           { eapply _get_field_success'; eauto; simpl; [ | vm_reflect]. *)
    (*             eapply _get_field_success'; eauto; simpl; [ | vm_reflect]. *)
    (*             auto. *)
    (*           } *)
    (*           destruct s ; [discriminate | ]. *)
    (*           destruct s ; [| discriminate ]. *)
    (*           destruct b; [ discriminate | ]. *)
    (*           congruence. *)
    (*         } *)
    (*         { simpl_match. congruence. } *)
    (*       - bash_destruct himpl_meta; simplify; auto. *)
    (*     } *)
    (*     rewrite hmeta_eq in Heqo. repeat simpl_match. congruence. *)
    (*    } *)
Qed. (* DONE *)


Lemma ext_mem_sim_preserved:
  forall core config impl_mem impl_mem' spec_mem spec_mem' cycles impl_log spec_log ,
  ext_mem_sim core config impl_mem spec_mem cycles  ->
  (is_mem_core_write_turn' core cycles = true ->
   (obs_mainmem (get_mem_observations impl_log)) = (obs_mainmem (get_mem_observations spec_log))) ->
  (_unsafe_get_field mem_input "put_valid"
                        (obs_mainmem (get_mem_observations impl_log)) = Ob~0 \/
    is_mem_core_write_turn' core cycles = true \/
    is_mem_core_write_turn' (other_core core) cycles = true)  ->
  (_unsafe_get_field mem_input "put_valid" (obs_mainmem (get_mem_observations spec_log))) = Ob~0 \/
    is_mem_core_write_turn' core cycles = true ->
  (is_mem_core_write_turn' (other_core core) cycles = true ->
   match get_valid_addr_from_push_req (obs_mainmem (get_mem_observations impl_log)) with
   | Some addr => addr_in_config (to_N addr) config -> False
   | None => True
   end ) ->
  (is_mem_core_write_turn' (core) cycles = true ->
   match get_valid_addr_from_push_req (obs_mainmem (get_mem_observations impl_log))  with
   | Some addr => addr_in_config (to_N addr) config
   | None => True
   end ) ->
  ExternalMemory.update_memory (get_mem_observations (impl_log)) impl_mem = Success impl_mem' ->
  ExternalMemory.update_memory (get_mem_observations (spec_log)) spec_mem = Success spec_mem' ->
  (forall cache, (obs_meta (get_mem_observations impl_log) cache core) =
            (obs_meta (get_mem_observations spec_log) cache core)) ->
  (forall cache, (obs_cache (get_mem_observations impl_log) cache core) =
            (obs_cache (get_mem_observations spec_log) cache core)) ->
  (forall cache, valid_cache_pair_obs (obs_meta (get_mem_observations impl_log) cache core)
                                 (obs_cache (get_mem_observations impl_log) cache core)) ->
  (* (forall cache, unblocked_cache (ExternalMemory.ext_pair_cache (ExternalMemory.ext_l1_caches impl_mem cache core)) *)
  (*                           (obs_cache (get_mem_observations impl_log) cache core)) -> *)
  (* (forall cache, valid_ghost_st (obs_cache (get_mem_observations impl_log) cache core) (ghost_st' cache)) -> *)
  ext_mem_sim core config impl_mem' spec_mem' (cycles + 1) .
Proof.
  intros * hsim hpush_sim himpl_zeroes hspec_zeroes haddr hcore_addr himpl hspec
             hobs_meta_eq hobs_cache_eq (* hunblocked hghost *).
  consider ExternalMemory.update_memory.
  destruct_matches_in_hyp_as himpl himpl_main_mem; [ | discriminate].
  destruct_matches_in_hyp_as himpl himpl_icache0; [ | discriminate].
  destruct_matches_in_hyp_as himpl himpl_dcache0; [ | discriminate].
  destruct_matches_in_hyp_as himpl himpl_icache1; [ | discriminate].
  destruct_matches_in_hyp_as himpl himpl_dcache1; [ | discriminate].
  destruct_matches_in_hyp_as hspec hspec_main_mem; [ | discriminate].
  destruct_matches_in_hyp_as hspec hspec_icache0; [ | discriminate].
  destruct_matches_in_hyp_as hspec hspec_dcache0; [ | discriminate].
  destruct_matches_in_hyp_as hspec hspec_icache1; [ | discriminate].
  destruct_matches_in_hyp_as hspec hspec_dcache1; [ | discriminate].
  simplify.
  destruct hsim.
  constructor; simpl.
  - eapply ext_main_mem_sim_preserved; eauto.
  - eapply ext_main_mem_sim_preserved; eauto.
  - intros.
    repeat destruct_match; subst;
    eapply ext_mem_cache_sim_preserved; eauto;
      rewrite hobs_meta_eq; rewrite hobs_cache_eq; auto.
Qed.
Lemma is_mem_core_write_turn_iff:
  forall core st cycles,
  st.[_rid (Memory (Memory.turn))] = Bits.of_nat 2 (Nat.modulo cycles 4) ->
  is_mem_core_write_turn core st = is_mem_core_write_turn' core cycles.
Proof.
  consider is_mem_core_write_turn. consider is_mem_core_write_turn'.
  intros * hturn.
  rewrite hturn.
  pose proof (PeanoNat.Nat.mod_bound_pos cycles0 4) as Hcycles.
  assert_pre_and_specialize Hcycles; [lia | ].
  assert_pre_and_specialize Hcycles; [lia | ].
  set (Nat.modulo cycles0 4) in *.
  destruct core; simplify.
  - consider mem_core0_write_turn.
    do 4 (destruct n; auto). lia.
    (* apply of_nat_to_nat in H. set (pow2 _ ) in *. vm_compute in n. subst n. *)
    (* rewrite PeanoNat.Nat.mod_mod in H by lia. rewrite H in * . cbv in Heqb. congruence. *)
  - do 4 (destruct n; auto). lia.
Qed.
Ltac unfold_head_term t :=
  match t with
  | ?x ?y => unfold_head_term x
  | _ => unfold t
  end.

Ltac unfold_head :=
  match goal with
  | |- ?x = _ => unfold_head_term x
  | |- ?y ?z => unfold_head_term y
  end.

Lemma is_mem_core_write_turn_iff':
  forall core st cycles,
    st.[_rid (Memory (Memory.turn))]  = Bits.of_nat 2 (Nat.modulo cycles 4) ->
  is_mem_core_write_turn' core cycles = true <->
    st.[_rid (Memory (Memory.turn))]   = mem_core_write_turn core.
Proof.
  intros. eapply is_mem_core_write_turn_iff with (core := core) in H.
  rewrite<-H. unfold is_mem_core_write_turn.
  split; destruct core; propositional; simplify; auto.
  - rewrite beq_dec_iff. auto.
  - rewrite beq_dec_iff. auto.
Qed.
Lemma impl_mem_update':
  forall (impl_st impl_st' : PfImplDefs.impl_state_t) (log : ext_log_t),
    ImplPost impl_st impl_st' log ->
    ExternalMemory.update_memory (get_mem_observations log) (machine_mem_st impl_st) =
      Success (machine_mem_st impl_st').
Proof.
  intros * hpost. destruct hpost.
  unfold_head.
  setoid_rewrite impl_mem_update0.
  setoid_rewrite (impl_cache_update0 imem CoreId0).
  setoid_rewrite (impl_cache_update0 dmem CoreId0).
  setoid_rewrite (impl_cache_update0 imem CoreId1).
  setoid_rewrite (impl_cache_update0 dmem CoreId1).
  f_equal. destruct impl_st'; simpl.
  destruct machine_mem_st0; simpl.
  f_equal.
  do 2 (apply functional_extensionality; intros).
  repeat destruct_match; auto.
Qed.
Lemma WF_meta_len:
  forall cache core log,
  WF_ext_log _ext_fn_tys log ->
  Datatypes.length (obs_meta (get_mem_observations log) cache core) = _unsafe_struct_sz metadata_input_sig.
Proof.
  consider WF_ext_log. consider get_mem_observations. simpl.
  intros. consider _unsafe_get_ext_call_from_log. unfold SemanticUtils.unsafe_get_ext_call_from_log.
  destruct_match; auto; destruct_match; auto; try destruct_match; auto; subst;
    destruct core; auto;
    specialize H with (1 := Heqo); propositional; cbn in H0; simplify; auto.
Qed.
Lemma WF_cache_len:
  forall cache core log,
  WF_ext_log _ext_fn_tys log ->
  Datatypes.length (obs_cache (get_mem_observations log) cache core) = _unsafe_struct_sz cache_input_sig.
Proof.
  consider WF_ext_log. consider get_mem_observations. simpl.
  intros. consider _unsafe_get_ext_call_from_log. unfold SemanticUtils.unsafe_get_ext_call_from_log.
  destruct_match; auto; destruct_match; auto; try destruct_match; auto; subst;
    destruct core; auto;
    specialize H with (1 := Heqo); propositional; cbn in H0; simplify; auto.
Qed.


Lemma SimPost_implied_core:
  forall external_world_state_t core impl_st spec_st (ext_world: external_world_state_t) input_machine log mem_st' spec_ext_mem' spec_log machine_st config,
  Sim impl_st spec_st ->
  impl_step impl_st ext_world input_machine = Success log ->
  ImplPost impl_st
                 {|
                   machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log);
                   machine_mem_st := mem_st'
                 |} (Log__ext log) ->
  machine_state spec_st core = CoreState_Enclave machine_st config ->
  machine_step machine_st (filter_input (Some config) (i_get_output input_machine ext_world)) (spec_schedule core) = Success spec_log ->
  SpecCoreInvariant__Running core machine_st config ->
  ExternalMemory.update_memory (get_mem_observations (Log__ext spec_log))
            (machine_mem_st machine_st) = Success spec_ext_mem' ->
  strong_WF_state reg_type_env (commit_update (machine_koika_st machine_st) (Log__koika spec_log)) ->
  WF_ext_log _ext_fn_tys (Log__ext spec_log) ->
  WF_ext_mem spec_ext_mem' ->
  Pf.SimPost core impl_st
    {| machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log); machine_mem_st := mem_st' |}
    machine_st
    {| machine_koika_st := commit_update (machine_koika_st machine_st) (Log__koika spec_log); machine_mem_st := spec_ext_mem' |}
    config log
    (get_observations (machine_koika_st machine_st)
       (commit_update (machine_koika_st machine_st) (Log__koika spec_log)) (Log__ext spec_log)) (cycles spec_st + 1).
Proof.
  unfold impl_step.
  intros * hsim himpl_step himpl_post hspec_st hspec_step hspec_running hspec_push hwf_spec' hwf_spec_log hwf_spec_mem'.
  specialize PfLemmas.impl_interp_cycle_correct with
    (sigma := (mk_sigma_fn (machine_mem_st impl_st) (i_get_output input_machine ext_world)))
    (koika_st := machine_koika_st impl_st). intros hsched.
  assert_pre_and_specialize hsched; eauto with modularity.
  assert_pre_and_specialize hsched; eauto with modularity.
  simplify.  destruct hsched as (hwf_impl' & hwf_impl_log).

  assert (running_sim core impl_st config machine_st (cycles spec_st)) as Hrunning_sim.
  { specialize Sim_machine_state with (1 := hsim) (core_id := core). unfold machine_sim. simpl_match; auto. }

  setoid_rewrite himpl_step in Heqr0. simplify. rename s into log.
  consider machine_step.
  specialize_spec_sim core step_sim_sched_correct
    HSimPre HSimPost himpl_step hspec_step tt
    wf_impl' wf_spec'  wf_iext' wf_sext'.
  { eapply running_sim__pre; eauto. }

  specialize running_sim__ghost with (1 := Hrunning_sim) as hghost.
  apply machine_st_to_ghost_core_enclave in hghost. subst.

  assert (forall input, SimPreInvariants core (commit_update (machine_koika_st impl_st) (Log__koika log))
    (commit_update (machine_koika_st machine_st) (Log__koika spec_log)) (mk_sigma_fn mem_st' input)
    (mk_sigma_fn spec_ext_mem'
       (filter_input
          (Some (unsafe_enclave_data_to_config (machine_koika_st impl_st).[_rid (SM (enc_data core))]))
          input))) as Hpre.
  { intros. eapply SimPost_implies_SimPreInvariants; eauto.
  }

  constructor; auto.
  - intros. eapply SimPre_stay_implied; auto.
    * eauto with modularity.
    * eauto with modularity.
    * eapply SimPreIgnoresInputs; eauto.
      { clear - hspec_running.
        apply SpecInv_WF_state in hspec_running.
        apply strong_WF_state_weaken in hspec_running.
        destruct core; unsafe_auto_simplify_structs.
      }
      { prop_pose_with_custom foo (CustomSmSim (SmSim__Regs)) HSimPre.
        setoid_rewrite foo; auto. destruct core; solve_In_to_find.
      }
    * eapply SimPostIgnoresInputs; eauto.
    * apply impl_mem_update'; auto.
    * eapply running_sim__ghost; eauto.
    * unfold dram_sim_at_config. eapply ext_mem_sim__dram. eapply running_sim__ext_mem; eauto.
    * eapply ext_mem_sim__caches. eapply running_sim__ext_mem; eauto.
  - (* DONE *)
    destruct core.
    + prop_apply_with_custom (CustomSm (SM_config_same CoreId0)) HSimPost.
    + prop_apply_with_custom (CustomSm (SM_config_same CoreId1)) HSimPost.
  - (* ext uart sim *)
    simpl.
    intros huart; simplify. split.
    + prop_apply_with_custom CustomExtUartWriteSim HSimPost; auto.
    + prop_apply_with_custom CustomExtUartReadSim HSimPost; auto.
  - (* ext led sim *)
    (* DONE *)
    simpl.
    intros hled; simplify.
    prop_apply_with_custom CustomExtLedSim HSimPost; auto.
  - (* DONE *)
    simpl.
    intros hfinish ; simplify.
    prop_apply_with_custom CustomExtFinishSim HSimPost; auto.
  - eapply ext_mem_sim_preserved with (1 := running_sim__ext_mem _ _ _ _ _ Hrunning_sim)
                                      (impl_log := Log__ext log) (spec_log := Log__ext spec_log).
    + rewrite is_mem_core_write_turn_iff' by eauto with modularity.
      intros.
      prop_apply_with_custom CustomExtMemPushRequest__Sim HSimPost; auto.
      cbn - [_id]. auto.
      (* (_ext ext_mainmem) sim *)
    + repeat rewrite is_mem_core_write_turn_iff' by eauto with modularity.
      prop_apply_with_custom CustomExtMemPushRequest__ImplInvalidOrWriteTurn HSimPost; auto.
      (* push request prop *)
    + repeat rewrite is_mem_core_write_turn_iff' by eauto with modularity.
      prop_apply_with_custom CustomExtMemPushRequest__SpecInvalidOrWriteTurn HSimPost; auto.
    + rewrite is_mem_core_write_turn_iff' by eauto with modularity.
      intros hturn.
      prop_pose_with_custom hfoo CustomExtMemPushRequest__NotInConfig HSimPost.

      eapply addr_not_in_config_implies with
        (final_st := commit_update (machine_koika_st impl_st) (Log__koika log)); auto.
      { eapply ImplInv_WF_state. eauto with modularity. }
      cbn - [_id fs_addr_not_in_config mk_sigma_fn filter_input] in hfoo.
      propositional.
      apply hfoo.
      specialize running_sim__ghost with (1 := Hrunning_sim).
      unfold machine_st_to_ghost_core. destruct_match; simplify; auto. discriminate.
    + specialize wf_mem_push with (1 := impl_wf_log _ _ _ himpl_post).
      intros * hwf hturn. consider mem_push_in_config.
      consider is_mem_core0_push_turn. consider is_mem_core1_push_turn.
      rewrite Sim_cycles_mem with (1 :=hsim)  in hwf.
      consider is_mem_core_write_turn'.
      consider spec_cycles_to_bits.
      destruct core; simplify.
      { rewrite hturn in hwf. simpl in hwf.
        rewrite running_sim__ghost with (1 := Hrunning_sim) in hwf; auto.
      }
      { rewrite hturn in hwf. simpl in hwf.
        rewrite running_sim__ghost with (1 := Hrunning_sim) in hwf; auto.
      }
    + apply impl_mem_update'; auto.
    + auto.
    + intros. clear - HSimPost.
      wrap_solve_cache_post_implies CustomMemSim MemSimMetadata HSimPost.
    + intros. clear - HSimPost.
      wrap_solve_cache_post_implies CustomMemSim MemSimCache HSimPost.
    + intros; constructor.
      * apply WF_meta_len; auto.
      * apply WF_cache_len; auto.
  - reflexivity.
  - reflexivity.
Unshelve. exact ((fun _ _ => Failure tt) : ext_sigma_t).
Qed.


Lemma step_enclave_sim :
  forall external_world_state_t impl_st spec_st core config machine_st
    input_machine (ext_world: external_world_state_t)
    log mem_st' local_output machine_st',
    Sim impl_st spec_st ->
    (* obs_exit_enclave local_output core = None -> *)
    machine_state spec_st core = CoreState_Enclave machine_st config  ->
    spec_step_core core (CoreState_Enclave machine_st config) (i_get_output input_machine ext_world)
                   machine_st = (machine_st', local_output) ->
    impl_step impl_st ext_world input_machine = Success log ->
    ImplPost impl_st
           {|
             machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log);
             machine_mem_st := mem_st'
           |} (Log__ext log) ->
    SpecCorePost core machine_st config machine_st' local_output ->
    Pf.SimPost core impl_st
           {|
             machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log);
             machine_mem_st := mem_st'
           |}
           machine_st machine_st' config log local_output (spec_st.(cycles) + 1).
Proof.
  consider @impl_step. consider spec_step_core.
  unfold local_step_fn0, local_step_fn1 in *.
  unfold Core0Machine.step, Core1Machine.step, unsafe_machine_step_local_obs in *.
  intros * hsim hspec_st hspec_step himpl_step himpl_post hspec_post.
  specialize spec_machine_inv with (1 := Sim_spec_invariant _ _ hsim) (core := core); intros hspec_running.
  rewrite hspec_st in hspec_running. simpl in hspec_running.

  destruct core.
  - specialize spec0_interp_cycle_correct with
      (1 := SpecInv_WF_state _ _ _ hspec_running)
      (2 := WF_mk_sigma_fn _ (filter_input (get_core_config (CoreState_Enclave machine_st config))
                                (i_get_output input_machine ext_world))
                             (SpecInv_ExtMem _ _ _ hspec_running) ).
    intros hsuccess. simplify. destruct hsuccess as (hwf_spec' & hwf_ext_log).
    revert hspec_step.
    unfold Machine.machine_step_local_obs. unfold Machine.koika_step. unfold Machine.koika_step'.
    unfold interp_cycle'. setoid_rewrite Heqr0. simpl. intros hspec_step.
    simpl in hspec_step.
    specialize update_memory_success with
      (1 := hwf_ext_log) (2 :=  SpecInv_ExtMem _ _ _ hspec_running); intros hupdate. simplify.
    eapply SimPost_implied_core with (2 := himpl_step); auto.
  - specialize spec1_interp_cycle_correct with
      (1 := SpecInv_WF_state _ _ _ hspec_running)
      (2 := WF_mk_sigma_fn _ (filter_input (get_core_config (CoreState_Enclave machine_st config))
                                (i_get_output input_machine ext_world))
                             (SpecInv_ExtMem _ _ _ hspec_running) ).
    intros hsuccess. simplify. destruct hsuccess as (hwf_spec' & hwf_ext_log).
    revert hspec_step.
    unfold Machine.machine_step_local_obs. unfold Machine.koika_step. unfold Machine.koika_step'.
    unfold interp_cycle'. setoid_rewrite Heqr0. simpl. intros hspec_step.
    simpl in hspec_step.
    specialize update_memory_success with
      (1 := hwf_ext_log) (2 :=  SpecInv_ExtMem _ _ _ hspec_running); intros hupdate. simplify.
    eapply SimPost_implied_core with (2 := himpl_step); auto.
Qed.
Lemma SimPreInvariants_implies_reg_sim:
  forall core impl_st spec_st config input,
  (SimPreInvariants core (machine_koika_st impl_st) (machine_koika_st spec_st)
                                 (mk_sigma_fn (machine_mem_st impl_st) input)
                                 (mk_sigma_fn (machine_mem_st spec_st) (filter_input (Some config) input))) ->
  forall reg,
  In reg (map reg_to_debug_id [SM (state core); (SM (enc_req core)); SM (enc_data core)]) ->
  (machine_koika_st impl_st).[_id reg] = (machine_koika_st spec_st).[_id reg].
Proof. (* DONE *)
  intros * hinv hreg.
  consider SimPreInvariants.
  prop_pose_with_custom hfoo (CustomSmSim SmSim__Regs) hinv.
  cbn - [_id In sm_regs] in hfoo. intros.
  apply hfoo. destruct core; eapply In_subset with (2 := H); eauto.
Qed. (* DONE *)


Lemma SimPost_implies_reg_sim:
  forall core impl_st impl_st' spec_st spec_st' config impl_out spec_out cycles reg,
  Pf.SimPost core impl_st impl_st' spec_st spec_st' config impl_out spec_out cycles ->
  In reg (map reg_to_debug_id [SM (state core); (SM (enc_req core)); SM (enc_data core)]) ->
  (machine_koika_st impl_st').[_id reg] = (machine_koika_st spec_st').[_id reg].
Proof.
  intros * hsim hin.
  specialize SimPost__Invariants with (1 := hsim) (input := dummy_input); intros hinvariants.
  eapply SimPreInvariants_implies_reg_sim; eauto.
Qed.

Lemma SimPreInvariants_implies_core_sim:
  forall core impl_st spec_st config input,
  (SimPreInvariants core (machine_koika_st impl_st) (machine_koika_st spec_st)
                                 (mk_sigma_fn (machine_mem_st impl_st) input)
                                 (mk_sigma_fn (machine_mem_st spec_st) (filter_input (Some config) input))) ->
  forall reg,
  In reg (map reg_to_debug_id (map (core_reg core) (map Core.rf FiniteType.finite_elements))) ->
  (machine_koika_st impl_st).[_id reg] = (machine_koika_st spec_st).[_id reg].
Proof. (* DONE *)
  intros * hinv hreg.
  consider SimPreInvariants.
  prop_pose_with_custom hfoo (CustomCoreSim CoreSimRegs) hinv.
  cbn - [_id In core_regs] in hfoo. intros.
  apply hfoo. destruct core; eapply In_subset with (2 := H); eauto.
Qed. (* DONE *)

Lemma SimPost_implies_core_sim:
  forall core impl_st impl_st' spec_st spec_st' config impl_out spec_out cycles reg,
  Pf.SimPost core impl_st impl_st' spec_st spec_st' config impl_out spec_out cycles ->
  In reg (map reg_to_debug_id (map (core_reg core) (map Core.rf FiniteType.finite_elements))) ->
  (machine_koika_st impl_st').[_id reg] = (machine_koika_st spec_st').[_id reg].
Proof.
  intros * hsim hin.
  specialize SimPost__Invariants with (1 := hsim) (input := dummy_input); intros hinvariants.
  eapply SimPreInvariants_implies_core_sim; eauto.
Qed.

Lemma spec_sim_stay:
  forall core machine_st config machine_st' impl_st' impl_st impl_out cycles spec_out,
  Pf.SimPost core impl_st impl_st' machine_st machine_st' config impl_out spec_out cycles ->
  SpecCorePost core machine_st config machine_st' spec_out ->
  obs_exit_enclave spec_out core = None ->
  machine_st_to_ghost_core (machine_koika_st machine_st) core SecurityParams.extract_rf = GhostCoreState_Enclave config ->
  machine_st_to_ghost_core (machine_koika_st impl_st') core SecurityParams.extract_rf = GhostCoreState_Enclave config.
Proof.
  intros * hsim hspec hstay hconfig.
  specialize SpecPost__obs_exit with (1 := hspec).
  consider spec_post_obs_exit. simpl_match. propositional.
  consider machine_st_to_ghost_core.
  setoid_rewrite SimPost_implies_reg_sim with (1 := hsim); [ | destruct core; solve_In_to_find].
  setoid_rewrite SimPost_implies_reg_sim with (1 := hsim); [ | destruct core; solve_In_to_find].
  setoid_rewrite SimPost_implies_reg_sim with (1 := hsim); [ | destruct core; solve_In_to_find].

  destruct_match; simplify.
  - setoid_rewrite Heqb in H0. congruence.
  - bash_destruct hconfig; simplify.
    inversions hconfig. setoid_rewrite H1. auto.
Qed.


Lemma step_running_sim :
  forall external_world_state_t impl_st spec_st core config machine_st
    input_machine (ext_world: external_world_state_t)
    log mem_st' local_output machine_st',
    Sim impl_st spec_st ->
    obs_exit_enclave local_output core = None ->
    machine_state spec_st core = CoreState_Enclave machine_st config  ->
    spec_step_core core (CoreState_Enclave machine_st config) (i_get_output input_machine ext_world)
                   machine_st = (machine_st', local_output) ->
    impl_step impl_st ext_world input_machine = Success log ->
    ImplPost impl_st
           {|

             machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log);
             machine_mem_st := mem_st'
           |} (Log__ext log) ->
   running_sim core
     {| machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log); machine_mem_st := mem_st' |}
     config machine_st' (cycles spec_st + 1) /\
   local_output_sim (get_ext_observations (Log__ext log)) (obs_ext local_output) (Some config).
Proof.
  intros * hsim hstay hspec_st hspec_step himpl_step himpl_post .
  specialize spec_machine_inv with (1 := Sim_spec_invariant _ _ hsim) (core := core).
  rewrite hspec_st. simpl.
  intros hrunning_inv.

  specialize Sim_machine_state with (1 := hsim) (core_id := core); intros hrunning.
  rewrite hspec_st in *. simpl in hrunning.
  specialize PfSpecLemmas.spec_step_core_invariant with (1 := hrunning_inv) (2 := hspec_step). intros hspec_post.
  assert(Pf.SimPost core impl_st
           {|
             machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log);
             machine_mem_st := mem_st'
           |}
           machine_st machine_st' config log local_output (spec_st.(cycles) + 1)) as HSimPost.
  { eapply step_enclave_sim ; eauto. }
  split_ands_in_goal.
  - constructor; cbn - [filter_input _id]; auto.
    + eapply spec_sim_stay with (1 := HSimPost); eauto with solve_invariants.
    + specialize SimPost__Pre with (1 := HSimPost) (2 := hstay).
      intros * hpre'. intros.
eapply hpre'.
    + inversions HSimPost; auto.
    + inversions HSimPost; auto.
  - constructor.
    + eapply wf_ext; eauto. eapply impl_wf_log; eauto.
    + eapply SpecPost__wf_ext_obs; eauto.
    + eapply SpecPost__wf_spec_output_config; eauto.
    + split_ands_in_goal.
      * inversion HSimPost; eauto.
      * inversion HSimPost; eauto.
      * inversion HSimPost; eauto.
Qed.


Lemma Sim_impl_configs_eq:
  forall impl_st spec_st core,
    Sim impl_st spec_st ->
    get_spec_configs spec_st core = get_impl_config (machine_koika_st impl_st) core SecurityParams.extract_rf.
Proof.
  intros * Hsim.
  pose proof (Sim_machine_state _ _ Hsim core) as Hmachine.
  unfold get_spec_configs, get_impl_config.
  consider machine_sim. consider impl_is_waiting.
  bash_destruct Hmachine; auto.
  - erewrite running_sim__ghost by eauto. reflexivity.
  - rewrite_solve.
Qed.
Lemma SimPre_implies:
  forall core st1 st2 sigma1 sigma2 st1' st2' sigma1' sigma2',
  st1 = st1' ->
  st2 = st2' ->
  sigma1 = sigma1' ->
  sigma2 = sigma2' ->
  SimPre EnclaveParams.enclave_sig core st1 st2 sigma1 sigma2 ->
  SimPre EnclaveParams.enclave_sig core st1' st2' sigma1' sigma2'.
Proof.
  propositional.
Qed.
Lemma sim_cycles_plus:
  forall bits1 bits2 nat1,
  bits1 = spec_cycles_to_bits (nat1) ->
  plus bits1 (of_nat 2 1) = Success bits2 ->
  bits2 = spec_cycles_to_bits (nat1 + 1).
Proof.
  unfold spec_cycles_to_bits.
  intros.
  pose proof (PeanoNat.Nat.mod_upper_bound nat1 4).
  propositional.
  rewrite PeanoNat.Nat.add_mod by lia.
  destruct_with_eqn (PeanoNat.Nat.modulo nat1 4); [ cbv in *; simplify; auto | ].
  destruct n; [ cbv in *; simplify; auto | ].
  destruct n; [ cbv in *; simplify; auto | ].
  destruct n; [ cbv in *; simplify; auto | ].
  lia.
Qed.
Lemma plus_one:
  forall b1 ,
  plus [b1] (of_nat 1 1) = Success [negb b1].
Proof.
  intros.
  cbn. destruct_match; subst; simpl; auto.
Qed.
Lemma nat_odd_plus_one:
  forall n,
  Nat.odd (n  + 1 ) = negb (Nat.odd n).
Proof.
  intros.
  rewrite PeanoNat.Nat.add_1_r.
  rewrite PeanoNat.Nat.odd_succ.
  rewrite PeanoNat.Nat.negb_odd. auto.
Qed.
Lemma region_in_config_conflict:
  forall region config1 config2,
  region_in_config region config1 = true ->
  region_in_config region config2 = true ->
  configs_conflict config1 (Some config2) = true.
Proof.
  intros * hconfig1 hconfig2.
  consider @configs_conflict. consider region_in_config.
  bash_destruct hconfig1; simplify; try rewrite hconfig1; simpl.
  - rewrite internal_enclave_id_dec_lb; auto.
  - consider shared_regions_conflict. destruct id; rewrite hconfig1; rewrite hconfig2; simpl; repeat rewrite orb_true_r; auto.
Qed.

Lemma addr_in_configs_conflict:
  forall config1 config2 addr,
  addr_in_config addr config1 ->
  addr_in_config addr config2 ->
  configs_conflict config1 (Some config2) = true.
Proof.
  intros * haddr1 haddr2. unfold addr_in_config. unfold addr_in_config in *.
  propositional.
  pose proof EnclaveParams.pf_disjoint_configs as hdisjoint. consider Common.wf_disjoint_configs.
  specialize hdisjoint with (1 := haddr1) (2 := haddr2). subst.
  eapply region_in_config_conflict; eauto.
Qed.


Lemma addr_in_disjoint_config:
  forall impl_st core new e addr,
  can_enter_enclave new (get_impl_config impl_st (other_core core) SecurityParams.extract_rf) = true ->
  addr_in_config addr new ->
  get_ghost_running_config (machine_st_to_ghost_core (impl_st) (other_core core) SecurityParams.extract_rf) =
         Some e ->
  addr_in_config addr e ->
  False.
Proof.
  intros * henter haddr0 hother haddr1.
  consider can_enter_enclave.
  consider get_impl_config. rewrite hother in *.
  rewrite negb_true_iff in henter.
  pose proof (addr_in_configs_conflict _ _ _ haddr0 haddr1). congruence.
Qed.

Lemma ext_mem_unchanged_at_addr:
  forall impl_st core addr new mem_st' log rf,
  machine_st_to_ghost_core (machine_koika_st impl_st) core SecurityParams.extract_rf = GhostCoreState_Waiting new rf ->
  can_enter_enclave new (get_impl_config impl_st.(machine_koika_st) (other_core core) SecurityParams.extract_rf) = true ->
  ExternalMemory.mainmem__ext
           (unsafe_get_ext_call_from_log (log) (_ext ext_mainmem))
           (ExternalMemory.ext_main_mem (machine_mem_st impl_st)) = Success mem_st' ->
  addr_in_config addr new ->
  mem_push_in_config (machine_koika_st impl_st)
            (unsafe_get_ext_call_from_log (log) (_ext ext_mainmem)) ->
  ExternalMemory.ext_mem mem_st' addr = ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st impl_st)) addr.
Proof.
  intros * hst henter hmem haddr hpush.
  unfold ExternalMemory.mainmem__ext in *. simplify. bash_destruct hmem; simplify; auto.
  - consider mem_push_in_config.
    consider get_valid_addr_from_push_req. repeat simpl_match.
    consider ExternalMemory.update_dram. simplify.
    destruct_matches_in_hyp hmem; simplify; simpl; auto.
    destruct_match; simplify; auto.
    bash_destruct hpush.
    + destruct core.
      * rewrite hst in hpush. simpl in hpush. auto.
      * consider mem_addr_in_option_config; consider PfHelpers.mem_addr_in_option_config. simplify.
        exfalso. eapply addr_in_disjoint_config; eauto.
    + destruct core.
      * consider mem_addr_in_option_config. consider PfHelpers.mem_addr_in_option_config; simplify.
        exfalso. eapply addr_in_disjoint_config; eauto.
      * rewrite hst in hpush. simpl in hpush. auto.
Qed.

Lemma machine_caches_spin_up_machine :
  forall cache core cycles dram core' params,
  ExternalMemory.ext_l1_caches (machine_mem_st (spin_up_machine core' cycles params dram )) cache core =
    ExternalMemory.initial_cache_pair.
Proof.
  intros. unfold spin_up_machine; simpl; auto. destruct core'; auto.
Qed.

Lemma enter_enclave_sim:
  forall external_world_state_t impl_st core new input_machine (ext_world: external_world_state_t)
    log mem_st' spec_mem cycles rf,
  ImplInvariant impl_st ->
  machine_st_to_ghost_core (machine_koika_st impl_st) core SecurityParams.extract_rf = GhostCoreState_Waiting new rf ->
  can_enter_enclave new (get_impl_config impl_st.(machine_koika_st) (other_core core) SecurityParams.extract_rf) = true ->
  is_sm_turn core impl_st.(machine_koika_st) = true ->
  impl_step impl_st ext_world input_machine = Success log ->
  impl_st.(machine_koika_st).[_rid (SM SecurityMonitor.clk)] = [Nat.odd cycles] ->
  impl_st.(machine_koika_st).[_rid (Memory Memory.turn)] = spec_cycles_to_bits cycles ->
  (dram_sim_at_config new ((machine_mem_st impl_st).(ExternalMemory.ext_main_mem).(ExternalMemory.ext_mem))
                          (get_enclave_dram EnclaveParams.enclave_sig spec_mem new)) ->
  ImplPost impl_st
            {|
              machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log);
              machine_mem_st := mem_st'
            |} (Log__ext log) ->
  running_sim core {| machine_koika_st := (commit_update (machine_koika_st impl_st) (Log__koika log));
                     machine_mem_st := mem_st'
              |} new
    (spin_up_machine core (cycles + 1)
                     {| machine_pc := _enclave_bootloader_addr EnclaveParams.enclave_sig (config_eid new);
                        machine_config := Some new;
                        machine_rf := rf |}
                     (get_enclave_dram EnclaveParams.enclave_sig spec_mem new) )
    (cycles + 1).
Proof.
  intros * hinv hconfig henter hturn hstep hcycles hmem_turn hsim hpost.
  pose proof (impl_mem_update _ _ _ hpost) as hmem.
  pose proof (impl_w2e _ _ _ hpost) as hw2e. consider impl_enter.
  specialize hw2e with (1 := hconfig) (2 := henter) (3 := hturn). simpl in hw2e.
  constructor; simpl.
  - specialize impl_w2e with (1 := hpost); intros himpl_enter.
    consider impl_enter. eapply himpl_enter with (rf := rf); auto.
  - intros input. specialize PostImplEnter_sim with (1 := hw2e) (input := input) (spec_mem := spec_mem).
    apply SimPre_implies; simpl.
    + reflexivity.
    + simpl.
      specialize impl_increment_mem_cycles with (1 := hpost); intros hmem_cycles; simpl in hmem_cycles.
      specialize impl_increment_sm_cycles with (1 := hpost); intros hsm_cycles; simpl in hsm_cycles.
      setoid_rewrite hcycles in hsm_cycles.
      eapply sim_cycles_plus in hmem_cycles; eauto.
      rewrite plus_one in hsm_cycles; simplify. setoid_rewrite hmem_cycles.
      unfold init_spec_koika_st. unfold spin_up_machine. destruct core; auto.
      { unfold spec_cycles_to_bits. rewrite nat_odd_plus_one.
        cbn - [of_nat Nat.modulo]. f_equal.
        rewrite PostImplEnter_rf with (1 := hw2e). auto.
      }
      { unfold spec_cycles_to_bits. rewrite nat_odd_plus_one.
        cbn - [of_nat Nat.modulo]. f_equal.
        rewrite PostImplEnter_rf with (1 := hw2e). auto.
      }
    + reflexivity.
    + consider spin_up_machine. consider Machine.initial_state. consider initial_machine_state.
      repeat destruct_match; reflexivity.
  - constructor.
    + simpl. unfold spin_up_machine; destruct core; simpl; intros * haddr.
      * rewrite<-hsim by auto.
        pose proof (wf_mem_push  _ _ (impl_wf_log _ _ _ hpost)) as hpush.
        eapply ext_mem_unchanged_at_addr; eauto.
      * rewrite<-hsim by auto.
        consider ExternalMemory.update_memory.
        pose proof (wf_mem_push  _ _ (impl_wf_log _ _ _ hpost)) as hpush.
        eapply ext_mem_unchanged_at_addr; eauto.
    + unfold spin_up_machine. destruct core; simpl ExternalMemory.ext_resp; consider ExternalMemory.update_memory;
        consider ExternalMemory.mainmem__ext;
        bash_destruct hmem; simplify; auto;
        consider ExternalMemory.update_dram.
      * simplify. destruct_matches_in_hyp hmem; simplify; simpl ExternalMemory.ext_resp; auto.
        simpl in hturn. consider is_sm_core0_turn. rewrite hcycles in hturn. simplify. rewrite hturn in *.
        pose proof (wf_mem_push  _ _ (impl_wf_log _ _ _ hpost)) as hpush.
        consider mem_push_in_config. consider get_valid_addr_from_push_req.
        simpl_match.
        simpl_match.
        rewrite Heqr2 in hpush.
        rewrite hconfig in hpush. simpl in hpush.
        bash_destruct hpush; auto.
        consider mem_addr_in_option_config. simplify.
        consider is_mem_core1_push_turn; simplify.
        unfold is_mem_core_read_turn'. intros hturn'; simplify.
        exfalso.
        consider is_mem_core0_push_turn.
        rewrite hmem_turn in *. consider spec_cycles_to_bits. simplify.
        assert (Nat.modulo (Nat.modulo cycles0 4) (pow2 2) = to_nat Ob~1~0) as foo.
        { rewrite PeanoNat.Nat.Div0.mod_mod.
          rewrite<-PeanoNat.Nat.Div0.add_mod_idemp_l in hturn'.
          clear - Heqb0 hturn'. set (pow2 2). vm_compute in n. subst n.
          pose proof (PeanoNat.Nat.mod_upper_bound (cycles0) 4). propositional.
          set (Nat.modulo cycles0 4) in *.
          destruct n; cbn in Heqb0; try discriminate.
          destruct n; cbn in Heqb0; try discriminate.
          destruct n; cbn in Heqb0; try discriminate; auto.
          destruct n; cbn in Heqb0; try discriminate; auto. lia.
        }
        set (pow2 _ ) in *. vm_compute in n. subst n.
        rewrite PeanoNat.Nat.mod_mod in foo by lia.
        rewrite<-PeanoNat.Nat.add_mod_idemp_l in hturn' by lia.
        rewrite foo in *. cbv in hturn'. discriminate.
      * simplify. destruct_matches_in_hyp hmem; simplify; simpl ExternalMemory.ext_resp; auto.
        simpl in hturn. consider is_sm_core1_turn. rewrite hcycles in hturn. simplify. rewrite hturn in *.
        pose proof (wf_mem_push  _ _ (impl_wf_log _ _ _ hpost)) as hpush.
        consider mem_push_in_config. consider get_valid_addr_from_push_req.
        simpl_match.
        simpl_match.
        rewrite Heqr2 in hpush.
        rewrite hconfig in hpush. simpl in hpush.
        bash_destruct hpush; auto.
        consider mem_addr_in_option_config. simplify.
        consider is_mem_core0_push_turn; simplify.
        unfold is_mem_core_read_turn'. intros hturn'; simplify.
        exfalso.
        consider is_mem_core1_push_turn.
        rewrite hmem_turn in *. consider spec_cycles_to_bits.
        assert (Nat.modulo (Nat.modulo cycles0 4) (pow2 2) = to_nat Ob~0~0) as foo.
        { rewrite PeanoNat.Nat.Div0.mod_mod.
          rewrite<-PeanoNat.Nat.Div0.add_mod_idemp_l in hturn'.
          clear - Heqb hturn'. set (pow2 2). vm_compute in n. subst n.
          pose proof (PeanoNat.Nat.mod_upper_bound (cycles0) 4). propositional.
          set (Nat.modulo cycles0 4) in *.
          destruct n; cbn in Heqb; try discriminate.
          destruct n; cbn in Heqb; try discriminate.
          destruct n; cbn in Heqb; try discriminate; auto.
          destruct n; cbn in Heqb; try discriminate; auto. lia.
        }
        set (pow2 _ ) in *. vm_compute in n. subst n.
        rewrite PeanoNat.Nat.mod_mod in foo by lia.
        rewrite<-PeanoNat.Nat.add_mod_idemp_l in hturn' by lia.
        rewrite foo in *. cbv in hturn'. discriminate.
      + intros.
        setoid_rewrite (PostImplEnter_cache _ _ _ _ hw2e cache ).
        rewrite machine_caches_spin_up_machine.
        repeat constructor; auto.
    - unfold strong_WF_state, spin_up_machine; destruct core; split; try reflexivity.
      all: apply PfHelpers.WF_initial_koika_state; auto.
      all: try rewrite length_of_nat; auto.
      all: unfold enclave_config_to_core_init_params; simpl;
          eapply wf_bootloader_addr; apply EnclaveParams.wf_sig.
  Qed.
Lemma spec_sim_exit:
  forall core machine_st config machine_st' new impl_st' impl_st impl_out cycles spec_out ,
  Pf.SimPost core impl_st impl_st' machine_st machine_st' config impl_out spec_out cycles ->
  SpecCorePost core machine_st config machine_st' spec_out ->
  obs_exit_enclave spec_out core = Some new ->
  machine_st_to_ghost_core (machine_koika_st impl_st') core SecurityParams.extract_rf =
    GhostCoreState_Waiting new (SecurityParams.extract_rf machine_st' core).
Proof.
  intros * hsim hspec hexit.
  specialize SpecPost__obs_exit with (1 := hspec).
  consider spec_post_obs_exit. simpl_match. propositional.
  unfold machine_st_to_ghost_core.
  repeat (setoid_rewrite SimPost_implies_reg_sim with (1 := hsim); [ | destruct core; solve_In_to_find]).
  repeat setoid_rewrite H0. rewrite beq_dec_refl. f_equal; auto.
  apply extract_rf_eq. unfold machine_koika_st at 1.
  intros.
  eapply SimPost_implies_core_sim; eauto.
  rewrite in_map_iff. eexists; split; eauto.
  rewrite in_map_iff. eexists; split; eauto.
Qed.

Lemma step_exit_sim :
  forall external_world_state_t impl_st spec_st core config machine_st
    input_machine (ext_world: external_world_state_t)
    log mem_st' local_output machine_st' new ,
    Sim impl_st spec_st ->
    obs_exit_enclave local_output core = Some new ->
    machine_state spec_st core = CoreState_Enclave machine_st config  ->
    spec_step_core core (CoreState_Enclave machine_st config) (i_get_output input_machine ext_world)
                   machine_st = (machine_st', local_output) ->
    impl_step impl_st ext_world input_machine = Success log ->
    ImplPost impl_st
           {|
             machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log);
             machine_mem_st := mem_st'
           |} (Log__ext log) ->
  impl_is_waiting core
    {|
      machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log);
      machine_mem_st := mem_st'
    |} new (SecurityParams.extract_rf machine_st' core) /\
   local_output_sim (get_ext_observations (Log__ext log)) (obs_ext local_output) (Some config) /\
   dram_sim_at_config config (ExternalMemory.ext_mem (ExternalMemory.ext_main_mem mem_st') )
                              (ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st machine_st'))).
   (* (forall addr : N, addr_in_config addr config -> ExternalMemory.ext_mem (ExternalMemory.ext_main_mem mem_st') addr = ExternalMemory.ext_mem (machine_mem_st machine_st') addr). *)
Proof.
  intros * hsim hexit hrunning hspec_step himpl_step himpl_post.
  unfold impl_is_waiting; simpl.
  specialize spec_machine_inv with (1 := Sim_spec_invariant _ _ hsim) (core := core). rewrite hrunning. simpl.
  intros hrunning_inv.
  specialize PfSpecLemmas.spec_step_core_invariant with (1 := hrunning_inv) (2 := hspec_step). intros hspec_post.
  assert(Pf.SimPost core impl_st
           {|
             machine_koika_st := commit_update (machine_koika_st impl_st) (Log__koika log);
             machine_mem_st := mem_st'
           |}
           machine_st machine_st' config log local_output (spec_st.(cycles) + 1)) as HSimPost.
  { eapply step_enclave_sim ; eauto. }
  split_ands_in_goal.
  - eapply spec_sim_exit with (1 := HSimPost); auto.
  - constructor.
    + eapply wf_observations; eapply wf_ext; eauto. eapply impl_wf_log; eauto.
    + eapply SpecPost__wf_ext_obs; eauto.
    + eapply SpecPost__wf_spec_output_config; eauto.
    + split_ands_in_goal.
      * inversion HSimPost; eauto.
      * inversion HSimPost; eauto.
      * inversion HSimPost; eauto.
  - inversion HSimPost. simpl in SimPost__ext_mem0.
    unfold dram_sim_at_config.
    eapply ext_mem_sim__dram; eauto.
Qed.

Lemma can_start_implies_sm_turn:
  forall core koika_st cycles,
 (koika_st).[_rid (SM SecurityMonitor.clk)] = [Nat.odd cycles] ->
  match core with
  | CoreId0 => Nat.even (cycles ) = true
  | CoreId1 => Nat.even (cycles ) = false
  end ->
  is_sm_turn core koika_st = true.
Proof.
  unfold is_sm_turn, is_sm_core0_turn, is_sm_core1_turn.
  intros * Hclk Hcore. rewrite Hclk.
  destruct core; rewrite beq_dec_iff;
    rewrite<-PeanoNat.Nat.negb_odd in Hcore;
    try rewrite negb_true_iff in Hcore;
    try rewrite negb_false_iff in Hcore;
    try rewrite Hcore; auto.
Qed.
Lemma get_enclave_dram_addr_in_region:
  forall region addr config memory,
  addr_in_region EnclaveParams.enclave_sig region addr = true ->
  region_in_config region config = true ->
  memory region addr = get_enclave_dram EnclaveParams.enclave_sig memory config addr.
Proof.
  intros * haddr hregion. unfold get_enclave_dram.
  pose proof (EnclaveParams.pf_disjoint_configs) as pf_disjoint. consider Common.wf_disjoint_configs.
  destruct config; unfold Common.config_eid, Common.config_shared_regions.
  repeat destruct_match;
    repeat match goal with
    | H: addr_in_region _ ?r1 _ = true,
      H1: addr_in_region _ ?r2 _ = true |- _ =>
        assert (r1 = r2) by (apply (pf_disjoint _ _ _ H H1)); try discriminate; subst; clear H
    | H: _ && _ = true |- _ => rewrite andb_true_iff in H; split_ands_in_goal
    | H: MemRegion_Enclave _ = MemRegion_Enclave _ |- _ =>
        inversions H
    | |- _ => progress propositional
    end.
  destruct region; simpl in hregion; simplify; try congruence.
  destruct id; rewrite hregion in *; rewrite andb_true_l in *; try congruence.
Qed.

Lemma enter_mem_sim :
  forall spec_st core new exit_cycle impl_st memory0 addr rf,
  machine_state spec_st core = CoreState_Waiting new exit_cycle rf ->
  mem_map_equivalent (ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st impl_st))) (get_spec_configs spec_st) memory0 ->
  can_enter_enclave new (get_impl_config impl_st.(machine_koika_st) (other_core core) SecurityParams.extract_rf) = true ->
  get_impl_config impl_st.(machine_koika_st) (other_core core) SecurityParams.extract_rf = get_spec_configs spec_st (other_core core)  ->
  addr_in_config addr new ->
  ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st impl_st)) addr = get_enclave_dram EnclaveParams.enclave_sig memory0 new addr.
Proof.
  intros * hwait hmem henter hsim haddr.
  consider mem_map_equivalent. consider can_enter_enclave.
  unfold addr_in_config in *. propositional. specialize hmem with (1 := haddr1).
  rewrite negb_true_iff in henter. consider @configs_conflict.
  assert_pre_and_specialize hmem.
  { intros core0; destruct_with_eqn (beq_dec core core0); simplify; try simpl_match; auto.
    - unfold get_spec_configs, get_core_config; try simpl_match; auto.
    - destruct core; destruct core0; try discriminate; simpl in hsim; try rewrite<-hsim;
        unfold get_spec_configs, get_core_config; try simpl_match; auto.
      + simpl in henter. bash_destruct henter; repeat rewrite orb_false_iff in henter; simpl; propositional; simplify.
        consider region_in_config. destruct region; simplify; auto.
        { destruct new; destruct e; simpl in *; destruct config_eid; destruct config_eid0; simpl in *; auto. }
        { consider shared_regions_conflict; destruct id; rewrite haddr2 in *; simpl in *;
            repeat rewrite orb_false_iff in *; propositional.
        }
      + simpl in henter. bash_destruct henter; repeat rewrite orb_false_iff in henter; simpl; propositional; simplify.
        consider region_in_config. destruct region; simplify; auto.
        { destruct new; destruct e; simpl in *; destruct config_eid; destruct config_eid0; simpl in *; auto. }
        { consider shared_regions_conflict; destruct id; rewrite haddr2 in *; simpl in *;
            repeat rewrite orb_false_iff in *; propositional.
        }
  }
  rewrite hmem.
  eapply get_enclave_dram_addr_in_region; eauto.
Qed.
Lemma wf_external_obs_empty:
  wf_external_observations empty_external_obs.
Proof.
  constructor; auto.
Qed.
Lemma wf_spec_output_config_empty:
  wf_spec_output_config empty_external_obs None.
Proof.
  unfold wf_spec_output_config. reflexivity.
Qed.

Lemma sim_local_step:
  forall {external_world_state_t: Type} core impl_st spec_st input_machine (ext_st: external_world_state_t) impl_st' input_machine' external_observations' output spec_st' memory0 memory1,
  Sim impl_st spec_st ->
  ImplInvariant impl_st' ->
  SpecInvariant spec_st' ->
  Impl.step input_machine impl_st ext_st = Success(impl_st', input_machine', external_observations') ->
  mem_map_equivalent impl_st.(machine_mem_st).(ExternalMemory.ext_main_mem).(ExternalMemory.ext_mem)
                     (get_spec_configs spec_st)
                     memory0 ->
  case_core_state core (spec_step_core core (machine_state spec_st core) (i_get_output input_machine ext_st))
                       (machine_state spec_st core) (machine_state spec_st' core) output (cycles spec_st)
                       memory0 memory1 (get_spec_configs spec_st (other_core core)) ->
  machine_sim core impl_st' (machine_state spec_st' core) (cycles spec_st + 1) /\
  local_output_sim external_observations' output (get_core_config (machine_state spec_st core)) /\
  step_memory_update_sim core (machine_state spec_st core) (machine_mem_st impl_st').(ExternalMemory.ext_main_mem)
                         input_machine ext_st.
Proof.
   unfold Impl.step, Machine.step, StateMachine.step.
  unfold Machine.machine_step_external, Machine.koika_step, Machine.koika_step', interp_cycle'.
  intros * Hsim Himpl_inv Hspec_inv Himpl_step Hmem Hcase. simplify.
  rename s0 into mem'. rename s into log.
  specialize PfImplLemmas.impl_step_preserves_impl_inv' with (1 := Sim_impl_invariant _ _ Hsim) (input := i_get_output input_machine ext_st).
  propositional. setoid_rewrite H0 in Heqr0. simplify.
  rename H0 into Himpl_step. rename H2 into Hpost. simpl.
  pose proof (impl_mem_update  _ _ _ Hpost) as Hupdate.
  specialize impl_cache_update with (1 := Hpost) as Hcache_update. simpl in *.

  (* apply impl_interp_modular_schedule in Himpl_step. simpl. *)
  unfold case_core_state in *. unfold get_core_config.
  unfold get_observations in *. simpl in *. consider ExternalMemory.update_memory. simplify. simpl in *.
  setoid_rewrite Heqr0 in Hupdate. simplify.
  specialize Sim_spec_invariant with (1 := Hsim); intros hspec_inv.
  specialize spec_machine_inv with (1 := hspec_inv); intros hspec_machine_inv.
  rename Heqr0 into Hmain_mem.
  rename Heqr2 into Hicache0. rename Heqr3 into Hdcache0.
  rename Heqr4 into Hicache1. rename Heqr5 into Hdcache1.
  setoid_rewrite (Hcache_update imem CoreId0) in Hicache0.
  setoid_rewrite (Hcache_update imem CoreId1) in Hicache1.
  setoid_rewrite (Hcache_update dmem CoreId0) in Hdcache0.
  setoid_rewrite (Hcache_update dmem CoreId1) in Hdcache1. simplify.
  set (ExternalMemory.Build_external_mem_t _ _ ) as mem_st'' in *.
  assert (mem_st'' = mem_st') as hmem_eq.
  { unfold mem_st''. destruct mem_st'; f_equal.
    apply functional_extensionality; intros.
    apply functional_extensionality; intros.
    destruct x; destruct x0; reflexivity.
  }
  unfold mem_st'' in *. rewrite hmem_eq in *.
  destruct_matches_in_hyp Hcase.
  - simpl. destruct_matches_in_hyp Hcase; propositional;
      set (spec_step_core _ _ _ _) as spec_step in *; destruct_with_eqn spec_step; propositional;
    simpl; unfold spec_step in *.
    + split_ands_in_goal; try eapply step_running_sim; eauto.
      unfold dram_sim_at_config.
      eapply step_running_sim; eauto.
    + eapply step_exit_sim; eauto.
  - simpl.
    assert (output = empty_external_obs) by (bash_destruct Hcase; propositional); subst.
    split_ands_in_goal; auto.
    + pose proof (Sim_machine_state _ _ Hsim core) as hsim_core. unfold machine_sim, impl_is_waiting in hsim_core. simpl_match.
      destruct_matches_in_hyp Hcase; propositional; simpl.
      * (* Waiting -> Enclave; need unused regions to be related at the start of the cycle. *)
        erewrite Sim_impl_configs_eq in Hcase2 by eauto.
        eapply @enter_enclave_sim with (5 := Himpl_step); eauto with solve_invariants.
        { eapply can_start_implies_sm_turn; eauto with solve_invariants.  }
        { eapply Sim_cycles_mem; eauto. }
        { intros * haddr; eapply enter_mem_sim; eauto.
          pose proof (Sim_machine_state _ _ Hsim (other_core core)) as hsim_core'.
          unfold machine_sim, impl_is_waiting in hsim_core'; unfold get_impl_config, get_ghost_running_config.
          bash_destruct hsim_core'; auto.
          - destruct hsim_core'. simpl_match. unfold get_spec_configs. rewrite Heqc1. auto.
          - rewrite hsim_core'. unfold get_spec_configs. rewrite Heqc1. auto.
        }
      * unfold impl_is_waiting.
        eapply (impl_w2w _ _ _ Hpost); eauto.
        erewrite<-Sim_impl_configs_eq; eauto.
        split_ors_in Hcase0; subst; auto.
        { right. unfold is_sm_turn, is_sm_core0_turn, is_sm_core1_turn.
          erewrite Sim_cycles_sm by eauto.
          destruct core; rewrite beq_dec_false_iff; unfold not; intros clk; inversions clk;
            rewrite<-PeanoNat.Nat.negb_even in *.
          - rewrite Hcase0 in *. discriminate.
          - rewrite Hcase0 in *. discriminate.
        }
    + constructor; eauto with solve_invariants.
      eapply wf_observations. eapply wf_ext. eapply impl_wf_log. eauto.
      * apply wf_external_obs_empty.
      * apply wf_spec_output_config_empty.
Qed.
Lemma update_regions_not_in_config:
  forall config dram mem0 region,
  region_in_config region config = false ->
  update_regions EnclaveParams.enclave_sig config dram mem0 region = mem0 region.
Proof.
  intros * hregion.
  unfold update_regions. consider region_in_config.
  bash_destruct hregion; simplify; destruct_match; auto.
  - apply internal_enclave_id_dec_bl in Heqb.
    contradiction.
  - discriminate.
Qed.

Lemma mem_map_equivalent_update_config:
  forall impl_st spec_st config dram memory0 core machine_state0,
  mem_map_equivalent (ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st impl_st))) (get_spec_configs spec_st) memory0 ->
  machine_state spec_st core = CoreState_Enclave machine_state0 config ->
  mem_map_equivalent (ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st impl_st))) (get_spec_configs spec_st)
    (update_regions EnclaveParams.enclave_sig config dram memory0).
Proof.
  consider mem_map_equivalent.
  intros * hmem hmachine. intros * haddr hregion.
  specialize hmem with (1 := haddr) (2 := hregion).
  pose proof (hregion core) as hcore. unfold region_in_option_config in hcore.
  unfold get_spec_configs in *. rewrite hmachine in hcore. simpl in hcore.
  rewrite update_regions_not_in_config by auto. assumption.
Qed.

Lemma intermediate_mem_map_equivalent:
  forall impl_st spec_st input core output0 memory0 memory1 st',
  Sim impl_st spec_st ->
  mem_map_equivalent (ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st impl_st))) (get_spec_configs spec_st) memory0 ->
  case_core_state core
            (spec_step_core core (machine_state spec_st core) input)
            (machine_state spec_st core) st' output0 (cycles spec_st)
            memory0 memory1 (get_spec_configs spec_st (other_core core)) ->
  mem_map_equivalent (ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st impl_st))) (get_spec_configs spec_st) memory1.
Proof.
  intros * hsim hmem hcase.
  consider case_core_state.
  repeat destruct_matches_in_hyp hcase; propositional.
  eapply mem_map_equivalent_update_config; eauto.
Qed.
Record output_sim_zeroes impl_out (spec_config0 spec_config1: option enclave_config) : Prop :=
  { sim_uart_zero: (owns_uart spec_config0 || owns_uart spec_config1) = false ->
                   obs_uart_write impl_out = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_uart_write))
                /\ obs_uart_read impl_out = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_uart_read));
    sim_led_zero: (owns_led spec_config0 || owns_led spec_config1) = false ->
                   obs_led impl_out = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_led));
    sim_finish_zero: (owns_finish spec_config0 || owns_finish spec_config1) = false ->
                   obs_finish impl_out = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_finish));
  }.

Lemma sim_step_output:
  forall {external_world_state_t: Type} impl_st spec_st input_machine (ext_st: external_world_state_t) impl_st' input_machine' external_observations' output0 output1 spec_st' memory1 ,
  Sim impl_st spec_st ->
  Impl.step input_machine impl_st ext_st = Success(impl_st', input_machine', external_observations') ->
  case_core_state CoreId0 (spec_step_core CoreId0 (machine_state spec_st CoreId0) (i_get_output input_machine ext_st)) (machine_state spec_st CoreId0) (machine_state spec_st' CoreId0) output0 (cycles spec_st) (mem_regions spec_st) memory1 (get_spec_configs spec_st CoreId1) ->
  case_core_state CoreId1 (spec_step_core CoreId1 (machine_state spec_st CoreId1) (i_get_output input_machine ext_st)) (machine_state spec_st CoreId1) (machine_state spec_st' CoreId1) output1 (cycles spec_st) memory1 (mem_regions spec_st') (get_spec_configs spec_st CoreId0) ->
  output_sim_zeroes external_observations' (get_spec_configs spec_st CoreId0) (get_spec_configs spec_st CoreId1).
Proof.
  intros * Hsim Hstep Hcase0 Hcase1.
  consider case_core_state. unfold get_spec_configs, get_core_config.
  pose proof (Sim_machine_state _ _ Hsim CoreId0) as machine_sim0.
  pose proof (Sim_machine_state _ _ Hsim CoreId1) as machine_sim1.
  unfold machine_sim, impl_is_waiting in *.
  specialize impl_step_preserves_impl_inv with (1 := Sim_impl_invariant _ _ Hsim).
  intros Himpl_step. specialize (Himpl_step _ input_machine ext_st). propositional. rewrite Hstep in Himpl_step1. simplify.
  destruct Himpl_step2. consider get_impl_config. consider get_ghost_running_config.
  destruct_matches_in_hyp Hcase0.
  - destruct machine_sim0.
    destruct_matches_in_hyp Hcase1; simpl.
    + destruct machine_sim1; repeat simpl_match.
      constructor; auto.
    + repeat simpl_match. constructor; auto.
  - destruct_matches_in_hyp Hcase1; simpl.
    + destruct machine_sim1. repeat simpl_match.
      constructor; auto.
    + repeat simpl_match. constructor; auto.
Qed.

Lemma proof_output_sim:
  forall spec_st ext_obs' output0 output1,
  SpecInvariant spec_st ->
  local_output_sim ext_obs' output0 (get_core_config (machine_state spec_st CoreId0))->
  local_output_sim ext_obs' output1 (get_core_config (machine_state spec_st CoreId1))->
  output_sim_zeroes ext_obs' (get_spec_configs spec_st CoreId0)
                     (get_spec_configs spec_st CoreId1)->
  ext_obs' = merge_external_observations output0 output1.
Proof. (* DONE *)
  intros * spec_invariant sim0 sim1 output_sim.
  destruct output_sim.
  unfold merge_external_observations. unfold merge_ext.
  destruct ext_obs'; simpl in *.
  destruct sim0. destruct sim1; simpl in *.
  consider @get_spec_configs.
  consider @get_core_config.
  assert (disjoint_option_configs' spec_st) as Hdisjoint.
  { auto with solve_invariants. }
  consider disjoint_option_configs'.
bash_destruct local_output_sim_sim0; bash_destruct local_output_sim_sim1; simpl in *; try rewrite orb_false_r in *.
  - destruct Hdisjoint.
    f_equal.
    + destruct_with_eqn (config_ext_uart config);
      destruct_with_eqn (config_ext_uart config0);
        propositional;
        try rewrite wf_uart_write by auto;
        destruct_match; simplify; auto.
      rewrite_solve.
    + destruct_with_eqn (config_ext_uart config);
      destruct_with_eqn (config_ext_uart config0);
        propositional;
        try rewrite wf_uart_read by auto;
        destruct_match; simplify; auto.
      rewrite_solve.
    + destruct_with_eqn (config_ext_led config);
      destruct_with_eqn (config_ext_led config0);
        propositional; try rewrite wf_led by auto; destruct_match; simplify; auto.
      rewrite_solve.
    + destruct_with_eqn (config_ext_finish config);
      destruct_with_eqn (config_ext_finish config0);
        propositional; try rewrite wf_finish by auto; destruct_match; simplify; auto.
      rewrite_solve.
  - f_equal.
    + destruct_with_eqn (config_ext_uart config); propositional;
        try rewrite wf_uart_write by auto;
        destruct_match; simplify; auto.
    + destruct_with_eqn (config_ext_uart config); propositional;
        try rewrite wf_uart_read by auto;
        destruct_match; simplify; auto.
    + destruct_with_eqn (config_ext_led config); propositional;
        try rewrite wf_led by auto;
        destruct_match; simplify; auto.
    + destruct_with_eqn (config_ext_finish config); propositional;
        try rewrite wf_finish by auto;
        destruct_match; simplify; auto.
  - f_equal.
    + destruct_with_eqn (config_ext_uart config); propositional;
        try rewrite wf_uart_write by auto;
        destruct_match; simplify; auto.
    + destruct_with_eqn (config_ext_uart config); propositional;
        try rewrite wf_uart_read by auto;
        destruct_match; simplify; auto.
    + destruct_with_eqn (config_ext_led config); propositional;
        try rewrite wf_led by auto;
        destruct_match; simplify; auto.
    + destruct_with_eqn (config_ext_finish config); propositional;
        try rewrite wf_finish by auto;
        destruct_match; simplify; auto.
  - propositional.
Qed. (* DONE *)
Lemma disjoint_configs_impl_regions_disjoint:
  forall region config0 config1,
  disjoint_configs config0 config1 ->
  region_in_config region config0 = true->
  region_in_config region config1 = true->
  False.
Proof.
  intros * hdisjoint hregion0 hregion1.
  destruct hdisjoint.
  consider region_in_config.
  destruct region; try discriminate; simplify.
  - congruence.
  - specialize disjoint_shared_regions with (region := id); propositional.
Qed.
Lemma disjoint_option_configs_impl_regions_disjoint:
  forall st region,
  disjoint_option_configs' st ->
  region_in_option_config region (get_spec_configs st CoreId0) = true ->
  region_in_option_config region (get_spec_configs st CoreId1) = true ->
  False.
Proof.
  unfold disjoint_option_configs'.
  unfold region_in_option_config.
  consider get_spec_configs. intros hdisjoint hregion0 hregion1.
  bash_destruct  hregion1; auto.
  intros; destruct_all_matches; try discriminate.
  eapply  disjoint_configs_impl_regions_disjoint; eauto.
Qed.
Lemma region_was_in_option_config:
  forall region st st' core output cycles mem0 mem1 step other_config,
  region_in_option_config region (get_spec_configs st core) = true ->
  region_in_option_config region (get_spec_configs st' core) = false ->
  case_core_state core step (machine_state st core) (machine_state st' core)
                  output cycles mem0 mem1 other_config ->
  exists config config' cycles' koika_st rf,
  machine_state st core = CoreState_Enclave koika_st config /\
  machine_state st' core = CoreState_Waiting config' rf cycles' .
Proof.
  intros * hregion hregion' hcase.
  consider region_in_option_config.
  consider get_spec_configs. consider case_core_state.
  bash_destruct hcase; simpl in *; propositional; eauto; try congruence.
  repeat eexists; eauto.
Qed.
Lemma region_not_in_option_config:
  forall region st st' core output cycles mem0 mem1 step other_config,
  region_in_option_config region (get_spec_configs st core) = false ->
  region_in_option_config region (get_spec_configs st' core) = false ->
  case_core_state core step (machine_state st core) (machine_state st' core)
                  output cycles mem0 mem1 other_config ->
  mem1 region = mem0 region.
Proof.
  intros * hregion hregion' hcase.
  consider region_in_option_config.
  consider get_spec_configs. consider case_core_state.
  bash_destruct  hcase; simpl in *; propositional.
  rewrite update_regions_not_in_config; auto.
Qed.
Lemma update_regions_in_config:
  forall config dram mem0 region addr,
  region_in_config region config = true ->
  addr_in_region EnclaveParams.enclave_sig region addr = true ->
  update_regions EnclaveParams.enclave_sig config dram mem0 region addr = dram addr.
Proof.
  unfold update_regions.
  intros * hregion haddr.
  consider region_in_config.
  bash_destruct hregion; simplify.
  - rewrite internal_enclave_id_dec_lb by auto.
    consider filter_dram. simpl_match. auto.
  - simpl_match.
    consider filter_dram. simpl_match. auto.
Qed.
     Definition get_mem_req_addr (req: vect_t) : vect_t :=
         match _get_field (mem_input) "put_request" req with
         | Success req =>
             match _get_field (mem_req) "addr" req with
             | Success v => v
             | _ => Ob
             end
         | _ => Ob
         end.

     Definition valid_local_obs_push_request (impl_st: impl_state_t) (resp: vect_t)
                                             (core0 core1: bool) : bool :=
        match _get_field (mem_input) "put_valid" resp with
       | Success Ob~1 =>
           (is_mem_core0_push_turn (machine_koika_st impl_st ) && core0 &&
            match machine_st_to_ghost_core (machine_koika_st impl_st) CoreId0 SecurityParams.extract_rf with
            | GhostCoreState_Waiting _ _ => false
            | GhostCoreState_Enclave config =>
                addr_in_config_dec EnclaveParams.enclave_sig (to_N (get_mem_req_addr resp)) config
            end) ||
           (is_mem_core1_push_turn (machine_koika_st impl_st)&& core1 &&
            match machine_st_to_ghost_core (machine_koika_st impl_st) CoreId1 SecurityParams.extract_rf with
            | GhostCoreState_Waiting _  _ => false
            | GhostCoreState_Enclave config =>
                addr_in_config_dec EnclaveParams.enclave_sig (to_N (get_mem_req_addr resp)) config
            end)
       | Success Ob~0 => true
       | _ => false
       end.

     Lemma impl_step_memory_obs:
       forall impl_st koika_st' output local_obs,
       ImplInvariant impl_st ->
       Machine.koika_step Impl.schedule
                (mk_sigma_fn (machine_mem_st impl_st) output)
                (machine_koika_st impl_st) = Success (koika_st', local_obs) ->
       valid_local_obs_push_request impl_st (obs_mainmem (obs_mem local_obs)) true true = true.
     Proof.
       intros * hinv. specialize PfImplLemmas.impl_step_preserves_impl_inv' with (1 := hinv).
       consider Machine.koika_step. unfold Machine.koika_step', interp_cycle'.
       propositional. specialize H with (input := output). propositional. setoid_rewrite H1 in H0. simplify.
       simpl. unfold valid_local_obs_push_request. pose proof (impl_wf_log _ _ _ H3). destruct H. consider mem_push_in_config.
       consider get_valid_addr_from_push_req.
       specialize PfImplLemmas.impl_interp_cycle_correct' with (1 := hinv) (input := output). setoid_rewrite H1.
       intros (hwf' & hwf_log).
       unsafe_simplify_structs_as Hwf_push.
       assert_pre_and_specialize Hwf_push.
       { unfold _unsafe_get_ext_call_from_log.
         eapply WF_ext_log_call_length; eauto.
       }
       simplify.
       destruct s; [discriminate | ].
       destruct s; [ | discriminate ].
       destruct b; auto.
       unfold get_ghost_running_config in wf_mem_push0.
       destruct_matches_in_hyp wf_mem_push0; simpl.
       - revert wf_mem_push0.
         setoid_rewrite Heqr0.
         unsafe_simplify_structs_as hwf_put.
         assert_pre_and_specialize hwf_put.
         { eapply WF_ext_log_call_length; eauto. }
         simplify.
         unsafe_simplify_structs_as hwf_addr.
         assert_pre_and_specialize hwf_addr; auto. simplify.
         intros wf_mem_push0.
         destruct_match; simpl in wf_mem_push0; [ | contradiction].
         unfold get_mem_req_addr. repeat simpl_match. rewrite orb_true_iff.
         rewrite (@addr_in_config_iff EnclaveParams.enclave_sig) by assumption.
         setoid_rewrite Heqr1. setoid_rewrite Heqr2. auto.
       - destruct_matches_in_hyp wf_mem_push0; simpl.
         revert wf_mem_push0. setoid_rewrite Heqr0.
         unsafe_simplify_structs_as hwf_put.
         assert_pre_and_specialize hwf_put.
         { eapply WF_ext_log_call_length; eauto. }
         simplify.
         unsafe_simplify_structs_as hwf_addr. assert_pre_and_specialize hwf_addr; auto. simplify.
         intros wf_mem_push0.
         destruct_match; simpl in wf_mem_push0; [ | contradiction].
         unfold get_mem_req_addr. repeat simpl_match.
         setoid_rewrite Heqr1. setoid_rewrite Heqr2.
         rewrite (@addr_in_config_iff EnclaveParams.enclave_sig) by assumption. auto.
         setoid_rewrite Heqr0 in wf_mem_push0. discriminate.
     Qed.

Lemma sim_addr_not_in_config:
  forall {external_world_state_t : Type} impl_st spec_st region addr
    (ext_st: external_world_state_t) input_machine input_machine' impl_st' external_observations',
  Sim impl_st spec_st ->
  Impl.step input_machine impl_st ext_st =
    Success (impl_st', input_machine', external_observations') ->
  addr_in_region EnclaveParams.enclave_sig region addr = true ->
  region_in_option_config region (get_spec_configs spec_st CoreId0) = false ->
  region_in_option_config region (get_spec_configs spec_st CoreId1) = false ->
  ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st impl_st')) addr = ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st impl_st)) addr.
Proof.
  consider @Impl.step.
  consider Machine.step.
  consider @StateMachine.step.
  consider Machine.machine_step_external.
  intros * hsim himpl haddr hregion0 hregion1. simplify; simpl.
  specialize impl_step_memory_obs with (1 := Sim_impl_invariant _ _ hsim ) (2 := Heqr0).
  consider ExternalMemory.update_memory.
  consider ExternalMemory.mainmem__ext. simplify; simpl; [ | propositional].
  consider get_spec_configs.
  consider ExternalMemory.update_dram. simplify.
  bash_destruct Heqr4; simplify; simpl; auto.
  pose proof (Sim_machine_state _ _ hsim CoreId0) as machine_sim0.
  pose proof (Sim_machine_state _ _ hsim CoreId1) as machine_sim1.
  intros hwf_mem.
  (* destruct_match; simplify; auto. *)
  consider valid_local_obs_push_request. simpl_match.
  rewrite orb_true_iff in hwf_mem. repeat rewrite andb_true_iff in hwf_mem.
  (* bash_destruct Heqr1; simplify; simpl; auto. *)
  destruct_match; simplify; auto.
  destruct hwf_mem as [hwf_mem | hwf_mem]; propositional; simplify; bash_destruct hwf_mem1;
  consider get_mem_req_addr; simpl_match.
  + setoid_rewrite Heqr1 in hwf_mem1.
    rewrite (addr_in_config_iff EnclaveParams.enclave_sig) in hwf_mem1.
    unfold addr_in_config in *. propositional.
    pose proof EnclaveParams.pf_disjoint_configs as Hdisjoint. consider Common.wf_disjoint_configs.
    specialize Hdisjoint with (1 := hwf_mem1) (2 := haddr). subst.
    unfold machine_sim, impl_is_waiting in machine_sim0. bash_destruct machine_sim0.
    destruct machine_sim0. rewrite running_sim__ghost0 in *. inversions Heqg. simpl in hregion0. congruence.
  + setoid_rewrite Heqr1 in hwf_mem1.
    rewrite (addr_in_config_iff EnclaveParams.enclave_sig) in hwf_mem1.
    unfold addr_in_config in *. propositional.
    pose proof EnclaveParams.pf_disjoint_configs as Hdisjoint. consider Common.wf_disjoint_configs.
    specialize Hdisjoint with (1 := hwf_mem1) (2 := haddr). subst.
    unfold machine_sim, impl_is_waiting in machine_sim1. bash_destruct machine_sim1.
    destruct machine_sim1. rewrite running_sim__ghost0 in *. inversions Heqg. simpl in hregion1. congruence.
Qed.

    Lemma sim_step_memory:
      forall {external_world_state_t: Type} impl_st spec_st input_machine (ext_st: external_world_state_t) impl_st' input_machine' external_observations' output0 output1 spec_st' memory1 ,
      Sim impl_st spec_st ->
      ImplInvariant impl_st' ->
      SpecInvariant spec_st' ->
      Impl.step input_machine impl_st ext_st = Success(impl_st', input_machine', external_observations') ->
      case_core_state CoreId0 (spec_step_core CoreId0 (machine_state spec_st CoreId0) (i_get_output input_machine ext_st)) (machine_state spec_st CoreId0) (machine_state spec_st' CoreId0) output0 (cycles spec_st) (mem_regions spec_st) memory1 (get_spec_configs spec_st CoreId1)->
      case_core_state CoreId1 (spec_step_core CoreId1 (machine_state spec_st CoreId1) (i_get_output input_machine ext_st)) (machine_state spec_st CoreId1) (machine_state spec_st' CoreId1) output1 (cycles spec_st) memory1 (mem_regions spec_st') (get_spec_configs spec_st CoreId0)->
      mem_map_equivalent (ExternalMemory.ext_mem (ExternalMemory.ext_main_mem (machine_mem_st impl_st'))) (get_spec_configs spec_st')
        (mem_regions spec_st').
    Proof.
      intros * hsim himpl_inv hspec_inv impl_step case0 case1.
      specialize @sim_local_step with (1 := hsim) (2 := himpl_inv) (3 := hspec_inv)
                                      (4:=impl_step) (5 := Sim_memory_regions _ _ hsim) (6:=case0).
      intros (sim0 & sim_output0 & sim_mem0).
      specialize intermediate_mem_map_equivalent with (1 := hsim) (2 := Sim_memory_regions _ _ hsim)
                                                      (3 := case0); intros hinter_mem.
      specialize @sim_local_step with (1 := hsim) (2 := himpl_inv) (3 := hspec_inv)
                                      (4:=impl_step) (5 := hinter_mem) (6 := case1).
      intros (sim1 & sim_output1 & sim_mem1).
      consider @mem_map_equivalent.
      intros * hregion hdormant.
      pose proof (hdormant CoreId0) as hdormant0.
      pose proof (hdormant CoreId1) as hdormant1.
      clear hdormant.
      destruct (region_in_option_config region (get_spec_configs spec_st CoreId0)) eqn:region0;
      destruct (region_in_option_config region (get_spec_configs spec_st CoreId1)) eqn:region1.
      - exfalso.
        apply disjoint_option_configs_impl_regions_disjoint with
          (2 := region0) (3 := region1).
        eauto with solve_invariants.
      -
        specialize region_was_in_option_config with (1 := region0) (2 := hdormant0) (3 := case0).
        intros (config & config' & cycles' & rf & koika_st & hst1 & hst2).
        rewrite hst1 in *. rewrite hst2 in *. revert case0. unfold case_core_state. intros case0.
        simplify. propositional.
        rewrite region_not_in_option_config with (1 := region1) (2 := hdormant1) (3 := case1).
        assert (region_in_config region config = true) as hregion_in_config.
        { revert region0. unfold region_in_option_config, get_spec_configs. intros region0.
          rewrite hst1 in *. simpl in region0. assumption.
        }
        rewrite update_regions_in_config by assumption.
        safe_unfold @step_memory_update_sim sim_mem0.
        unfold output_t in *.
        rewrite Heqp in sim_mem0.
        apply sim_mem0.
        eapply addr_in_region_implies_in_config; eauto.
      - specialize region_was_in_option_config with (1 := region1) (2 := hdormant1) (3 := case1).
        intros (config & config' & cycles' & rf & koika_st & hst1 & hst2).
        rewrite hst1 in *. rewrite hst2 in *. safe_unfold @case_core_state case1.
        simplify. propositional.
        rewrite case4.
        assert (region_in_config region config = true) as hregion_in_config.
        { revert region1. unfold region_in_option_config, get_spec_configs. intros region1.
          rewrite hst1 in *. simpl in region1. assumption.
        }
        rewrite update_regions_in_config by assumption.
        safe_unfold @step_memory_update_sim sim_mem1.
        unfold output_t in *.
        rewrite Heqp in sim_mem1.
        apply sim_mem1.
        eapply addr_in_region_implies_in_config; eauto.
      - rewrite region_not_in_option_config with (1 := region1) (2 := hdormant1) (3 := case1) in *.
        rewrite region_not_in_option_config with (1 := region0) (2 := hdormant0) (3 := case0) in *.
        erewrite @sim_addr_not_in_config; eauto.
        eapply Sim_memory_regions; auto.
        destruct core; auto.
    Qed.
Lemma impl_step_increment_mem_cycles:
  forall {external_world_state_t} (ext_st: external_world_state_t) impl_st impl_st' input_machine input_machine' ext_obs',
  ImplInvariant impl_st->
  Impl.step input_machine impl_st ext_st =
               Success (impl_st', input_machine', ext_obs')->
  Bits.plus ((machine_koika_st impl_st).[_rid (Memory Memory.turn)]) (Bits.of_nat 2 1) =
            Success (machine_koika_st impl_st').[_rid (Memory Memory.turn)].
Proof.
  intros * Hinv.
  consider @Impl.step; consider @Machine.step. consider @StateMachine.step.
  unfold Machine.machine_step_external, Machine.koika_step, Machine.koika_step', interp_cycle'.
  intros; simplify.
  apply PfImplLemmas.impl_step_preserves_impl_inv' with (input := (i_get_output input_machine ext_st)) in Hinv.
  propositional. simplify. setoid_rewrite Hinv0 in Heqr0. simplify. simpl. inversions Hinv2.
  propositional.
Qed.
Lemma impl_step_increment_sm_cycles:
  forall {external_world_state_t} (ext_st: external_world_state_t) impl_st impl_st' input_machine input_machine' ext_obs',
  ImplInvariant impl_st->
  Impl.step input_machine impl_st ext_st =
               Success (impl_st', input_machine', ext_obs')->
  Bits.plus ((machine_koika_st impl_st).[_rid (SM SecurityMonitor.clk)]) (Bits.of_nat 1 1) =
            Success (machine_koika_st impl_st').[_rid (SM SecurityMonitor.clk)].
Proof.
  intros * Hinv.
  consider @Impl.step; consider @Machine.step. consider @StateMachine.step.
  unfold Machine.machine_step_external, Machine.koika_step, Machine.koika_step', interp_cycle'.
  intros; simplify.
  apply PfImplLemmas.impl_step_preserves_impl_inv' with (input := (i_get_output input_machine ext_st)) in Hinv.
  propositional. simplify. setoid_rewrite Hinv0 in Heqr0. simplify. simpl. inversions Hinv2. propositional.
Qed.
Lemma nat_odd_plus_even:
  forall n m,
  Nat.odd m = true ->
  Nat.odd (n + m) = Nat.even n.
Proof.
  intros. destruct m.
  - discriminate.
  - rewrite PeanoNat.Nat.odd_succ in H.
    rewrite<-PeanoNat.Nat.add_succ_comm.
    rewrite PeanoNat.Nat.odd_add_even; auto.
    + rewrite PeanoNat.Nat.odd_succ. auto.
    + rewrite<-PeanoNat.Nat.even_spec. auto.
Qed.

  Theorem step_sim:
      forall (impl_st: impl_state_t) (spec_st spec_st': spec_state_t)
        (external_world_state_t: Type)
        (input_machine: @i_machine_t external_world_state_t output_t input_t)
        (ext_st ext_st'__spec: external_world_state_t)
        (output__spec: output_t),
      Sim impl_st spec_st ->
      Spec.step
          SecurityParams.local_step_fn0
        SecurityParams.local_step_fn1
        SpecParams.can_start_fn
        SecurityParams.spin_up_machine
        SecurityParams.extract_dram
        SecurityParams.extract_rf
        input_machine spec_st ext_st = (spec_st', ext_st'__spec, output__spec) ->
    match Impl.step input_machine impl_st ext_st with
    | Success (impl_st', ext_st'__impl, output__impl) =>
      Sim impl_st' spec_st' /\ ext_st'__impl = ext_st'__spec /\ output__impl = output__spec
    | Failure _ => False
    end.
  Proof.
      intros * HSim Hspec_step.
      specialize PfSpecLemmas.spec_step_preserves_spec_inv with (1:= Sim_spec_invariant _ _ HSim) (2:= Hspec_step);intros Hspec_inv'.
      pose proof (Sim_impl_invariant _ _ HSim) as HImplInv.
      pose proof (impl_step_preserves_impl_inv impl_st _ input_machine ext_st HImplInv) as (impl_st' & ext_st' & ext_obs' & HImpl_step & HImplInv' & step_WF_ext_obs & Hext').
      subst.
      simpl_match.
      unfold Spec.step, safe_step in *. simplify.
      specialize PfSpecLemmas.spec_step_case_core_state with (2:=Heqp); intros (output0 & output1 & memory1 & hcase0 &hcase1&hcase2);propositional; eauto with solve_invariants.
      rename Heqp into hspec_step.
      specialize spec_step_increment_cycles with (1:= hspec_step); intros cycles'.

      specialize @sim_local_step with (1:= HSim) (2:= HImplInv') (3:=Hspec_inv') (4:=HImpl_step) (5 := Sim_memory_regions _ _ HSim ) (6:= hcase0); intros (hsim0' & houtput0 & hmem0).
      specialize @sim_local_step with (1:= HSim) (2:= HImplInv') (3:=Hspec_inv') (4:=HImpl_step) (6:= hcase1); intros (hsim1' & houtput & hmem11).
      { eapply intermediate_mem_map_equivalent with (2 := Sim_memory_regions _ _ HSim) (3 := hcase0); auto. }
      setoid_rewrite<-cycles' in hsim0'.
      setoid_rewrite<-cycles' in hsim1'.
      specialize @sim_step_output with (1:=HSim) (2:= HImpl_step) (3:=hcase0) (4:=hcase1); intros houtput_zeroes.
      assert (ext_obs' = merge_external_observations output0 output1) as hobservations.
      { eapply proof_output_sim with (spec_st:=spec_st); eauto with solve_invariants. }
      subst.
      split_ands_in_goal; auto.
      constructor; auto.
      + destruct core_id; auto.
      + eapply sim_step_memory; eauto.
      + apply spec_step_increment_cycles in hspec_step. setoid_rewrite hspec_step.
        specialize @impl_step_increment_mem_cycles with (1:= HImplInv) (2:=HImpl_step).
        intros himpl_cycles.
        eapply sim_cycles_plus with (2:=himpl_cycles).
        apply Sim_cycles_mem. assumption.
      + apply spec_step_increment_cycles in hspec_step. setoid_rewrite hspec_step.
        specialize @impl_step_increment_sm_cycles with (1:= HImplInv) (2:=HImpl_step).
        intros himpl_cycles.
        erewrite Sim_cycles_sm in himpl_cycles by eauto.
        rewrite nat_odd_plus_even by auto.
        rewrite<-PeanoNat.Nat.negb_odd.
        destruct_with_eqn (PeanoNat.Nat.odd (cycles spec_st)); cbn in himpl_cycles; simplify.
        * setoid_rewrite H0. auto.
        * setoid_rewrite H0. auto.
  Qed.
  Lemma step_n'_sim:
  forall (external_world_state_t: Type)
    (input_machine: @i_machine_t external_world_state_t output_t input_t)
    (n: nat)
    (ext_st ext_st'__spec: external_world_state_t)
    (impl_st: machine_state_t) (spec_st spec_st': spec_state_t)
    (output__spec: list output_t),
      Sim impl_st spec_st ->
      Spec.step_n'
        SecurityParams.local_step_fn0
        SecurityParams.local_step_fn1
        SpecParams.can_start_fn
        SecurityParams.spin_up_machine
        SecurityParams.extract_dram
        SecurityParams.extract_rf
        input_machine n spec_st ext_st = (spec_st', ext_st'__spec, output__spec) ->
      match Impl.step_n' input_machine n impl_st ext_st with
      | Success (impl_st', ext_st'__impl, output__impl) =>
        Sim impl_st' spec_st' /\ ext_st'__impl = ext_st'__spec /\ output__impl = output__spec
      | Failure _ => False
      end.
  Proof.
    induction n.
    - simpl; propositional; simplify; auto.
    - intros * HSim Hstep__spec.
      specialize IHn with (1 := HSim).
      unfold Impl.step_n', Machine.step_n' in *.
      unfold Spec.step_n' in *.
      rewrite rewrite_step_succ_n'.
      rewrite rewrite_safe_step_succ_n' in Hstep__spec.
      destruct_match_pairs. simplify_tupless.
      specialize IHn with (1 := Heqp); propositional.
      bash_destruct IHn; propositional.
      specialize step_sim with (1 := IHn0) (2 := Heqp1).
      intros Hstep_sim. simplify.
      revert Heqr1. unfold Impl.step, Machine.step, StateMachine.step. (* revert: bypass slow QED *)
      propositional.  simpl_match. auto.
   Qed.
  Theorem simulation :
  forall (initial_dram: dram_t)
  (external_world_state_t: Type)
  (input_machine: @i_machine_t external_world_state_t output_t input_t)
        (n: nat),
        WF_dram initial_dram ->
        Impl.step_n initial_dram input_machine n =
          Success (Spec.step_n SecurityParams.local_step_fn0
                               SecurityParams.local_step_fn1
                               SpecParams.can_start_fn
                               SecurityParams.spin_up_machine
                               SecurityParams.extract_dram
                               SecurityParams.extract_rf
                               (dram_to_mem_map EnclaveParams.enclave_sig initial_dram) input_machine n).
  Proof.
    intros * wf_dram. unfold Impl.step_n, Spec.step_n, step_n, safe_step_n, Machine.step_n.
    unfold Machine.step_n. destruct_match_pairs; simplify.
    specialize step_n'_sim with (1 := @InitialSim initial_dram wf_dram) (2 := Heqp).
    intros Impl__step. simplify. propositional.
    consider @Impl.step_n'. consider Machine.step_n'.
    consider @StateMachine.step_n.
    setoid_rewrite Heqr0. reflexivity.
  Qed.






End Pf.
