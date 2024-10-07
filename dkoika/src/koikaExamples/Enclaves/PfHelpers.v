Require Import rv_isolation.Common.
Require Import rv_isolation.Machine.
Require Import rv_isolation.rv32.
Require Import rv_isolation.SecurityMonitor.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koikaExamples.Enclaves.ProofUtils.
Require Import koikaExamples.Enclaves.PfDefs.

Require Import FunctionalExtensionality.
  Import ExternalMemory.
  Import TopLevelModuleHelpers.

  Lemma WF_ext_log_call_length:
    forall log fn n,
    WF_ext_log _ext_fn_tys log ->
    match Typechecking.lookup_ext_fn_type _ext_fn_tys (_ext fn) tt with
    | Success (n, _) => Success n
    | Failure _ => Failure tt
    end = Success n ->
    Datatypes.length (unsafe_get_ext_call_from_log log (_ext fn)) = n.
  Proof.
    consider WF_ext_log.
    intros. simplify. consider @lookup_ext_fn_type.
    consider unsafe_get_ext_call_from_log. consider SemanticUtils.unsafe_get_ext_call_from_log.
    simplify. consider @lookup_ext_fn.
    simplify.
    assert (Datatypes.length (zeroes (unsafe_get_ext_fn_arg_type (_ext fn))) = n) as Hlen.
    { consider _ext_fn_tys.
      destruct fn; simpl in *; simplify; reflexivity.
    }
    destruct_match; auto.
    destruct_match; subst; auto.
      specialize H with (1 := Heqo). propositional. simplify. setoid_rewrite Heqo1 in Heqo0.
        simplify; auto.
  Qed.
  Lemma mem_get_response__koika__Success:
    forall mem,
      WF_ext_mem mem ->
      match mem_get_response__koika mem with
      | Success res => Datatypes.length res = _unsafe_struct_sz mem_output
      | Failure _ => False
      end.
  Proof.
    intros * Hwf. unfold mem_get_response__koika. destruct_match; auto with simplify_bits.
    assert (Datatypes.length (mem_resp_byte_en m) = 4) by (eauto with solve_invariants).
    assert (Datatypes.length (mem_resp_addr m) = 32) by (eauto with solve_invariants).
    assert (Datatypes.length (mem_resp_data m) = 32) by (eauto with solve_invariants).
    simplify_structs_as Hmem_resp.
    simplify_structs_as Hmem_output.
    auto.
  Qed.
  Lemma enclave_config_to_enclave_request_length:
    forall config,
    Datatypes.length (enclave_config_to_enclave_request config) = _unsafe_struct_sz enclave_req.
  Proof.
    intros. unfold enclave_config_to_enclave_request.
    unfold success_or_default.
    simplify_structs_as Foo; simpl; auto.
    unfold enclave_id_to_vect. rewrite length_of_nat. auto.
  Qed.
  Lemma opt_enclave_config_to_enclave_data_length:
   forall opt_config,
   Datatypes.length (opt_enclave_config_to_enclave_data opt_config)  = _unsafe_struct_sz enclave_data.
  Proof.
    intros *. unfold opt_enclave_config_to_enclave_data. destruct_match; auto.
    unfold enclave_config_to_valid_enclave_data. unfold success_or_default.
    simplify_structs_as Foo; simpl.
    - apply enclave_config_to_enclave_request_length.
    - auto.
  Qed.
  Lemma WF_state_update_env:
    forall reg_types reg_env reg new_v default,
    WF_state reg_types reg_env ->
    match lookup_reg_type reg_types reg with
    | Some v => beq_dec (Datatypes.length new_v) v
    | _ => true
    end = true ->
    WF_state reg_types (SortedRegEnv.update reg_env reg (fun _ => new_v) default).
  Proof.
    consider WF_state. consider get_reg.
    intros. specialize (H reg0).
    destruct_match; auto. simpl.
    simplify.
    destruct_with_eqn (beq_dec reg reg0); simplify.
    - rewrite SortedRegEnv.update_correct_eq. rewrite Heqo0.
      setoid_rewrite Heqo in H0. simplify. auto.
    - rewrite SortedRegEnv.update_correct_neq; auto. rewrite Heqo0. reflexivity.
  Qed.
Lemma enclave_data_to_config_involutive:
  forall config,
  unsafe_enclave_data_to_config (enclave_config_to_valid_enclave_data config) = config.
Proof.
  intros; simpl.
  unfold unsafe_enclave_data_to_config, enclave_config_to_valid_enclave_data. destruct config; simpl.
  unfold success_or_default.
  simplify_structs_as hdata; simpl.
  - apply enclave_config_to_enclave_request_length.
  - pose proof (eta_expand_list_correct false s) as henc_data.
    rewrite hdata in henc_data.
    cbn in henc_data. rewrite henc_data in *.
    unfold unsafe_enclave_req_to_config.
    cbn - [nth].
    f_equal.
    + destruct config_eid; cbv - [nth] in Heqr0; simplify; auto.
    + apply functional_extensionality. destruct config_eid; cbv - [nth] in Heqr0; simplify; destruct x; auto.
    + destruct config_ext_uart; cbv - [nth] in Heqr0; simplify; auto.
    + destruct config_ext_led; cbv - [nth] in Heqr0; simplify; auto.
    + destruct config_ext_finish; cbv - [nth] in Heqr0; simplify; auto.
Qed.
Lemma enclave_config_valid_length:
  forall eid,
  Datatypes.length (enclave_config_to_valid_enclave_data eid) = _unsafe_struct_sz enclave_data.
Proof.
  intros. unfold enclave_config_to_valid_enclave_data.
  consider @success_or_default.
  simplify_structs_as Hinit; simplify; simpl; auto.
  apply enclave_config_to_enclave_request_length.
Qed.
Lemma enclave_config_to_valid_enclave_data_valid:
  forall config,
    unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid enclave_data)) (_fld enclave_data "valid")
        (enclave_config_to_valid_enclave_data config) = Ob~1.
Proof.
  intros. unfold enclave_config_to_valid_enclave_data.
  destruct config; simpl.
  unfold enclave_config_to_enclave_request. simpl.
  unfold enclave_id_to_vect.
  unfold shared_regions_to_vect.
  destruct config_eid; auto.
Qed.
Lemma reg_to_debug_id_inj:
  forall x y,
  _id (reg_to_debug_id x) = _id (reg_to_debug_id y) ->
  x = y.
Proof.
  intros.
  consider reg_to_debug_id.
  unfold _id in *. unfold snd in *.
  apply Nnat.Nat2N.inj_iff in H.
  apply FiniteType.finite_index_injective in H. subst. auto.
Qed.

Lemma reg_type_ok:
  forall x,
    In x FiniteType.finite_elements ->
  _reg_t x = Types.type_sz (R x).
Proof.
  intros. consider _reg_t.
  change _reg_types with  (id_transform_reg_types _id reg_types).
  change reg_types with (map (fun r => ((reg_to_debug_id r), Types.type_sz (R r))) (FiniteType.finite_elements)).
  unfold id_transform_reg_types. rewrite map_map.
  destruct_match; auto.
  - destruct_match_pairs. subst. apply find_some in Heqo. propositional; simplify.
    rewrite in_map_iff in Heqo0. propositional; simplify.
    consider _rid.
    apply reg_to_debug_id_inj in H0. subst. auto.
  - eapply find_none with (x := (_rid x, Types.type_sz (R x))) in Heqo; simplify; auto.
    rewrite in_map_iff. exists x. eauto.
Qed.

Lemma WF_state_implied:
  forall st,
  (forall reg, match get_reg st (_rid reg) with
          | Some v => Datatypes.length v = _reg_t reg
          | None => False
          end) ->
  WF_state (SortedRegEnv.to_list reg_type_env) st.
Proof.
  intros. consider WF_state.
  intros. unfold reg_type_env.
  change _reg_types with (id_transform_reg_types _id reg_types).
  change reg_types with (map (fun r => ((reg_to_debug_id r), Types.type_sz (R r))) (@FiniteType.finite_elements _ FiniteType_reg_t)).
  unfold SortedRegEnv.from_list, SortedRegEnv.to_list. unfold SortedRegEnv.Env.
  unfold id_transform_reg_types. rewrite map_map.
  unfold lookup_reg_type. destruct_match; auto. destruct_match_pairs; simplify.
  apply find_some in Heqo. propositional; simplify. apply in_map_iff in Heqo0.
  propositional; simplify.
  specialize H with (reg := x). simplify.
  unfold _rid in *. simpl_match.
  rewrite<-reg_type_ok; auto.
Qed.
Lemma in_finite_elements:
  forall {T} (FT: FiniteType.FiniteType T) (t: T),
    In t (@FiniteType.finite_elements _ FT).
Proof.
  intros. eapply nth_error_In with (n := FiniteType.finite_index t).
  apply FiniteType.finite_surjective.
Qed.

Lemma length_r_ok:
  forall params0 params1 mem_turn sm_turn reg,
  Datatypes.length params0.(machine_pc) = 32 ->
  Datatypes.length params1.(machine_pc) = 32 ->
  Datatypes.length mem_turn = 2 ->
  Datatypes.length sm_turn = 1 ->
  Datatypes.length (r params0 params1 mem_turn sm_turn reg) = Types.type_sz (R reg).
Proof.
  intros * hpc1 hpc2 hmem_turn hsm_turn . unfold r. rewrite reg_type_ok.
  2: { apply in_finite_elements. }
  destruct_match; auto.
  - destruct_match; try rewrite zeroes_length; auto.
    destruct_match.
    destruct_match; try rewrite zeroes_length; auto.
    rewrite bits_slice_length. auto.
  - destruct_match; try rewrite zeroes_length; auto.
    destruct_match.
    destruct_match; try rewrite zeroes_length; auto.
    rewrite bits_slice_length. auto.
  - destruct_match; auto; try rewrite zeroes_length; auto.
  - repeat destruct_match; auto; try rewrite zeroes_length; auto;
      rewrite opt_enclave_config_to_enclave_data_length; auto.
Qed.
Lemma initial_koika_state_lookup:
  forall params0 params1 mem_turn sm_turn reg,
  get_reg (initial_koika_state params0 params1 mem_turn sm_turn) (_rid reg)
    = Some (r  params0 params1 mem_turn sm_turn reg).
Proof.
  unfold initial_koika_state.
  intros.
  unfold unsafe_get_reg, r_get_reg.
  unfold SortedRegEnv.from_list. unfold get_reg, SortedRegEnv.opt_get. unfold SortedRegEnv.Env.
  destruct_match; destruct_match_pairs; subst; simpl.
  - apply find_some in Heqo. destruct_match_pairs. propositional; simplify.
    rewrite in_map_iff in Heqo0.
    propositional. simplify. unfold _rid in *.
    apply reg_to_debug_id_inj in H. subst. auto.
  - specialize find_none with (1 := Heqo).
    intros.
    set (r params0 params1 mem_turn sm_turn reg) as z.
    specialize H with (x := (_rid reg,z)).
    rewrite in_map_iff in H. rewrite beq_dec_false_iff in H.
    exfalso.
    apply H; auto.
    exists reg. split; auto.
    apply in_finite_elements.
Qed.

Lemma initial_koika_state_lookup':
  forall params0 params1 mem_turn sm_turn reg,
  (initial_koika_state params0 params1 mem_turn sm_turn).[_rid reg] =
    r  params0 params1 mem_turn sm_turn reg.
Proof.
  unfold unsafe_get_reg, r_get_reg. intros. rewrite initial_koika_state_lookup. auto.
Qed.

Lemma WF_initial_koika_state:
  forall params0 params1 mem_turn sm_turn,
  Datatypes.length params0.(machine_pc) = 32 ->
  Datatypes.length params1.(machine_pc) = 32 ->
  Datatypes.length mem_turn = 2 ->
  Datatypes.length sm_turn = 1 ->
  WF_state (SortedRegEnv.to_list reg_type_env)
    (initial_koika_state params0 params1 mem_turn sm_turn).
Proof.
  intros * hpc1 hpc2 hmem_turn hsm_turn .
  apply WF_state_implied. intros.
  rewrite initial_koika_state_lookup.
  rewrite length_r_ok; auto.
  rewrite reg_type_ok; auto.
  apply in_finite_elements.
Qed.
Lemma disjoint_configs_sym:
  forall e1 e2,
  disjoint_configs e1 e2 ->
  disjoint_configs e2 e1.
Proof.
  intros. inversions H.
  constructor; eauto.
  - intros; propositional; eapply disjoint_shared_regions; eauto.
  - propositional; eauto.
  - propositional; eauto.
  - propositional; eauto.
Qed.
    Lemma can_enter_enclave_implies_disjoint:
      forall config1 config2,
        can_enter_enclave config1 (Some config2) = true ->
        disjoint_configs config1 config2.
    Proof.
      intros * henter. consider can_enter_enclave.
      rewrite negb_true_iff in henter.
      consider configs_conflict. repeat rewrite orb_false_iff in henter.
      repeat rewrite andb_false_iff in henter. propositional; simplify.
      constructor.
      - unfold not; intros heid. rewrite heid in *.
        rewrite internal_enclave_id_dec_lb in *; auto. discriminate.
      - intros *; propositional.
        consider shared_regions_conflict.
        destruct region; rewrite H0 in henter5; rewrite H1 in henter5; simpl in henter5;
          repeat rewrite orb_true_r in henter5; try discriminate.
      - propositional. rewrite H0 in *. rewrite H1 in *.
        split_cases; discriminate.
      - propositional. rewrite H0 in *. rewrite H1 in *.
        split_cases; discriminate.
      - propositional. rewrite H0 in *. rewrite H1 in *.
        split_cases; discriminate.

    Qed.
    Lemma get_enclave_dram_update_regions_eq:
      forall regions config config' dram enclave_sig,
      configs_conflict config (Some config') = false ->
      get_enclave_dram enclave_sig regions config =
      get_enclave_dram enclave_sig (update_regions enclave_sig config' dram regions) config.
    Proof.
      intros * Hconflict.
      consider configs_conflict.
      unfold shared_regions_conflict in *.
      repeat rewrite orb_false_iff in *. repeat rewrite andb_false_iff in *. propositional.
      unfold update_regions.
      unfold get_enclave_dram. apply functional_extensionality. intros addr.
      repeat destruct_match; unfold filter_dram;
        repeat match goal with
               | H: _ && _ = true |- _ => rewrite andb_true_iff in H
               | H: _ \/ true = false |- _ => destruct H; [ | discriminate]
               | H1: ?x = _, H2: ?x = _ |- _ => rewrite H1 in H2; clear H1
               | _ => progress(try simpl_match; try discriminate; propositional)
               end.
    Qed.
