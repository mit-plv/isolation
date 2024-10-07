Require Import rv_cache_isolation.Common.
Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.EnclaveWithCache.ExtractionUtils.
Require Import koikaExamples.EnclaveWithCache.ProofUtils.
Require Import koikaExamples.EnclaveWithCache.PfDefs.
Require Import koikaExamples.EnclaveWithCache.ProofCore_symb.
Require Import koikaExamples.EnclaveWithCache.SmProofs.
Require Import koikaExamples.EnclaveWithCache.MemoryProofs.
Require Import koikaExamples.EnclaveWithCache.SymbSpec.
Require Import koikaExamples.EnclaveWithCache.PfImplDefs.
Require Import koikaExamples.EnclaveWithCache.PfImplLemmas_sig.
Require Import koikaExamples.EnclaveWithCache.PfChain.
Require Import koikaExamples.EnclaveWithCache.PfSim_sig.
Require Import koikaExamples.EnclaveWithCache.PfImplHelpers.
Require Import koikaExamples.EnclaveWithCache.PfChainHelpers_sig.
Import TopLevelModuleHelpers.

Module PfChainHelpers (EnclaveParams: EnclaveParams_sig)
                   (SecurityParams: SecurityParams_sig EnclaveParams)
                   (ImplDefs: PfImplDefs EnclaveParams SecurityParams)
                   (SmtOk: SMT_Chain_sig EnclaveParams)
                   (PfChain: PfChain.PfChain EnclaveParams SecurityParams SmtOk)
                   : PfChainHelpers_sig EnclaveParams SecurityParams ImplDefs.

Module Import ImplHelpers := ImplHelpers EnclaveParams SecurityParams ImplDefs.
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.

  Import SecurityParams.
  Import ExternalMemory.
  Import ImplDefs.
  Import PfChain.
  Import Utils.PfHelpers.
  Import TopLevelModuleHelpers.
  Module Import PfLemmas := PfLemmas EnclaveParams SecurityParams.
  (* TODO: MOVE *)
  Lemma ImplInvariant_destruct:
    forall st,
      strong_WF_state reg_type_env st.(machine_koika_st) ->
      WF_ext_mem (machine_mem_st st) ->
      (forall (cache : mem_type) (core : ind_core_id),
        wf_cache_pair cache core (machine_koika_st st)
          (ext_l1_caches (machine_mem_st st) cache core))  ->
      ImplInvariant_spreds EnclaveParams.enclave_sig (st) ->
      ImplInvariant st.
  Proof.
    intros * hwf_st hwf_mem hwf_caches pres. consider ImplInvariant_spreds.
    propositional; constructor; auto.
  Qed.

  Lemma ImplInvariant_implies_spreds:
    forall st,
      ImplInvariant st ->
      ImplInvariant_spreds EnclaveParams.enclave_sig st.
  Proof.
    intros * H; destruct H; propositional.
    constructor; auto.
  Qed.
Ltac basic_cbn_in H :=
  cbn - [_id _sid _fld mk_sigma_fn of_N_sz] in H.

Import PfHelpers.
Import CoreSymbDefs.
Import SymbSimDefs.

Import SymbPfChain.
Import SMSymbDefs.

Ltac init_interp ::=
  repeat
   match goal with
   | |- dummy_interp _ _ _ _ _ _ => unfold dummy_interp, dummy_pkg
   | |- Forall (fun '(_, p) => interp_fancy_spred _ _) _ => rewrite <- forall_preprocess_fancy_spreds_correct
   | |- Forall (fun '(_, p) => interp_fancy_spred2 _ _ _) _ => rewrite <- forall_preprocess_fancy_spreds_correct2
   end.
  Lemma ImplInvariant_implies_sm_inv:
    forall init_st mid_st final_st ext_log1 ext_log2 sigma input,
    ImplInvariant init_st ->
    sigma = mk_sigma_fn (machine_mem_st init_st) input ->
    dummy_interp (machine_koika_st init_st) mid_st final_st sigma ext_log1 ext_log2
      (map_fst CustomSM (sm_invariant EnclaveParams.enclave_sig impl_init impl_get_field)).
  Proof. (* DONE *)
    intros * hinv sigma. subst.
    specialize ImplInv_SMInvariant with (1 := hinv) (input := dummy_input_t).
    consider SMPre. consider sm_pre_conds. rewrite Forall_app. unfold dummy_interp. propositional.
    apply Forall_ignore_map_fst. revert H1.
    repeat rewrite<-forall_preprocess_fancy_spreds_correct.
    apply forall_interp_spred_package_equiv; solve_package_equiv.
  Qed. (* DONE *)

Hint Resolve WF_mk_sigma_fn: modularity.
#[global] Hint Resolve @WF_ext_log__empty: modularity.
#[global] Hint Resolve strong_WF_state_weaken : modularity.
#[global] Hint Resolve @ImplInv_Core0Invariant: modularity.
#[global] Hint Resolve @ImplInv_Core1Invariant: modularity.
#[global] Hint Resolve @ImplInv_WF_ext_mem : modularity.
#[global] Hint Resolve @ImplInv_WF_state : modularity.
#[global] Hint Resolve @ImplInv_WF_state : solve_invariants.
#[global] Hint Resolve @WF_mk_sigma_fn: solve_invariants.
(* #[global] Hint Resolve @WF_mk_sigma_fn': solve_invariants. *)
#[global] Hint Resolve @ImplInv_WF_ext_mem: solve_invariants.
#[global] Hint Rewrite ext_log_app_empty_r: solve_invariants.
#[global] Hint Resolve WF_ext_log_app : modularity.

Ltac solve_package_equiv ::=
  constructor; unfold package_equiv_taint'; split_ands_in_goal;
   (solve [ left; trivial ]) || (right; vm_compute; reflexivity).
(* Lemma or_zeroes: *)
(*   forall v, *)
(*   or v (zeroes (Datatypes.length v)) = Success v. *)
(* Proof. *)
(*   unfold or. induction v; auto. *)
(*   simpl. setoid_rewrite IHv. rewrite orb_false_r. auto. *)
(* Qed. *)

(* Lemma unsafe_get_ext_call_from_log_app_empty_r: *)
(*   forall log1 log2 fn, *)
(*   WF_ext_log _ext_fn_tys log1 -> *)
(*   unsafe_get_ext_call_from_log log2 fn = zeroes (unsafe_get_ext_fn_arg_type fn) -> *)
(*   unsafe_get_ext_call_from_log (ext_log_app log1 log2) fn = *)
(*   unsafe_get_ext_call_from_log log1 fn. *)
(* Proof. *)
(*   consider ext_log_app. consider unsafe_get_ext_call_from_log. *)
(*   consider SemanticUtils.unsafe_get_ext_call_from_log. *)
(*   intros. rewrite SortedExtFnEnv.opt_get_mapV. *)
(*   rewrite SortedExtFnEnv.opt_get_zip_default. *)
(*   consider unsafe_get_ext_fn_arg_type. *)
(*   destruct_all_matches; auto. *)
(*   consider WF_ext_log. specialize H with (1 := Heqo). propositional. *)
(*   consider SemanticUtils.unsafe_get_ext_fn_arg_type. *)
(*   setoid_rewrite H0. *)
(*   rewrite or_zeroes. auto. *)
(* Qed. *)
Instance EqDec_mem_custom_t : EqDec mem_custom_t := _.
Instance EqDec_custom_chaining_asserts  : EqDec custom_chaining_asserts := _.
Instance EqDec_sm_custom_t : EqDec sm_custom_t := _.
Ltac convert_get_field :=
  match goal with
  | H: _get_field _ _ _ = Success _ |- _ =>
      eapply _get_field_implies_unsafe_get_field in H; [ | reflexivity | reflexivity]
  end.

Lemma mem_step_put_valid_implied:
  forall ext_log mem mem' arg input,
  WF_ext_log _ext_fn_tys ext_log ->
  mainmem__ext (obs_mainmem (get_mem_observations ext_log)) (ext_main_mem mem) = Success (ext_main_mem mem') ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid mem_output))
        (_fld mem_output "get_valid")
        (unsafe_call_ext (mk_sigma_fn mem' input) (_id (_extid ext_mainmem)) arg) = Ob~1 ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid mem_input))
    (_fld mem_input "put_valid") (unsafe_get_ext_call_from_log ext_log (_id (_extid ext_mainmem))) =
  Ob~1.
Proof.
  intros * hwf hupdate hget_valid. intros.
  (* apply ext_mem_update_memory_implies_main_mem in hupdate. *)
  consider mainmem__ext. simplify.

  bash_destruct hupdate.
  { consider update_dram. simplify. destruct_matches_in_hyp hupdate; simplify.
    - repeat convert_get_field. auto.
    - unfold mk_sigma_fn in hget_valid. rewrite<-H0 in *. cbv in hget_valid. discriminate.
  }
  { simplify.
    unfold mk_sigma_fn in hget_valid. rewrite<-H0 in *. cbv in hget_valid. discriminate.
  }
Qed.
Lemma main_mem_get_valid_implies_put_load:
  forall mem ext_log arg big_mem' input,
  mainmem__ext (unsafe_get_ext_call_from_log ext_log (_ext ext_mainmem)) mem = Success (ext_main_mem big_mem') ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid mem_input))
                 (_fld mem_input "put_valid")
                 (SemanticUtils.unsafe_get_ext_call_from_log _ext_fn_tys ext_log (_id (_extid ext_mainmem))) =
               Ob~1 ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid mem_output))
             (_fld mem_output "get_valid") (unsafe_call_ext (mk_sigma_fn big_mem' input) (_id (_extid ext_mainmem)) arg) =
           Ob~1 ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid mem_req)) (_fld mem_req "byte_en")
    (unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid mem_input)) (_fld mem_input "put_request")
       (SemanticUtils.unsafe_get_ext_call_from_log _ext_fn_tys ext_log (_id (_extid ext_mainmem)))) = Ob~0~0~0~0.
Proof.
  intros * hmain hput_valid hget_valid. consider mainmem__ext.  simplify.
  repeat convert_get_field.
  simplify. simpl in *. simpl_match. setoid_rewrite hput_valid in hmain.
  consider update_dram. simplify. bash_destruct hmain; simplify; try rewrite<-H0 in *.
  - repeat convert_get_field. auto.
  - repeat convert_get_field. auto.
  - exfalso. unfold mk_sigma_fn in hget_valid. rewrite<-H0 in *. cbv in hget_valid. discriminate.
Qed.

(* Lemma _get_field_length_implied : *)
(*   forall sig fld data ret, *)
(*   _get_field sig  fld data = Success ret -> *)
(*   Datatypes.length data = _unsafe_struct_sz sig. *)
(* Proof. *)
(*   intros. consider _get_field. consider get_field. simplify. *)
(*   unfold Semantics.get_field in *. simplify. *)
(*   consider _unsafe_struct_sz. *)
(*   unfold struct_sz. unfold _lookup_struct. simpl_match. auto. *)
(* Qed. *)
(* Lemma _get_field_success': *)
(*   forall (struct_def : Types.struct_sig' Types.type) (fld : string) (v : list bool) (width : nat) value, *)
(*   match _lookup_struct struct_def with *)
(*   | Success s => Datatypes.length v = struct_sz' (dstruct_fields s) *)
(*   | Failure _ => False *)
(*   end -> *)
(*   match _lookup_struct struct_def with *)
(*   | Success s => get_field_width (dstruct_fields s) (unsafe_lookup_field_idx s fld) = Success width *)
(*   | Failure _ => False *)
(*   end -> *)
(*   _get_field struct_def fld v = Success value -> *)
(*   Datatypes.length value = width. *)
(* Proof. *)
(*   intros. specialize _get_field_success with (1 := H) (2 := H0). *)
(*   simpl_match; auto. *)
(* Qed. *)

Lemma impl_ext_mem_correct_core_implied:
  forall init_st impl_st__koika final_koika_st s input mid_ext_log ext_log core impl_mem ,
  WF_ext_log _ext_fn_tys (ext_log ) ->
  SemanticUtils.unsafe_get_ext_call_from_log _ext_fn_tys mid_ext_log (_ext ext_mainmem) =
    (zeroes (unsafe_get_ext_fn_arg_type (_ext ext_mainmem))) ->
  update_memory (get_mem_observations (ext_log_app ext_log mid_ext_log)) impl_mem = Success s ->
  interp_fancy_spred
    (dummy_pkg init_st impl_st__koika final_koika_st (mk_sigma_fn impl_mem input) (Some mid_ext_log) ext_log)
    (MemSymbDefs.impl_post_ext_mem_correct_core core impl_final impl_get_field impl_final_ext) ->
  interp_fancy_spred
    (dummy_pkg init_st impl_st__koika final_koika_st (mk_sigma_fn impl_mem input) (Some mid_ext_log) ext_log)
    (MemSymbDefs.impl_post_main_mem_put_is_read_turn impl_final impl_get_field impl_final_ext) ->
  interp_fancy_spred
    (dummy_pkg final_koika_st impl_st__koika final_koika_st (mk_sigma_fn s input) (Some mid_ext_log) ext_log)
    (MemSymbDefs.impl_ext_mem_correct_core core impl_init impl_get_field).
Proof.
  intros * hwf hzero hupdate hpost_correct hpost_turn.
  apply ext_mem_update_memory_implies_main_mem in hupdate.
  simpl in hupdate.
  setoid_rewrite unsafe_get_ext_call_from_log_app_empty_r with (1 := hwf) (2 := hzero) in hupdate.
  destruct core.
  - unfold MemSymbDefs.impl_ext_mem_correct_core.
    cbn - [_id _sid _fld mk_sigma_fn] in *.
    intros * hlen hvalid.
    assert_pre_as hput_valid hpost_correct.
    { eapply mem_step_put_valid_implied; eauto. }
    propositional. split; [auto | ].
    intros. apply hpost_correct; auto.
    eapply main_mem_get_valid_implies_put_load; eauto.
  - unfold MemSymbDefs.impl_ext_mem_correct_core.
    cbn - [_id _sid _fld mk_sigma_fn] in *.
    intros * hlen hvalid.
    assert_pre_as hput_valid hpost_correct.
    { eapply mem_step_put_valid_implied; eauto. }
    propositional. split; [auto | ].
    intros. apply hpost_correct; auto.
    eapply main_mem_get_valid_implies_put_load; eauto.
Qed.
Lemma mem_post_conds_impl_cache_post_conds:
  forall f reg_init reg_final get_field ext_log,
  Forall f (MemSymbDefs.mem_post_conds EnclaveParams.enclave_sig reg_init reg_final ext_log get_field) ->
  Forall f (List.concat
              (map (fun '(cache, core) => MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field ext_log)
                 [(imem, CoreId0); (dmem, CoreId0); (imem, CoreId1); (dmem, CoreId1)])).
Proof.
  intros. unfold MemSymbDefs.mem_post_conds in *. consider MemSymbDefs.mem_post_conds'.
  consider MemSymbDefs.mem_post_conds'_preserve.
  repeat rewrite Forall_app in H. split_ands_in_hyps. auto.
Qed.
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

Ltac simplify_structs_init_as H :=
  match goal with
  | |- context [ _struct_init ?struct_def ?fields] =>
        pose proof (_struct_init_success struct_def fields) as H ; assert_pre_and_specialize H;
         [ repeat constructor; auto |  ]
  end.

Lemma mem_cache_put_ready_implied:
  forall cache core mem input ,
  WF_ext_mem mem ->
  forall y : vect_t,
  Datatypes.length y = unsafe_get_ext_fn_arg_type (_ext (Memory.Memory.ext_cache cache core)) ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid cache_output_sig))
    (_fld cache_output_sig "put_ready")
    (unsafe_call_ext (mk_sigma_fn mem input) (_id (_extid (Memory.Memory.ext_cache cache core))) y) = Ob~1 \/
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid cache_input_sig))
    (_fld cache_input_sig "put_valid") y = Ob~0 \/
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid cache_input_sig))
    (_fld cache_input_sig "get_ready") y = Ob~0.
Proof.
  intros * hwf.
  intros arg hlen.
  specialize cache_get_response__koika__Success with (1 := hwf); intros hresp.
  specialize (hresp cache core arg).
  assert_pre_and_specialize hresp.
  { destruct cache; destruct core; auto. }
  destruct_matches_in_hyp_as hresp hresp'; auto.
  erewrite rewrite_call_cache_fn with (mem' := mem); eauto.
  consider cache_get_response__koika.
  destruct_matches_in_hyp_as hresp' get_ready; [ | discriminate].
  destruct_matches_in_hyp_as hresp' put_request; [ | discriminate].
  destruct_matches_in_hyp_as hresp' put_valid ; [ | discriminate].
  assert (Datatypes.length s2 = 1) as hlen'.
    { eapply _get_field_success'; eauto; try reflexivity. simpl.
      erewrite _get_field_length_implied; eauto. reflexivity.
    }
  destruct s2; [discriminate | ]. destruct s2; [ | discriminate ].

  bash_destruct hresp'.
  - revert hresp'.
    assert (Datatypes.length v = 32) as hv_len.
    { eapply WF_cache_resp; eauto. eapply WF_pair_cache. eapply WF_ext_l1_caches. auto. }
    simplify_structs_init_as foo; simpl.
    intros; simplify.
    pose proof (eta_expand_list_correct false v) as hv. rewrite hv_len in hv. cbn in hv.
    rewrite hv in Heqr0. cbv - [nth] in Heqr0. simplify.
    destruct b; [left; reflexivity| ].
    { repeat convert_get_field. right. setoid_rewrite put_valid. auto. }
  - simplify. repeat convert_get_field. setoid_rewrite get_ready. auto.
  -    destruct b.
    { cbv in hresp'. simplify. auto. }
    { repeat convert_get_field. setoid_rewrite put_valid. auto. }
Qed.

Lemma mem_meta_put_ready_implied:
  forall cache core mem input ,
  WF_ext_mem mem ->
  forall y : vect_t,
  Datatypes.length y = unsafe_get_ext_fn_arg_type (_ext (Memory.Memory.ext_metadata cache core)) ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid metadata_output_sig))
    (_fld metadata_output_sig "put_ready")
    (unsafe_call_ext (mk_sigma_fn mem input) (_id (_extid (Memory.Memory.ext_metadata cache core))) y) = Ob~1 \/
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid metadata_input_sig))
    (_fld metadata_input_sig "put_valid") y = Ob~0 \/
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid metadata_input_sig))
    (_fld metadata_input_sig "get_ready") y = Ob~0.
Proof.
  intros * hwf.
  intros arg hlen.
  specialize metadata_get_response__koika__Success with (1 := hwf); intros hresp.
  specialize (hresp cache core arg).
  assert_pre_and_specialize hresp.
  { destruct cache; destruct core; auto. }
  destruct_matches_in_hyp_as hresp hresp'; auto.

  erewrite rewrite_call_meta_fn with (mem' := mem); eauto.
  consider metadata_get_response__koika.
  destruct_matches_in_hyp_as hresp' get_ready; [ | discriminate].
  destruct_matches_in_hyp_as hresp' put_request; [ | discriminate].
  destruct_matches_in_hyp_as hresp' put_valid ; [ | discriminate].
  assert (Datatypes.length s2 = 1) as hlen'.
    { eapply _get_field_success'; eauto; try reflexivity. simpl.
      erewrite _get_field_length_implied; eauto. reflexivity.
    }
  destruct s2; [discriminate | ]. destruct s2; [ | discriminate ].

  bash_destruct hresp'.
  - revert hresp'.
    assert (Datatypes.length v = _unsafe_struct_sz metadata_sig) as hv_len.
    { eapply PfDefs.WF_meta_resp; eauto. eapply WF_pair_meta. eapply WF_ext_l1_caches. auto. }
    simplify_structs_init_as foo; simpl.
    intros; simplify.
    pose proof (eta_expand_list_correct false v) as hv. rewrite hv_len in hv. cbn in hv.
    rewrite hv in Heqr0. cbv - [nth] in Heqr0. simplify.
    destruct b; [left; reflexivity| ].
    { repeat convert_get_field. right. setoid_rewrite put_valid. auto. }
  - simplify. repeat convert_get_field. setoid_rewrite get_ready. auto.
  -    destruct b.
    { cbv in hresp'. simplify. auto. }
    { repeat convert_get_field. setoid_rewrite put_valid. auto. }
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


Lemma cache_step_put_valid_implied:
  forall ext_log mem mem' arg input cache core,
  WF_ext_mem mem' ->
  WF_ext_log _ext_fn_tys ext_log ->
  ext_cache_resp (ext_pair_cache (ext_l1_caches mem cache core)) = None \/
  _get_field cache_input_sig "get_ready" (obs_cache (get_mem_observations ext_log) cache core) = Success Ob~1 ->
  Datatypes.length arg = unsafe_get_ext_fn_arg_type (_ext (Memory.Memory.ext_cache cache core)) ->
  cache__ext (obs_cache (get_mem_observations ext_log) cache core) (ext_pair_cache (ext_l1_caches mem cache core))
    = Success (ext_pair_cache (ext_l1_caches mem' cache core)) ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid cache_output_sig))
                 (_fld cache_output_sig "get_valid")
                 (unsafe_call_ext (mk_sigma_fn mem' input) (_id (_extid (Memory.Memory.ext_cache cache core))) arg) = Ob~1 ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid cache_input_sig))
    (_fld cache_input_sig "put_valid")
    (SemanticUtils.unsafe_get_ext_call_from_log _ext_fn_tys ext_log
       (_id (_extid (Memory.Memory.ext_cache cache core)))) = Ob~1 /\
   unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid cache_req_sig)) (_fld cache_req_sig "byte_en")
    (unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid cache_input_sig))
       (_fld cache_input_sig "put_request")
       (SemanticUtils.unsafe_get_ext_call_from_log _ext_fn_tys ext_log
          (_id (_extid (Memory.Memory.ext_cache cache core))))) = Ob~0~0~0~0.
Proof.
  intros * hwf_mem hwf hcase harg_len hupdate hget_valid. intros.
  consider cache__ext. simplify.
  (* repeat convert_get_field. auto. *)
  rewrite cache_arg_type in harg_len.
  specialize cache_get_response__koika__Success with (1 := hwf_mem) (2 := harg_len) (mem_ty := cache) (core := core); intros hresp. simplify.
  erewrite rewrite_call_cache_fn in hget_valid; [ | eauto].
  (* rewrite hno_resp in *. *) rename s into put_valid.
  assert (Datatypes.length put_valid = 1) as hlen_put_valid.
  { bash_destruct hupdate; auto. }
  apply case_singleton_bv in hlen_put_valid.
  assert (ext_cache_resp (ext_pair_cache (ext_l1_caches mem' cache core) ) = None -> False) as hnone'.
  { consider cache_get_response__koika; simplify.
    intros; simpl_match.
    assert (Datatypes.length s4 = 1).
    { repeat unsafe_auto_simplify_structs. auto. }
    destruct s4; [discriminate| ]. destruct s4; [| discriminate ].
    cbv in Heqr3. simplify. cbv in hget_valid. discriminate.
  }
  consider cache_get_response__koika. simplify.
  destruct_matches_in_hyp Heqr3; propositional.
  bash_destruct Heqr3.
  - destruct hcase as [hcase | hcase]; simplify.
    + rewrite hcase in *.
      destruct hlen_put_valid; subst.
      * assert (
            update_cache s0 (ext_cache (ext_pair_cache (ext_l1_caches mem cache core)))
            = Success (ext_pair_cache (ext_l1_caches mem' cache core))) as hmem'.
        { bash_destruct hupdate. }
        unfold update_cache in hmem'.
        simplify. destruct_matches_in_hyp hmem'; simplify.
        { repeat convert_get_field.
          split; auto. setoid_rewrite Heqr1. auto.
        }
        { rewrite<-H0 in *. simpl in Heqo. clear - Heqo. discriminate. }
      * bash_destruct hupdate; propositional; simplify.
        rewrite<-H0 in *. simpl in Heqo. clear - Heqo. discriminate.
    + bash_destruct hupdate; propositional; simplify.
      * consider update_cache; simplify.
        destruct_matches_in_hyp hupdate; simplify.
        { repeat convert_get_field. split; auto. setoid_rewrite Heqr1. auto. }
        { rewrite<-H0 in *.  simpl in Heqo. clear - Heqo. discriminate. }
      * rewrite<-H0 in Heqo. simpl in Heqo. clear - Heqo. discriminate.
  - simplify. cbv in hget_valid. discriminate.
Qed.

Lemma meta_step_put_valid_implied:
  forall ext_log mem mem' arg input cache core,
  WF_ext_mem mem' ->
  WF_ext_log _ext_fn_tys ext_log ->
  ext_metadata_resp (ext_pair_meta (ext_l1_caches mem cache core)) = None \/
  _get_field metadata_input_sig "get_ready" (obs_meta (get_mem_observations ext_log) cache core) = Success Ob~1 ->
  Datatypes.length arg = unsafe_get_ext_fn_arg_type (_ext (Memory.Memory.ext_metadata cache core)) ->
  metadata__ext (obs_meta (get_mem_observations ext_log) cache core) (ext_pair_meta (ext_l1_caches mem cache core))
    = Success (ext_pair_meta (ext_l1_caches mem' cache core)) ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid metadata_output_sig))
                 (_fld metadata_output_sig "get_valid")
                 (unsafe_call_ext (mk_sigma_fn mem' input) (_id (_extid (Memory.Memory.ext_metadata cache core))) arg) = Ob~1 ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid metadata_input_sig))
    (_fld metadata_input_sig "put_valid")
    (SemanticUtils.unsafe_get_ext_call_from_log _ext_fn_tys ext_log
       (_id (_extid (Memory.Memory.ext_metadata cache core)))) = Ob~1 /\
   unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid metadata_req_sig)) (_fld metadata_req_sig "is_write")
    (unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid metadata_input_sig))
       (_fld metadata_input_sig "put_request")
       (SemanticUtils.unsafe_get_ext_call_from_log _ext_fn_tys ext_log
          (_id (_extid (Memory.Memory.ext_metadata cache core))))) = Ob~0.
Proof.
  intros * hwf_mem hwf hcase harg_len hupdate hget_valid. intros.
  consider metadata__ext. simplify.
  (* repeat convert_get_field. auto. *)
  rewrite meta_arg_type in harg_len.
  specialize metadata_get_response__koika__Success with (1 := hwf_mem) (2 := harg_len) (mem_ty := cache) (core := core); intros hresp. simplify.
  erewrite rewrite_call_meta_fn in hget_valid; [ | eauto].
  (* rewrite hno_resp in *. *) rename s into put_valid.
  assert (Datatypes.length put_valid = 1) as hlen_put_valid.
  { bash_destruct hupdate; auto. }
  apply case_singleton_bv in hlen_put_valid.
  assert (ext_metadata_resp (ext_pair_meta (ext_l1_caches mem' cache core) ) = None -> False) as hnone'.
  { consider metadata_get_response__koika; simplify.
    intros; simpl_match.
    assert (Datatypes.length s4 = 1).
    { repeat unsafe_auto_simplify_structs. auto. }
    destruct s4; [discriminate| ]. destruct s4; [| discriminate ].
    cbv in Heqr3. simplify. cbv in hget_valid. discriminate.
  }
  consider metadata_get_response__koika. simplify.
  destruct_matches_in_hyp Heqr3; propositional.
  bash_destruct Heqr3.
  - destruct hcase as [hcase | hcase]; simplify.
    + rewrite hcase in *.
      destruct hlen_put_valid; subst.
      * assert (
            update_metadata s0 (ext_metadata (ext_pair_meta (ext_l1_caches mem cache core)))
            = Success (ext_pair_meta (ext_l1_caches mem' cache core))) as hmem'.
        { bash_destruct hupdate. }
        unfold update_metadata in hmem'.
        simplify. destruct_matches_in_hyp hmem'; simplify.
        { repeat convert_get_field.
          split; auto. setoid_rewrite Heqr1. auto.
        }
        { rewrite<-H0 in *. simpl in Heqo. clear - Heqo. discriminate. }
      * bash_destruct hupdate; propositional; simplify.
        rewrite<-H0 in *. simpl in Heqo. clear - Heqo. discriminate.
    + bash_destruct hupdate; propositional; simplify.
      * consider update_metadata; simplify.
        destruct_matches_in_hyp hupdate; simplify.
        { repeat convert_get_field. split; auto. setoid_rewrite Heqr1. auto. }
        { rewrite<-H0 in *.  simpl in Heqo. clear - Heqo. discriminate. }
      * rewrite<-H0 in Heqo. simpl in Heqo. clear - Heqo. discriminate.
  - simplify. cbv in hget_valid. discriminate.
Qed.

Lemma WF_ext_log_implies_obs_cache_len:
  forall ext_log cache core,
  WF_ext_log _ext_fn_tys ext_log ->
  Datatypes.length (obs_cache (get_mem_observations ext_log) cache core) = _unsafe_struct_sz cache_input_sig.
Proof.
  intros * Wf. consider WF_ext_log.
  unfold get_mem_observations. simpl. unfold _unsafe_get_ext_call_from_log.
  specialize (Wf (_ext (Memory.Memory.ext_cache cache core))).
  unfold SemanticUtils.unsafe_get_ext_call_from_log.
  repeat destruct_match; destruct core; subst; eauto.
  all: specialize Wf with (1 := Heqo); propositional; cbv in Wf0; simplify; auto.
Qed.
Ltac convert_get_field_in H :=
  match type of H with
  | _get_field _ _ _ = Success _  =>
      eapply _get_field_implies_unsafe_get_field in H; [ | reflexivity | reflexivity]
  end.

Lemma impl_ext_cache_no_resp_core_implied:
  forall init_st impl_st__koika final_koika_st mid_ext_log ext_log cache core mem mem' input,
  WF_ext_mem mem' ->
  WF_ext_log _ext_fn_tys (ext_log_app ext_log mid_ext_log) ->
  update_memory (get_mem_observations (ext_log_app ext_log mid_ext_log)) mem = Success mem' ->
  wf_cache_pair cache core init_st (ext_l1_caches mem cache core) ->
  interp_fancy_spred
    (dummy_pkg init_st impl_st__koika final_koika_st (mk_sigma_fn mem input) (Some mid_ext_log) ext_log)
    (MemSymbDefs.cache_obs_get_ready_implied cache core impl_init impl_get_field impl_committed_ext) ->
  interp_fancy_spred
    (dummy_pkg init_st impl_st__koika final_koika_st (mk_sigma_fn mem input) (Some mid_ext_log) ext_log)
    (MemSymbDefs.impl_post_ext_cache_no_resp_core core cache impl_init impl_final impl_get_field impl_committed_ext) ->
  interp_fancy_spred
    (dummy_pkg final_koika_st impl_st__koika final_koika_st (mk_sigma_fn mem' input) (Some mid_ext_log) ext_log)
    (MemSymbDefs.impl_ext_cache_no_resp_core core cache impl_init impl_get_field).
Proof.
  intros * hwf_mem hwf_log hupdate hwf_pair .
  apply ext_mem_update_memory_implies_cache with (cache := cache) (core := core) in hupdate.
  consider cachepair__ext.
  simplify. rename H0 into Hmem'.
  rename Heqr0 into Hcache. rename Heqr1 into Hmeta. rename s into cache'. rename s0 into meta'.
  cbn - [_id _sid _fld mk_sigma_fn].
  assert (cache__ext (obs_cache (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core)
                 (ext_pair_cache (ext_l1_caches mem cache core)) =
               Success (ext_pair_cache (ext_l1_caches mem' cache core))) as hupdate.
      { rewrite<-Hmem'. auto. }
  intros obs_get_ready.
  destruct (ext_cache_resp (ext_pair_cache (ext_l1_caches mem cache core))) eqn:hresp.
  - assert (match _get_field cache_input_sig "get_ready" (obs_cache (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core) with
            | Success v => Datatypes.length v = 1
            | _ => False
            end) as hlen_get_ready.
    { apply get_field_success; auto.
      rewrite WF_ext_log_implies_obs_cache_len; auto.
    }
    simplify.
    apply case_singleton_bv in hlen_get_ready. destruct hlen_get_ready; subst.
    { intros * hpost arg harg_len hget_valid.
      specialize cache_step_put_valid_implied with (mem := mem) (1 := hwf_mem) (2 := hwf_log) (4 := harg_len) (input := input); intros hput_valid.
      assert_pre_and_specialize hput_valid; auto.
      assert_pre_and_specialize hput_valid; auto.
      propositional. eapply hpost; eauto.
    }
    { exfalso.
      convert_get_field. setoid_rewrite obs_get_ready in Heqr0; [discriminate | ].
      destruct hwf_pair. specialize WF_cache_state_inv0 with (1 := hresp).
      setoid_rewrite CacheRespInv_fromCache_invalid with (1 := WF_cache_state_inv0).
      auto.
    }
  - intros * hpost arg harg_len hget_valid.
    specialize cache_step_put_valid_implied with (mem := mem) (1 := hwf_mem) (2 := hwf_log) (4 := harg_len) (input := input); intros hput_valid.
      assert_pre_and_specialize hput_valid; auto.
      assert_pre_and_specialize hput_valid; auto.
      propositional. eapply hpost; eauto.
Qed.
Lemma WF_ext_log_implies_obs_meta_len:
  forall ext_log cache core,
  WF_ext_log _ext_fn_tys ext_log ->
  Datatypes.length (obs_meta (get_mem_observations ext_log) cache core) = _unsafe_struct_sz metadata_input_sig.
Proof.
  intros * Wf. consider WF_ext_log.
  unfold get_mem_observations. simpl. unfold _unsafe_get_ext_call_from_log.
  specialize (Wf (_ext (Memory.Memory.ext_metadata cache core))).
  unfold SemanticUtils.unsafe_get_ext_call_from_log.
  repeat destruct_match; destruct core; subst; eauto;
    specialize Wf with (1 := Heqo); propositional; cbv in Wf0; simplify; auto.
Qed.

Lemma impl_ext_meta_no_resp_core_implied:
  forall init_st impl_st__koika final_koika_st mid_ext_log ext_log cache core mem mem' input,
  WF_ext_mem mem' ->
  WF_ext_log _ext_fn_tys (ext_log_app ext_log mid_ext_log) ->
  update_memory (get_mem_observations (ext_log_app ext_log mid_ext_log)) mem = Success mem' ->
  wf_cache_pair cache core init_st  (ext_l1_caches mem cache core) ->
  interp_fancy_spred
    (dummy_pkg init_st impl_st__koika final_koika_st (mk_sigma_fn mem input) (Some mid_ext_log) ext_log)
    (MemSymbDefs.meta_obs_get_ready_implied cache core impl_init impl_get_field impl_committed_ext) ->
  interp_fancy_spred
    (dummy_pkg init_st impl_st__koika final_koika_st (mk_sigma_fn mem input) (Some mid_ext_log) ext_log)
    (MemSymbDefs.impl_post_ext_meta_no_resp_core core cache impl_init impl_final impl_get_field impl_committed_ext) ->
  interp_fancy_spred
    (dummy_pkg final_koika_st impl_st__koika final_koika_st (mk_sigma_fn mem' input) (Some mid_ext_log) ext_log)
    (MemSymbDefs.impl_ext_meta_no_resp_core core cache impl_init impl_get_field).
Proof.
  intros * hwf_mem hwf_log hupdate hwf_pair .
  apply ext_mem_update_memory_implies_cache with (cache := cache) (core := core) in hupdate.
  consider cachepair__ext.
  simplify. rename H0 into Hmem'.
  rename Heqr0 into Hcache. rename Heqr1 into Hmeta. rename s into cache'. rename s0 into meta'.
  cbn - [_id _sid _fld mk_sigma_fn].
  assert (metadata__ext (obs_meta (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core)
                 (ext_pair_meta (ext_l1_caches mem cache core)) =
               Success (ext_pair_meta (ext_l1_caches mem' cache core))) as hupdate.
      { rewrite<-Hmem'. auto. }
  intros obs_get_ready.
  destruct (ext_metadata_resp (ext_pair_meta (ext_l1_caches mem cache core))) eqn:hresp.
  - assert (match _get_field metadata_input_sig "get_ready" (obs_meta (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core) with
            | Success v => Datatypes.length v = 1
            | _ => False
            end) as hlen_get_ready.
    { apply get_field_success; auto.
      rewrite WF_ext_log_implies_obs_meta_len; auto.
    }
    simplify.
    apply case_singleton_bv in hlen_get_ready. destruct hlen_get_ready; subst.
    { intros * hpost arg harg_len hget_valid.
      specialize meta_step_put_valid_implied with (mem := mem) (1 := hwf_mem) (2 := hwf_log) (4 := harg_len) (input := input); intros hput_valid.
      assert_pre_and_specialize hput_valid; auto.
      assert_pre_and_specialize hput_valid; auto.
      propositional. eapply hpost; eauto.
    }
    { exfalso.
      convert_get_field. setoid_rewrite obs_get_ready in Heqr0; [discriminate | ].
      destruct hwf_pair. specialize WF_meta_state_inv0 with (1 := hresp).
      setoid_rewrite MetaRespInv_fromMeta_invalid with (1 := WF_meta_state_inv0).
      auto.
    }
  - intros * hpost arg harg_len hget_valid.
    specialize meta_step_put_valid_implied with (mem := mem) (1 := hwf_mem) (2 := hwf_log) (4 := harg_len) (input := input); intros hput_valid.
      assert_pre_and_specialize hput_valid; auto.
      assert_pre_and_specialize hput_valid; auto.
      propositional. eapply hpost; eauto.
Qed.
(* Lemma interp_fs_addr_in_region_addr_eq: *)
(*   forall pkg pkg' addr addr' enc_data args args' ext_fns lookup_structs region enc_data', *)
(*   @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args addr = *)
(*     @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' addr' -> *)
(*   (file_struct_defs (pkg_machine pkg))  = (file_struct_defs (pkg_machine pkg')) -> *)
(*   @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args enc_data = *)
(*   @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' enc_data' -> *)
(*   @interp_fancy_spred' ext_fns lookup_structs pkg args *)
(*     (MemSymbDefs.fs_addr_in_region EnclaveParams.enclave_sig region impl_get_field addr enc_data) <-> *)
(*   @interp_fancy_spred' ext_fns lookup_structs pkg' args' *)
(*     (MemSymbDefs.fs_addr_in_region EnclaveParams.enclave_sig region impl_get_field addr' enc_data'). *)
(* Proof. *)
(*   intros * hsv hstructs henc_data. unfold MemSymbDefs.fs_addr_in_region. *)
(*   destruct region. *)
(*   - cbn - [_id _sid _fld mk_sigma_fn _enclave_base enclave_id_to_vect interp_bits2]. *)
(*     repeat rewrite hsv. repeat rewrite hstructs. repeat rewrite henc_data. reflexivity. *)
(*   - cbn - [_id _sid _fld mk_sigma_fn _enclave_base enclave_id_to_vect interp_bits2]. *)
(*     repeat rewrite hsv. repeat rewrite hstructs. repeat rewrite henc_data. reflexivity. *)
(*   - reflexivity. *)
(* Qed. *)


(* Lemma interp_fs_addr_in_range_addr_eq: *)
(*   forall pkg pkg' addr addr' reg_fn reg_fn' enc_data args args' ext_fns lookup_structs, *)
(*   @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args addr = *)
(*     @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' addr' -> *)
(*   @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args (reg_fn enc_data) *)
(*     = @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' (reg_fn' enc_data) -> *)
(*   (file_struct_defs (pkg_machine pkg))  = (file_struct_defs (pkg_machine pkg')) -> *)
(*   @interp_fancy_spred' ext_fns lookup_structs pkg args *)
(*     (MemSymbDefs.fs_addr_in_range EnclaveParams.enclave_sig reg_fn impl_get_field enc_data addr) <-> *)
(*   @interp_fancy_spred' ext_fns lookup_structs pkg' args' *)
(*     (MemSymbDefs.fs_addr_in_range EnclaveParams.enclave_sig reg_fn' impl_get_field enc_data addr'). *)
(* Proof. *)
(*   intros * hsv henc_data hstructs. *)
(*   unfold MemSymbDefs.fs_addr_in_range. *)
(*   cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.fs_addr_in_region] in *. *)
(*   match goal with *)
(*   | |- context[?x ?y ?z (MemSymbDefs.fs_addr_in_region _ _ _ _ _ )]  => *)
(*       replace x with (@interp_fancy_spred' ext_fns lookup_structs) by reflexivity *)
(*   end. *)
(*   repeat rewrite interp_fs_addr_in_region_addr_eq with (1 := hsv) (2 := hstructs) (3 := henc_data). *)
(*   reflexivity. *)
(* Qed. *)

Lemma wf_cache_pair_impl_meta_resp_in_range:
  forall st st' st'' sigma mid_log final_log cache core mem resp,
  wf_cache_pair cache core st (ext_l1_caches mem cache core)  ->
  ext_metadata_resp (ext_pair_meta (ext_l1_caches mem cache core)) = Some resp ->
  interp_fancy_spred (dummy_pkg st st' st'' sigma mid_log final_log)
    (MemSymbDefs.meta_resp_in_range EnclaveParams.enclave_sig resp cache core impl_init impl_get_field).
Proof.
  intros * hwf hresp.
  eapply WF_valid_meta_resp; eauto.
Qed.
Lemma meta_get_valid_implies__resp_is_some:
  forall mem input arg cache core resp,
    WF_ext_mem mem ->
    Datatypes.length arg = _unsafe_struct_sz metadata_input_sig ->
    Datatypes.length resp = _unsafe_struct_sz metadata_output_sig ->
    metadata_get_response__koika arg (ext_pair_meta (ext_l1_caches mem cache core)) = Success resp ->
    unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid metadata_output_sig))
                 (_fld metadata_output_sig "get_valid")
                 (unsafe_call_ext (mk_sigma_fn mem input) (_id (_extid (Memory.Memory.ext_metadata cache core)))
                    arg) = Ob~1 ->
    ext_metadata_resp (ext_pair_meta (ext_l1_caches mem cache core)) = Some
           (unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid metadata_output_sig))
                       (_fld metadata_output_sig "get_response")
                       (unsafe_call_ext (mk_sigma_fn mem input)
                          (_id (_extid (Memory.Memory.ext_metadata cache core))) arg)) .
Proof.
  intros * hwf_mem harg_len hresp_len hresp hvalid.
  rewrite rewrite_call_meta_fn with (1 := hresp) in hvalid.
  rewrite rewrite_call_meta_fn with (1 := hresp).
  consider metadata_get_response__koika. simplify.
  assert (Datatypes.length s1 = 1) as hlen_put_ready.
  { eapply _get_field_success'; eauto.
    all: auto ||  reflexivity.
  }
  destruct s1; [discriminate | ]. destruct s1; [ | discriminate].
  destruct_matches_in_hyp hresp; eauto.
  - bash_destruct hresp; simplify.
    + assert (Datatypes.length v = _unsafe_struct_sz metadata_sig) as hlen_resp.
      { eapply WF_meta_resp with (2 := Heqo); eauto with solve_invariants. }
      pose proof (eta_expand_list_correct false v) as hv. rewrite hlen_resp in hv. cbn - [nth] in hv.
      rewrite hv in hresp. cbn - [nth] in hresp. simplify. auto.
    + cbv in hvalid. discriminate.
  - cbv in hresp. simplify. cbv in hvalid. discriminate.
Qed.

Lemma impl_ext_meta_resp_in_range_implied:
  forall impl_st__koika final_koika_st mid_ext_log ext_log cache core mem mem' input,
  WF_ext_mem mem' ->
  WF_ext_log _ext_fn_tys (ext_log_app ext_log mid_ext_log) ->
  update_memory (get_mem_observations (ext_log_app ext_log mid_ext_log)) mem = Success mem' ->
  wf_cache_pair cache core final_koika_st (ext_l1_caches mem' cache core)  ->
  interp_fancy_spred
    (dummy_pkg final_koika_st impl_st__koika final_koika_st (mk_sigma_fn mem' input) (Some mid_ext_log) ext_log)
    (MemSymbDefs.impl_ext_meta_resp_in_range EnclaveParams.enclave_sig core cache impl_init impl_get_field).
Proof.
  intros * hwf_mem hwf_log hupdate hwf_pair.
  apply ext_mem_update_memory_implies_cache with (cache := cache) (core := core) in hupdate.
  consider cachepair__ext.
  simplify. rename H0 into Hmem'.
  rename Heqr0 into Hcache. rename Heqr1 into Hmeta. rename s into cache'. rename s0 into meta'.
  cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.fs_addr_in_range].
  intros * harg_len hget_valid hget_response.
  match goal with
  | |- context[?x ?y ?z (MemSymbDefs.fs_addr_in_range _ _ _ _ _)]  =>
      replace x with (@interp_fancy_spred' _ext_fn_tys unsafe_lookup_dstruct_fields) by reflexivity;
      set y as _pkg; set z as _args
  end.
  rewrite meta_arg_type in harg_len.
  specialize metadata_get_response__koika__Success with (1 := hwf_mem) (2 := harg_len) (mem_ty := cache) (core := core); intros hresponse. destruct_matches_in_hyp_as hresponse hresp; auto.

  specialize meta_get_valid_implies__resp_is_some with
    (1 := hwf_mem) (2 := harg_len) (3 := hresponse) (4 := hresp) (5 := hget_valid);
    intros meta_resp; propositional.
  specialize wf_cache_pair_impl_meta_resp_in_range with (1 := hwf_pair) (2 := meta_resp).
  intros hfoo.
  specialize (hfoo impl_st__koika final_koika_st (mk_sigma_fn mem' input) (Some mid_ext_log) ext_log).
  cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.meta_resp_in_range] in hfoo.
  consider MemSymbDefs.meta_resp_in_range.
  cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.fs_addr_in_range] in hfoo.
  match type of hfoo with
  | context[?x ?y ?z (MemSymbDefs.fs_addr_in_range _ _ _ _ _)]  =>
      replace x with (@interp_fancy_spred' _ext_fn_tys unsafe_lookup_dstruct_fields) in hfoo by reflexivity
  end.
  propositional.
Qed.

Lemma cache_post_cond_impl_cache_pre_cond:
  forall init_st impl_st__koika final_koika_st mid_ext_log ext_log cache core mem mem' input,
  WF_ext_mem mem' ->
  WF_ext_log _ext_fn_tys (ext_log_app ext_log mid_ext_log) ->
  update_memory (get_mem_observations (ext_log_app ext_log mid_ext_log)) mem = Success mem' ->
  wf_cache_pair cache core init_st (ext_l1_caches mem cache core) ->
  wf_cache_pair cache core final_koika_st (ext_l1_caches mem' cache core) ->
  Forall
    (fun '(_, p) =>
     interp_fancy_spred
       (dummy_pkg init_st impl_st__koika final_koika_st (mk_sigma_fn mem input) (Some mid_ext_log) ext_log) p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core impl_init impl_final impl_get_field impl_committed_ext ) ->
  Forall
    (fun '(_, p) =>
     interp_fancy_spred
       (dummy_pkg final_koika_st impl_st__koika final_koika_st (mk_sigma_fn mem' input) (Some mid_ext_log) ext_log) p)
    (MemSymbDefs.cache_pre_conds' EnclaveParams.enclave_sig cache core impl_init impl_get_field).
Proof.
  intros * hwf hwf_log hupdate hwf_pair hwf_pair' hcache_post.
  (* unfold MemSymbDefs.cache_post in *. *)
  unfold MemSymbDefs.cache_pre_conds'.
  repeat constructor.
  - unfold MemSymbDefs.cache_post in *.
    repeat rewrite Forall_cons_iff in hcache_post. split_ands_in_hyps.
    eapply impl_ext_cache_no_resp_core_implied with (init_st := init_st); eauto.
  - unfold MemSymbDefs.cache_post in *.
    repeat rewrite Forall_cons_iff in hcache_post. split_ands_in_hyps.
    eapply impl_ext_meta_no_resp_core_implied with (init_st := init_st); eauto.
  - eapply impl_ext_meta_resp_in_range_implied; eauto.
  - cbn - [_id _sid _fld mk_sigma_fn].
    eapply mem_cache_put_ready_implied; eauto.
  - cbn - [_id _sid _fld mk_sigma_fn].
    eapply mem_meta_put_ready_implied; eauto.
Qed.
Lemma post_mem_exprs_impl_cache_post_conds:
  forall f reg_init reg_final get_field ext_log,
  Forall f (post_mem_exprs EnclaveParams.enclave_sig reg_init reg_final ext_log get_field) ->
  Forall f (map_fst PfChain.CustomMem (List.concat
              (map (fun '(cache, core) => MemSymbDefs.cache_post EnclaveParams.enclave_sig
                                         cache core reg_init reg_final get_field ext_log)
                 [(imem, CoreId0); (dmem, CoreId0); (imem, CoreId1); (dmem, CoreId1)]))).
Proof.
  intros * hpost. unfold MemSymbDefs.mem_post_conds in *. consider MemSymbDefs.mem_post_conds'.
  consider post_mem_exprs. rewrite Forall_app in hpost. split_ands_in_hyps.
  consider MemSymbDefs.mem_post_conds'_preserve.
  consider @map_fst. repeat rewrite map_app in hpost1.
  repeat rewrite Forall_app in hpost1. split_ands_in_hyps. auto.
Qed.
Lemma wf_cache_pair_implies_cache_zeroed_outside_range:
  forall cache obs cache',
  (forall n : N, (n >= 2 ^ N.of_nat log_nlines)%N -> (ext_cache cache) n = Some (zeroes 32)) ->
   cache__ext obs cache = Success cache' ->
  (forall n : N, (n >= 2 ^ N.of_nat log_nlines)%N -> (ext_cache cache') n = Some (zeroes 32)).
Proof.
  intros * hzero hupdate. consider cache__ext. simplify.
  assert (ext_cache cache' = ext_cache cache \/ update_cache s0 (ext_cache cache) = Success cache') as hcase.
  { bash_destruct hupdate; simplify; auto. }
  destruct hcase as [hcase | hcase]; [rewrite hcase | ]; auto.
  unfold update_cache in hcase. simplify.
  bash_destruct hcase; simplify; auto.
  unfold ext_cache.
  repeat destruct_match; simplify.
  intros * hlen.
  destruct_match; simplify; auto.
  exfalso.
  assert (Datatypes.length s2 = log_nlines) as hlen_addr.
  { repeat unsafe_auto_simplify_structs.
    rewrite _get_field_length_implied with (1 := Heqr0). reflexivity. }
  pose proof (to_N_bounded s2). rewrite hlen_addr in *. lia.
Qed.
Lemma wf_cache_pair_implies_meta_zeroed_outside_range:
  forall meta obs meta',
  (forall n : N, (n >= 2 ^ N.of_nat log_nlines)%N -> (ext_metadata meta) n = Some (zeroes (_unsafe_struct_sz metadata_sig))) ->
   metadata__ext obs meta = Success meta' ->
  (forall n : N, (n >= 2 ^ N.of_nat log_nlines)%N -> (ext_metadata meta') n = Some (zeroes (_unsafe_struct_sz metadata_sig))).
Proof.
  intros * hzero hupdate. consider metadata__ext. simplify.
  assert (ext_metadata meta' = ext_metadata meta \/ update_metadata s0 (ext_metadata meta) = Success meta') as hcase.
  { bash_destruct hupdate; simplify; auto. }
  destruct hcase as [hcase | hcase]; [rewrite hcase | ]; auto.
  unfold update_metadata in hcase. simplify.
  bash_destruct hcase; simplify; auto.
  unfold ext_cache.
  repeat destruct_match; simplify.
  intros * hlen. simpl.
  destruct_match; simplify; auto.
  exfalso.
  assert (Datatypes.length s4 = log_nlines) as hlen_addr.
  { repeat unsafe_auto_simplify_structs.
    rewrite _get_field_length_implied with (1 := Heqr0). reflexivity. }
  pose proof (to_N_bounded s4). rewrite hlen_addr in *. lia.
Qed.
Ltac solve_cache_post_implies name :=
  let hfoo := fresh in
  let hpost := fresh in
  intros * hpost; match goal with
                  | cache: mem_type, core: ind_core_id |- _ =>
                      destruct cache; destruct core
                  end;
    [prop_pose_with_custom hfoo (name imem CoreId0) hpost; auto
    |prop_pose_with_custom hfoo (name imem CoreId1) hpost; auto
    |prop_pose_with_custom hfoo (name dmem CoreId0) hpost; auto
    |prop_pose_with_custom hfoo (name dmem CoreId1) hpost; auto
    ].
Lemma cache_post_implies_post_ext_meta_no_resp_core:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) => interp_fancy_spred pkg  p)
  (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.impl_post_ext_meta_no_resp_core core cache reg_init reg_final get_field final_ext).
Proof.
  solve_cache_post_implies MemMetaNoResp.
Qed.
Lemma cache_post_implies_post_ext_cache_no_resp_core:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) => interp_fancy_spred pkg  p)
  (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.impl_post_ext_cache_no_resp_core core cache reg_init reg_final get_field final_ext).
Proof.
  solve_cache_post_implies MemCacheNoResp.
Qed.

Lemma cache_post_implies_post_invert_Purged:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) => interp_fancy_spred pkg  p)
  (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.cache_post_invert_Purged cache core reg_init reg_final get_field final_ext).
Proof. solve_cache_post_implies (Mem_PostCacheFSM_InvertPurged). Qed.
Lemma cache_post_implies_post_invert_Flushed:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) => interp_fancy_spred pkg  p)
  (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.cache_post_invert_Flushed cache core reg_init reg_final get_field final_ext).
Proof. solve_cache_post_implies (Mem_PostCacheFSM_InvertFlushed). Qed.
Lemma cache_post_implies_post_invert_FlushPrivateData:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) => interp_fancy_spred pkg  p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.cache_post_invert_FlushPrivateData cache core reg_init reg_final get_field final_ext).
Proof. solve_cache_post_implies (Mem_PostCacheFSM_InvertFlushPrivateData). Qed.
Lemma cache_post_implies_post_invert_FlushLineReady:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) => interp_fancy_spred pkg  p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.cache_post_invert_FlushLineReady cache core reg_init reg_final get_field final_ext).
Proof. solve_cache_post_implies (Mem_PostCacheFSM_InvertFlushLineReady). Qed.
Lemma cache_post_implies_post_invert_FlushLineProcess:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) => interp_fancy_spred pkg  p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.cache_post_invert_FlushLineProcess cache core reg_init reg_final get_field final_ext).
Proof. solve_cache_post_implies (Mem_PostCacheFSM_InvertFlushLineProcess). Qed.

Lemma cache_post_implies_postFlushLineProcess:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) => interp_fancy_spred pkg  p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.mem_post_FlushLineProcess cache core reg_init reg_final get_field final_ext).
Proof. solve_cache_post_implies (Mem_post_FlushLineProcess). Qed.

Ltac basic_cbn :=
  cbn - [_id _sid _fld mk_sigma_fn of_N_sz].
(* Lemma case_n_le_max_log_nline: *)
(*   forall n, *)
(*   (n <= to_N Ob~1~1~1~1~1~1~1~1~1)%N -> *)
(*   (n <= to_N Ob~1~1~1~1~1~1~1~1~0)%N \/ n = to_N Ob~1~1~1~1~1~1~1~1~1. *)
(* Proof. *)
(*   intros. *)
(*   apply N.lt_eq_cases in H. split_cases; auto. left. *)
(*   replace (to_N Ob~1~1~1~1~1~1~1~1~0) with (N.pred (to_N Ob~1~1~1~1~1~1~1~1~1)); auto. *)
(*   apply N.lt_le_pred. assumption. *)
(* Qed. *)
(* TODO: MOVE *)
(* Lemma plus_length_r: *)
(*   forall x1 x2 v, *)
(*   plus x1 x2 = Success v -> *)
(*   Datatypes.length v = Datatypes.length x2. *)
(* Proof. *)
(*   consider plus. intros. bash_destruct H. simplify. *)
(*   rewrite firstn_fill_length. auto. *)
(* Qed. *)
(*     Lemma to_N_zeroes {sz} : *)
(*       to_N (zeroes sz) = 0%N. *)
(*     Proof. induction sz; consider zeroes; simpl; try rewrite IHsz; auto. Qed. *)
(* Require Export Coq.NArith.NArith.          (* Coq bug: If this isn't exported, other files can't import Vect.vo *) *)
(* Require Import Coq.ZArith.ZArith. *)
    (* Lemma of_N_double sz n: *)
    (*   of_N_sz (S sz) (N.double n) = cons false (of_N_sz sz n). *)
    (* Proof. destruct n; reflexivity. Qed. *)
    (* Lemma of_N_succ_double sz n: *)
    (*   of_N_sz (S sz) (N.succ_double n) = cons true (of_N_sz sz n). *)
    (* Proof. destruct n; reflexivity. Qed. *)
    (* Lemma to_N_cons hd tl: *)
    (*   to_N (cons hd tl) = ((if hd then 1 else 0) + 2 * to_N tl)%N. *)
    (* Proof. reflexivity. Qed. *)
    (* Lemma N_double_div_2 n : *)
    (*   (N.double n / 2 = n)%N. *)
    (* Proof. *)
    (*   replace (N.double n) with (N.b2n false + 2 * n)%N by reflexivity. *)
    (*   apply N.add_b2n_double_div2. *)
    (* Qed. *)
    (* Lemma N_succ_double_div_2 n : *)
    (*   (N.succ_double n / 2 = n)%N. *)
    (* Proof. *)
    (*   replace (N.succ_double n) with (N.b2n true + 2 * n)%N *)
    (*     by (simpl N.b2n; rewrite N.succ_double_spec; lia). *)
    (*   apply N.add_b2n_double_div2. *)
    (* Qed. *)


    (* Lemma to_N_of_N_mod : *)
    (*   forall n sz, *)
    (*     to_N (of_N_sz sz n) = (n mod 2 ^ N.of_nat sz)%N. *)
    (* Proof. *)
    (*   (* consider of_N_sz. *) *)
    (*   induction n using N.binary_ind. *)
    (*   1: solve [simpl; intros; apply to_N_zeroes]. *)
    (*   all: destruct sz; [ rewrite N.mod_1_r; reflexivity | ]. *)
    (*   all: rewrite ?of_N_double, ?of_N_succ_double, ?to_N_cons, ?IHn. *)
    (*   all: rewrite ?Nat2N.inj_succ, ?N.pow_succ_r'. *)
    (*   all: set (N.of_nat sz) as nz. *)
    (*   all: pose proof N.pow_nonzero 2 nz ltac:(lia). *)
    (*   all: rewrite !N.mod_eq, <- !N.div_div, ?N_double_div_2, ?N_succ_double_div_2 by lia. *)
    (*   all: rewrite ?(N.double_spec n), ?(N.succ_double_spec n). *)
    (*   - lia. *)
    (*   - pose proof N.mul_div_le n (2 ^ nz). *)
    (*     rewrite N.mul_sub_distr_l, N.add_sub_assoc; lia. *)
    (* Qed. *)
Lemma cache_post_implies_post_MemCacheNoResp:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) =>
            interp_fancy_spred pkg  p)
  (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.impl_post_ext_cache_no_resp_core core cache reg_init reg_final get_field final_ext).
Proof. solve_cache_post_implies (MemCacheNoResp). Qed.
(* Lemma length_of_N_sz: *)
(*   forall n v, *)
(*   Datatypes.length (of_N_sz n v) = n. *)
(* Proof. *)
(*   consider of_N_sz. intros. rewrite firstn_fill_length. auto. *)
(* Qed. *)
(* Lemma length_one: *)
(*   forall sz, *)
(*   Datatypes.length (one sz) = sz. *)
(* Proof. *)
(*   unfold one. intros. rewrite firstn_fill_length. reflexivity. *)
(* Qed. *)

Lemma success_or_default_plus_minus_one:
  forall line,
  (0 < line < 2 ^ N.of_nat log_nlines)%N ->
  success_or_default (plus (of_N_sz log_nlines (line - 1)) (@one log_nlines)) Ob = of_N_sz log_nlines line.
Proof.
  intros.
  specialize plus_success with (v1 := of_N_sz log_nlines (line - 1)) (v2 := one log_nlines).
  rewrite length_one. rewrite length_of_N_sz. propositional. rewrite H2. simpl.
  consider plus. simplify. rewrite length_of_N_sz.
  fold (@of_N_sz log_nlines ((to_N (of_N_sz log_nlines (line - 1)) + 1)) ).
  rewrite to_N_of_N_mod.
  rewrite N.mod_small by lia. replace (line - 1 + 1)%N with line by lia. reflexivity.
Qed.
Lemma update_cache_byte_en:
  forall cache cache' req,
  update_cache req cache = Success cache' ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid cache_req_sig))
                    (_fld cache_req_sig "byte_en") req = Ob~0~0~0~0 ->
  cache = ext_cache cache'.
Proof.
  intros. consider update_cache. simplify.
  convert_get_field_in Heqr2. setoid_rewrite H0 in Heqr2. subst. simpl in H. simplify; auto.
Qed.
(* Lemma to_N_inj : *)
(*   forall sz bs1 bs2, *)
(*     sz = Datatypes.length bs1 -> *)
(*     sz = Datatypes.length bs2 -> *)
(*     to_N bs1 = to_N bs2 -> *)
(*     bs1 = bs2. *)
(* Proof. *)
(*   induction sz; destruct bs1, bs2; simpl; subst; intros; try lia. *)
(*   - reflexivity. *)
(*   - destruct b, b0, (to_N bs1) eqn:?, (to_N bs2) eqn:?; cbn in *; *)
(*       discriminate || (rewrite (IHsz bs1 bs2) by congruence; reflexivity). *)
(* Qed. *)


(* Lemma exists_of_N_sz: *)
(*   forall v, *)
(*   (to_N v < 2 ^ N.of_nat (Datatypes.length v))%N -> *)
(*   v = of_N_sz (Datatypes.length v) (to_N v). *)
(* Proof. *)
(*   intros.  eapply to_N_inj; eauto; try rewrite length_of_N_sz; [reflexivity | ]. *)
(*   rewrite to_N_of_N_mod. rewrite N.mod_small;auto. *)
(* Qed. *)

(*  Lemma success_or_default_plus: *)
(*   forall x x' y, *)
(*   Datatypes.length x = Datatypes.length y -> *)
(*   Datatypes.length x' = Datatypes.length y -> *)
(*   success_or_default (plus x y) Ob = success_or_default (plus x' y) Ob -> *)
(*   x = x'. *)
(* Proof. *)
(*   intros * hlen_x hlen_x' hplus. *)
(*   specialize plus_success with (v1 := x) (v2 := y). propositional. rewrite H0 in *. *)
(*   specialize plus_success with (v1 := x') (v2 := y). propositional. rewrite H1 in *.  simpl in hplus. subst. *)
(*   consider plus. simplify. *)
(*   fold (of_N_sz (Datatypes.length x) (to_N x + to_N y)) in H1. *)
(*   fold (of_N_sz (Datatypes.length x') (to_N x' + to_N y)) in H1. *)
(*   apply f_equal with (f := to_N) in H1. *)
(*   repeat rewrite to_N_of_N_mod in H1. *)
(*   rewrite (exists_of_N_sz x) in H1. *)
(*   rewrite (exists_of_N_sz x') in H1. *)
(*   rewrite (exists_of_N_sz y) in H1. *)
(*   all: try eapply to_N_bounded. *)
(*   repeat rewrite to_N_of_N_mod in H1. *)
(*   repeat rewrite length_of_N_sz in H1. *)
(*   rewrite hlen_x in *. rewrite hlen_x' in *. set (N.of_nat (Datatypes.length y)) in *. *)
(*   assert (((to_N x mod 2 ^ n + to_N y mod 2 ^ n + ((2 ^ n - to_N y) mod 2 ^ n)) mod 2 ^ n)%N *)
(*           = (((to_N x' mod 2 ^ n + to_N y mod 2 ^ n+ ((2 ^ n - to_N y) mod 2 ^ n))) mod 2 ^ n)%N). *)
(*   { rewrite<-N.Div0.add_mod_idemp_l. rewrite H1. *)
(*     rewrite N.Div0.add_mod_idemp_l.  reflexivity. *)
(*   } *)
(*   assert (to_N y < 2^n)%N by (eapply to_N_bounded). *)
(*   rewrite<-N.add_assoc in H. *)
(*   rewrite<-N.add_assoc in H. *)
(*   rewrite<-N.Div0.add_mod_idemp_r in H. *)
(*   rewrite<-N.Div0.add_mod_idemp_r with (a :=  (to_N x' mod 2^n)%N) in H. *)
(*   replace (((to_N y mod 2 ^ n + (2 ^ n - to_N y) mod 2 ^ n) mod 2^ n)%N) with (0 mod 2 ^ n)%N in H. *)
(*   { repeat rewrite N.Div0.mod_0_l in *. repeat rewrite N.add_0_r in *. *)
(*     rewrite N.mod_mod in H by lia. *)
(*     rewrite N.mod_mod in H by lia. *)
(*     rewrite N.mod_small in H. *)
(*     2: { unfold n. rewrite<-hlen_x. eapply to_N_bounded. } *)
(*     rewrite N.mod_small in H. *)
(*     2: { unfold n. rewrite<-hlen_x'. eapply to_N_bounded. } *)
(*     eapply to_N_inj; eauto. rewrite_solve. *)
(*   } *)
(*   { rewrite N.Div0.mod_0_l. *)
(*     rewrite N.Div0.add_mod_idemp_l. *)
(*     rewrite N.Div0.add_mod_idemp_r. *)
(*     rewrite N.add_sub_assoc by lia. *)
(*     rewrite N.add_comm. rewrite<-N.add_sub_assoc by lia. *)
(*     rewrite N.sub_diag. rewrite N.add_0_r. *)
(*     rewrite N.Div0.mod_same. reflexivity. *)
(*   } *)
(* Qed. *)
(* Lemma of_N_sz_eq: *)
(*   forall sz v x, *)
(*   (v < 2 ^ N.of_nat sz)%N -> *)
(*   of_N_sz sz v = x -> *)
(*   v = to_N x. *)
(* Proof. *)
(*   intros. subst. rewrite to_N_of_N_mod. *)
(*   rewrite N.mod_small;auto. *)
(* Qed. *)
(* Lemma to_N_of_N_sz_idem: *)
(*   forall sz v, *)
(*   (v < 2 ^ (N.of_nat sz))%N -> *)
(*   to_N (of_N_sz sz v) = v. *)
(* Proof. *)
(*   intros. rewrite to_N_of_N_mod. *)
(*   rewrite N.mod_small; auto. *)
(* Qed. *)

Lemma wf_cache_pair_implies_cache_flush_correct:
  forall st st' cache core ext_log mid_ext_log cache' mid_st mem input,
  WF_state _reg_types st ->
  cache_flush_line cache core st (ext_pair_cache (ext_l1_caches mem cache core))  ->
  cache__ext (obs_cache (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core)
           (ext_pair_cache (ext_l1_caches mem cache core)) = Success cache' ->
  Forall
    (fun '(_, p) =>
     interp_fancy_spred
       (dummy_pkg st mid_st st' (mk_sigma_fn mem input) (Some mid_ext_log) ext_log) p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core impl_init impl_final impl_get_field impl_committed_ext ) ->
  cache_flush_line cache core st' cache'.
Proof.
  intros * hwf_st hzeroed hupdate hpost. consider cache__ext.
  destruct_matches_in_hyp_as hupdate hput_valid; [ | discriminate]. rename s into put_valid.
  destruct_matches_in_hyp_as hupdate hput_req; [ | discriminate]. rename s into put_request.
  destruct_matches_in_hyp_as hupdate hget_rdy; [ | discriminate]. rename s into get_ready.
  pose proof (_get_field_length_implied _ _ _ _ hput_valid) as hlen_obs.
  assert (Datatypes.length get_ready = 1) as hlen_get_ready.
  { bash_destruct hupdate; auto. }
  assert (Datatypes.length put_valid= 1) as hlen_put_valid.
  { bash_destruct hupdate; auto. }

  consider cache_flush_line. intros * hlen_lines hflush hflush_line hn.
  consider dummy_interp_spred_at_st.
  specialize (hflush mid_st st' (mk_sigma_fn mem input) (Some mid_ext_log) ext_log).
  specialize (hflush_line mid_st st' (mk_sigma_fn mem input) (Some mid_ext_log) ext_log).
  cbn - [_id _sid _fld mk_sigma_fn _enum] in hflush.
  cbn - [_id _sid _fld mk_sigma_fn _enum of_N_sz] in hflush_line.

  destruct hflush as [hpurged | hflushing].
  { propositional.
    destruct hpurged as [hPurged | [hFlushed | hFlushPrivateData ] ].
    - specialize cache_post_implies_post_invert_Purged with (1 := hpost); intros hpost_purged.
      basic_cbn_in hpost_purged.
      propositional.
      (* If purged, then
         (st = Purged \/ cache = Flushed ) /\
         put_valid = False, so cache is unchanged
       *)
      assert (put_valid = Ob~0); subst.
      { convert_get_field_in hput_valid. setoid_rewrite hput_valid in hpost_purged2. auto. }
      assert (ext_cache cache' = ext_cache (ext_pair_cache (ext_l1_caches mem cache core))) as hcache_eq.
      { bash_destruct hupdate; simplify; auto. }
      rewrite hcache_eq.
      eapply hzeroed with (1 := hlen_lines); eauto.
      + basic_cbn. intros. left. destruct hpost_purged0; propositional.
      + basic_cbn. intros. split; [auto | ].
        intros hst. exfalso. propositional.
        destruct hpost_purged0 as [hcase0 | hcase1].
        { propositional. rewrite hcase2 in hst0. clear - hst0. split_cases. }
        { setoid_rewrite hcase1 in hst0. destruct hst0; discriminate. }
    - specialize cache_post_implies_post_invert_Flushed with (1 := hpost); intros hpost_flushed.
      basic_cbn_in hpost_flushed.
      (* If st' flushed, then st = Flushed \/ st = FlushPrivateData *)
      (* same as above *)
      assert (put_valid = Ob~0); subst.
      { propositional. convert_get_field_in hput_valid. setoid_rewrite hput_valid in hpost_flushed1. auto.  }
      assert (ext_cache cache' = ext_cache (ext_pair_cache (ext_l1_caches mem cache core))) as hcache_eq.
      { bash_destruct hupdate; simplify; auto. }
      rewrite hcache_eq.
      eapply hzeroed with (1 := hlen_lines); eauto.
      + basic_cbn. intros. left. propositional.
      + basic_cbn. intros. split; [auto | ].
        intros hst. exfalso.
        propositional. destruct hst0 as [hcase0 | hcase1].
        { rewrite hcase0 in hpost_flushed2. cbv in hpost_flushed2.
          clear - hpost_flushed2; destruct hpost_flushed2; discriminate.
        }
        { rewrite hcase1 in hpost_flushed2. cbv in hpost_flushed2.
          clear - hpost_flushed2; destruct hpost_flushed2; discriminate.
        }
    - (* st' = FlushPrivateData *)
      (* If st' = FlushPrivateData,
         then st = FlushPrivateData
          \/ (st = FlushLineProcess and line = ones
              /\ put zero to metadata at line ones
              /\ put zero to cache  at line ones
              /\ get_ready = Ob~1 *)
      specialize cache_post_implies_post_invert_FlushPrivateData with (1 := hpost). intros hflush.
      basic_cbn_in hflush. propositional.
      destruct hflush1 as [hcase0 | hcase1].
      + propositional.
        assert (put_valid = Ob~0); subst.
        { convert_get_field_in hput_valid.
          setoid_rewrite hcase0 in hput_valid. auto.
        }
        assert (ext_cache cache' = ext_cache (ext_pair_cache (ext_l1_caches mem cache core))) as hcache'.
        { bash_destruct hupdate; simplify; auto. }
        rewrite hcache'.
        eapply hzeroed; eauto.
        { intros. basic_cbn. auto. }
        { intros. basic_cbn. split; auto.
          rewrite hcase1. clear. intros hflush. propositional. clear - hflush0. split_cases. }
      + propositional.
        specialize cache_post_implies_postFlushLineProcess with (1 := hpost); intros hpost_flush.
        basic_cbn_in hpost_flush. propositional.
        assert_pre_and_specialize hpost_flush.
        { rewrite hFlushPrivateData. rewrite hcase0. discriminate. }
        destruct hpost_flush as (flush_line & meta_put_valid & meta_write & meta_data & meta_addr & meta_get_ready & cache_put_valid & cache_load & cache_data & cache_get_ready & cache_line).
        assert (update_cache put_request (ext_cache (ext_pair_cache (ext_l1_caches mem cache core))) = Success cache') as hupdate'.
        { repeat convert_get_field.
          setoid_rewrite hget_rdy in cache_get_ready.
          setoid_rewrite hput_valid in cache_put_valid. subst. auto.
        }
        unfold update_cache in hupdate'.
        destruct_matches_in_hyp_as hupdate' haddr; [ | discriminate].
        destruct_matches_in_hyp_as hupdate' hdata; [ | discriminate].
        destruct_matches_in_hyp_as hupdate' hbyte_en; [ | discriminate].
        repeat convert_get_field. unfold dstruct_fields in *. setoid_rewrite hput_req in cache_load.
        setoid_rewrite cache_load in hbyte_en. rewrite<-hbyte_en in hupdate'.
        simpl in hupdate'. apply Success_inj in hupdate'. subst. unfold ext_cache.
        destruct_match.
        { setoid_rewrite cache_data.
          rewrite compute_with_byte_en_store. reflexivity.
        }
        { destruct_match; auto. setoid_rewrite cache_line in Heqb.
          (* specialize case_n_le_max_log_nline with (1 := hn); intros hn'. *)
          rewrite hcase2 in Heqb. simplify.
          assert ((n <= line-1)%N \/ n = line)%N as hn' by lia.
          destruct hn'; subst.
          2: { rewrite<-hflush_line0 in Heqb.
               rewrite to_N_of_N_mod in Heqb.
               rewrite N.mod_small in Heqb by auto. congruence.
             }
          eapply hzeroed with (4 := H).
          { lia. }
          { intros. basic_cbn.  right. split; auto. rewrite_solve. }
          { intros. basic_cbn.
            split.
            - rewrite hcase0.
              intros * hcase. destruct hcase as [case__purge | [case1 | case2] ]; [ | discriminate | discriminate].
              clear - hflush0 case__purge. congruence.
            - intros (foo & bar). rewrite hcase2.
              rewrite<-hflush_line0.
              apply success_or_default_plus_minus_one.
              split; auto. destruct line; [| lia].
              clear - hflush_line0. discriminate.
          }
        }
  }
  { propositional.
    destruct hflushing0 as [hFlushLineReady | hFlushLineProcess ].
    - specialize cache_post_implies_post_invert_FlushLineReady with (1 := hpost). intros hflush.
      basic_cbn_in hflush.
      propositional.

        (* st' = FlushLineReady ->
           (st = FlushLineReady /\ st'.line = st.line
            /\ (put_valid = true -> byte_en = Ob~0~0~0~0/is_write = false ) \/
           (st = FlushLineProcess /\
            (put_valid = true /\ write zeroes to cache and metadata) /\
             fromCache/fromMeta valid = Ob~1 (so no resp blocking) /\
             st'.line = st.line + 1
            ) \/
           (st = Ready /\ st'.line = zero /\ put_valid = Ob~0
           *)

      destruct hflush1 as [hflushReady |[hflushProcess | hflushReady] ].
      { propositional.
        assert (put_valid = Ob~0); subst.
        { repeat convert_get_field. setoid_rewrite hput_valid in hflushReady1. auto. }
        { assert (ext_cache cache' = ext_cache (ext_pair_cache (ext_l1_caches mem cache core))) as hcache'.
          { bash_destruct hupdate; simplify; auto. }
          rewrite hcache'.
          eapply hzeroed; eauto.
          { intros *. basic_cbn. right. split; auto. rewrite_solve. }
          { intros *. basic_cbn. split.
            - rewrite hflushReady0. intros * h. clear - hflush0 h. split_cases.
            - intros. rewrite_solve.
          }
        }
      }
      { propositional.
        specialize cache_post_implies_postFlushLineProcess with (1 := hpost); intros hpost_flush.
        basic_cbn_in hpost_flush. propositional.
        assert_pre_and_specialize hpost_flush.
        { rewrite hFlushLineReady. rewrite hflushProcess. discriminate. }
        destruct hpost_flush as (flush_line & meta_put_valid & meta_write & meta_data & meta_addr & meta_get_ready & cache_put_valid & cache_load & cache_data & cache_get_ready & cache_line).
        assert (update_cache put_request (ext_cache (ext_pair_cache (ext_l1_caches mem cache core))) = Success cache') as hupdate'.
        { repeat convert_get_field.
          setoid_rewrite hget_rdy in cache_get_ready.
          setoid_rewrite hput_valid in cache_put_valid. subst. auto.
        }
        unfold update_cache in hupdate'.
        destruct_matches_in_hyp_as hupdate' haddr; [ | discriminate].
        destruct_matches_in_hyp_as hupdate' hdata; [ | discriminate].
        destruct_matches_in_hyp_as hupdate' hbyte_en; [ | discriminate].
        repeat convert_get_field. unfold dstruct_fields in *. setoid_rewrite hput_req in cache_load.
        setoid_rewrite cache_load in hbyte_en. rewrite<-hbyte_en in hupdate'.
        setoid_rewrite cache_put_valid in hput_valid.
        setoid_rewrite cache_get_ready in hget_rdy.
        simpl in hupdate'. apply Success_inj in hupdate'. subst. unfold ext_cache.
        setoid_rewrite cache_line.
        destruct_match.
        { setoid_rewrite cache_data.
          rewrite compute_with_byte_en_store. reflexivity.
        }
        { destruct_match; auto.
          (* setoid_rewrite cache_line in Heqb. *)
          assert ((n <= line - 1)%N \/ n = line) as hcase by lia.
          move flush_line at bottom. move hflush_line1 at bottom.
          rewrite flush_line in hflush_line1. simplify.
          apply success_or_default_plus in hflush_line1; auto.
          2: rewrite length_of_N_sz; auto.
          2: { erewrite WF_state_length' with (1 := hwf_st); eauto.
               clear. destruct cache; destruct core; reflexivity.
             }
          destruct hcase; subst.
          2: { rewrite<-hflush_line1 in Heqb.
               rewrite to_N_of_N_sz_idem in Heqb by auto. clear - Heqb. congruence.
             }
          eapply hzeroed with (4 := H).
          { lia. }
          { intros. basic_cbn.  right. split; auto. unfold not; intros hflush. rewrite hflush in flush_line.
            simplify. rewrite hflush in Heqb. simpl in Heqb.
            assert (line = 0%N); subst.
            { rewrite hflush in hflush_line1. apply of_N_sz_eq in hflush_line1; assumption. }
            lia.
          }
          { intros. basic_cbn. split; auto.
            - rewrite hflushProcess.
              intros * hcase. destruct hcase as [case__purge | [case1 | case2] ]; [ | discriminate | discriminate].
              clear - hflush0 case__purge. congruence.
            - intros.
              rewrite success_or_default_plus_minus_one; auto.
              split; try lia. rewrite<-hflush_line1 in Heqb.
              destruct line; [ | lia].
              rewrite to_N_of_N_sz_idem in Heqb by auto. lia.
          }
        }
      }
      { propositional. }
    - (* st' = FlushLineProcess ->
         (st = FlushLineProcess /\  st'.line = st.line /\ put_valid = false) \/
         (st = FlushLineReady /\ st'.line = st.line  /\
          (put_valid = true -> byte_en = zeroes/is_write = false
       *)
      specialize cache_post_implies_post_invert_FlushLineProcess with (1 := hpost); intros hpost'.
      basic_cbn_in hpost'. propositional.

      assert (ext_cache cache' = ext_cache (ext_pair_cache (ext_l1_caches mem cache core))) as hcache_eq.
      { destruct hpost'1 as [hcase0 | hcase1].
        - propositional.
          convert_get_field_in hput_valid. setoid_rewrite hput_valid in hcase2. subst.
          bash_destruct hupdate; simplify; auto.
        - destruct hcase1 as (hcase_fsm & hcase_line & hcase_byte_en & hcase_is_write & hcase_cache_get_rdy & hcase_meta_get_rdy).
          apply case_singleton_bv in hlen_put_valid.
          destruct hlen_put_valid; subst.
          + convert_get_field_in hget_rdy. setoid_rewrite hget_rdy in hcase_cache_get_rdy. subst.
            eapply update_cache_byte_en in hupdate; auto.
            convert_get_field_in hput_req. subst. setoid_rewrite hcase_byte_en. reflexivity.
          + bash_destruct hupdate. simplify. auto.
      }
      rewrite hcache_eq.
      eapply hzeroed with (1 := hlen_lines); eauto.
      + basic_cbn.
        intros. right. propositional.
        destruct hpost'1 as [hcase0 | hcase1].
        { split_ands_in_hyps. split; auto. rewrite_solve. }
        { split_ands_in_hyps. split; auto. rewrite_solve. }
      + basic_cbn. intros. split.
        * intros hst. exfalso.
          destruct hpost'1 as [hcase0 | hcase1].
          { split_ands_in_hyps. rewrite hcase1 in hst. clear - hpost'0 hst. split_cases.
          }
          { split_ands_in_hyps. rewrite hcase0 in hst. clear - hpost'0 hst. split_cases.
          }
        * intros hst.
          destruct hpost'1 as [hcase0 | hcase1]; split_ands_in_hyps; rewrite_solve.
      }
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

Lemma update_metadata_load:
  forall meta meta' req,
  update_metadata req meta = Success meta' ->
  unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid metadata_req_sig))
                    (_fld metadata_req_sig "is_write") req = Ob~0 ->
  meta= ext_metadata meta'.
Proof.
  intros. consider update_metadata. simplify.
  convert_get_field_in Heqr0. setoid_rewrite H0 in Heqr0. subst. simpl in H. simplify; auto.
Qed.


Lemma wf_cache_pair_implies_meta_flush_correct:
  forall st st' cache core ext_log mid_ext_log meta' mid_st mem input,
  WF_state _reg_types st ->
  meta_flush_line cache core st (ext_pair_meta (ext_l1_caches mem cache core))  ->
  metadata__ext (obs_meta (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core)
           (ext_pair_meta (ext_l1_caches mem cache core)) = Success meta' ->
  Forall
    (fun '(_, p) =>
     interp_fancy_spred
       (dummy_pkg st mid_st st' (mk_sigma_fn mem input) (Some mid_ext_log) ext_log) p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core impl_init impl_final impl_get_field impl_committed_ext ) ->
  meta_flush_line cache core st' meta'.
Proof.
  intros * wf_st hzeroed hupdate hpost.
  simplify_metadata_and_cache__ext hupdate.
  unfold meta_flush_line in *. intros * hlen_lines hflush hflush_line hn. consider dummy_interp_spred_at_st.
  specialize (hflush mid_st st' (mk_sigma_fn mem input) (Some mid_ext_log) ext_log).
  specialize (hflush_line mid_st st' (mk_sigma_fn mem input) (Some mid_ext_log) ext_log).
  basic_cbn_in hflush. basic_cbn_in hflush_line.

  destruct hflush as [hpurged | hflushing].
  { propositional. destruct hpurged as [hPurged | [hFlushed | hFlushPrivateData ] ].
    - specialize cache_post_implies_post_invert_Purged with (1 := hpost); intros hpost_purged.
      basic_cbn_in hpost_purged. propositional.
      (* If purged, then
         (st = Purged \/ cache = Flushed ) /\
         put_valid = False, so cache is unchanged
       *)
      assert (put_valid = Ob~0); subst.
      { convert_get_field_in hput_valid. setoid_rewrite hput_valid in hpost_purged3. auto. }
      assert (ext_metadata meta' = ext_metadata (ext_pair_meta (ext_l1_caches mem cache core))) as hmeta_eq.
      { bash_destruct hupdate; simplify; auto. }
      rewrite hmeta_eq.
      eapply hzeroed with (1 := hlen_lines); eauto.
      + basic_cbn. intros. left. destruct hpost_purged0; propositional.
      + basic_cbn. intros. split; [auto | ].
        intros hst. exfalso. propositional.
        destruct hpost_purged0 as [hcase0 | hcase1].
        { propositional. rewrite hcase2 in hst0. clear - hst0. split_cases. }
        { setoid_rewrite hcase1 in hst0. destruct hst0; discriminate. }
    - specialize cache_post_implies_post_invert_Flushed with (1 := hpost); intros hpost_flushed.
      basic_cbn_in hpost_flushed.
      (* If st' flushed, then st = Flushed \/ st = FlushPrivateData *)
      (* same as above *)
      assert (put_valid = Ob~0); subst.
      { propositional. convert_get_field_in hput_valid. setoid_rewrite hput_valid in hpost_flushed4. auto.  }
      assert (ext_metadata meta' = ext_metadata (ext_pair_meta (ext_l1_caches mem cache core))) as hmeta_eq.
      { bash_destruct hupdate; simplify; auto. }
      rewrite hmeta_eq.
      eapply hzeroed with (1 := hlen_lines); eauto.
      + basic_cbn. intros. left. propositional.
      + basic_cbn. intros. split; [auto | ].
        intros hst. exfalso.
        propositional. destruct hst0 as [hcase0 | hcase1].
        { rewrite hcase0 in hpost_flushed2. cbv in hpost_flushed2.
          clear - hpost_flushed2; destruct hpost_flushed2; discriminate.
        }
        { rewrite hcase1 in hpost_flushed2. cbv in hpost_flushed2.
          clear - hpost_flushed2; destruct hpost_flushed2; discriminate.
        }
    - (* st' = FlushPrivateData *)
      (* If st' = FlushPrivateData,
         then st = FlushPrivateData
          \/ (st = FlushLineProcess and line = ones
              /\ put zero to metadata at line ones
              /\ put zero to cache  at line ones
              /\ get_ready = Ob~1 *)
      specialize cache_post_implies_post_invert_FlushPrivateData with (1 := hpost). intros hflush.
      basic_cbn_in hflush. propositional.
      destruct hflush1 as [hcase0 | hcase1].
      + propositional.
        assert (put_valid = Ob~0); subst.
        { convert_get_field_in hput_valid.
          setoid_rewrite hcase3 in hput_valid. auto.
        }
        assert (ext_metadata meta' = ext_metadata (ext_pair_meta (ext_l1_caches mem cache core))) as hmeta'.
        { bash_destruct hupdate; simplify; auto. }
        rewrite hmeta'.
        eapply hzeroed; eauto.
        { intros. basic_cbn. auto. }
        { intros. basic_cbn. split; auto.
          rewrite hcase1. clear. intros hflush. propositional. clear - hflush0. split_cases. }
      + propositional.
        specialize cache_post_implies_postFlushLineProcess with (1 := hpost); intros hpost_flush.
        basic_cbn_in hpost_flush. propositional.
        assert_pre_and_specialize hpost_flush.
        { rewrite hFlushPrivateData. rewrite hcase0. discriminate. }
        destruct hpost_flush as (flush_line & meta_put_valid & meta_write & meta_data & meta_addr & meta_get_ready & cache_put_valid & cache_load & cache_data & cache_get_ready & cache_line).
        assert (update_metadata put_request (ext_metadata (ext_pair_meta (ext_l1_caches mem cache core))) = Success meta') as hupdate'.
        { repeat convert_get_field.
          setoid_rewrite hget_rdy in meta_get_ready.
          setoid_rewrite hput_valid in meta_put_valid. subst. auto.
        }
        unfold update_metadata in hupdate'.
        destruct_matches_in_hyp_as hupdate' his_write ; [ | discriminate].
        destruct_matches_in_hyp_as hupdate' hdata; [ | discriminate].
        destruct_matches_in_hyp_as hupdate' haddr; [ | discriminate].
        repeat convert_get_field. unfold dstruct_fields in *. setoid_rewrite hput_req in meta_write.
        setoid_rewrite meta_write in his_write. rewrite<-his_write in hupdate'.
        simpl in hupdate'. apply Success_inj in hupdate'. subst. unfold ext_metadata.
        destruct_match.
        { setoid_rewrite meta_data. reflexivity.
        }
        { destruct_match; auto. setoid_rewrite meta_addr in Heqb.
          (* specialize case_n_le_max_log_nline with (1 := hn); intros hn'. *)
          rewrite hcase2 in Heqb. simplify.
          assert ((n <= line-1)%N \/ n = line)%N as hn' by lia.
          destruct hn'; subst.
          2: { rewrite<-hflush_line0 in Heqb.
               rewrite to_N_of_N_mod in Heqb.
               rewrite N.mod_small in Heqb by auto. congruence.
             }
          eapply hzeroed with (4 := H).
          { lia. }
          { intros. basic_cbn.  right. split; auto. rewrite_solve. }
          { intros. basic_cbn.
            split.
            - rewrite hcase0.
              intros * hcase. destruct hcase as [case__purge | [case1 | case2] ]; [ | discriminate | discriminate].
              clear - hflush0 case__purge. congruence.
            - intros (foo & bar). rewrite hcase2.
              rewrite<-hflush_line0.
              apply success_or_default_plus_minus_one.
              split; auto. destruct line; [| lia].
              clear - hflush_line0. discriminate.
          }
        }
  }
  { propositional.
    destruct hflushing0 as [hFlushLineReady | hFlushLineProcess ].
    - specialize cache_post_implies_post_invert_FlushLineReady with (1 := hpost). intros hflush.
      basic_cbn_in hflush. propositional.

        (* st' = FlushLineReady ->
           (st = FlushLineReady /\ st'.line = st.line
            /\ (put_valid = true -> byte_en = Ob~0~0~0~0/is_write = false ) \/
           (st = FlushLineProcess /\
            (put_valid = true /\ write zeroes to cache and metadata) /\
             fromCache/fromMeta valid = Ob~1 (so no resp blocking) /\
             st'.line = st.line + 1
            ) \/
           (st = Ready /\ st'.line = zero /\ put_valid = Ob~0
           *)

      destruct hflush1 as [hflushReady |[hflushProcess | hflushReady] ].
      { propositional.
        assert (put_valid = Ob~0); subst.
        { repeat convert_get_field. setoid_rewrite hput_valid in hflushReady4. auto. }
        { assert (ext_metadata meta' = ext_metadata (ext_pair_meta (ext_l1_caches mem cache core))) as hmeta'.
          { bash_destruct hupdate; simplify; auto. }
          rewrite hmeta'.
          eapply hzeroed; eauto.
          { intros *. basic_cbn. right. split; auto. rewrite_solve. }
          { intros *. basic_cbn. split.
            - rewrite hflushReady0. intros * h. clear - hflush0 h. split_cases.
            - intros. rewrite_solve.
          }
        }
      }
      { propositional.
        specialize cache_post_implies_postFlushLineProcess with (1 := hpost); intros hpost_flush.
        basic_cbn_in hpost_flush. propositional.
        assert_pre_and_specialize hpost_flush.
        { rewrite hFlushLineReady. rewrite hflushProcess. discriminate. }
        destruct hpost_flush as (flush_line & meta_put_valid & meta_write & meta_data & meta_addr & meta_get_ready & cache_put_valid & cache_load & cache_data & cache_get_ready & cache_line).
        assert (update_metadata put_request (ext_metadata (ext_pair_meta (ext_l1_caches mem cache core))) = Success meta') as hupdate'.
        { repeat convert_get_field.
          setoid_rewrite hget_rdy in meta_get_ready.
          setoid_rewrite hput_valid in meta_put_valid. subst. auto.
        }
        unfold update_metadata in hupdate'.
        destruct_matches_in_hyp_as hupdate' his_write ; [ | discriminate].
        destruct_matches_in_hyp_as hupdate' hdata; [ | discriminate].
        destruct_matches_in_hyp_as hupdate' haddr; [ | discriminate].
        repeat convert_get_field. unfold dstruct_fields in *. setoid_rewrite hput_req in meta_write.
        setoid_rewrite meta_write in his_write. rewrite<-his_write in hupdate'.
        setoid_rewrite meta_put_valid in hput_valid.
        setoid_rewrite meta_get_ready in hget_rdy.
        simpl in hupdate'. apply Success_inj in hupdate'. subst. unfold ext_metadata.
        setoid_rewrite meta_addr.
        destruct_match.
        { setoid_rewrite meta_data. reflexivity. }
        { destruct_match; auto.
          (* setoid_rewrite cache_line in Heqb. *)
          assert ((n <= line - 1)%N \/ n = line) as hcase by lia.
          move flush_line at bottom. move hflush_line1 at bottom.
          rewrite flush_line in hflush_line1. simplify.
          apply success_or_default_plus in hflush_line1; auto.
          2: rewrite length_of_N_sz; auto.
          2: { erewrite WF_state_length' with (1 := wf_st); eauto.
               clear. destruct cache; destruct core; reflexivity.
             }
          destruct hcase; subst.
          2: { rewrite<-hflush_line1 in Heqb.
               rewrite to_N_of_N_sz_idem in Heqb by auto. clear - Heqb. congruence.
             }
          eapply hzeroed with (4 := H).
          { lia. }
          { intros. basic_cbn.  right. split; auto. unfold not; intros hflush. rewrite hflush in flush_line.
            simplify. rewrite hflush in Heqb. simpl in Heqb.
            assert (line = 0%N); subst.
            { rewrite hflush in hflush_line1. apply of_N_sz_eq in hflush_line1; assumption. }
            lia.
          }
          { intros. basic_cbn. split; auto.
            - rewrite hflushProcess.
              intros * hcase. destruct hcase as [case__purge | [case1 | case2] ]; [ | discriminate | discriminate].
              clear - hflush0 case__purge. congruence.
            - intros.
              rewrite success_or_default_plus_minus_one; auto.
              split; try lia. rewrite<-hflush_line1 in Heqb.
              destruct line; [ | lia].
              rewrite to_N_of_N_sz_idem in Heqb by auto. lia.
          }
        }
      }
      { propositional. }
    - (* st' = FlushLineProcess ->
         (st = FlushLineProcess /\  st'.line = st.line /\ put_valid = false) \/
         (st = FlushLineReady /\ st'.line = st.line  /\
          (put_valid = true -> byte_en = zeroes/is_write = false
       *)
      specialize cache_post_implies_post_invert_FlushLineProcess with (1 := hpost); intros hpost'.
      basic_cbn_in hpost'. propositional.

      assert (ext_metadata meta' = ext_metadata (ext_pair_meta (ext_l1_caches mem cache core))) as hcache_eq.
      { destruct hpost'1 as [hcase0 | hcase1].
        - propositional.
          convert_get_field_in hput_valid. setoid_rewrite hput_valid in hcase4. subst.
          bash_destruct hupdate; simplify; auto.
        - destruct hcase1 as (hcase_fsm & hcase_line & hcase_byte_en & hcase_is_write & hcase_cache_get_rdy & hcase_meta_get_rdy).
          apply case_singleton_bv in hlen_put_valid.
          destruct hlen_put_valid; subst.
          + convert_get_field_in hget_rdy. setoid_rewrite hget_rdy in hcase_meta_get_rdy. subst.
            eapply update_metadata_load in hupdate; auto.
            convert_get_field_in hput_req. subst. setoid_rewrite hcase_is_write. reflexivity.
          + bash_destruct hupdate. simplify. auto.
      }
      rewrite hcache_eq.
      eapply hzeroed with (1 := hlen_lines); eauto.
      + basic_cbn.
        intros. right. propositional.
        destruct hpost'1 as [hcase0 | hcase1].
        { split_ands_in_hyps. split; auto. rewrite_solve. }
        { split_ands_in_hyps. split; auto. rewrite_solve. }
      + basic_cbn. intros. split.
        * intros hst. exfalso.
          destruct hpost'1 as [hcase0 | hcase1].
          { split_ands_in_hyps. rewrite hcase1 in hst. clear - hpost'0 hst. split_cases.
          }
          { split_ands_in_hyps. rewrite hcase0 in hst. clear - hpost'0 hst. split_cases.
          }
        * intros hst.
          destruct hpost'1 as [hcase0 | hcase1]; split_ands_in_hyps; rewrite_solve.
      }
Qed.
Lemma cache_post_implies_meta_obs_get_ready_implied:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) =>
            interp_fancy_spred pkg  p)
  (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.meta_obs_get_ready_implied cache core reg_init get_field final_ext).
Proof. solve_cache_post_implies (Mem_PostMetaGetReady__Reg). Qed.
Lemma cache_post_implies_cache_obs_get_ready_implied:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) =>
            interp_fancy_spred pkg  p)
  (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.cache_obs_get_ready_implied cache core reg_init get_field final_ext).
Proof. solve_cache_post_implies (Mem_PostCacheGetReady__Reg). Qed.

Lemma cache_post_implies_cache_flush_only_invalidate_metadata:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) =>
            interp_fancy_spred pkg  p)
  (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.cache_flush_only_invalidate_metadata cache core reg_init reg_final get_field final_ext).
Proof. solve_cache_post_implies (Mem_FlushFSM_OnlyInvalidateMetadata). Qed.
Ltac simplify_update_metadata H :=
  unfold update_metadata in H;
  let his_write := fresh "hmeta_is_write" in
  let is_write := fresh "meta_is_write" in
  let hdata := fresh "hmeta_data" in
  let data := fresh "meta_data" in
  let haddr := fresh "hmeta_addr" in
  let addr := fresh "meta_addr" in
  destruct_matches_in_hyp_as H his_write; [ | discriminate]; rename_success_var his_write is_write;
  destruct_matches_in_hyp_as H hdata; [ | discriminate]; rename_success_var hdata data;
  destruct_matches_in_hyp_as H haddr; [ | discriminate]; rename_success_var haddr addr.

Lemma wf_cache_pair_implies_meta_resp_invariant_correct:
  forall st st' cache core ext_log mid_ext_log meta' mid_st mem input,
  (forall v : vect_t,
   ext_metadata_resp (ext_pair_meta (ext_l1_caches mem cache core)) = Some v ->
   meta_resp_invariant (get_cache_reg st cache core) v) ->
  metadata__ext (obs_meta (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core)
           (ext_pair_meta (ext_l1_caches mem cache core)) = Success meta' ->
  Forall
    (fun '(_, p) =>
     interp_fancy_spred
       (dummy_pkg st mid_st st' (mk_sigma_fn mem input) (Some mid_ext_log) ext_log) p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core impl_init impl_final impl_get_field impl_committed_ext ) ->
  (forall v : vect_t,
   ext_metadata_resp meta' = Some v ->
   meta_resp_invariant (get_cache_reg st' cache core) v).
Proof.
  intros * hinv hupdate hpost.
  intros * hresp. simplify_metadata_and_cache__ext hupdate.
  assert (Datatypes.length (obs_meta (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core) =
                           (_unsafe_struct_sz metadata_input_sig)) as hlen_obs.
  { eapply _get_field_length_implied; eauto. }
  specialize cache_post_implies_post_ext_meta_no_resp_core with (1 := hpost); intros hpost'.
  basic_cbn_in hpost'. rewrite meta_arg_type in hpost'.
  specialize hpost' with (1 := hlen_obs).

  destruct (ext_metadata_resp (ext_pair_meta (ext_l1_caches mem cache core))) eqn:hresp0.
  + specialize hinv with (1 := eq_refl).
    assert (get_ready = Ob~1); subst.
    { specialize cache_post_implies_meta_obs_get_ready_implied with (1 := hpost).
      intros hpost''. basic_cbn_in hpost''. convert_get_field_in hget_rdy.
      setoid_rewrite hget_rdy in hpost''. apply hpost''.
      eapply MetaRespInv_fromMeta_invalid with (1 := hinv).
    }
    bash_destruct hupdate; simplify; [ | discriminate].
    simplify_update_metadata hupdate.
    destruct_matches_in_hyp hupdate; simplify; simpl in hresp; simplify.
    assert_pre_and_specialize hpost'. { unsafe_auto_simplify_structs; reflexivity. }
    assert_pre_and_specialize hpost'.
    { unsafe_auto_simplify_structs; auto. unsafe_auto_simplify_structs; auto. }
    constructor; propositional.
  + assert (put_valid = Ob~1); subst.
    { bash_destruct hupdate; simplify; discriminate. }
    assert (update_metadata put_request (ext_metadata (ext_pair_meta (ext_l1_caches mem cache core))) =
              Success meta') as hmeta'.
    { bash_destruct hupdate; simplify; auto. }
    consider update_metadata. simplify.
    destruct_matches_in_hyp hmeta'; simplify; simpl in hresp; simplify.
    assert_pre_and_specialize hpost'. { unsafe_auto_simplify_structs; reflexivity. }
    assert_pre_and_specialize hpost'.
    { unsafe_auto_simplify_structs; auto. unsafe_auto_simplify_structs; auto. }
    constructor; propositional.
Qed.
Ltac simplify_update_cache H :=
  unfold update_cache in H;
  let haddr := fresh "hcache_addr" in
  let addr := fresh "cache_addr" in
  let hdata := fresh "hcache_data" in
  let data := fresh "cache_data" in
  let his_write := fresh "hcache_is_write" in
  let is_write := fresh "cache_is_write" in
  destruct_matches_in_hyp_as H his_write; [ | discriminate]; rename_success_var his_write is_write;
  destruct_matches_in_hyp_as H hdata; [ | discriminate]; rename_success_var hdata data;
  destruct_matches_in_hyp_as H haddr; [ | discriminate]; rename_success_var haddr addr.


Lemma wf_cache_pair_implies_cache_resp_invariant_correct:
  forall st st' cache core ext_log mid_ext_log cache' mid_st mem input,
  (forall v : vect_t,
   ext_cache_resp (ext_pair_cache (ext_l1_caches mem cache core)) = Some v ->
   cache_resp_invariant (get_cache_reg st cache core) v) ->
  cache__ext (obs_cache (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core)
           (ext_pair_cache (ext_l1_caches mem cache core)) = Success cache' ->
  Forall
    (fun '(_, p) =>
     interp_fancy_spred
       (dummy_pkg st mid_st st' (mk_sigma_fn mem input) (Some mid_ext_log) ext_log) p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core impl_init impl_final impl_get_field impl_committed_ext ) ->
  (forall v : vect_t,
   ext_cache_resp cache' = Some v ->
   cache_resp_invariant (get_cache_reg st' cache core) v).
Proof.
  intros * hinv hupdate hpost.
  intros * hresp.
  simplify_metadata_and_cache__ext hupdate.
  pose proof (_get_field_length_implied _ _ _ _ hput_valid) as hlen_obs.
  specialize cache_post_implies_post_ext_cache_no_resp_core with (1 := hpost); intros hpost'.
  basic_cbn_in hpost'. rewrite cache_arg_type in hpost'.
  specialize hpost' with (1 := hlen_obs).

  destruct (ext_cache_resp (ext_pair_cache(ext_l1_caches mem cache core))) eqn:hresp0.
  + specialize hinv with (1 := eq_refl).
    assert (get_ready = Ob~1); subst.
    { specialize cache_post_implies_cache_obs_get_ready_implied with (1 := hpost); intros hpost''.
      basic_cbn_in hpost''. convert_get_field_in hget_rdy. subst.
      assert_pre_and_specialize hpost''.
      { specialize CacheRespInv_fromCache_invalid with (1 := hinv); auto. }
      auto.
    }
    bash_destruct hupdate; simplify; [ | discriminate].
    simplify_update_cache hupdate.
    destruct_matches_in_hyp hupdate; simplify; simpl in hresp; simplify.
    assert_pre_and_specialize hpost'. { unsafe_auto_simplify_structs; reflexivity. }
    assert_pre_and_specialize hpost'.
    { unsafe_auto_simplify_structs; auto. unsafe_auto_simplify_structs; auto. }
    constructor; propositional.
  + assert (put_valid = Ob~1); subst.
    { bash_destruct hupdate; simplify; discriminate. }
    assert (update_cache put_request (ext_cache (ext_pair_cache (ext_l1_caches mem cache core))) =
              Success cache') as hcache'.
    { bash_destruct hupdate; simplify; auto. }
    consider update_cache. simplify.
    destruct_matches_in_hyp hcache'; simplify; simpl in hresp; simplify.
    assert_pre_and_specialize hpost'. { unsafe_auto_simplify_structs; reflexivity. }
    assert_pre_and_specialize hpost'.
    { unsafe_auto_simplify_structs; auto. unsafe_auto_simplify_structs; auto. }
    constructor; propositional.
Qed.
Lemma cache_post_implies_post_ext_meta_req_in_range_core:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) => interp_fancy_spred pkg  p)
  (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.impl_post_ext_meta_req_in_range EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext).
Proof.
  solve_cache_post_implies MemMetaRespInRange.
Qed.
Ltac replace_interp_fancy_spred'_cbn :=
        match goal with
        | |- context[?x ?y ?z (MemSymbDefs.fs_addr_in_range _ _ _ _ _)]  =>
            replace x with (@interp_fancy_spred' _ext_fn_tys unsafe_lookup_dstruct_fields) by reflexivity
        end.
Lemma cache_post_implies_valid_meta_addr:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) => interp_fancy_spred pkg  p)
  (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.valid_meta_addr cache core reg_init reg_final get_field final_ext).
Proof. solve_cache_post_implies (Mem_PostCacheAddr). Qed.
(* Lemma interp_derive_metadata_addr_eq: *)
(*   forall pkg pkg' args args' ext_fns lookup_structs e1 e1' e2 e2', *)
(*   (file_struct_defs (pkg_machine pkg))  = (file_struct_defs (pkg_machine pkg')) -> *)
(*   @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args e1 = *)
(*   @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' e1' -> *)
(*   @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args e2 = *)
(*   @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' e2' -> *)
(*   @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args *)
(*     (MemSymbDefs.derive_metadata_addr e1 e2) = *)
(*   @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' *)
(*     (MemSymbDefs.derive_metadata_addr e1' e2'). *)
(* Proof. *)
(*   intros * hstructs he1 he2. *)
(*   simpl. rewrite he1. rewrite_solve. *)
(* Qed. *)
Lemma cache_post_implies_meta_put_valid_impl_get_ready:
  forall pkg cache core reg_init reg_final get_field final_ext,
  Forall (fun '(_, p) => interp_fancy_spred pkg  p)
  (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core reg_init reg_final get_field final_ext) ->
  interp_fancy_spred pkg
    (MemSymbDefs.meta_obs_put_valid_impl_get_ready__ext cache core reg_final get_field final_ext).
Proof. solve_cache_post_implies (Mem_PostMetaGetReady__Ext). Qed.

Lemma meta_resp_in_range:
  forall cache core ext_log mid_ext_log meta' st mid_st st' mem input,
  WF_ext_log _ext_fn_tys (ext_log_app ext_log mid_ext_log) ->
  st'.[_id (_smid (SecurityMonitor.enc_data core))] = st.[_id (_smid (SecurityMonitor.enc_data core))] ->
  metadata__ext (obs_meta (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core)
           (ext_pair_meta (ext_l1_caches mem cache core)) = Success meta' ->
  wf_cache_pair cache core st (ext_l1_caches mem cache core) ->
  Forall
    (fun '(_, p) =>
     interp_fancy_spred
       (dummy_pkg st mid_st st' (mk_sigma_fn mem input) (Some mid_ext_log) ext_log) p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core impl_init impl_final impl_get_field impl_committed_ext ) ->
  forall v : vect_t,
  ext_metadata_resp meta' = Some v ->
  dummy_interp_spred_at_st st'
    (MemSymbDefs.meta_resp_in_range EnclaveParams.enclave_sig v cache core impl_init impl_get_field).
Proof.
  intros * hwf_ext henc_data hupdate hwf hpost * hresp'.
  apply WF_ext_log_implies_obs_meta_len with (cache := cache) (core := core) in hwf_ext.

  simplify_metadata_and_cache__ext hupdate.
  pose proof (_get_field_length_implied _ _ _ _ hput_valid) as hlen_obs.
  destruct put_valid; [discriminate |]. destruct put_valid; [| discriminate].
  destruct get_ready; [discriminate | ]. destruct get_ready; [| discriminate ].
  destruct b.
  - destruct b0; simplify.
    + consider update_metadata. simplify.
      destruct_matches_in_hyp hupdate; simplify; simpl in hresp'; simplify.
      unfold dummy_interp_spred_at_st. intros.
      destruct_match.
      * unfold MemSymbDefs.meta_resp_in_range.
        cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.fs_addr_in_range MemSymbDefs.derive_metadata_addr].
        match goal with
        | |- context[?x ?y ?z (MemSymbDefs.fs_addr_in_range _ _ _ _ _)]  =>
            replace x with (@interp_fancy_spred' _ext_fn_tys unsafe_lookup_dstruct_fields) by reflexivity;
            set y as _pkg; set z as _args
        end.
        specialize WF_meta_addrs with (1 := hwf) (2 := Heqo); intros hwf_meta.
        assert_pre_as hlen_line hwf_meta; [ | specialize hwf_meta with (1 := hlen_line)].
        { unsafe_auto_simplify_structs; auto.  erewrite _get_field_length_implied; eauto. reflexivity. }
        unfold dummy_interp_spred_at_st in *.
        specialize (hwf_meta  st'0 st'' sigma mid_log final_log). revert hwf_meta.
        cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.fs_addr_in_range MemSymbDefs.derive_metadata_addr].
        replace_interp_fancy_spred'_cbn. intros h_in_range hhvalid; propositional.
        unfold MemSymbDefs.derive_metadata_addr_from_push_req.
        specialize cache_post_implies_valid_meta_addr with (1 := hpost); intros hpost'.
        cbn - [_id _sid _fld mk_sigma_fn interp_bits1] in hpost'.
        assert_pre_and_specialize hpost'. { unsafe_auto_simplify_structs; auto. }
        assert_pre_and_specialize hpost'.
        { unsafe_auto_simplify_structs; auto.  unsafe_auto_simplify_structs; auto. }
        split; intros hcache_fsm.
        { eapply interp_fs_addr_in_range_addr_eq.
          4: eauto.
          { rewrite hcache_fsm in hpost'.
            split_ors_in hpost'; split_ands_in_hyps;[ clear - hpost'0; discriminate | ].
            eapply interp_derive_metadata_addr_eq; auto.
            cbn - [_id _sid _fld mk_sigma_fn interp_bits1].
            rewrite hpost'3.
            convert_get_field_in Heqr2.
            convert_get_field_in hput_req. setoid_rewrite hput_req. auto.
          }
          { basic_cbn. assumption. }
          { reflexivity. }
        }
        { eapply interp_fs_addr_in_range_addr_eq.
          4: eauto.
          { rewrite hcache_fsm in hpost'.
            split_ors_in hpost'; split_ands_in_hyps; [ | clear - hpost'0; discriminate].
            eapply interp_derive_metadata_addr_eq; auto.
            cbn - [_id _sid _fld mk_sigma_fn interp_bits1].
            rewrite hpost'1.
            convert_get_field_in Heqr2. convert_get_field_in hput_req. setoid_rewrite hput_req. auto.
          }
          { basic_cbn. assumption. }
          { reflexivity. }
        }
      * unfold MemSymbDefs.meta_resp_in_range.
        cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.fs_addr_in_range MemSymbDefs.derive_metadata_addr].
        intro. cbv in H. discriminate.
    + destruct_matches_in_hyp hupdate.
      * specialize WF_meta_state_inv with (1 := hwf) (2 := Heqo); intros hmeta_inv.
        specialize cache_post_implies_meta_obs_get_ready_implied with (1 := hpost); intros obs_get_ready.
        basic_cbn_in obs_get_ready.
        convert_get_field_in hget_rdy.
        setoid_rewrite obs_get_ready  in hget_rdy; [ discriminate | ].
        apply MetaRespInv_fromMeta_invalid with (1 := hmeta_inv).
      * consider update_metadata. simplify. destruct_matches_in_hyp hupdate; simplify; simpl in hresp'; simplify.
        exfalso.
        specialize cache_post_implies_meta_put_valid_impl_get_ready with (1 := hpost); intros hpost'.
        basic_cbn_in hpost'.
        assert_pre_and_specialize hpost'. { unsafe_auto_simplify_structs; auto.  }
        convert_get_field_in hget_rdy. setoid_rewrite hget_rdy in hpost'.
        propositional. discriminate.
  - destruct b0; simplify; simpl in hresp'.
    + discriminate.
    + specialize WF_meta_state_inv with (1 := hwf) (2 := hresp'); intros hmeta_inv.
      specialize cache_post_implies_meta_obs_get_ready_implied with (1 := hpost); intros obs_get_ready.
      basic_cbn_in obs_get_ready.
      convert_get_field_in hget_rdy.
      setoid_rewrite obs_get_ready  in hget_rdy; [ discriminate | ].
      apply MetaRespInv_fromMeta_invalid with (1 := hmeta_inv).
Qed.

(* Lemma interp_meta_resp_in_range_with_line_eq: *)
(*   forall pkg pkg' reg_fn reg_fn' args args' ext_fns lookup_structs line v cache core, *)
(*   (unsafe_get_field (lookup_structs (file_struct_defs (pkg_machine pkg')) *)
(*                        (_sid metadata_sig)) (_fld metadata_sig "valid") v <> Ob~1 \/ *)
(*      @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args (reg_fn (_smid (SecurityMonitor.enc_data core))) *)
(*     = @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' (reg_fn' (_smid (SecurityMonitor.enc_data core)))) -> *)
(*   (file_struct_defs (pkg_machine pkg))  = (file_struct_defs (pkg_machine pkg')) -> *)
(*   @interp_fancy_spred' ext_fns lookup_structs pkg args *)
(*     (MemSymbDefs.meta_resp_in_range_with_line EnclaveParams.enclave_sig line v cache core reg_fn impl_get_field) <-> *)
(*   @interp_fancy_spred' ext_fns lookup_structs pkg' args' *)
(*     (MemSymbDefs.meta_resp_in_range_with_line EnclaveParams.enclave_sig line v cache core reg_fn' impl_get_field). *)
(* Proof. *)
(*   intros * henc_data hstructs. *)
(*   cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.fs_addr_in_range MemSymbDefs.derive_metadata_addr ]. *)
(*   match goal with *)
(*   | |- context[?x ?y ?z (MemSymbDefs.fs_addr_in_range _ _ _ _ _ )]  => *)
(*       replace x with (@interp_fancy_spred' ext_fns lookup_structs) by reflexivity *)
(*   end. rewrite hstructs. *)
(*   split; intros; eapply interp_fs_addr_in_range_addr_eq; try (eapply H; auto). *)
(*   all: auto; try rewrite_solve; propositional. *)
(*   all: split_ors_in henc_data; try congruence. *)
(*   all: eapply interp_derive_metadata_addr_eq; eauto. *)
(*   all: simpl; rewrite hstructs; auto. *)
(* Qed. *)

Lemma meta_update_in_range:
  forall cache core ext_log mid_ext_log meta' st mid_st st' mem input,
  WF_ext_log _ext_fn_tys (ext_log_app ext_log mid_ext_log) ->
  st'.[_id (_smid (SecurityMonitor.enc_data core))] = st.[_id (_smid (SecurityMonitor.enc_data core))] ->
  metadata__ext (obs_meta (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core)
           (ext_pair_meta (ext_l1_caches mem cache core)) = Success meta' ->
  wf_cache_pair cache core st (ext_l1_caches mem cache core)  ->
  Forall
    (fun '(_, p) =>
     interp_fancy_spred
       (dummy_pkg st mid_st st' (mk_sigma_fn mem input) (Some mid_ext_log) ext_log) p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core impl_init impl_final impl_get_field impl_committed_ext ) ->
  forall (line : vect_t) (v : metadata_t),
  ext_metadata meta' (to_N line) = Some v ->
  Datatypes.length line = log_nlines ->
  dummy_interp_spred_at_st st'
    (MemSymbDefs.meta_resp_in_range_with_line EnclaveParams.enclave_sig line v cache core impl_init impl_get_field).
Proof.
  intros * hwf_ext henc_data hupdate hwf hpost * hresp'h hlen_lines.
  apply WF_ext_log_implies_obs_meta_len with (cache := cache) (core := core) in hwf_ext.
  simplify_metadata_and_cache__ext hupdate.
  pose proof (_get_field_length_implied _ _ _ _ hput_valid) as hlen_obs.
  destruct put_valid; [discriminate |]. destruct put_valid; [| discriminate].
  destruct get_ready; [discriminate | ]. destruct get_ready; [| discriminate ].
  intros.

  destruct b.
  - assert (b0 = true); subst.
    { specialize cache_post_implies_meta_put_valid_impl_get_ready with (1 := hpost); intros hpost'.
      basic_cbn_in hpost'.
      assert_pre_and_specialize hpost'. { unsafe_auto_simplify_structs; auto. }
      propositional.
      convert_get_field_in hget_rdy.
      { setoid_rewrite hget_rdy in hpost'0. clear - hpost'0. destruct b0; auto. discriminate. }
    }
    simplify_update_metadata hupdate.
    destruct_matches_in_hyp hupdate; simplify; simpl in hresp'h.
    + eapply WF_meta_addrs in hresp'h; auto.
      2: eauto.
      unfold dummy_interp_spred_at_st in *.
      intros.
      eapply interp_meta_resp_in_range_with_line_eq.
      3 : { eapply hresp'h. }
      all: eauto.
    + bash_destruct hresp'h; simplify.
      * eapply to_N_inj in Heqb0; eauto.
        2: { rewrite hlen_lines.  unsafe_auto_simplify_structs.
             eapply _get_field_success'; eauto; simpl; auto.
           }
        subst.
        specialize cache_post_implies_post_ext_meta_req_in_range_core with (1 := hpost); intros hpost'.
        cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.fs_addr_in_range MemSymbDefs.derive_metadata_addr] in hpost'.
        rewrite meta_arg_type in *. specialize hpost' with (1 := hlen_obs).
        assert_pre_and_specialize hpost'. { unsafe_auto_simplify_structs; auto. }
        assert (Datatypes.length put_request = _unsafe_struct_sz metadata_req_sig ) as hput_req_len.
        { eapply _get_field_length_implied; eauto. }
        assert (Datatypes.length meta_is_write = 1) as hlen_is_write.
        { unsafe_auto_simplify_structs. auto. }
        apply case_singleton_bv in hlen_is_write.
        destruct hlen_is_write; [| congruence]; subst.
        assert_pre_and_specialize hpost'.
        { repeat (unsafe_auto_simplify_structs; auto). }
        unfold dummy_interp_spred_at_st.
        cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.fs_addr_in_range MemSymbDefs.derive_metadata_addr].
        intros * hvalid.
        assert_pre_and_specialize hpost'.
        { repeat (unsafe_auto_simplify_structs; auto). }
        revert hpost'. replace_interp_fancy_spred'_cbn; intros hpost'.
        eapply interp_fs_addr_in_range_addr_eq.
        4: eapply hpost'.
        all: auto.
        convert_get_field_in hmeta_data. convert_get_field_in hput_req.
        eapply interp_derive_metadata_addr_eq.
        { auto. }
        { basic_cbn. subst. reflexivity. }
        { convert_get_field_in hmeta_addr. basic_cbn. subst. reflexivity. }
      * eapply WF_meta_addrs in hresp'h; auto.
        2: eauto.
        unfold dummy_interp_spred_at_st in *.
        intros. eapply interp_meta_resp_in_range_with_line_eq.
        3 : { eapply hresp'h. }
        all: eauto.
 - assert (ext_metadata meta' = ext_metadata (ext_pair_meta (ext_l1_caches mem cache core))) as hmeta'
       by (bash_destruct hupdate; simplify; auto).
   specialize WF_meta_addrs with (1 := hwf). rewrite<-hmeta'. intros hline.
   unfold dummy_interp_spred_at_st in *.
   intros.
   eapply interp_meta_resp_in_range_with_line_eq.
   3 : { eapply hline; eauto. }
   all: eauto.
Unshelve.
all: auto.
Qed.

Lemma mem_step_wf_caches_pair:
  forall cache core st st' mid_st mem mem' input mid_ext_log ext_log,
  WF_ext_log _ext_fn_tys (ext_log_app ext_log mid_ext_log) ->
  WF_state _reg_types st ->
  st'.[_id (_smid (SecurityMonitor.enc_data core))] = st.[_id (_smid (SecurityMonitor.enc_data core))] ->
  cachepair__ext (obs_meta (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core)
              (obs_cache (get_mem_observations (ext_log_app ext_log mid_ext_log)) cache core)
              (ext_l1_caches mem cache core) = Success (ext_l1_caches mem' cache core) ->
  wf_cache_pair cache core st (ext_l1_caches mem cache core)  ->
  Forall
    (fun '(_, p) =>
     interp_fancy_spred
       (dummy_pkg st mid_st st' (mk_sigma_fn mem input) (Some mid_ext_log) ext_log) p)
    (MemSymbDefs.cache_post EnclaveParams.enclave_sig cache core impl_init impl_final impl_get_field impl_committed_ext ) ->
  wf_cache_pair cache core st' (ext_l1_caches mem' cache core).
Proof.
  intros * hwf_log hwf_st hsm_enc_preserve hupdate hwf hpost .
  consider cachepair__ext. simplify.
  constructor; auto.
  - eapply wf_cache_pair_implies_cache_zeroed_outside_range; eauto.
    eapply WF_cache_outside_range; eauto.
  - eapply wf_cache_pair_implies_meta_zeroed_outside_range; eauto.
    eapply WF_meta_outside_range; eauto.
  - eapply wf_cache_pair_implies_cache_flush_correct; eauto.
    eapply WF_cache_flushed; eauto.
  - eapply wf_cache_pair_implies_meta_flush_correct; eauto.
    eapply WF_meta_flushed; eauto.
  - eapply meta_update_in_range; eauto.
  - eapply meta_resp_in_range; eauto.
  - eapply wf_cache_pair_implies_meta_resp_invariant_correct; eauto.
    + eapply WF_meta_state_inv. eauto.
  - eapply wf_cache_pair_implies_cache_resp_invariant_correct; eauto.
    eapply WF_cache_state_inv. eauto.
Qed.
Lemma In_exists:
  forall {A} {EqDec: EqDec A} x (l: list A),
  existsb (beq_dec x) l = true -> In x l.
Proof.
  intros * hexists. rewrite existsb_exists in hexists. propositional. simplify. auto.
Qed.
Ltac solve_In_to_find' :=
  apply In_exists; vm_reflect.

  Lemma mem_step_implies:
  forall init_st impl_st__koika impl_st__mem koika_log ext_log mid_ext_log input,
  strong_WF_state reg_type_env init_st ->
  WF_ext_mem impl_st__mem ->
  WF_ext_log _ext_fn_tys mid_ext_log ->
  WF_ext_log _ext_fn_tys ext_log ->
  ImplInvariant {| machine_koika_st := init_st;
                   machine_mem_st := impl_st__mem
                |} ->
  ImplInvariant {| machine_koika_st := impl_st__koika;
                   machine_mem_st := impl_st__mem
                |} ->
  strong_WF_state reg_type_env (commit_update (impl_st__koika) koika_log) ->
  MemSymbDefs.MemPost EnclaveParams.enclave_sig (impl_st__koika) (commit_update (impl_st__koika) koika_log) (mk_sigma_fn impl_st__mem input) ext_log ->
  dummy_interp init_st (impl_st__koika) (commit_update (impl_st__koika) koika_log)
               (mk_sigma_fn impl_st__mem input)
               (Some mid_ext_log) ext_log
               (SymbPfChain.post_core1_exprs impl_init impl_mid impl_mid_ext) ->
  exists mem,
  update_memory
    (get_mem_observations (ext_log_app ext_log mid_ext_log))
                        impl_st__mem  = Success mem /\
    ImplInvariant {| machine_koika_st := (commit_update (impl_st__koika) koika_log);
                     machine_mem_st := mem |} /\
          dummy_interp init_st (impl_st__koika) (commit_update (impl_st__koika) koika_log)
                       (mk_sigma_fn mem input)
                         (Some mid_ext_log) ext_log
                         (SymbPfChain.post_mem_exprs EnclaveParams.enclave_sig impl_init impl_final impl_committed_ext impl_get_field).
  Proof.
    intros * hwf_init hwf_sigma hwf_mid_ext_log hwf_ext_log hinv_init hinv hwf' hpost hcore1.
    set {| machine_koika_st := init_st; machine_mem_st := impl_st__mem |} as st_init in *.
    set {| machine_koika_st := impl_st__koika; machine_mem_st := impl_st__mem |} as st_mid in *.
    set (commit_update impl_st__koika koika_log) as final_koika_st in *.
    specialize ImplInvariant_implies_spreds with (1 := hinv); intros hpres.
    specialize ImplInvariant_implies_spreds with (1 := hinv_init); intros hpres_init.

    assert (WF_ext_log _ext_fn_tys (ext_log_app ext_log mid_ext_log)) as hwf_log_app.
    { eauto with modularity. }
    specialize symbolic_evaluate_file_success with (file := impl_mem_step_file EnclaveParams.enclave_sig).
    set (mk_sigma_fn impl_st__mem input) as sigma in *.

    assert (SymbolicInterp.WF_single_file (impl_mem_step_file EnclaveParams.enclave_sig) = true) as Hwf_file.
    { apply WF_impl_mem_step_file. }

    assert (WF_abstract_state_set dummy_machine sigma init_st
              impl_st__koika final_koika_st  mid_ext_log ext_log) as Hwf_step.
    { unfold WF_abstract_state_set; repeat unsafe_weaken_strong_WF; split_ands_in_goal; eauto with modularity.
      eapply ImplInv_WF_state with (1 := hinv); eauto.
    }
    intros Hok.
    cbn [file_machines impl_mem_step_file] in Hok. propositional.
    unfold symbolic_evaluate_file_success_abstract_single in *.
    specialize Hok with (sigma := sigma) (st := init_st)
                        (st' := final_koika_st) (mid_ext_log := mid_ext_log)
                        (ext_log' := ext_log) (2 := Hwf_step).

    assert_pre_as Hassumes Hok; [clear Hok| specialize Hok with (1 := Hassumes)].
    {
      unfold impl_mem_step_file. unfold file_assumptions.
      do 3 rewrite Forall_app. split_ands_in_goal.
      - unfold sigma. replace init_st with (machine_koika_st st_init) by auto.
        replace impl_st__mem with (machine_mem_st st_init) by auto.
        apply ImplInvariant_spreds_implies_invariant_spreds'_init; auto.
      - unfold sigma. replace impl_st__koika with (machine_koika_st st_mid) by auto.
        replace impl_st__mem with (machine_mem_st st_mid) by auto.
        apply ImplInvariant_spreds_implies_invariant_spreds'_mid.  auto.
      - consider dummy_interp. consider dummy_pkg. init_interp_in hcore1.
        revert hcore1.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      - (* DONE *)
        consider MemSymbDefs.MemPost. init_interp_in hpost.
        replace_mid_st_in hpost (Some impl_st__koika); [ | solve_package_equiv ].
        rewrite Lift_Forall with (g := replace_spred_init_reg_with_mid) in hpost;
          [ | solve[ intro q; apply replace_fancy_spred_init_reg_with_mid_correct with (p := PBase q); auto] ].
        clear - hpost.
        change_Forall_lists1 hpost.
        revert hpost.  clearbody sigma. clearbody final_koika_st.
        apply forall_interp_spred_package_equiv. solve_package_equiv.
    }

    unfold file_assertions, impl_mem_step_file in Hok.
    rewrite Forall_app in Hok. destruct Hok as (Hok & hpost1).

    consider update_memory.
    specialize update_memory_success with (log := ext_log_app ext_log mid_ext_log) (2 := hwf_sigma); intros hsuccess.
    propositional. simplify. exists s; split; auto.

    split.
    - pose proof (ImplInvariant_destruct {| machine_koika_st := final_koika_st; machine_mem_st := s |}) as Hconc.
      assert_pre_and_specialize Hconc; [eauto with modularity | ].
      assert_pre_and_specialize Hconc; [eauto with modularity | ].
      simpl in Hconc.
      assert_pre_as Hwf_cache' Hconc; [| specialize Hconc with (1 := Hwf_cache')].
      {
        intros * .
        rewrite forall_preprocess_fancy_spreds_correct in hpost1.
        (* cbn - [MemSymbDefs.cache_pre_conds']. repeat rewrite Forall_app. split_ands_in_hyps. *)
        eapply mem_step_wf_caches_pair.
        1: eauto.
        3: eapply ext_mem_update_memory_implies_cache; eauto.
        4: { specialize post_mem_exprs_impl_cache_post_conds with (1 := hpost1); intros Hcache_post.
             rewrite Forall_ignore_map_fst in Hcache_post.
             cbn - [MemSymbDefs.cache_post] in Hcache_post. repeat rewrite Forall_app in Hcache_post.
             split_ands_in_hyps. destruct cache; destruct core; eauto.
           }
        { apply strong_WF_state_weaken in hwf_init. assumption. }
        { prop_pose_with_custom hfoo  CustomTaint hpost1.
          apply hfoo. destruct core; solve_In_to_find'.
        }
        { eapply (ImplInv_metapair st_init). auto. }
      }
      apply Hconc.
      assert (forall core,
                 dummy_interp final_koika_st impl_st__koika final_koika_st (mk_sigma_fn s input) (Some mid_ext_log) ext_log
                   (map_fst PfChain.CustomMem
                      (MemSymbDefs.mem_pre_conds' EnclaveParams.enclave_sig core impl_init impl_get_field))) as hpre.
      { intros.
        rewrite forall_preprocess_fancy_spreds_correct in hpost1.
        unfold file_assumptions, impl_mem_step_file in Hassumes.
        unfold MemSymbDefs.mem_pre_conds'.
        do 3 rewrite Forall_app in Hassumes. destruct Hassumes as (_hinv_init & _hinv_mid  & _hpost_core1 & _hpost_mem).
        rewrite forall_preprocess_fancy_spreds_correct in _hpost_mem.
        rewrite forall_preprocess_fancy_spreds_correct in _hpost_core1.
        (* prop_pose_with_custom hmem (PfChain.CustomExtFn ((_ext ext_mainmem))) _hpost_core1. *)
        unfold dummy_interp.
        rewrite Forall_ignore_map_fst.
        rewrite Forall_app. split.
        { constructor.
          {  prop_pose_with_custom  hfoo
              ((MemoryProofs.MemImplExtCorrectCore CoreId0)) _hpost_mem.
            prop_pose_with_custom hturn ((MemoryProofs.MemMainMemPutIsReadTurn)) _hpost_mem.
            eapply impl_ext_mem_correct_core_implied; eauto.
            prop_pose_with_custom hmem (PfChain.CustomExtFn ((_ext ext_mainmem))) _hpost_core1.
            auto.
          }
          constructor.
          { prop_pose_with_custom  hfoo
              ((MemoryProofs.MemImplExtCorrectCore CoreId1)) _hpost_mem.
            prop_pose_with_custom hturn ((MemoryProofs.MemMainMemPutIsReadTurn)) _hpost_mem.
            eapply impl_ext_mem_correct_core_implied; eauto.
            prop_pose_with_custom hmem (PfChain.CustomExtFn ((_ext ext_mainmem))) _hpost_core1. auto.
          }
          constructor.
        }
        specialize post_mem_exprs_impl_cache_post_conds with (1 := hpost1); intros Hcache_post.
        all: specialize ImplInv_metapair with (1 := hinv_init); intros hmeta.
        rewrite Forall_ignore_map_fst in Hcache_post.
        cbn - [MemSymbDefs.cache_post] in Hcache_post. repeat rewrite Forall_app in Hcache_post.
        cbn - [MemSymbDefs.cache_pre_conds']. repeat rewrite Forall_app. split_ands_in_goal.
        3: constructor.
        all: split_ands_in_hyps; destruct core; eapply cache_post_cond_impl_cache_pre_cond; eauto with modularity.
      }


      eapply ImplInvariant_spreds_implied with (mid_st:= impl_st__koika) (final_st := final_koika_st)
                                                 (ext_log1 := Some mid_ext_log) (ext_log2 := ext_log) (input := input) (1 := eq_refl).
        * replace impl_st__koika with (machine_koika_st {| machine_koika_st := impl_st__koika;
                                                        machine_mem_st := impl_st__mem
                                                      |}) by reflexivity.
          replace final_koika_st with (machine_koika_st {| machine_koika_st := final_koika_st;
                                                           machine_mem_st := s
                                                        |}) by reflexivity.
          eapply ImplInvariant_spreds_implies_invariant_spreds'_init'. unfold machine_koika_st.
          eapply Hok.
        * apply hpre.
    - (* DONE; slowish  *)
      clear - hpost1. unfold dummy_interp.
      init_interp. revert hpost1.
      apply forall_interp_spred_package_equiv.
      clearbody sigma. clearbody final_koika_st.
      solve_package_equiv.
  Qed. (* TODO: SLOW  *)
Ltac rewrite_hcache_reg hcache_reg st' :=
    match goal with
    | |- context[st'.[_id (_mid (Memory.Memory.cache_reg ?cache ?core ?reg))] ] =>
        setoid_rewrite (hcache_reg cache core reg)
    | |- context[(st').[_id (_mid (Memory.Memory.cache_imem0 ?reg))] ] =>
        setoid_rewrite (hcache_reg imem CoreId0 reg)
    | |- context[(st').[_id (_mid (Memory.Memory.cache_dmem0 ?reg))] ] =>
        setoid_rewrite (hcache_reg dmem CoreId0 reg)
    | |- context[(st').[_id (_mid (Memory.Memory.cache_imem1 ?reg))] ] =>
        setoid_rewrite (hcache_reg imem CoreId1 reg)
    | |- context[(st').[_id (_mid (Memory.Memory.cache_dmem1 ?reg))] ] =>
        setoid_rewrite (hcache_reg dmem CoreId1 reg)
    end.
(* Lemma interp_meta_resp_in_range_eq: *)
(*   forall pkg pkg' reg_fn reg_fn' args args' ext_fns lookup_structs cache core, *)
(*   (forall args args', @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args *)
(*         (reg_fn (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm))) *)
(*     = @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' *)
(*         (reg_fn' (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm)))) -> *)
(*   (forall args args', *)
(*       @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args *)
(*         (reg_fn (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm))) = (_enum Memory.cache_fsm_sig "ProcessRequest") \/ *)
(*       @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args *)
(*         (reg_fn (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm))) = (_enum Memory.cache_fsm_sig "FlushLineProcess")  -> *)
(*       @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args (reg_fn (_smid (SecurityMonitor.enc_data core))) *)
(*     = @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' (reg_fn' (_smid (SecurityMonitor.enc_data core)))) -> *)
(*   (forall args args', *)
(*       @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args *)
(*         (reg_fn (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm))) = (_enum Memory.cache_fsm_sig "ProcessRequest") -> *)
(*         @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args *)
(*         (reg_fn (_mid (Memory.Memory.coreToCache cache core MemReq.data0))) *)
(*     = @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' *)
(*         (reg_fn' (_mid (Memory.Memory.coreToCache cache core MemReq.data0))))  -> *)
(*   (forall args args', @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args *)
(*         (reg_fn (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.line_flush_idx))) *)
(*     = @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args' *)
(*         (reg_fn' (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.line_flush_idx)))) -> *)
(*   (file_struct_defs (pkg_machine pkg))  = (file_struct_defs (pkg_machine pkg')) -> *)
(*   (forall arg, (unsafe_call_ext (pkg_sigma pkg) (_id (_extid (Memory.Memory.ext_metadata cache core))) arg ) = *)
(*           (unsafe_call_ext (pkg_sigma pkg') (_id (_extid (Memory.Memory.ext_metadata cache core))) arg )) -> *)
(*   @interp_fancy_spred' ext_fns lookup_structs pkg args *)
(*     (MemSymbDefs.impl_ext_meta_resp_in_range EnclaveParams.enclave_sig core cache reg_fn impl_get_field) <-> *)
(*   @interp_fancy_spred' ext_fns lookup_structs pkg' args' *)
(*     (MemSymbDefs.impl_ext_meta_resp_in_range EnclaveParams.enclave_sig core cache reg_fn' impl_get_field). *)
(* Proof. *)
(*   intros * (* henc_data *) hcache_fsm hreg_eq hreg_eq' hflush_eq hstructs hsigma_eq . *)
(*   cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.fs_addr_in_range MemSymbDefs.derive_metadata_addr ]. *)
(*   split; intros * g * hlen hget_valid hvalid; specialize g with (1 := hlen); revert g; *)
(*     match goal with *)
(*     | |- context[?x ?y ?z (MemSymbDefs.fs_addr_in_range _ _ _ _ _ )]  => *)
(*         replace x with (@interp_fancy_spred' ext_fns lookup_structs) by reflexivity *)
(*     end;  specialize (hreg_eq (args~("arg",y)) (args'~("arg",y))); *)
(*     specialize (hreg_eq' (args~("arg",y)) (args'~("arg",y))); *)
(*     repeat rewrite hstructs in *; *)
(*     repeat rewrite (hsigma_eq y) in *; *)
(*     repeat rewrite (hcache_fsm (args~("arg",y)) (args'~("arg",y))) in *; *)
(*     propositional. *)
(*   all: split; propositional. *)
(*   all:  eapply interp_fs_addr_in_range_addr_eq; [ | | | eauto]; auto. *)
(*   all: eapply interp_derive_metadata_addr_eq; auto. *)
(*   1,3,6: basic_cbn; rewrite hsigma_eq; rewrite hstructs; reflexivity. *)
(*   - simpl; rewrite hstructs. rewrite_solve. *)
(*   - basic_cbn. rewrite hstructs. rewrite hsigma_eq. auto. *)
(*   - simpl; rewrite hstructs; rewrite_solve. *)
(* Qed. *)
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

Lemma cache_pre_conds_implied:
  forall st st' ext_log input mid_log cache core,
  ImplInvariant_spreds EnclaveParams.enclave_sig st ->
  (forall reg, (machine_koika_st st').[_id (_mid (Memory.Memory.cache_reg cache core reg))] =
          (machine_koika_st st).[_id (_mid (Memory.Memory.cache_reg cache core reg))]) ->
  ((machine_koika_st st).[_id (_mid (Memory.Memory.purge core))] <> _enum purge_state "Purged" ->
   (machine_koika_st st').[_id (_smid (SecurityMonitor.enc_data core))] =
        (machine_koika_st st).[_id (_smid (SecurityMonitor.enc_data core))]) ->
  ((machine_koika_st st).[_id (_mid (Memory.Memory.coreToCache cache core MemReq.valid0))] = Ob~1 ->
   (machine_koika_st st').[_id (_mid (Memory.Memory.coreToCache cache core MemReq.data0))] =
        (machine_koika_st st).[_id (_mid (Memory.Memory.coreToCache cache core MemReq.data0))]) ->
  Forall
    (fun '(_, p) =>
     interp_fancy_spred
       {|
         pkg_machine := MemSymbDefs.impl_machine;
         pkg_init_st := machine_koika_st st;
         pkg_sigma := mk_sigma_fn (machine_mem_st st) input;
         pkg_mid_st := None;
         pkg_final_st := machine_koika_st st;
         pkg_mid_ext_log := None;
         pkg_ext_log' := SortedExtFnEnv.empty
       |} p) (MemSymbDefs.cache_pre_conds' EnclaveParams.enclave_sig cache core impl_init impl_get_field) ->
  Forall
    (fun '(_, p) =>
     interp_fancy_spred
       (dummy_pkg (machine_koika_st st') (machine_koika_st st) (machine_koika_st st')
          (mk_sigma_fn (machine_mem_st st) input) (Some mid_log) ext_log) p)
    (MemSymbDefs.cache_pre_conds' EnclaveParams.enclave_sig cache core impl_init impl_get_field).
Proof.
  intros * hInv hcache_reg henq hreq. unfold MemSymbDefs.cache_pre_conds'.
  intros hinv.
  repeat rewrite Forall_cons_iff in hinv.
  destruct hinv as (h0 & h1 & h2 & h3 & h4 & h5).
  repeat constructor.
  - cbn - [_id _sid _fld mk_sigma_fn].
    cbn - [_id _sid _fld mk_sigma_fn] in h0.
    repeat rewrite hcache_reg; assumption.
  - cbn - [_id _sid _fld mk_sigma_fn].
    cbn - [_id _sid _fld mk_sigma_fn] in h1.
    repeat rewrite hcache_reg; assumption.
  - eapply interp_meta_resp_in_range_eq with (7 := h2).
    all: basic_cbn; auto;
      intros;
    eapply ImplInvariant_spreds_implies with
      (mid_st := machine_koika_st st) (final_st := machine_koika_st st)
      (input := input) (ext_log1 := None) (ext_log2 := SortedExtFnEnv.empty) in hInv ; eauto;
      rewrite hcache_reg in H.
    { rewrite henq; auto. unfold not; intros hpurge. propositional. destruct core.
      1: prop_pose_with_custom hfoo (PfChain.CustomMem Mem_purged0) hInv0.
      2: prop_pose_with_custom hfoo (PfChain.CustomMem Mem_purged1) hInv0.
      all: cbn - [_id _sid _fld mk_sigma_fn of_N_sz mem_regs_to_reset] in hfoo;
           rewrite hfoo in H; auto.
      2,4: destruct cache; solve_In_to_find'.
      all: clear - H; destruct cache; split_ors_in H; vm_compute in H; discriminate.
    }
    intros.
    { rewrite hreq; auto;
      unfold dummy_interp in hInv. set (dummy_pkg _ _ _ _ _ _) as _pkg in hInv.
      assert (interp_fancy_spred _pkg
                  (MemSymbDefs.cache_ProcessRequest core cache impl_init impl_get_field)) as hProcessRequest.
      { propositional. wrap_solve_cache_post_implies PfChain.CustomMem Mem_cache_ProcessRequest hInv0. }
      basic_cbn_in hProcessRequest. propositional.
    }
  - cbn - [_id _sid _fld mk_sigma_fn].
    cbn - [_id _sid _fld mk_sigma_fn] in h3.
    repeat rewrite hcache_reg; assumption.
  - cbn - [_id _sid _fld mk_sigma_fn].
    cbn - [_id _sid _fld mk_sigma_fn] in h4.
    repeat rewrite hcache_reg; assumption.
Qed.

Lemma mem_pre_conds_implied':
  forall st st' ext_log input mid_log core,
  ImplInvariant_spreds EnclaveParams.enclave_sig st ->
  machine_mem_st st' = machine_mem_st st ->
  (machine_koika_st st').[_id (_mid Memory.Memory.SHReq)] =  (machine_koika_st st).[_id (_mid Memory.Memory.SHReq)] ->
  (machine_koika_st st').[_id (_mid Memory.Memory.turn)] =  (machine_koika_st st).[_id (_mid Memory.Memory.turn)] ->
  (forall cache core reg, (machine_koika_st st').[_id (_mid (Memory.Memory.cache_reg cache core reg))] =
                 (machine_koika_st st).[_id (_mid (Memory.Memory.cache_reg cache core reg))]) ->
  (forall core,
      (machine_koika_st st).[_id (_mid (Memory.Memory.purge core))] <> _enum purge_state "Purged" ->
    (machine_koika_st st').[_id (_smid (SecurityMonitor.enc_data core))] =
      (machine_koika_st st).[_id (_smid (SecurityMonitor.enc_data core))]) ->
  (forall cache core ,
      (machine_koika_st st).[_id (_mid (Memory.Memory.coreToCache cache core MemReq.valid0))] = Ob~1 ->
      (machine_koika_st st').[_id (_mid (Memory.Memory.coreToCache cache core MemReq.data0))] =
        (machine_koika_st st).[_id (_mid (Memory.Memory.coreToCache cache core MemReq.data0))]) ->
  dummy_interp (machine_koika_st st') (machine_koika_st st) (machine_koika_st st')
    (mk_sigma_fn (machine_mem_st st') input) (Some mid_log) ext_log
    (map_fst PfChain.CustomMem (MemSymbDefs.mem_pre_conds' EnclaveParams.enclave_sig core impl_init impl_get_field)).
Proof.
  intros * hinv hmemeq hshreq hturn hcache_reg henc_data hreq.
  pose proof hinv as hinv'.
  apply ImplInvariant_spreds_impl_mem_pre with (input := input) (core := core) in hinv.
  consider MemSymbDefs.mem_pre_conds'.
  unfold dummy_interp.
  rewrite Forall_app in hinv. split_ands_in_hyps.
  cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.impl_ext_mem_correct_core] in hinv0.
  repeat rewrite Forall_cons_iff in hinv0.
  split_ands_in_hyps.
  rewrite Forall_ignore_map_fst.
  repeat rewrite hmemeq.
  constructor.
  { cbn - [_id _sid _fld mk_sigma_fn].
    repeat rewrite hshreq. repeat rewrite hturn.
    repeat rewrite_hcache_reg hcache_reg (machine_koika_st st'). auto.
  }
  constructor.
  { cbn - [_id _sid _fld mk_sigma_fn].
    repeat rewrite hshreq. repeat rewrite hturn.
    repeat (rewrite_hcache_reg hcache_reg (machine_koika_st st')); auto.
  }
  cbn - [MemSymbDefs.cache_pre_conds'].
  repeat rewrite Forall_app.
  cbn - [MemSymbDefs.cache_pre_conds'] in hinv1.
  repeat rewrite Forall_app in hinv1.
  split_ands_in_hyps. split_ands_in_goal.
  all: try eapply cache_pre_conds_implied; auto.
Qed.


Lemma mem_pre_conds_implied:
  forall st st' ext_log input mid_log core,
  ImplInvariant_spreds EnclaveParams.enclave_sig st ->
  machine_mem_st st' = machine_mem_st st ->
  (machine_koika_st st').[_id (_mid Memory.Memory.SHReq)] =  (machine_koika_st st).[_id (_mid Memory.Memory.SHReq)] ->
  (machine_koika_st st').[_id (_mid Memory.Memory.turn)] =  (machine_koika_st st).[_id (_mid Memory.Memory.turn)] ->
  (forall cache core reg, (machine_koika_st st').[_id (_mid (Memory.Memory.cache_reg cache core reg))] =
                 (machine_koika_st st).[_id (_mid (Memory.Memory.cache_reg cache core reg))]) ->
  (forall core,
      (machine_koika_st st).[_id (_mid (Memory.Memory.purge core))] <> _enum purge_state "Purged" ->
    (machine_koika_st st').[_id (_smid (SecurityMonitor.enc_data core))] =
      (machine_koika_st st).[_id (_smid (SecurityMonitor.enc_data core))]) ->
  (forall cache core ,
      (machine_koika_st st).[_id (_mid (Memory.Memory.coreToCache cache core MemReq.valid0))] = Ob~1 ->
      (machine_koika_st st').[_id (_mid (Memory.Memory.coreToCache cache core MemReq.data0))] =
        (machine_koika_st st).[_id (_mid (Memory.Memory.coreToCache cache core MemReq.data0))]) ->
  dummy_interp (machine_koika_st st') (machine_koika_st st) (machine_koika_st st')
    (mk_sigma_fn (machine_mem_st st') input) (Some mid_log) ext_log
    (map_fst PfChain.CustomMem (MemSymbDefs.mem_pre_conds' EnclaveParams.enclave_sig core impl_init impl_get_field)).
Proof.
  intros * hinv hmemeq hshreq hturn hcache_reg henc_data hreq.
  pose proof hinv as hinv'.
  apply ImplInvariant_spreds_impl_mem_pre with (input := input) (core := core) in hinv.
  consider MemSymbDefs.mem_pre_conds'.
  unfold dummy_interp.
  rewrite Forall_app in hinv. split_ands_in_hyps.
  cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.impl_ext_mem_correct_core] in hinv0.
  repeat rewrite Forall_cons_iff in hinv0.
  split_ands_in_hyps.
  rewrite Forall_ignore_map_fst.
  repeat rewrite hmemeq.
  constructor.
  { cbn - [_id _sid _fld mk_sigma_fn].
    repeat rewrite hshreq. repeat rewrite hturn.
    repeat rewrite_hcache_reg hcache_reg (machine_koika_st st'). auto.
  }
  constructor.
  { cbn - [_id _sid _fld mk_sigma_fn].
    repeat rewrite hshreq. repeat rewrite hturn.
    repeat (rewrite_hcache_reg hcache_reg (machine_koika_st st')); auto.
  }
  cbn - [MemSymbDefs.cache_pre_conds'].
  repeat rewrite Forall_app.
  cbn - [MemSymbDefs.cache_pre_conds'] in hinv1.
  repeat rewrite Forall_app in hinv1.
  split_ands_in_hyps. split_ands_in_goal.
  all: try eapply cache_pre_conds_implied; auto.
Qed.
Instance FT_MemCacheState : FiniteType.FiniteType Memory.CacheState.reg_t := _.

Lemma cache_regs_untainted_by_sm:
  forall cache core reg,
  In (_mid (Memory.Memory.cache_reg cache core reg))
    (remove_regs reg_list (map reg_to_debug_id (sm_regs CoreId0 ++ sm_regs CoreId1))).
Proof.
  intros.
  set (remove_regs reg_list (map reg_to_debug_id (sm_regs CoreId0 ++ sm_regs CoreId1))) .
  vm_compute in l.
  eapply In_subset with (xs1 := map (fun r => _mid (Memory.Memory.cache_reg cache core r)) (@FiniteType.finite_elements _ FT_MemCacheState)).
  - destruct cache; destruct core; vm_reflect.
  - rewrite in_map_iff. exists reg; split; auto. apply in_finite_elements.
Qed.
Ltac specialize_dummies:=
  repeat match goal with
  | H: ?x -> _, g: ?x |- _ =>  specialize (H g)
  end.
Lemma cache_flush_line_eq:
  forall cache core st st' caches,
  (st'.[_id (_mid (Memory.Memory.purge core))] = Ob~1~1 ->
   st.[_id (_mid (Memory.Memory.purge core))] = Ob~1~1) ->
  ((st.[_id (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm))] = _enum Memory.cache_fsm_sig "FlushLineReady" \/
    st.[_id (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm))] = _enum Memory.cache_fsm_sig "FlushLineProcess" ) ->
    st.[_id (_mid (Memory.Memory.purge core))] <> Ob~1~1) ->
  (forall reg, st'.[_id (_mid (Memory.Memory.cache_reg cache core reg))] =
          st.[_id (_mid (Memory.Memory.cache_reg cache core reg))]) ->
  cache_flush_line cache core st caches ->
  cache_flush_line cache core st' caches.
Proof.
  consider cache_flush_line. unfold dummy_interp_spred_at_st.
  intros * hpurge hcache_purged hreg_eq hinv * hline hflush heq hline'; intros.
  specialize hinv with (1 := hline) (n := n) (4 := hline').
  eapply hinv; eauto.
  - basic_cbn. basic_cbn_in hflush. propositional. specialize_dummies.
    repeat rewrite hreg_eq in *. split_cases.
  - basic_cbn. basic_cbn_in heq. basic_cbn_in hflush. propositional. specialize_dummies.
    repeat rewrite hreg_eq in *; propositional.
    split_ors_in hflush; propositional.
    split; auto. intros. split_ors_in H; propositional.
Qed.
Lemma meta_flush_line_eq:
  forall cache core st st' caches,
  (st'.[_id (_mid (Memory.Memory.purge core))] = Ob~1~1 ->
   st.[_id (_mid (Memory.Memory.purge core))] = Ob~1~1) ->
  ((st.[_id (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm))] = Ob~1~0~0 \/
    st.[_id (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm))] = Ob~1~0~1) ->
    st.[_id (_mid (Memory.Memory.purge core))] <> Ob~1~1) ->
  (forall reg, st'.[_id (_mid (Memory.Memory.cache_reg cache core reg))] =
          st.[_id (_mid (Memory.Memory.cache_reg cache core reg))]) ->
  meta_flush_line cache core st caches ->
  meta_flush_line cache core st' caches.
Proof.
  consider meta_flush_line. unfold dummy_interp_spred_at_st.
  intros * hpurge hcache_purged hreg_eq hinv * hline hflush heq hline'; intros.
  specialize hinv with (1 := hline) (n := n) (4 := hline').
  eapply hinv; eauto.
  - basic_cbn. basic_cbn_in hflush. propositional. specialize_dummies.
    repeat rewrite hreg_eq in *. split_cases.
  - basic_cbn. basic_cbn_in heq. basic_cbn_in hflush. propositional. specialize_dummies.
    repeat rewrite hreg_eq in *; propositional.
    split_ors_in hflush; propositional.
    split; auto. intros. split_ors_in H; propositional.
Qed.
Lemma meta_resp_inv_unchanged:
  forall st st' cache core v,
(st'.[_id (_mid (Memory.Memory.cache_reg cache core (Memory.CacheState.SH_metadata_resp Memory.MetadataResp.valid0)))] = st.[_id (_mid (Memory.Memory.cache_reg cache core (Memory.CacheState.SH_metadata_resp Memory.MetadataResp.valid0)))]) ->
(st'.[_id (_mid (Memory.Memory.cache_reg cache core (Memory.CacheState.cache_fsm)))] = st.[_id (_mid (Memory.Memory.cache_reg cache core (Memory.CacheState.cache_fsm)))]) ->
  meta_resp_invariant (get_cache_reg st cache core) v ->
  meta_resp_invariant (get_cache_reg st' cache core) v.
Proof.
  intros * heq hfsm hinv. destruct hinv.
  constructor; consider get_cache_reg; try rewrite_solve.
Qed.
Lemma cache_resp_inv_unchanged:
  forall st st' cache core v,
(st'.[_id (_mid (Memory.Memory.cache_reg cache core (Memory.CacheState.SH_cache_resp Memory.CacheResp.valid0)))] = st.[_id (_mid (Memory.Memory.cache_reg cache core (Memory.CacheState.SH_cache_resp Memory.CacheResp.valid0)))]) ->
(st'.[_id (_mid (Memory.Memory.cache_reg cache core (Memory.CacheState.cache_fsm)))] = st.[_id (_mid (Memory.Memory.cache_reg cache core (Memory.CacheState.cache_fsm)))]) ->

  cache_resp_invariant (get_cache_reg st cache core) v ->
  cache_resp_invariant (get_cache_reg st' cache core) v.
Proof.
  intros * heq hfsm hinv. destruct hinv.
  constructor; consider get_cache_reg; try rewrite_solve.
Qed.
Lemma interp_meta_resp_in_range_eq':
  forall pkg pkg' reg_fn reg_fn' args args' ext_fns lookup_structs v cache core,
  (file_struct_defs (pkg_machine pkg))  = (file_struct_defs (pkg_machine pkg')) ->
  (@SymbolicInterp.interp_sval ext_fns lookup_structs pkg args
        (reg_fn (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm)))
    = @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args'
        (reg_fn' (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm)))) ->
   (@SymbolicInterp.interp_sval ext_fns lookup_structs pkg args
        (reg_fn (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm))) = (_enum Memory.cache_fsm_sig "ProcessRequest") ->
        @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args
        (reg_fn (_mid (Memory.Memory.coreToCache cache core MemReq.data0)))
    = @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args'
        (reg_fn' (_mid (Memory.Memory.coreToCache cache core MemReq.data0))))  ->
  (unsafe_get_field (lookup_structs (file_struct_defs (pkg_machine pkg')) (_sid metadata_sig))
         (_fld metadata_sig "valid") v <> Ob~1 \/
  @SymbolicInterp.interp_sval ext_fns lookup_structs pkg args
    (reg_fn ( (_smid (SecurityMonitor.enc_data core)))) =
  @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args'
    (reg_fn' ( (_smid (SecurityMonitor.enc_data core))))) ->
  (@SymbolicInterp.interp_sval ext_fns lookup_structs pkg args
        (reg_fn (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.line_flush_idx)))
    = @SymbolicInterp.interp_sval ext_fns lookup_structs pkg' args'
        (reg_fn' (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.line_flush_idx)))) ->
  @interp_fancy_spred' ext_fns lookup_structs pkg args
    (MemSymbDefs.meta_resp_in_range  EnclaveParams.enclave_sig v cache core reg_fn impl_get_field) <->
  @interp_fancy_spred' ext_fns lookup_structs pkg' args'
    (MemSymbDefs.meta_resp_in_range EnclaveParams.enclave_sig v cache core reg_fn' impl_get_field).
Proof.
  intros * hstructs hcache_fsm hcore henc hline.
  cbn - [_id _sid _fld mk_sigma_fn MemSymbDefs.fs_addr_in_range MemSymbDefs.derive_metadata_addr ].
  match goal with
  | |- context[?x ?y ?z (MemSymbDefs.fs_addr_in_range _ _ _ _ _ )]  =>
      replace x with (@interp_fancy_spred' ext_fns lookup_structs) by reflexivity
  end. repeat rewrite hstructs; rewrite hcache_fsm in *;
  split; propositional; split; propositional; try eapply interp_fs_addr_in_range_addr_eq;
    try (eapply H1; solve[auto]);
    try (eapply H2; solve[auto]); auto.
  all: try solve[split_ors_in henc; [congruence | ]; auto].
  all: eapply interp_derive_metadata_addr_eq; eauto.
  all: simpl; try rewrite hstructs; auto.
  all: try rewrite hcore; auto.
Qed.

Lemma wf_cache_pair_unchanged:
  forall cache core st0 st st' caches ,
   ImplInvariant_spreds EnclaveParams.enclave_sig st0 ->
   WF_ext_cache_pair caches ->
   st = machine_koika_st st0 ->
  (st'.[_id (_mid (Memory.Memory.purge core))] = Ob~1~1 -> st.[_id (_mid (Memory.Memory.purge core))] = Ob~1~1) ->
  (forall reg : Memory.CacheState.reg_t,
   st'.[_id (_mid (Memory.Memory.cache_reg cache core reg))] =
   st.[_id (_mid (Memory.Memory.cache_reg cache core reg))]) ->
  (forall core : ind_core_id,
      (st).[_id (_mid (Memory.Memory.purge core))] <> _enum purge_state "Purged" ->
    (st').[_id (_smid (SecurityMonitor.enc_data core))] =
      (st).[_id (_smid (SecurityMonitor.enc_data core))]) ->
  (st.[_id (_mid (Memory.Memory.coreToCache cache core MemReq.valid0))]  = Ob~1 ->
   st'.[_id (_mid (Memory.Memory.coreToCache cache core MemReq.data0))] =
  (machine_koika_st st0).[_id (_mid (Memory.Memory.coreToCache cache core MemReq.data0))]) ->
  wf_cache_pair cache core st caches  ->
  wf_cache_pair cache core st' caches .
Proof.
  intros * hInv hwf hbar hpurge hreg_eq henc hfifo hinv.
  eapply ImplInvariant_spreds_implies with
      (mid_st := st) (final_st := st)
      (input := dummy_input_t) (ext_log1 := None) (ext_log2 := SortedExtFnEnv.empty) in hInv; eauto.
  propositional.
  destruct hinv.
  assert (
  (machine_koika_st st0).[_id (_mid (Memory.Memory.cache_reg cache core Memory.CacheState.cache_fsm))] <> _enum Memory.cache_fsm_sig "Ready" ->
  (machine_koika_st st0).[_id (_mid (Memory.Memory.purge core))] <> Ob~1~1) as hnot_purged.
  { unfold not; intros * hfsm hmem_purge.
    destruct core.
    1: prop_pose_with_custom hfoo (PfChain.CustomMem Mem_purged0) hInv0.
    2: prop_pose_with_custom hfoo (PfChain.CustomMem Mem_purged1) hInv0.
    all: apply hfoo in hmem_purge; cbn - [_id _sid _fld mk_sigma_fn of_N_sz mem_regs_to_reset] in hmem_purge.
    all: rewrite hmem_purge in hfsm.
    2,4: destruct cache; solve_In_to_find'.
    all: assert_pre_and_specialize hfsm; auto.
    all: destruct cache; vm_compute; reflexivity.
  }

  constructor; auto.
  - eapply cache_flush_line_eq with (st := machine_koika_st st0); eauto.
    intros; apply hnot_purged; split_ors_in H; try rewrite H; auto; discriminate.
  - eapply meta_flush_line_eq with (st := machine_koika_st st0); eauto.
    intros; apply hnot_purged; split_ors_in H; try rewrite H; auto; discriminate.
  - intros * hline hlen. specialize WF_meta_addrs0 with (1 := hline) (2 := hlen).
    consider dummy_interp_spred_at_st. intros.
    assert (Datatypes.length v = _unsafe_struct_sz metadata_sig) as hlen_meta.
    { eapply WF_meta_sram; eauto with solve_invariants. }
    assert (Datatypes.length
              (unsafe_get_field (unsafe_lookup_dstruct_fields (file_struct_defs (pkg_machine (dummy_pkg st' st'0 st'' sigma mid_log final_log))) (_sid metadata_sig)) (_fld metadata_sig "valid") v) = 1) as hresp_len.
    { pose proof (eta_expand_list_correct false v) as hv. rewrite hlen_meta in hv. cbn in hv.
      rewrite hv. vm_reflect. }
    apply case_singleton_bv in hresp_len.
    eapply interp_meta_resp_in_range_with_line_eq.
    3: eapply WF_meta_addrs0.
    2: reflexivity.
    split_ors_in hresp_len.
    2: { left. setoid_rewrite hresp_len. congruence. }
    right.
    eapply henc.
    consider meta_flush_line. move WF_meta_flushed0 at bottom.
    unfold not; intros.
    rewrite WF_meta_flushed0 with (line := ((2 ^ N.of_nat log_nlines) - 1)%N) in hline; auto.
    { simplify. vm_compute in hresp_len. congruence. }
    { lia. }
    { unfold dummy_interp_spred_at_st. basic_cbn. auto. }
    { unfold dummy_interp_spred_at_st. basic_cbn. intros.  split.
      - auto.
      - propositional. assert_pre_and_specialize hnot_purged; propositional.
        split_ors_in H1; rewrite H1; destruct cache; auto; discriminate.
    }
    { pose proof (to_N_bounded line). rewrite hlen in *. lia. }
  - intros * hresp. specialize WF_valid_meta_resp0 with (1 := hresp).
    specialize WF_meta_state_inv0 with (1 := hresp).
    consider dummy_interp_spred_at_st. intros.
    eapply interp_meta_resp_in_range_eq'.
    6: eapply WF_valid_meta_resp0; auto.
    all: basic_cbn; auto.
    { rewrite hreg_eq.
      intros. apply hfifo.
      unfold dummy_interp in *. set (dummy_pkg _ _ _ _ _ _ ) as _pkg in *.
      assert (interp_fancy_spred _pkg
                  (MemSymbDefs.cache_ProcessRequest core cache impl_init impl_get_field)) as hProcessRequest.
      { propositional. wrap_solve_cache_post_implies PfChain.CustomMem Mem_cache_ProcessRequest hInv0. }
      basic_cbn_in hProcessRequest. propositional.
    }
    { right. apply henc. apply hnot_purged.
      apply MetaRespInv_fsm in WF_meta_state_inv0.
      split_ors_in WF_meta_state_inv0; setoid_rewrite WF_meta_state_inv0; discriminate.
    }
  - intros. eapply meta_resp_inv_unchanged.
    3 : eapply WF_meta_state_inv0; eauto.
    all: auto.
  - intros. eapply cache_resp_inv_unchanged.
    3 : eapply WF_cache_state_inv0; eauto.
    all: auto.
  Unshelve. all: auto.
Qed.


  Lemma sm_step_implies:
    forall init_st impl_st__koika impl_st__mem  impl_mem__init koika_log ext_log mid_ext_log input,
    strong_WF_state reg_type_env init_st ->
    WF_ext_log _ext_fn_tys mid_ext_log ->
    WF_ext_log _ext_fn_tys ext_log ->
    WF_ext_mem impl_st__mem  ->
    ImplInvariant {| machine_koika_st := init_st;
                     machine_mem_st := impl_mem__init
                  |} ->
    ImplInvariant {| machine_koika_st := impl_st__koika;
                     machine_mem_st := impl_st__mem
                  |} ->
    strong_WF_state reg_type_env (commit_update (impl_st__koika) koika_log) ->
    SMPost EnclaveParams.enclave_sig (impl_st__koika) (commit_update (impl_st__koika) koika_log)
      (mk_sigma_fn impl_mem__init input) ext_log ->
    dummy_interp init_st (impl_st__koika) (commit_update (impl_st__koika) koika_log)
                 (mk_sigma_fn impl_st__mem input)
                 (Some mid_ext_log) ext_log
                 (post_mem_exprs EnclaveParams.enclave_sig impl_init impl_mid impl_mid_ext impl_get_field) ->
    ImplInvariant {| machine_koika_st := (commit_update (impl_st__koika) koika_log);
                     machine_mem_st := impl_st__mem |} /\
    dummy_interp init_st (impl_st__koika)
                     (commit_update (impl_st__koika) koika_log)
                     (mk_sigma_fn impl_st__mem input)
                     (Some mid_ext_log) ext_log
                     (post_sm_exprs EnclaveParams.enclave_sig impl_init impl_final
                                    impl_mid_ext impl_committed_ext impl_get_field).
  Proof.
    intros * hwf_init hwf_mid_ext_log hwf_ext_log hwf_mem hinv_init hinv hwf' hpost hmem.
    set {| machine_koika_st := init_st; machine_mem_st := impl_mem__init |} as st_init in *.
    set {| machine_koika_st := impl_st__koika; machine_mem_st := impl_st__mem |} as st_mid in *.
    set (commit_update impl_st__koika koika_log) as final_koika_st in *.
    set {| machine_koika_st := final_koika_st;
           machine_mem_st := impl_st__mem
        |} as final_st in *.

    specialize ImplInvariant_implies_spreds with (1 := hinv); intros hpres.
    specialize ImplInvariant_implies_spreds with (1 := hinv_init); intros hpres_init.

    assert (WF_ext_log _ext_fn_tys (ext_log_app ext_log mid_ext_log)) as hwf_log_app.
    { eauto with modularity. }
    specialize symbolic_evaluate_file_success with (file := impl_sm_step_file EnclaveParams.enclave_sig).
    set (mk_sigma_fn impl_st__mem input) as sigma in *.

    assert (SymbolicInterp.WF_single_file (impl_sm_step_file EnclaveParams.enclave_sig) = true) as Hwf_file.
    { apply WF_impl_sm_step_file. }

    assert (WF_abstract_state_set dummy_machine sigma init_st
              impl_st__koika final_koika_st  mid_ext_log ext_log) as Hwf_step.
    { unfold WF_abstract_state_set; repeat unsafe_weaken_strong_WF; split_ands_in_goal; eauto with modularity.
      eapply ImplInv_WF_state with (1 := hinv); eauto.
    }
    intros Hok.
    cbn [file_machines impl_sm_step_file] in Hok. propositional.
    unfold symbolic_evaluate_file_success_abstract_single in *.
    specialize Hok with (sigma := sigma) (st := init_st)
                        (st' := final_koika_st) (mid_ext_log := mid_ext_log)
                        (ext_log' := ext_log) (2 := Hwf_step).
    assert_pre_as Hassumes Hok; [clear Hok| specialize Hok with (1 := Hassumes)].
    {
      unfold impl_sm_step_file. unfold file_assumptions.
      do 3 rewrite Forall_app. split_ands_in_goal.
      - replace init_st with (machine_koika_st st_init) by auto.
        replace impl_st__koika with (machine_koika_st st_mid) by reflexivity.
        replace final_koika_st with (machine_koika_st final_st) by reflexivity.
        apply ImplInvariant_spreds_implies_invariant_spreds'_init.
        auto.
      - unfold sigma. replace impl_st__koika with (machine_koika_st st_mid) by auto.
        replace impl_st__mem with (machine_mem_st st_mid) by auto.
        apply ImplInvariant_spreds_implies_invariant_spreds'_mid.  auto.
      - consider dummy_interp. consider dummy_pkg. init_interp_in hmem.
        revert hmem.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      - consider SMPost. init_interp_in hpost.
        replace_mid_st_in hpost (Some impl_st__koika); [ | solve_package_equiv ].
        rewrite Lift_Forall with (g := replace_spred_init_reg_with_mid) in hpost;
          [ | solve[ intro q; apply replace_fancy_spred_init_reg_with_mid_correct with (p := PBase q); auto] ].
        change_Forall_lists1 hpost.
        revert hpost.  clear. clearbody sigma; clearbody final_koika_st.
        apply forall_interp_spred_package_equiv. solve_package_equiv.
    }
    unfold file_assertions, impl_sm_step_file in Hok.
    rewrite Forall_app in Hok. destruct Hok as (Hok & hpost1).
    pose proof (ImplInvariant_destruct {| machine_koika_st := final_koika_st; machine_mem_st := impl_st__mem |}) as Hconc.
    assert_pre_and_specialize Hconc; [eauto with modularity | ].
    assert_pre_and_specialize Hconc; [eauto with modularity | ].
    simpl in Hconc.
    unfold file_assumptions, impl_sm_step_file in Hassumes.
    do 3 rewrite Forall_app in Hassumes. destruct Hassumes as (hinv_init' & hinv_mid & hpost_mem & hpost_sm).
    rewrite forall_preprocess_fancy_spreds_correct in hpost_sm.

    assert (forall core : ind_core_id,
               impl_st__koika.[_id (_mid (Memory.Memory.purge core))] <> _enum purge_state "Purged" ->
               final_koika_st.[_id (_smid (SecurityMonitor.enc_data core))] =
                 impl_st__koika.[_id (_smid (SecurityMonitor.enc_data core))]) as henc_preserved.
    { intros.
      destruct core.
      1: prop_pose_with_custom hfoo' (SM_post_mem_not_purged CoreId0) hpost_sm.
      2: prop_pose_with_custom hfoo' (SM_post_mem_not_purged CoreId1) hpost_sm.
      all: symmetry; basic_cbn_in hfoo'; apply hfoo'; auto.
    }

    assert (forall (cache : mem_type) (core : ind_core_id),
               impl_st__koika.[_id (_mid (Memory.Memory.coreToCache cache core MemReq.valid0))] = Ob~1 ->
               final_koika_st.[_id (_mid (Memory.Memory.coreToCache cache core MemReq.data0))] =
                 impl_st__koika.[_id (_mid (Memory.Memory.coreToCache cache core MemReq.data0))]) as hmem_fifo.
    { intros * hvalid.
      destruct core.
      1: prop_pose_with_custom hfifo (SM_wf_fifos CoreId0) hpost_sm.
      2: prop_pose_with_custom hfifo (SM_wf_fifos CoreId1) hpost_sm.
      all: basic_cbn_in hfifo; clear - hvalid hfifo; destruct cache; propositional.
    }

    split.
    - assert_pre_and_specialize Hconc.
      {
       intros. eapply wf_cache_pair_unchanged with (1 := hpres); auto.
       4: { specialize ImplInv_metapair with (1 := hinv); eauto. }
       { eauto with solve_invariants. }
       { destruct core.
         - prop_pose_with_custom hfoo (SM_post_mem_purge0) hpost_sm. auto.
         - prop_pose_with_custom hfoo (SM_post_mem_purge1) hpost_sm. auto.
       }
       { prop_pose_with_custom hfoo (SM_taint) hpost_sm.
         intros. apply hfoo. apply cache_regs_untainted_by_sm.
       }
      }
      apply Hconc.
      assert (forall core,
        dummy_interp (machine_koika_st {| machine_koika_st := final_koika_st; machine_mem_st := impl_st__mem |})
          impl_st__koika final_koika_st
          (mk_sigma_fn (machine_mem_st {| machine_koika_st := final_koika_st; machine_mem_st := impl_st__mem |}) input)
          (Some mid_ext_log) ext_log
          (map_fst PfChain.CustomMem
             (MemSymbDefs.mem_pre_conds' EnclaveParams.enclave_sig core impl_init impl_get_field))) as hpre'.
      { intros. replace impl_st__koika with (machine_koika_st {| machine_koika_st := impl_st__koika;
                                                      machine_mem_st := impl_st__mem
                                                    |}) by reflexivity.
        replace final_koika_st with (machine_koika_st {| machine_koika_st := final_koika_st;
                                                         machine_mem_st := impl_st__mem
                                                      |}) by reflexivity.
        prop_pose_with_custom hfoo (SM_taint) hpost_sm.
        eapply mem_pre_conds_implied; unfold machine_koika_st.
        { apply hpres. }
        { reflexivity. }
        { apply hfoo. solve_In_to_find'. }
        { apply hfoo. solve_In_to_find'. }
        { intros. apply hfoo. apply cache_regs_untainted_by_sm. }
        all: auto.
      }

      eapply ImplInvariant_spreds_implied with (mid_st:= impl_st__koika) (final_st := final_koika_st)
                                               (ext_log1 := Some mid_ext_log) (ext_log2 := ext_log) (input := input) (1 := eq_refl).
      + replace impl_st__koika with (machine_koika_st {| machine_koika_st := impl_st__koika;
                                                      machine_mem_st := impl_st__mem
                                                    |}) by reflexivity.
        replace final_koika_st with (machine_koika_st {| machine_koika_st := final_koika_st;
                                                         machine_mem_st := impl_st__mem
                                                      |}) by reflexivity.
        eapply ImplInvariant_spreds_implies_invariant_spreds'_init'.
        eapply Hok.
      + apply hpre'.
    - clear - hpost1. unfold dummy_interp.
      init_interp. revert hpost1. clearbody final_koika_st. clearbody sigma.
      apply forall_interp_spred_package_equiv. solve_package_equiv.
  Qed.

  Lemma core0_step_preserve_invariant':
    forall st st' ext_log input,
    strong_WF_state reg_type_env (machine_koika_st st) ->
    strong_WF_state reg_type_env (machine_koika_st st') ->
    WF_ext_mem (machine_mem_st st) ->
    WF_ext_log _ext_fn_tys ext_log ->
    (machine_mem_st st')  = machine_mem_st st ->
    ImplInvariant_spreds EnclaveParams.enclave_sig st ->
    CoreSymbDefs.CorePost CoreId0 (machine_koika_st st) (machine_koika_st st')
      (mk_sigma_fn (machine_mem_st st) input ) ext_log ->
    ImplInvariant_spreds EnclaveParams.enclave_sig st'.
  Proof.  (* DONE *)
    intros * hwf hwf' hwf_mem hwf_ext_log hmemeq hinv Core0_post.
    specialize symbolic_evaluate_file_success with (file := (impl_core0_step_file EnclaveParams.enclave_sig)).
    set (mk_sigma_fn (machine_mem_st st) input) as sigma in *.
    assert (SymbolicInterp.WF_single_file (impl_core0_step_file EnclaveParams.enclave_sig) = true) as Hwf_file.
    { apply WF_impl_core0_step_file. }
    assert (WF_abstract_state_set dummy_machine sigma (machine_koika_st st) (machine_koika_st st) (machine_koika_st st') SortedExtFnEnv.empty ext_log) as Hwf_step.
    { unfold WF_abstract_state_set; repeat unsafe_weaken_strong_WF; split_ands_in_goal;
        eauto with modularity.
    }
    intros Hok.
    cbn [file_machines impl_core0_step_file] in Hok.
    specialize Hok with (1 := Hwf_file).
    unfold symbolic_evaluate_file_success_abstract_single in *.
    specialize Hok with (sigma := sigma) (st := machine_koika_st st) (mid_st := machine_koika_st st) (st' := machine_koika_st st') (mid_ext_log := SortedExtFnEnv.empty) (ext_log' := ext_log) (2 := Hwf_step).
    assert_pre_as Hassumes Hok; [clear Hok| specialize Hok with (1 := Hassumes)].
    { unfold impl_core0_step_file. unfold file_assumptions.
      rewrite forall_interp_spred_preprocess_app_iff.
      rewrite Forall_app; split_ands_in_goal.
      - apply  ImplInvariant_spreds_implies_invariant_spreds'_init; auto.
      - consider CoreSymbDefs.CorePost .
        rewrite<-forall_preprocess_fancy_spreds_correct in Core0_post.
        rewrite preprocess_fancy_spreds_map_fst_equiv.
        revert Core0_post.
        eapply forall_interp_spred_package_equiv.
        clearbody sigma.
        solve_package_equiv.
    }
    unfold file_assertions, impl_core0_step_file in Hok.
    eapply ImplInvariant_spreds_implied with (mid_st:= (machine_koika_st st)) (final_st := machine_koika_st st') (ext_log1 := Some SortedExtFnEnv.empty) (ext_log2 := ext_log) (input := input) (1 := eq_refl).
    - eapply ImplInvariant_spreds_implies_invariant_spreds'_init' with (1 := Hok).
    - unfold file_assumptions, impl_core0_step_file in Hassumes.
      rewrite forall_preprocess_fancy_spreds_correct in Hassumes.
      prop_pose_with_custom htaint (CustomCore0 CoreTaint) Hassumes.
      set (remove_regs reg_list  (map reg_to_debug_id (core_regs CoreId0))) in htaint. vm_compute in l.
      intros.
      eapply mem_pre_conds_implied; auto.
      + apply htaint. solve_In_to_find'.
      + apply htaint. solve_In_to_find'.
      + intros. pose proof (@in_finite_elements _ Memory.FiniteType_CacheState reg) as hin.
        apply htaint.
        eapply In_subset with (xs1 := (map (fun x => _mid (Memory.Memory.cache_reg cache core0 x))
                                         (@finite_elements _ Memory.FiniteType_CacheState))).
        destruct cache; destruct core0; vm_reflect.
        rewrite in_map_iff. exists reg; split; auto.
      + intros; apply htaint. destruct core0; solve_In_to_find'.
      + intros; apply htaint.
        destruct cache; destruct core0; solve_In_to_find'.
  Qed. (* DONE *)

  Lemma core0_step_preserve_invariant:
    forall impl_st koika_log ext_log input,
    WF_ext_log _ext_fn_tys ext_log ->
    WF_ext_mem (machine_mem_st impl_st) ->
    ImplInvariant impl_st ->
    strong_WF_state reg_type_env (commit_update (machine_koika_st impl_st) koika_log) ->
    CoreSymbDefs.CorePost CoreId0 (machine_koika_st impl_st)
                   (commit_update (machine_koika_st impl_st) koika_log)
                   (mk_sigma_fn (machine_mem_st impl_st) input) ext_log ->
    ImplInvariant {| machine_koika_st := (commit_update (machine_koika_st impl_st) koika_log);
                     machine_mem_st := impl_st.(machine_mem_st) |}.
  Proof.
    intros * hwf_ext_log hwf_mem hinv hwf' hpost.

    apply ImplInvariant_destruct; simpl; eauto with modularity.
    - specialize ImplInv_metapair with (1 := hinv); intros hwf_caches.
      specialize ImplInvariant_implies_spreds with (1 := hinv); intros hinv_spreds.
      consider CorePost.
      prop_pose_with_custom hfoo CoreTaint hpost.
      set (remove_regs _ _) as l in *. vm_compute in l.
      intros. eapply wf_cache_pair_unchanged; eauto with solve_invariants.
      + setoid_rewrite hfoo; [ solve[auto] | ].
        destruct core; solve_In_to_find'.
      + intros. setoid_rewrite hfoo; [ solve[auto] | ].
        eapply In_subset with (xs1 := map (fun r => _mid (Memory.Memory.cache_reg cache core r))
                                        (@FiniteType.finite_elements _ FT_MemCacheState)).
        { destruct cache; destruct core; vm_reflect.  }
        { rewrite in_map_iff. exists reg; split; auto.
          apply in_finite_elements.
        }
      + intros. setoid_rewrite hfoo; [solve[auto] | ].
        destruct core0; solve_In_to_find'.
      + setoid_rewrite hfoo; [solve[auto] | ].
        destruct cache; destruct core; solve_In_to_find'.
    - specialize ImplInvariant_implies_spreds with (1 := hinv); intros hpres.
      eapply core0_step_preserve_invariant' with (st := impl_st); eauto with modularity.
  Qed.


Lemma CorePost_implies_post_conds':
  forall core sigma1 sigma2 final_st init_st mid_st post_log final_log,
  CorePost core init_st mid_st sigma2 post_log ->
  dummy_interp init_st mid_st final_st
    sigma1 (Some post_log) final_log (post_conds' core impl_init impl_mid impl_mid_ext).
Proof. (* DONE *)
  intros * HPostCore.
  unfold dummy_interp, dummy_pkg.
  init_interp.
  consider CorePost. consider post_conds.
  rewrite Forall_app in HPostCore.
  destruct HPostCore as (HPostCore & HPostCore').
  init_interp_in HPostCore.
  destruct core.
  - replace_final_st_with_mid.
    replace_final_ext_with_mid.
    change_Forall_lists1 HPostCore.
    revert HPostCore.
    apply forall_interp_spred_package_equiv; try solve_package_equiv.
  - replace_final_st_with_mid.
    replace_final_ext_with_mid.
    change_Forall_lists1 HPostCore.
    revert HPostCore.
    apply forall_interp_spred_package_equiv; try solve_package_equiv.
Qed. (* DONE *)
Lemma CorePost_implies_post_conds:
  forall core sigma1 sigma2 final_st init_st mid_st post_log final_log,
  CorePost core init_st mid_st sigma2 post_log ->
  dummy_interp init_st mid_st final_st
    sigma1 (Some post_log) final_log (post_conds core impl_init impl_mid impl_mid_ext).
Proof. (* DONE *)
  intros * HPostCore.
  unfold dummy_interp, dummy_pkg.
  init_interp.
  consider CorePost. init_interp_in HPostCore.
  destruct core.
  - replace_final_st_with_mid.
    replace_final_ext_with_mid.
    change_Forall_lists1 HPostCore.
    revert HPostCore.
    apply forall_interp_spred_package_equiv; try solve_package_equiv.
  - replace_final_st_with_mid.
    replace_final_ext_with_mid.
    change_Forall_lists1 HPostCore.
    revert HPostCore.
    apply forall_interp_spred_package_equiv; try solve_package_equiv.
Qed. (* DONE *)

  Lemma core1_step_implies':
    forall init_st mid_st final_st mid_ext_log ext_log sigma1 sigma2 input,
    strong_WF_state reg_type_env (machine_koika_st init_st) ->
    strong_WF_state reg_type_env mid_st.(machine_koika_st) ->
    strong_WF_state reg_type_env final_st.(machine_koika_st) ->
    WF_ext_mem (machine_mem_st mid_st) ->
    WF_ext_log _ext_fn_tys mid_ext_log ->
    WF_ext_log _ext_fn_tys ext_log ->
    ImplInvariant_spreds EnclaveParams.enclave_sig init_st ->
    ImplInvariant_spreds EnclaveParams.enclave_sig mid_st ->
    (machine_mem_st mid_st) = machine_mem_st final_st ->
    (machine_mem_st init_st) = machine_mem_st final_st ->
    dummy_interp (machine_koika_st init_st) mid_st.(machine_koika_st) final_st.(machine_koika_st)
                 sigma1
                 (Some mid_ext_log) ext_log
        (CoreSymbDefs.post_conds' CoreId0 impl_init impl_mid
                                            impl_mid_ext
        ) ->
    CoreSymbDefs.CorePost CoreId1 mid_st.(machine_koika_st) final_st.(machine_koika_st) (mk_sigma_fn (machine_mem_st mid_st) input) ext_log ->
    ImplInvariant_spreds EnclaveParams.enclave_sig final_st /\
      dummy_interp (machine_koika_st init_st) mid_st.(machine_koika_st) final_st.(machine_koika_st) sigma2
                   (Some mid_ext_log) ext_log
        (SymbPfChain.post_core1_exprs impl_init impl_final impl_committed_ext).
  Proof. (* DONE *)
    intros * hwf_init hwf_mid hwf_final hwf_sigma hwf_mid_ext_log hwf_ext_log
             hinv_init hinv hmem0 hmem1 hcore0 hcore1.
    specialize symbolic_evaluate_file_success with (file := (impl_core1_step_file EnclaveParams.enclave_sig)).
    set (mk_sigma_fn (machine_mem_st mid_st) input) as sigma in *.

    assert (SymbolicInterp.WF_single_file (impl_core1_step_file EnclaveParams.enclave_sig) = true) as Hwf_file.
    { apply WF_impl_core1_step_file. }

    assert (WF_abstract_state_set dummy_machine sigma (machine_koika_st init_st)
              mid_st.(machine_koika_st) final_st.(machine_koika_st) mid_ext_log ext_log) as Hwf_step.
    { unfold WF_abstract_state_set; repeat unsafe_weaken_strong_WF; split_ands_in_goal; eauto with modularity.
    }
    intros Hok.
    cbn [file_machines impl_core1_step_file] in Hok. specialize Hok with (1 := Hwf_file).
    unfold symbolic_evaluate_file_success_abstract_single in *.
    specialize Hok with (sigma := sigma) (st := machine_koika_st init_st)
                        (st' := machine_koika_st final_st) (mid_ext_log := mid_ext_log)
                        (ext_log' := ext_log) (2 := Hwf_step).
    assert_pre_as Hassumes Hok; [clear Hok| specialize Hok with (1 := Hassumes)].
    { unfold impl_core1_step_file. unfold file_assumptions.
      rewrite forall_preprocess_fancy_spreds_correct.
      repeat rewrite Forall_app. split_ands_in_goal.
      - rewrite<-forall_preprocess_fancy_spreds_correct.
        unfold sigma. rewrite hmem0. rewrite<-hmem1.
        apply ImplInvariant_spreds_implies_invariant_spreds'_init; auto.
      - rewrite<-forall_preprocess_fancy_spreds_correct.
        apply ImplInvariant_spreds_implies_invariant_spreds'_mid.  auto.
      - rewrite Forall_ignore_map_fst. init_interp.
        consider dummy_interp. consider dummy_pkg. init_interp_in hcore0.
        revert hcore0. clearbody sigma.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      - consider CorePost. init_interp_in hcore1.
        init_interp. clearbody sigma.
        replace_mid_st_in hcore1 (Some (machine_koika_st mid_st)); [ | solve_package_equiv ].
        rewrite Lift_Forall with (g := replace_spred_init_reg_with_mid) in hcore1;
          [ | solve[ intro q; apply replace_fancy_spred_init_reg_with_mid_correct with (p := PBase q); auto] ].
        change_Forall_lists1 hcore1.
        revert hcore1.
        apply forall_interp_spred_package_equiv. solve_package_equiv.
    }
    unfold file_assertions, impl_core1_step_file in Hok.
    rewrite Forall_app in Hok. destruct Hok as (Hok & hpost1).
    split.
    - eapply ImplInvariant_spreds_implied with (mid_st:= (machine_koika_st mid_st)) (final_st := machine_koika_st final_st) (ext_log1 := Some mid_ext_log) (ext_log2 := ext_log) (input := input) (1 := eq_refl).
      + eapply ImplInvariant_spreds_implies_invariant_spreds'_init' with (sigma := sigma) (mid_st := Some (machine_koika_st mid_st)).
        eapply Hok.
      + unfold file_assumptions, impl_core1_step_file in Hassumes.
        rewrite forall_preprocess_fancy_spreds_correct in Hassumes.
        prop_pose_with_custom htaint (CustomCore1 CoreTaint) Hassumes.
        set (remove_regs reg_list  (map reg_to_debug_id (core_regs CoreId1))) in htaint. vm_compute in l.
        intros. eapply mem_pre_conds_implied ; auto.
        * apply htaint. solve_In_to_find'.
        * apply htaint. solve_In_to_find'.
        * intros. pose proof (@in_finite_elements _ Memory.FiniteType_CacheState reg) as hin.
          apply htaint.
          eapply In_subset with (xs1 := (map (fun x => _mid (Memory.Memory.cache_reg cache core0 x))
                                           (@finite_elements _ Memory.FiniteType_CacheState))).
          destruct cache; destruct core0; vm_reflect.
          rewrite in_map_iff. eauto.
        * intros. apply htaint. destruct core0; solve_In_to_find'.
        * intros. apply htaint. destruct cache; destruct core0; solve_In_to_find'.
    - clear - hpost1. unfold dummy_interp.
      init_interp. revert hpost1.
      apply forall_interp_spred_package_equiv. clearbody sigma. solve_package_equiv.
  Qed. (* DONE *)


  Lemma core1_step_preserve_invariant:
    forall init_st impl_st__koika impl_st__mem koika_log ext_log mid_ext_log sigma1 sigma2 input,
    strong_WF_state reg_type_env init_st ->
    WF_ext_mem impl_st__mem  ->
    WF_ext_log _ext_fn_tys mid_ext_log ->
    WF_ext_log _ext_fn_tys ext_log ->
    ImplInvariant {| machine_koika_st := init_st;
                     machine_mem_st := impl_st__mem
                  |} ->
    ImplInvariant {| machine_koika_st := impl_st__koika;
                     machine_mem_st := impl_st__mem
                  |} ->
    strong_WF_state reg_type_env (commit_update impl_st__koika  koika_log) ->
    CoreSymbDefs.CorePost CoreId1 impl_st__koika (commit_update impl_st__koika koika_log)
                 (mk_sigma_fn (impl_st__mem) input)
                   ext_log ->
    dummy_interp init_st impl_st__koika (commit_update impl_st__koika koika_log)
                 sigma1
                 (Some mid_ext_log) ext_log
      (CoreSymbDefs.post_conds' CoreId0 impl_init impl_mid impl_mid_ext) ->
    ImplInvariant {| machine_koika_st := (commit_update impl_st__koika koika_log);
                     machine_mem_st := impl_st__mem |} /\
    dummy_interp init_st impl_st__koika
                         (commit_update impl_st__koika koika_log)
                         sigma2
                         (Some mid_ext_log) ext_log
                         (SymbPfChain.post_core1_exprs impl_init impl_final impl_committed_ext).
  Proof.
    intros * hwf_init hwf_sigma hwf_mid_ext_log hwf_ext_log hinv_init hinv hwf' hpost hcore0.
    set {| machine_koika_st := (commit_update impl_st__koika koika_log);
           machine_mem_st := impl_st__mem |} as final_st.
    specialize ImplInvariant_implies_spreds with (1 := hinv); intros hpres.
    specialize ImplInvariant_implies_spreds with (1 := hinv_init); intros hpres_init.
    specialize core1_step_implies' with
      (init_st := {| machine_koika_st := init_st;
                     machine_mem_st := impl_st__mem |}) (mid_ext_log := mid_ext_log) (final_st := final_st)
      (sigma2 := sigma2) (sigma1 := sigma1)
      (8 := hpres) (12 := hpost);simpl; intros hcore1.
    assert_conclusion_of hcore1 Hnew; [ | clear hcore1].
    { eapply hcore1; auto with modularity.
      eapply ImplInv_WF_state with (1 := hinv); eauto.
    }
    destruct Hnew as (hinv_final & hpost_core1).
    split_ands_in_goal.
    - apply ImplInvariant_destruct; simpl; eauto with modularity.
      specialize ImplInv_metapair with (1 := hinv); intros hwf_caches.
      specialize ImplInvariant_implies_spreds with (1 := hinv); intros hinv_spreds.
      consider CorePost.
      prop_pose_with_custom hfoo CoreTaint hpost.
      set (remove_regs _ _) as l in *. vm_compute in l.
      intros. eapply wf_cache_pair_unchanged; eauto with solve_invariants.
      * setoid_rewrite hfoo; [ solve[auto] | ].
        destruct core; solve_In_to_find'.
      * intros. setoid_rewrite hfoo; [ solve[auto] | ].
        eapply In_subset with (xs1 := map (fun r => _mid (Memory.Memory.cache_reg cache core r))
                                        (@FiniteType.finite_elements _ FT_MemCacheState)).
        { destruct cache; destruct core; vm_reflect.  }
        { rewrite in_map_iff. exists reg; split; auto.
          apply in_finite_elements.
        }
      * intros. setoid_rewrite hfoo; [solve[auto] | ].
        destruct core0; solve_In_to_find'.
      * setoid_rewrite hfoo; [solve[auto] | ].
        destruct cache; destruct core; solve_In_to_find'.
    - assumption.
  Qed.

  Lemma mem_addr_in_config_implied:
    forall core st mid_st final_st mid_log final_log s0 s1 sigma (* st' *),
    WF_state (SortedRegEnv.to_list reg_type_env) st ->
    WF_ext_log _ext_fn_tys (ext_log_app final_log mid_log) ->
    dummy_interp st mid_st final_st sigma (Some mid_log) final_log
                     (post_sm_exprs EnclaveParams.enclave_sig impl_init impl_final
                        impl_mid_ext impl_committed_ext
                        impl_get_field) ->
    st.[_rid (SecurityMonitor.SM (SecurityMonitor.state core))] <> _enum enum_core_state "Waiting" ->
    _get_field mem_input "put_valid"
             (unsafe_get_ext_call_from_log (ext_log_app final_log mid_log) (_ext ext_mainmem)) =
           Success Ob~1 ->
    _get_field mem_input "put_request"
              (unsafe_get_ext_call_from_log (ext_log_app final_log mid_log) (_ext ext_mainmem)) = Success s0 ->
    _get_field (mem_req) ("addr") s0 = Success s1 ->
    st.[_rid (SecurityMonitor.Memory Memory.Memory.turn)] = mem_core_write_turn core ->
    addr_in_config EnclaveParams.enclave_sig (to_N s1) (unsafe_enclave_data_to_config (st.[_rid (SecurityMonitor.SM (SecurityMonitor.enc_data core))])).
  Proof. (* DONE *)
    intros * hwf_st hwf_log hpost hnot_waiting hpush_valid hpush_request hreq_addr hturn.
    prop_pose_with_custom hreq0 (PfChain.CustomMem Mem_push_in_config0) hpost.
    prop_pose_with_custom hreq1 (PfChain.CustomMem Mem_push_in_config1) hpost.
    (* prop_pose_with_custom hreq1 (PfChain.Custom_PushReq1) hpost. *)
    assert (Datatypes.length s1 = addr_sz) as haddr_sz.
    { repeat unsafe_auto_simplify_structs. }
    destruct core.
    - unfold MemSymbDefs.push_req_in_config in hreq0.
      cbn - [_id interp_bits2 MemSymbDefs.fs_addr_in_range] in hreq0.
      assert_pre_and_specialize hreq0.
      { rewrite _get_field_implies_unsafe_get_field with (1 := hpush_valid); auto. }
      assert_pre_and_specialize hreq0; auto.
      eapply addr_in_config_implied; eauto.
      unsafe_auto_simplify_structs.
    - unfold MemSymbDefs.push_req_in_config in hreq1.
      cbn - [_id interp_bits2 MemSymbDefs.fs_addr_in_range] in hreq1.
      assert_pre_and_specialize hreq1.
      { rewrite _get_field_implies_unsafe_get_field with (1 := hpush_valid); auto. }
      assert_pre_and_specialize hreq1; auto.
      eapply addr_in_config_implied; eauto.
      unsafe_auto_simplify_structs.
  Qed.
  Lemma ImplInvariant_implies_mem_inv:
    forall init_st mid_st final_st ext_log1 ext_log2 sigma input,
    ImplInvariant init_st ->
    sigma = mk_sigma_fn (machine_mem_st init_st) input ->
    dummy_interp (machine_koika_st init_st) mid_st final_st sigma ext_log1 ext_log2
      (map_fst CustomMem (MemSymbDefs.mem_invariant EnclaveParams.enclave_sig impl_init impl_get_field)).
  Proof. (* DONE *)
    intros * hinv sigma. subst.
    specialize ImplInv_MemInvariant with (1 := hinv) (input := dummy_input_t).
    consider MemSymbDefs.MemPre. consider MemSymbDefs.mem_pre_conds. repeat rewrite Forall_app. unfold dummy_interp. propositional.
    apply Forall_ignore_map_fst. revert H3.
    repeat rewrite<-forall_preprocess_fancy_spreds_correct.
    apply forall_interp_spred_package_equiv; solve_package_equiv.
  Qed. (* DONE *)

  Lemma mem_push_in_config_implied:
    forall init_st mid_st st mid_log final_log mem sigma,
    WF_ext_log _ext_fn_tys mid_log ->
    WF_ext_log _ext_fn_tys final_log ->
    ImplInvariant {| machine_koika_st := init_st;
                     machine_mem_st := mem
                  |} ->
    dummy_interp init_st mid_st st sigma (Some mid_log) final_log
                     (post_sm_exprs EnclaveParams.enclave_sig impl_init impl_final
                        impl_mid_ext impl_committed_ext
                        impl_get_field) ->
    mem_push_in_config init_st (unsafe_get_ext_call_from_log (ext_log_app final_log mid_log) (_ext ext_mainmem)).
  Proof.
    intros * hwf_mid_log hwf_final_log hinv hpost.
    specialize ImplInv_WF_state with (1 := hinv); intros hwf; simpl in hwf.
    unfold mem_push_in_config, is_mem_core0_push_turn, is_mem_core1_push_turn.
    specialize ImplInvariant_implies_mem_inv with
      (1 := hinv) (mid_st := mid_st) (final_st := st) (ext_log1 := Some mid_log) (ext_log2 := final_log).
    intros hmem_inv.
    specialize ImplInvariant_implies_sm_inv with
      (1 := hinv) (mid_st := mid_st) (final_st := st) (ext_log1 := Some mid_log) (ext_log2 := final_log).
    intros hsm_inv.

    evar (sigma': @ext_sigma_t N).
    evar (input': @input_t).
    specialize (hmem_inv sigma' input'). specialize hmem_inv with (1 := eq_refl).
    specialize (hsm_inv sigma' input'). specialize hsm_inv with (1 := eq_refl).
    consider dummy_interp.
    unfold get_ghost_running_config, machine_st_to_ghost_core, mem_addr_in_option_config, ImplDefs.mem_addr_in_option_config, get_valid_addr_from_push_req.
    intros. destruct_all_matches; simplify.
    - prop_pose_with_custom hmem_zero (PfChain.CustomMem Mem_push_zero0) hpost.
      prop_pose_with_custom hsm_waiting (PfChain.CustomSM (SM_inv_waiting CoreId0)) hsm_inv.
      prop_pose_with_custom hmem_purged (CustomMem (Mem_purged0)) hmem_inv.
      cbn - [_id In mem_regs_to_reset] in hsm_waiting, hmem_purged, Heqb1, hmem_zero.
      consider @mem_core0_write_turn. propositional.
      exfalso.
      assert (init_st.[_id (_mid (Memory.Memory.cache_imem0 Memory.CacheState.cache_fsm))]  = Ob~0~0~0) as hifsm.
      { rewrite hmem_purged; [reflexivity | ] .
        solve_In_to_find.
      }
      assert (init_st.[_id (_mid (Memory.Memory.cache_dmem0 Memory.CacheState.cache_fsm))]  = Ob~0~0~0) as hdfsm.
      { rewrite hmem_purged; [reflexivity | ] .
        solve_In_to_find.
      }
      assert_conclusion_of hmem_zero hfalse.
      { apply hmem_zero; auto. }
      unfold unsafe_get_field in hfalse.
      setoid_rewrite Heqr0 in hfalse. discriminate.
    - consider mem_addr_in_option_config.
      consider addr_in_config.
      eapply mem_addr_in_config_implied with (3 := hpost);eauto with modularity.
    - prop_pose_with_custom hmem_zero (PfChain.CustomMem Mem_push_zero1) hpost.
      prop_pose_with_custom hsm_waiting (PfChain.CustomSM (SM_inv_waiting CoreId1)) hsm_inv.
      prop_pose_with_custom hmem_purged (CustomMem (Mem_purged1)) hmem_inv.
      cbn - [_id In mem_regs_to_reset] in hsm_waiting, hmem_purged,  hmem_zero.
      consider @mem_core1_write_turn. propositional.
      exfalso.
      assert (init_st.[_id (_mid (Memory.Memory.cache_imem1 Memory.CacheState.cache_fsm))]  = Ob~0~0~0) as hifsm.
      { rewrite hmem_purged; [reflexivity | ] .
        solve_In_to_find.
      }
      assert (init_st.[_id (_mid (Memory.Memory.cache_dmem1 Memory.CacheState.cache_fsm))]  = Ob~0~0~0) as hdfsm.
      { rewrite hmem_purged; [reflexivity | ] .
        solve_In_to_find.
      }
      assert_conclusion_of hmem_zero hfalse.
      { apply hmem_zero; auto. }
      unfold unsafe_get_field in hfalse.
      setoid_rewrite Heqr0 in hfalse. discriminate.
    - consider mem_addr_in_option_config.
      consider addr_in_config.
      eapply mem_addr_in_config_implied with (3 := hpost);eauto with modularity.
    - prop_pose_with_custom hmem_zero (PfChain.CustomMem Mem_push_zero_both) hpost.
      cbn - [_id] in hmem_zero.
      propositional. setoid_rewrite hmem_zero.
      unfold MemSymbDefs.almost_zeroed_mainmem_call.
      auto.
      Unshelve.
      exact dummy_input_t.
  Qed.

End PfChainHelpers.
