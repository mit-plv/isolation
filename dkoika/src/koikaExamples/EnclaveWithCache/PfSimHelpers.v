Require Import rv_cache_isolation.Common.
Require Import rv_cache_isolation.SecurityMonitor.

Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.Utils.
Require Import koikaExamples.EnclaveWithCache.ProofUtils.
Require Import koikaExamples.EnclaveWithCache.ExtractionUtils.
Require Import koikaExamples.EnclaveWithCache.PfDefs.
Require Import koikaExamples.EnclaveWithCache.PfSim_sig.
Require Import koikaExamples.EnclaveWithCache.Impl.

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

Module EnclaveParamUtils (EnclaveParams: EnclaveParams_sig).
  Import SymbSimDefs.
  Import TopLevelModuleHelpers.
  Notation addr_in_config := (addr_in_config EnclaveParams.enclave_sig).
 Lemma enclave_vect_to_enclave_id:
  forall eid default value,
    Datatypes.length value = 2 ->
    eid = success_or_default (eid_vect_to_enclave_id value) default ->
    value = enclave_id_to_vect eid.
Proof.
  intros. consider eid_vect_to_enclave_id.
  destruct value; [discriminate |] .
  destruct value; [discriminate | ].
  destruct value; [ | discriminate].
  destruct b; destruct b0; simpl in *; subst; auto.
Qed.
 Definition lookup_field_sz (s: @struct_t debug_id_ty) (fld: string) : result nat unit :=
  match find (fun '(f, _) => beq_dec (fst f) fld) s.(dstruct_fields) with
  | Some (_, sz) => Success sz
  | None => Failure tt
  end.
  Definition _unsafe_lookup_field_sz (s: Types.struct_sig) (fld: string) : nat :=
    success_or_default (let/res sdef := _lookup_struct s in
                        get_field_width (dstruct_fields sdef) (unsafe_lookup_field_idx sdef fld)
                        ) 0.
Lemma length_unsafe_get_field:
  forall sdef fld v width,
  Datatypes.length v = _unsafe_struct_sz sdef ->
  match lookup_struct (Types.struct_name sdef) with
  | Success s =>
      match get_field_width s.(dstruct_fields) (_fld sdef fld) with
      | Success width => Success width
      | _ => Failure tt
      end
  | _ => Failure tt
  end = Success width ->
  Datatypes.length (_unsafe_get_field sdef fld v) = width.
Proof.
  unfold _unsafe_get_field, _unsafe_lookup_field_sz.
  intros. consider _get_field. consider get_field. consider _lookup_struct.
  bash_destruct H0; simpl; auto.
  - eapply get_field_success in Heqr1; eauto.
    + simplify.
      consider @unsafe_lookup_field_idx. consider _fld. consider _lookup_struct.
      setoid_rewrite Heqr0 in Heqr2. consider lookup_dstruct_field. consider lookup_field_idx.
      setoid_rewrite Heqr2. auto.
    + consider _unsafe_struct_sz. consider struct_sz. simplify.
      consider _lookup_struct. rewrite Heqr0 in H. simpl in H. rewrite H.
      auto.
Qed.
Lemma sel_ok:
  forall v idx default,
  PeanoNat.Nat.ltb (to_nat idx) (Datatypes.length v) = true ->
  sel v idx   = Success (nth (to_nat idx) v default).
Proof.
  unfold sel. propositional. simpl_match. consider @opt_result.
  destruct_match; auto.
  - eapply nth_error_nth with (d := default) in Heqo; eauto. rewrite_solve.
  - rewrite nth_error_None in Heqo. rewrite PeanoNat.Nat.ltb_lt in H. lia.
Qed.

Ltac addr_not_in_config_simplify :=
  match goal with
  (* | H: nth _ ?v _ = _ *)
  (*   |- context[sel ?v _] => *)
  (*     rewrite sel_correct with (default := false); auto; [ setoid_rewrite H | ] *)
  | H: _ = success_or_default (eid_vect_to_enclave_id ?v) _ |- ?v = _ =>
      apply enclave_vect_to_enclave_id with (2 := H)
  | H: _ && _ = true |- _ =>
      rewrite andb_true_iff in H
  | |- Datatypes.length (_unsafe_get_field ?sdef ?fld ?v) = ?width =>
     apply length_unsafe_get_field with (2 := eq_refl)
  | H: (_ <=? _)%N = true |- _ =>
      rewrite N.leb_le in H
  | |- success_or_default (bitfun_of_predicate unsigned_le _ _ )Ob = Ob~1 =>
      rewrite<-bitfun_unsigned_le_iff
  | |- success_or_default (bitfun_of_predicate unsigned_lt _ _ )Ob = Ob~1 =>
      rewrite<-bitfun_unsigned_lt_plus
  | |- context[Datatypes.length (_enclave_base EnclaveParams.enclave_sig _)] =>
      rewrite wf_enclave_base with (1 := EnclaveParams.wf_sig)
  | |- context[Datatypes.length (_enclave_size EnclaveParams.enclave_sig _)] =>
      rewrite wf_enclave_size with (1 := EnclaveParams.wf_sig)
  | |- context[Datatypes.length (_shared_region_base EnclaveParams.enclave_sig _)] =>
      rewrite wf_shared_base with (1 := EnclaveParams.wf_sig)
  | |- context[Datatypes.length (_shared_region_size EnclaveParams.enclave_sig )] =>
      rewrite wf_shared_size with (1 := EnclaveParams.wf_sig)

  | |- ?x = Datatypes.length _ =>
      lazymatch x with
      | Datatypes.length _ => fail
      | _ => symmetry
      end
| H: shared_vect_to_shared_regions _ _ = true
  |- success_or_default (let/res b := sel _ _ in Success [b]) _ = _ =>
  rewrite sel_ok with (default := false); consider shared_vect_to_shared_regions;
  [ setoid_rewrite H; reflexivity |]
  | H0: ?x <> of_nat 2 0,
    H1: ?x <> of_nat 2 1,
    H2: ?x <> of_nat 2 2
    |- ?x = Ob~1~1 =>
      let H := fresh in
      assert (Datatypes.length x = 2) as H; [ | apply case_doubleton_bits in H; split_ors_in H; auto; contradiction]
  | |- _ => progress (simplify; propositional)
  end.

  Lemma addr_not_in_config_implies:
    forall core init_st final_st sigma ext_log,
    WF_ext_log _ext_fn_tys ext_log ->
    WF_state (SortedRegEnv.to_list reg_type_env) init_st ->
    interp_fancy_spred (dummy_pkg init_st init_st final_st sigma None ext_log)
                       (fs_addr_not_in_config EnclaveParams.enclave_sig core impl_init impl_get_field impl_final_ext) ->
    match get_valid_addr_from_push_req
        (unsafe_get_ext_call_from_log ext_log (_ext ext_mainmem)) with
    | Some addr =>
        addr_in_config (to_N addr) (unsafe_enclave_data_to_config
                                      init_st.[_rid (SM (enc_data core))]) -> False
    | None => True
    end.
  Proof.
    intros * hwf_st hwf_ext hpred.
    destruct_match; auto.
    consider get_valid_addr_from_push_req; simplify. bash_destruct Heqo. simplify.
    cbn - [_id dstruct_fields _sid _fld] in hpred.
    assert_pre_and_specialize hpred.
    { unsafe_auto_simplify_structs; auto. }
    unfold addr_in_config in *. propositional.
    apply hpred. clear hpred.
    destruct region.
    - destruct eid;
        [ left | right; left | right; right; left | right; right; right; left].
      all: simpl in H1; cbn - [_id _sid unsafe_enclave_id_vect_to_eid] in H2;
           consider _smid; consider _rid.
      all: split_ands_in_goal; simplify; auto; destruct core;
          repeat addr_not_in_config_simplify; repeat unsafe_auto_simplify_structs; auto.
    - assert (Datatypes.length init_st.[_id (reg_to_debug_id (SM (enc_data core)))] =
                                               (_unsafe_struct_sz enclave_data)) as hlen.
      { destruct core; unsafe_auto_simplify_structs. }
      consider _smid. consider _rid.
        simpl in H1; cbn - [_id _sid unsafe_enclave_id_vect_to_eid] in H2; do 4 right;
          set (init_st.[_]) as enc_data in *;
        epose proof (eta_expand_list_correct false _) as hdata_enc;
        erewrite hlen in hdata_enc; cbn in hdata_enc;  destruct id;
        [ left | right; left | right; right; left | right; right; right; left |
          right; right; right; right; left  |
          right; right; right; right; right ].
        all: split_ands_in_goal; simplify; auto;
          repeat addr_not_in_config_simplify; repeat unsafe_auto_simplify_structs; auto.
        all: rewrite hdata_enc; vm_reflect.
    - discriminate.
  Qed.
End EnclaveParamUtils.
