Require Import rv_cache_isolation.Common.
Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.Utils.
Require Import FunctionalExtensionality.
(* Require Import koikaExamples.EnclaveWithCache.ProofCore_symb. *)
Require Import koikaExamples.EnclaveWithCache.ExtractionUtils.
(* Require Import koikaExamples.EnclaveWithCache.ScheduleEquiv. *)
Create HintDb solve_invariants.
Create HintDb modularity.

Definition assert_ext_fns_empty {X}
  (extfn: debug_id_ty -> sval) (debug_fn: debug_id_ty -> X)
  (fns: list ext_fn_t) : list (X* fancy_spred) :=
  map (fun (fn: ext_fn_t) => (debug_fn (_extid fn), {{{ `extfn (_extid fn)` = #(zeroes (unsafe_get_ext_fn_arg_type (_ext fn))) }}}))
      fns.

Ltac specialize_symbolic_evaluate_file_success _vm_file _file :=
  specialize symbolic_evaluate_file_success with (file := _vm_file);
  compute_change (file_machines _vm_file) (_file.(file_machines));
  compute_change (file_assumptions _vm_file) (_file.(file_assumptions));
  compute_change (file_assertions _vm_file) (_file.(file_assertions)).


Ltac unsafe_weaken_strong_WF:=
  repeat match goal with
  | H: strong_WF_state _ _ |- _ => apply strong_WF_state_weaken in H
  end.
Ltac change_Forall_lists1 H :=
  match type of H with
  | Forall _ ?xs =>
      match goal with
      | |- Forall _ ?ys => compute_change xs ys
      end
  end.
Ltac custom_unsafe_auto_simplify_structs :=
  match goal with
  | |- _ => fail
  end.
Ltac unsafe_auto_simplify_structs :=
  match goal with
  | |- context [ match _struct_init ?struct_def ?fields with
                 | _ => _
                 end ] =>
      let H := fresh in simplify_structs_as H
  | |- context [ match struct_init ?struct_def ?fields with
                 | _ => _
                 end ] =>
      let H := fresh in unsafe_simplify_structs_as H;
      assert_pre_and_specialize H
  | |- context [ match _get_field ?fields ?_fld ?req with
                 | _ => _
                 end ] =>
      let H := fresh in unsafe_simplify_structs_as H;
      assert_pre_and_specialize H
  | |- context [ match get_field ?fields ?_fld ?req with
                 | _ => _
                 end ] =>
      let H := fresh in unsafe_simplify_structs_as H;
      assert_pre_and_specialize H
  | H: get_field ?fields ?_fld ?req = Success ?s|-  Datatypes.length ?s = _ =>
      let H' := fresh in
      specialize get_field_success with (EqDec := EqDec_debug_id_ty) (flds := fields) (
       fld := _fld) (v := req) (2 := eq_refl); intros H'; rewrite H in H'; apply H'
  | H: unsafe_get_field ?flds ?fld ?v = ?x,
    H1: get_field ?flds ?fld ?v = Success ?y |- _ =>
    let H' := fresh in
    assert (x = y) by (apply unsafe_get_field_eq with (1 := H) (2 := H1)); subst
  | H: get_field ?flds ?fld ?v = Success ?y |-
      unsafe_get_field ?flds2 ?fld ?v = ?x =>
      unfold unsafe_get_field; setoid_rewrite H
  | H: get_field _ ?fld ?v = Success _,
    H1: context[unsafe_get_field _ ?fld ?v] |- _ =>
      setoid_rewrite unsafe_get_field_eq' with (1 :=H) in H1
  | H: get_field _ ?fld ?v = Success _
    |- context[unsafe_get_field _ ?fld ?v] =>
      setoid_rewrite unsafe_get_field_eq' with (1 :=H)
  | H:WF_state _ ?st
    |- Datatypes.length ?st.[?reg] = _ => solve
    [ eapply WF_state_length'; eauto ]
  | |- _ =>
    custom_unsafe_auto_simplify_structs
end.
Ltac step_modular_schedule hinterp new_step new_st new_log :=
  rewrite interp_modular_schedule'_cons in hinterp;
  destruct_matches_in_hyp_as hinterp new_step; [ | congruence];
  match type of new_step with
  | interp_scheduler ?sigma _ _ ?koika_st _ ?schedule = Success ?log =>
      rename log into new_log;
      set (commit_update koika_st (Log__koika new_log)) as new_st in *
  end.
Ltac specialize_spec fn HPre HPost impl_step _ghost hwf_impl' hwf_impl_ext' :=
    pose proof fn as HPost; unfold interp_scheduler_satisfies_spec in HPost;
    match type of impl_step with
    | interp_scheduler ?_sigma _ _ ?_st ?rules ?sched  = Success ?_log=>
        specialize HPost  with (sigma := _sigma) (st := _st) (log := _log)
    end;
    match type of HPost with
    | _ -> _ -> _ -> _ ->  ?impl = Success _ ->  _ =>
      match type of impl_step with
      | ?impl0 = Success ?log=>
          replace (impl) with (impl0) in HPost
              (* by (apply interp_scheduler_setoid_eq; repeat constructor) *)
      end;
      [ specialize HPost with (5 := impl_step) (1 := _ghost);
        do 2 (assert_pre_and_specialize HPost; [solve[(eauto with solve_invariants)] | ]);
        (assert_pre_and_specialize HPost; [ vm_compute; reflexivity| ]) ;
        assert_pre_as HPre HPost;
        [ | specialize HPost with (1 := HPre); destruct HPost as (hwf_impl' & hwf_impl_ext' & HPost)]
      | ]
    end.

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


Lemma unsafe_get_ext_call_from_log_app_empty_r:
  forall log1 log2 fn,
  WF_ext_log _ext_fn_tys log1 ->
  unsafe_get_ext_call_from_log log2 fn = zeroes (unsafe_get_ext_fn_arg_type fn) ->
  unsafe_get_ext_call_from_log (ext_log_app log1 log2) fn =
  unsafe_get_ext_call_from_log log1 fn.
Proof.
  consider ext_log_app. consider unsafe_get_ext_call_from_log.
  consider SemanticUtils.unsafe_get_ext_call_from_log.
  intros. rewrite SortedExtFnEnv.opt_get_mapV.
  rewrite SortedExtFnEnv.opt_get_zip_default.
  consider unsafe_get_ext_fn_arg_type.
  destruct_all_matches; auto.
  consider WF_ext_log. specialize H with (1 := Heqo). propositional.
  consider SemanticUtils.unsafe_get_ext_fn_arg_type.
  setoid_rewrite H0.
  rewrite or_zeroes. auto.
Qed.
