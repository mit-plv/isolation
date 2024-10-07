Require Import rv_isolation.Common.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
(* Require Import koikaExamples.Enclaves.TypeDefs. *)
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
Require Import FunctionalExtensionality.
(* Require Import koikaExamples.Enclaves.ProofCore_symb. *)
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koikaExamples.Enclaves.ScheduleEquiv.
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
