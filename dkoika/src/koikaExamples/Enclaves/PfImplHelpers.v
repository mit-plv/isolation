Require Import rv_isolation.Common.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
Require Import koikaExamples.Enclaves.ProofUtils.
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koikaExamples.Enclaves.PfDefs.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.ProofCore_symb.
Require Import koikaExamples.Enclaves.SmProofs.
Require Import koikaExamples.Enclaves.MemoryProofs.
Require Import koikaExamples.Enclaves.PfChain.
Require Import koikaExamples.Enclaves.PfSim_sig.

Import Utils.PfHelpers.
Import TopLevelModuleHelpers.
Ltac init_interp:=
  repeat match goal with
  | |- dummy_interp _ _ _ _ _ _ =>
      unfold dummy_interp, dummy_pkg
  | |- Forall (fun '(_, p) => interp_fancy_spred _ _) _  =>
    rewrite<-forall_preprocess_fancy_spreds_correct
  end.
Ltac init_interp_in H:=
  repeat match type of H with
  | dummy_interp _ _ _ _ _ _ =>
      unfold dummy_interp, dummy_pkg in H
  | Forall (fun '(_, p) => interp_fancy_spred _ _) _  =>
    rewrite<-forall_preprocess_fancy_spreds_correct in H
  end.

  Definition ImplInvariant_spreds enclave_sig st :=
    CoreSymbDefs.CorePre CoreId0 (machine_koika_st st) /\
    CoreSymbDefs.CorePre CoreId1 (machine_koika_st st) /\
    (forall input, MemSymbDefs.MemPre (machine_koika_st st) (mk_sigma_fn (machine_mem_st st) input)) /\
    (forall input, SMSymbDefs.SMPre enclave_sig (machine_koika_st st) (mk_sigma_fn (machine_mem_st st) input)).

  Lemma ImplInvariant_spreds_implies:
    forall init_st mid_st final_st sigma ext_log1 ext_log2 enclave_sig input,
      sigma = mk_sigma_fn (machine_mem_st init_st) input ->
      ImplInvariant_spreds enclave_sig init_st ->
      (dummy_interp (machine_koika_st init_st) mid_st final_st sigma ext_log1 ext_log2 (SymbPfChain.invariant_spreds' enclave_sig impl_init impl_get_field) /\
       dummy_interp (machine_koika_st init_st) mid_st final_st sigma ext_log1 ext_log2 (map_fst CustomMem (MemSymbDefs.mem_pre_conds' impl_init impl_get_field))).
  Proof.
    intros * sigma hinv. subst.
    consider dummy_interp. consider SymbPfChain.invariant_spreds'.
    repeat rewrite Forall_app.
    consider ImplInvariant_spreds.
    destruct hinv as (hcore0 & hcore1 & hmem & hsm).
    consider CoreSymbDefs.CorePre.
    consider CoreSymbDefs.CorePre.
    consider MemSymbDefs.MemPre. consider SMSymbDefs.SMPre.
    split_ands_in_goal.
    - clear - hcore0. unfold dummy_pkg.
      apply Forall_ignore_map_fst.
      revert hcore0. unfold dummy_pkg.
      repeat rewrite Forall_map_snd.
      apply forall_interp_fancy_spred_package_equiv'; solve_package_equiv.
    - clear - hcore1. unfold dummy_pkg.
      apply Forall_ignore_map_fst.
      revert hcore1. unfold dummy_pkg.
      repeat rewrite Forall_map_snd.
      apply forall_interp_fancy_spred_package_equiv'; solve_package_equiv.
    - clear - hmem.
      specialize hmem with (input := input).
      consider MemSymbDefs.mem_pre_conds. rewrite Forall_app in hmem. split_ands_in_hyps.
      unfold dummy_pkg. apply Forall_ignore_map_fst.
      revert hmem1.
      repeat rewrite Forall_map_snd.
      apply forall_interp_fancy_spred_package_equiv'; solve_package_equiv.
    - clear - hsm.
      specialize hsm with (input := input).
      consider SMSymbDefs.sm_pre_conds. rewrite Forall_app in hsm. split_ands_in_hyps.
      unfold dummy_pkg. apply Forall_ignore_map_fst.
      revert hsm1.
      repeat rewrite Forall_map_snd.
      apply forall_interp_fancy_spred_package_equiv'; solve_package_equiv.
    - clear - hmem. specialize hmem with (input := input). unfold dummy_pkg.
      consider MemSymbDefs.mem_pre_conds. rewrite Forall_app in hmem. split_ands_in_hyps.
      apply Forall_ignore_map_fst. revert hmem0.
      repeat rewrite Forall_map_snd.
      apply forall_interp_fancy_spred_package_equiv'; solve_package_equiv.
  Qed.
Lemma mainmem_ignores_input:
  forall input0 input1 arg mem,
  unsafe_call_ext (mk_sigma_fn mem input0) (_id (_extid ext_mainmem)) arg  =
  unsafe_call_ext (mk_sigma_fn mem input1) (_id (_extid ext_mainmem)) arg.
Proof.
  reflexivity.
Qed.


  Lemma ImplInvariant_spreds_implied:
    forall init_st mid_st final_st sigma ext_log1 ext_log2 enclave_sig input,
      sigma = mk_sigma_fn (machine_mem_st init_st) input ->
      dummy_interp (machine_koika_st init_st) mid_st final_st sigma ext_log1 ext_log2 (SymbPfChain.invariant_spreds' enclave_sig impl_init impl_get_field) ->
      dummy_interp (machine_koika_st init_st) mid_st final_st sigma ext_log1 ext_log2
        (map_fst CustomMem (MemSymbDefs.mem_pre_conds' impl_init impl_get_field)) ->
      ImplInvariant_spreds enclave_sig init_st.
  Proof.
    intros * sigma hinv hmem_pre. subst.
    consider dummy_interp. consider SymbPfChain.invariant_spreds'.
    repeat rewrite Forall_app in hinv.
    destruct hinv as (hcore0 & hcore1 & hmem & hsm).
    consider ImplInvariant_spreds.
    consider CoreSymbDefs.CorePre.
    consider CoreSymbDefs.CorePre.
    - split_ands_in_goal; auto.
      + apply Forall_ignore_map_fst in hcore0.
        init_interp_in hcore0. init_interp.
        revert hcore0. unfold dummy_pkg.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      + apply Forall_ignore_map_fst in hcore1.
        init_interp_in hcore1. init_interp.
        revert hcore1. unfold dummy_pkg.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      + consider MemSymbDefs.MemPre. intros.
        unfold MemSymbDefs.mem_pre_conds. rewrite Forall_app. split.
        * clear - hmem_pre. consider MemSymbDefs.mem_pre_conds'. cbn - [_id] in hmem_pre. cbn - [_id].
          repeat rewrite Forall_cons_iff in hmem_pre. propositional.
        * clear - hmem. apply Forall_ignore_map_fst in hmem.
          intros.  consider MemSymbDefs.MemPre. consider MemSymbDefs.mem_pre_conds.
          revert hmem.
          repeat rewrite Forall_map_snd. unfold dummy_pkg.
          apply forall_interp_fancy_spred_package_equiv'; solve_package_equiv.
      + apply Forall_ignore_map_fst in hsm.
        intros.  consider SMSymbDefs.SMPre. consider SMSymbDefs.sm_pre_conds.
        rewrite Forall_app. split; [constructor | ].
        revert hsm.
        repeat rewrite Forall_map_snd. unfold dummy_pkg.
        apply forall_interp_fancy_spred_package_equiv'; solve_package_equiv.
  Qed.
Ltac replace_sigma v :=
  match goal with
  | |- Forall (fun p => interp_spred ?package p) _ =>
    apply forall_interp_spred_package_equiv with
      (pkg1 := set_sigma package v)
  end.

Lemma ImplInvariant_spreds_implies_invariant_spreds'_init:
  forall st ext_log mid_log mid_st final_st enclave_sig sigma,
  ImplInvariant_spreds enclave_sig st ->
  Forall
    (fun p : spred =>
     interp_spred
       {|
         pkg_machine := dummy_machine;
         pkg_init_st := machine_koika_st st;
         pkg_sigma := sigma;
         pkg_mid_st := Some mid_st;
         pkg_final_st := final_st;
         pkg_mid_ext_log := mid_log;
         pkg_ext_log' := ext_log
       |} p) (preprocess_fancy_spreds (SymbPfChain.invariant_spreds' enclave_sig impl_init impl_get_field)).
Proof.
  intros.
  eapply ImplInvariant_spreds_implies in H; propositional.
  unfold dummy_interp, dummy_pkg in H0.
  (* rewrite forall_preprocess_fancy_spreds_correct. *)
  replace_sigma (mk_sigma_fn (machine_mem_st st) dummy_input_t).
  { solve_package_equiv. }
   rewrite forall_preprocess_fancy_spreds_correct.
  eauto.
Qed.


Lemma ImplInvariant_spreds_implies_invariant_spreds'_init':
  forall st st' mid_st mid_log ext_log sigma sigma' enclave_sig mid_st' final_st' mid_log' ext_log' ,
    Forall
          (fun p : spred =>
           interp_spred
             {|
               pkg_machine := dummy_machine;
               pkg_init_st := st';
               pkg_sigma := sigma;
               pkg_mid_st := mid_st;
               pkg_final_st := st;
               pkg_mid_ext_log :=  mid_log ;
               pkg_ext_log' := ext_log
             |} p)
          (preprocess_fancy_spreds (SymbPfChain.invariant_spreds' enclave_sig impl_final impl_get_field)) ->
  dummy_interp st  mid_st' final_st'
    sigma' mid_log' ext_log'
    (SymbPfChain.invariant_spreds' enclave_sig impl_init impl_get_field).
Proof.
  intros; unfold dummy_interp, dummy_pkg.
  init_interp.
  replace_init_st_in H st; [ | solve_package_equiv].
  rewrite Lift_Forall with (g := replace_spred_final_reg_with_init) in H.
  2: { intros. apply replace_fancy_spred_final_reg_with_init_correct with (p := PBase p); auto. }
  change_Forall_lists1 H. revert H.
  repeat rewrite<-forall_preprocess_fancy_spreds_correct.
  apply forall_interp_spred_package_equiv; solve_package_equiv.
Qed.

Lemma ImplInvariant_spreds_implies_invariant_spreds'_mid:
  forall ext_log mid_log mid_st final_st enclave_sig init_st input,
  ImplInvariant_spreds enclave_sig mid_st ->
  Forall
    (fun p : spred =>
     interp_spred
       {|
         pkg_machine := dummy_machine;
         pkg_init_st := init_st;
         pkg_sigma := mk_sigma_fn (machine_mem_st mid_st) input;
         pkg_mid_st := Some (machine_koika_st mid_st);
         pkg_final_st := final_st;
         pkg_mid_ext_log := mid_log;
         pkg_ext_log' := ext_log
       |} p) (preprocess_fancy_spreds (SymbPfChain.invariant_spreds' enclave_sig impl_mid impl_get_field)).
Proof.
  intros.
  eapply ImplInvariant_spreds_implies with (mid_st := machine_koika_st mid_st) (final_st:= final_st) (input := input) (ext_log1 := mid_log) (ext_log2 := ext_log) in H; propositional.
  unfold dummy_interp, dummy_pkg in H0.
  replace_init_st (machine_koika_st mid_st); [solve_package_equiv | ].
  init_interp_in H0.
  rewrite Lift_Forall with (g := replace_spred_init_reg_with_mid) in H0.
  2: { intros. apply replace_fancy_spred_init_reg_with_mid_correct with (p := PBase p); auto. }
  change_Forall_lists1 H0.
  revert H0.
  apply forall_interp_spred_package_equiv; solve_package_equiv.
Qed.

Lemma ImplInvariant_spreds_impl_mem_pre:
  forall input st enclave_sig,
  ImplInvariant_spreds enclave_sig st ->
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
     |} p) (MemSymbDefs.mem_pre_conds' impl_init impl_get_field).
Proof.
  intros * (hcore0 & hcore1 & hmem & hsm).
  consider MemSymbDefs.MemPre. specialize (hmem input).
  consider MemSymbDefs.mem_pre_conds. rewrite Forall_app in hmem. propositional.
Qed.

Lemma mem_pre_conds_implied:
  forall st st' ext_log input enclave_sig mid_log,
  ImplInvariant_spreds enclave_sig st ->
  machine_mem_st st' = machine_mem_st st ->
  (machine_koika_st st').[_id (_mid Memory.Memory.SHReq)] =  (machine_koika_st st).[_id (_mid Memory.Memory.SHReq)] ->
  (machine_koika_st st').[_id (_mid Memory.Memory.turn)] =  (machine_koika_st st).[_id (_mid Memory.Memory.turn)] ->
  dummy_interp (machine_koika_st st') (machine_koika_st st) (machine_koika_st st')
    (mk_sigma_fn (machine_mem_st st') input) (Some mid_log) ext_log
    (map_fst PfChain.CustomMem (MemSymbDefs.mem_pre_conds' impl_init impl_get_field)).
Proof.
  intros * hinv hmemeq hshreq hturn.
  apply ImplInvariant_spreds_impl_mem_pre with (input := input) in hinv.
  consider MemSymbDefs.mem_pre_conds'.
  unfold dummy_interp. cbn - [_id].
  repeat rewrite Forall_cons_iff in hinv. split_ands_in_hyps.
  rewrite hmemeq.
  repeat constructor.
  - cbn - [_id _sid _fld mk_sigma_fn].
    cbn - [_id _sid _fld mk_sigma_fn] in hinv0.
    rewrite hshreq. rewrite hturn. auto.
  - cbn - [_id _sid _fld mk_sigma_fn].
    cbn - [_id _sid _fld mk_sigma_fn] in hinv2.
    rewrite hshreq. rewrite hturn. auto.
Qed.

Lemma enclave_id_beq_false_iff:
  forall x y,
  enclave_id_beq x y = false <-> x <> y.
Proof.
  consider enclave_id_beq. destruct x; destruct y; split; propositional; discriminate.
Qed.
Lemma finish_disjoint:
  forall v0 v1,
  Datatypes.length v0 = _unsafe_struct_sz enclave_data ->
  Datatypes.length v1 = _unsafe_struct_sz enclave_data ->
  config_ext_finish (unsafe_enclave_data_to_config v0) && config_ext_finish (unsafe_enclave_data_to_config v1) = false ->
  success_or_default (interp_bits2 And (_unsafe_get_field enclave_req "ext_finish" (_unsafe_get_field enclave_data "data" v0))
(_unsafe_get_field enclave_req "ext_finish" (_unsafe_get_field enclave_data "data" v1))) Ob = Ob~0.
Proof.
  intros * hlen0 hlen1 hconflict.
  consider unsafe_enclave_data_to_config. consider config_ext_uart.
  repeat rewrite and_false_iff in hconflict.
  pose proof (eta_expand_list_correct false v0) as hdata0. rewrite hlen0 in hdata0.
  pose proof (eta_expand_list_correct false v1) as hdata1. rewrite hlen1 in hdata1.
  rewrite hdata0 in *. rewrite hdata1 in *. cbn. cbn in hconflict.
  rewrite andb_false_iff in hconflict.
  repeat match goal with
  | |- [ ?x && _] = _ =>
      destruct x; simpl; auto
  | |- [ nth ?x ?y ?z] = _ =>
      destruct (nth x y z)
  end; split_cases; simplify; auto.
Qed.
Lemma unsafe_enclave_eid_eq:
  forall (data1 data2 : list bool),
    Datatypes.length data1 = _unsafe_struct_sz enclave_data ->
    Datatypes.length data2 = _unsafe_struct_sz enclave_data ->
    unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid enclave_req)) (_fld enclave_req "eid")
      (unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid enclave_data))
         (_fld enclave_data "data") data1) =
    unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid enclave_req)) (_fld enclave_req "eid")
      (unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid enclave_data))
         (_fld enclave_data "data") data2) ->
    config_eid (unsafe_enclave_data_to_config data1) = config_eid (unsafe_enclave_data_to_config data2).
Proof.
  intros * hlen1 hlen2 heq.
  set (_unsafe_struct_sz _) as len in *. vm_compute in len. subst len.
  pose proof (eta_expand_list_correct false data1) as hdata1.
  pose proof (eta_expand_list_correct false data2) as hdata2.
  rewrite hlen1 in hdata1.
  rewrite hlen2 in hdata2.
  cbn in hdata1. rewrite hdata1 in *.
  cbn in hdata2. rewrite hdata2 in *.
  simpl.
  _vm_simplify.
    destruct_with_eqn (nth 0 data1 false); destruct_with_eqn (nth 1 data1 false);
    destruct_with_eqn (nth 0 data2 false); destruct_with_eqn (nth 1 data2 false); try reflexivity.
    all: cbv in heq; discriminate.
Qed.
  Definition enc_data' core st :=
    (_unsafe_get_field enclave_data ("data")
       st.[_rid (SecurityMonitor.SM (SecurityMonitor.enc_data core))]).
  Lemma not_owns_uart_implies :
    forall st core extract_rf,
    WF_state (SortedRegEnv.to_list reg_type_env) st ->
    owns_uart (get_impl_config st core extract_rf)  = false ->
     (st.[_rid (SecurityMonitor.SM (SecurityMonitor.state core))] = (_enum enum_core_state "Waiting") \/
     _unsafe_get_field enclave_req "ext_uart" (enc_data' core st) = Ob~0).
  Proof.
    unfold get_impl_config, get_ghost_running_config, machine_st_to_ghost_core.
    intros * hwf H. unfold owns_uart, owns_led, enc_data' in *. propositional.
    bash_destruct H; simplify; propositional; simplify; try split; auto.
    right. unfold not in *.
    match goal with
    | |- ?x = _ =>
        assert (Datatypes.length x = 1) as hlen
    end.
    { consider _unsafe_get_field. consider @success_or_default.
      unsafe_auto_simplify_structs; [ | simplify; auto].
      unsafe_auto_simplify_structs; [ | simplify; auto].
      destruct core; unsafe_auto_simplify_structs.
    }
    apply case_singleton_bv in hlen. split_ors_in hlen; propositional.
  Qed.
  Lemma not_owns_led_implies :
    forall st core extract_rf,
    WF_state (SortedRegEnv.to_list reg_type_env) st ->
    owns_led (get_impl_config st core extract_rf)  = false ->
     (st.[_rid (SecurityMonitor.SM (SecurityMonitor.state core))] = (_enum enum_core_state "Waiting") \/
     _unsafe_get_field enclave_req "ext_led" (enc_data' core st) = Ob~0).
  Proof.
    unfold get_impl_config, get_ghost_running_config, machine_st_to_ghost_core.
    intros * hwf H. unfold owns_led, owns_led, enc_data' in *. propositional.
    bash_destruct H; simplify; propositional; simplify; try split; auto.
    right. unfold not in *.
    match goal with
    | |- ?x = _ =>
        assert (Datatypes.length x = 1) as hlen
    end.
    { consider _unsafe_get_field. consider @success_or_default.
      unsafe_auto_simplify_structs; [ | simplify; auto].
      unsafe_auto_simplify_structs; [ | simplify; auto].
      destruct core; unsafe_auto_simplify_structs.
    }
    apply case_singleton_bv in hlen. split_ors_in hlen; propositional.
  Qed.

  Lemma not_owns_finish_implies :
    forall st core extract_rf,
    WF_state (SortedRegEnv.to_list reg_type_env) st ->
    owns_finish (get_impl_config st core extract_rf)  = false ->
     (st.[_rid (SecurityMonitor.SM (SecurityMonitor.state core))] = (_enum enum_core_state "Waiting") \/
     _unsafe_get_field enclave_req "ext_finish" (enc_data' core st) = Ob~0).
  Proof.
    unfold get_impl_config, get_ghost_running_config, machine_st_to_ghost_core.
    intros * hwf H. unfold owns_led, owns_led, enc_data' in *. propositional.
    bash_destruct H; simplify; propositional; simplify; try split; auto.
    right. unfold not in *.
    match goal with
    | |- ?x = _ =>
        assert (Datatypes.length x = 1) as hlen
    end.
    { consider _unsafe_get_field. consider @success_or_default.
      unsafe_auto_simplify_structs; [ | simplify; auto].
      unsafe_auto_simplify_structs; [ | simplify; auto].
      destruct core; unsafe_auto_simplify_structs.
    }
    apply case_singleton_bv in hlen. split_ors_in hlen; propositional.
  Qed.

   Lemma shared_region_lookup:
    forall data sid,
    Datatypes.length data = _unsafe_struct_sz enclave_data ->
    success_or_default
      (let/res b
       := sel (unsafe_get_field
                 (unsafe_lookup_dstruct_fields struct_defs (_sid enclave_req))
               (_fld enclave_req "shared_regions")
               (unsafe_get_field
                  (unsafe_lookup_dstruct_fields struct_defs (_sid enclave_data))
                    (_fld enclave_data "data") data))
              (shared_id_index sid) in Success [b]) [] = [true] <->
    config_shared_regions (unsafe_enclave_data_to_config data) sid = true.
  Proof.
    intros * hlen.
    pose proof (eta_expand_list_correct false data) as hdata. rewrite hlen in hdata.
    cbn in hdata. rewrite hdata. unfold sel. unfold __debug__.
    destruct sid; cbv; simpl; apply unit_equiv.
  Qed.
  #[global] Hint Resolve WF_ext_log_app : modularity.

Lemma interp_sval_ignores_mem:
  forall mem1 mem2 pkg input ext_args v,
  pkg.(pkg_sigma) = mk_sigma_fn mem1 input ->
  sval_ignores_fn (_extid ext_mainmem) v = true ->
  interp_sval pkg ext_args v = interp_sval (set_sigma pkg (mk_sigma_fn mem2 input)) ext_args v.
Proof.
  intros mem1 mem2 pkg input ext_args v hsim.
  induction v; propositional; simpl in *; repeat rewrite IHv; auto; try rewrite andb_true_iff in *; propositional.
  - rewrite IHv1; rewrite IHv2; auto.
  - unfold unsafe_call_ext. rewrite hsim. unfold mk_sigma_fn.
    rewrite negb_true_iff in *.
    repeat setoid_rewrite H1. auto.
Qed.

(* Lemma interp_fancy_spred_taint_fns: *)
(*   forall mem1 mem2 pkg input p, *)
(*   pkg.(pkg_sigma) = mk_sigma_fn mem1 input -> *)
(*   fancy_spred_ignores_fn (_extid ext_mainmem) p = true -> *)
(*   interp_fancy_spred pkg p <-> interp_fancy_spred (set_sigma pkg (mk_sigma_fn mem2 input)) p. *)


(* Lemma interp_fancy_spred_ignores_mem: *)
(*   forall mem1 mem2 pkg input p, *)
(*   pkg.(pkg_sigma) = mk_sigma_fn mem1 input -> *)
(*   fancy_spred_ignores_fn (_extid ext_mainmem) p = true -> *)
(*   interp_fancy_spred pkg p <-> interp_fancy_spred (set_sigma pkg (mk_sigma_fn mem2 input)) p. *)
(* Proof. *)
(*   (* intros mem1 mem2 pkg input p hsim. unfold interp_fancy_spred. *) *)
(*   (* generalize (@nil (string * vect_t)) as ext_args. *) *)
(*   (* einduction p using fancy_spred_mut with (P:= fun p1 => *) *)
(*   (*   forall ext_args : list (string * vect_t), *) *)
(*   (*   fancy_spred_ignores_fn (_extid ext_mainmem) (PBase p1) = true -> *) *)
(*   (*   interp_fancy_spred' pkg ext_args (PBase p1) <-> *) *)
(*   (*   interp_fancy_spred' (set_sigma pkg (mk_sigma_fn mem2 input)) ext_args (PBase p1)); *) *)
(*   (*   repeat rewrite interp_fancy_spred'_PBase in *; *) *)
(*   (*   repeat rewrite interp_spred'_PAnd in *; *) *)
(*   (*   simpl in *; propositional; split; propositional; split_ands_in_goal; *) *)
(*   (*   repeat rewrite interp_fancy_spred'_PBase in *; *) *)
(*   (*   repeat rewrite interp_spred'_PAnd in *; *) *)
(*   (*   try destruct_match_pairs; subst; *) *)
(*   (* repeat match goal with *) *)
(*   (* | H: _ && _ = true |- _ => rewrite andb_true_iff in H; split_ands_in_hyps *) *)
(*   (* | H: forall _, spred_ignores_fn _ ?p1 = true -> *) *)
(*   (*    interp_spred' ?pkg _ ?p1 <-> interp_spred' _ _ _ , *) *)
(*   (*   H1: spred_ignores_fn _ ?p1 = true, *) *)
(*   (*   H2: context[interp_spred' ?pkg _ ?p1] *) *)
(*   (*   |- _ => *) *)
(*   (*   rewrite H in H2 by auto *) *)
(*   (* | H: forall _, spred_ignores_fn _ ?p1 = true -> *) *)
(*   (*    interp_spred' ?pkg _ ?p1 <-> interp_spred' _ _ _ , *) *)
(*   (*   H1: spred_ignores_fn _ ?p1 = true *) *)
(*   (*   |- context[interp_spred' ?pkg _ ?p1] => *) *)
(*   (*   rewrite H by auto *) *)
(*   (* | |- context[interp_sval (set_sigma _ _) _ _] => *) *)
(*   (*   erewrite<-interp_sval_ignores_mem by eauto *) *)
(*   (* | H: context[interp_sval (set_sigma _ _) _ _] |- _ => *) *)
(*   (*   erewrite<-interp_sval_ignores_mem in H by eauto *) *)
(*   (* | H: forall (y: vect_t), _ |- forall (y: vect_t), _ => *) *)
(*   (*     let y := fresh in intro y; specialize (H y) *) *)
(*   (* | H: forallb _ _ = true |- _ => rewrite forallb_forall in H *) *)
(*   (* | H: forall _, In _ ?l -> _, H1: In _ ?l |- _ => *) *)
(*   (*   pose_fresh (H _ H1) *) *)
(*   (* end; auto. *) *)
(*   (* simpl. *) *)
(*   (* - rewrite<-H; eauto. *) *)
(*   (* - rewrite H; eauto. *) *)
(* Admitted. *)
Lemma interp_spred_ignores_mem:
  forall mem1 mem2 p pkg input,
  pkg.(pkg_sigma) = mk_sigma_fn mem1 input ->
  spred_taints_only_fns
               [_extid ext_uart_read; _extid ext_uart_write; _extid ext_led; _extid ext_finish] p = true ->
  interp_spred pkg p <-> interp_spred (set_sigma pkg (mk_sigma_fn mem2 input)) p.
Proof.
  intros.
  erewrite interp_spred_taints_only_ok.
  2: eauto.
  { reflexivity. }
  rewrite H.
  repeat constructor; simpl; auto.
Qed.

Lemma forall_interp_spred_ignores_mem:
  forall mem1 mem2 ps pkg input,
  pkg.(pkg_sigma) = mk_sigma_fn mem1 input ->
    forallb (spred_taints_only_fns
               [_extid ext_uart_read; _extid ext_uart_write; _extid ext_led; _extid ext_finish]) ps = true ->
    Forall (fun p => interp_spred pkg p) ps <->
    Forall (fun p => interp_spred (set_sigma pkg (mk_sigma_fn mem2 input)) p) ps.
  Proof.
    intros. repeat rewrite Forall_forall. rewrite forallb_forall in H0.
  split; propositional.
  - rewrite<-interp_spred_ignores_mem; eauto.
  - rewrite interp_spred_ignores_mem; eauto.
Qed.
Lemma SMPre_ignores_mem:
  forall st mem1 mem2 input enclave_sig,
  SMSymbDefs.SMPre enclave_sig st (mk_sigma_fn mem1 input) <-> SMSymbDefs.SMPre enclave_sig st (mk_sigma_fn mem2 input).
Proof.
  unfold SMSymbDefs.SMPre.
  intros.
  repeat rewrite<-forall_preprocess_fancy_spreds_correct.
  eapply forall_interp_spred_ignores_mem with (mem2 := mem2).
  - simpl. eauto.
  - vm_reflect.
Qed.
    Ltac simplify_get_field :=
     match goal with
     | H :_get_field ?sdef ?_fld ?req = Success ?s
     |- Datatypes.length ?s = _ =>
        let H':= fresh in
        pose proof (_get_field_success sdef _fld req) as H'; simpl in H';
        specialize H' with (2 := eq_refl); assert_pre_and_specialize H'; [ | simplify; auto]
   end.

Import Utils.PfHelpers.
Ltac custom_unsafe_auto_simplify_structs ::=
  match goal with
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

Require Import koikaExamples.Enclaves.PfImplDefs.
  Import ExternalMemory.
  Lemma unsafe_call_ext_empty:
    forall mem input arg,
      mem.(ext_resp) = None ->
      unsafe_call_ext (mk_sigma_fn mem input) (_id (_extid ext_mainmem)) arg = zeroes (_unsafe_struct_sz mem_output).
  Proof.
    intros. unfold mk_sigma_fn. unfold mem_get_response__koika. rewrite H. reflexivity.
  Qed.
  Lemma update_memory_none:
    forall log mem mem',
      WF_ext_log _ext_fn_tys log ->
      mainmem__ext (unsafe_get_ext_call_from_log log (_ext ext_mainmem)) mem = Success mem' ->
      unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid Memory.Memory.mem_input))
        (_fld Memory.Memory.mem_input "put_valid") (unsafe_get_ext_call_from_log log (_id (_extid ext_mainmem))) =
        Ob~0 ->
      ext_resp mem' = None.
  Proof.
    intros * hlog. intros. consider mainmem__ext. simplify.
    bash_destruct H; simplify; auto.
    erewrite _get_field_implies_unsafe_get_field with (1 := Heqr0) in H0; eauto.
    discriminate.
  Qed.


Lemma filter_input_led_valid:
  forall arg mem mem' v config,
  config.(config_ext_led) = true ->
  unsafe_call_ext (mk_sigma_fn mem (filter_input (Some config) v)) (_id (_extid ext_led)) arg =
  unsafe_call_ext (mk_sigma_fn mem' v) (_id (_extid ext_led)) arg.
Proof.
  intros. unfold filter_input. rewrite H. auto.
Qed.
Lemma filter_input_uart_read_valid:
  forall arg mem mem' v config,
  config.(config_ext_uart) = true ->
  unsafe_call_ext (mk_sigma_fn mem (filter_input (Some config) v)) (_id (_extid ext_uart_read)) arg =
  unsafe_call_ext (mk_sigma_fn mem' v) (_id (_extid ext_uart_read)) arg.
Proof.
  intros. unfold filter_input. rewrite H. auto.
Qed.
Lemma filter_input_uart_write_valid:
  forall arg mem mem' v config,
  config.(config_ext_uart) = true ->
  unsafe_call_ext (mk_sigma_fn mem (filter_input (Some config) v)) (_id (_extid ext_uart_write)) arg =
  unsafe_call_ext (mk_sigma_fn mem' v) (_id (_extid ext_uart_write)) arg.
Proof.
  intros. unfold filter_input. rewrite H. auto.
Qed.
Lemma filter_input_finish_valid:
  forall arg mem mem' v config,
  config.(config_ext_finish) = true ->
  unsafe_call_ext (mk_sigma_fn mem (filter_input (Some config) v)) (_id (_extid ext_finish)) arg =
  unsafe_call_ext (mk_sigma_fn mem' v) (_id (_extid ext_finish)) arg.
Proof.
  intros. unfold filter_input. rewrite H. auto.
Qed.
Lemma init_spec_koika_st_enc_data:
  forall core params mem_turn sm_turn ,
  (init_spec_koika_st core params mem_turn sm_turn).[_id (_smid (SecurityMonitor.enc_data core))] =
    opt_enclave_config_to_enclave_data params.(machine_config).
Proof.
  intros. destruct core; reflexivity.
Qed.



Module ImplHelpers (EnclaveParams: EnclaveParams_sig) (SecurityParams: SecurityParams_sig EnclaveParams)
                   (ImplDefs: PfImplDefs EnclaveParams SecurityParams).
  Require Import FunctionalExtensionality.
  Lemma extract_rf_eq:
    forall m1 m2 core,
    (forall reg, In reg (map RVCore.Core.rf (FiniteType.finite_elements)) ->
            m1.(machine_koika_st).[_rid (SecurityMonitor.core_reg core reg)] = m2.(machine_koika_st).[_rid (SecurityMonitor.core_reg core reg)]
    ) ->
    SecurityParams.extract_rf m1 core = SecurityParams.extract_rf m2 core.
  Proof.
    unfold SecurityParams.extract_rf. intros. apply functional_extensionality.
    intros. destruct_match; auto.
    specialize H with (reg := (RVCore.Core.rf (RVCore.Core.Rf.rData i))).
    rewrite H; auto.
    rewrite in_map_iff. exists (RVCore.Core.Rf.rData i). split; auto.
    eapply nth_error_In with (n := x).
    do 32 (destruct x; [ cbv in Heqo; inversions Heqo; reflexivity | ]).
    cbv in Heqo. discriminate.
  Qed.

  (* Lemma core_regs_implied: *)
  (*   forall core x, *)
  (*   In x (map reg_to_debug_id (core_regs core)) -> *)
  (*   In x (map reg_to_debug_id (map (SecurityMonitor.core_reg core) [RVCore.Core.purge; RVCore.Core.init_pc; RVCore.Core.core_id] ++ (core_regs_to_reset core) ++ (core_to_sm_fifos core) ++ (map (SecurityMonitor.core_reg core) (map RVCore.Core.rf FiniteType.finite_elements)))). *)
  (* Proof. *)
  (*   (* intros. *) *)
  (*   (* destruct core. *) *)
  (*   (* - set (map reg_to_debug_id (core_regs _)) in H. vm_compute in l. *) *)
  (*   (*   match goal with *) *)
  (*   (*   | |- In x ?y => set y *) *)
  (*   (*   end. *) *)
  (*   (*   vm_compute in l0. subst l0. *) *)
  (*   (*   eapply In_subset with (2 := H). vm_reflect. *) *)
  (*   (* - set (map reg_to_debug_id (core_regs _)) in H. vm_compute in l. *) *)
  (*   (*   match goal with *) *)
  (*   (*   | |- In x ?y => set y *) *)
  (*   (*   end. *) *)
  (*   (*   vm_compute in l0. subst l0. *) *)
  (*   (*   eapply In_subset with (2 := H). vm_reflect. *) *)
  (* Admitted. *)
Lemma forallb_cons:
  forall {X} f (x: X) xs,
  f x = true ->
  forallb f xs = true ->
  forallb f (x::xs) = true .
Proof.
  simpl. intros. rewrite H. rewrite H0. auto.
Qed.
Lemma opt_get_env_from_list:
  forall {T} (xs: list Impl.reg_t) (x: Impl.reg_t) (f: Impl.reg_t -> T) pf_sorted,
  In x xs ->
  SortedRegEnv.opt_get (SortedRegEnv.from_list (map (fun v => (_id (reg_to_debug_id v), f v)) xs) pf_sorted) (_id (reg_to_debug_id x)) = Some (f x).
Proof.
  consider @SortedRegEnv.from_list. unfold SortedRegEnv.opt_get. unfold SortedRegEnv.Env.
  intros * pf_sorted. clear pf_sorted. revert x. induction xs.
  - intros. inversions H; hnf.
  - intros. inversions H; hnf.
    + rewrite map_cons. cbn - [_id reg_to_debug_id].
      rewrite beq_dec_refl. auto.
    + rewrite map_cons. cbn - [_id reg_to_debug_id].
      destruct_match; simplify; auto.
      apply PfHelpers.reg_to_debug_id_inj in Heqb. subst.
      reflexivity.
Qed.

Lemma init_spec_st_r_eq:
  forall reg init0 init1 mem_turn sm_turn st,
  st.[_id (reg_to_debug_id reg)] = r init0 init1 mem_turn sm_turn reg ->
  st.[_id (reg_to_debug_id reg)] = (initial_koika_state init0 init1 mem_turn sm_turn).[_id (reg_to_debug_id reg)].
Proof.
  intros. unfold initial_koika_state.
  consider unsafe_get_reg. consider r_get_reg.
  rewrite opt_get_env_from_list.
  - rewrite H. reflexivity.
  - eapply nth_error_In. eapply FiniteType.finite_surjective.
Qed.
Lemma slice_eq:
  forall n v,
  Datatypes.length v = n ->
  slice 0 n v = v.
Proof.
  unfold slice. intros. subst. rewrite skipn_O.
  rewrite firstn_fill_eq; auto.
  apply firstn_all.
Qed.
Instance EqDec_FiniteType' {T} {FT: FiniteType.FiniteType T} : EqDec T | 3.
Proof.
  econstructor; intros.
  destruct (PeanoNat.Nat.eq_dec (FiniteType.finite_index t1) (FiniteType.finite_index t2)) as [ ? | Hneq ].
  - eauto using FiniteType.finite_index_injective.
  - right; intro Habs; apply (f_equal FiniteType.finite_index) in Habs.
    contradiction.
Defined.

Instance EqDec_rf: EqDec RVCore.Core.Rf.reg_t := EqDec_FiniteType'.

Lemma rf_init_sim:
  forall core reg st mem_turn sm_turn params,
  WF_state (SortedRegEnv.to_list reg_type_env) (machine_koika_st st) ->
  In reg (map reg_to_debug_id
              (map (SecurityMonitor.core_reg core) (map RVCore.Core.rf finite_elements))) ->
  params.(machine_rf) = SecurityParams.extract_rf (st) core ->
  (machine_koika_st st).[_id reg] =
    (init_spec_koika_st core params mem_turn sm_turn ).[_id reg].
Proof.
  intros * wf hin hrf.
  unfold init_spec_koika_st.
  apply in_map_iff in hin. propositional.
  apply in_map_iff in hin2. propositional.
  apply in_map_iff in hin2. propositional.
  destruct params. consider Common.machine_rf. subst.
  destruct core.
  - eapply init_spec_st_r_eq.
    destruct x.
    rename n into a.
    repeat (destruct a; [
              match goal with
              | |- ?x = _ =>
                  rewrite<-slice_eq with (n := 32) (v := x); [ cbn - [slice]; reflexivity| apply WF_state_length' with (1 := wf); reflexivity ]
              end | ]).
    exfalso.
    eapply @In_false with (A := RVCore.Core.Rf.reg_t) (2 := hin2).  vm_reflect.
  - eapply init_spec_st_r_eq.
    destruct x.
    rename n into a.
    repeat (destruct a; [
              match goal with
              | |- ?x = _ =>
                  rewrite<-slice_eq with (n := 32) (v := x); [ cbn - [slice]; reflexivity | apply WF_state_length' with (1 := wf); reflexivity ]
              end | ]).
    exfalso.
    eapply In_false with (2 := hin2). vm_reflect.
Qed.
  Import SMSymbDefs.
Lemma beq_dec_single:
  forall b,
  beq_dec [b] Ob~1 = b.
Proof.  intros. destruct b; auto.
Qed.

Lemma enclave_data_to_config_involutive':
  forall data,
  Datatypes.length data = _unsafe_struct_sz enclave_data ->
  _unsafe_get_field enclave_data "valid" data = Ob~1 ->
  (enclave_config_to_valid_enclave_data (unsafe_enclave_data_to_config data)) = data.
Proof.
  intros* hlen hvalid. pose proof (eta_expand_list_correct false data) as henc_data.
  set (_unsafe_struct_sz _ ) in *. vm_compute in n. rewrite hlen in henc_data.
  subst n. cbn in henc_data. rewrite henc_data. rewrite henc_data in hvalid.
  cbn - [_id] in hvalid. setoid_rewrite unit_equiv in hvalid.  rewrite hvalid in *.
  simpl in hvalid.
  unfold enclave_config_to_valid_enclave_data.
  unfold enclave_config_to_enclave_request.
  unfold unsafe_enclave_data_to_config.
  unfold unsafe_enclave_req_to_config.
  consider _unsafe_get_field.
  _vm_simplify.
  cbv [config_ext_finish config_ext_led config_ext_uart config_shared_regions config_eid success_or_default].
  destruct_with_eqn (nth 0 data false);
  destruct_with_eqn (nth 1 data false); auto.
  all: repeat rewrite beq_dec_single; reflexivity.
Qed.
Import SymbSimDefs.
   Lemma core_sim_regs_implied:
      forall core x,
      In x (map reg_to_debug_id (SymbSimDefs.core_sim_regs core)) ->
      In x (((_smid (SecurityMonitor.sm_reset core))::(map reg_to_debug_id (sm_reset_regs core))) ++
             (map reg_to_debug_id (map (SecurityMonitor.core_reg core) (map RVCore.RV32Core.rf finite_elements))) ++
             (map reg_to_debug_id (map (SecurityMonitor.core_reg core) [RVCore.Core.purge; RVCore.Core.init_pc; RVCore.Core.core_id]))).
   Proof.
     intros *.
     eapply In_subset.
     set (map reg_to_debug_id _).
     set (map reg_to_debug_id _).
     set (map reg_to_debug_id _).
     destruct core.
     - vm_compute in l. vm_compute in l0. vm_compute in l1. vm_reflect.
     - vm_compute in l. vm_compute in l0. vm_compute in l1. vm_reflect.
   Qed. (* DONE *)

  Lemma impl_core_sim_init:
    forall st core reg params mem_turn sm_turn st',
      WF_state (SortedRegEnv.to_list reg_type_env) (st) ->
      (forall reg, In reg (((_smid (SecurityMonitor.sm_reset core))::(map reg_to_debug_id (sm_reset_regs core)))) ->
              st.[_id reg] = (zeroes (unsafe_lookup_reg_type (_id reg)))) ->
      st.[_id (_crid core (RVCore.Core.core_id))] = cid_to_bits core ->
      st.[_id (_crid core (RVCore.Core.purge))] = _enum enum_core_state "Running" ->
      st.[_id (_crid core (RVCore.Core.init_pc))] = params.(machine_pc) ->
      In reg (map reg_to_debug_id (core_sim_regs core)) ->
      machine_koika_st st' = st ->
      params.(machine_rf) = SecurityParams.extract_rf (st') core ->
      st.[_id reg] = (init_spec_koika_st core params mem_turn sm_turn ).[_id reg].
  Proof.
    intros * hwf hreset hcore hpurge hpc hcore_regs hst.
    apply core_sim_regs_implied in hcore_regs.
    repeat rewrite in_app_iff in hcore_regs. split_ors_in hcore_regs.
    - rewrite hreset; auto.
      apply in_map with (f := _id) in hcore_regs.
      symmetry. eapply init_private_zeroed; [ | eauto].
      destruct core.
      + set (map _ _ ) as hreset_regs. vm_compute in hreset_regs.
        reflexivity.
      + set (map _ _ ) as hreset_regs. vm_compute in hreset_regs.
        reflexivity.
    - subst.
      destruct core.
      + eapply rf_init_sim; auto.
      + eapply rf_init_sim; auto.
    - simpl in hcore_regs.
      split_ors_in hcore_regs; subst.
      + setoid_rewrite hpurge. destruct core; reflexivity.
      + setoid_rewrite hpc. destruct core; reflexivity.
      + setoid_rewrite hcore. destruct core; reflexivity.
      + contradiction.
  Qed. (* DONE *)
Lemma In_fifos_type:
  forall {B} rvalid (rdata: B) pairs sz,
  In (rvalid, rdata) pairs ->
  forallb (fun '(r,_) => beq_dec (unsafe_lookup_reg_type (_id r)) sz) pairs = true ->
  unsafe_lookup_reg_type (_id rvalid) = sz.
Proof.
  intros * hin hforall. rewrite forallb_forall in hforall.
  specialize hforall with (1 := hin). simpl in *. simplify; auto.
Qed.
Lemma In_fifos_reset:
  forall B rvalid (rdata: B) pairs st,
  In (rvalid, rdata) pairs ->
  (forall r, In r (map fst pairs) -> st.[_id r] = zeroes ((unsafe_lookup_reg_type (_id r)))) ->
  forallb (fun '(r,_) => beq_dec (unsafe_lookup_reg_type (_id r)) 1) pairs = true ->
  st.[_id rvalid] = Ob~0.
Proof.
  intros * hin hzeroes hftype.
  eapply In_fifos_type in hftype; eauto.
  specialize (hzeroes rvalid). rewrite hftype in hzeroes. apply hzeroes.
  rewrite in_map_iff. eexists; split; eauto. auto.
Qed.
Lemma core_fifo_valid_in_sm_reset_regs:
  forall r core,
  In r (map fst (core_fifo_reg_pairs' core)) ->
  In r (map reg_to_debug_id (sm_reset_regs core)).
Proof.
  intros * . set (map _ _). set (map _ _).
  eapply In_subset.
  destruct core; vm_compute in l; vm_compute in l0; vm_reflect.
Qed.
  Lemma sm_regs_implied:
    forall core x,
    In x (map reg_to_debug_id (sm_sim_regs core)) ->
    In x (((map reg_to_debug_id (map SecurityMonitor.SM [SecurityMonitor.state core; SecurityMonitor.enc_req core; SecurityMonitor.enc_data core; SecurityMonitor.sm_reset core; SecurityMonitor.clk]))) ++
          (map reg_to_debug_id (sm_reset_regs core))).
  Proof.
    intros *.  repeat set (map _ _). eapply In_subset.
    destruct core; vm_compute in l; vm_compute in l0; vm_compute in l1; vm_reflect.
  Qed.
Lemma In_exists:
  forall {A} {EqDec: EqDec A} x (l: list A),
  existsb (beq_dec x) l = true -> In x l.
Proof.
  intros * hexists. rewrite existsb_exists in hexists. propositional. simplify. auto.
Qed.

Ltac solve_In_to_find' :=
  apply In_exists; vm_reflect.

  Lemma impl_sm_sim_init:
    forall st core reg params mem_turn sm_turn st',
      WF_state (SortedRegEnv.to_list reg_type_env) (st) ->
      WF_state (SortedRegEnv.to_list reg_type_env) (machine_koika_st st' )->
      (forall reg, In reg (((_smid (SecurityMonitor.sm_reset core))::(map reg_to_debug_id (sm_reset_regs core)))) ->
              st.[_id reg] = (zeroes (unsafe_lookup_reg_type (_id reg)))) ->
      (forall reg, In reg [_cid core RVCore.RV32Core.purge; _mid (Memory.Memory.purge core);
                    _smid (SecurityMonitor.enc_req core)] ->
              st.[_id reg] = zeroes (unsafe_lookup_reg_type (_id reg))) ->
      st.[_id (_crid core (RVCore.Core.init_pc))] = params.(machine_pc) ->
      st.[_smrid SecurityMonitor.clk] = sm_turn ->
      st.[_smrid (SecurityMonitor.state core)] = Ob~0~0 ->
      params.(machine_config) = Some (unsafe_enclave_data_to_config
        (machine_koika_st st').[_smrid (SecurityMonitor.enc_data core)]) ->
      _unsafe_get_field enclave_data "valid"
        ((machine_koika_st st').[_smrid (SecurityMonitor.enc_data core)]) = Ob~1 ->
      ((machine_koika_st st').[_smrid (SecurityMonitor.enc_data core)])  =
      (st).[_smrid (SecurityMonitor.enc_data core)]  ->
      In reg (map reg_to_debug_id (sm_sim_regs core)) ->
      params.(machine_rf) = (SecurityParams.extract_rf st' core) ->
      st.[_id reg] = (init_spec_koika_st core params mem_turn sm_turn ).[_id reg].
  Proof.
    intros * hwf hwf' hreset hswitch hpc hclk hstate hconfig hvalid hdata hregs hrf.
    destruct params. simpl in hconfig. subst. simpl in hrf. subst.
    apply sm_regs_implied in hregs.
    (repeat rewrite map_app in hregs; repeat rewrite in_app_iff in hregs).

    consider _smrid. consider _rid. consider _crid. consider _smid. consider _cid. consider _mid.
    consider init_spec_koika_st.
    pose proof PfHelpers.initial_koika_state_lookup' as hlookup. consider _rid.
    split_ors_in hregs.
    - rewrite in_map_iff in hregs. propositional. rewrite in_map_iff in hregs2. propositional.
      simpl in hregs2.
      destruct core; rewrite hlookup; split_ors_in hregs2; subst;
        try ((rewrite hstate; reflexivity) || (rewrite hswitch; [reflexivity | solve_In_to_find'] ))
            || (rewrite hreset; [ reflexivity | solve_In_to_find']); auto.
      + cbn - [_id]. rewrite enclave_data_to_config_involutive'; auto.
        unsafe_auto_simplify_structs.
      + cbn - [_id]. rewrite enclave_data_to_config_involutive'; auto.
        unsafe_auto_simplify_structs.
    - rewrite hreset.
      { destruct core; apply in_map with (f := _id) in hregs;
          rewrite @init_private_zeroed with (2 := hregs); reflexivity.
      }
      { right. auto. }
  Qed.
Lemma sm_fifo_valid_in_sm_reset_regs:
  forall r core,
  In r (map fst (sm_fifo_reg_pairs' core)) ->
  In r (map reg_to_debug_id (sm_reset_regs core)).
Proof.
  intros * . set (map _ _). set (map _ _).
  eapply In_subset.
  destruct core; vm_compute in l; vm_compute in l0; vm_reflect.
Qed.

  Lemma impl_mem_sim_init:
    forall st core reg params sm_turn,
      (forall reg, In reg ((map reg_to_debug_id (sm_reset_regs core))) ->
              st.[_id reg] = (zeroes (unsafe_lookup_reg_type (_id reg)))) ->
      (*  (forall reg, In reg (map reg_to_debug_id (private_mem_regs core ++ (memory_to_sm_fifos core) ++ (sm_to_memory_fifos core))) -> *)
      (*         st.[_id reg] = (zeroes (unsafe_lookup_reg_type (_id reg)))) -> *)
      st.[_mrid (Memory.Memory.purge core)] = Ob~0~0 ->
      In reg (mem_sim_regs core) ->
      st.[_id reg] = (init_spec_koika_st  core params
                        st.[_mrid Memory.Memory.turn]
                        sm_turn
                        ).[_id reg].
  Proof.
    intros * hreset hpurge hregs. consider mem_sim_regs. repeat rewrite in_app_iff in hregs.
    set (map _ _) in hreset.
    repeat rewrite map_app in hregs.  rewrite in_app_iff in hregs. rewrite in_app_iff in hregs.
    destruct core.
    - vm_compute in l. split_ors_in hregs; auto.
      + simpl in hregs; split_ors_in hregs; auto; subst; reflexivity.
      + simpl in hregs; split_ors_in hregs; auto; subst. rewrite hreset; auto. solve_In_to_find'.
      + simpl in hregs; split_ors_in hregs; auto; subst.  setoid_rewrite hpurge. reflexivity.
      + rewrite<-map_app in hregs.
        set (map _ _) in hregs. vm_compute in l0.
        rewrite hreset; auto.
        2: { eapply In_subset with (2 := hregs). vm_reflect. }
        apply in_map with (f := _id) in hregs.
        rewrite @init_private_zeroed with (2 := hregs); reflexivity.
    - vm_compute in l. split_ors_in hregs; auto.
      + simpl in hregs; split_ors_in hregs; auto; subst; reflexivity.
      + simpl in hregs; split_ors_in hregs; auto; subst. rewrite hreset; auto. solve_In_to_find'.
      + simpl in hregs; split_ors_in hregs; auto; subst.  setoid_rewrite hpurge. reflexivity.
      + rewrite<-map_app in hregs.
        set (map _ _) in hregs. vm_compute in l0.
        rewrite hreset; auto.
        2: { eapply In_subset with (2 := hregs). vm_reflect. }
        apply in_map with (f := _id) in hregs.
        rewrite @init_private_zeroed with (2 := hregs); reflexivity.
  Qed.
Lemma mem_fifo_valid_in_sm_reset_regs:
  forall r core,
  In r (map fst (mem_fifo_pairs' core)) ->
  In r (map reg_to_debug_id (sm_reset_regs core)).
Proof.
  intros * . set (map _ _). set (map _ _).
  eapply In_subset.
  destruct core; vm_compute in l; vm_compute in l0; vm_reflect.
Qed.


  Ltac req_addrs_in_range_simplify :=
    match goal with
    | _ => progress (simplify; safe_propositional; try rewrite_solve; unsafe_auto_simplify_structs)
    | H: _ && _ = true |- _ =>
        rewrite andb_true_iff in H
    | H: (_ <=? _)%N = true |- _ =>
        rewrite N.leb_le in H
    | H: (_ <? _)%N = true |- _ =>
        rewrite N.ltb_lt in H
    | |- _ && _ = true =>
        rewrite andb_true_iff; split
    | |- (_ <=? _)%N = true =>
        rewrite N.leb_le
    | |- (_ <? _)%N = true =>
        rewrite N.ltb_lt
    | |- beq_dec _ _ = true =>
        rewrite beq_dec_iff
    | H: (_ ?= _)%N = Gt |- _ => rewrite N.compare_gt_iff in H
    | H: (_ ?= _)%N = Eq |- _ => rewrite N.compare_eq_iff in H
    | |- (_ <= to_N _)%N =>
      eapply bitfun_unsigned_le_iff; auto
    | |- (_ < _ )%N =>
      eapply bitfun_unsigned_lt_plus; auto
    | |- context[Datatypes.length (_enclave_base EnclaveParams.enclave_sig _)] =>
      rewrite wf_enclave_base with (1 := EnclaveParams.wf_sig)
    | |- context[Datatypes.length (_enclave_size EnclaveParams.enclave_sig _)] =>
      rewrite wf_enclave_size with (1 := EnclaveParams.wf_sig)
    | H: unsafe_get_field _ (_fld enclave_req "eid") _ = _
      |- _ = config_eid (unsafe_enclave_data_to_config _) =>
      eapply enclave_eid; eauto
    | |- context[Datatypes.length (_shared_region_base EnclaveParams.enclave_sig _)] =>
      rewrite wf_shared_base with (1 := EnclaveParams.wf_sig)
    | |- context[Datatypes.length (_shared_region_size EnclaveParams.enclave_sig )] =>
      rewrite wf_shared_size with (1 := EnclaveParams.wf_sig)
    | |- config_shared_regions (unsafe_enclave_data_to_config _) _ = true =>
      eapply shared_region_lookup; eauto
    end.

  Import SMSymbDefs.
  Lemma addr_in_config_implied:
    forall st mid_st final_st sigma mid_log final_log s1 s0 reg_enc,
    interp_fancy_spred
      (dummy_pkg st mid_st final_st sigma (Some mid_log) final_log)
      (fs_req_addrs_in_config EnclaveParams.enclave_sig impl_get_field
         (impl_get_field (_sid mem_input) (_fld mem_input "put_request")
            (impl_committed_ext (_extid ext_mainmem)))
         (impl_init reg_enc)) ->
    Datatypes.length st.[_id reg_enc] = _unsafe_struct_sz enclave_data ->
    WF_ext_log _ext_fn_tys (ext_log_app final_log mid_log) ->
    Datatypes.length s1 = addr_sz ->
    _get_field (mem_input) "put_request"
                      (unsafe_get_ext_call_from_log (ext_log_app final_log mid_log)
                         (_ext ext_mainmem)) = Success s0 ->
    _get_field (mem_req) ( "addr") s0 = Success s1 ->
    addr_in_config EnclaveParams.enclave_sig (to_N s1)
      (unsafe_enclave_data_to_config st.[_id reg_enc]).
  Proof.
    intros.
    unfold addr_in_config, addr_in_region, region_in_config.
    cbn - [_id _sid _fld] in H.
    consider _ext. consider _extid.
    split_ors_in H; propositional.
    + exists (MemRegion_Enclave Enclave0); split_ands_in_goal; repeat req_addrs_in_range_simplify.
    + exists (MemRegion_Enclave Enclave1); split_ands_in_goal; repeat req_addrs_in_range_simplify.
    + exists (MemRegion_Enclave Enclave2); split_ands_in_goal; repeat req_addrs_in_range_simplify.
    + exists (MemRegion_Enclave Enclave3); split_ands_in_goal; repeat req_addrs_in_range_simplify.
    + exists (MemRegion_Shared Shared01); split_ands_in_goal; repeat req_addrs_in_range_simplify.
    + exists (MemRegion_Shared Shared02); split_ands_in_goal; repeat req_addrs_in_range_simplify.
    + exists (MemRegion_Shared Shared03); split_ands_in_goal; repeat req_addrs_in_range_simplify.
    + exists (MemRegion_Shared Shared12); split_ands_in_goal; repeat req_addrs_in_range_simplify.
    + exists (MemRegion_Shared Shared13); split_ands_in_goal; repeat req_addrs_in_range_simplify.
    + exists (MemRegion_Shared Shared23); split_ands_in_goal; repeat req_addrs_in_range_simplify.
  Qed.

 Ltac init_interp ::=
  repeat
   match goal with
   | |- dummy_interp _ _ _ _ _ _ => unfold dummy_interp, dummy_pkg
   | |- Forall (fun '(_, p) => interp_fancy_spred _ _) _ => rewrite <- forall_preprocess_fancy_spreds_correct
   | |- Forall (fun '(_, p) => interp_fancy_spred2 _ _ _) _ => rewrite <- forall_preprocess_fancy_spreds_correct2
   end.

 Ltac basic_cbn :=
    cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat filter_input].
  Import SecurityMonitor.
  Import RVCore.
  Import Memory.
  Import ImplDefs.
  Import SecurityParams.
  Import koika.SymbolicInterp.
Lemma SimPre__init_spec:
  forall core input mem_turn sm_turn spec_mem params impl_st spec_config,
  ImplInvariant impl_st ->
  params.(machine_rf) = (extract_rf impl_st core) ->
  sm_turn = (machine_koika_st impl_st).[_smrid clk] ->
  mem_turn = (machine_koika_st impl_st).[_mrid Memory.turn] ->
  spec_config = (unsafe_enclave_data_to_config (machine_koika_st impl_st).[_smrid (enc_data core)] ) ->
  params.(machine_config) = Some spec_config ->
  (forall reg : ProofCore_symb.reg_t,
   In reg (map reg_to_debug_id (SMSymbDefs.sm_reset_regs core))~(_smid (sm_reset core)) ->
   (machine_koika_st impl_st).[_id reg] = zeroes (unsafe_lookup_reg_type (_id reg))) ->
   (machine_koika_st impl_st).[_id (_crid core Core.core_id)] = cid_to_bits core ->
   (forall reg : ProofCore_symb.reg_t,
       In reg [SMSymbDefs._cid core RV32Core.purge; _mid (Memory.purge core); _smid (enc_req core)] ->
       (machine_koika_st impl_st).[_id reg] = zeroes (unsafe_lookup_reg_type (_id reg))) ->
   (machine_koika_st impl_st).[_id (_crid core Core.init_pc)] = params.(machine_pc) ->
  (machine_koika_st impl_st).[_smrid (state core)] = Ob~0~0 ->
  _unsafe_get_field enclave_data "valid" (machine_koika_st impl_st).[_smrid (enc_data core)] = Ob~1 ->
  ((machine_koika_st impl_st).[_id (_mid Memory.Memory.turn)] = (mem_core_read_turn  core) ->
   (machine_mem_st impl_st).(ExternalMemory.ext_resp) = None) ->
  ((machine_koika_st impl_st).[_id (_mid Memory.turn)] <> mem_core0_read_turn ->
   (machine_koika_st impl_st).[_id (_mid Memory.turn)] <> mem_core1_read_turn ->
   (machine_mem_st impl_st).(ExternalMemory.ext_resp) = None) ->
  SymbSimDefs.SimPre EnclaveParams.enclave_sig core (machine_koika_st impl_st)
    (init_spec_koika_st core params mem_turn sm_turn )
    (mk_sigma_fn (machine_mem_st impl_st) input)
    (mk_sigma_fn (ExternalMemory.initial_mem (get_enclave_dram EnclaveParams.enclave_sig spec_mem spec_config))
                 (filter_input (Some spec_config) input)).
Proof.
  unfold SymbSimDefs.SimPre.
  intros * himpl_inv hrf hsm_turn mem_turn hconfig hconfig' hreset_sm hcore_id hcore_purge hcore_pc hsm_state henc_valid
           himpl_mem_resp himpl_mem_resp'.
  unfold SymbSimDefs.sim_pre_conds.
  subst.
  assert (WF_state (SortedRegEnv.to_list reg_type_env) (machine_koika_st impl_st)) as hwf_impl.
  { apply strong_WF_state_weaken. eauto with solve_invariants. }

  apply Forall_app; split; [ | apply Forall_app; split].
  + unfold SymbSimDefs.sim_invariants.
    repeat rewrite Forall_app. split_ands_in_goal.
    * unfold core_sim_invariants.
      repeat constructor.
      { cbn - [ map _sid of_nat _fld reg_to_debug_id In _id core_regs].
        intros. eapply impl_core_sim_init; try assumption; try reflexivity; auto.
        rewrite hcore_purge; auto.
        { destruct core; reflexivity. }
        { destruct core; solve_In_to_find'. }
      }
      { cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat filter_input core_fifo_reg_pairs'].
        intros * hin. destruct x as (rvalid & rdata).
        cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat filter_input core_fifo_reg_pairs'].
        intro Hfalse.
        assert ((machine_koika_st impl_st).[_id rvalid] = Ob~0) as hfalse.
        { eapply In_fifos_reset.
          - apply hin.
          - intros * hin'. apply hreset_sm. right.
            eapply core_fifo_valid_in_sm_reset_regs. auto.
          - destruct core; vm_reflect.
        }
        congruence.
      }
    * unfold sm_sim_invariants.
      rewrite Forall_app. split_ands_in_goal.
      { specialize (ImplInv_SMInvariant _ himpl_inv); intros ImplInv_SMInvariant.
        revert ImplInv_SMInvariant. unfold SMSymbDefs.SMPre. unfold SMSymbDefs.sm_pre_conds. intros.
        specialize ImplInv_SMInvariant0 with (input := input).
        rewrite Forall_app in ImplInv_SMInvariant0. propositional.
        unfold sm_impl_invariants.
        init_interp. rewrite Forall_interp_spred2_using_impl_only; [ | vm_reflect].
        init_interp_in ImplInv_SMInvariant2.
        change_Forall_lists1 ImplInv_SMInvariant2. revert ImplInv_SMInvariant2.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      }
      repeat constructor.
      { cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat filter_input sm_sim_regs].
        intros.
        eapply impl_sm_sim_init; eauto.
      }
      { cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat filter_input sm_fifo_reg_pairs'].
             intros * hin. destruct x as (rvalid & rdata).
        cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat filter_input sm_fifo_reg_pairs'].
        intro Hfalse.
        assert ((machine_koika_st impl_st).[_id rvalid] = Ob~0) as hfalse.
        { eapply In_fifos_reset.
          - apply hin.
          - intros * hin'. apply hreset_sm. right.
            eapply sm_fifo_valid_in_sm_reset_regs. assumption.
          - destruct core; vm_reflect.
        }
        congruence.
      }
      { cbn - [_id sm_regs].
        intros. clear - H. destruct core; simpl in H; split_ors_in H; subst; try contradiction; reflexivity.
      }
    * unfold mem_sim_invariants. repeat rewrite Forall_app.
      constructor.
      { specialize (ImplInv_MemInvariant _ himpl_inv) with (input :=  input) as ImplInv_MemInvariant0.
        revert ImplInv_MemInvariant0. unfold MemSymbDefs.MemPre, MemSymbDefs.mem_pre_conds; intros.
        rewrite Forall_app in ImplInv_MemInvariant0. propositional.
        unfold mem_impl_invariants.
        init_interp.
        rewrite Forall_interp_spred2_using_impl_only; [ | vm_reflect].
        init_interp_in ImplInv_MemInvariant2.
        change_Forall_lists1 ImplInv_MemInvariant2.
        revert ImplInv_MemInvariant2.
        apply forall_interp_spred_package_equiv; solve_package_equiv.
      }
      repeat constructor.
      { basic_cbn; destruct core; reflexivity. }
      { cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat filter_input mem_sim_regs].
        intros * hin.
        apply impl_mem_sim_init. auto.
        { intros. apply hreset_sm. right. auto. }
        { setoid_rewrite hcore_purge; auto.
          destruct core; reflexivity.
          destruct core; solve_In_to_find'.
        }
        auto.
      }
      { cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat filter_input mem_fifo_pairs'].
         intros * hin. destruct x as (rvalid & rdata).
         cbn - [_id _sid _fld mk_sigma_fn of_N_sz _enum ones N.of_nat N.pow of_nat filter_input mem_fifo_pairs'].
         intro Hfalse.
        assert ((machine_koika_st impl_st).[_id rvalid] = Ob~0) as hfalse.
        { eapply In_fifos_reset.
          - apply hin.
          - intros * hin'. apply hreset_sm. right.
            eapply mem_fifo_valid_in_sm_reset_regs. assumption.
           - destruct core; vm_reflect.
        }
        congruence.
      }
    + unfold sim_sm_pre_conds. simplify.
      repeat constructor.
      * basic_cbn. setoid_rewrite hsm_state. discriminate.
      * basic_cbn. intros.
        rewrite filter_input_led_valid with (mem' := machine_mem_st impl_st); auto.
        rewrite init_spec_koika_st_enc_data in H0. rewrite hconfig' in *. clear - H0.
        set (unsafe_enclave_data_to_config _) in *. clearbody e.
        destruct e; simpl in *.
        destruct config_ext_led; auto. destruct config_eid; vm_compute in H0; discriminate.
      * basic_cbn.
        intros. rewrite filter_input_uart_read_valid with (mem' := machine_mem_st impl_st); auto.
        rewrite init_spec_koika_st_enc_data in H0. rewrite hconfig' in *. clear - H0.
        set (unsafe_enclave_data_to_config _) in *. clearbody e.
        destruct e; simpl in *.
        destruct config_ext_uart; auto. destruct config_eid; vm_compute in H0; discriminate.
      * basic_cbn.
        intros. rewrite filter_input_uart_write_valid with (mem' := machine_mem_st impl_st); auto.
        set (unsafe_enclave_data_to_config _) in *. clearbody e.
        rewrite init_spec_koika_st_enc_data in H0. rewrite hconfig' in *. clear - H0.
        destruct e; simpl in *.
        destruct config_ext_uart; auto. destruct config_eid; vm_compute in H0; discriminate.
      * basic_cbn.
        intros. rewrite filter_input_finish_valid with (mem' := machine_mem_st impl_st); auto.
        rewrite init_spec_koika_st_enc_data in H0. rewrite hconfig' in *. clear - H0.
        set (unsafe_enclave_data_to_config _) in *. clearbody e.
        destruct e; simpl in *.
        destruct config_ext_finish; auto. destruct config_eid; vm_compute in H0; discriminate.
    + repeat constructor.
      * basic_cbn. propositional.
        rewrite unsafe_call_ext_empty by (destruct himpl_mem_resp; auto; destruct core; discriminate).
        rewrite unsafe_call_ext_empty by auto.
        split; auto.
        intros. vm_compute in H1. discriminate.
      * basic_cbn. propositional.
        rewrite unsafe_call_ext_empty; auto.
      * basic_cbn. propositional.
      * basic_cbn. propositional.
        prop_pose_with_custom hfoo (MemoryProofs.MemImplExtCorrectCore CoreId0) (ImplInv_MemInvariant _ himpl_inv input).
        cbn - [_id _sid _fld mk_sigma_fn] in hfoo.
        eapply hfoo; eauto.
      * basic_cbn. propositional.
        prop_pose_with_custom hfoo (MemoryProofs.MemImplExtCorrectCore CoreId1) (ImplInv_MemInvariant _ himpl_inv input).
        cbn - [_id _sid _fld mk_sigma_fn] in hfoo.
        eapply hfoo; eauto.
Qed.

End ImplHelpers.
