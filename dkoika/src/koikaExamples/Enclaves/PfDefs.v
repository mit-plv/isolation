Require Import rv_isolation.Common.
Require Import rv_isolation.SecurityMonitor.

Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
(* Require Import koikaExamples.Enclaves.TypeDefs. *)
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
(* Require Import koikaExamples.Enclaves.ProofCore. *)
(* Require Import koikaExamples.Enclaves.ProofMemory. *)
(* Require Import koikaExamples.Enclaves.ProofSm. *)
Require Import FunctionalExtensionality.
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koikaExamples.Enclaves.ProofUtils.

Import ExternalMemory.
Import TopLevelModuleHelpers.

Record WF_ext_mem (mem: external_mem_t) : Prop :=
    { WF_ext_mem__resp__byte_en: forall resp, mem.(ext_resp) = Some resp -> Datatypes.length resp.(mem_resp_byte_en) = 4;
      WF_ext_mem__resp__addr: forall resp, mem.(ext_resp) = Some resp -> Datatypes.length resp.(mem_resp_addr) = addr_sz;
      WF_ext_mem__resp__data: forall resp, mem.(ext_resp) = Some resp -> Datatypes.length resp.(mem_resp_data) = data_sz;
      WF_ext_mem__dram: WF_dram mem.(ext_mem)
    }.
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
  #[global] Hint Resolve @WF_ext_mem__resp__byte_en : solve_invariants.
  #[global] Hint Resolve WF_ext_mem__resp__addr: solve_invariants.
  #[global] Hint Resolve WF_ext_mem__resp__data: solve_invariants.

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


  Ltac custom_unsafe_auto_simplify_structs  ::=
    match goal with
    | H: WF_ext_log _ ?log |- Datatypes.length (unsafe_get_ext_call_from_log ?log ?fn) = _ =>
        solve[eapply WF_ext_log_call_length; eauto]
    end.

  Definition dummy_machine : Symbolic.machine_t :=
        {| file_registers := reg_types;
           file_ext_sigma := ext_fn_tys;
           file_struct_defs := struct_defs;
        |}.

  Definition dummy_input_t : input_t :=
    {| input_ext_uart_write := fun _ => [];
       input_ext_uart_read := fun _ => [];
       input_ext_led := fun _ => [];
       input_ext_finish := fun _ => []

    |}.

  Definition dummy_pkg (st: Environments.state_t) mid_st final_st sigma ext_log1 ext_log2:=
    {| pkg_machine := dummy_machine;
       pkg_init_st := st;
       pkg_sigma := sigma;
       pkg_mid_st := Some mid_st ;
       pkg_final_st := final_st;
       pkg_mid_ext_log := ext_log1;
       pkg_ext_log' := ext_log2;
    |}.
  Lemma WF_mk_sigma_fn:
    forall mem inputs,
      WF_ext_mem mem ->
      WF_ext_sigma _ext_fn_tys (mk_sigma_fn mem inputs).
  Proof.
    intros * Hwf_mem.
    unfold WF_ext_sigma. unfold ext_fn_tys, lookup_ext_fn . simpl.
    intros; repeat destruct_match; simplify; simpl; intros; autorewrite with simplify_bits; auto.
    unfold mk_sigma_fn. simpl.
    apply mem_get_response__koika__Success; autorewrite with simplify_bits; auto.
  Qed.
  Definition dummy_interp
    (init_st mid_st final_st: Environments.state_t) sigma ext_log1 ext_log2 {X} (ps: list (X * fancy_spred)) : Prop :=
      Forall
        (fun '(_, p) => interp_fancy_spred (dummy_pkg init_st mid_st final_st sigma ext_log1 ext_log2) p)
        ps.
Notation reg_t := (@Syntax.reg_t debug_id_ty).
  Definition senc_data (core: ind_core_id) (reg_fn: reg_t -> sval) get_field : sval :=
    get_field (_sid enclave_data) (_fld enclave_data "data") (reg_fn (reg_to_debug_id (SM (enc_data core)))).
  Definition senc_data_valid (core: ind_core_id) (reg_fn: reg_t -> sval) get_field : sval :=
    get_field (_sid enclave_data) (_fld enclave_data "valid") (reg_fn (reg_to_debug_id (SM (enc_data core)))).
  Lemma enclave_eid:
    forall eid data,
    Datatypes.length data = _unsafe_struct_sz enclave_data ->
    unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid enclave_req))
                     (_fld enclave_req "eid")
      (unsafe_get_field (unsafe_lookup_dstruct_fields struct_defs (_sid enclave_data))
                 (_fld enclave_data  "data") data) = enclave_id_to_vect eid <->
    eid = config_eid (unsafe_enclave_data_to_config data).
  Proof.
    intros * hlen.
    set (_unsafe_struct_sz _) as len in hlen. vm_compute in len. subst len.
    pose proof (eta_expand_list_correct false data) as hdata.
    rewrite hlen in hdata.
    cbn in hdata. rewrite hdata in *.
    simpl.
    _vm_simplify.
    destruct eid;
      destruct_with_eqn (nth 0 data false); destruct_with_eqn (nth 1 data false); split; auto; discriminate.
  Qed.

  Lemma shared_region_conflict:
    forall v0 v1,
    Datatypes.length v0 = _unsafe_struct_sz enclave_data ->
    Datatypes.length v1 = _unsafe_struct_sz enclave_data ->
    shared_regions_conflict
          (config_shared_regions (unsafe_enclave_data_to_config v0))
          (config_shared_regions (unsafe_enclave_data_to_config v1)) = true ->
    success_or_default
      (map2 andb
         (_unsafe_get_field enclave_req "shared_regions"
            (_unsafe_get_field enclave_data "data" v0))
         (_unsafe_get_field enclave_req ("shared_regions")
            (_unsafe_get_field enclave_data ("data") v1)))
      Ob <> Ob~0~0~0~0~0~0.
  Proof.
    intros * hlen0 hlen1 hconflict.
    consider shared_regions_conflict.
    repeat rewrite orb_true_iff in hconflict.
    set (_unsafe_struct_sz _) as X in *; vm_compute in X; subst X.
    pose proof (eta_expand_list_correct false v0) as hdata0. rewrite hlen0 in hdata0.
    pose proof (eta_expand_list_correct false v1) as hdata1. rewrite hlen1 in hdata1.
    cbn in hdata0. cbn in hdata1.
    rewrite hdata0 in *. rewrite hdata1 in *. cbn.
    simpl in hconflict.
    split_cases;
       match goal with
      | H: _ && _ = true |- _ =>
          let X := fresh in let Y := fresh in
          rewrite andb_true_iff in H; destruct H as (X & Y); try rewrite X; try rewrite Y
      end; simpl; discriminate.
  Qed.

Section WithEnclaveParams.
   Context (enclave_sig : enclave_params_sig).
   Context (pf_disjoint_configs : Common.wf_disjoint_configs enclave_sig).
   Context (wf_sig : wf_enclave_params enclave_sig).

  Definition get_enclave_bootloader_addr eid :=
    match eid with
    | Ob~0~0 => _enclave_bootloader_addr enclave_sig Enclave0
    | Ob~0~1 => _enclave_bootloader_addr enclave_sig Enclave1
    | Ob~1~0 => _enclave_bootloader_addr enclave_sig Enclave2
    | Ob~1~1 => _enclave_bootloader_addr enclave_sig Enclave3
    | _ => zeroes (addr_sz)
    end.

End WithEnclaveParams.
Lemma shared_region_conflict_false:
  forall v0 v1,
  Datatypes.length v0 = _unsafe_struct_sz enclave_data ->
  Datatypes.length v1 = _unsafe_struct_sz enclave_data ->
  shared_regions_conflict
        (config_shared_regions (unsafe_enclave_data_to_config v0))
        (config_shared_regions (unsafe_enclave_data_to_config v1)) = false->
  success_or_default
    (map2 andb
       (_unsafe_get_field enclave_req "shared_regions"
          (_unsafe_get_field enclave_data "data" v0))
       (_unsafe_get_field enclave_req "shared_regions"
          (_unsafe_get_field enclave_data "data" v1)))
    Ob = Ob~0~0~0~0~0~0.
Proof.
  intros * hlen0 hlen1 hconflict.
  consider shared_regions_conflict.
  repeat rewrite orb_false_iff in hconflict.
  pose proof (eta_expand_list_correct false v0) as hdata0. rewrite hlen0 in hdata0.
  pose proof (eta_expand_list_correct false v1) as hdata1. rewrite hlen1 in hdata1.
  rewrite hdata0 in *. rewrite hdata1 in *. simpl.
  simpl in hconflict.
  propositional. rewrite_solve.
Qed.
Lemma uart_disjoint:
  forall v0 v1,
  Datatypes.length v0 = _unsafe_struct_sz enclave_data ->
  Datatypes.length v1 = _unsafe_struct_sz enclave_data ->
  config_ext_uart (unsafe_enclave_data_to_config v0) && config_ext_uart (unsafe_enclave_data_to_config v1) = false ->
  success_or_default (interp_bits2 And (_unsafe_get_field enclave_req "ext_uart" (_unsafe_get_field enclave_data "data" v0))
(_unsafe_get_field enclave_req "ext_uart" (_unsafe_get_field enclave_data "data" v1))) Ob = Ob~0.
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
Lemma led_disjoint:
  forall v0 v1,
  Datatypes.length v0 = _unsafe_struct_sz enclave_data ->
  Datatypes.length v1 = _unsafe_struct_sz enclave_data ->
  config_ext_led (unsafe_enclave_data_to_config v0) && config_ext_led (unsafe_enclave_data_to_config v1) = false ->
  success_or_default (interp_bits2 And (_unsafe_get_field enclave_req "ext_led" (_unsafe_get_field enclave_data "data" v0))
(_unsafe_get_field enclave_req "ext_led" (_unsafe_get_field enclave_data "data" v1))) Ob = Ob~0.
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
Import PfHelpers.
Lemma init_private_zeroed:
  forall st reg xs,
  forallb (fun reg => beq_dec st.[reg] (zeroes (unsafe_lookup_reg_type (reg)))) xs  = true ->
  In reg xs  ->
  st.[reg] = zeroes (unsafe_lookup_reg_type reg).
Proof.
  intros. rewrite forallb_forall in H.
   propositional. specialize ( H _ H0). simplify. auto.
Qed.

Definition dummy_ext_mem: external_mem_t :=
  {| ext_resp := None;
     ext_mem := fun _ => None
  |}.
  Definition machine_st_to_ghost_core (st: koika_state_t) (core: ind_core_id) extract_rf : ghost_core_state_t :=
    let reg_state := SM (state core) in
    let reg_enc_data := SM (enc_data core) in
    let reg_enc_req := SM (enc_req core) in
    if beq_dec st.[_rid reg_state] (_enum enum_core_state "Waiting") then
      (GhostCoreState_Waiting (unsafe_enclave_data_to_config st.[_rid reg_enc_req])
         (extract_rf {| machine_koika_st := st;
                                       machine_mem_st := dummy_ext_mem  |} core))
    else
      (GhostCoreState_Enclave (unsafe_enclave_data_to_config st.[_rid reg_enc_data])).
  Definition get_ghost_running_config (st: ghost_core_state_t) : option enclave_config :=
    match st with
    | GhostCoreState_Enclave config => Some config
    | _ => None
    end.

  Definition get_impl_config impl_st (core: ind_core_id) extract_rf: option enclave_config :=
    get_ghost_running_config (machine_st_to_ghost_core (impl_st) core extract_rf).

  Definition is_sm_core0_turn (st: Environments.state_t) : bool :=
    beq_dec st.[_rid (SM clk)] [false].

  Definition is_sm_core1_turn (st: Environments.state_t) : bool :=
    beq_dec st.[_rid (SM clk)] [true].

  Definition is_sm_turn (core: ind_core_id) (st: Environments.state_t) : bool :=
    match core with
    | CoreId0 => is_sm_core0_turn st
    | CoreId1 => is_sm_core1_turn st
    end.

  Record wf_external_observations (obs: external_observations_t): Prop :=
    { wf_uart_write: Datatypes.length obs.(obs_uart_write) = unsafe_get_ext_fn_arg_type (_ext ext_uart_write);
      wf_uart_read: Datatypes.length obs.(obs_uart_read) = unsafe_get_ext_fn_arg_type (_ext ext_uart_read);
      wf_led: Datatypes.length obs.(obs_led) = unsafe_get_ext_fn_arg_type (_ext ext_led);
      wf_finish: Datatypes.length obs.(obs_finish) = unsafe_get_ext_fn_arg_type (_ext ext_finish);
    }.
  Definition wf_spec_output_config (spec_out: external_observations_t) (config: option enclave_config): Prop :=
    match config with
    | Some config =>
          (config_ext_uart config = false ->
           (obs_uart_write spec_out = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_uart_write))) /\
           (obs_uart_read spec_out = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_uart_read)))
          ) /\
          (config_ext_led config = false ->
           obs_led spec_out = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_led))) /\
          (config_ext_finish config = false ->
           obs_finish spec_out = zeroes (unsafe_get_ext_fn_arg_type (_ext ext_finish)))
    | None => spec_out = empty_external_obs
    end.

  Definition init_spec_koika_st
    (core: ind_core_id) params (turn sm_clk: vect_t) :=
             match core with
             | CoreId0 =>
                 initial_koika_state params dummy_core_init_params
                   turn sm_clk
             | CoreId1 =>
                 initial_koika_state dummy_core_init_params params
                   turn sm_clk
             end.

Module PfLemmas (EnclaveParams: EnclaveParams_sig)
                (SecurityParams: SecurityParams_sig EnclaveParams).
  Import SecurityParams.Machine.

  Module Impl := FullMachine.
  (* Module Core0 := Machine.SM.Core0. *)
  (* Module Core0Params := Machine.SM.Core0_params. *)
  (* Module Core1 := Machine.SM.Core1. *)
  (* Module Core1Params := Machine.SM.Core1_params. *)
  (* Module Memory := Machine.SM.Memory. *)
  (* Module MemoryParams := Machine.SM.Memory_params. *)
  Import SecurityParams.
  Import Spec.
  (* Module SM := Machine.SM. *)
  Notation impl_state_t := machine_state_t.
  Import PfHelpers.

  Notation reg_t := (@Syntax.reg_t debug_id_ty).

  Lemma impl_interp_cycle_correct:
      forall sigma koika_st,
        strong_WF_state reg_type_env koika_st ->
        WF_ext_sigma _ext_fn_tys sigma ->
        (* WF_int_fn_env Machine.reg_types ext_fn_types Machine.int_fns Machine.struct_defs -> *)
        match interp_scheduler sigma
               id_int_fns
               id_struct_defs
               koika_st
               Impl.id_rules
               Impl.schedule with
        | Success log => strong_WF_state reg_type_env (commit_update koika_st log.(Log__koika)) /\
                          WF_ext_log _ext_fn_tys log.(Log__ext)
        | _ => False
        end.
    Proof.
      intros * Hwf_state Hwf_ext.
      eapply typecheck_schedule_correct' with (ext_fn_types := _ext_fn_tys); try assumption.
      - apply Impl.typecheck_schedule_Success.
      - auto with WF_auto.
      - auto with WF_auto.
      - unfold WF_int_fn_env. reflexivity.
  Qed.
  Lemma spec0_interp_cycle_correct:
      forall sigma koika_st,
        strong_WF_state reg_type_env koika_st ->
        WF_ext_sigma _ext_fn_tys sigma ->
        (* WF_int_fn_env Machine.reg_types ext_fn_types Machine.int_fns Machine.struct_defs -> *)
        match interp_scheduler sigma
                               id_int_fns
                               id_struct_defs
               koika_st
               Impl.id_rules
               Core0Machine.schedule with
        | Success log => strong_WF_state reg_type_env (commit_update koika_st log.(Log__koika)) /\
                          WF_ext_log _ext_fn_tys log.(Log__ext)
        | _ => False
        end.
    Proof.
      intros * Hwf_state Hwf_ext.
      eapply typecheck_schedule_correct' with (ext_fn_types := _ext_fn_tys); try assumption.
      - apply Core0Machine.typecheck_schedule_Success.
      - auto with WF_auto.
      - auto with WF_auto.
      - unfold WF_int_fn_env. reflexivity.
  Qed.
  Lemma spec1_interp_cycle_correct:
      forall sigma koika_st,
        strong_WF_state reg_type_env koika_st ->
        WF_ext_sigma _ext_fn_tys sigma ->
        (* WF_int_fn_env Machine.reg_types ext_fn_types Machine.int_fns Machine.struct_defs -> *)
        match interp_scheduler sigma
               id_int_fns
               id_struct_defs
               koika_st
               Impl.id_rules
               Core1Machine.schedule with
        | Success log => strong_WF_state reg_type_env (commit_update koika_st log.(Log__koika)) /\
                          WF_ext_log _ext_fn_tys log.(Log__ext)
        | _ => False
        end.
    Proof.
      intros * Hwf_state Hwf_ext.
      eapply typecheck_schedule_correct' with (ext_fn_types := _ext_fn_tys); try assumption.
      - apply Core1Machine.typecheck_schedule_Success.
      - auto with WF_auto.
      - auto with WF_auto.
      - unfold WF_int_fn_env. reflexivity.
  Qed.
  Lemma impl_interp_modular_schedule :
    forall sigma st log,
        interp_scheduler
          sigma id_int_fns id_struct_defs st Impl.id_rules
               Impl.schedule = Success log ->
      interp_modular_schedule
          sigma id_int_fns id_struct_defs Impl.id_rules st
               modular_schedule =
        Success (commit_update st log.(Log__koika), log.(Log__ext)).
  Proof.
    intros. eapply check_modular_conflicts_correct.
    - vm_compute. reflexivity.
    - assumption.
  Qed.


  Lemma mem_push_request__success:
    forall log mem,
    WF_ext_log _ext_fn_tys log ->
    WF_ext_mem mem ->
    match mainmem__ext (unsafe_get_ext_call_from_log log (_ext ext_mainmem)) mem with
    | Success v => WF_ext_mem v
    | _ => False
    end.
  Proof.
    intros * hwf_log hwf_mem.
    consider mainmem__ext.
    repeat unsafe_auto_simplify_structs.
    destruct (case_singleton_bv _ H0); subst; auto.
    - consider update_dram. simpl.
      repeat unsafe_auto_simplify_structs; auto.
      destruct_match; simplify;
        constructor; simpl; propositional; simplify; simpl; auto.
      + destruct hwf_mem; auto.
        destruct_match; auto.
        consider WF_dram. eauto.
      + unfold WF_dram. intros *. (* destruct_match; propositional; simplify; auto. *)
        destruct hwf_mem. eapply WF_ext_mem__dram0; eauto.
      + unfold WF_dram. intros *. destruct_match; propositional; simplify; auto.
        destruct hwf_mem. eapply WF_ext_mem__dram0; eauto.
    - constructor; simpl; propositional; try discriminate.
      destruct hwf_mem; auto.
  Qed.

  Lemma WF_ext_log_observations:
    forall log,
    WF_ext_log _ext_fn_tys log ->
    wf_external_observations (get_ext_observations log).
  Proof.
    intros. consider get_ext_observations. consider WF_ext_log.
    consider @lookup_ext_fn. consider _unsafe_get_ext_call_from_log;
      consider SemanticUtils.unsafe_get_ext_call_from_log; consider @SortedExtFnEnv.opt_get.
    constructor; simpl.
    1: specialize (H (_ext ext_uart_write)).
    2: specialize (H (_ext ext_uart_read)).
    3: specialize (H (_ext ext_led)).
    4: specialize (H (_ext ext_finish)).
    all: repeat destruct_match; propositional;
         specialize (H v); propositional; simplify;
      unfold unsafe_get_ext_fn_arg_type, SemanticUtils.unsafe_get_ext_fn_arg_type;
      unfold lookup_ext_fn; simpl_match; auto.
    all: setoid_rewrite Heqo0; auto.
  Qed.
  Hint Resolve WF_ext_log_observations: modularity.

End PfLemmas.
