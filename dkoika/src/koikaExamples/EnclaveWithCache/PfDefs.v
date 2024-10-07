Require Import rv_cache_isolation.Common.
Require Import rv_cache_isolation.SecurityMonitor.

Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.
Require Import koikaExamples.EnclaveWithCache.Impl.
Require Import koikaExamples.EnclaveWithCache.Spec.
Require Import koikaExamples.EnclaveWithCache.Theorem.
Require Import koikaExamples.EnclaveWithCache.Utils.
Require Import FunctionalExtensionality.
Require Import koikaExamples.EnclaveWithCache.ExtractionUtils.
Require Import koikaExamples.EnclaveWithCache.ProofUtils.

Import ExternalMemory.
Import TopLevelModuleHelpers.


Record WF_ext_mainmem (mem: external_mainmem_t) : Prop :=
    { WF_ext_mem__resp__byte_en: forall resp, mem.(ext_resp) = Some resp -> Datatypes.length resp.(mem_resp_byte_en) = 4;
      WF_ext_mem__resp__addr: forall resp, mem.(ext_resp) = Some resp -> Datatypes.length resp.(mem_resp_addr) = addr_sz;
      WF_ext_mem__resp__data: forall resp, mem.(ext_resp) = Some resp -> Datatypes.length resp.(mem_resp_data) = data_sz;
      WF_ext_mem__dram: WF_dram mem.(ext_mem)
    }.

Record WF_cache (cache: external_cache_t) : Prop :=
  { WF_cache_resp: forall resp, cache.(ext_cache_resp) = Some resp -> Datatypes.length resp = data_sz;
    WF_cache_sram: forall addr data, cache.(ext_cache) addr = Some data -> Datatypes.length data = data_sz }.
Record WF_meta (meta: external_metadata_t) : Prop :=
  { WF_meta_resp: forall resp, meta.(ext_metadata_resp) = Some resp -> Datatypes.length resp = _unsafe_struct_sz metadata_sig;
    WF_meta_sram: forall addr data, meta.(ext_metadata) addr = Some data -> Datatypes.length data = _unsafe_struct_sz metadata_sig }.

Record WF_ext_cache_pair (p: external_cache_pair_t) : Prop :=
  { WF_pair_cache: WF_cache p.(ext_pair_cache);
    WF_pair_meta: WF_meta p.(ext_pair_meta)
  }.

Record WF_ext_mem (mem: external_mem_t) : Prop :=
  { WF_ext_main_mem: WF_ext_mainmem mem.(ext_main_mem);
    WF_ext_l1_caches: forall mem_ty core, WF_ext_cache_pair (mem.(ext_l1_caches)  mem_ty core)
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
      destruct fn; try destruct core; cbv in Heqo0; simplify; reflexivity.
    }
    destruct_match; auto.
    destruct_match; subst; auto.
      specialize H with (1 := Heqo). propositional. simplify. setoid_rewrite Heqo1 in Heqo0.
        simplify; auto.
  Qed.
  #[global] Hint Resolve @WF_ext_mem__resp__byte_en : solve_invariants.
  #[global] Hint Resolve WF_ext_mem__resp__addr: solve_invariants.
  #[global] Hint Resolve WF_ext_mem__resp__data: solve_invariants.
  #[global] Hint Resolve WF_ext_main_mem: solve_invariants.
  #[global] Hint Resolve WF_ext_l1_caches: solve_invariants.
  #[global] Hint Resolve WF_pair_cache: solve_invariants.
  #[global] Hint Resolve WF_pair_meta: solve_invariants.
  #[global] Hint Resolve WF_cache_resp: solve_invariants.
  #[global] Hint Resolve WF_cache_sram: solve_invariants.
  #[global] Hint Resolve WF_meta_resp: solve_invariants.
  #[global] Hint Resolve WF_meta_sram: solve_invariants.

  Lemma mem_get_response__koika__Success:
    forall mem,
      WF_ext_mem mem ->
      match mem_get_response__koika mem.(ext_main_mem) with
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
  Lemma cache_get_response__koika__Success:
    forall mem mem_ty core arg,
      WF_ext_mem mem ->
      Datatypes.length arg = _unsafe_struct_sz cache_input_sig ->
      match cache_get_response__koika arg (ext_pair_cache (ext_l1_caches mem mem_ty core))  with
      | Success res => Datatypes.length res = _unsafe_struct_sz cache_output_sig
      | Failure _ => False
      end.
  Proof.
    intros * Hwf hlen. unfold cache_get_response__koika.
    repeat unsafe_auto_simplify_structs; auto.
    destruct_match; auto with simplify_bits.
    - assert (Datatypes.length v = 32) by (eauto with solve_invariants).
      destruct_match; [ discriminate | ].
      destruct_match.
      + destruct_match; [ | discriminate]. subst. unsafe_auto_simplify_structs; auto.
      + destruct_match; [ | discriminate]. reflexivity.
    - unsafe_auto_simplify_structs. auto.
  Qed.
  Lemma metadata_get_response__koika__Success:
    forall mem mem_ty core arg,
      WF_ext_mem mem ->
      Datatypes.length arg = _unsafe_struct_sz metadata_input_sig ->
      match metadata_get_response__koika arg (ext_pair_meta (ext_l1_caches mem mem_ty core))  with
      | Success res => Datatypes.length res = _unsafe_struct_sz metadata_output_sig
      | Failure _ => False
      end.
  Proof.
    intros * Hwf hlen. unfold metadata_get_response__koika.
    repeat unsafe_auto_simplify_structs; auto.
    destruct_match; auto with simplify_bits.
    - assert (Datatypes.length v = _unsafe_struct_sz metadata_sig) by (eauto with solve_invariants).
      destruct_match; [ discriminate | ].
      destruct_match.
      + destruct_match; [ | discriminate]. subst. unsafe_auto_simplify_structs; auto.
      + destruct_match; [ | discriminate]. reflexivity.
    - unsafe_auto_simplify_structs; auto.
  Qed.


  Lemma WF_mk_sigma_fn:
    forall mem inputs,
      WF_ext_mem mem ->
      WF_ext_sigma _ext_fn_tys (mk_sigma_fn mem inputs).
  Proof.
    intros * Hwf_mem.
    unfold WF_ext_sigma. unfold ext_fn_tys, lookup_ext_fn ; simpl;
    intros; repeat destruct_match; simplify; simpl; intros; autorewrite with simplify_bits; auto;
      unfold mk_sigma_fn; simpl.
    all: try match goal with
         | |- context[mem_get_response__koika] =>
             apply mem_get_response__koika__Success
         | |- context[cache_get_response__koika] =>
             apply cache_get_response__koika__Success
         | |- context[metadata_get_response__koika] =>
             apply metadata_get_response__koika__Success
         end; autorewrite with simplify_bits; auto.
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

Definition dummy_ext_cache : external_cache_t :=
  {| ext_cache_resp := None;
     ext_cache := fun _ => None
  |}.

Definition dummy_ext_meta: external_metadata_t :=
  {| ext_metadata_resp := None;
     ext_metadata := fun _ => None
  |}.

Definition dummy_ext_mem: external_mem_t :=
  {| ext_main_mem := {| ext_resp := None;
                        ext_mem := fun _ => None
                     |};
     ext_l1_caches := fun _ _ => {| ext_pair_cache := dummy_ext_cache;
                                 ext_pair_meta := dummy_ext_meta |}
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
    WF_ext_mainmem mem ->
    match mainmem__ext (unsafe_get_ext_call_from_log log (_ext ext_mainmem)) mem with
    | Success v => WF_ext_mainmem v
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
Lemma wf_cache_none:
  forall cache,
  WF_cache cache ->
  WF_cache {| ext_cache_resp := None; ext_cache := ext_cache cache |}.
Proof.
  constructor; simpl; propositional.
  - discriminate.
  - destruct H; eauto.
Qed.
#[global] Hint Resolve  wf_cache_none: solve_invariants.

Lemma wf_meta_none:
  forall meta,
  WF_meta meta ->
  WF_meta {| ext_metadata_resp := None; ext_metadata := ext_metadata meta |}.
Proof.
  constructor; simpl; propositional.
  - discriminate.
  - destruct H; eauto.
Qed.
#[global] Hint Resolve  wf_meta_none: solve_invariants.

Lemma update_cache_Success:
  forall v cache,
  (forall (addr : N) (data : data_t),
    cache addr = Some data -> Datatypes.length data = data_sz) ->
  Datatypes.length v = _unsafe_struct_sz cache_req_sig  ->
  match update_cache v cache  with
  | Success v  => WF_cache v
  | _ => False
  end.
Proof.
  intros * hcache hlen.
  consider update_cache.
  repeat (unsafe_auto_simplify_structs; auto; simplify).
  destruct_match; auto.
  - constructor; simpl; auto.
    intros. simplify. destruct_match; auto.
    eauto.
  - constructor; simpl; auto.
    + discriminate.
    + intro. destruct_match; auto; propositional; simplify; eauto.
      rewrite compute_with_byte_en_ok. auto.
Qed.
  Lemma cache_push_request__success:
    forall log cache mem_type core ,
    WF_ext_log _ext_fn_tys log ->
    WF_cache cache ->
    match cache__ext (unsafe_get_ext_call_from_log log (_ext (Memory.Memory.ext_cache mem_type core))) cache with
    | Success v => WF_cache v
    | _ => False
    end.
  Proof.
    intros * hwf_log hwf_mem.
    consider cache__ext.
    repeat (unsafe_auto_simplify_structs; [ solve[destruct mem_type; destruct core; unsafe_auto_simplify_structs] | ]).
    edestruct (case_singleton_bv s); subst; auto.
    - edestruct (case_singleton_bv s1); subst; auto.
      + apply update_cache_Success; eauto with solve_invariants.
      + destruct_match; auto.
        apply update_cache_Success; eauto with solve_invariants.
    - edestruct (case_singleton_bv s1 ); subst; auto.
      eauto with solve_invariants.
  Qed.
Lemma update_metadata_Success:
  forall v meta,
  (forall (addr : N) (data : data_t),
    meta addr = Some data -> Datatypes.length data = _unsafe_struct_sz metadata_sig) ->
  Datatypes.length v = _unsafe_struct_sz metadata_req_sig  ->
  match update_metadata v meta with
  | Success v  => WF_meta v
  | _ => False
  end.
Proof.
  intros * hmeta hlen.
  consider update_metadata.
  repeat (unsafe_auto_simplify_structs; auto; simplify).
  destruct_match; auto.
  - constructor; simpl; auto.
    intros. simplify. destruct_match; auto.
    eauto.
  - constructor; simpl; auto.
    + discriminate.
    + intro. destruct_match; auto; propositional; simplify; eauto.
Qed.

  Lemma meta_push_request__success:
    forall log meta mem_type core ,
    WF_ext_log _ext_fn_tys log ->
    WF_meta meta ->
    match metadata__ext (unsafe_get_ext_call_from_log log (_ext (Memory.Memory.ext_metadata mem_type core))) meta with
    | Success v => WF_meta v
    | _ => False
    end.
  Proof.
    intros * hwf_log hwf_mem.
    consider metadata__ext.
    repeat (unsafe_auto_simplify_structs; [ solve[destruct mem_type; destruct core; unsafe_auto_simplify_structs] | ]).
    edestruct (case_singleton_bv s); subst; auto.
    - edestruct (case_singleton_bv s1); subst; auto.
      + apply update_metadata_Success; eauto with solve_invariants.
      + destruct_match; auto.
        apply update_metadata_Success; eauto with solve_invariants.
    - edestruct (case_singleton_bv s1 ); subst; auto.
      eauto with solve_invariants.
  Qed.

  Lemma cache_pair_push_request__success:
    forall log metacache mem_type core ,
    WF_ext_log _ext_fn_tys log ->
    WF_ext_cache_pair metacache ->
    match cachepair__ext (unsafe_get_ext_call_from_log log (_ext (Memory.Memory.ext_metadata mem_type core)))
                       (unsafe_get_ext_call_from_log log (_ext (Memory.Memory.ext_cache mem_type core)))
                       metacache with
    | Success v => WF_ext_cache_pair v
    | _ => False
    end.
  Proof.
    intros * hwf_log hwf_mem.
    destruct hwf_mem.
    specialize meta_push_request__success with (1 := hwf_log) (2 := WF_pair_meta0) (mem_type := mem_type) (core := core).
    specialize cache_push_request__success with (1 := hwf_log) (2 := WF_pair_cache0) (mem_type := mem_type) (core := core).
    consider cachepair__ext.
    intros; simplify. constructor; auto.
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
Lemma WF_update_cache:
  forall cache new_data,
  WF_cache cache ->
  Datatypes.length new_data = _unsafe_struct_sz cache_req_sig ->
  match ExternalMemory.update_cache new_data (ExternalMemory.ext_cache cache) with
  | Success v => WF_cache v
  | Failure _ => False
  end.
Proof.
  intros * hwf hlen.  destruct hwf.
  consider ExternalMemory.update_cache.
  repeat (unsafe_auto_simplify_structs; [rewrite_solve | ]; simplify).
  destruct_match; simplify.
  - constructor; eauto. simpl.
    propositional; simplify.
    destruct_match; eauto.
  - constructor; simpl; propositional; [discriminate | ].
    bash_destruct H2; simplify; eauto.
    apply ExternalMemory.compute_with_byte_en_ok.
Qed.

Lemma WF_update_metadata:
  forall meta new_data,
  WF_meta meta ->
  Datatypes.length new_data = data_sz ->
  match ExternalMemory.update_metadata new_data (ExternalMemory.ext_metadata meta) with
  | Success v => WF_meta v
  | Failure _ => False
  end.
Proof.
  intros * hwf hlen.  destruct hwf.
  consider ExternalMemory.update_metadata.
  repeat (unsafe_auto_simplify_structs; [rewrite_solve | ]; simplify).
  destruct_match; simplify.
  - constructor; eauto. simpl.
    propositional; simplify.
    destruct_match; eauto.
  - constructor; simpl; propositional; [discriminate | ].
    bash_destruct H2; simplify; eauto.
Qed.

  Lemma meta_update__success:
    forall log meta mem_ty core,
    WF_ext_log _ext_fn_tys log ->
    WF_meta meta ->
    match ExternalMemory.metadata__ext (obs_meta (get_mem_observations log) mem_ty core) meta with
    | Success v => WF_meta v
    | _ => False
    end.
  Proof.
    intros * hlog hmeta. pose proof hmeta as hmeta'. destruct hmeta.
    consider ExternalMemory.metadata__ext.
    unfold obs_meta. unfold get_mem_observations.
    unsafe_auto_simplify_structs.
    { destruct mem_ty; destruct core; unsafe_auto_simplify_structs. }
    custom_simplify; auto.
    unsafe_auto_simplify_structs.
    { destruct mem_ty; destruct core; unsafe_auto_simplify_structs. }
    custom_simplify; auto.
    unsafe_auto_simplify_structs.
    { destruct mem_ty; destruct core; unsafe_auto_simplify_structs. }
    custom_simplify; auto.
    destruct_match; [discriminate | ].
    destruct v; [ | discriminate].
    destruct s; [ discriminate | ].
    destruct s; [ | discriminate ].

    destruct_match; propositional.
    - destruct_match; propositional.
      + eapply WF_update_metadata; eauto.
      + constructor; eauto. simpl.
        discriminate.
    - destruct_match; propositional.
      destruct_match; propositional.
      eapply WF_update_metadata; eauto.
  Qed.
  Lemma cache_update__success:
    forall log cache mem_ty core,
    WF_ext_log _ext_fn_tys log ->
    WF_cache cache  ->
    match ExternalMemory.cache__ext (obs_cache (get_mem_observations log) mem_ty core) cache with
    | Success v => WF_cache v
    | _ => False
    end.
  Proof.
    intros * hwf hcache. pose proof hcache as hcache'. destruct hcache.
    consider ExternalMemory.cache__ext.
    unfold obs_cache. unfold get_mem_observations.
    unsafe_auto_simplify_structs; custom_simplify; auto.
    { destruct mem_ty; destruct core; unsafe_auto_simplify_structs. }
    unsafe_auto_simplify_structs; custom_simplify; auto.
    { destruct mem_ty; destruct core; unsafe_auto_simplify_structs. }
    unsafe_auto_simplify_structs; custom_simplify; auto.
    { destruct mem_ty; destruct core; unsafe_auto_simplify_structs. }
    destruct_match; [discriminate | ].
    destruct v; [ | discriminate]; propositional.
    destruct s; [ discriminate | ].
    destruct s; [ | discriminate].
    destruct_match; propositional.
    - destruct_match; propositional.
      + apply WF_update_cache; auto.
      + constructor; eauto. simpl.
        discriminate.
    - destruct_match; propositional.
      destruct_match; propositional.
      apply WF_update_cache; auto.
  Qed.

  Lemma cache_pair_update__success:
    forall log mem_ty core cache_pair,
    WF_ext_log _ext_fn_tys log ->
    WF_ext_cache_pair cache_pair ->
    match ExternalMemory.cachepair__ext (obs_meta (get_mem_observations log) mem_ty core)
                                      (obs_cache (get_mem_observations log) mem_ty core)
                                      cache_pair with
    | Success v => WF_ext_cache_pair v
    | _ => False
    end.
  Proof.
    intros * hwf_log hwf_cache.
    consider ExternalMemory.cachepair__ext. destruct hwf_cache.
    specialize cache_update__success with (1 := hwf_log) (2 := WF_pair_cache0); intros success_cache.
    specialize (success_cache mem_ty core). simplify.
    specialize meta_update__success with (1 := hwf_log) (2 := WF_pair_meta0); intros success_meta.
    specialize (success_meta mem_ty core). simplify.
    constructor; auto.
  Qed.

Lemma update_memory_success:
  forall (log : ext_log_t) (mem : ExternalMemory.external_mem_t),
    WF_ext_log _ext_fn_tys log ->
    WF_ext_mem mem ->
    match ExternalMemory.update_memory (get_mem_observations log) mem with
    | Success v => WF_ext_mem v
    | Failure _ => False
    end.
Proof.
  intros * hwf Hwf_mem.
  consider ExternalMemory.update_memory.
  destruct Hwf_mem.
  specialize mem_push_request__success with (mem := ExternalMemory.ext_main_mem mem) (log := log); intros ext_mem. propositional.
  specialize cache_pair_update__success with (1 := hwf) (2 := WF_ext_l1_caches0 imem CoreId0) (mem_ty := imem) (core := CoreId0).
  specialize cache_pair_update__success with (1 := hwf) (2 := WF_ext_l1_caches0 imem CoreId1) (mem_ty := imem) (core := CoreId1).
  specialize cache_pair_update__success with (1 := hwf) (2 := WF_ext_l1_caches0 dmem CoreId1) (mem_ty := dmem) (core := CoreId1).
  specialize cache_pair_update__success with (1 := hwf) (2 := WF_ext_l1_caches0 dmem CoreId0) (mem_ty := dmem) (core := CoreId0).
  intros; simplify.
  destruct_match.
  - setoid_rewrite Heqr4 in Heqr5. simplify.
    constructor; simpl; auto.
    intros; repeat destruct_match; eauto.
  - setoid_rewrite Heqr4 in Heqr5. simplify.
Qed.
Lemma ext_mem_update_memory_implies_main_mem:
  forall obs mem mem',
  ExternalMemory.update_memory obs mem = Success mem' ->
  ExternalMemory.mainmem__ext (obs_mainmem obs) (ExternalMemory.ext_main_mem mem)
    = Success (ExternalMemory.ext_main_mem mem').
Proof.
  consider ExternalMemory.update_memory.
  intros; simplify; auto.
Qed.

Lemma ext_mem_update_memory_implies_cache:
  forall obs mem mem' cache core,
  ExternalMemory.update_memory obs mem = Success mem' ->
  ExternalMemory.cachepair__ext (obs_meta obs cache core ) (obs_cache obs cache core )
                              (ExternalMemory.ext_l1_caches mem cache core)
    = Success (ExternalMemory.ext_l1_caches mem' cache core).
Proof.
  consider ExternalMemory.update_memory.
  intros; simplify; auto; simpl;
    destruct cache; destruct core; auto.
Qed.

End PfLemmas.
