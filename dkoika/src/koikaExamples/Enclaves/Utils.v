Require Import rv_isolation.Common.
Require Import rv_isolation.SecurityMonitor.

Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.Impl.
Require Import koika.Frontend.

Definition _smrid reg := _rid (SM reg).
Definition _smid reg := reg_to_debug_id (SM reg).
Definition _mrid reg := _rid (Memory reg).
Definition _mid reg := reg_to_debug_id (Memory reg).
Definition _crid core_id reg := reg_to_debug_id ((core_reg core_id) reg).
Definition _crid0 reg := reg_to_debug_id (Core0 reg).
Definition _crid1 reg := reg_to_debug_id (Core0 reg).
Instance EqDec_FiniteType' {T} {FT: FiniteType.FiniteType T} : EqDec T | 3.
Proof.
  econstructor; intros.
  destruct (PeanoNat.Nat.eq_dec (FiniteType.finite_index t1) (FiniteType.finite_index t2)) as [ ? | Hneq ].
  - eauto using FiniteType.finite_index_injective.
  - right; intro Habs; apply (f_equal FiniteType.finite_index) in Habs.
    contradiction.
Defined.

(* Require Import koikaExamples.Enclaves.TypeDefs. *)
Module PfHelpers.
  Import Memory.
  Import SecurityMonitor.
  Import RVCore.
  Import RV32Core.

    Definition get_valid_addr_from_push_req (push_req: vect_t) : option vect_t  :=
      match _get_field mem_input "put_valid" push_req  with
      | Success [true] =>
        match _get_field mem_input "put_request" push_req with
        | Success req =>
            match _get_field mem_req "addr" req with
            | Success addr => Some addr
            | _ => None
            end
        | _ => None
        end
      | _ => None
      end.
    Definition region_in_config (region: mem_region) (config: enclave_config) : bool :=
      match region with
      | MemRegion_Enclave eid => beq_dec eid config.(config_eid)
      | MemRegion_Shared sid => config.(config_shared_regions) sid
      | MemRegion_Other => false
      end.

    Definition region_in_option_config (region: mem_region) (config: option enclave_config) : bool:=
      match config with
      | Some config => region_in_config region config
      | None => false
      end.
    Definition addr_in_config enclave_sig (addr: N) (config: enclave_config) : Prop :=
      exists region, addr_in_region enclave_sig region addr = true /\
                  region_in_config region config = true.

    Definition addr_in_config_dec enclave_sig (addr: N) (config: enclave_config) : bool :=
        (addr_in_region enclave_sig (MemRegion_Enclave config.(config_eid)) addr)
      || existsb (fun region => config.(config_shared_regions) region &&
                              addr_in_region enclave_sig (MemRegion_Shared region) addr)
        [Shared01; Shared02; Shared03; Shared12; Shared13; Shared23].

    Definition mem_addr_in_option_config enclave_sig (addr: vect_t) (config: option enclave_config) : Prop :=
      match config with
      | Some config => addr_in_config enclave_sig (to_N addr) config
      | None => False
      end.

    Lemma addr_in_region_implies_in_config:
      forall enclave_sig addr region config,
        addr_in_region enclave_sig region addr = true ->
        region_in_config region config = true ->
        addr_in_config enclave_sig addr config.
    Proof.
      unfold addr_in_config; propositional; eauto.
    Qed.

    Lemma addr_in_config_iff enclave_sig (addr: N) (config: enclave_config) :
      addr_in_config_dec enclave_sig addr config = true <-> addr_in_config enclave_sig addr config.
    Proof.
      split; unfold addr_in_region; intros H.
      - consider addr_in_config_dec. rewrite orb_true_iff in H.
        destruct H.
        + eapply addr_in_region_implies_in_config; eauto. simpl. rewrite beq_dec_refl. auto.
        + rewrite existsb_exists in H. propositional.
          rewrite andb_true_iff in *. propositional.
          eapply addr_in_region_implies_in_config; eauto.
      - consider addr_in_config_dec. rewrite orb_true_iff.
        consider addr_in_config. propositional. destruct region.
        + simpl in H2. simplify. auto.
        + simpl in H2. right. rewrite existsb_exists. exists id.
          rewrite H2. rewrite H1. simpl; destruct id; split; eauto.
          * right; auto.
          * right; right; auto.
       + simpl in H1. discriminate.
    Qed.
    Definition unsafe_enclave_id_vect_to_eid (vect: vect_t) : enclave_id :=
      if beq_dec vect (of_nat 2 0) then Enclave0
      else if beq_dec vect (of_nat 2 1) then Enclave1
      else if beq_dec vect (of_nat 2 2) then Enclave2
      else Enclave3.

    Definition unsafe_shared_regions_vect_to_bool (vect: vect_t) (region: shared_id) : bool :=
      match region with
      | Shared01 => List.nth 0 vect false
      | Shared02 => List.nth 1 vect false
      | Shared03 => List.nth 2 vect false
      | Shared12 => List.nth 3 vect false
      | Shared13 => List.nth 4 vect false
      | Shared23 => List.nth 5 vect false
      end.

    Definition fifo_addrs_in_range enclave_sig (st: Environments.state_t) (config: enclave_config)
                                   (reg_valid reg_data: N) : Prop :=
        (st.[reg_valid] = Ob~1 ->
         mem_addr_in_option_config enclave_sig
           (_unsafe_get_field mem_req "addr" st.[reg_data])  (Some config)).

    Definition fifo_addrs_not_in_range enclave_sig (st: Environments.state_t) (config: enclave_config)
                                   (reg_valid reg_data: N) : Prop :=
        st.[reg_valid] = Ob~1 ->
         mem_addr_in_option_config enclave_sig
           (_unsafe_get_field mem_req "addr" st.[reg_data]) (Some config) ->
         False.

    Definition is_mem_core0_push_turn (st: Environments.state_t) : bool :=
      beq_dec st.[_rid (Memory Memory.turn)] Ob~0~0.

    Definition is_mem_core1_push_turn (st: Environments.state_t) : bool :=
      beq_dec st.[_rid (Memory Memory.turn)] Ob~1~0.

    Definition is_mem_core0_read_turn (st: Environments.state_t) : bool :=
      beq_dec st.[_rid (Memory Memory.turn)] Ob~0~1.

    Definition is_mem_core1_read_turn (st: Environments.state_t) : bool :=
      beq_dec st.[_rid (Memory Memory.turn)] Ob~1~1.

    Definition is_mem_core_read_turn (core: ind_core_id) (st: Environments.state_t) : bool :=
      match core with
      | CoreId0 => is_mem_core0_read_turn st
      | CoreId1 => is_mem_core1_read_turn st
      end.

    Definition is_mem_core_read_turn' (core: ind_core_id) (cycles: nat) : bool :=
      match core with
      | CoreId0 => beq_dec (Nat.modulo cycles 4) 1
      | CoreId1 => beq_dec (Nat.modulo cycles 4) 3
      end.

    Definition mem_core0_write_turn := Ob~0~0.
    Definition mem_core1_write_turn := Ob~1~0.
    Definition mem_core0_read_turn := Ob~0~1.
    Definition mem_core1_read_turn := Ob~1~1.

    Definition is_mem_core_write_turn (core: ind_core_id) (st: Environments.state_t) : bool :=
      match core with
      | CoreId0 => beq_dec st.[_rid (Memory Memory.turn)] mem_core0_write_turn
      | CoreId1 => beq_dec st.[_rid (Memory Memory.turn)] mem_core1_write_turn
      end.


    Definition is_mem_core_write_turn' (core: ind_core_id) (cycles: nat) : bool :=
      match core with
      | CoreId0 => beq_dec (Nat.modulo cycles 4) 0
      | CoreId1 => beq_dec (Nat.modulo cycles 4) 2
      end.

    Definition ext_core_fifos_regs (core: ind_core_id) :=
    Eval vm_compute in (
      map (core_reg core)
      ((map toSM (@FiniteType.finite_elements toSMEnc.reg_t _)) ++
       (map toIMem (@FiniteType.finite_elements MemReqBypass.reg_t _)) ++
       (map toDMem (@FiniteType.finite_elements MemReqBypass.reg_t _)) ++
       (map toMMIO (@FiniteType.finite_elements MemReqBypass .reg_t _)) ++
       (map fromIMem (@FiniteType.finite_elements MemResp.reg_t _)) ++
       (map fromDMem (@FiniteType.finite_elements MemResp.reg_t _)) ++
       (map fromMMIO (@FiniteType.finite_elements MemResp.reg_t _)))).
Open Scope list_scope.
    Definition ext_core_regs (core: ind_core_id) :=
    Eval vm_compute in (
      (map (core_reg core) [Core.purge; Core.init_pc]) ++ (ext_core_fifos_regs core)).
    Definition private_core_regs core : list SecurityMonitor.reg_t :=
    Eval vm_compute in (
      map (core_reg core)
        ((map f2d (@FiniteType.finite_elements fromFetch.reg_t _)) ++
         (map f2dprim (@FiniteType.finite_elements waitFromFetch.reg_t _)) ++
         (map d2e (@FiniteType.finite_elements fromDecode.reg_t _)) ++
         (map e2w FiniteType.finite_elements) ++
         (map rf FiniteType.finite_elements) ++
         (map mulState FiniteType.finite_elements) ++
         (map scoreboard FiniteType.finite_elements) ++
         [Core.core_id; Core.cycle_count; Core.instr_count; Core.pc; Core.epoch; Core.freeze_fetch]
        )).
  Definition memory_to_sm_fifos (core: ind_core_id) : list SecurityMonitor.reg_t :=
      map Memory ((map (Memory.fromIMem core) FiniteType.finite_elements) ++
                  (map (Memory.fromDMem core) FiniteType.finite_elements)
                 ).

  Definition memory_to_sm_reg_pairs (core: ind_core_id) :=
    [(Memory.fromIMem core MemRespBypass.valid0,Memory.fromIMem core MemRespBypass.data0)
    ;(Memory.fromDMem core MemRespBypass.valid0,Memory.fromDMem core MemRespBypass.data0)
    ].
  Definition core_to_sm_fifo_reg_pairs :=
    [(RV32Core.toIMem MemReqBypass.valid0, RV32Core.toIMem MemReqBypass.data0)
    ;(RV32Core.toDMem MemReqBypass.valid0,RV32Core.toDMem MemReqBypass.data0)
    ;(RV32Core.toMMIO MemReqBypass.valid0,RV32Core.toMMIO MemReqBypass.data0)
    ;(RV32Core.toSM toSMEnc.valid0,RV32Core.toSM toSMEnc.data0)
    ].

  Definition memory_to_sm_fifos__valid (core: ind_core_id) : list SecurityMonitor.reg_t :=
      map Memory ((map (Memory.fromIMem core) [MemRespBypass.valid0]) ++
                  (map (Memory.fromDMem core) [MemRespBypass.valid0])
                 ).


  Definition sm_to_memory_fifos (core: ind_core_id) : list SecurityMonitor.reg_t :=
      map Memory ((map (Memory.toIMem core) FiniteType.finite_elements) ++
                  (map (Memory.toDMem core) FiniteType.finite_elements)
                 ).
  Definition sm_to_memory_pairs (core: ind_core_id) :=
    [(Memory.toIMem core MemReq.valid0,Memory.toIMem core MemReq.data0)
    ;(Memory.toDMem core MemReq.valid0,Memory.toDMem core MemReq.data0)
    ].


    Definition ext_mem_regs (core: ind_core_id) : list SecurityMonitor.reg_t :=
      ([Memory (Memory.purge core)])  ++
       (memory_to_sm_fifos core) ++
       (sm_to_memory_fifos core).

  Definition sm_to_memory_fifos__valid (core: ind_core_id) : list SecurityMonitor.reg_t :=
      map Memory ((map (Memory.toIMem core) [MemReq.valid0]) ++
                  (map (Memory.toDMem core) [MemReq.valid0])
                 ).


    Definition mem_regs_to_reset (core: ind_core_id) :=
      sm_to_memory_fifos__valid core ++  [Memory (Memory.priv_turn core)].
    Definition memory_regs :=
      ((map Memory (@FiniteType.finite_elements _ Memory.FiniteType_reg_t))).

    Definition mem_regs (core: ind_core_id) :=
      map Memory ([Memory.purge core; Memory.turn; Memory.priv_turn core] ++
                  (map (Memory.toIMem core) FiniteType.finite_elements) ++
                  (map (Memory.toDMem core) FiniteType.finite_elements) ++
                  (map (Memory.fromIMem core) FiniteType.finite_elements) ++
                  (map (Memory.fromDMem core) FiniteType.finite_elements)
                 ).

    Definition private_mem_regs (core: ind_core_id)  :=
      map Memory [Memory.priv_turn core].

    Definition to_mmio_regs (core: ind_core_id) :=
      (map (toMemMMIO core) FiniteType.finite_elements).
    Definition from_mmio_regs (core: ind_core_id) :=
      (map (fromMemMMIO core) FiniteType.finite_elements).

    Definition to_mmio_regs__valid (core: ind_core_id) :=
      (map (toMemMMIO core) [MemReqBypass.valid0]).
    Definition from_mmio_regs_valid (core: ind_core_id) :=
      (map (fromMemMMIO core) [MemRespBypass.valid0]).


    Definition private_sm_regs (core: ind_core_id) :=
      (map SM ([state core; enc_req core; enc_data core; sm_reset core; clk])) ++
      (to_mmio_regs core) ++ (from_mmio_regs core).

  Definition sm_regs core :=
    (private_sm_regs core) ++ (ext_core_regs core) ++ (ext_mem_regs core).

  Existing Instance Core.FiniteType_reg_t.

  Definition core_regs (core: ind_core_id)  :=
    Eval vm_compute in ((map (core_reg core) (@FiniteType.finite_elements _ Core.FiniteType_reg_t))).

  (* Existing Instance Machine.FiniteType_reg_t. *)

  Definition is_core_reg (id: ind_core_id) (reg: SecurityMonitor.reg_t) : bool :=
    is_someb (find (EqDec.beq_dec reg) (core_regs id)).

   (* Definition core_sim (core_id: ind_core_id) (machine1 machine2: koika_state_t) : Prop := *)
   (*    forall reg, In reg ((core_regs core_id)) -> *)
   (*           machine1.[_rid reg] = machine2.[_rid reg]. *)

  Definition core_to_sm_fifos (core: ind_core_id) : list SecurityMonitor.reg_t :=
    Eval vm_compute in (
      map (core_reg core)
      ((map toSM (@FiniteType.finite_elements toSMEnc.reg_t _)) ++
       (map toIMem (@FiniteType.finite_elements MemReqBypass.reg_t _)) ++
       (map toDMem (@FiniteType.finite_elements MemReqBypass.reg_t _)) ++
       (map toMMIO (@FiniteType.finite_elements MemReqBypass .reg_t _)))).

  Definition core_to_sm_fifos__valid (core: ind_core_id) : list SecurityMonitor.reg_t :=
    Eval vm_compute in (
      map (core_reg core)
      ((map toSM [toSMEnc.valid0]) ++
       (map toIMem [MemReqBypass.valid0]) ++
       (map toDMem [MemReqBypass.valid0]) ++
       (map toMMIO [MemReqBypass.valid0]))).

  Definition sm_to_core_fifo_reg_pairs :=
    [(RV32Core.fromIMem MemResp.valid0,RV32Core.fromIMem MemResp.data0)
    ;(RV32Core.fromDMem MemResp.valid0,RV32Core.fromDMem MemResp.data0)
    ;(RV32Core.fromMMIO MemResp.valid0,RV32Core.fromMMIO MemResp.data0)
    ].

  Definition sm_to_core_fifos (core: ind_core_id) : list SecurityMonitor.reg_t :=
    Eval vm_compute in (
    (map (core_reg core)
       ((map fromIMem (@FiniteType.finite_elements MemResp.reg_t _)) ++
        (map fromDMem (@FiniteType.finite_elements MemResp.reg_t _)) ++
        (map fromMMIO (@FiniteType.finite_elements MemResp.reg_t _))))).

  Definition sm_to_core_fifos__data (core: ind_core_id) : list SecurityMonitor.reg_t :=
    Eval vm_compute in (
    (map (core_reg core)
       ((map fromIMem [MemResp.data0]) ++
        (map fromDMem [MemResp.data0]) ++
        (map fromMMIO [MemResp.data0])))).

  Definition core_fifo_reg_pairs :=
    [(RV32Core.toIMem MemReqBypass.valid0, RV32Core.toIMem MemReqBypass.data0)
    ;(RV32Core.toDMem MemReqBypass.valid0,RV32Core.toDMem MemReqBypass.data0)
    ;(RV32Core.toMMIO MemReqBypass.valid0,RV32Core.toMMIO MemReqBypass.data0)
    ;(RV32Core.fromIMem MemResp.valid0,RV32Core.fromIMem MemResp.data0)
    ;(RV32Core.fromDMem MemResp.valid0,RV32Core.fromDMem MemResp.data0)
    ;(RV32Core.fromMMIO MemResp.valid0,RV32Core.fromMMIO MemResp.data0)
    ;(RV32Core.toSM RV32Core.toSMEnc.valid0,RV32Core.toSM RV32Core.toSMEnc.data0)
    ;(RV32Core.f2d RV32Core.fromFetch.valid0,RV32Core.f2d RV32Core.fromFetch.data0)
    ;(RV32Core.f2dprim RV32Core.waitFromFetch.valid0,RV32Core.f2dprim RV32Core.waitFromFetch.data0)
    ;(RV32Core.d2e RV32Core.fromDecode.valid0,RV32Core.d2e RV32Core.fromDecode.data0)
    ;(RV32Core.e2w RV32Core.fromExecute.valid0,RV32Core.e2w RV32Core.fromExecute.data0)
    ].

  Definition core_regs_to_reset core : list SecurityMonitor.reg_t :=
    remove_regs (core_regs core) ((map (core_reg core)) [core_id; init_pc; purge] ++
                                  (core_to_sm_fifos core) ++
                                  (map (core_reg core) (map rf FiniteType.finite_elements)) ++
                                  (map (core_reg core) (map snd core_fifo_reg_pairs))
                                  (* (sm_to_core_fifos__data core) *)
                                 ).

  Definition mem_core_read_turn (core: ind_core_id) :=
    match core with
    | CoreId0 => mem_core0_read_turn
    | CoreId1 => mem_core1_read_turn
    end.
  Definition mem_core_write_turn (core: ind_core_id) :=
    match core with
    | CoreId0 => mem_core0_write_turn
    | CoreId1 => mem_core1_write_turn
    end.

   Definition unsafe_lookup_reg_type (reg:N ) :=
     match find (fun '(r', _) => beq_dec reg r') _reg_types with
     | Some (_, n) => n
     | _ => 0
     end.
    Lemma _get_field_implies_unsafe_get_field:
      forall s (str_fld: string) v (flds: list (debug_id_ty * nat)) (id_fld: debug_id_ty) v',
        _get_field s str_fld v = Success v' ->
        match _lookup_struct s with
        | Success s => Success s.(dstruct_fields)
        | _ => Failure tt
        end = Success flds ->
        match _lookup_struct s with
        | Success s =>  lookup_dstruct_field s str_fld
        | _ => Failure tt
        end = Success id_fld ->
        @unsafe_get_field debug_id_ty EqDec_debug_id_ty flds id_fld v = v'.
    Proof.
      intros * hget hflds hfld.
      consider @unsafe_get_field.
      consider _get_field. consider Impl.get_field. consider @get_field. consider _lookup_struct.
      consider lookup_dstruct_field. consider unsafe_lookup_field_idx. consider @lookup_field_idx.
      simplify; simpl in *.
      setoid_rewrite Heqr1. setoid_rewrite Heqr2. rewrite Heqb. rewrite PeanoNat.Nat.eqb_refl. auto.
    Qed.


End PfHelpers.

Inductive ghost_core_state_t :=
| GhostCoreState_Enclave (config: enclave_config)
| GhostCoreState_Waiting (new: enclave_config) (rf: reg_file_t)
.

Record ghost_state_t :=
{ ghost_st0: ghost_core_state_t;
  ghost_st1: ghost_core_state_t
}.

Definition get_ghost_state (st: ghost_state_t) (core: ind_core_id) : ghost_core_state_t :=
  match core with
  | CoreId0 => st.(ghost_st0)
  | CoreId1 => st.(ghost_st1)
  end.

(* Record disjoint_configs (config1 config2: enclave_config) : Prop := *)
(* { disjoint_eid: config_eid config1 <> config_eid config2 *)
(* ; disjoint_shared_regions: forall region, config_shared_regions config1 region = true /\ config_shared_regions config2 region = true -> False; *)
(*   disjoint_ext_uart: config_ext_uart config1 = true /\ config_ext_uart config2 = true -> False; *)
(*   disjoint_ext_led: config_ext_led config1 = true /\ config_ext_led config2 = true -> False; *)
(*   disjoint_ext_finish: config_ext_finish config1 = true /\ config_ext_finish config2 = true -> False; *)

(* }. *)

Definition disjoint_ghost_state st1 st2 : Prop :=
  match st1, st2 with
  | GhostCoreState_Enclave config1, GhostCoreState_Enclave config2 => disjoint_configs config1 config2
  | _, _ => True
  end.

Definition valid_ghost_state (ghost_st: ghost_state_t): Prop :=
  disjoint_ghost_state ghost_st.(ghost_st0) ghost_st.(ghost_st1).

Definition disjoint_option_configs config0 config1 : Prop :=
  match config0, config1 with
  | Some config0, Some config1 => disjoint_configs config0 config1
  | _,_ => True
  end.
  Definition eta_expand_state' (st : Environments.state_t) (types : SortedRegEnv.EnvT nat) : Environments.state_t :=
    (* TODO add a proof producing that the key are sorted *)
    SortedRegEnv.map (fun h _ => blacklist_unsafe_get_reg st h) types.
  Arguments eta_expand_state' / st types.

  Definition eta_expand_state (st : Environments.state_t) (types : SortedRegEnv.EnvT nat) : Prop :=
    let st' := eta_expand_state' st types in
    st = SortedRegEnv.from_list (SortedRegEnv.to_list st') st'.(SortedRegEnv.pf_sorted).
  Arguments eta_expand_state / st types.

Lemma WF_state_subset:
  forall reg_list reg_list' st,
  (forallb (fun '(r,t) =>
              match find (fun '(r', _) => beq_dec r r') reg_list with
              | Some (_, t') => beq_dec t t'
              | _ => false
              end) reg_list') = true ->
  WF_state reg_list st ->
  WF_state reg_list' st.
Proof.
  consider WF_state. consider @lookup_reg_type. intros.
  specialize (H0 reg). destruct_match; auto.
  rewrite forallb_forall in H.
  apply find_some in Heqo. propositional. destruct_match_pairs; subst; simplify.
  specialize (H _ Heqo0). destruct_match_pairs; simplify. bash_destruct  H; simplify.
  unfold SortedExtFnEnv.EqDec_KeyT in *. unfold OrderedN.EqDec_T in *.
  reflexivity.
Qed.


Create HintDb simplify_bits.
Hint Rewrite @firstn_fill_length : simplify_bits.

Section TODO_MOVE_BITS.
Lemma element_offset_success:
  forall id_ty {EqDec: EqDec id_ty} flds (fld: @dstruct_field_t id_ty) width,
  get_field_width flds fld = Success width ->
  match element_offset flds fld with
  | Success offset => True
  | _ => False
  end.
Proof.
  intros * Hwidth. unfold get_field_width, element_offset in *.
  simplify.
  apply find_with_index_Some_eq in Heqo. propositional. simpl_match. trivial.
Qed.
Lemma get_field_success:
  forall id_ty {EqDec: EqDec id_ty} flds (fld: @dstruct_field_t id_ty) v width,
  Datatypes.length v = struct_sz' flds ->
  get_field_width flds fld = Success width ->
  match Semantics.get_field flds fld v with
  | Success value => Datatypes.length value = width
  | Failure _ => False
  end.
Proof.
  intros * Hlength Hwidth.
  unfold Semantics.get_field. simpl_match.
  apply element_offset_success in Hwidth. simplify.
  rewrite Hlength. rewrite PeanoNat.Nat.eqb_refl. rewrite bits_slice_length. reflexivity.
Qed.
Lemma _get_field_success:
  forall struct_def fld v width,
    match _lookup_struct struct_def with
    | Success s =>
        Datatypes.length v = struct_sz' (dstruct_fields s)
    | _ => False
    end ->
    match _lookup_struct struct_def with
    | Success s =>
        get_field_width (dstruct_fields s) (unsafe_lookup_field_idx s fld) = Success width
    | _ => False
    end ->
    match _get_field struct_def fld v with
    | Success value => Datatypes.length value = width
    | Failure _ => False
    end.
Proof.
  intros * Hlen Hwidth. unfold _get_field. unfold Impl.get_field.
  consider _lookup_struct. simplify.
  apply get_field_success; propositional.
Qed.


Lemma subst_field_success:
  forall id_ty {EqDec: EqDec id_ty} flds (fld: @dstruct_field_t id_ty) vect arg,
  Datatypes.length vect = struct_sz' flds ->
  get_field_width flds fld = Success (Datatypes.length arg) ->
  match subst_field flds fld vect arg with
  | Success vect' => Datatypes.length vect' = struct_sz' flds
  | _ => False
  end.
Proof.
  unfold subst_field. intros * Hlen Hwidth.
  pose proof (element_offset_success _ _ _ _ Hwidth) as Helem_offset. simplify. simpl_match.
  rewrite Hlen. repeat rewrite PeanoNat.Nat.eqb_refl.
  rewrite Bits.slice_subst_length; auto.
  specialize element_offset_and_width_lt_struct_sz with (1 := Heqr) (2 := Hwidth).
  rewrite Hlen.
  unfold OrderedN.T in *. lia.
Qed.
End TODO_MOVE_BITS.
Hint Rewrite bits_slice_length : simplify_bits.
Hint Rewrite zeroes_length : simplify_bits.
Lemma struct_init_success:
  forall id_ty {EqDec: EqDec id_ty} struct_def (fields: list (@dstruct_field_t id_ty * list bool)),
  Forall (fun '(fld, v) =>
    match get_field_width struct_def.(dstruct_fields) fld with
    | Success width => Datatypes.length v = width
    | _ => False
    end) fields ->
  match Semantics.struct_init struct_def fields with
  | Success v => Datatypes.length v = SyntaxMacros.struct_sz struct_def
  | _ => False
  end.
Proof.
  intros *. unfold Semantics.struct_init.
  set (zeroes _) as init.
  assert (Datatypes.length init = SyntaxMacros.struct_sz struct_def) as Hlen_init by (unfold init; autorewrite with simplify_bits; auto).
  clearbody init. generalize dependent init.
  induction fields; intros * Hlen_init Hforall; simpl; autorewrite with simplify_bits; auto.
  inversions Hforall. destruct_match_pairs; subst. simplify.
  specialize IHfields with (2 := H2).
  consider @struct_sz.
  pose proof (subst_field_success _ _ _ _ _ Hlen_init Heqr). simplify. eapply IHfields. auto.
Qed.
Lemma _struct_init_success:
  forall struct_def (fields: list (string * list bool)),
    match _lookup_struct struct_def with
    | Success s =>
        Forall (fun '(fld, v) =>
                  match lookup_field_idx s fld with
                  | Success fld =>
                    match get_field_width s.(dstruct_fields) fld with
                    | Success width => Datatypes.length v = width
                    | _ => False
                    end
                  | Failure _ => False
                  end) fields
    | _ => False
    end ->
  match _struct_init struct_def fields with
  | Success v => Datatypes.length v = _unsafe_struct_sz struct_def
  | _ => False
  end.
Proof.
  intros * hcond.
  unfold _struct_init. intros. simplify.
  unfold Impl.struct_init.
  unfold _unsafe_struct_sz. unfold Impl.struct_sz.
  consider _lookup_struct.  simpl_match.
  apply struct_init_success.
  rewrite Forall_forall. rewrite Forall_forall in hcond.
  intros. consider @unsafe_field_map. rewrite in_map_iff in H.
  propositional; simplify. specialize hcond with (1 := H2). simplify.
  consider unsafe_lookup_field_idx. rewrite Heqr0. simpl. simpl_match.
  auto.
Qed.


Ltac simplify_structs_as H :=
  match goal with
  | |- context [ match _struct_init ?struct_def ?fields with
                 | _ => _
                 end ] =>
     pose proof  (_struct_init_success struct_def fields) as H; assert_pre_and_specialize H;
     [ repeat constructor; auto | ]
  | |- context[match struct_init ?struct_def ?fields with | _ => _ end] =>
      pose (struct_init_success _ struct_def fields) as H;
      assert_pre_and_specialize H; [repeat constructor; auto | ]
  | |- context[match get_field ?fields ?_fld ?req with | _ => _ end] =>
      specialize get_field_success with (flds := fields) (fld := _fld) (2 := eq_refl) (v :=req);
      intros H; propositional
  end; simplify.
Ltac unsafe_simplify_structs_as H :=
  match goal with
  | |- context [ match struct_init ?struct_def ?fields with
                 | _ => _
                 end ] =>
        pose (H := struct_init_success _ struct_def fields); assert_pre_and_specialize H;
         [ repeat constructor; auto |  ]
  | |- context [ match _get_field ?_struct_def ?_fld ?req with
                 | _ => _
                 end ] =>
        pose proof (_get_field_success _struct_def _fld req) as H; simpl in H;
        specialize H with (2 := eq_refl)
  | |- context [ match get_field ?fields ?_fld ?req with
                 | _ => _
                 end ] =>
        specialize get_field_success with (EqDec := EqDec_debug_id_ty) (flds := fields) (fld := _fld) (v := req) (2 := eq_refl); intros H; propositional
  end; simplify.

Section TODO_MOVE_specs.
  Context {CustomProps: Type}.
  Context {EqDec_CustomProps: EqDec CustomProps}.

   (* Definition reg_spec := Environments.state_t -> Environments.state_t -> @ext_sigma_t N -> vect_t -> Prop. *)
   (* Definition post_reg_spec := list (@reg_t N * reg_spec). *)
   (* Definition post_reg_spec_to_prop (spec: post_reg_spec) *)
   (*           (st: Environments.state_t) (sigma: ext_sigma_t) (st': Environments.state_t) := *)
   (*   Forall (fun '(r, prop) => prop st st' sigma (unsafe_get_reg st' r)) spec. *)

   (* Definition custom_spec := Environments.state_t -> Environments.state_t -> ext_log_t -> @ext_sigma_t N -> Prop. *)

   (* Record postcond_t := *)
   (*   { Post_taint_set: result (option taint_env_t) unit; *)
   (*     Post_ext_fn_set: result (option ext_fn_taint_env_t) unit; *)
   (*     Post_custom: list (option CustomProps * custom_spec); *)
   (*     Post_regs: post_reg_spec; *)
   (*   }. *)

   (* Definition post_custom_to_prop *)
   (*            (custom: list (option CustomProps * custom_spec)) *)
   (*            (st st': Environments.state_t) (ext_log: ext_log_t) (sigma: ext_sigma_t) :Prop := *)
   (*   Forall (fun '(_, prop) => prop st st' ext_log sigma) custom. *)

   (* Definition postcond_to_Prop (postcond: postcond_t) *)
   (*            (st st': Environments.state_t) (ext_log: ext_log_t) (sigma: ext_sigma_t): Prop := *)
   (*   taint_set_to_prop st st' (Post_taint_set postcond) /\ *)
   (*   post_custom_to_prop (Post_custom postcond) st st' ext_log sigma /\ *)
   (*   post_reg_spec_to_prop postcond.(Post_regs) st sigma st'. *)

   (* Lemma postcond_to_custom_lookup_name: *)
   (*   forall postcond st st' ext_log sigma prop name, *)
   (*     postcond_to_Prop postcond st st' ext_log sigma -> *)
   (*     find (fun '(opt, _) => *)
   (*             match opt with *)
   (*             | Some name' => beq_dec name name' *)
   (*             | None => false *)
   (*             end) (Post_custom postcond) = Some (Some name, prop) -> *)
   (*     prop st st' ext_log sigma. *)
   (* Proof. *)
   (*   intros. unfold postcond_to_Prop in *. propositional. *)
   (*   unfold post_custom_to_prop in *. *)
   (*   rewrite Forall_forall in H3. *)
   (*   apply find_some in H0; propositional. *)
   (*   specialize H3 with (1 := H2). auto. *)
   (* Qed. *)

   (*    Lemma postcond_to_Prop_lookup_reg: *)
   (*      forall postcond st st' ext_log sigma reg prop, *)
   (*        postcond_to_Prop postcond st st' ext_log sigma -> *)
   (*        find (fun '(r, _) => beq_dec reg r) (Post_regs postcond) = Some (reg, prop) -> *)
   (*        prop st st' sigma (unsafe_get_reg st' reg). *)
   (*    Proof. *)
   (*      intros. unfold postcond_to_Prop in *. propositional. *)
   (*      unfold post_reg_spec_to_prop in *. *)
   (*      rewrite Forall_forall in H4. *)
   (*      apply find_some in H0; propositional. *)
   (*      specialize H4 with (1 := H2). auto. *)
   (*    Qed. *)

   (*    Lemma postcond_to_Prop_implies_taint_set_to_Prop: *)
   (*      forall postcond st1 st2 ext_log sigma, *)
   (*        postcond_to_Prop postcond st1 st2 ext_log sigma -> *)
   (*        taint_set_to_prop st1 st2 (Post_taint_set postcond). *)
   (*    Proof. *)
   (*      intros. destruct H; propositional. *)
   (*    Qed. *)

   (*    Lemma postcond_to_Prop_implies_Post_custom: *)
   (*      forall postcond st1 st2 ext_log sigma, *)
   (*        postcond_to_Prop postcond st1 st2 ext_log sigma -> *)
   (*        post_custom_to_prop (Post_custom postcond) st1 st2 ext_log sigma. *)
   (*    Proof. *)
   (*      intros. destruct H; propositional. *)
   (*    Qed. *)

   (*    Definition post_fail_spec := @ext_sigma_t N -> Environments.state_t -> Prop. *)

   (*    Record rule_spec_t := *)
   (*      { RulePre: Environments.state_t -> @ext_sigma_t N -> Prop; *)
   (*        RulePost: postcond_t; *)
   (*        FailInversion: post_fail_spec *)
   (*      }. *)

   (*    Record schedule_spec_t : Type := *)
   (*      { SchedPre: Environments.state_t -> @ext_sigma_t N -> Prop; *)
   (*        SchedPost: postcond_t *)
   (*      }. *)
   (*   Definition oraat_rule_satisfies_spec' int_fn_env struct_env reg_type_env ext_fn_types *)
   (*      (spec: rule_spec_t) (rl: action) : Prop := *)
   (*      forall st sigma rl', *)
   (*        strong_WF_state reg_type_env st -> *)
   (*        WF_ext_sigma ext_fn_types sigma -> *)
   (*        WF_int_fn_env (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env -> *)
   (*        typecheck_rule (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env rl = Success (rl', 0) -> *)
   (*        spec.(RulePre) st sigma -> *)
   (*        match *)
   (*          oraat_interp_action sigma int_fn_env struct_env *)
   (*            (safe_fuel int_fn_env rl) st st SortedExtFnEnv.empty true *)
   (*            GenericGammaEmpty rl with *)
   (*        | (true, opt) => *)
   (*            let st':= match opt with *)
   (*                      | Some (_, st', _, _) => (st') *)
   (*                      | None => (st ) *)
   (*                      end in *)
   (*            strong_WF_state reg_type_env st' -> *)
   (*            let ext_log' := *)
   (*              match opt with *)
   (*              | Some (_, _, ext_log, _) => ext_log *)
   (*              | None => (SortedExtFnEnv.empty ) *)
   (*              end in *)
   (*            postcond_to_Prop (spec.(RulePost)) st st' ext_log'  sigma *)
   (*                                     /\ match opt with *)
   (*                                       | Some _ => True *)
   (*                                       | None => (spec.(FailInversion) sigma st) *)
   (*                                       end *)
   (*        | _ => True *)
   (*        end. *)

   (*    Definition oraat_rule_satisfies_spec int_fn_env struct_env reg_type_env ext_fn_types *)
   (*      (spec: rule_spec_t) (rl: action) : Prop := *)
   (*      forall st sigma rl', *)
   (*        strong_WF_state reg_type_env st -> *)
   (*        WF_ext_sigma ext_fn_types sigma -> *)
   (*        WF_int_fn_env (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env -> *)
   (*        typecheck_rule (SortedRegEnv.to_list  reg_type_env) ext_fn_types int_fn_env struct_env rl = Success (rl', 0) -> *)
   (*        spec.(RulePre) st sigma -> *)
   (*        match oraat_interp_rule sigma int_fn_env struct_env st rl with *)
   (*        | (true, st', ext_log) => *)
   (*            strong_WF_state reg_type_env st' -> *)
   (*            postcond_to_Prop (spec.(RulePost)) st st' ext_log sigma *)
   (*        | _ => True *)
   (*        end. *)

   (*    Lemma oraat_rule_satisfies_spec_implies: *)
   (*      forall int_fn_env struct_env reg_types ext_fn_types spec rl, *)
   (*        oraat_rule_satisfies_spec' int_fn_env struct_env reg_types ext_fn_types spec rl -> *)
   (*        oraat_rule_satisfies_spec int_fn_env struct_env reg_types ext_fn_types spec rl. *)
   (*    Proof. *)
   (*      unfold oraat_rule_satisfies_spec, oraat_rule_satisfies_spec', oraat_interp_rule. *)
   (*      unfold OrderedN.T in *. *)
   (*      intros; destruct_all_matches; propositional; *)
   (*        specialize (H st sigma rl'); destruct_all_matches; propositional. *)

   (*    Qed. *)

     (*  Definition TODO_oraat_interp_rule_safety *)
     (* : forall reg_types  (ext_fn_types : ext_fn_types_t) (sigma : ext_sigma_t) *)
     (*     (int_fn_env : int_fn_env_t) (struct_env : struct_env_t) (st st' : state_t) (action0 : action) *)
     (*     (ext_log' : ext_log_t) (rule' : AnnotatedSyntax.aaction), *)
     (*   strong_WF_state reg_types st -> *)
     (*   WF_ext_sigma ext_fn_types sigma -> *)
     (*   WF_int_fn_env (SortedRegEnv.to_list reg_types) ext_fn_types int_fn_env struct_env -> *)
     (*   typecheck_rule (SortedRegEnv.to_list reg_types) ext_fn_types int_fn_env struct_env action0 = Success (rule', 0) -> *)
     (*   oraat_interp_rule sigma int_fn_env struct_env st action0 = (true, st', ext_log') -> strong_WF_state reg_types st'. *)

      (* Definition interp_cycle'_satisfies_spec int_fn_env struct_env reg_type_env ext_fn_types *)
      (*   {rule_name_t: Type} (rules: rule_name_t -> rule) *)
      (*            (spec: schedule_spec_t) (schedule: scheduler) : Prop := *)
      (*   forall st sigma , *)
      (*   strong_WF_state reg_type_env st -> *)
      (*   WF_ext_sigma ext_fn_types sigma -> *)
      (*   WF_int_fn_env (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env -> *)
      (*   typecheck_schedule (SortedRegEnv.to_list reg_type_env) *)
      (*     ext_fn_types int_fn_env struct_env schedule rules = Success tt -> *)
      (*   spec.(SchedPre) st sigma -> *)
      (*   match interp_cycle' sigma int_fn_env struct_env st rules schedule with *)
      (*   | Success (st', ext_log) => *)
      (*       strong_WF_state reg_type_env st' -> *)
      (*       WF_ext_log ext_fn_types ext_log -> *)
      (*       postcond_to_Prop spec.(SchedPost) st st' ext_log sigma *)
      (*   | _ => True *)
      (*   end. *)

  Definition interp_scheduler_satisfies_spec
      {rule_name_t1 : Type}
      reg_type_env ext_fn_types int_fn_env struct_env
      (rules: rule_name_t1 -> rule)
      schedule
      (ghost_t: Type)
      (precond: state_t -> ext_sigma_t -> ghost_t -> Prop) postcond : Prop :=
    forall st sigma log (ghost: ghost_t),
    strong_WF_state reg_type_env st ->
    WF_ext_sigma ext_fn_types sigma ->
    WF_int_fn_env (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env ->
    interp_scheduler sigma int_fn_env struct_env st rules schedule = Success log ->
    precond st sigma ghost ->
    strong_WF_state reg_type_env (commit_update st (Log__koika log)) /\
    WF_ext_log ext_fn_types (Log__ext log) /\
    postcond st sigma (commit_update st (Log__koika log)) (Log__ext log) ghost.


  Definition sim_interp_scheduler_satisfies_spec
      {rule_name_t1 rule_name_t2: Type}
      reg_type_env ext_fn_types int_fn_env1 int_fn_env2 struct_env1 struct_env2
      (impl_rules: rule_name_t1 -> rule)
      (spec_rules: rule_name_t2 -> rule)
      impl_schedule spec_schedule
      (ghost_t: Type)
      precond postcond : Prop :=
    forall impl_st spec_st impl_sigma spec_sigma impl_log spec_log (ghost: ghost_t),
    strong_WF_state reg_type_env impl_st ->
    strong_WF_state reg_type_env spec_st ->
    WF_ext_sigma ext_fn_types impl_sigma ->
    WF_ext_sigma ext_fn_types spec_sigma ->
    WF_int_fn_env (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env1 struct_env1 ->
    WF_int_fn_env (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env2 struct_env2 ->
    interp_scheduler impl_sigma int_fn_env1 struct_env1 impl_st impl_rules impl_schedule = Success impl_log ->
    interp_scheduler spec_sigma int_fn_env2 struct_env2 spec_st spec_rules spec_schedule = Success spec_log ->
    precond impl_st impl_sigma (commit_update impl_st (Log__koika impl_log)) (Log__ext impl_log)
             spec_st spec_sigma (commit_update spec_st (Log__koika spec_log)) (Log__ext spec_log)
             ghost ->
    strong_WF_state reg_type_env (commit_update impl_st (Log__koika impl_log)) /\
    strong_WF_state reg_type_env (commit_update spec_st (Log__koika spec_log)) /\
    WF_ext_log ext_fn_types (Log__ext impl_log) /\
    WF_ext_log ext_fn_types (Log__ext spec_log) /\
    postcond impl_st impl_sigma (commit_update impl_st (Log__koika impl_log)) (Log__ext impl_log)
             spec_st spec_sigma (commit_update spec_st (Log__koika spec_log)) (Log__ext spec_log)
             ghost.

    End TODO_MOVE_specs.
      (* Ltac rewrite_with_custom name postcond := *)
      (*   let foo := constr:(postcond_to_custom_lookup_name _ _ _ _ _ _ name postcond eq_refl) in *)
      (*   rewrite foo. *)
      (* Ltac rewrite_with_custom_in H name postcond := *)
      (*   let foo := constr:(postcond_to_custom_lookup_name _ _ _ _ _ _ name postcond eq_refl) in *)
      (*   rewrite foo in H. *)
      (* Ltac pose_custom_as H name postcond := *)
      (*   specialize (postcond_to_custom_lookup_name _ _ _ _ _ _ name postcond eq_refl) as H. *)
      (* Ltac apply_custom name postcond := *)
      (*   let foo := constr:((postcond_to_custom_lookup_name _ _ _ _ _ _ name postcond eq_refl)) in *)
      (*   apply foo. *)

      (* Ltac rewrite_with_reg_spec reg postcond := *)
      (*   rewrite (postcond_to_Prop_lookup_reg _ _ _ _ _ reg _ postcond eq_refl). *)
      (* Ltac rewrite_with_reg_spec_in H reg postcond := *)
      (*   rewrite (postcond_to_Prop_lookup_reg _ _ _ _ _ reg _ postcond eq_refl) in H. *)

      (* Ltac rewrite_no_write reg postcond := *)
      (*   rewrite (taint_set_to_prop_no_write' _ _ _ reg *)
      (*              (postcond_to_Prop_implies_taint_set_to_Prop _ _ _ _ _ postcond) eq_refl). *)

      (* Ltac rewrite_no_write_in H reg postcond := *)
      (*   rewrite (taint_set_to_prop_no_write' _ _ _ reg *)
      (*              (postcond_to_Prop_implies_taint_set_to_Prop _ _ _ _ _ postcond) eq_refl) in H. *)

      (* Definition dummy_int_fn_spec : int_fn_spec_t := mk_int_fn_spec [] [] [] 0%N 0 0 {{ pass }}. *)
   (*    Definition replace_fn_reg_tys (int_fns int_fns': @int_fn_env_t N (@action N)) : @int_fn_env_t N (@action N):= *)
   (*      map *)
   (*        (fun '(fn, fn') => *)
   (*           {| *)
   (*             fn_name := fid fn; *)
   (*             fn_reg_tys := fn_reg_tys fn'; *)
   (*             fn_ext_fn_tys := fn_ext_fn_tys fn; *)
   (*             fn_struct_defs := fn_struct_defs fn; *)
   (*             fn_arg_ty := fn_arg_ty fn; *)
   (*             fn_arg_name := fn_arg_name fn; *)
   (*             fn_ret_ty := fn_ret_ty fn; *)
   (*             fn_body := fn_body fn *)
   (*           |}) (combine int_fns int_fns'). *)

   (*    Lemma rewrite_int_fns_reg_tys : *)
   (*        forall int_fns int_fns', *)
   (*     map fn_reg_tys int_fns = map fn_reg_tys int_fns' -> *)
   (*     int_fns = replace_fn_reg_tys int_fns int_fns'. *)
   (* Proof. *)
   (*   unfold replace_fn_reg_tys. *)
   (*   induction int_fns. *)
   (*   + intros; vm_compute; eauto. *)
   (*   + intros. *)
   (*     destruct int_fns'; [discriminate|..]. *)
   (*     inversions H. *)
   (*     simpl. *)
   (*     rewrite <- H1. *)
   (*     f_equal. *)
   (*     - destruct a; eauto. *)
   (*     - eauto. *)
   (*  Qed. *)

(*     Lemma sorted_env_shift_equiv: *)
(*       forall {T: Type} (env1 env2: SortedRegEnv.EnvT T) n, *)
(*       SortedRegEnv.to_list env1 = map (fun '(k,v) => ((k + n)%N, v)) (SortedRegEnv.to_list env2) -> *)
(*       forall x, SortedRegEnv.opt_get env1 ((x + n)%N) = SortedRegEnv.opt_get env2 x. *)
(*     Proof. *)
(*       unfold SortedRegEnv.to_list. destruct env1. destruct env2. simpl in *. *)
(*       unfold SortedRegEnv.opt_get. intros; subst; simpl. *)
(*       clear. induction Env0; auto. *)
(*       simpl. destruct_match_pairs; simplify. destruct_match; simplify. *)
(*       - repeat destruct_match; simplify; lia. *)
(*       - repeat destruct_match; simplify; auto. *)
(*     Qed. *)
(* Lemma get_restrict_env_some: *)
(*   forall st reg shift shift_max, *)
(*   (reg + shift < shift_max)%N -> *)
(*   get_reg (restrict_env shift shift_max st) reg = get_reg st (reg + shift)%N . *)
(* Proof. *)
(*   unfold get_reg, restrict_env. *)
(*   intros. *)
(*   rewrite SortedRegEnv.restrict_equiv by lia. reflexivity. *)
(* Qed. *)

Lemma strong_WF_state_commit_update:
  forall reg_type_env st log,
  strong_WF_state reg_type_env st ->
  WF_log (SortedRegEnv.to_list reg_type_env) log ->
  strong_WF_state reg_type_env (commit_update st log).
Proof.
  intros * hwf_st hwf_log.
  consider strong_WF_state. propositional. split_ands_in_goal.
  - consider KeysEq. consider commit_update. rewrite<-hwf_st0.
    unfold SortedRegEnv.keys. unfold SortedRegEnv.map. consider @SortedRegEnv.to_list. simpl. rewrite map_map.
    f_equal.
Require Import FunctionalExtensionality.
    apply functional_extensionality.
    intros. destruct_match; auto.
  - apply WF_commit_update; auto.
Qed.

Lemma typecheck_schedule_correct':
forall (rule_name_t : Type) reg_type_env (ext_fn_types : ext_fn_types_t)
  (int_fn_env : int_fn_env_t) (struct_env : struct_env_t) (ext_sigma : ext_sigma_t) (s : scheduler)
  (rls : rule_name_t -> action) (st : Environments.state_t) (sched_log : Log_t),
  typecheck_schedule (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env s rls = Success tt ->
  strong_WF_state reg_type_env st ->
  WF_log (SortedRegEnv.to_list reg_type_env) (Log__koika sched_log) ->
  WF_ext_log ext_fn_types (Log__ext sched_log) ->
  WF_ext_sigma ext_fn_types ext_sigma ->
  WF_int_fn_env (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env ->
  match interp_scheduler' ext_sigma int_fn_env struct_env st rls s sched_log with
  | Success log => strong_WF_state reg_type_env (commit_update st (Log__koika log)) /\ WF_ext_log ext_fn_types (Log__ext log)
  | Failure _ => False
  end.
Proof.
  intros * htype hwf hwf_log hwf_ext_log hwf_ext_sigma hwf_int_fn_env.
  specialize @typecheck_schedule_correct'_log with
    (1 := htype) (3 := hwf_ext_log) (4 := hwf_log) (5 := hwf_ext_sigma) (6 := hwf_int_fn_env) (st := st)
    (2 := strong_WF_state_weaken _ _ hwf).
  consider WF_int_fn_env. propositional. simplify.
  split_ands_in_goal; propositional.
  apply strong_WF_state_commit_update; auto.
Qed.

Lemma typecheck_scheduler_correct'':
forall (rule_name_t : Type) reg_type_env (ext_fn_types : ext_fn_types_t)
  (int_fn_env : int_fn_env_t) (struct_env : struct_env_t) (ext_sigma : ext_sigma_t) (s : scheduler)
  (rls : rule_name_t -> action) (st : Environments.state_t) log,
  typecheck_schedule (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env s rls = Success tt ->
  strong_WF_state reg_type_env st ->
  WF_ext_sigma ext_fn_types ext_sigma ->
  WF_int_fn_env (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env ->
  interp_scheduler ext_sigma int_fn_env struct_env st rls s = Success log ->
  strong_WF_state reg_type_env (commit_update st (Log__koika log)) /\ WF_ext_log ext_fn_types (Log__ext log).
Proof.
  intros * htype hwf hwf_ext_sigma hwf_int_fn_env hinterp.
  specialize typecheck_schedule_correct' with
    (1 := htype) (2 := hwf) (5 := hwf_ext_sigma) (6 := hwf_int_fn_env)
    (sched_log := Log_empty). consider interp_scheduler. simpl_match.
  intros hcorrect. apply hcorrect.
  - apply WF_log_GenericLogEmpty.
  - apply WF_ext_log__empty.
Qed.


Lemma typecheck_cycle_correct'
  : forall reg_type_env (ext_fn_types : ext_fn_types_t) (int_fn_env : int_fn_env_t)
      (struct_env : struct_env_t) (ext_sigma : ext_sigma_t) {rule_name_t: Type} (s : @scheduler rule_name_t)
      (rls : rule_name_t -> action)
      (st0 : Environments.state_t),
  typecheck_schedule (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env s rls = Success tt ->
  strong_WF_state reg_type_env st0 ->
  WF_ext_sigma ext_fn_types ext_sigma ->
  WF_int_fn_env (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env ->
  match interp_cycle' ext_sigma int_fn_env struct_env st0 rls s with
  | Success (st', ext_log) =>
      strong_WF_state reg_type_env st' /\ WF_ext_log ext_fn_types ext_log
  | Failure _ => False
  end.
Proof.
  intros * Htype Hst Hsigma Hint_fn. consider interp_cycle'. unfold interp_scheduler.
  pose proof @typecheck_schedule_correct' as Hsched.
  specialize Hsched with (1 := Htype) (2 := Hst) (5 := Hsigma) (sched_log := Log_empty) (6 := Hint_fn).
  simpl in *.
  specialize Hsched with (1 := WF_log_GenericLogEmpty _ ) (2 := WF_ext_log__empty _).
  simplify. auto.
Qed.
Definition ext_fn_none (ext: ext_log_t) fn : bool :=
  match SortedExtFnEnv.opt_get ext fn with
  | None => true
  | Some None => false
  | _ => false
  end.
Definition other_core core :=
      match core with
      | CoreId0 => CoreId1
      | CoreId1 => CoreId0
      end.



    (* Definition unsafe_enclave_data_to_config (data: vect_t) : enclave_config := *)
    (*   let enc_req := (unsafe_get_field (dstruct_fields enclave_data) FLD_enclave_data__data data) in *)
    (*   let eid := unsafe_get_field (dstruct_fields enclave_req) FLD_enclave_req__eid enc_req in *)
    (*   let shared_regions := unsafe_get_field (dstruct_fields enclave_req) FLD_enclave_req__shared_regions enc_req in *)
    (*   let ext_uart := unsafe_get_field (dstruct_fields enclave_req) FLD_enclave_req__ext_uart enc_req in *)
    (*   let ext_led := unsafe_get_field (dstruct_fields enclave_req) FLD_enclave_req__ext_led enc_req in *)
    (*   {| config_eid := unsafe_enclave_id_vect_to_eid eid; *)
    (*      config_shared_regions := fun id => unsafe_shared_regions_vect_to_bool shared_regions id; *)
    (*      config_ext_uart := beq_dec ext_uart [true]; *)
    (*      config_ext_led := beq_dec ext_led [true]; *)
     (* |}. *)



    Lemma unsafe_get_reg_success_or_default:
      forall st reg ,
        success_or_default (r_get_reg st reg) Ob = unsafe_get_reg st reg.
    Proof.
      intros. unfold success_or_default, unsafe_get_reg, r_get_reg. destruct_match; auto.
    Qed.
    Lemma unsafe_get_field_success_or_default:
      forall flds fld v,
        success_or_default (Semantics.get_field flds fld v) Ob = unsafe_get_field flds fld v.
    Proof.
      reflexivity.
    Qed.
    Lemma list_beq_equiv_bits_eq:
      forall x1 x2,
        list_beq bool Bool.eqb x1 x2 = bits_eq x1 x2.
    Proof.
      reflexivity.
    Qed.
    Lemma bool_eqb_true:
      forall b,
        Bool.eqb b true = b.
    Proof.
      destruct b; auto.
    Qed.

Ltac step_oraat_simpl_term_in_goal x :=
  match x with
  | _ && true =>
    rewrite andb_true_r
  | Bool.eqb _ true =>
    rewrite bool_eqb_true
  | list_beq bool Bool.eqb ?x1 ?x2 =>
    rewrite (@list_beq_equiv_bits_eq x1 x2)
  | context[(success_or_default (Semantics.get_field  ?flds ?fld ?v) _)] =>
    rewrite (@unsafe_get_field_success_or_default flds fld v)
  | context[success_or_default (r_get_reg ?st ?reg)] =>
    rewrite (@unsafe_get_reg_success_or_default st reg)
  | PeanoNat.Nat.eqb _ _ = true =>
    rewrite PeanoNat.Nat.eqb_eq
  end.

Ltac step_oraat_simpl :=
  repeat match goal with
         | |- if ?x then _ else _ =>
           step_oraat_simpl_term_in_goal x
         | |- ?x -> _ =>
           step_oraat_simpl_term_in_goal x
         end.
Lemma pair_eq2:
  forall {A B} (a1 a2: A) (b1 b2: B),
  (a1,b1) = (a2,b2) -> b1 = b2.
Proof.
  intros. apply simple_tuple_inversion in H. propositional.
Qed.
Lemma pair_eq1:
  forall {A B} (a1 a2: A) (b1 b2: B),
  (a1,b1) = (a2,b2) -> a1 = a2.
Proof.
  intros. apply simple_tuple_inversion in H. propositional.
Qed.
Ltac solve_safe :=
  match goal with
  | |- false = true -> _ => discriminate
  | |- forall _, false = true -> _ =>
    clear; intros; discriminate
  | |- forall _, (false, _) = (true, _) -> _ =>
    clear; intros; discriminate
  | |- forall _, (false, _) = (?b, ?opt) -> _ =>
    let H := fresh "H" in
    solve[clear; intros * ? H; simplify_tupless; bash_destruct H]
  end.

Ltac step_wp_oraat_lib__safe :=
  match goal with
  | |- oraat_wp_action _ _ _ _ _ (invalid _ ) _ _ _ _ _ =>
    apply oraat_wp_binop__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (valid _ _ ) _ _ _ _ _ =>
    apply oraat_wp_binop__safe;[ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (action_struct_init _ _ ) _ _ _ _ _ =>
    apply oraat_wp_binop__safe;[ solve_safe | ]
  end.

(* Ltac step_wp_oraat_safe := *)
(*   lazymatch goal with *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Fail _) _) _ _ _ _ _ => *)
(*    apply oraat_wp_fail__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Var _) _) _ _ _ _ _ => *)
(*    apply oraat_wp_var__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Const _) _) _ _ _ _ _ => *)
(*    apply oraat_wp_const__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Bind _ _) _ _) _ _ _ _ _ => *)
(*    apply oraat_wp_bind__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Seq _ _ ) _) _ _ _ _ => *)
(*    apply oraat_wp_seq__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (If _ _) _ _) _ _ _ _ _ => *)
(*     apply oraat_wp_if__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Assign _ _) _) _ _ _ _ _ => *)
(*     apply oraat_wp_assign__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Zop _ _) ) _ _ _ _ _ => *)
(*     apply oraat_wp_zop__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Unop _ _) _ ) _ _ _ _ _ => *)
(*     apply oraat_wp_unop__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Binop _ _) _ _ ) _ _ _ _ _ => *)
(*     apply oraat_wp_binop__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Read P0 _) _) _ _ _ _ _ => *)
(*     apply oraat_wp_read0__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Read P1 _) _) _ _ _ _ _ => *)
(*     apply oraat_wp_read1__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (Write _ _) _ _) _ _ _ _ _ => *)
(*     apply oraat_wp_write__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (ExternalCall _ _) _) _ _ _ _ _ => *)
(*     apply oraat_wp_external_call__safe; [ solve_safe | ] *)
(*   | |- oraat_wp_action _ _ _ _ _ (Action (InternalCall _ _) _) _ _ _ _ _ => *)
(*     fail *)
(*   | |- oraat_wp_action _ _ _ _ _ _ _ _ _ _ _ => *)
(*     step_wp_oraat_lib__safe *)
(*   | |- true = true -> _ => *)
(*     let H := fresh in intro H; clear H *)
(*   | |- (true, _) = (true, _) -> _ => *)
(*     let H := fresh in intro H; apply pair_eq2 in H *)
(*   | |- _ = true -> _ => *)
(*     repeat step_oraat_simpl; let H := fresh "Hsafe" in intro H *)
(*   | |- _ => progress (step_oraat_simpl) *)
(*   end. *)


(* END TODO_MOVE*)

Definition cid_to_bits (id: ind_core_id) : vect_t :=
  match id with
  | CoreId0 => Ob~0
  | CoreId1 => Ob~1
  end.
Ltac custom_simplify_updates_in_term V :=
  fail.

Ltac simplify_updates_in_term V :=
  match V with
  | ?V1 \/ ?V2 =>
    simplify_updates_in_term V1 || simplify_updates_in_term V2
  | ?V1 /\ ?V2 =>
    simplify_updates_in_term V1 || simplify_updates_in_term V2
  | ?V1 = ?V2 =>
    simplify_updates_in_term V1 || simplify_updates_in_term V2
  | ?V1 <> ?V2 =>
    simplify_updates_in_term V1 || simplify_updates_in_term V2
  | ?V1 && ?V2 =>
    match V2 with
    | false => rewrite andb_false_r
    | _ => simplify_updates_in_term V1 || simplify_updates_in_term V2
    end
  | ?V1 || ?V2 =>
    simplify_updates_in_term V1 || simplify_updates_in_term V2
  | if ?V1 then _ else _ =>
    simplify_updates_in_term V1
  | unsafe_get_field ?flds ?fld (success_or_default (subst_field ?flds ?fld' _ _) _) =>
    lazymatch fld with
    | fld' => rewrite unsafe_get_subst_field_eq by (assumption;auto)
    | _ => rewrite unsafe_get_subst_field_neq by (assumption || discriminate)
    end
  | unsafe_get_field ?flds ?fld (slice_subst ?fld' _ _) =>
    lazymatch fld with
    | _  => rewrite unsafe_get_field_slice_subst_eq by auto
    end
  | unsafe_get_field _ _ ?V1 =>
    simplify_updates_in_term V1
  | unsafe_get_reg (state_set _ ?r1 _) ?r2 =>
    lazymatch r1 with
    | r2 => rewrite unsafe_get_reg_state_set_eq with (idx:= r1)
    | _ => rewrite unsafe_get_reg_state_set_neq with (idx1:= r1) (idx2:= r2) by discriminate
    end
  | success_or_default (r_get_reg ?st ?reg) _ =>
    rewrite (@unsafe_get_reg_success_or_default st reg)
  (* | bits_eq ?x ?x => *)
  (*    rewrite (bits_eq_refl x) *)
  | bits_eq ?x1 ?x2 =>
    simplify_updates_in_term x1 || simplify_updates_in_term x2
  | _ => custom_simplify_updates_in_term V
  end.
Ltac simplify_updates  :=
  repeat match goal with
         | |- ?V1 -> ?V2 => simplify_updates_in_term V1 || simplify_updates_in_term V2
         | |- ?V => simplify_updates_in_term V
         | |- _ => progress simpl_match
         | |- _ => reflexivity
         end.

  (* Lemma oraat_interp_scheduler'_cons__spec: *)
  (*   forall {rule_name_t CustomProps: Type} *)
  (*   sigma int_fn_env struct_env reg_type_env ext_fn_types *)
  (*   (st st'': state_t) (rules: rule_name_t -> action) rl s *)
  (*   (rl_spec: rule_spec_t) action' ext_log ext_log'' , *)
  (*   strong_WF_state reg_type_env st -> *)
  (*   WF_ext_sigma ext_fn_types sigma -> *)
  (*   WF_int_fn_env (SortedRegEnv.to_list reg_type_env) ext_fn_types int_fn_env struct_env -> *)
  (*   typecheck_rule (SortedRegEnv.to_list reg_type_env) *)
  (*                  ext_fn_types int_fn_env struct_env (rules rl) = Success (action',0) -> *)
  (*   oraat_rule_satisfies_spec' int_fn_env struct_env reg_type_env ext_fn_types rl_spec (rules rl) -> *)
  (*   rl_spec.(RulePre) st sigma -> *)
  (*   oraat_interp_scheduler' sigma int_fn_env struct_env rules st ext_log true (Cons rl s) = (true, st'', ext_log'') -> *)
  (*   exists ext_log' st', @postcond_to_Prop CustomProps rl_spec.(RulePost) st st' ext_log' sigma /\ *)
  (*     oraat_interp_scheduler' sigma int_fn_env struct_env rules st' (ext_log_app ext_log' ext_log) true s = *)
  (*       (true, st'', ext_log'') /\ *)
  (*     strong_WF_state reg_type_env st'. *)
  (* Proof. *)
  (*   intros * Hst Hext_sigma Hint_fn_env Htype Hspec Hpre Horaat.  simpl in Horaat. simplify. *)
  (*   apply oraat_rule_satisfies_spec_implies in Hspec. *)
  (*   consider @oraat_rule_satisfies_spec. *)
  (*   specialize Hspec with (1 := Hst) (2 := Hext_sigma) (3 := Hint_fn_env) (4 := Htype) (5 := Hpre). *)
  (*   destruct_match_pairs. *)
  (*   specialize @oraat_interp_scheduler'_is_safe_generalizes with (1 := Horaat); propositional. *)
  (*   simplify. *)
  (*   assert (strong_WF_state reg_type_env s0) as Hwf_st'. *)
  (*   { eapply TODO_oraat_interp_rule_safety; eauto. } *)
  (*   propositional. eauto. *)
  (* Qed. *)

(* Ltac autorewrite_no_write reg := *)
(*   match goal with *)
(*   | H: postcond_to_Prop _ _ ?st' _ _ *)
(*     |- context[ ?st'.[_id reg] ] => *)
(*       rewrite_no_write (_id reg) H *)
(*   end. *)
Lemma forall_regs_no_writes:
  forall (reg: debug_id_ty) taint_set reg_list,
  In reg reg_list ->
  forallb (fun reg => no_writes_in_taint_set taint_set (_id reg)) reg_list = true ->
  no_writes_in_taint_set taint_set (_id reg) = true.
Proof.
  intros. rewrite forallb_forall in H0.
  eauto.
Qed.
Lemma forall_regs_no_writes_exclude:
  forall reg taint_set reg_list,
  (forall reg, (In reg reg_list -> False) -> SortedRegEnv.opt_get taint_set reg = None) ->
  (In reg reg_list -> False)  ->
  no_writes_in_taint_set (Success (Some taint_set)) (reg) = true.
Proof.
  intros. consider no_writes_in_taint_set.
  rewrite H; auto.
Qed.
Lemma WF_state_length':
  forall (reg_types : reg_types_t) (idx : Syntax.reg_t) (st : Environments.state_t)  (n : nat),
  WF_state reg_types st ->
  Typechecking.lookup_reg_type reg_types idx tt = Success n ->
  Datatypes.length st.[idx] = n.
Proof.
  unfold WF_state, lookup_reg_type, r_get_reg, get_reg.
  intros. specialize (H idx). simplify.
  consider @Typechecking.lookup_reg_type. consider @lookup_reg_type. simplify.
  unfold unsafe_get_reg, r_get_reg.  simpl_match. auto.
Qed.
Notation "st1 .[[ idx1 ]] == st2 .[[ idx2 ]]" :=
  (match SortedRegEnv.opt_get st1 idx1, SortedRegEnv.opt_get st2 idx2 with
   | Some v1, Some v2 => v1 = v2
   | _, _ => False
   end) (at level 1, format "st1 .[[ idx1 ]] == st2 .[[ idx2 ]]").
Notation "st .[[ idx ]] = v " := (SortedRegEnv.opt_get st idx = Some v) (at level 1, format "st .[[ idx ]] = v").
Notation machine_t := (Symbolic.machine_t).

Lemma unsafe_get_field_eq:
  forall (flds: list (dstruct_field_t * nat)) fld v v' v'',
  @unsafe_get_field debug_id_ty EqDec_debug_id_ty flds fld v = v' ->
  get_field flds fld v = Success v'' ->
  v' = v''.
Proof.
  unfold unsafe_get_field, success_or_default; propositional; simpl_match; auto.
Qed.
Lemma unsafe_get_field_eq':
  forall (flds : list (@dstruct_field_t debug_id_ty * nat)) (fld : dstruct_field_t) (v v'' : list bool),
  get_field flds fld v = Success v''  ->
  unsafe_get_field flds fld v = v''.
Proof.
  intros. specialize unsafe_get_field_eq with (2 := H). auto.
Qed.
(* Lemma of_nat_to_nat: *)
(*   forall len v bs, *)
(*   of_nat len v = bs -> *)
(*   Nat.modulo v (pow2 len) = (to_nat bs) . *)
(* Proof. *)
Lemma case_doubleton_bits :
  forall bv,
  Datatypes.length bv = 2 ->
  bv = Ob~0~0 \/ bv = Ob~0~1 \/ bv = Ob~1~0 \/ bv = Ob~1~1.
Proof.
  destruct bv; try discriminate.
  destruct bv; try discriminate.
  destruct bv; try discriminate.
  destruct b; destruct b0; eauto.
Qed.


(* TODO: MOVE *)
