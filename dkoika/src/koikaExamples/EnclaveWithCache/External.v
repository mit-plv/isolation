Require Import rv_cache_isolation.Common.
Require Import koika.Frontend.
Require Import koikaExamples.EnclaveWithCache.Common.

Module EnclaveParams <:  EnclaveParams_sig.

  Definition enclave_base (eid: enclave_id) : addr_t :=
    match eid with
    | Enclave0 => Ob~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave1 => Ob~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave2 => Ob~0~0~0~0~0~0~0~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave3 => Ob~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    end.

 Definition enclave_size (eid: enclave_id) : vect_t :=
                  Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0.
 Definition enclave_bootloader_addr (eid: enclave_id) : addr_t :=
    match eid with
    | Enclave0 => Ob~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0
    | Enclave1 => Ob~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0
    | Enclave2 => Ob~0~0~0~0~0~0~0~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave3 => Ob~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    end.

  Definition shared_region_base (id: shared_id) : addr_t :=
    match id with
    | Shared01 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared02 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared03 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared12 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared13 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared23 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~1~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    end.

  Definition shared_region_size : vect_t := Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.

  Definition initial_enclave_config0 : enclave_config :=
    {| config_eid := Enclave0;
       config_shared_regions := fun _ => false;
       config_ext_uart := false;
       config_ext_led := false;
       config_ext_finish := false;
    |}.
  Definition initial_enclave_config1 : enclave_config :=
    {| config_eid := Enclave1;
       config_shared_regions := fun _ => false;
       config_ext_uart := false;
       config_ext_led := false;
       config_ext_finish := false;
    |}.

  Definition core_init0 : core_init_params_t :=
    {| machine_pc := Ob~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
       machine_rf := fun _ => Some (zeroes 32);
       machine_config := Some initial_enclave_config0
    |}.

  Definition core_init1 : core_init_params_t :=
    {| machine_pc := Ob~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
       machine_rf := fun _ => Some (zeroes 32);
       machine_config := Some initial_enclave_config1
    |}.

  Definition enclave_sig: enclave_params_sig :=
  {| _enclave_base := enclave_base;
     _enclave_size := enclave_size;
     _enclave_bootloader_addr := enclave_bootloader_addr;
     _shared_region_base :=shared_region_base;
     _shared_region_size := shared_region_size;
     _core_init0 := core_init0;
     _core_init1 :=  core_init1;
  |}.
    Ltac simplify_bool_prop :=
      repeat match goal with
      | H: _ && _ = true |- _ => rewrite andb_true_iff in H
      end; propositional.

  Lemma pf_disjoint_configs : wf_disjoint_configs enclave_sig.
  Proof.
    consider wf_disjoint_configs.
    intros * haddr1 haddr2.
    consider addr_in_region.
    destruct region1; [ | | discriminate];
    destruct region2; try discriminate; repeat rewrite andb_true_iff in *;
      repeat rewrite PeanoNat.Nat.leb_le in *;
      repeat rewrite PeanoNat.Nat.ltb_lt in *;
      consider enclave_sig; consider enclave_base_N;
      consider enclave_max_N; simpl in *.
    - destruct eid; destruct eid0; simpl in *; auto;
        propositional; rewrite N.leb_le in *; rewrite N.ltb_lt in *; lia.
    - consider shared_base_N. consider shared_max_N.
      destruct eid; destruct id; simpl in *; auto;
        propositional; rewrite N.leb_le in *; rewrite N.ltb_lt in *; lia.
    - consider shared_base_N. consider shared_max_N.
      destruct eid; destruct id; simpl in *; auto;
        propositional; rewrite N.leb_le in *; rewrite N.ltb_lt in *; lia.
    - consider shared_base_N. consider shared_max_N.
      destruct id0; destruct id; simpl in *; auto;
        propositional; rewrite N.leb_le in *; rewrite N.ltb_lt in *; lia.
  Qed.

  Lemma _wf_bootloader_addr: forall eid,
    Datatypes.length (enclave_sig.(_enclave_bootloader_addr) eid) = 32.
  Proof.
    destruct eid; reflexivity.
  Qed.

  Lemma _wf_enclave_base:
    forall eid, Datatypes.length (_enclave_base enclave_sig eid) = 32.
  Proof.
    destruct eid; reflexivity.
  Qed.
  Lemma _wf_shared_base: forall sid, Datatypes.length (_shared_region_base enclave_sig sid) = 32.
  Proof.
    destruct sid; reflexivity.
  Qed.

  Lemma _wf_core_init0:  Datatypes.length enclave_sig.(_core_init0).(machine_pc) = 32.
  Proof.
    reflexivity.
  Qed.
  Lemma _wf_core_init1: Datatypes.length enclave_sig.(_core_init1).(machine_pc) = 32.
  Proof.
    reflexivity.
  Qed.
  Lemma _wf_enclave_size : forall eid, Datatypes.length (_enclave_size enclave_sig eid) = 32.
  Proof.
    destruct eid; reflexivity.
  Qed.


  Lemma _wf_shared_size : Datatypes.length (_shared_region_size enclave_sig) = 32.
  Proof.
    reflexivity.
  Qed.

  Lemma _wf_config0 : is_some (machine_config (_core_init0 enclave_sig)).
  Proof.
    unfold is_some. eexists; simpl; eauto.
  Qed.

  Lemma _wf_config1 : is_some (machine_config (_core_init1 enclave_sig)).
  Proof.
    unfold is_some. eexists; simpl; eauto.
  Qed.

  Lemma _wf_init_configs: wf_opt_disjoint_configs (machine_config (_core_init0 enclave_sig))
                           (machine_config (_core_init1 enclave_sig)).
  Proof.
    consider wf_opt_disjoint_configs. simpl.
    constructor; propositional; try discriminate.
  Qed.
  Lemma _wf_rf0 : enclave_sig.(_core_init0).(machine_rf) = fun _ => Some (Bits.zeroes 32).
  Proof. reflexivity. Qed.
  Lemma _wf_rf1 : enclave_sig.(_core_init1).(machine_rf) = fun _ => Some (Bits.zeroes 32).
  Proof. reflexivity. Qed.

   Definition wf_sig : wf_enclave_params enclave_sig :=
     {| wf_bootloader_addr := _wf_bootloader_addr;
        wf_enclave_base := _wf_enclave_base;
        wf_enclave_size := _wf_enclave_size;
        wf_shared_base := _wf_shared_base;
        wf_shared_size := _wf_shared_size;
        wf_core_init0 := _wf_core_init0;
        wf_core_init1 := _wf_core_init1;
        wf_config0 := _wf_config0;
        wf_config1 := _wf_config1;
        wf_init_configs := _wf_init_configs;
        wf_rf0 := _wf_rf0;
        wf_rf1 := _wf_rf1;
     |}.

End EnclaveParams.
