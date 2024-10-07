Require Import Koika.Frontend.

Require Import Koika.examples.ResourceIsolation_Util.
Require Import Koika.examples.ResourceIsolation_Impl.
Require Import Koika.examples.ResourceIsolation_Spec.
Require Import Koika.examples.ResourceIsolation_Theorem.
Require Import Koika.examples.ResourceIsolation_ProofImpl.
Require Import Koika.examples.ResourceIsolation_ProofSpec.



(* - spec says once a job continues, it's no longer affected by external inputs *)

Import Common.

Section TODO_MOVE_Infrastructure.
  Context {SimCustomProps: Type}.
Lemma Forall_single:
  forall {A} (f: A -> Prop) (a: A),
    Forall f [a] <-> f a.
Proof.
  intros; split; intros; auto.
  apply Forall_inv in H. assumption.
Qed.

  Definition sim_reg_spec : Type :=
    state_t -> ext_sigma_t -> state_t -> state_t -> ext_sigma_t -> state_t -> vect_t -> vect_t -> Prop.

  Definition sim_custom_spec : Type :=
    state_t -> ext_sigma_t -> state_t -> state_t -> ext_sigma_t -> state_t -> Prop.

  Record sim_postcond_t :=
  { SimPost_custom: list (SimCustomProps * sim_custom_spec);
    SimPost_regs : list ((reg_t * reg_t) * sim_reg_spec)
  }.

  Definition sim_reg_prespec : Type := state_t -> state_t -> vect_t -> vect_t -> Prop.
  Definition sim_custom_prespec : Type := state_t -> ext_sigma_t -> state_t -> ext_sigma_t -> Prop.

  Record sim_precond_t :=
    { SimPre_regs: list ((reg_t * reg_t) * sim_reg_prespec);
      SimPre_custom: list (SimCustomProps * sim_custom_prespec)
    }.

  Record sim_spec_t :=
   { SimPre: sim_precond_t
   ; SimPost: sim_postcond_t
   }.

  (* Assume syntactically equivalent rules *)
  Record sim_rule_spec_t :=
    { rule_spec: rule_spec_t
    ; sim_spec: sim_spec_t
    }.

  Record SimPrecondProp (sim: sim_rule_spec_t)
    (impl_st spec_st: state_t) (impl_sigma spec_sigma: ext_sigma_t) : Prop :=
    { SimPre_impl: sim.(rule_spec).(Pre) impl_st impl_sigma;
      SimPre_spec: sim.(rule_spec).(Pre) spec_st spec_sigma;
      SimPre_customSim: Forall (fun '(_, p) => p impl_st impl_sigma spec_st spec_sigma)
                          sim.(sim_spec).(SimPre).(SimPre_custom);
      SimPre_regSim: Forall (fun '((r1,r2), p) => p impl_st spec_st impl_st.[r1] spec_st.[r2])
                          sim.(sim_spec).(SimPre).(SimPre_regs)
    }.

  Record SimPostcondProp (sim: sim_rule_spec_t)
    (impl_st impl_st' spec_st spec_st': state_t) (impl_sigma spec_sigma: ext_sigma_t) : Prop :=
    { SimPost_impl: postcond_to_Prop sim.(rule_spec).(Post) impl_st impl_st' impl_sigma;
      SimPost_spec: postcond_to_Prop sim.(rule_spec).(Post) spec_st spec_st' spec_sigma;
      SimPost_customSim: Forall (fun '(_, p) => p impl_st impl_sigma impl_st' spec_st spec_sigma spec_st')
                                sim.(sim_spec).(SimPost).(SimPost_custom);
      SimPost_regSim: Forall (fun '((r1,r2), p) =>
                                p impl_st impl_sigma impl_st' spec_st spec_sigma spec_st'
                                  impl_st'.[r1] spec_st'.[r2]
                        ) sim.(sim_spec).(SimPost).(SimPost_regs)
    }.

  Definition sim_oraat_rule_satisfies_spec'
    int_fn_env struct_env reg_types ext_fn_types
    (spec: sim_rule_spec_t) (rl: action) : Prop :=
    forall impl_st spec_st impl_sigma spec_sigma,
    WF_state reg_types impl_st ->
    WF_state reg_types spec_st ->
    WF_ext_sigma ext_fn_types impl_sigma ->
    WF_ext_sigma ext_fn_types spec_sigma ->
    WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
    typecheck_rule reg_types ext_fn_types int_fn_env struct_env rl = Success 0 ->
    SimPrecondProp spec  impl_st spec_st impl_sigma spec_sigma ->
    match oraat_interp_action impl_sigma int_fn_env struct_env
            (safe_fuel int_fn_env (Datatypes.length int_fn_env) rl) impl_st impl_st true GenericGammaEmpty rl,
          oraat_interp_action spec_sigma int_fn_env struct_env
            (safe_fuel int_fn_env (Datatypes.length int_fn_env) rl) spec_st spec_st true GenericGammaEmpty rl
    with
    | (true, impl_opt), (true, spec_opt) =>
      let impl_st' := match impl_opt with
                      | Some (_, st', _) => st'
                      | None => impl_st
                      end in
      let spec_st' := match spec_opt with
                      | Some (_, st', _) => st'
                      | None => spec_st
                      end in
      WF_state reg_types impl_st' ->
      WF_state reg_types spec_st' ->
      match impl_opt with
      | Some _ => True
      | None => spec.(rule_spec).(FailInversion) impl_sigma impl_st
      end /\
      match spec_opt with
      | Some _ => True
      | None => spec.(rule_spec).(FailInversion) spec_sigma spec_st
      end /\
      SimPostcondProp spec impl_st impl_st' spec_st spec_st' impl_sigma spec_sigma
    | _, _ => True
    end.

  Definition sim_oraat_rule_satisfies_spec
    int_fn_env struct_env reg_types ext_fn_types
    (spec: sim_rule_spec_t) (rl: action) : Prop :=
    forall impl_st spec_st impl_sigma spec_sigma,
    WF_state reg_types impl_st ->
    WF_state reg_types spec_st ->
    WF_ext_sigma ext_fn_types impl_sigma ->
    WF_ext_sigma ext_fn_types spec_sigma ->
    WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
    typecheck_rule reg_types ext_fn_types int_fn_env struct_env rl = Success 0 ->
    SimPrecondProp spec  impl_st spec_st impl_sigma spec_sigma ->
    match oraat_interp_rule impl_sigma int_fn_env struct_env impl_st rl,
          oraat_interp_rule spec_sigma int_fn_env struct_env spec_st rl
    with
    | (true, impl_st'), (true, spec_st') =>
      WF_state reg_types impl_st' ->
      WF_state reg_types spec_st' ->
      SimPostcondProp spec impl_st impl_st' spec_st spec_st' impl_sigma spec_sigma
    | _, _ => True
    end.

  Lemma sim_oraat_rule_satisfies_spec_implies:
    forall int_fn_env struct_env reg_types ext_fn_types spec rl,
    sim_oraat_rule_satisfies_spec' int_fn_env struct_env reg_types ext_fn_types spec rl ->
    sim_oraat_rule_satisfies_spec int_fn_env struct_env reg_types ext_fn_types spec rl.
  Proof.
    unfold sim_oraat_rule_satisfies_spec, sim_oraat_rule_satisfies_spec', oraat_interp_rule.
    intros; destruct_all_matches; propositional;
    specialize (H impl_st spec_st impl_sigma spec_sigma); destruct_all_matches; simplify; propositional.
  Qed.

    Lemma sim_oraat_interp_scheduler'_cons__spec:
      forall {rule_name_t: Type}
      impl_sigma spec_sigma int_fn_env struct_env reg_types ext_fn_types
      (impl_st impl_st'' spec_st spec_st'': state_t) (rules: rule_name_t -> action) rl s
      (spec: sim_rule_spec_t),
      WF_state reg_types impl_st ->
      WF_state reg_types spec_st ->
      WF_ext_sigma ext_fn_types impl_sigma ->
      WF_ext_sigma ext_fn_types spec_sigma ->
      WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
      typecheck_rule reg_types ext_fn_types int_fn_env struct_env (rules rl) = Success 0 ->
      sim_oraat_rule_satisfies_spec' int_fn_env struct_env reg_types ext_fn_types spec (rules rl) ->
      SimPrecondProp spec  impl_st spec_st impl_sigma spec_sigma ->
      oraat_interp_scheduler' impl_sigma int_fn_env struct_env rules impl_st true (Cons rl s) = (true, impl_st'') ->
      oraat_interp_scheduler' spec_sigma int_fn_env struct_env rules spec_st true (Cons rl s) = (true, spec_st'') ->
      exists impl_st' spec_st',
        SimPostcondProp spec impl_st impl_st' spec_st spec_st' impl_sigma spec_sigma /\
        oraat_interp_scheduler' impl_sigma int_fn_env struct_env rules impl_st' true s = (true, impl_st'') /\
        oraat_interp_scheduler' spec_sigma int_fn_env struct_env rules spec_st' true s = (true, spec_st'') /\
        WF_state reg_types impl_st' /\
        WF_state reg_types spec_st'.
    Proof.
      intros * Hwf_impl Hwf_spec Hsigma_impl Hsigma_spec Hfns Htype Hspec Hpre Horaat_impl Horaat_spec; simpl in *.
      apply sim_oraat_rule_satisfies_spec_implies in Hspec.
      consider sim_oraat_rule_satisfies_spec.
      specialize Hspec with (1 := Hwf_impl) (2 := Hwf_spec) (3 := Hsigma_impl) (4 := Hsigma_spec)
                            (5 := Hfns) (6 := Htype) (7 := Hpre).
      destruct_match_pairs.
      specialize @oraat_interp_scheduler'_is_safe_generalizes with (1 := Horaat_impl); propositional.
      specialize @oraat_interp_scheduler'_is_safe_generalizes with (1 := Horaat_spec); propositional.
      assert (WF_state reg_types s1) as Hwf_impl_st'.
      { eapply oraat_interp_rule_safety with (st := impl_st) (sigma := impl_sigma); eauto. }
      assert (WF_state reg_types s0) as Hwf_spec_st'.
      { eapply oraat_interp_rule_safety with (st := spec_st) (sigma := spec_sigma); eauto. }
      propositional.
      eexists; eexists; eauto.
    Qed.

End TODO_MOVE_Infrastructure.

Section SimRuleSpecs.
    Definition job_reg' (tag: Tag) :=
      match tag with
      | Tag0 => Impl.REG_job0'
      | Tag1 => Impl.REG_job1'
      end.

    Definition tag_ext_output_reg (tag: Tag) :=
      match tag with
      | Tag0 => Impl.REG_ext_output_reg0
      | Tag1 => Impl.REG_ext_output_reg1
      end.

    Definition tag_fvalid (tag: Tag) :=
      match tag with
      | Tag0 => Impl.F0Box.REG_valid0
      | Tag1 => Impl.F1Box.REG_valid0
      end.

    Definition tag_gvalid (tag: Tag) :=
      match tag with
      | Tag0 => Impl.G0Box.REG_valid0
      | Tag1 => Impl.G1Box.REG_valid0
      end.
    Definition reg_in_taint_list (tag: Tag) (reg: reg_t) (regs0 regs1: list reg_t) : Prop :=
      match tag with
      | Tag0 => existsb (Nat.eqb reg) regs0 = true
      | Tag1 => existsb (Nat.eqb reg) regs1 = true
      end.

    Definition taint_list (tag: Tag) (regs0 regs1: list reg_t) : list reg_t :=
      match tag with
      | Tag0 => regs0
      | Tag1 => regs1
      end.

  Inductive box_t :=
  | FBox (tag: Tag)
  | GBox (tag: Tag).

  Instance EqDec_box_t : EqDec box_t := _.

  (* Record box_def := *)
  (*   { box_valid_regs : list (reg_t * list bool); *)
  (*     box_data_regs : list reg_t *)
  (*   }. *)
  Import BoxSimCorrect.

  Definition fbox (tag: Tag) : box_def :=
    {| box_valid_regs := [(match tag with
                           | Tag0 => Impl.F0Box.REG_valid0
                           | Tag1 => Impl.F1Box.REG_valid0
                           end, Ob~1)];
       box_data_regs := (taint_list tag (map fst Impl.F0Box.reg_tys_list) (map fst Impl.F1Box.reg_tys_list))
    |}.

  Definition gbox (tag: Tag) : box_def :=
    {| box_valid_regs := [(match tag with
                           | Tag0 => Impl.G0Box.REG_valid0
                           | Tag1 => Impl.G1Box.REG_valid0
                           end, Ob~1)];
       box_data_regs := (taint_list tag (map fst Impl.G0Box.reg_tys_list) (map fst Impl.G1Box.reg_tys_list))
    |}.


  Definition boxes : list (box_t * box_def) :=
    [(FBox Tag0, fbox Tag0)
    ;(FBox Tag1, fbox Tag1)
    ;(GBox Tag0, gbox Tag0)
    ;(GBox Tag1, gbox Tag1)
    ].

  Definition box_fns : list (fn_name_t * (box_t * list ext_fn_t)) :=
    [(Impl.F0Box.FN_can_send_req.(fn_name), (FBox Tag0, []))
    ;(Impl.F0Box.FN_send_req.(fn_name), (FBox Tag0, []))
    ;(Impl.F0Box.FN_can_receive_resp.(fn_name), (FBox Tag0, []))
    ;(Impl.F0Box.FN_receive_resp.(fn_name), (FBox Tag0, []))
    ;(Impl.G0Box.FN_can_send_req.(fn_name), (GBox Tag0, []))
    ;(Impl.G0Box.FN_send_req.(fn_name), (GBox Tag0,[]))
    ;(Impl.G0Box.FN_can_receive_resp.(fn_name), (GBox Tag0, []))
    ;(Impl.G0Box.FN_receive_resp.(fn_name), (GBox Tag0, []))
    ;(Impl.F1Box.FN_can_send_req.(fn_name), (FBox Tag1, []))
    ;(Impl.F1Box.FN_send_req.(fn_name), (FBox Tag1, []))
    ;(Impl.F1Box.FN_can_receive_resp.(fn_name), (FBox Tag1, []))
    ;(Impl.F1Box.FN_receive_resp.(fn_name), (FBox Tag1, []))
    ;(Impl.G1Box.FN_can_send_req.(fn_name), (GBox Tag1, []))
    ;(Impl.G1Box.FN_send_req.(fn_name), (GBox Tag1, []))
    ;(Impl.G1Box.FN_can_receive_resp.(fn_name), (GBox Tag1, []))
    ;(Impl.G1Box.FN_receive_resp.(fn_name), (GBox Tag1, []))
    ].

  Record box_sim (box: box_def)
    (impl_st spec_st: state_t) : Prop :=
  { pf_box_valid_sim: forall r, In r (map fst box.(box_valid_regs)) ->
                           impl_st.[r] = spec_st.[r];
    pf_box_data_sim: box_data_sim box impl_st spec_st
  }.

  Definition fbox_sim (tag: Tag) (impl_st: state_t) (spec_st: state_t) : Prop :=
    box_data_sim (fbox tag) impl_st spec_st.

      (* forall reg, impl_st.[(match tag with *)
      (*        | Tag0 => Impl.F0Box.REG_valid0 *)
      (*        | Tag1 => Impl.F1Box.REG_valid0 *)
      (*        end)] = Ob~1 -> *)
      (*        reg_in_taint_list tag reg (map fst Impl.F0Box.reg_tys_list) *)
      (*                                  (map fst Impl.F1Box.reg_tys_list) -> *)
      (*        impl_st.[reg] = spec_st.[reg]. *)

    Definition gbox_sim (tag: Tag) (impl_st: state_t) (spec_st: state_t) : Prop :=
      box_data_sim (gbox tag) impl_st spec_st.
      (* box_data_sim [(match tag with *)
      (*                 | Tag0 => Impl.G0Box.REG_valid0 *)
      (*                 | Tag1 => Impl.G1Box.REG_valid0 *)
      (*                 end, Ob~1)] *)
      (*               (taint_list tag (map fst Impl.G0Box.reg_tys_list) (map fst Impl.G1Box.reg_tys_list)) *)
      (*               impl_st spec_st. *)

      (* forall reg, impl_st.[(match tag with *)
      (*        | Tag0 => Impl.G0Box.REG_valid0 *)
      (*        | Tag1 => Impl.G1Box.REG_valid0 *)
      (*        end)] = Ob~1 -> *)
      (*        reg_in_taint_list tag reg (map fst Impl.G0Box.reg_tys_list) *)
      (*                                  (map fst Impl.G1Box.reg_tys_list) -> *)
      (*        impl_st.[reg] = spec_st.[reg]. *)

    Definition output_reg_sim (tag: Tag) (impl_st: state_t) (spec_st: state_t) : Prop :=
      impl_st.[Impl.REG_clk] = (match tag with
                                | Tag0 => Ob~1
                                | Tag1 => Ob~0
                                end) ->
      impl_st.[Impl.REG_ext_output_reg] =
      spec_st.[Impl.REG_ext_output_reg].


    Inductive SimCustomProps :=
    | SimCustomInput
    | SimCustom__BoxF
    | SimCustom__BoxG
    | SimSigmaF
    | SimSigmaG.

    Scheme Equality for SimCustomProps.

    Definition SimSpec__InteractWithWorld : @sim_spec_t SimCustomProps :=
      {| SimPre :=
          {| SimPre_regs := [];
             SimPre_custom := []
          |};
         SimPost :=
          {| SimPost_custom := [];
             SimPost_regs := []
          |}
      |}.

    Definition SimRuleSpec__InteractWithWorld : sim_rule_spec_t :=
      {| rule_spec := RlSpec__InteractWithWorld;
         sim_spec := SimSpec__InteractWithWorld
      |}.


    Definition SimSpec__DoInput (tag: Tag) : @sim_spec_t SimCustomProps :=
      {| SimPre :=
          {| SimPre_regs :=
              [((job_reg tag, job_reg tag),
                 fun ist sst iv sv => iv = sv )
              ];
             SimPre_custom :=
              [(SimCustomInput,
                 fun ist isigma sst ssigma =>
                 (ist.[Impl.REG_ext_ready_for_job] <> mk_ready_tag tag /\
                  sst.[Impl.REG_ext_ready_for_job] <> mk_ready_tag tag) \/
                 (ist.[Impl.REG_ext_ready_for_job] = mk_ready_tag tag /\
                  ist.[Impl.REG_ext_ready_for_job] = sst.[Impl.REG_ext_ready_for_job] /\
                  (forall job_id, isigma Impl.EXTFN_GetJob job_id = ssigma Impl.EXTFN_GetJob job_id))
               )
              ]
          |};
         SimPost :=
          {| SimPost_custom :=
              [];
             SimPost_regs :=
              [((job_reg tag, job_reg tag),
                 fun ist isigma ist' sst ssigma sst' iv sv =>
                   iv = sv
               )
              ]
          |}
      |}.

    Definition SimRuleSpec__DoInput (tag: Tag) : sim_rule_spec_t :=
      {| rule_spec := RlSpec__DoInput;
         sim_spec := SimSpec__DoInput tag
      |}.

    Definition SimSpec__StepBoxes (tag: Tag) : @sim_spec_t SimCustomProps :=
      {| SimPre :=
          {| SimPre_regs := [
                               ((tag_fvalid tag, tag_fvalid tag), fun _ _ iv sv => iv = sv);
                               ((tag_gvalid tag, tag_gvalid tag), fun _ _ iv sv => iv = sv)
                            ];
             SimPre_custom :=
                [(SimCustom__BoxF, fun ist isigma sst ssigma => fbox_sim tag ist sst)
                 ;(SimCustom__BoxG, fun ist isigma sst ssigma => gbox_sim tag ist sst)
                 ;(SimSigmaF, fun ist isigma sst ssigma =>  forall fn v,
                                fn = match tag with | Tag0 => Impl.EXTFN_F0 | Tag1 => Impl.EXTFN_F1 end ->
                                isigma fn v = ssigma fn v)
                 ;(SimSigmaG, fun ist isigma sst ssigma =>  forall fn v,
                                fn = match tag with | Tag0 => Impl.EXTFN_G0 | Tag1 => Impl.EXTFN_G1 end ->
                                isigma fn v = ssigma fn v)
                ]
          |};
         SimPost :=
          {| SimPost_custom :=
                [(SimCustom__BoxF, fun ist isigma ist' sst ssigma sst' => fbox_sim tag ist' sst')
                ;(SimCustom__BoxG, fun ist isigma ist' sst ssigma sst' => gbox_sim tag ist' sst')
                ];
             SimPost_regs := [
                 ((tag_fvalid tag, tag_fvalid tag), fun ist isigma ist' sst ssigma st' iv sv => iv = sv)
                ;((tag_gvalid tag, tag_gvalid tag), fun ist isigma ist' sst ssigma st' iv sv => iv = sv)
                ]
          |}
      |}.

    Definition SimRuleSpec__StepBoxes (tag: Tag) : sim_rule_spec_t :=
      {| rule_spec := RlSpec__StepBoxes;
         sim_spec := SimSpec__StepBoxes tag
      |}.

    Definition SimSpec__DoStep (step_id: Tag) (sim_id: Tag): @sim_spec_t SimCustomProps :=
      let sim_tag :=
        {| SimPre :=
            {| SimPre_regs := [((Impl.REG_clk, Impl.REG_clk), fun _ _ iv sv => iv = sv);
                               ((job_reg step_id, job_reg step_id), fun _ _ iv sv => iv = sv);
                               ((tag_fvalid step_id, tag_fvalid step_id), fun _ _ iv sv => iv = sv);
                               ((tag_gvalid step_id, tag_gvalid step_id), fun _ _ iv sv => iv = sv)
                              ];
               SimPre_custom :=
                [(SimCustom__BoxF, fun ist isigma sst ssigma => fbox_sim step_id ist sst)
                 ;(SimCustom__BoxG, fun ist isigma sst ssigma => gbox_sim step_id ist sst)
                ]
            |};
           SimPost :=
            {| SimPost_custom :=
                [(SimCustom__BoxF, fun ist isigma ist' sst ssigma sst' => fbox_sim step_id ist' sst')
                ;(SimCustom__BoxG, fun ist isigma ist' sst ssigma sst' => gbox_sim step_id ist' sst')
                ];
               SimPost_regs :=
                [((job_reg step_id, job_reg step_id), fun ist isigma ist' sst ssigma st' iv sv => iv = sv)
                ;((job_reg' step_id, job_reg' step_id), fun ist isigma ist' sst ssigma st' iv sv => iv = sv)
                ;((tag_fvalid step_id, tag_fvalid step_id), fun ist isigma ist' sst ssigma st' iv sv => iv = sv)
                ;((tag_gvalid step_id, tag_gvalid step_id), fun ist isigma ist' sst ssigma st' iv sv => iv = sv)
                ;((tag_ext_output_reg step_id, tag_ext_output_reg step_id), fun ist isigma ist' sst ssigma st' iv sv => iv = sv)
                ]
            |}
        |} in
      match step_id, sim_id with
      | Tag0, Tag0 => sim_tag
      | Tag1, Tag1 => sim_tag
      | _, _ =>
          {| SimPre :=
              {| SimPre_regs := [];
                 SimPre_custom := []
              |};
            SimPost :=
              {| SimPost_custom := [];
                 SimPost_regs := [];
              |}
          |}
      end.


    Definition SimRuleSpec__DoStep0 (tag: Tag): sim_rule_spec_t :=
      {| rule_spec := RlSpec__DoStep0;
         sim_spec := SimSpec__DoStep Tag0 tag
      |}.

    Definition SimRuleSpec__DoStep1 (tag: Tag): sim_rule_spec_t :=
      {| rule_spec := RlSpec__DoStep1;
         sim_spec := SimSpec__DoStep Tag1 tag
      |}.

    Definition SimSpec__UpdateReady (tag: Tag): @sim_spec_t SimCustomProps :=
      {| SimPre :=
          {| SimPre_regs := [((Impl.REG_clk, Impl.REG_clk), fun _ _ iv sv => iv = sv);
                             (* ((job_reg tag, job_reg tag), fun _ _ iv sv => iv = sv); *)
                             ((job_reg' tag, job_reg' tag), fun _ _ iv sv => iv = sv);
                             ((tag_ext_output_reg tag, tag_ext_output_reg tag), fun _ _ iv sv => iv = sv)
                             (* ((tag_fvalid tag, tag_fvalid tag), fun _ _ iv sv => iv = sv); *)
                             (* ((tag_gvalid tag, tag_fvalid tag), fun _ _ iv sv => iv = sv) *)
                            ];
             SimPre_custom := []
          |};
         SimPost :=
          {| SimPost_custom := [];
              (* [(SimCustom__BoxF, fun ist isigma ist' sst ssigma sst' => fbox_sim tag ist' sst') *)
              (* ;(SimCustom__BoxG, fun ist isigma ist' sst ssigma sst' => gbox_sim tag ist' sst') *)
              (* ]; *)
             SimPost_regs :=
              [((Impl.REG_clk, Impl.REG_clk), fun ist isigma ist' sst ssigma st' iv sv => iv = sv)
              ;((Impl.REG_ext_output_reg, Impl.REG_ext_output_reg),
                 fun ist isigma ist' sst ssigma sst' iv sv => output_reg_sim tag ist' sst'
               )
              (* ;((job_reg tag, job_reg tag), fun ist isigma ist' sst ssigma st' iv sv => iv = sv) *)
              (* ;((tag_fvalid tag, tag_fvalid tag), fun ist isigma ist' sst ssigma st' iv sv => iv = sv) *)
              (* ;((tag_gvalid tag, tag_gvalid tag), fun ist isigma ist' sst ssigma st' iv sv => iv = sv) *)
              ]
          |}
      |}.

    Definition SimRuleSpec__UpdateReady (tag: Tag): sim_rule_spec_t :=
      {| rule_spec := RlSpec__UpdateReady;
         sim_spec := SimSpec__UpdateReady tag
      |}.


End SimRuleSpecs.

Notation __sim_oraat_rule_satisfies_spec := (sim_oraat_rule_satisfies_spec' Impl.int_fn_env Impl.struct_env Impl.reg_types Impl.ext_fn_types).

Record sim_rule_spec_t' :=
  { SimRuleSpec_rl: rule
  ; SimRuleSpec_spec: @sim_rule_spec_t SimCustomProps
  ; SimRuleSpec_pf : __sim_oraat_rule_satisfies_spec SimRuleSpec_spec SimRuleSpec_rl
  }.



Module Type SimProofs_Sig.
  Parameter SimRlSatisfiesSpec__InteractWithWorld :
    __sim_oraat_rule_satisfies_spec SimRuleSpec__InteractWithWorld (Impl.rules Impl.InteractWithWorld).
  Parameter SimRlSatisfiesSpec__DoInput :
    forall tag, __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoInput tag) (Impl.rules Impl.DoInput).
  Parameter SimRlSatisfiesSpec__StepBoxes :
    forall tag, __sim_oraat_rule_satisfies_spec (SimRuleSpec__StepBoxes tag) (Impl.rules Impl.StepBoxes).
  Parameter SimRlSatisfiesSpec__DoStep0 :
    forall tag, __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoStep0 tag) (Impl.rules Impl.DoStep0).
  Parameter SimRlSatisfiesSpec__DoStep1 :
    forall tag, __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoStep1 tag) (Impl.rules Impl.DoStep1).
  Parameter SimRlSatisfiesSpec__UpdateReady :
    forall tag, __sim_oraat_rule_satisfies_spec (SimRuleSpec__UpdateReady tag) (Impl.rules Impl.UpdateReady).
End SimProofs_Sig.

Notation spec_local_machine_t := (@Spec.local_machine_state_t SpecParams.local_st_t).

Section Invariants.

    Definition sim0_regs : list reg_t := [Impl.REG_job0; Impl.F0Box.REG_valid0; Impl.G0Box.REG_valid0].
    Definition sim1_regs : list reg_t := [Impl.REG_job1; Impl.F1Box.REG_valid0; Impl.G1Box.REG_valid0].

    Definition is_taint_reg (tag: Tag) (reg: reg_t) : Prop :=
      match tag with
      | Tag0 => existsb (Nat.eqb reg) sim0_regs = true
      | Tag1 => existsb (Nat.eqb reg) sim1_regs = true
      end.


    Record LocalRegSim (tag: Tag) (impl_st: state_t) (spec_st: state_t) : Prop :=
    { pf_taint_sim: forall reg, is_taint_reg tag reg ->
                             impl_st.[reg] = spec_st.[reg]
    ; pf_clk_sim: impl_st.[Impl.REG_clk] = spec_st.[Impl.REG_clk]
    ; pf_f_sim : fbox_sim tag impl_st spec_st
    ; pf_g_sim : gbox_sim tag impl_st spec_st
    }.


    Record LocalStateSim__Running (tag: Tag) (impl_st: state_t) (spec_st: state_t) : Prop :=
      { spec_invariant: SpecInvariant tag spec_st
      ; pf_reg_sim: LocalRegSim tag impl_st spec_st
      ; pf_ext_output_reg_sim: output_reg_sim tag impl_st spec_st
      }.

    Definition impl_boxes_reset (tag: Tag) (impl_st: state_t) : Prop :=
      forall reg, reg_in_taint_list tag reg [Impl.F0Box.REG_valid0; Impl.G0Box.REG_valid0]
                                       [Impl.F1Box.REG_valid0; Impl.G1Box.REG_valid0] ->
             impl_st.[reg] = Ob~0.

    Record LocalStateSim__Waiting (tag: Tag) (impl_st: state_t) : Prop :=
    { pf_waiting_output_reg_None:
        impl_st.[Impl.REG_clk] = (match tag with | Tag0 => Ob~1 | Tag1 => Ob~0 end) ->
        impl_st.[Impl.REG_ext_output_reg] = zeroes (struct_sz Impl.S_maybe_sz)
    ; pf_waiting_job_stage_None:
          forall reg, reg = job_reg tag ->
          unsafe_get_job_stage (impl_st.[reg]) = Impl.ENUM_stage__None
    ; pf_waiting_boxes_reset : impl_boxes_reset tag impl_st
    }.

    Definition LocalStateSim : Tag -> state_t -> @Spec.local_machine_state_t SpecParams.local_st_t -> Prop :=
      fun tag impl_st spec_st =>
        match spec_st with
        | Spec.Running (Success spec_st') =>
          LocalStateSim__Running tag impl_st spec_st'
        | Spec.Running (Failure _) => False
        | Spec.Waiting => LocalStateSim__Waiting tag impl_st
        end.

    Definition get_spec_st (tag: Tag) (spec_st: @Spec.state_t SpecParams.local_st_t) : spec_local_machine_t :=
      match tag with
      | Tag0 => Spec.state0 spec_st
      | Tag1 => Spec.state1 spec_st
      end.

    Record Sim (impl_st: state_t) (spec_st: @Spec.state_t SpecParams.local_st_t) : Prop :=
    { Sim_impl_invariant: ImplInvariant impl_st;
      Sim_clk: impl_st.[Impl.REG_clk] = [Spec.turn spec_st];
      Sim_local: forall tag, LocalStateSim tag impl_st (get_spec_st tag spec_st);
    }.

    Lemma is_taint_reg_job:
      forall tag,
        is_taint_reg tag (job_reg tag).
    Proof.
      destruct tag; reflexivity.
    Qed.

    Lemma is_job_reg_job:
      forall tag,
        is_job_reg tag (job_reg tag).
    Proof.
      destruct tag; reflexivity.
    Qed.

    Notation __sim_oraat_rule_satisfies_spec := (@sim_oraat_rule_satisfies_spec' SimCustomProps Impl.int_fn_env Impl.struct_env Impl.reg_types Impl.ext_fn_types).

End Invariants.

Create HintDb solve_taint.
Global Hint Immediate is_taint_reg_job: solve_taint.
Global Hint Immediate is_job_reg_job: solve_taint.
Global Hint Immediate zeroes_length : solve_bits.

Ltac basic_simpl :=
  match goal with
  | _ => simplify
  | _ => progress(auto with solve_bits)
  end.

Ltac solve_reg_in_taint:=
  repeat match goal with
  | H: reg_in_taint_list _ _ _ _ |- _ =>
    apply regs_in_taint_existsb in H
  | H : existsb (Nat.eqb _) _ = true |- _ =>
    apply existsb_exists in H; propositional
  | H: In ?x _ |- Impl.initial_state ?x = _  =>
    inversions H; [reflexivity |]
  | _ => basic_simpl
  end.

Ltac apply_sim :=
  match goal with
  | H: Sim ?impl_st ?spec_st
    |- ImplInvariant ?impl_st =>
    solve[apply (Sim_impl_invariant _ _ H)]
  | H: Sim ?impl_st ?spec_st
    |- WF_state Impl.reg_types ?impl_st =>
    pose proof (Sim_impl_invariant _ _ H); apply_impl_invariant
  | H : LocalStateSim__Running ?tag ?impl_st ?spec_st
    |- LocalRegSim ?tag ?impl_st ?spec_st =>
    apply pf_reg_sim; auto
  | H : LocalStateSim__Running ?tag ?impl_st ?spec_st
    |- LocalRegSim ?tag ?impl_st ?spec_st =>
    apply pf_reg_sim; auto
  | H: LocalStateSim__Running ?tag ?impl_st ?spec_st
    |- SpecInvariant ?tag ?spec_st =>
      apply (spec_invariant _ _ _ H)
  | H: SpecInvariant ?tag ?spec_st
    |- WF_state Impl.reg_types ?spec_st =>
      apply (pf_wf_spec _ _ H)
  end.
Ltac ri_solve :=
  match goal with
  | |- _ => solve[apply_sim]
  | |- _ => solve[apply_wf_sigma ]
  | |- _ => solve[apply_impl_invariant]
  | |- _ => solve[auto with WF_auto solve_taint]
 | |- WF_int_fn_env Impl.reg_types Impl.ext_fn_types Impl.int_fn_env Impl.struct_env=>
    solve[apply Impl.typecheck_int_fns_Success]
  | |- _ => progress(auto)
  end.
Ltac ri_step_match V :=
  match V with
  | ?impl_st.[?_reg] =>
    match goal with
    | H: Sim ?impl_st _ |- _ =>
      let foo := fresh in
      pose (impl_wf_state _ (Sim_impl_invariant _ _ H)) as foo;
      unfold WF_state in foo; specialize foo with (reg := _reg); simpl in foo;
      destruct_matches_in_hyp foo; auto
    end
  end.


Module StepSim (SimProofs: SimProofs_Sig).
  Include SimProofs.

  Section Specs.
    Definition Spec__InteractWithWorld : sim_rule_spec_t' :=
      {| SimRuleSpec_rl := Impl.rules Impl.InteractWithWorld;
         SimRuleSpec_spec := SimRuleSpec__InteractWithWorld;
         SimRuleSpec_pf := SimRlSatisfiesSpec__InteractWithWorld
      |}.

    Definition Spec__DoInput (tag: Tag) : sim_rule_spec_t' :=
      {| SimRuleSpec_rl := Impl.rules Impl.DoInput;
         SimRuleSpec_spec := SimRuleSpec__DoInput tag;
         SimRuleSpec_pf := SimRlSatisfiesSpec__DoInput tag
      |}.

    Definition Spec__StepBoxes (tag: Tag) : sim_rule_spec_t' :=
      {| SimRuleSpec_rl := Impl.rules Impl.StepBoxes;
         SimRuleSpec_spec := SimRuleSpec__StepBoxes tag;
         SimRuleSpec_pf := SimRlSatisfiesSpec__StepBoxes tag
      |}.


     Definition Spec__Step0 (tag: Tag): sim_rule_spec_t' :=
      {| SimRuleSpec_rl := Impl.rules Impl.DoStep0;
         SimRuleSpec_spec := SimRuleSpec__DoStep0 tag;
         SimRuleSpec_pf := SimRlSatisfiesSpec__DoStep0 tag
      |}.

    Definition Spec__Step1 (tag: Tag): sim_rule_spec_t' :=
      {| SimRuleSpec_rl := Impl.rules Impl.DoStep1;
         SimRuleSpec_spec := SimRuleSpec__DoStep1 tag;
         SimRuleSpec_pf := SimRlSatisfiesSpec__DoStep1 tag
      |}.

    Definition Spec__UpdateReady (tag: Tag): sim_rule_spec_t' :=
      {| SimRuleSpec_rl := Impl.rules Impl.UpdateReady;
         SimRuleSpec_spec := SimRuleSpec__UpdateReady tag;
         SimRuleSpec_pf := SimRlSatisfiesSpec__UpdateReady tag
      |}.

  End Specs.

  Lemma SimPostcondProp_implies_taint_set_to_Prop_impl:
    forall {customProps} (spec: @sim_rule_spec_t customProps) ist ist' sst sst' isigma ssigma,
      SimPostcondProp spec ist ist' sst sst' isigma ssigma ->
      taint_set_to_prop ist ist' (spec.(rule_spec).(Post).(Post_taint_set)).
  Proof.
    intros. destruct H; propositional.
    eapply postcond_to_Prop_implies_taint_set_to_Prop; eauto.
  Qed.

  Lemma SimPostcondProp_implies_taint_set_to_Prop_spec:
    forall {customProps} (spec: @sim_rule_spec_t customProps) ist ist' sst sst' isigma ssigma,
      SimPostcondProp spec ist ist' sst sst' isigma ssigma ->
      taint_set_to_prop sst sst' (spec.(rule_spec).(Post).(Post_taint_set)).
  Proof.
    intros. destruct H; propositional.
    eapply postcond_to_Prop_implies_taint_set_to_Prop; eauto.
  Qed.

  Lemma SimPostcondProp_lookup_reg:
    forall {customProps} (spec: @sim_rule_spec_t customProps) ist ist' sst sst' isigma ssigma prop reg1 reg2,
      SimPostcondProp spec ist ist' sst sst' isigma ssigma ->
      find (fun '((r1,r2), _) => Nat.eqb reg1 r1 && Nat.eqb reg2 r2) spec.(sim_spec).(SimPost).(SimPost_regs) = Some ((reg1,reg2),prop) ->
      prop ist isigma ist' sst ssigma sst' ist'.[reg1] sst'.[reg2].
  Proof.
    intros * HSim Hfind.
    destruct HSim.
    rewrite Forall_forall in SimPost_regSim0.
    apply find_some in Hfind. propositional.
    specialize SimPost_regSim0 with (1 := Hfind0). simplify. rewrite andb_true_iff in Hfind1. propositional; simplify.
  Qed.

  Lemma SimPostcondProp_lookup_custom:
    forall (spec: @sim_rule_spec_t SimCustomProps) ist ist' sst sst' isigma ssigma prop custom,
      SimPostcondProp spec ist ist' sst sst' isigma ssigma ->
      find (fun '(c, _) => SimCustomProps_beq c custom) spec.(sim_spec).(SimPost).(SimPost_custom) = Some (custom,prop) ->
      prop ist isigma ist' sst ssigma sst'.
  Proof.
    intros * HSim Hfind.
    destruct HSim.
    rewrite Forall_forall in SimPost_customSim0.
    apply find_some in Hfind. propositional.
    specialize SimPost_customSim0 with (1 := Hfind0). simplify. auto.
  Qed.


  Lemma is_taint_reg_equiv:
    forall tag reg,
      is_taint_reg tag reg <->
        reg = (job_reg tag) \/ reg = (tag_fvalid tag) \/ reg = (tag_gvalid tag).
  Proof.
    intros; unfold is_taint_reg; simpl.
    repeat rewrite orb_false_r.
    destruct tag; repeat rewrite orb_true_iff; repeat rewrite PeanoNat.Nat.eqb_eq; simpl; reflexivity.
  Qed.

  Ltac sim_rewrite_no_write_impl reg postcond :=
    rewrite (taint_set_to_prop_no_write'
               _ _ _ reg
               (SimPostcondProp_implies_taint_set_to_Prop_impl _ _ _ _  _ _ _ postcond) eq_refl).
  Ltac sim_rewrite_no_write_impl_in H reg postcond :=
    rewrite (taint_set_to_prop_no_write'
               _ _ _ reg
               (SimPostcondProp_implies_taint_set_to_Prop_impl _ _ _ _  _ _ _ postcond) eq_refl) in H.

  Ltac sim_rewrite_no_write_spec reg postcond :=
    rewrite (taint_set_to_prop_no_write' _ _ _ reg
               (SimPostcondProp_implies_taint_set_to_Prop_spec _ _ _ _  _ _ _ postcond) eq_refl).

  Ltac sim_rewrite_no_write_spec_in H reg postcond :=
    rewrite (taint_set_to_prop_no_write' _ _ _ reg
               (SimPostcondProp_implies_taint_set_to_Prop_spec _ _ _ _  _ _ _ postcond) eq_refl) in H.


  Ltac sim_rewrite_no_write_sim reg postcond :=
    sim_rewrite_no_write_impl reg postcond;
    sim_rewrite_no_write_spec reg postcond.


  Ltac sim_apply_reg_spec reg postcond :=
    apply (SimPostcondProp_lookup_reg _ _ _ _ _ _ _ _ reg reg postcond eq_refl).
  Ltac sim_apply_reg_spec_in H reg postcond :=
    apply (SimPostcondProp_lookup_reg _ _ _ _ _ _ _ _ reg reg postcond eq_refl) in H.

  Ltac sim_rewrite_with_reg_spec reg postcond :=
    rewrite (SimPostcondProp_lookup_reg _ _ _ _ _ _ _ _ reg reg postcond eq_refl).

  Ltac sim_rewrite_with_reg_spec_in H reg postcond :=
    rewrite (SimPostcondProp_lookup_reg _ _ _ _ _ _ _ _ reg reg postcond eq_refl) in H.
  Ltac sim_rewrite_with_custom custom postcond :=
    rewrite (SimPostcondProp_lookup_custom _ _ _ _ _ _ _ _ custom postcond eq_refl).
  Ltac sim_apply_with_custom custom postcond :=
    apply (SimPostcondProp_lookup_custom _ _ _ _ _ _ _ _ custom postcond eq_refl).

  Ltac sim_rewrite_with_custom_in H custom postcond :=
    rewrite (SimPostcondProp_lookup_custom _ _ _ _ _ _ _ _ custom postcond eq_refl) in H.
  Ltac sim_apply_custom_in H custom postcond :=
    apply (SimPostcondProp_lookup_custom _ _ _ _ _ _ _ _ custom postcond eq_refl) in H.



  Ltac step_sim_oraat_scheduler
      Himpl_sched Hspec_sched RlSpec
      NewImplSt NewSpecSt NewPostCond
      NewImplSched NewSpecSched NewWfImplSt NewWfSpecSt :=
    eapply sim_oraat_interp_scheduler'_cons__spec with
      (reg_types := Impl.reg_types) (ext_fn_types := Impl.ext_fn_types)
      (spec := RlSpec.(SimRuleSpec_spec)) (9 := Himpl_sched)
      in Hspec_sched; [
        destruct Hspec_sched as (NewImplSt & NewSpecSt & NewPostCond & NewImplSched & NewSpecSched & NewWfImplSt & NewWfSpecSt)
      | ri_solve | ri_solve | ri_solve | ri_solve | ri_solve | ri_solve | apply RlSpec.(SimRuleSpec_pf) | ]; clear Himpl_sched.

    Lemma Sim_step:
      forall tag impl_input spec_input spec_st spec_st' impl_st impl_st' sigma,
        Impl.wf_sigma sigma ->
        ImplInvariant impl_st ->
        SpecInvariant tag spec_st ->
        LocalRegSim tag impl_st spec_st ->
        Impl.koika_step' sigma impl_st impl_input = Success impl_st' ->
        Impl.koika_step' sigma spec_st spec_input = Success spec_st' ->
        WF_state Impl.reg_types spec_st' ->
        (((impl_st.[Impl.REG_ext_ready_for_job] <> mk_ready_tag tag)
          /\ spec_st.[Impl.REG_ext_ready_for_job] <> mk_ready_tag tag
          /\ spec_input = None) \/
          (exists input, impl_input = Some input /\ impl_input = spec_input /\
                    impl_st.[Impl.REG_ext_ready_for_job] = spec_st.[Impl.REG_ext_ready_for_job] /\
                    spec_st.[Impl.REG_ext_ready_for_job] = mk_ready_tag tag
          )) ->
        (unsafe_get_job_stage spec_st.[job_reg tag] = Impl.ENUM_stage__None ->
         spec_st.[Impl.REG_ext_ready_for_job] = mk_ready_tag tag) ->
        LocalStateSim__Running tag impl_st' spec_st'.
    Proof.
      intros * Hsigma HImpl HSpec HSim Himpl_step Hspec_step Hwf_spec' Hinput Hext_ready.
      assert (SpecInvariant tag spec_st') as HSpecInv'.
      { eapply SpecProofs.spec_invariant_preserved; eauto.
        destruct Hinput; propositional.
        - split.
          + intros; congruence.
          + unfold is_some; propositional; discriminate.
        - split.
          + intros; unfold is_some. eexists; eauto.
          + rewrite H4. reflexivity.
      }

      unfold Impl.koika_step', interp_cycle in *. simplify.
      rename Heqr0 into Himpl_step. rename Heqr into Hspec_step.
      specialize schedule_does_not_conflict_implies with
          (1 := Impl.oraat_schedule_does_not_conflict); intros (taint & Htaint).
      eapply oraat_interp_schedule'_correct with (reg_types := Impl.reg_types) (ext_fn_types := Impl.ext_fn_types) (taint := SortedRegEnv.empty) (taint' := taint) in Himpl_step; eauto; try ri_solve.
      2: { eapply taint_env_approximates_log_empty. }
      eapply oraat_interp_schedule'_correct with (reg_types := Impl.reg_types) (ext_fn_types := Impl.ext_fn_types) (taint := SortedRegEnv.empty) (taint' := taint) in Hspec_step; eauto; try ri_solve.
      2: { eapply taint_env_approximates_log_empty. }
      clear dependent taint.

      rewrite commit_update_empty in Himpl_step.
      rewrite commit_update_empty in Hspec_step.
      consider Impl.schedule. consider interp_scheduler.

      step_sim_oraat_scheduler Himpl_step Hspec_step Spec__InteractWithWorld
                               ImplSt__World SpecSt__World Post__World
                               ImplSched__World SpecSched__World ImplWf__World SpecWf__World.
      2: { repeat constructor. }

      step_sim_oraat_scheduler ImplSched__World SpecSched__World (Spec__DoInput tag)
                               ImplSt__Input SpecSt__Input Post__Input
                               ImplSched__Input SpecSched__Input ImplWf__Input SpecWf__Input.
      2: { constructor; try solve[repeat constructor].
           - constructor; auto.
             destruct Hinput as [Hinput | Hinput].
             + left. propositional.
               sim_rewrite_no_write_sim Impl.REG_ext_ready_for_job Post__World; auto.
             + right. propositional.
               sim_rewrite_no_write_sim Impl.REG_ext_ready_for_job Post__World; auto.
               split_ands_in_goal; auto. rewrite Hinput2. auto.
           - constructor; auto.
             destruct tag;
               match goal with
               | |- ?x.[?_reg] = _ =>
                   sim_rewrite_no_write_sim _reg Post__World
               end; erewrite pf_taint_sim; eauto; reflexivity.
         }

      step_sim_oraat_scheduler ImplSched__Input SpecSched__Input (Spec__StepBoxes tag)
                               ImplSt__Boxes SpecSt__Boxes Post__Boxes
                               ImplSched__Boxes SpecSched__Boxes ImplWf__Boxes SpecWf__Boxes.
      2: { constructor; try solve[repeat constructor].
           - repeat constructor;
               [ | | intros fn v; specialize Impl.wf_Constants with (1 := Hsigma) (fn := fn) (input1 := impl_input) (input2 := spec_input); destruct tag; intros Heq; intros; subst; simpl in Heq; rewrite Heq; solve[auto] .. ];
             unfold fbox_sim, gbox_sim, BoxSimCorrect.box_data_sim; intro Hvalid; apply Forall_inv in Hvalid;
               intro reg; destruct tag; simpl; rewrite orb_false_r;
               repeat rewrite orb_true_iff; repeat rewrite PeanoNat.Nat.eqb_eq;
               intros Hcase; destruct Hcase as [Hcase | [Hcase | Hcase]]; subst reg;
             match goal with
             | |- ?x.[?_reg] = _ =>
               sim_rewrite_no_write_sim _reg Post__Input;
               sim_rewrite_no_write_sim _reg Post__World
             end;
             match type of Hvalid with
             | ImplSt__Input.[?_reg] = _ =>
               sim_rewrite_no_write_impl_in Hvalid _reg Post__Input;
               sim_rewrite_no_write_impl_in Hvalid _reg Post__World
             end; try solve[eapply pf_f_sim; eauto; simpl; auto];
                  try solve[eapply pf_g_sim; eauto; simpl; auto].
           - repeat constructor; destruct tag; simpl.
             all: match goal with
             | |- ?x.[?_reg] = _ =>
               sim_rewrite_no_write_sim _reg Post__Input;
               sim_rewrite_no_write_sim _reg Post__World;
               eapply pf_taint_sim; eauto; reflexivity
             end.
         }
      step_sim_oraat_scheduler ImplSched__Boxes SpecSched__Boxes (Spec__Step0 tag)
                               ImplSt__Step0 SpecSt__Step0 Post__Step0
                               ImplSched__Step0 SpecSched__Step0 ImplWf__Step0 SpecWf__Step0.
      2: { constructor; try solve[repeat constructor].
           - destruct tag; try solve[repeat constructor];
             repeat constructor;
               unfold fbox_sim, BoxSimCorrect.box_data_sim; intro Hvalid; apply Forall_inv in Hvalid;
               intro reg;
               simpl; rewrite orb_false_r; repeat rewrite orb_true_iff;
                 repeat rewrite PeanoNat.Nat.eqb_eq;
               intros Hcase; destruct Hcase as [ Hcase | [Hcase | Hcase]]; subst.
               all: try solve[sim_rewrite_with_custom SimCustom__BoxF Post__Boxes; simpl BoxSimCorrect.box_valid_regs; auto; reflexivity];
                    try solve[sim_rewrite_with_custom SimCustom__BoxG Post__Boxes; simpl BoxSimCorrect.box_valid_regs; auto; reflexivity].
           - destruct tag; try solve[repeat constructor].
             repeat constructor; simpl.
             + sim_rewrite_no_write_sim Impl.REG_clk Post__Boxes.
               sim_rewrite_no_write_sim Impl.REG_clk Post__Input.
               sim_rewrite_no_write_sim Impl.REG_clk Post__World.
               eapply pf_clk_sim; eauto.
             + sim_rewrite_no_write_sim Impl.REG_job0 Post__Boxes.
               sim_rewrite_with_reg_spec Impl.REG_job0 Post__Input; auto.
             + sim_rewrite_with_reg_spec Impl.F0Box.REG_valid0 Post__Boxes; auto.
             + sim_rewrite_with_reg_spec Impl.G0Box.REG_valid0 Post__Boxes; auto.
         }

      step_sim_oraat_scheduler ImplSched__Step0 SpecSched__Step0 (Spec__Step1 tag)
                               ImplSt__Step1 SpecSt__Step1 Post__Step1
                               ImplSched__Step1 SpecSched__Step1 ImplWf__Step1 SpecWf__Step1.
      2: { constructor; try solve[repeat constructor].
           - destruct tag; try solve[repeat constructor]; simpl.
             repeat constructor.
             + unfold fbox_sim, BoxSimCorrect.box_data_sim; intro Hvalid; apply Forall_inv in Hvalid; intro reg; simpl.
               sim_rewrite_no_write_impl_in Hvalid Impl.F1Box.REG_valid0 Post__Step0.
               simpl. rewrite orb_false_r. repeat rewrite orb_true_iff. repeat rewrite PeanoNat.Nat.eqb_eq.
               intros Hcase; destruct Hcase as [Hcase | [Hcase | Hcase]]; subst.
               all: match goal with
                    | |- ?X.[?_reg] = _ =>
                        sim_rewrite_no_write_sim _reg Post__Step0
                    end; sim_rewrite_with_custom SimCustom__BoxF Post__Boxes; simpl BoxSimCorrect.box_valid_regs; auto; reflexivity.
             + unfold gbox_sim, BoxSimCorrect.box_data_sim; intro Hvalid; apply Forall_inv in Hvalid; intro reg;
               sim_rewrite_no_write_impl_in Hvalid Impl.G1Box.REG_valid0 Post__Step0;
               simpl; rewrite orb_false_r; repeat rewrite orb_true_iff;
                 repeat rewrite PeanoNat.Nat.eqb_eq.
               intros Hcase; destruct Hcase as [Hcase | [Hcase | Hcase]]; subst.
               all: match goal with
                    | |- ?X.[?_reg] = _ =>
                        sim_rewrite_no_write_sim _reg Post__Step0
                    end; sim_rewrite_with_custom SimCustom__BoxG Post__Boxes; simpl BoxSimCorrect.box_valid_regs; auto; reflexivity.
           - destruct tag; try solve[repeat constructor]; simpl.
             repeat constructor.
             + sim_rewrite_no_write_sim Impl.REG_clk Post__Step0.
               sim_rewrite_no_write_sim Impl.REG_clk Post__Boxes.
               sim_rewrite_no_write_sim Impl.REG_clk Post__Input.
               sim_rewrite_no_write_sim Impl.REG_clk Post__World.
               eapply pf_clk_sim; eauto.
             + sim_rewrite_no_write_sim Impl.REG_job1 Post__Step0.
               sim_rewrite_no_write_sim Impl.REG_job1 Post__Boxes.
               sim_rewrite_with_reg_spec Impl.REG_job1 Post__Input; auto.
             + sim_rewrite_no_write_sim Impl.F1Box.REG_valid0 Post__Step0.
               sim_rewrite_with_reg_spec Impl.F1Box.REG_valid0 Post__Boxes; auto.
             + sim_rewrite_no_write_sim Impl.G1Box.REG_valid0 Post__Step0.
               sim_rewrite_with_reg_spec Impl.G1Box.REG_valid0 Post__Boxes; auto.
         }

      step_sim_oraat_scheduler ImplSched__Step1 SpecSched__Step1 (Spec__UpdateReady tag)
                               ImplSt__UpdateReady SpecSt__UpdateReady Post__UpdateReady
                               ImplSched__UpdateReady SpecSched__UpdateReady ImplWf__UpdateReady SpecWf__UpdateReady.
      2: { constructor; try solve[repeat constructor].
           repeat constructor.
           - sim_rewrite_no_write_sim Impl.REG_clk Post__Step1; auto.
             sim_rewrite_no_write_sim Impl.REG_clk Post__Step0; auto.
             sim_rewrite_no_write_sim Impl.REG_clk Post__Boxes; auto.
             sim_rewrite_no_write_sim Impl.REG_clk Post__Input; auto.
             sim_rewrite_no_write_sim Impl.REG_clk Post__World; auto.
             eapply pf_clk_sim; eauto.
           - destruct tag; simpl.
             + sim_rewrite_no_write_sim Impl.REG_job0' Post__Step1; auto.
               sim_rewrite_with_reg_spec Impl.REG_job0' Post__Step0; auto.
             + sim_rewrite_with_reg_spec Impl.REG_job1' Post__Step1; auto.
           - destruct tag; simpl.
             + sim_rewrite_no_write_sim Impl.REG_ext_output_reg0 Post__Step1; auto.
               sim_rewrite_with_reg_spec Impl.REG_ext_output_reg0 Post__Step0; auto.
             + sim_rewrite_with_reg_spec Impl.REG_ext_output_reg1 Post__Step1; auto.
         }

      simpl in ImplSched__UpdateReady; simpl in SpecSched__UpdateReady; simplify.

      constructor; auto.
      - constructor.
        + intros reg Htaint.
          apply is_taint_reg_equiv in Htaint.
          destruct Htaint as [Hjob | [Hfvalid | Hgvalid]]; subst.
          * destruct tag; simpl.
            { sim_rewrite_no_write_sim Impl.REG_job0 Post__UpdateReady; auto.
              sim_rewrite_no_write_sim Impl.REG_job0 Post__Step1; auto.
              sim_rewrite_with_reg_spec Impl.REG_job0 Post__Step0; auto.
            }
            { sim_rewrite_no_write_sim Impl.REG_job1 Post__UpdateReady; auto.
              sim_rewrite_with_reg_spec Impl.REG_job1 Post__Step1; auto.
            }
          * destruct tag; simpl.
            { sim_rewrite_no_write_sim Impl.F0Box.REG_valid0 Post__UpdateReady; auto.
              sim_rewrite_no_write_sim Impl.F0Box.REG_valid0 Post__Step1; auto.
              sim_rewrite_with_reg_spec Impl.F0Box.REG_valid0 Post__Step0; auto.
            }
            { sim_rewrite_no_write_sim Impl.F1Box.REG_valid0 Post__UpdateReady; auto.
              sim_rewrite_with_reg_spec Impl.F1Box.REG_valid0 Post__Step1; auto.
            }
          * destruct tag; simpl.
            { sim_rewrite_no_write_sim Impl.G0Box.REG_valid0 Post__UpdateReady; auto.
              sim_rewrite_no_write_sim Impl.G0Box.REG_valid0 Post__Step1; auto.
              sim_rewrite_with_reg_spec Impl.G0Box.REG_valid0 Post__Step0; auto.
            }
            { sim_rewrite_no_write_sim Impl.G1Box.REG_valid0 Post__UpdateReady; auto.
              sim_rewrite_with_reg_spec Impl.G1Box.REG_valid0 Post__Step1; auto.
            }
        + sim_rewrite_with_reg_spec Impl.REG_clk Post__UpdateReady; auto.
        + unfold fbox_sim, BoxSimCorrect.box_data_sim; simpl; intros Hvalid reg ; apply Forall_inv in Hvalid; destruct tag; simpl;
            rewrite orb_false_r; repeat rewrite orb_true_iff; intros Hcase;
            destruct Hcase as [Hcase | [Hcase | Hcase]]; simplify; subst;
            match goal with
            | |- (commit_update impl_st _).[?_reg] = (commit_update spec_st _).[?_reg] =>
                sim_rewrite_no_write_sim _reg Post__UpdateReady
            end;
            match type of Hvalid with
            | (commit_update impl_st _).[?_reg] = _ =>
              sim_rewrite_no_write_impl_in Hvalid _reg Post__UpdateReady
            end.
            1-3: match goal with
                 | |- ?X.[?_reg] = ?Y =>
                   sim_rewrite_no_write_sim _reg Post__Step1
                 end;
                 match type of Hvalid with
                 | ?X.[?_reg] = _ =>
                   sim_rewrite_no_write_impl_in Hvalid _reg Post__Step1
                 end; sim_rewrite_with_custom SimCustom__BoxF Post__Step0; simpl BoxSimCorrect.box_valid_regs; auto.
            all: sim_rewrite_with_custom SimCustom__BoxF Post__Step1; simpl BoxSimCorrect.box_valid_regs; auto.
        + unfold gbox_sim, BoxSimCorrect.box_data_sim; simpl; intros Hvalid reg; apply Forall_inv in Hvalid; destruct tag; simpl;
            rewrite orb_false_r; repeat rewrite orb_true_iff; intros Hcase;
            destruct Hcase as [Hcase | [Hcase | Hcase]]; simplify; subst;
            match goal with
            | |- (commit_update impl_st _).[?_reg] = (commit_update spec_st _).[?_reg] =>
                sim_rewrite_no_write_sim _reg Post__UpdateReady
            end;
            match type of Hvalid with
            | (commit_update impl_st _).[?_reg] = _ =>
              sim_rewrite_no_write_impl_in Hvalid _reg Post__UpdateReady
            end.
            1-3: match goal with
                 | |- ?X.[?_reg] = ?Y =>
                   sim_rewrite_no_write_sim _reg Post__Step1
                 end;
                 match type of Hvalid with
                 | ?X.[?_reg] = _ =>
                   sim_rewrite_no_write_impl_in Hvalid _reg Post__Step1
                 end; sim_rewrite_with_custom SimCustom__BoxG Post__Step0; simpl BoxSimCorrect.box_valid_regs; auto.
            all: sim_rewrite_with_custom SimCustom__BoxG Post__Step1; simpl BoxSimCorrect.box_valid_regs; auto.
      - sim_apply_reg_spec Impl.REG_ext_output_reg Post__UpdateReady; auto.
    Qed.
        (* Proof sketch:
           - Precondition:
             + job sim; f0/g0 valid sim; box sim if valid
             + ready for tag job -> ready for job sim /\ input is some and equal
             + sigma is the same except for input
           - World: do nothing
           - Input:
             + case:
                 * if impl ready for job tag, then job tag sim
                 * otherwise, spec input is none so no write to job tag
             + post: job tag sim
           - StepBoxes
             + pre: ftag/gtag valid sim; box sim if valid
             + cases: if impl_valid, then spec_valid; then paths are the same
               * function sim spec: case valid; regs sim if valid -> box sim if valid
             + post: ftag /gtag valid sim; box sim if valid
           - Step0 (assuming tag):
             + pre: job sim; ftag/gtag valid sim; box sim if valid
             + steps:
               * FN_can_send_req: fncall same if valid is same
               * FN_send_req: FN_can_send_req same; input same -> valid same -> box sim
               * FN_can_receive_resp: valid true -> response sim; valid false -> response sim; --> response sim
               * FN_receive_resp: Fn_can_receive_resp sim: valid sim; response sim
               *
             + post: job0 sim; job0' sim; ext_output_reg0 sim; valid -> box sim
           - Step1
             + do nothing on relevant registers
             + pre: job sim; ftag/gtag valid sim; box sim if valid
             + steps:
               * FN_can_send_req: fncall same if valid is same
               * FN_send_req: FN_can_send_req same; input same -> valid same -> box sim
               * FN_can_receive_resp: valid true -> response sim; valid false -> response sim; --> response sim
               * FN_receive_resp: Fn_can_receive_resp sim: valid sim; response sim
               *
             + post: job tag sim; job tag' sim; ext_output_reg sim; valid -> box sim
           - UpdateReady
             + pre: clk sim; job tag sim; job' tag sim; ext_output_reg tag sim; valid sim
             * post: clk -> output_reg sim; clk sim
             + post: clk sim; job sim; box valid sim; box valid -> box sim; clk -> output sim
         *)


End StepSim.

(* TODO: MOVE *)
Lemma SimplifySimPostcondProp:
  forall {custom: Type} (sim: @sim_rule_spec_t custom) ist ist' sst sst' isigma ssigma,
  postcond_to_Prop sim.(rule_spec).(Post) ist ist' isigma  ->
  postcond_to_Prop sim.(rule_spec).(Post) sst sst' ssigma  ->
  Forall (fun '(_, p) => p ist isigma ist' sst ssigma sst')
                              sim.(sim_spec).(SimPost).(SimPost_custom) /\
  Forall (fun '((r1,r2), p) => p ist isigma ist' sst ssigma sst' ist'.[r1] sst'.[r2])
         sim.(sim_spec).(SimPost).(SimPost_regs) ->
  SimPostcondProp sim ist ist' sst sst' isigma ssigma.
Proof.
  intros; constructor; propositional.
Qed.

Module SimProofs : SimProofs_Sig.
  Lemma SimPrecondProp_lookup_reg:
    forall {customProps} (spec: @sim_rule_spec_t customProps) ist sst isigma ssigma prop reg1 reg2,
      SimPrecondProp spec ist sst isigma ssigma ->
      find (fun '((r1,r2), _) => Nat.eqb reg1 r1 && Nat.eqb reg2 r2) spec.(sim_spec).(SimPre).(SimPre_regs) = Some ((reg1,reg2),prop) ->
      prop ist sst ist.[reg1] sst.[reg2].
  Proof.
    intros * HSim Hfind.
    destruct HSim.
    rewrite Forall_forall in SimPre_regSim0.
    apply find_some in Hfind. propositional.
    specialize SimPre_regSim0 with (1 := Hfind0). simplify. rewrite andb_true_iff in Hfind1. propositional; simplify.
  Qed.

  Lemma SimPrecondProp_lookup_custom:
    forall (spec: @sim_rule_spec_t SimCustomProps) ist sst isigma ssigma prop custom,
      SimPrecondProp spec ist sst isigma ssigma ->
      find (fun '(c, _) => SimCustomProps_beq c custom) spec.(sim_spec).(SimPre).(SimPre_custom) = Some (custom,prop) ->
      prop ist isigma sst ssigma.
  Proof.
    intros * HSim Hfind.
    destruct HSim.
    rewrite Forall_forall in SimPre_customSim0.
    apply find_some in Hfind. propositional.
    specialize SimPre_customSim0 with (1 := Hfind0). simplify. auto.
  Qed.

  Ltac pre_sim_rewrite_with_reg_spec reg precond :=
    rewrite (SimPrecondProp_lookup_reg _ _ _ _ _ _ reg reg precond eq_refl).
  Ltac pre_sim_rewrite_with_reg_spec__rev reg precond :=
    rewrite<-(SimPrecondProp_lookup_reg _ _ _ _ _ _ reg reg precond eq_refl).

  Ltac pre_sim_pose_custom_as H custom precond :=
    pose proof (SimPrecondProp_lookup_custom _ _ _ _ _ _ custom precond eq_refl) as H.
  Ltac pre_sim_apply_custom custom precond :=
    apply (SimPrecondProp_lookup_custom _ _ _ _ _ _ custom precond eq_refl).
  Ltac pre_sim_rewrite_custom custom precond :=
    rewrite (SimPrecondProp_lookup_custom _ _ _ _ _ _ custom precond eq_refl).

  Lemma WF_state_length':
    forall (reg_types : reg_types_t) (idx : reg_t) (st : state_t) (n : nat),
      WF_state reg_types st ->
      Typechecking.lookup_reg_type reg_types idx tt = Success n ->
      is_success (r_get_reg st idx) = true -> Datatypes.length st.[idx] = n.
  Proof.
    intros. eapply WF_state_length; eauto. unfold unsafe_get_reg.
    consider r_get_reg; unfold is_success in *; simplify; auto.
  Qed.

  Create HintDb wf_types.
  Hint Immediate WF_state_length' : wf_types.

  Ltac apply_impl_pf impl_st impl_sigma precond pf :=
    match goal with
    | Htype: typecheck_rule _ _ _ _ _ = _,
      Hwf_impl: WF_state _ impl_st,
      Hsigma_impl: WF_ext_sigma _ impl_sigma |- _ =>
        eapply pf in Htype;
          [ | eapply Hwf_impl | eapply Hsigma_impl | auto];
        specialize Htype with (1 := SimPre_impl _ _ _ _ _ precond);
        consider oraat_interp_rule; simpl_match; propositional
    end.

  Ltac start_sim_proof Himpl_fail Hspec_fail RlProof :=
    unfold __sim_oraat_rule_satisfies_spec;
    intros impl_st spec_st impl_sigma spec_sigma Hwf_impl Hwf_spec Hsigma_impl Hsigma_spec Hint_fn_env Htype Hpre;
    unfold oraat_interp_rule;
    destruct oraat_interp_action as (impl_safe, impl_opt) eqn:Horaat_impl;
    destruct (oraat_interp_action spec_sigma) as (spec_safe, spec_opt) eqn:Horaat_spec;
      destruct_match_pairs; simplify_tupless; subst;
    destruct_match; auto; destruct_match; auto;
    intros HWF_impl' Hwf_spec';
    assert_left_as Himpl_fail;
     [ apply_impl_pf impl_st impl_sigma Hpre RlProof  | ];
    assert_left_as Hspec_fail;
     [ apply_impl_pf spec_st spec_sigma Hpre RlProof  | ];
    apply SimplifySimPostcondProp;
    [ apply_impl_pf impl_st impl_sigma Hpre RlProof
    | apply_impl_pf spec_st spec_sigma Hpre RlProof
    | ].

  Lemma SimRlSatisfiesSpec__InteractWithWorld :
    __sim_oraat_rule_satisfies_spec SimRuleSpec__InteractWithWorld (Impl.rules Impl.InteractWithWorld).
  Proof.
    start_sim_proof HImpl_fail Hspec_fail ImplementationProofs.RlSatisfiesSpec__InteractWithWorld.
    repeat constructor.
  Qed.
Ltac prepare_finish :=
  subst; destruct_ands.
  (* let Horaat := fresh in *)
  (* let Hopt := fresh in *)
  (* let Hsuccess := fresh in *)
  (* intros Horaat Hopt; apply simple_tuple_inversion in Horaat; *)
  (* destruct Horaat; subst; *)
  (* apply simple_tuple_inversion in Hopt; *)
  (* destruct Hopt as (Hsuccess & ?); subst; *)
  (* repeat rewrite andb_true_iff in Hsuccess; destruct_ands. *)
Arguments oraat_wp_action : simpl never.
Arguments oraat_interp_action: simpl never.
Arguments struct_fields : simpl never.
Arguments fn_body : simpl never.
Notation "'_oraat_wp_action' '_' '_' '_' '_' st '(' action ')' '[...]' '_' '_' '_' " :=
  (oraat_wp_action _ _ _ _ st action _ _ _ _)
                                             (at level 200, only printing) : wp_notations.
Open Scope wp_notations.

Lemma fbox_sim_preserved:
  forall tag ist ist' sst sst',
  fbox_sim tag ist sst ->
  (forall reg, reg_in_taint_list tag reg
            (map fst Impl.F0Box.reg_tys_list)
            (map fst Impl.F1Box.reg_tys_list) ->
          ist.[reg] = ist'.[reg] /\ sst.[reg] = sst'.[reg]) ->
  fbox_sim tag ist' sst'.
Proof.
  unfold fbox_sim, BoxSimCorrect.box_data_sim, BoxSimCorrect.box_valid_regs, BoxSimCorrect.box_data_regs, fbox, gbox; intros * Hsim Heq Hvalid * Hreg.
  rewrite Forall_single in *.
  destruct tag.
  - pose proof (Heq Impl.F0Box.REG_valid0) as Hvalid'. simpl in Hvalid'. propositional.
    rewrite<-Hvalid'0 in Hvalid. specialize Hsim with (1 := Hvalid); simpl in *.
    specialize Hsim with (1 := Hreg).
    specialize Heq with (1 := Hreg).  propositional.
    congruence.
  - pose proof (Heq Impl.F1Box.REG_valid0) as Hvalid'. simpl in Hvalid'. propositional.
    rewrite<-Hvalid'0 in Hvalid. specialize Hsim with (1 := Hvalid).
    specialize Hsim with (1 := Hreg).
    specialize Heq with (1 := Hreg).  propositional.
    congruence.
Qed.
Lemma gbox_sim_preserved:
  forall tag ist ist' sst sst',
  gbox_sim tag ist sst ->
  (forall reg, reg_in_taint_list tag reg
            (map fst Impl.G0Box.reg_tys_list)
            (map fst Impl.G1Box.reg_tys_list) ->
          ist.[reg] = ist'.[reg] /\ sst.[reg] = sst'.[reg]) ->
  gbox_sim tag ist' sst'.
Proof.
  unfold gbox_sim, BoxSimCorrect.box_data_sim, BoxSimCorrect.box_valid_regs, BoxSimCorrect.box_data_regs, fbox, gbox; intros * Hsim Heq Hvalid * Hreg.
  rewrite Forall_single in *.
  destruct tag.
  - pose proof (Heq Impl.G0Box.REG_valid0) as Hvalid'. simpl in Hvalid'. propositional.
    rewrite<-Hvalid'0 in Hvalid. specialize Hsim with (1 := Hvalid).
    specialize Hsim with (1 := Hreg).
    specialize Heq with (1 := Hreg).  propositional.
    congruence.
  - pose proof (Heq Impl.G1Box.REG_valid0) as Hvalid'. simpl in Hvalid'. propositional.
    rewrite<-Hvalid'0 in Hvalid. specialize Hsim with (1 := Hvalid).
    specialize Hsim with (1 := Hreg).
    specialize Heq with (1 := Hreg).  propositional.
    congruence.
Qed.
Ltac simplify_reg_in_taints_in H :=
  simpl in H; rewrite orb_false_r in H; repeat rewrite orb_true_iff in H;
  repeat rewrite PeanoNat.Nat.eqb_eq in H.

  Definition no_fail_spec (body: action) :=
    {| Function_precond := fun _ _ _ => True;
       Function_taint_set := taint_function_body Impl.int_fn_env body;
       Function_fail_inversion := fun ext_sigma r r_acc varg => False;
       Function_reg_specs := []
    |}.
  Definition function_matches_spec'
    (sigma: ext_sigma_t) (spec: function_spec_t) (fn: int_fn_spec_t) : Prop :=
     function_matches_spec sigma Impl.int_fn_env Impl.struct_env
      (function_spec_to_Prop sigma spec)
      (fn_arg_name fn) (fn_body fn).

  Ltac start_function_proof :=
    unfold function_matches_spec', function_matches_spec;
    intros * Horaat;
    match goal with
    | H: oraat_interp_action _ _ _ ?fuel _ _ _ _ ?action = _ |- _ =>
      set (new_fuel := (safe_fuel Impl.int_fn_env (Datatypes.length Impl.int_fn_env)
                          (action) + fuel));
      apply oraat_interp_action_increase_fuel with (fuel2 := new_fuel) in Horaat; [ | lia];
      let safe := fresh in
      set (safe_fuel _ _ _) as safe in *; compute in safe; subst safe
   end;
   apply function_spec_to_Prop_implies;
   split; [ repeat destruct_match; propositional; eapply taint_safety_function; eauto | ];
   revert Horaat; eapply oraat_wp_action_correct.

  Lemma f0_step_matches_spec:
    forall sigma,
    function_matches_spec' sigma (no_fail_spec Impl.F0Box.FN_step.(fn_body)) Impl.F0Box.FN_step.
  Proof.
    start_function_proof.
    unfold Impl.F0Box.FN_step. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl; try destruct_match); auto; discriminate.
  Qed.

  Lemma f1_step_matches_spec:
    forall sigma,
    function_matches_spec' sigma (no_fail_spec Impl.F1Box.FN_step.(fn_body)) Impl.F1Box.FN_step.
  Proof.
    start_function_proof.
    unfold Impl.F0Box.FN_step. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl; try destruct_match); auto; discriminate.
  Qed.
  Lemma g0_step_matches_spec:
    forall sigma,
    function_matches_spec' sigma (no_fail_spec Impl.G0Box.FN_step.(fn_body)) Impl.G0Box.FN_step.
  Proof.
    start_function_proof.
    unfold Impl.F0Box.FN_step. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl; try destruct_match); auto; discriminate.
  Qed.
  Lemma g1_step_matches_spec:
    forall sigma,
    function_matches_spec' sigma (no_fail_spec Impl.G1Box.FN_step.(fn_body)) Impl.G1Box.FN_step.
  Proof.
    start_function_proof.
    unfold Impl.F0Box.FN_step. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl; try destruct_match); auto; discriminate.
  Qed.

  Opaque __fn_call__.
  Opaque taint_set_to_prop.
Ltac step_no_fail_call fn_proof FnName TaintName :=
    eapply oraat_wp_internal_call'__safe with (2 := eq_refl); [solve_safe | apply fn_proof | ..];
    repeat (repeat step_wp_oraat_safe; simpl);
    destruct_match_as FnName; auto;
    repeat (repeat step_wp_oraat_safe; simpl);
    match goal with
    | |- match ?o with | _ => _ end =>
      destruct o as [[[? ?] ?]  | ] eqn:?; [ | auto]
    end;
    split; [trivial | ];
    let H := fresh in intros TaintName H; inversions H;
    repeat (repeat step_wp_oraat_safe; simpl).
Import BoxSimCorrect.
  (* sigmas can be from static analysis *)
  Ltac start_function_preserves_box_sim :=
    unfold BoxSimCorrect.function_preserves_box_sim;
    intros * Hsigma Horaat1 Horaat2 Hsimr Hsimracc; destruct Hsimr; destruct Hsimracc; simpl in *;
    unfold BoxSimCorrect.box_data_sim in *;
    match type of Horaat1 with
    | oraat_interp_action _ _ _ ?_fuel1 _ _ _ _ ?action = _ =>
        match type of Horaat2 with
        | oraat_interp_action _ _ _ ?_fuel2 _ _ _ _ _ = _ =>
            set (new_fuel := (safe_fuel Impl.int_fn_env (Datatypes.length Impl.int_fn_env)
                                action + _fuel1 + _fuel2));
            apply oraat_interp_action_increase_fuel with (fuel2 := new_fuel) in Horaat1; [ | lia];
            apply oraat_interp_action_increase_fuel with (fuel2 := new_fuel) in Horaat2; [ | lia];
            set (safe_fuel _ _ _) as n in *; compute in n; subst n
        end
    end;
    repeat rewrite Forall_single in *;
    simpl BoxSimCorrect.box_valid_regs in *; simpl BoxSimCorrect.box_data_regs in *.


  Lemma f0_step_preserves_box_sim :
    BoxSimCorrect.function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (fbox Tag0) Impl.F0Box.FN_step [Impl.EXTFN_F0].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).

    assert (Datatypes.length r1.[Impl.F0Box.REG_valid0] = 1).
    { apply is_success_and_length' in Hsafe2; propositional. }

    destruct (bits_eq r1.[Impl.F0Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as Hctr_eq.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim0 by auto. rewrite<-pf_box_data_sim0 by auto.
        rewrite HImplValid; simpl.
        repeat (repeat step_wp_oraat_safe; simpl). simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
        constructor; unfold BoxSimCorrect.box_data_sim; simpl map.
        * intros * Hin; inversions Hin; simplify_updates; auto.
        * intros ? reg Hexists. simpl in Hexists. repeat rewrite orb_true_iff in Hexists.
          split_cases; simplify; simplify_updates; auto.
          rewrite Hsigma. rewrite pf_box_data_sim0 by auto. reflexivity.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim0 by auto. rewrite HImplValid; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_data_sim0 by auto. simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl).  simplify. split; auto.
        constructor; unfold box_data_sim; simpl map; try rewrite Forall_single; auto.
    - apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      rewrite<-pf_box_valid_sim0 by auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
      constructor; unfold box_data_sim; simpl map; try rewrite Forall_single; auto.
  Qed.

  Lemma g0_step_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (gbox Tag0) Impl.G0Box.FN_step [Impl.EXTFN_G0].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).

    assert (Datatypes.length r1.[Impl.G0Box.REG_valid0] = 1).
    { apply is_success_and_length' in Hsafe2; propositional. }

    destruct (bits_eq r1.[Impl.G0Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as Hctr_eq.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim0 by auto. rewrite<-pf_box_data_sim0 by auto.
        rewrite HImplValid; simpl.
        repeat (repeat step_wp_oraat_safe; simpl). simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
        constructor; unfold box_data_sim; simpl map.
        * intros * Hin; inversions Hin; simplify_updates; auto.
        * intros ? reg Hexists. simpl in Hexists. repeat rewrite orb_true_iff in Hexists.
          split_cases; simplify; simplify_updates; auto.
          rewrite Hsigma. rewrite pf_box_data_sim0 by auto. reflexivity.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim0 by auto. rewrite HImplValid; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_data_sim0 by auto. simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl).  simplify. split; auto.
        constructor; unfold box_data_sim; simpl map; try rewrite Forall_single; auto.
    - apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      rewrite<-pf_box_valid_sim0 by auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
      constructor; unfold box_data_sim; simpl map; try rewrite Forall_single; auto.
  Qed.

  Lemma f1_step_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (fbox Tag1) Impl.F1Box.FN_step [Impl.EXTFN_F1].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).

    assert (Datatypes.length r1.[Impl.F1Box.REG_valid0] = 1).
    { apply is_success_and_length' in Hsafe2; propositional. }

    destruct (bits_eq r1.[Impl.F1Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as Hctr_eq.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim0 by auto. rewrite<-pf_box_data_sim0 by auto.
        rewrite HImplValid; simpl.
        repeat (repeat step_wp_oraat_safe; simpl). simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
        constructor; unfold box_data_sim; simpl map; try rewrite Forall_single; simplify_updates; auto.
        * intros * Hin; inversions Hin; simplify_updates; auto.
        * intros ? reg Hexists. simpl in Hexists. repeat rewrite orb_true_iff in Hexists.
          split_cases; simplify; simplify_updates; auto.
          rewrite Hsigma. rewrite pf_box_data_sim0 by auto. reflexivity.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim0 by auto. rewrite HImplValid; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_data_sim0 by auto. simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl).  simplify. split; auto.
        constructor; unfold box_data_sim; simpl map; try rewrite Forall_single; auto.
    - apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      rewrite<-pf_box_valid_sim0 by auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
      constructor; unfold box_data_sim; simpl map; try rewrite Forall_single; auto.
  Qed.

  Lemma g1_step_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (gbox Tag1) Impl.G1Box.FN_step [Impl.EXTFN_G1].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).

    assert (Datatypes.length r1.[Impl.G1Box.REG_valid0] = 1).
    { apply is_success_and_length' in Hsafe2; propositional. }

    destruct (bits_eq r1.[Impl.G1Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as Hctr_eq.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim0 by auto. rewrite<-pf_box_data_sim0 by auto.
        rewrite HImplValid; simpl.
        repeat (repeat step_wp_oraat_safe; simpl). simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
        constructor; unfold box_data_sim; simpl map; try rewrite Forall_single; simplify_updates; auto.
        * intros * Hin; inversions Hin; simplify_updates; auto.
        * intros ? reg Hexists. simpl in Hexists. repeat rewrite orb_true_iff in Hexists.
          split_cases; simplify; simplify_updates; auto.
          rewrite Hsigma. rewrite pf_box_data_sim0 by auto. reflexivity.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim0 by auto. rewrite HImplValid; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_data_sim0 by auto. simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl).  simplify. split; auto.
        constructor; unfold box_data_sim; simpl map; try rewrite Forall_single; auto.
    - apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      rewrite<-pf_box_valid_sim0 by auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
      constructor; unfold box_data_sim; simpl map; try rewrite Forall_single; auto.
  Qed.

  Lemma f0_can_receive_resp_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (fbox Tag0) Impl.F0Box.FN_can_receive_resp [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.F0Box.REG_valid0] = 1).
    { apply is_success_and_length in Hsafe1; simpl in *; propositional. }
    destruct (bits_eq r_acc1.[Impl.F0Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid; propositional. simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      rewrite<-pf_box_valid_sim1 by auto. rewrite<-pf_box_data_sim1 by auto. split; auto.
      constructor; simpl map; unfold box_data_sim; auto.
    - simplify. apply single_bit_negate in HImplValid; auto. rewrite HImplValid.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      rewrite<-pf_box_valid_sim1 by auto.  rewrite HImplValid; simpl. split; auto.
      constructor; simpl map; unfold box_data_sim; simpl box_data_regs; simpl box_valid_regs; auto.
  Qed.

  Lemma f1_can_receive_resp_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (fbox Tag1) Impl.F1Box.FN_can_receive_resp [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.F1Box.REG_valid0] = 1).
    { apply is_success_and_length in Hsafe1; simpl in *; propositional. }
    destruct (bits_eq r_acc1.[Impl.F1Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid; propositional. simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      rewrite<-pf_box_valid_sim1 by auto. rewrite<-pf_box_data_sim1 by auto. split; auto.
      constructor; simpl map; unfold box_data_sim; auto.
    - simplify. apply single_bit_negate in HImplValid; auto. rewrite HImplValid.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      rewrite<-pf_box_valid_sim1 by auto.  rewrite HImplValid; simpl. split; auto.
      constructor; simpl map; unfold box_data_sim; simpl box_data_regs; simpl box_valid_regs; auto.
  Qed.

  Lemma g0_can_receive_resp_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (gbox Tag0) Impl.G0Box.FN_can_receive_resp [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.G0Box.REG_valid0] = 1).
    { apply is_success_and_length in Hsafe1; simpl in *; propositional. }
    destruct (bits_eq r_acc1.[Impl.G0Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid; propositional. simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      rewrite<-pf_box_valid_sim1 by auto. rewrite<-pf_box_data_sim1 by auto. split; auto.
      constructor; simpl map; unfold box_data_sim; auto.
    - simplify. apply single_bit_negate in HImplValid; auto. rewrite HImplValid.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      rewrite<-pf_box_valid_sim1 by auto.  rewrite HImplValid; simpl. split; auto.
      constructor; simpl map; unfold box_data_sim; simpl box_data_regs; simpl box_valid_regs; auto.
  Qed.



  Lemma g1_can_receive_resp_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (gbox Tag1) Impl.G1Box.FN_can_receive_resp [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.G1Box.REG_valid0] = 1).
    { apply is_success_and_length in Hsafe1; simpl in *; propositional. }
    destruct (bits_eq r_acc1.[Impl.G1Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid; propositional. simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      rewrite<-pf_box_valid_sim1 by auto. rewrite<-pf_box_data_sim1 by auto. split; auto.
      constructor; simpl map; unfold box_data_sim; auto.
    - simplify. apply single_bit_negate in HImplValid; auto. rewrite HImplValid.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify.
      rewrite<-pf_box_valid_sim1 by auto.  rewrite HImplValid; simpl. split; auto.
      constructor; simpl map; unfold box_data_sim; simpl box_data_regs; simpl box_valid_regs; auto.
  Qed.


  Lemma f0_send_req_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (fbox Tag0) Impl.F0Box.FN_send_req [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    apply oraat_wp_internal_call__safe; [solve_safe | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.F0Box.REG_valid0] = 1).
    { unfold neg in Hsafe0. repeat rewrite map_length in Hsafe0. auto. }
    destruct (bits_eq r_acc1.[Impl.F0Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl). discriminate.
    - repeat (repeat step_wp_oraat_safe; simpl).
      apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl); simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      apply oraat_wp_internal_call__safe; [solve_safe | ].
      repeat (repeat step_wp_oraat_safe; simpl).
      unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      rewrite<-pf_box_valid_sim1 by auto. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
      constructor; simpl map; unfold box_data_sim; try rewrite Forall_single; simplify_updates; auto.
      * intros * Hin; inversions Hin; simplify_updates; auto.
      * intros ? reg Hexists. simpl in Hexists. repeat rewrite orb_true_iff in Hexists.
        split_cases; simplify; simplify_updates; auto.
  Qed.

  Lemma f1_send_req_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (fbox Tag1) Impl.F1Box.FN_send_req [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    apply oraat_wp_internal_call__safe; [solve_safe | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.F1Box.REG_valid0] = 1).
    { unfold neg in Hsafe0. repeat rewrite map_length in Hsafe0. auto. }
    destruct (bits_eq r_acc1.[Impl.F1Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl). discriminate.
    - repeat (repeat step_wp_oraat_safe; simpl).
      apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl); simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      apply oraat_wp_internal_call__safe; [solve_safe | ].
      repeat (repeat step_wp_oraat_safe; simpl).
      unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      rewrite<-pf_box_valid_sim1 by auto. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
      constructor; simpl map; unfold box_data_sim; try rewrite Forall_single; simplify_updates; auto.
      * intros * Hin; inversions Hin; simplify_updates; auto.
      * intros ? reg Hexists. simpl in Hexists. repeat rewrite orb_true_iff in Hexists.
        split_cases; simplify; simplify_updates; auto.
  Qed.

  Lemma g0_send_req_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (gbox Tag0) Impl.G0Box.FN_send_req [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    apply oraat_wp_internal_call__safe; [solve_safe | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.G0Box.REG_valid0] = 1).
    { unfold neg in Hsafe0. repeat rewrite map_length in Hsafe0. auto. }
    destruct (bits_eq r_acc1.[Impl.G0Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl). discriminate.
    - repeat (repeat step_wp_oraat_safe; simpl).
      apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl); simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      apply oraat_wp_internal_call__safe; [solve_safe | ].
      repeat (repeat step_wp_oraat_safe; simpl).
      unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      rewrite<-pf_box_valid_sim1 by auto. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
      constructor; simpl map; unfold box_data_sim; try rewrite Forall_single; simplify_updates; auto.
      * intros * Hin; inversions Hin; simplify_updates; auto.
      * intros ? reg Hexists. simpl in Hexists. repeat rewrite orb_true_iff in Hexists.
        split_cases; simplify; simplify_updates; auto.
  Qed.

  Lemma g1_send_req_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (gbox Tag1) Impl.G1Box.FN_send_req [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    apply oraat_wp_internal_call__safe; [solve_safe | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.G1Box.REG_valid0] = 1).
    { unfold neg in Hsafe0. repeat rewrite map_length in Hsafe0. auto. }
    destruct (bits_eq r_acc1.[Impl.G1Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl). discriminate.
    - repeat (repeat step_wp_oraat_safe; simpl).
      apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl); simplify.
      revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      apply oraat_wp_internal_call__safe; [solve_safe | ].
      repeat (repeat step_wp_oraat_safe; simpl).
      unfold fn_body; simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      rewrite<-pf_box_valid_sim1 by auto. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl). simplify. split; auto.
      constructor; simpl map; unfold box_data_sim; try rewrite Forall_single; simplify_updates; auto.
      * intros * Hin; inversions Hin; simplify_updates; auto.
      * intros ? reg Hexists. simpl in Hexists. repeat rewrite orb_true_iff in Hexists.
        split_cases; simplify; simplify_updates; auto.
  Qed.


Ltac custom_simplify_updates_in_term V ::=
  match V with
  | success_or_default (subst_field _ _ ?V1 ?V2) _ =>
      simplify_updates_in_term V1 || simplify_updates_in_term V2
  end.

  Lemma f0_receive_resp_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (fbox Tag0) Impl.F0Box.FN_receive_resp [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    apply oraat_wp_internal_call__safe; [solve_safe | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.F0Box.REG_valid0] = 1).
    { unfold neg in Hsafe2. repeat rewrite map_length in Hsafe2.
      apply is_success_and_length' in Hsafe2; propositional. }

    destruct (bits_eq r_acc1.[Impl.F0Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as Hcase.
      + repeat (repeat step_wp_oraat_safe; simpl). discriminate.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        apply oraat_wp_internal_call__safe; [solve_safe | ].
        repeat (repeat step_wp_oraat_safe; simpl). unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim1 by auto. rewrite HImplValid; simpl. rewrite<-pf_box_data_sim1 by auto.
        rewrite Hcase.
        repeat (repeat step_wp_oraat_safe; simpl).  simplify.
        split; [simplify_updates; auto| ].
        * rewrite<-pf_box_data_sim1 by auto. auto.
        * constructor; unfold box_data_sim; simpl box_valid_regs; simpl box_data_regs;
            simpl map; simplify_updates.
          { intros * Hin; inversions Hin; simplify_updates; auto. }
          { rewrite Forall_single. simplify_updates. discriminate. }
    - apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). discriminate.
  Qed.

  Lemma f1_receive_resp_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (fbox Tag1) Impl.F1Box.FN_receive_resp [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    apply oraat_wp_internal_call__safe; [solve_safe | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.F1Box.REG_valid0] = 1).
    { unfold neg in Hsafe2. repeat rewrite map_length in Hsafe2.
      apply is_success_and_length' in Hsafe2; propositional. }

    destruct (bits_eq r_acc1.[Impl.F1Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as Hcase.
      + repeat (repeat step_wp_oraat_safe; simpl). discriminate.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        apply oraat_wp_internal_call__safe; [solve_safe | ].
        repeat (repeat step_wp_oraat_safe; simpl). unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim1 by auto. rewrite HImplValid; simpl. rewrite<-pf_box_data_sim1 by auto.
        rewrite Hcase.
        repeat (repeat step_wp_oraat_safe; simpl).  simplify.
        split; [simplify_updates; auto| ].
        * rewrite<-pf_box_data_sim1 by auto. auto.
        * constructor; unfold box_data_sim; simpl box_valid_regs; simpl box_data_regs;
            simpl map; simplify_updates.
          { intros * Hin; inversions Hin; simplify_updates; auto. }
          { rewrite Forall_single. simplify_updates. discriminate. }
    - apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). discriminate.
  Qed.

  Lemma g0_receive_resp_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (gbox Tag0) Impl.G0Box.FN_receive_resp [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    apply oraat_wp_internal_call__safe; [solve_safe | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.G0Box.REG_valid0] = 1).
    { unfold neg in Hsafe2. repeat rewrite map_length in Hsafe2.
      apply is_success_and_length' in Hsafe2; propositional. }

    destruct (bits_eq r_acc1.[Impl.G0Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as Hcase.
      + repeat (repeat step_wp_oraat_safe; simpl). discriminate.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        apply oraat_wp_internal_call__safe; [solve_safe | ].
        repeat (repeat step_wp_oraat_safe; simpl). unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim1 by auto. rewrite HImplValid; simpl. rewrite<-pf_box_data_sim1 by auto.
        rewrite Hcase.
        repeat (repeat step_wp_oraat_safe; simpl).  simplify.
        split; [simplify_updates; auto| ].
        * rewrite<-pf_box_data_sim1 by auto. auto.
        * constructor; unfold box_data_sim; simpl box_valid_regs; simpl box_data_regs;
            simpl map; simplify_updates.
          { intros * Hin; inversions Hin; simplify_updates; auto. }
          { rewrite Forall_single. simplify_updates. discriminate. }
    - apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). discriminate.
  Qed.

  Lemma g1_receive_resp_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env
      (gbox Tag1) Impl.G1Box.FN_receive_resp [].
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    apply oraat_wp_internal_call__safe; [solve_safe | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl).
    assert (Datatypes.length r_acc1.[Impl.G1Box.REG_valid0] = 1).
    { unfold neg in Hsafe2. repeat rewrite map_length in Hsafe2.
      apply is_success_and_length' in Hsafe2; propositional. }

    destruct (bits_eq r_acc1.[Impl.G1Box.REG_valid0] Ob~1) eqn:HImplValid.
    - apply bits_eq_iff in HImplValid. rewrite HImplValid. simpl.
      repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as Hcase.
      + repeat (repeat step_wp_oraat_safe; simpl). discriminate.
      + repeat (repeat step_wp_oraat_safe; simpl). simplify.
        revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        apply oraat_wp_internal_call__safe; [solve_safe | ].
        repeat (repeat step_wp_oraat_safe; simpl). unfold fn_body; simpl.
        repeat (repeat step_wp_oraat_safe; simpl).
        rewrite<-pf_box_valid_sim1 by auto. rewrite HImplValid; simpl. rewrite<-pf_box_data_sim1 by auto.
        rewrite Hcase.
        repeat (repeat step_wp_oraat_safe; simpl).  simplify.
        split; [simplify_updates; auto| ].
        * rewrite<-pf_box_data_sim1 by auto. auto.
        * constructor; unfold box_data_sim; simpl box_valid_regs; simpl box_data_regs;
            simpl map; simplify_updates.
          { intros * Hin; inversions Hin; simplify_updates; auto. }
          { rewrite Forall_single. simplify_updates. discriminate. }
    - apply single_bit_negate in HImplValid; auto. rewrite HImplValid; simpl.
      repeat (repeat step_wp_oraat_safe; simpl). discriminate.
  Qed.

Lemma taint_set_to_prop_no_write_Forall_in_list:
  forall res_taint_set st1 st2 reg_list,
  taint_set_to_prop st1 st2 res_taint_set ->
  forallb (fun r => no_writes_in_taint_set res_taint_set r) reg_list = true ->
  Forall (fun r => st1.[r] = st2.[r]) reg_list.
Proof.
 intros.
 apply Forall_forall.
 rewrite forallb_forall in H0. intros. specialize H0 with (1 := H1).
 rewrite taint_set_to_prop_no_write' with (1 := H); auto.
Qed.

Lemma box_sim_preserved_no_writes_l:
  forall box st1 st1' st2 taint_set,
  box_sim box st1 st2 ->
  taint_set_to_prop st1 st1' taint_set ->
  forallb (fun r => no_writes_in_taint_set taint_set r) box.(box_data_regs)= true  ->
  forallb (fun r => no_writes_in_taint_set taint_set r) (map fst box.(box_valid_regs)) = true ->
  box_sim box st1' st2.
Proof.
  intros * Hsim Hprop Hno_write_reg Hno_write_valid.
  assert (Forall (fun r => st1.[r] = st1'.[r]) (map fst box.(box_valid_regs))) as Hvalid_eq.
  { eapply taint_set_to_prop_no_write_Forall_in_list; eauto. }
  assert (Forall (fun r => st1.[r] = st1'.[r]) box.(box_data_regs)) as Hregs_eq.
  { eapply taint_set_to_prop_no_write_Forall_in_list; eauto. }
  rewrite Forall_forall in Hvalid_eq.
  rewrite Forall_forall in Hregs_eq.

  destruct Hsim. constructor.
  - intros * HIn. destruct_match_pairs; subst.
    specialize Hvalid_eq with (1 := HIn). simpl in *. rewrite<-Hvalid_eq. auto.
  - unfold box_data_sim in *. intros. rewrite Forall_forall in H.
    assert_pre_and_specialize pf_box_data_sim0.
    { rewrite Forall_forall. intros; destruct_match_pairs; subst.
      specialize H with (1 := H1). destruct_match_pairs; simplify.
      apply in_map with (f := fst) in H1. auto.
    }
    { rewrite<-pf_box_data_sim0 by auto.
      rewrite existsb_exists in H0. propositional; simplify. rewrite<-Hregs_eq by auto. reflexivity.
    }
Qed.

Lemma box_sim_preserved_no_writes_r:
  forall box st1 st2' st2 taint_set,
  box_sim box st1 st2 ->
  taint_set_to_prop st2 st2' taint_set ->
  forallb (fun r => no_writes_in_taint_set taint_set r) box.(box_data_regs)= true  ->
  forallb (fun r => no_writes_in_taint_set taint_set r) (map fst box.(box_valid_regs)) = true ->
  box_sim box st1 st2'.
Proof.
  intros * Hsim Hprop Hno_write_reg Hno_write_valid.
  assert (Forall (fun r => st2.[r] = st2'.[r]) (map fst box.(box_valid_regs))) as Hvalid_eq.
  { eapply taint_set_to_prop_no_write_Forall_in_list; eauto. }
  assert (Forall (fun r => st2.[r] = st2'.[r]) box.(box_data_regs)) as Hregs_eq.
  { eapply taint_set_to_prop_no_write_Forall_in_list; eauto. }
  rewrite Forall_forall in Hvalid_eq.
  rewrite Forall_forall in Hregs_eq.

  destruct Hsim. constructor.
  - intros * HIn. destruct_match_pairs; subst.
    specialize Hvalid_eq with (1 := HIn). simpl in *. rewrite<-Hvalid_eq. auto.
  - unfold box_data_sim in *. intros. rewrite Forall_forall in H.
    assert_pre_and_specialize pf_box_data_sim0.
    { rewrite Forall_forall. intros; destruct_match_pairs; subst.
      specialize H with (1 := H1). destruct_match_pairs; simplify.
      apply in_map with (f := fst) in H1. auto.
    }
    { rewrite pf_box_data_sim0 by auto.
      rewrite existsb_exists in H0. propositional; simplify. rewrite<-Hregs_eq by auto. reflexivity.
    }
Qed.

(* TODO: do properly: lockstep semantics *)
  Lemma SimRlSatisfiesSpec__StepBoxesTag0 :
    __sim_oraat_rule_satisfies_spec (SimRuleSpec__StepBoxes Tag0) (Impl.rules Impl.StepBoxes).
  Proof.
    start_sim_proof Himpl_fail Hspec_fail ImplementationProofs.RlSatisfiesSpec__StepBoxes.
    set (match impl_opt with | Some (_, st', _) => st' | None => impl_st end) as impl_st' in *.
    set (match spec_opt with | Some (_, st', _) => st' | None => spec_st end) as spec_st' in *.

    (* revert Heqp0. revert Horaat_spec. *)
    revert Horaat_impl.
    unfold Impl.rules, Impl.step_boxes.
    set (safe_fuel _ _ _ ) as fuel in *. compute in fuel. subst fuel.
    eapply oraat_wp_action_correct.
    repeat (repeat step_wp_oraat_safe; simpl).

    step_no_fail_call f0_step_matches_spec ImplCall_F0Box_FN_step ImplHtaint__F0Box_Fn_step.
    step_no_fail_call f1_step_matches_spec ImplCall_F1Box_FN_step ImplHtaint__F1Box_Fn_step.
    step_no_fail_call g0_step_matches_spec ImplCall_G0Box_FN_step ImplHtaint__G0Box_Fn_step.
    step_no_fail_call g1_step_matches_spec ImplCall_G1Box_FN_step ImplHtaint__G1Box_Fn_step.
    prepare_finish.

    revert Horaat_spec.
    unfold Impl.rules, Impl.step_boxes.
    eapply oraat_wp_action_correct.
    repeat (repeat step_wp_oraat_safe; simpl).
    step_no_fail_call f0_step_matches_spec SpecCall_F0Box_FN_step SpecHtaint__F0Box_Fn_step.
    step_no_fail_call f1_step_matches_spec SpecCall_F1Box_FN_step SpecHtaint__F1Box_Fn_step.
    step_no_fail_call g0_step_matches_spec SpecCall_G0Box_FN_step SpecHtaint__G0Box_Fn_step.
    step_no_fail_call g1_step_matches_spec SpecCall_G1Box_FN_step SpecHtaint__G1Box_Fn_step.
    prepare_finish.
    repeat (rewrite Forall_cons_iff; try rewrite Forall_single); unfold fbox_sim, gbox_sim; simpl.

    assert (box_sim (fbox Tag0) impl_st spec_st) as HF0sim0.
    { clear - Hpre. destruct Hpre; simpl in *.
      repeat (rewrite Forall_cons_iff in *; try rewrite Forall_single in *); unfold fbox_sim, gbox_sim, fbox; simpl.
      constructor; simpl; propositional; simplify; auto.
    }
    assert (box_sim (gbox Tag0) impl_st spec_st) as HG0sim0.
    { clear - Hpre. destruct Hpre; simpl in *.
      repeat (rewrite Forall_cons_iff in *; try rewrite Forall_single in *); unfold fbox_sim, gbox_sim; simpl.
      constructor; simpl; propositional; simplify; auto.
    }

    assert (box_sim (fbox Tag0) impl_st' spec_st') as HFsim.
    { do 3 (eapply box_sim_preserved_no_writes_l; eauto; eapply box_sim_preserved_no_writes_r; eauto).
      eapply f0_step_preserves_box_sim with (2 := ImplCall_F0Box_FN_step) (3 := SpecCall_F0Box_FN_step); eauto.
      apply Forall_single. intros.  pre_sim_apply_custom SimSigmaF Hpre; reflexivity.
    }
    assert (box_sim (gbox Tag0) impl_st' spec_st') as HGsim.
    { do 1 (eapply box_sim_preserved_no_writes_l; eauto; eapply box_sim_preserved_no_writes_r; eauto).
      eapply g0_step_preserves_box_sim with (2 := ImplCall_G0Box_FN_step) (3 := SpecCall_G0Box_FN_step); eauto.
      { apply Forall_single. intros.  pre_sim_apply_custom SimSigmaG Hpre; reflexivity. }
      do 2 (eapply box_sim_preserved_no_writes_l; eauto; eapply box_sim_preserved_no_writes_r; eauto).
    }

    destruct HFsim; destruct HGsim; propositional.
    simpl in pf_box_valid_sim0, pf_box_valid_sim1.
    split; auto.
  Qed.

  Lemma SimRlSatisfiesSpec__StepBoxesTag1 :
    __sim_oraat_rule_satisfies_spec (SimRuleSpec__StepBoxes Tag1) (Impl.rules Impl.StepBoxes).
  Proof.
    start_sim_proof Himpl_fail Hspec_fail ImplementationProofs.RlSatisfiesSpec__StepBoxes.
    set (match impl_opt with | Some (_, st', _) => st' | None => impl_st end) as impl_st' in *.
    set (match spec_opt with | Some (_, st', _) => st' | None => spec_st end) as spec_st' in *.
    (* revert Heqp0. revert Horaat_spec. *)
    revert Horaat_impl.
    unfold Impl.rules, Impl.step_boxes.
    set (safe_fuel _ _ _ ) as fuel in *. compute in fuel. subst fuel.
    eapply oraat_wp_action_correct.
    repeat (repeat step_wp_oraat_safe; simpl).

    step_no_fail_call f0_step_matches_spec ImplCall_F0Box_FN_step ImplHtaint__F0Box_Fn_step.
    step_no_fail_call f1_step_matches_spec ImplCall_F1Box_FN_step ImplHtaint__F1Box_Fn_step.
    step_no_fail_call g0_step_matches_spec ImplCall_G0Box_FN_step ImplHtaint__G0Box_Fn_step.
    step_no_fail_call g1_step_matches_spec ImplCall_G1Box_FN_step ImplHtaint__G1Box_Fn_step.
    prepare_finish.

    revert Horaat_spec.
    unfold Impl.rules, Impl.step_boxes.
    eapply oraat_wp_action_correct.
    repeat (repeat step_wp_oraat_safe; simpl).
    step_no_fail_call f0_step_matches_spec SpecCall_F0Box_FN_step SpecHtaint__F0Box_Fn_step.
    step_no_fail_call f1_step_matches_spec SpecCall_F1Box_FN_step SpecHtaint__F1Box_Fn_step.
    step_no_fail_call g0_step_matches_spec SpecCall_G0Box_FN_step SpecHtaint__G0Box_Fn_step.
    step_no_fail_call g1_step_matches_spec SpecCall_G1Box_FN_step SpecHtaint__G1Box_Fn_step.
    prepare_finish.
    repeat (rewrite Forall_cons_iff; try rewrite Forall_single); unfold fbox_sim, gbox_sim; simpl.

    assert (box_sim (fbox Tag1) impl_st spec_st) as HF1sim0.
    { clear - Hpre. destruct Hpre; simpl in *.
      repeat (rewrite Forall_cons_iff in *; try rewrite Forall_single in *); unfold fbox_sim, gbox_sim; simpl.
      constructor; simpl; propositional; simplify; auto.
    }
    assert (box_sim (gbox Tag1) impl_st spec_st) as HG1sim0.
    { clear - Hpre. destruct Hpre; simpl in *.
      repeat (rewrite Forall_cons_iff in *; try rewrite Forall_single in *); unfold fbox_sim, gbox_sim; simpl.
      constructor; simpl; propositional; simplify; auto.
    }

    assert (box_sim (fbox Tag1) impl_st' spec_st') as HFsim.
    { do 2 (eapply box_sim_preserved_no_writes_l; eauto; eapply box_sim_preserved_no_writes_r; eauto).
      eapply f1_step_preserves_box_sim with (2 := ImplCall_F1Box_FN_step) (3 := SpecCall_F1Box_FN_step); eauto.
      { apply Forall_single. intros.  pre_sim_apply_custom SimSigmaF Hpre; reflexivity. }
      repeat (eapply box_sim_preserved_no_writes_l; eauto; eapply box_sim_preserved_no_writes_r; eauto).
    }
    assert (box_sim (gbox Tag1) impl_st' spec_st') as HGsim.
    { eapply g1_step_preserves_box_sim with (2 := ImplCall_G1Box_FN_step) (3 := SpecCall_G1Box_FN_step); eauto.
      { apply Forall_single. intros.  pre_sim_apply_custom SimSigmaG Hpre. reflexivity. }
      repeat (eapply box_sim_preserved_no_writes_l; eauto; eapply box_sim_preserved_no_writes_r; eauto).
    }
    destruct HFsim; destruct HGsim; propositional.
    simpl in pf_box_valid_sim0, pf_box_valid_sim1.
    split; auto.

  Qed.


  Lemma SimRlSatisfiesSpec__StepBoxes :
    forall tag, __sim_oraat_rule_satisfies_spec (SimRuleSpec__StepBoxes tag) (Impl.rules Impl.StepBoxes).
  Proof.
    destruct tag.
    - apply SimRlSatisfiesSpec__StepBoxesTag0.
    - apply SimRlSatisfiesSpec__StepBoxesTag1.
  Qed.

  Definition mk_sim_regs (regs: list reg_t) : SortedRegEnv.EnvT bool :=
    List.fold_left (fun acc r => SortedRegEnv.update acc r (fun _ => true) true)
      regs SortedRegEnv.empty.

  Definition step_sim0_regs :=
    mk_sim_regs [Impl.REG_clk; job_reg Tag0].
  Definition step_sim1_regs :=
    mk_sim_regs [Impl.REG_clk; job_reg Tag1].

  Lemma reg_sim_state_prop_implied:
    forall regs st1 st2,
      Forall (fun r => st1.[r] = st2.[r]) regs ->
      reg_sim_state_prop (mk_sim_regs regs) st1 st2.
  Proof.
    unfold reg_sim_state_prop, mk_sim_regs.
    induction regs using rev_ind; [discriminate | ].
    intros * Hforall reg Heq. apply Forall_app in Hforall. propositional. rewrite Forall_single in Hforall1.
    rewrite fold_left_app in Heq. simpl in Heq.
    destruct_with_eqn (Nat.eqb x reg); simplify; auto.
    rewrite SortedRegEnv.update_correct_neq in Heq by auto.
    auto.
  Qed.

  Lemma f0_can_send_req_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env (fbox Tag0) Impl.F0Box.FN_can_send_req Ob.
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl). simplify.
    revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl). simplify.
    split; auto.
    + repeat rewrite unsafe_get_reg_success_or_default.
      rewrite pf_box_valid_sim1 by auto. reflexivity.
    + constructor; unfold BoxSimCorrect.box_data_sim; simpl map; auto.
  Qed.

  Lemma g0_can_send_req_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env (gbox Tag0) Impl.G0Box.FN_can_send_req Ob.
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl). simplify.
    revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl). simplify.
    split; auto.
    + repeat rewrite unsafe_get_reg_success_or_default.
      rewrite pf_box_valid_sim1 by auto. reflexivity.
    + constructor; unfold BoxSimCorrect.box_data_sim; simpl map; auto.
  Qed.
  Lemma f1_can_send_req_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env (fbox Tag1) Impl.F1Box.FN_can_send_req Ob.
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl). simplify.
    revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl). simplify.
    split; auto.
    + repeat rewrite unsafe_get_reg_success_or_default.
      rewrite pf_box_valid_sim1 by auto. reflexivity.
    + constructor; unfold BoxSimCorrect.box_data_sim; simpl map; auto.
  Qed.

  Lemma g1_can_send_req_preserves_box_sim :
    function_preserves_box_sim Impl.int_fn_env Impl.struct_env (gbox Tag1) Impl.G1Box.FN_can_send_req Ob.
  Proof.
    start_function_preserves_box_sim.
    revert Horaat1. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl). simplify.
    revert Horaat2. eapply oraat_wp_action_correct. unfold fn_body; simpl.
    repeat (repeat step_wp_oraat_safe; simpl). simplify.
    split; auto.
    + repeat rewrite unsafe_get_reg_success_or_default.
      rewrite pf_box_valid_sim1 by auto. reflexivity.
    + constructor; unfold BoxSimCorrect.box_data_sim; simpl map; auto.
  Qed.



  Create HintDb function_preserves_hints.
  Hint Resolve f0_can_send_req_preserves_box_sim : function_preserves_hints.
  Hint Resolve f1_can_send_req_preserves_box_sim : function_preserves_hints.
  Hint Resolve g0_can_send_req_preserves_box_sim : function_preserves_hints.
  Hint Resolve g1_can_send_req_preserves_box_sim : function_preserves_hints.
  Hint Resolve f0_step_preserves_box_sim :function_preserves_hints.
  Hint Resolve f1_step_preserves_box_sim :function_preserves_hints.
  Hint Resolve g0_step_preserves_box_sim :function_preserves_hints.
  Hint Resolve g1_step_preserves_box_sim :function_preserves_hints.
  Hint Resolve f0_can_receive_resp_preserves_box_sim :function_preserves_hints.
  Hint Resolve f1_can_receive_resp_preserves_box_sim :function_preserves_hints.
  Hint Resolve g0_can_receive_resp_preserves_box_sim :function_preserves_hints.
  Hint Resolve g1_can_receive_resp_preserves_box_sim :function_preserves_hints.
  Hint Resolve f0_send_req_preserves_box_sim :function_preserves_hints.
  Hint Resolve f1_send_req_preserves_box_sim :function_preserves_hints.
  Hint Resolve g0_send_req_preserves_box_sim :function_preserves_hints.
  Hint Resolve g1_send_req_preserves_box_sim :function_preserves_hints.
  Hint Resolve f0_receive_resp_preserves_box_sim :function_preserves_hints.
  Hint Resolve f1_receive_resp_preserves_box_sim :function_preserves_hints.
  Hint Resolve g0_receive_resp_preserves_box_sim :function_preserves_hints.
  Hint Resolve g1_receive_resp_preserves_box_sim :function_preserves_hints.

  Lemma box_fns_preserve_boxes:
    box_fn_preserves_prop Impl.int_fn_env Impl.struct_env box_t boxes box_fns.
  Proof.
    unfold box_fn_preserves_prop.
    repeat match goal with
    | |- Forall _ _ => constructor; simpl
    | |- action_writes_regs_only _ _ _ =>
        apply compute_action_writes_regs_only_correct; reflexivity
    | |- _ /\ _ => split_ands_in_goal
    end; auto with function_preserves_hints.
  Qed.

  Lemma pf_WF_boxes: WF_boxes boxes.
  Proof.
    eapply computable_WF_boxes_correct.
    reflexivity.
  Qed.

 Lemma SimRlSatisfiesSpec__DoStep0__Tag0 :
    __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoStep0 Tag0) (Impl.rules Impl.DoStep0).
  Proof.
    start_sim_proof Himpl_fail Hspec_fail ImplementationProofs.RlSatisfiesSpec__DoStep0.
    simpl in Himpl_fail. simpl in Hspec_fail. simplify.
    rename s0 into impl_st'. rename s into spec_st'.

    specialize box_sim_analyze_rule_correct with
      (1 := Horaat_impl) (2 := Horaat_spec)
      (box_t_eq_dec := EqDec_box_t) (box_defs := boxes)
      (box_fns := box_fns) (ext_fn_sims := []) (reg_sims := step_sim0_regs) (box_sims := [FBox Tag0; GBox Tag0])
      (9 := eq_refl).
    intros Hbox_sim.
    assert_pre_and_specialize Hbox_sim.
    { apply reg_sim_state_prop_implied; simpl.
      repeat constructor.
      - pre_sim_rewrite_with_reg_spec Impl.REG_clk Hpre. auto.
      - pre_sim_rewrite_with_reg_spec Impl.REG_job0 Hpre. auto.
    }
    assert_pre_and_specialize Hbox_sim.
    { unfold box_sim_state_prop. constructor; [| constructor; [ | constructor]]; simpl;
      clear - Hpre; destruct Hpre; simpl in *;
      repeat (rewrite Forall_cons_iff in *; try rewrite Forall_single in *); unfold fbox_sim, gbox_sim; simpl;
      constructor; simpl; propositional; simplify; auto.
    }

    assert_pre_and_specialize Hbox_sim; [constructor | ].
    assert_pre_and_specialize Hbox_sim; [apply pf_WF_boxes | ].
    assert_pre_and_specialize Hbox_sim; [apply box_fns_preserve_boxes | ].
    assert_pre_and_specialize Hbox_sim. { apply computable_regs_not_in_boxes_correct. reflexivity. }

    destruct Hbox_sim as (Hsim_regs & Hsim_box).
    assert (fbox_sim Tag0 impl_st' spec_st') as HF0sim0.
    { consider box_sim_state_prop. simpl in Hsim_box.
      repeat (rewrite Forall_cons_iff in Hsim_box; try rewrite Forall_single in Hsim_box);
        simpl in Hsim_box; propositional; unfold fbox_sim;
        apply pf_box_data_sim; auto.
    }
    assert (gbox_sim Tag0 impl_st' spec_st') as HG0sim0.
    { consider box_sim_state_prop; simpl in Hsim_box.
      repeat (rewrite Forall_cons_iff in Hsim_box; try rewrite Forall_single in Hsim_box);
        simpl in Hsim_box; propositional; unfold fbox_sim;
        apply pf_box_data_sim; auto.
    }
    split;[repeat constructor; auto | ].
    repeat constructor; simpl; simpl in Hsim_regs; simpl in Hsim_box.
    all: match goal with
        | H: box_sim_state_prop _ _ _ ?impl_st' ?spec_st'
          |- ?impl_st'.[?reg] = ?spec_st'.[?reg] =>
            let _ := match reg with
                     | Impl.F0Box.REG_valid0 => idtac
                     | Impl.F1Box.REG_valid0 => idtac
                     | Impl.G0Box.REG_valid0 => idtac
                     | Impl.G1Box.REG_valid0 => idtac
                     end in
            unfold box_sim_state_prop in H;
            repeat (rewrite Forall_cons_iff in H; try rewrite Forall_single in H); simpl in H;
            unfold fbox, gbox in H; propositional
        | H: reg_sim_state_prop _ ?impl_st' ?spec_st'
          |- ?impl_st'.[?r_eg] = ?spec_st'.[?_reg] =>
            unfold reg_sim_state_prop in H; specialize H with (reg := _reg); simpl in H;
            consider BoxSimAnalysis.update_sim_reg' ;
            repeat rewrite SortedRegEnv.update_correct_neq in H by discriminate;
            try rewrite SortedRegEnv.update_correct_eq in H; simpl in H; auto
        end.
    - apply (pf_box_valid_sim _ _ _ Hsim_box0); simpl; auto.
    - apply (pf_box_valid_sim _ _ _ Hsim_box1); simpl; auto.
  Qed.

  Lemma SimRlSatisfiesSpec__DoStep0__Tag1 :
    __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoStep0 Tag1) (Impl.rules Impl.DoStep0).
  Proof.
    start_sim_proof Himpl_fail Hspec_fail ImplementationProofs.RlSatisfiesSpec__DoStep0.
    repeat constructor.
  Qed.

  Lemma SimRlSatisfiesSpec__DoStep0 :
    forall tag, __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoStep0 tag) (Impl.rules Impl.DoStep0).
  Proof.
    destruct tag.
    - apply SimRlSatisfiesSpec__DoStep0__Tag0.
    - apply SimRlSatisfiesSpec__DoStep0__Tag1.
  Qed.


  Lemma SimRlSatisfiesSpec__DoStep1__Tag0 :
    __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoStep1 Tag0) (Impl.rules Impl.DoStep1).
  Proof.
    start_sim_proof Himpl_fail Hspec_fail ImplementationProofs.RlSatisfiesSpec__DoStep1.
    repeat constructor.
  Qed.
  Ltac split_ors_in H:=
    repeat match type of H with
    | _ \/ _ =>
      destruct H as [H | H]; split_ors_in H
    end.

  Lemma SimRlSatisfiesSpec__DoStep1__Tag1 :
    __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoStep1 Tag1) (Impl.rules Impl.DoStep1).
  Proof.
    start_sim_proof Himpl_fail Hspec_fail ImplementationProofs.RlSatisfiesSpec__DoStep1.
    simpl in Himpl_fail. simpl in Hspec_fail. simplify.
    rename s0 into impl_st'. rename s into spec_st'.

    specialize box_sim_analyze_rule_correct with
      (1 := Horaat_impl) (2 := Horaat_spec)
      (box_t_eq_dec := EqDec_box_t) (box_defs := boxes)
      (box_fns := box_fns) (ext_fn_sims := []) (reg_sims := step_sim1_regs) (box_sims := [FBox Tag1; GBox Tag1])
      (9 := eq_refl).
    intros Hbox_sim.
    assert_pre_and_specialize Hbox_sim.
    { apply reg_sim_state_prop_implied; simpl.
      repeat constructor.
      - pre_sim_rewrite_with_reg_spec Impl.REG_clk Hpre. auto.
      - pre_sim_rewrite_with_reg_spec Impl.REG_job1 Hpre. auto.
    }
    assert_pre_and_specialize Hbox_sim.
    { unfold box_sim_state_prop. constructor; [| constructor; [ | constructor]]; simpl;
      clear - Hpre; destruct Hpre; simpl in *;
      repeat (rewrite Forall_cons_iff in *; try rewrite Forall_single in *); unfold fbox_sim, gbox_sim; simpl;
      constructor; simpl; propositional; simplify; auto.
    }

    assert_pre_and_specialize Hbox_sim; [constructor | ].
    assert_pre_and_specialize Hbox_sim; [apply pf_WF_boxes | ].
    assert_pre_and_specialize Hbox_sim; [apply box_fns_preserve_boxes | ].
    assert_pre_and_specialize Hbox_sim. { apply computable_regs_not_in_boxes_correct. reflexivity. }

    destruct Hbox_sim as (Hsim_regs & Hsim_box).
    assert (fbox_sim Tag1 impl_st' spec_st') as HF1sim1.
    { consider box_sim_state_prop. simpl in Hsim_box.
      repeat (rewrite Forall_cons_iff in Hsim_box; try rewrite Forall_single in Hsim_box);
        simpl in Hsim_box; propositional; unfold fbox_sim;
        apply pf_box_data_sim; auto.
    }
    assert (gbox_sim Tag1 impl_st' spec_st') as HG1sim1.
    { consider box_sim_state_prop; simpl in Hsim_box.
      repeat (rewrite Forall_cons_iff in Hsim_box; try rewrite Forall_single in Hsim_box);
        simpl in Hsim_box; propositional; unfold fbox_sim;
        apply pf_box_data_sim; auto.
    }
    split;[repeat constructor; auto | ].
    repeat constructor; simpl; simpl in Hsim_regs; simpl in Hsim_box.
    all: match goal with
        | H: box_sim_state_prop _ _ _ ?impl_st' ?spec_st'
          |- ?impl_st'.[?reg] = ?spec_st'.[?reg] =>
            let _ := match reg with
                     | Impl.F0Box.REG_valid0 => idtac
                     | Impl.F1Box.REG_valid0 => idtac
                     | Impl.G0Box.REG_valid0 => idtac
                     | Impl.G1Box.REG_valid0 => idtac
                     end in
            unfold box_sim_state_prop in H;
            repeat (rewrite Forall_cons_iff in H; try rewrite Forall_single in H); simpl in H;
            unfold fbox, gbox in H; propositional
        | H: reg_sim_state_prop _ ?impl_st' ?spec_st'
          |- ?impl_st'.[?r_eg] = ?spec_st'.[?_reg] =>
            unfold reg_sim_state_prop in H; specialize H with (reg := _reg); simpl in H;
            consider BoxSimAnalysis.update_sim_reg' ;
            repeat rewrite SortedRegEnv.update_correct_neq in H by discriminate;
            try rewrite SortedRegEnv.update_correct_eq in H; simpl in H; auto
        end.
    - apply (pf_box_valid_sim _ _ _ Hsim_box0); simpl; auto.
    - apply (pf_box_valid_sim _ _ _ Hsim_box1); simpl; auto.
  Qed.

  Lemma SimRlSatisfiesSpec__DoStep1 :
    forall tag, __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoStep1 tag) (Impl.rules Impl.DoStep1).
  Proof.
    destruct tag.
    - apply SimRlSatisfiesSpec__DoStep1__Tag0.
    - apply SimRlSatisfiesSpec__DoStep1__Tag1.
  Qed.

  Lemma SimRlSatisfiesSpec__DoInputTag1 :
    __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoInput Tag1) (Impl.rules Impl.DoInput).
  Proof.
    start_sim_proof Himpl_fail Hspec_fail ImplementationProofs.RlSatisfiesSpec__DoInput.
    (* revert Heqp0. revert Horaat_spec. *)
    revert Horaat_impl.
    unfold Impl.rules, Impl.do_input.
    eapply oraat_wp_action_correct.
    pre_sim_pose_custom_as Hpre_ext_ready SimCustomInput Hpre.
    simpl in Hpre_ext_ready.

    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HImpl__ext_valid.
    - repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as HImpl__GetJob; repeat (repeat step_wp_oraat_safe; simpl).
      + destruct_match_as HImpl__ext_data; repeat (repeat step_wp_oraat_safe; simpl).
        * destruct Hpre_ext_ready as [[Himpl_ext Hspec_ext]| [Himpl_ext ?]].
          2: { rewrite Himpl_ext in *; discriminate. }
          prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.do_input.
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as HSpec__ext_valid; repeat (repeat step_wp_oraat_safe; simpl).
          { destruct_match_as HSpec__GetJob; repeat (repeat step_wp_oraat_safe; simpl).
            { destruct_match_as HSpec__ext_data; repeat (repeat step_wp_oraat_safe; simpl).
              { prepare_finish; repeat constructor; simplify_updates; subst.
                pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1 Hpre; auto. }
              { apply single_bit_negate in HSpec__ext_data; auto; [ |  apply unsafe_get_field_length; auto].
                assert (spec_st.[Impl.REG_ext_ready_for_job] = (mk_ready_tag Tag1) ) as Hspec_ext_eq.
                { apply option_get_fields_eq with (sz := 1); try solve_bits; eauto. }
                contradiction.
              }
            }
            { prepare_finish; repeat constructor; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1 Hpre; auto. }
          }
          { prepare_finish; repeat constructor; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1 Hpre; auto. }
        * assert (impl_st.[Impl.REG_ext_ready_for_job] = (Ob~1 ++ Ob~1)%list) as Hext.
          { apply option_get_fields_eq with (sz := 1); try solve_bits; eauto.
            apply single_bit_negate in HImpl__ext_data; auto. apply unsafe_get_field_length; auto.
          }
          destruct Hpre_ext_ready as [[Himpl_ext Hspec_ext]| [Himpl_ext [Hext_sim Hsigma_sim]]]; [contradiction | ].
          prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.do_input.
          repeat (repeat step_wp_oraat_safe; simpl).
          rewrite<-Hext_sim; simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          rewrite<-Hsigma_sim. simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish; repeat constructor; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1 Hpre; auto.
      + prepare_finish; repeat constructor; revert Horaat_spec.
        eapply oraat_wp_action_correct; unfold Impl.rules, Impl.do_input.
        repeat (repeat step_wp_oraat_safe; simpl).
        destruct_match_as HSpec__ext_valid; repeat (repeat step_wp_oraat_safe; simpl).
        * destruct_match_as HSpec__GetJob; repeat (repeat step_wp_oraat_safe; simpl).
          { destruct_match_as HSpec__ext_data; repeat (repeat step_wp_oraat_safe; simpl).
            { prepare_finish; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1 Hpre; auto. }
            { assert (spec_st.[Impl.REG_ext_ready_for_job] = (mk_ready_tag Tag1)) as Hext.
              { apply option_get_fields_eq with (sz := 1); try solve_bits; eauto.
                apply single_bit_negate in HSpec__ext_data; auto. apply unsafe_get_field_length; auto.
              }
              destruct Hpre_ext_ready as [[Himpl_ext Hspec_ext]| [Himpl_ext [Hext_sim Hsigma_sim]]]; [contradiction | ].
              rewrite<-Hsigma_sim in HSpec__GetJob. rewrite<-Hext_sim in HSpec__GetJob. congruence.
            }
          }
          { prepare_finish; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1 Hpre; auto. }
        * prepare_finish; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1 Hpre; auto.
    - destruct Hpre_ext_ready as [[Himpl_ext Hspec_ext] | [Hext_eq ? ]].
      2: { rewrite Hext_eq in HImpl__ext_valid. discriminate. }
      repeat (repeat step_wp_oraat_safe; simpl).
      prepare_finish.  revert Horaat_spec.
      eapply oraat_wp_action_correct; unfold Impl.rules, Impl.do_input.
      repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as HSpec__ext_valid; repeat (repeat step_wp_oraat_safe; simpl).
      + destruct_match_as HSpec__GetJob; repeat (repeat step_wp_oraat_safe; simpl).
        * destruct_match_as HSpec__ext_data; repeat (repeat step_wp_oraat_safe; simpl).
          { prepare_finish; repeat constructor; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1 Hpre. auto. }
          { assert (spec_st.[Impl.REG_ext_ready_for_job] = (mk_ready_tag Tag1) ) as Hspec_ext_eq.
            { apply option_get_fields_eq with (sz := 1); try solve_bits; eauto.
              apply single_bit_negate in HSpec__ext_data; auto. apply unsafe_get_field_length; auto.
            }
            contradiction.
          }
        * prepare_finish; repeat constructor; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1 Hpre. auto.
      + prepare_finish; repeat constructor; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1 Hpre. auto.
  Qed.


  Lemma SimRlSatisfiesSpec__DoInputTag0 :
    __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoInput Tag0) (Impl.rules Impl.DoInput).
  Proof.
    start_sim_proof Himpl_fail Hspec_fail ImplementationProofs.RlSatisfiesSpec__DoInput.
    repeat constructor.
    (* rename s into impl_st'. *)
    (* rename s0 into spec_st'. *)
    (* revert Heqp0. revert Horaat_spec. *)
    revert Horaat_impl.
    unfold Impl.rules, Impl.do_input.
    eapply oraat_wp_action_correct.
    pre_sim_pose_custom_as Hpre_ext_ready SimCustomInput Hpre.
    simpl in Hpre_ext_ready.

    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HImpl__ext_valid.
    - repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as HImpl__GetJob; repeat (repeat step_wp_oraat_safe; simpl).
      + destruct_match_as HImpl__ext_data; repeat (repeat step_wp_oraat_safe; simpl).
        * assert (impl_st.[Impl.REG_ext_ready_for_job] = (Ob~1 ++ Ob~0)%list) as Hext.
          { apply option_get_fields_eq with (sz := 1); try solve_bits; eauto. }
          destruct Hpre_ext_ready as [[? ?]| [Himpl_ext [Hsim_ext Hsim_GetJob]]]; [ contradiction | ].
          prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.do_input.
          repeat (repeat step_wp_oraat_safe; simpl).
          rewrite<-Hsim_ext. simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          rewrite<-Hsim_GetJob. simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish; simplify_updates.
        * assert (impl_st.[Impl.REG_ext_ready_for_job] <> (mk_ready_tag Tag0) ) as Himpl_ext_neq.
          { unfold not, mk_ready_tag; intros Hext_eq; rewrite Hext_eq in *; discriminate. }
          destruct Hpre_ext_ready as [[Himpl_ext Hspec_ext]| [Himpl_ext ?]]; [ | contradiction].
          prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.do_input.
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as HSpec__ext_valid; repeat (repeat step_wp_oraat_safe; simpl).
          { destruct_match_as HSpec__GetJob; repeat (repeat step_wp_oraat_safe; simpl).
            { destruct_match_as HSpec__ext_data; repeat (repeat step_wp_oraat_safe; simpl).
              { assert (spec_st.[Impl.REG_ext_ready_for_job] = (mk_ready_tag Tag0) ) as Hspec_ext_eq.
                { apply option_get_fields_eq with (sz := 1); try solve_bits; eauto. }
                contradiction.
              }
              { prepare_finish. simplify_updates. pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0 Hpre. auto.
              }
            }
            { prepare_finish; simplify_updates. pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0 Hpre. auto.
            }
          }
          { prepare_finish; simplify_updates. pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0 Hpre. auto.
          }
      + prepare_finish. revert Horaat_spec.
        eapply oraat_wp_action_correct; unfold Impl.rules, Impl.do_input.
        repeat (repeat step_wp_oraat_safe; simpl).
        destruct_match_as HSpec__ext_valid; repeat (repeat step_wp_oraat_safe; simpl).
        * destruct_match_as HSpec__GetJob; repeat (repeat step_wp_oraat_safe; simpl).
          { destruct_match_as HSpec__ext_data; repeat (repeat step_wp_oraat_safe; simpl).
            { assert (spec_st.[Impl.REG_ext_ready_for_job] = (mk_ready_tag Tag0) ) as Hspec_ext_eq.
              { apply option_get_fields_eq with (sz := 1); try solve_bits; eauto. }
              destruct Hpre_ext_ready as [[Himpl_ext Hspec_ext] | [Himpl_ext [Hext_sim Hsigma_sim]]]; [contradiction | ].
              rewrite<-Hsigma_sim in HSpec__GetJob.
              rewrite<-Hext_sim in HSpec__GetJob. congruence.
            }
            { prepare_finish; simplify_updates. pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0 Hpre. auto.
            }
          }
          { prepare_finish; simplify_updates. pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0 Hpre. auto.
          }
        * prepare_finish; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0 Hpre. auto.
    - destruct Hpre_ext_ready as [[Himpl_ext Hspec_ext] | [Hext_eq ? ]].
      2: { rewrite Hext_eq in HImpl__ext_valid. discriminate. }
      repeat (repeat step_wp_oraat_safe; simpl).
      prepare_finish. revert Horaat_spec.
      eapply oraat_wp_action_correct; unfold Impl.rules, Impl.do_input.
      repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as HSpec__ext_valid; repeat (repeat step_wp_oraat_safe; simpl).
      + destruct_match_as HSpec__GetJob; repeat (repeat step_wp_oraat_safe; simpl).
        * destruct_match_as HSpec__ext_data; repeat (repeat step_wp_oraat_safe; simpl).
          { assert (spec_st.[Impl.REG_ext_ready_for_job] = (mk_ready_tag Tag0) ) as Hspec_ext_eq.
            { apply option_get_fields_eq with (sz := 1); try solve_bits; eauto. }
            contradiction.
          }
          { prepare_finish; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0 Hpre. auto. }
        * prepare_finish; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0 Hpre. auto.
      + prepare_finish; simplify_updates; pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0 Hpre. auto.
  Qed.


  Lemma SimRlSatisfiesSpec__DoInput :
    forall tag, __sim_oraat_rule_satisfies_spec (SimRuleSpec__DoInput tag) (Impl.rules Impl.DoInput).
  Proof.
    destruct tag.
    - apply SimRlSatisfiesSpec__DoInputTag0.
    - apply SimRlSatisfiesSpec__DoInputTag1.
  Qed.


  Lemma SimRlSatisfiesSpec__UpdateReadyTag1 :
    __sim_oraat_rule_satisfies_spec (SimRuleSpec__UpdateReady Tag1) (Impl.rules Impl.UpdateReady).
  Proof.
    start_sim_proof Himpl_fail Hspec_fail ImplementationProofs.RlSatisfiesSpec__UpdateReady.
    constructor; [ constructor; auto | ].
    set (match impl_opt with | Some (_, st', _) => st' | None => impl_st end) as impl_st' in *.
    set (match spec_opt with | Some (_, st', _) => st' | None => spec_st end) as spec_st' in *.

    revert Horaat_impl.
    unfold Impl.rules, Impl.update_ready.
    eapply oraat_wp_action_correct.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HImpl__Job0.
    - repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as HImpl__Clk.
      + repeat (repeat step_wp_oraat_safe; simpl).
        prepare_finish. revert Horaat_spec.
        eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
        repeat (repeat step_wp_oraat_safe; simpl).
        destruct_match_as HSpec__Job0.
        * repeat (repeat step_wp_oraat_safe; simpl).
          pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          subst impl_st' spec_st'; prepare_finish.
          repeat constructor; unfold output_reg_sim; simplify_updates.
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
          { apply bits_eq_iff in HImpl__Clk. rewrite HImpl__Clk. discriminate. }
        * repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as HImpl__Job1.
          { repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { apply bits_eq_iff in HImpl__Clk. rewrite HImpl__Clk. discriminate. }
          }
          { repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { apply bits_eq_iff in HImpl__Clk. rewrite HImpl__Clk. discriminate. }
          }
      + repeat (repeat step_wp_oraat_safe; simpl).
        prepare_finish. revert Horaat_spec.
        eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
        repeat (repeat step_wp_oraat_safe; simpl).
        destruct_match_as HSpec__Job0; repeat (repeat step_wp_oraat_safe; simpl).
        * pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          subst impl_st' spec_st'; prepare_finish.
          repeat constructor; unfold output_reg_sim; simplify_updates.
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg1 Hpre; auto. }
        * destruct_match_as HSpec__Job1; repeat (repeat step_wp_oraat_safe; simpl).
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg1 Hpre; auto. }
          }
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg1 Hpre; auto. }
          }
    - repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as HImpl__Job1; repeat (repeat step_wp_oraat_safe; simpl).
      + destruct_match_as HImpl__Clk; repeat (repeat step_wp_oraat_safe; simpl).
        * prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as HSpec__Job0; repeat (repeat step_wp_oraat_safe; simpl).
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { apply bits_eq_iff in HImpl__Clk. rewrite HImpl__Clk. discriminate. }
          }
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1' Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { apply bits_eq_iff in HImpl__Clk. rewrite HImpl__Clk. discriminate. }
          }
        * prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as HSpec__Job0; repeat (repeat step_wp_oraat_safe; simpl).
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg1 Hpre; auto. }
          }
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1' Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg1 Hpre; auto. }
          }
      + destruct_match_as HImpl__Clk; repeat (repeat step_wp_oraat_safe; simpl).
        * prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as HSpec__Job0; repeat (repeat step_wp_oraat_safe; simpl).
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { apply bits_eq_iff in HImpl__Clk; rewrite HImpl__Clk; discriminate. }
          }
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1' Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { apply bits_eq_iff in HImpl__Clk; rewrite HImpl__Clk; discriminate. }
          }
        * prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
          repeat (repeat step_wp_oraat_safe; simpl).
           destruct_match_as HSpec__Job0; repeat (repeat step_wp_oraat_safe; simpl).
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg1 Hpre; auto. }
          }
          { pre_sim_rewrite_with_reg_spec__rev Impl.REG_job1' Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto. }
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg1 Hpre; auto. }
          }
  Qed.

  Lemma SimRlSatisfiesSpec__UpdateReadyTag0 :
    __sim_oraat_rule_satisfies_spec (SimRuleSpec__UpdateReady Tag0) (Impl.rules Impl.UpdateReady).
  Proof.
    start_sim_proof Himpl_fail Hspec_fail ImplementationProofs.RlSatisfiesSpec__UpdateReady.
    constructor; [ constructor; auto | ].
    set (match impl_opt with | Some (_, st', _) => st' | None => impl_st end) as impl_st' in *.
    set (match spec_opt with | Some (_, st', _) => st' | None => spec_st end) as spec_st' in *.
    revert Horaat_impl.
    unfold Impl.rules, Impl.update_ready.
    eapply oraat_wp_action_correct.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HImpl__Job0.
    - repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as HImpl__Clk.
      + repeat (repeat step_wp_oraat_safe; simpl).
        prepare_finish. revert Horaat_spec.
        eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
        repeat (repeat step_wp_oraat_safe; simpl).
        pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0' Hpre; simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl).
        pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl).
        subst impl_st' spec_st'; prepare_finish.
        repeat constructor; simplify_updates.
        * pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto.
        * unfold output_reg_sim; simplify_updates.
          pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg0 Hpre. auto.
      + repeat (repeat step_wp_oraat_safe; simpl).
        prepare_finish. revert Horaat_spec.
        eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
        repeat (repeat step_wp_oraat_safe; simpl).
        pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0' Hpre; simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl).
        pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
        repeat (repeat step_wp_oraat_safe; simpl).
        subst impl_st' spec_st'; prepare_finish.
        repeat constructor; unfold output_reg_sim; simplify_updates.
        * pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre. auto.
        * apply single_bit_negate in HImpl__Clk; eauto with wf_types.
          rewrite HImpl__Clk. discriminate.
    - repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as HImpl__Job1.
      + repeat (repeat step_wp_oraat_safe; simpl).
        destruct_match_as HImpl__Clk.
        * repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
          repeat (repeat step_wp_oraat_safe; simpl).
          pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0' Hpre; simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as HSpec__Job1.
          { repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; auto. }
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg0 Hpre; auto.
            }
          }
          { repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; auto. }
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg0 Hpre; auto. }
          }
        * repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
          repeat (repeat step_wp_oraat_safe; simpl).
          pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0' Hpre; simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as HSpec__Job1.
          { repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; auto. }
            { apply single_bit_negate in HImpl__Clk; eauto with wf_types.
              rewrite HImpl__Clk. discriminate.
            }
          }
          { repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; auto. }
            { apply single_bit_negate in HImpl__Clk; eauto with wf_types.
              rewrite HImpl__Clk. discriminate.
            }
          }
      + repeat (repeat step_wp_oraat_safe; simpl).
        destruct_match_as HImpl__Clk.
        * repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
          repeat (repeat step_wp_oraat_safe; simpl).
          pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0' Hpre; simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as HSpec__Job1.
          { repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; auto. }
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg0 Hpre; auto. }
          }
          { repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; auto. }
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_ext_output_reg0 Hpre; auto. }
          }
        * repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish. revert Horaat_spec.
          eapply oraat_wp_action_correct; unfold Impl.rules, Impl.update_ready.
          repeat (repeat step_wp_oraat_safe; simpl).
          pre_sim_rewrite_with_reg_spec__rev Impl.REG_job0' Hpre; simpl_match.
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as HSpec__Job1.
          { repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; auto. }
            { apply single_bit_negate in HImpl__Clk; eauto with wf_types.
              rewrite HImpl__Clk. discriminate.
            }
          }
          { repeat (repeat step_wp_oraat_safe; simpl).
            pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; simpl_match.
            repeat (repeat step_wp_oraat_safe; simpl).
            subst impl_st' spec_st'; prepare_finish.
            repeat constructor; unfold output_reg_sim; simplify_updates.
            { pre_sim_rewrite_with_reg_spec__rev Impl.REG_clk Hpre; auto. }
            { apply single_bit_negate in HImpl__Clk; eauto with wf_types.
              rewrite HImpl__Clk. discriminate.
            }
          }
  Qed.

  Lemma SimRlSatisfiesSpec__UpdateReady :
    forall tag, __sim_oraat_rule_satisfies_spec (SimRuleSpec__UpdateReady tag) (Impl.rules Impl.UpdateReady).
  Proof.
    destruct tag.
    - apply SimRlSatisfiesSpec__UpdateReadyTag0.
    - apply SimRlSatisfiesSpec__UpdateReadyTag1.
  Qed.

End SimProofs.

Module SimProof := StepSim SimProofs.
Include SimProof.
