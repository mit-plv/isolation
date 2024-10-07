Require Import Koika.Frontend.

Require Import Koika.examples.ResourceIsolation_Util.
Require Import Koika.examples.ResourceIsolation_Impl.
Require Import Koika.examples.ResourceIsolation_Spec.
Require Import Koika.examples.ResourceIsolation_Theorem.
(* Require Import Koika.Magic. *)

Import Common.

Notation "st .[ idx ]" := (unsafe_get_reg st idx) (at level 1, format "st .[ idx ]").

Section Util.
  Definition unsafe_get_job_stage vs :=
    unsafe_get_field Impl.S_job_t.(struct_fields) Impl.FLD_job_t_stage vs.

  Definition job_reg (tag: Tag) : reg_t :=
    match tag with
    | Tag0 => Impl.REG_job0
    | Tag1 => Impl.REG_job1
    end.

  Definition is_job_reg tag reg :=
    reg = job_reg tag.

  Definition invert_tag (tag: Tag) : Tag :=
    match tag with
    | Tag0 => Tag1
    | Tag1 => Tag0
    end.

  Lemma regs_in_taint_existsb:
    forall tag reg r1s r2s,
      reg_in_taint_list tag reg r1s r2s ->
      existsb (Nat.eqb reg) (r1s ++ r2s) = true.
  Proof.
    consider reg_in_taint_list.
    destruct tag; intros.
    - rewrite existsb_app. apply orb_true_iff. left; auto.
    - rewrite existsb_app. apply orb_true_iff. right; auto.
  Qed.

  Lemma unsafe_get_field_length:
    forall fields f v n,
      get_field_width fields f = Success n ->
      is_success (get_field fields f v) = true ->
      Datatypes.length (unsafe_get_field fields f v) = n.
  Proof.
    intros * Hwidth Hsuccess. unfold is_success, unsafe_get_field, success_or_default in *. simplify.
    unfold get_field in *. simplify. unfold slice.
    specialize element_offset_and_width_lt_struct_sz with (1 := Heqr0) (2 := Heqr1). intros.
    rewrite firstn_fill_eq.
    2: { rewrite skipn_length. lia. }
    rewrite firstn_length. rewrite skipn_length.
    lia.
  Qed.
  Lemma single_bit_negate:
    forall bs x,
      Datatypes.length bs = 1 ->
      bits_eq bs Ob~x = false ->
      bs = Ob~(negb x).
  Proof.
    intros. destruct bs; [ discriminate | ].
    destruct b; simpl in *; destruct bs; simpl in *; try discriminate.
    - destruct x; simpl in *; try discriminate; auto.
    - destruct x; simpl in *; try discriminate; auto.
  Qed.


    Lemma bool_eqb_true:
      forall b,
        Bool.eqb b true = b.
    Proof.
      destruct b; auto.
    Qed.
    Lemma unsafe_get_field_success_or_default:
      forall flds fld v,
        success_or_default (Semantics.get_field flds fld v) Ob = unsafe_get_field flds fld v.
    Proof.
      reflexivity.
    Qed.
    Lemma unsafe_get_reg_success_or_default:
      forall st reg ,
        success_or_default (r_get_reg st reg) Ob = unsafe_get_reg st reg.
    Proof.
      intros. unfold success_or_default, unsafe_get_reg, r_get_reg. destruct_match; auto.
    Qed.

    Lemma unsafe_get_reg_state_set_eq:
      forall st reg v,
        unsafe_get_reg (state_set st reg v) reg = v.
    Proof.
      intros. unfold unsafe_get_reg, state_set, reg_t_beq, r_get_reg.
      rewrite SortedRegEnv.update_correct_eq. simpl. destruct_match; auto.
    Qed.

    Lemma option_get_fields_eq:
      forall sz v b1 b2,
        is_success (get_field (STRUCT_maybe_fields sz) FIELD_maybe_valid v) = true ->
        is_success (get_field (STRUCT_maybe_fields sz) FIELD_maybe_data v) = true ->
        unsafe_get_field (STRUCT_maybe_fields sz) FIELD_maybe_valid v = b1 ->
        unsafe_get_field (STRUCT_maybe_fields sz) FIELD_maybe_data v = b2 ->
        v = List.app b1 b2.
    Proof.
      unfold unsafe_get_field, is_success, success_or_default; intros.
      simplify.
      unfold get_field in *. simplify; simpl in *.
      cbn in *; simplify; simpl.
      unfold slice.
      rewrite firstn_fill_eq.
      2 : { rewrite skipn_length. lia. }
      rewrite firstn_fill_eq.
      2 : { rewrite skipn_length. lia. }
      rewrite skipn_O.
      destruct v; simpl in *; [ discriminate | ].
      f_equal. inversion Heqb.
      rewrite firstn_all. reflexivity.
    Qed.

    Lemma list_beq_equiv_bits_eq:
      forall x1 x2,
        list_beq bool Bool.eqb x1 x2 = bits_eq x1 x2.
    Proof.
      reflexivity.
    Qed.

    Lemma unsafe_get_reg_state_set_neq:
      forall st reg1 reg2 v,
        reg1 <> reg2 ->
        unsafe_get_reg (state_set st reg1 v) reg2 = unsafe_get_reg st reg2.
    Proof.
      intros. unfold unsafe_get_reg, state_set, reg_t_beq, r_get_reg.
      rewrite SortedRegEnv.update_correct_neq by auto.
      destruct_match; simplify_nat; auto; try discriminate.
    Qed.

    Lemma plus_one_negate:
      forall v1 default,
        is_success (plus v1 Ob~1) = true ->
        success_or_default (plus v1 Ob~1) default = neg v1.
    Proof.
      intros. unfold is_success, success_or_default, plus in *.
      simplify.
      destruct (case_singleton_bv v1); auto; subst; reflexivity.
    Qed.
    Lemma bits_eq_iff:
      forall xs ys,
        bits_eq xs ys = true <->
        xs = ys.
    Proof.
      unfold bits_eq.
      apply bool_list_beq_iff.
    Qed.

    Lemma bits_neq_iff:
      forall xs ys,
        bits_eq xs ys = false <->
        xs <> ys.
    Proof.
      unfold bits_eq.
      apply bool_list_bneq_iff.
    Qed.

    Lemma bits_eq_refl:
      forall x, bits_eq x x = true.
    Proof.
      intros. apply bits_eq_iff. auto.
    Qed.

    Lemma bits_eq_sym:
      forall x y,
        bits_eq x y = bits_eq y x.
    Proof.
      intros. destruct_with_eqn (bits_eq x y).
      - apply bits_eq_iff in Heqb; subst. rewrite bits_eq_refl. auto.
      - apply bits_neq_iff in Heqb. symmetry. apply bits_neq_iff. auto.
    Qed.

    Lemma bits_eq_negl:
      forall v1 v2,
        bits_eq (neg v1) v2  = true ->
        bits_eq v1 (neg v2) = true.
    Proof.
      intros. apply bits_eq_iff in H. apply bits_eq_iff. subst.
      rewrite neg_involutive.
      reflexivity.
    Qed.

    Lemma case_two_bits:
      forall bs,
        Datatypes.length bs = 2 ->
        bs = Ob~0~0 \/ bs = Ob~0~1 \/ bs = Ob~1~0 \/ bs = Ob~1~1.
    Proof.
      destruct bs; propositional; try discriminate.
      destruct bs; propositional; try discriminate.
      destruct bs; propositional; try discriminate.
      destruct b; destruct b0; auto.
    Qed.

    Lemma case_G:
      forall bs,
        Datatypes.length bs = 2 ->
        bs <> Ob~0~0 ->
        bs <> Ob~0~1 ->
        bs <> Ob~1~0 ->
        bs = Ob~1~1.
    Proof.
      intros bs length. apply case_two_bits  in length.
      propositional. split_cases; try discriminate; auto.
    Qed.

    Lemma is_success_and_length:
      forall v1 v2,
        is_success (and v1 v2) = true ->
        Datatypes.length v1 = Datatypes.length v2.
    Proof.
      intros. unfold and in *. unfold is_success in *. simplify.
      apply map2_length in Heqr. propositional.
    Qed.

Lemma is_success_and_length':
  forall v1 v2 n,
  is_success (and v1 v2) = true ->
  Datatypes.length (success_or_default (and v1 v2) Ob) = n ->
  Datatypes.length v1 = n /\ Datatypes.length v2 = n.
Proof.
  intros. unfold is_success in *. unfold success_or_default in *. simplify.
  unfold and in *. apply map2_length in Heqr. propositional. split; congruence.
Qed.
Lemma bits_eq_and_true:
  forall v1 v2 n,
  is_success (and v1 v2) = true ->
  Datatypes.length (success_or_default (and v1 v2) Ob) = n ->
  success_or_default (and v1 v2) Ob = ones n ->
  v1 = ones n /\ v2 = ones n.
Proof.
  intros * Hsuccess Hlength Hones.
  assert (Datatypes.length v1 = n /\ Datatypes.length v2 = n).
  { apply is_success_and_length'; propositional. }
  propositional. unfold is_success, success_or_default in *. simplify.
  unfold and, ones in *.
  generalize dependent v1.
  generalize dependent v2.
  generalize dependent s.
  induction s; simpl.
  - destruct v2; try discriminate. destruct v1; try discriminate. auto.
  - intros Heq. inversions Heq. specialize (IHs H1).
    destruct v2; simpl; [discriminate | ].
    intros Heq. inversions Heq. rewrite firstn_fill_length in H0. specialize IHs with (1 := H0).
    destruct v1; simpl; [discriminate | ].
    intros; simplify. rewrite H3 in *.
    rewrite<-H1 in Heqr0. specialize IHs with (1 := Heqr0). inversions H2.
    rewrite H0 in H4. propositional.
    rewrite firstn_fill_length. rewrite andb_true_iff in H3. propositional.
Qed.

Lemma bits_eq_and_true_l:
  forall v1 v2 n,
  is_success (and v1 v2) = true ->
  Datatypes.length (success_or_default (and v1 v2) Ob) = n ->
  success_or_default (and v1 v2) Ob = ones n ->
  v1 = ones n.
Proof.
  intros. eapply bits_eq_and_true in H; eauto.
  propositional.
Qed.

End Util.

Section TODO_ORAAT_CPS'.
    Context (ext_sigma: ext_sigma_t).
    Context (int_fns: int_fn_env_t).
    Context (struct_defs: struct_env_t).
    Notation oraat_interp_action_cps := (oraat_interp_action_cps ext_sigma int_fns struct_defs).
    Notation oraat_interp_action := (oraat_interp_action ext_sigma int_fns struct_defs).
    Notation oraat_wp_action := (oraat_wp_action ext_sigma int_fns struct_defs).
    Definition function_spec_prop : Type :=
      state_t -> state_t -> list bool -> option (state_t * list bool) -> Prop.
    Definition function_reg_spec_t :=
      state_t -> state_t -> vect_t -> vect_t -> Prop.

    Record function_spec_t :=
      { Function_precond: state_t -> state_t -> vect_t -> Prop (* TODO: include argument... *)
      ; Function_taint_set : result (option taint_env_t) unit
      ; Function_fail_inversion: ext_sigma_t -> state_t -> state_t -> list bool -> Prop
      ; Function_reg_specs : list (reg_t * function_reg_spec_t)
      }.

    Definition function_spec_to_Prop'
      (spec: function_spec_t)
      (* (argname: var_t)  *)
      (r r_acc: state_t) (varg: list bool)
      (opt_res: option (state_t * list bool)) : Prop :=
      match opt_res with
      | Some (r', ret) =>
          taint_set_to_prop r_acc r' spec.(Function_taint_set)
      | None => True
      end /\
      match opt_res with
      | Some (r', ret) =>
          spec.(Function_precond) r r_acc varg ->
            Forall (fun '(reg, spec) => spec r r_acc varg r'.[reg]
              ) spec.(Function_reg_specs)
      | None => spec.(Function_fail_inversion) ext_sigma r r_acc varg
      end.


    Definition function_spec_to_Prop
      (spec: function_spec_t)
      (* (argname: var_t)  *)
      (r r_acc: state_t) (varg: list bool)
      (opt_res: option (state_t * list bool)) : Prop :=
      match opt_res with
      | Some (r', ret) =>
          spec.(Function_precond) r r_acc varg ->
          taint_set_to_prop r_acc r' spec.(Function_taint_set) /\
            Forall (fun '(reg, spec) => spec r r_acc varg r'.[reg]
              ) spec.(Function_reg_specs)
      | None => spec.(Function_fail_inversion) ext_sigma r r_acc varg
      end.

    Lemma function_spec_to_Prop_implies:
      forall spec r r_acc varg opt_res,
      function_spec_to_Prop' spec r r_acc varg opt_res ->
      function_spec_to_Prop spec r r_acc varg opt_res.
    Proof.
      unfold function_spec_to_Prop', function_spec_to_Prop.
      intros; destruct_all_matches; propositional.
    Qed.


    Definition function_matches_spec
       (spec: function_spec_prop) (argname: var_t) (body: action) :=
        forall fuel (r r_acc: state_t) (varg: list bool) opt_res ,
          oraat_interp_action fuel r r_acc true (fn_gamma argname varg) body = (true, opt_res) ->
          spec r r_acc varg (let/opt3 _, st', ret' := opt_res in Some (st', ret')).

    Definition is_read_only_function (argname: var_t) (body: action) :=
        forall (fuel: nat) (r r_acc: state_t) (varg: list bool) opt_res ,
        oraat_interp_action fuel r r_acc true (fn_gamma argname varg) body = (true, opt_res) ->
        match opt_res with
        | Some (_, st', ret) => st' = r_acc
        | None => False
        end.
    Definition __fn_call__ (fn: fn_name_t) := __debug__ fn_name_t oraat_interp_action.
    Lemma unfold__fn_call__ (fn: fn_name_t) :
      __fn_call__ fn = oraat_interp_action.
    Proof.
      reflexivity.
    Qed.

    Lemma oraat_wp_internal_call__read_only__safe:
      forall fuel r fn arg
        (post: oraat_action_postcondition) (gamma: gamma_t) r_acc arg_name body,
        (forall res, post (false, res)) ->
        get_fn_arg_and_body' int_fns fn = (true, (arg_name, body)) ->
        is_read_only_function arg_name body ->
        oraat_wp_action (Nat.pred fuel) r arg (fun res =>
                         let '(is_safe, opt) := res in
                         is_safe = Datatypes.true ->
                         match opt with
                         | (Some (gamma, r_acc, v_arg)) =>
                           let '(is_safe', opt_res) := __fn_call__ fn (Nat.pred fuel) r r_acc true (fn_gamma arg_name v_arg) body in
                           is_safe' = true ->
                           match opt_res with
                           | Some (_, _, v) => post (true, Some (gamma, r_acc, v))
                           | None => True
                           end
                         | None => post (true, None)
                         end) gamma r_acc true ->
        oraat_wp_action fuel r (InternalCall fn arg) post gamma r_acc true.
    Proof.
      intros * Hpost Hfn_body Hspec Horaat.
      destruct fuel; propositional; cbn; auto.
      rewrite oraat_interp_action_cps_correct.
      rewrite oraat_wp_action_correct in Horaat. simpl in *.
      destruct_match; auto.
      destruct o as [[[? ?] ?]  | ].
      - unfold get_fn_arg_and_body' in *. simplify_tupless. rewrite H0.
        unfold __fn_call__, __debug__ in *.
        rewrite oraat_interp_action_cps_correct.
        rewrite H; simpl.
        destruct_match.
        consider is_read_only_function.
        destruct b0.
        + specialize oraat_interp_action_is_safe_generalizes with (1 := Heqp0).
          propositional. rewrite Heqp0 in *. propositional.
          specialize Hspec with (1 := Heqp0).
          destruct o as [[[? ?] ?]  | ]; subst; auto.
        + repeat destruct_match; auto.
      - destruct b; auto.
    Qed.

    Lemma oraat_wp_internal_call'__safe:
      forall fuel r fn arg
        (post: oraat_action_postcondition) (gamma: gamma_t) r_acc spec
        arg_name body,
        (forall res, post (false, res)) ->
        get_fn_arg_and_body' int_fns fn = (true, (arg_name, body)) ->
        function_matches_spec (function_spec_to_Prop spec) arg_name body ->
        oraat_wp_action (Nat.pred fuel) r arg (fun res =>
                         let '(is_safe, opt) := res in
                         is_safe = Datatypes.true ->
                         match opt with
                         | (Some (gamma, r_acc, v_arg)) =>
                           let '(is_safe', opt_res) := __fn_call__ fn (Nat.pred fuel) r r_acc true (fn_gamma arg_name v_arg) body in
                           is_safe' = true ->
                            match opt_res with
                            | Some (_, r_acc', v) =>
                                spec.(Function_precond) r r_acc v_arg /\
                                (
                                 taint_set_to_prop r_acc r_acc' spec.(Function_taint_set) ->
                                 Forall (fun '(reg, spec) => spec r r_acc v_arg r_acc'.[reg]
                                        ) spec.(Function_reg_specs) ->
                                 post (true, Some (gamma, r_acc', v)))
                            | None =>
                              spec.(Function_fail_inversion) ext_sigma r r_acc v_arg ->
                              post (true, None)
                            end
                         | _ =>
                           post (true, None)
                         end) gamma r_acc true ->
        oraat_wp_action fuel r (InternalCall fn arg) post gamma r_acc true.
    Proof.
      intros * Hpost Hfn_body Hspec Horaat.
      rewrite oraat_wp_action_correct. rewrite oraat_wp_action_correct in Horaat.
      destruct fuel; propositional; cbn; cbn in Horaat; simpl in *; auto.
      destruct_match.
      consider function_matches_spec.
      unfold __fn_call__, __debug__ in *.
      destruct o as [[[? ?] ?]  | ].
      - unfold get_fn_arg_and_body' in *. simplify_tupless.
        rewrite H0. rewrite H in *. simpl.
        destruct_match.
        destruct b0.
        + specialize oraat_interp_action_is_safe_generalizes with (1 := Heqp0). propositional.
          simpl_match. propositional.
          specialize Hspec with (1 := Heqp0).
          destruct o as [[[? ?] ?]  | ]; subst; simpl in Hspec; propositional.
        + destruct o as [[[? ?] ?]  | ]; auto.
     - destruct b; auto.
    Qed.

    Definition taint_function_body (int_fns: int_fn_env_t) (body: action) :=
      taint_action int_fns (safe_fuel int_fns (Datatypes.length int_fns) body) SortedRegEnv.empty body.

    Definition func_call_returns (fn: fn_name_t) (r r_acc: state_t) (varg: list bool) (pred: list bool -> Prop ):=
      match get_fn_arg_and_body' int_fns fn with
      | (true, (arg_name, body)) =>
          exists fuel gamma' st' ret',
            __fn_call__ fn fuel r r_acc true (fn_gamma arg_name varg) body = (true, Some(gamma', st', ret')) /\
              pred ret'
      | _ => False
      end.

End TODO_ORAAT_CPS'.

(*! TODO: MOVE *)
Ltac solve_unsafe :=
  intros; simplify_tupless; simplify_tupless; discriminate.

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
    Ltac solve_read_only :=
      match goal with
      | |- is_read_only_function ?sigma ?int_fn_env ?struct_env (fn_arg_name ?fn) (fn_body ?fn) =>
          let H := fresh in
          unfold is_read_only_function; intros * H;
          eapply read_only_function_safety' in H; [auto | cbv;reflexivity | reflexivity | reflexivity]
     end.


Ltac step_wp_oraat_lib__safe :=
  match goal with
  | |- oraat_wp_action _ _ _ _ _ (invalid _ ) _ _ _ _ =>
    apply oraat_wp_binop__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (valid _ _ ) _ _ _ _ =>
    apply oraat_wp_binop__safe;[ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (action_struct_init _ _ ) _ _ _ _ =>
    apply oraat_wp_binop__safe;[ solve_safe | ]
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

Ltac step_wp_oraat_safe :=
  lazymatch goal with
  | |- oraat_wp_action _ _ _ _ _ (Fail _) _ _ _ _ =>
   apply oraat_wp_fail__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (Var _) _ _ _ _ =>
   apply oraat_wp_var__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (Const _) _ _ _ _ =>
   apply oraat_wp_const__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (Bind _ _ _) _ _ _ _ =>
   apply oraat_wp_bind__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (Seq _ _ ) _ _ _ _ =>
   apply oraat_wp_seq__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (If _ _ _) _ _ _ _ =>
    apply oraat_wp_if__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (Assign _ _) _ _ _ _ =>
    apply oraat_wp_assign__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (Zop _ ) _ _ _ _ =>
    apply oraat_wp_zop__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (Unop _ _ ) _ _ _ _ =>
    apply oraat_wp_unop__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (Binop _ _ _ ) _ _ _ _ =>
    apply oraat_wp_binop__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (Read P0 _) _ _ _ _ =>
    apply oraat_wp_read0__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (Read P1 _) _ _ _ _ =>
    apply oraat_wp_read1__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (Write _ _ _) _ _ _ _ =>
    apply oraat_wp_write__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (ExternalCall _ _) _ _ _ _ =>
    apply oraat_wp_external_call__safe; [ solve_safe | ]
  | |- oraat_wp_action _ _ _ _ _ (InternalCall _ _) _ _ _ _ =>
    fail
  | |- oraat_wp_action _ _ _ _ _ _ _ _ _ _ =>
    step_wp_oraat_lib__safe
  | |- true = true -> _ =>
    let H := fresh in intro H; clear H
  | |- (true, _) = (true, _) -> _ =>
    let H := fresh in intro H; apply pair_eq2 in H
  | |- _ = true -> _ =>
    repeat step_oraat_simpl; let H := fresh "Hsafe" in intro H
  | |- _ => progress (step_oraat_simpl)
  end.
Ltac simplify_bits V :=
  match V with
  | bits_eq ?x ?x =>
    rewrite (bits_eq_refl x)
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
    | r2 => rewrite unsafe_get_reg_state_set_eq with (reg := r1)
    | _ => rewrite unsafe_get_reg_state_set_neq with (reg1 := r1) (reg2 := r2) by discriminate
    end
  | success_or_default (r_get_reg ?st ?reg) _ =>
    rewrite (@unsafe_get_reg_success_or_default st reg)
  | bits_eq ?x ?x =>
     rewrite (bits_eq_refl x)
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

Section Invariants.
  Record ImplPostCond (st st': state_t) (sigma: ext_sigma_t) : Prop :=
    { IP__clk: st'.[Impl.REG_clk] = neg st.[Impl.REG_clk]
    ; IP__waiting: forall tag reg, unsafe_get_job_stage st.[job_reg tag] = Impl.ENUM_stage__None ->
                            is_job_reg tag reg ->
                            (forall job_id, sigma Impl.EXTFN_GetJob job_id = Success (Impl.mk_GetJob None)) \/ (st.[Impl.REG_ext_ready_for_job] <> option_to_maybe' 1 (match tag with | Tag0 => Some Ob~0 | Tag1 => Some Ob~1 end)) ->
                            unsafe_get_job_stage st'.[reg] = Impl.ENUM_stage__None /\
                            (st'.[Impl.REG_clk] = (match tag with | Tag0 => Ob~1 | Tag1 => Ob~0 end) ->
                             st'.[Impl.REG_ext_output_reg] = zeroes (struct_sz Impl.S_maybe_sz))
    }.

  Definition ImplInvariant__ext_ready_for_job (impl_st: state_t) : Prop :=
    impl_st.[Impl.REG_ext_ready_for_job]
      = if bits_eq (unsafe_get_job_stage (impl_st.[Impl.REG_job0])) Impl.ENUM_stage__None then
          (option_to_maybe' 1 (Some [false]))
        else if bits_eq (unsafe_get_job_stage (impl_st.[Impl.REG_job1])) Impl.ENUM_stage__None then
          (option_to_maybe' 1 (Some [true]))
        else (option_to_maybe' 1 (None)).

  Definition ImplInvariant__NONE_OR_INIT (tag: Tag) (impl_st: state_t) : Prop :=
    (unsafe_get_job_stage (impl_st.[job_reg tag]) = Impl.ENUM_stage__None \/
     unsafe_get_job_stage (impl_st.[job_reg tag]) = Impl.ENUM_stage__INIT) ->
    forall reg,
      reg_in_taint_list tag reg [Impl.F0Box.REG_valid0; Impl.G0Box.REG_valid0]
                                [Impl.F1Box.REG_valid0; Impl.G1Box.REG_valid0] ->
      impl_st.[reg] = [false].

    Definition ImplInvariant__STAGE_F (tag: Tag) (impl_st: state_t) : Prop :=
      unsafe_get_job_stage (unsafe_get_reg impl_st (job_reg tag)) = Impl.ENUM_stage__F ->
      forall reg,
        reg_in_taint_list tag reg [Impl.G0Box.REG_valid0] [Impl.G1Box.REG_valid0] ->
        impl_st.[reg] = [false].

    Definition ImplInvariant__STAGE_G (tag: Tag) (impl_st: state_t) : Prop :=
      unsafe_get_job_stage (impl_st.[job_reg tag]) = Impl.ENUM_stage__G ->
      forall reg,
        reg_in_taint_list tag reg [Impl.F0Box.REG_valid0] [Impl.F1Box.REG_valid0] ->
        impl_st.[reg] = [false].

    Definition ImplInvariant__NONE_zeroed (tag: Tag) (impl_st: state_t) : Prop :=
      unsafe_get_job_stage (impl_st.[job_reg tag]) = Impl.ENUM_stage__None ->
      forall reg, is_job_reg tag reg ->
             impl_st.[reg] = (Bits.zeroes (struct_sz Impl.S_job_t)).

    Definition ImplInvariant__ext_output_reg (tag: Tag) (impl_st: state_t) : Prop :=
      impl_st.[Impl.REG_clk] = (match tag with
                                | Tag0 => Ob~1
                                | Tag1 => Ob~0
                                end) ->
      unsafe_get_job_stage (impl_st.[job_reg tag]) <> Impl.ENUM_stage__None ->
      impl_st.[Impl.REG_ext_output_reg] = (option_to_maybe' Impl.sz None).

    Record ImplInvariant (impl_st: state_t) : Prop :=
      { impl_wf_state: WF_state Impl.reg_types impl_st
      ; impl_ext_ready_for_job: ImplInvariant__ext_ready_for_job impl_st
      ; impl_ext_output_reg: forall tag, ImplInvariant__ext_output_reg tag impl_st
      ; impl_pf__NONE_OR_INIT: forall tag, ImplInvariant__NONE_OR_INIT tag impl_st
      ; impl_pf_STAGE_F: forall tag, ImplInvariant__STAGE_F tag impl_st
      ; impl_pf_STAGE_G: forall tag, ImplInvariant__STAGE_G tag impl_st
      ; impl_pf_job_NONE_zeroed: forall tag, ImplInvariant__NONE_zeroed tag impl_st
      }.

End Invariants.

Ltac apply_impl_invariant :=
  match goal with
  | H: ImplInvariant ?impl_st
    |- WF_state Impl.reg_types ?impl_st =>
    solve[apply (impl_wf_state _ H)]
  end.
Ltac apply_wf_sigma :=
  match goal with
  | H: Impl.wf_sigma ?sigma
    |- WF_ext_sigma Impl.ext_fn_types (?sigma ?input) =>
    solve[apply (Impl.wf); assumption]
  end.

Ltac ri_solve :=
  match goal with
  | H: Impl.wf_sigma ?sigma
    |- WF_ext_sigma Impl.ext_fn_types (?sigma ?input) =>
    solve[apply (Impl.wf); assumption]
  | H: ImplInvariant ?impl_st
    |- WF_state Impl.reg_types ?impl_st =>
    solve[apply (impl_wf_state _ H)]
  | |- WF_int_fn_env Impl.reg_types Impl.ext_fn_types Impl.int_fn_env Impl.struct_env=>
    solve[apply Impl.typecheck_int_fns_Success]
  | |- _ => solve[auto with WF_auto solve_taint]
  end.

Section ORAAT_Infra.
  Section TODO_MOVE.

    Lemma taint_equiv_read0_refl:
      forall st env,
        taint_equiv_read0_state st st env.
    Proof.
      unfold taint_equiv_read0_state.
      intros; destruct_all_matches.
    Qed.

    Lemma taint_equiv_acc_state_refl:
      forall st env,
        taint_equiv_acc_state st st env.
    Proof.
      unfold taint_equiv_acc_state.
      intros; destruct_all_matches.
    Qed.

    Lemma taint_equiv_acc_state_empty:
      forall st1 st2,
        taint_equiv_acc_state st1 st2 SortedRegEnv.empty.
    Proof.
      unfold taint_equiv_acc_state.
      intros; destruct_all_matches.
      rewrite SortedRegEnv.opt_get_empty in Heqo. discriminate.
    Qed.

    Lemma taint_equiv_acc_state_set_read1:
      forall st1 st2 env reg taint_env,
      taint_set_to_prop st1 st2 taint_env ->
      no_writes_in_taint_set taint_env reg = true ->
      taint_equiv_acc_state st1 st2 env ->
      taint_equiv_acc_state st1 st2 (set_reg_taint env reg set_taint_read1).
    Proof.
      unfold taint_equiv_acc_state, set_reg_taint; intros.
      eapply taint_set_to_prop_no_write' with (reg := reg) in H; auto.
      specialize (H1 reg0).
      destruct_with_eqn (Nat.eqb reg reg0); simplify.
      - rewrite SortedRegEnv.update_correct_eq; simpl.
        destruct_all_matches; simpl in *.
      - rewrite SortedRegEnv.update_correct_neq by auto; simpl.
        destruct_all_matches; simpl in *.
    Qed.

    Lemma taint_set_to_prop_no_write_forall_in_list:
      forall taint_list st1 st2 res_taint_set reg ,
      taint_set_to_prop st1 st2 res_taint_set ->
      reg_in_taint_list' reg taint_list ->
      forallb (fun r => no_writes_in_taint_set res_taint_set r) taint_list = true ->
      st2.[reg] = st1.[reg].
    Proof.
      induction taint_list; intros * Htaint Hlist Hforall; consider reg_in_taint_list'.
      - discriminate.
      - simpl in *. apply orb_true_iff in Hlist. apply andb_true_iff in Hforall. propositional.
        destruct Hlist; simplify_nat.
        + eapply taint_set_to_prop_no_write'; eauto.
        + eauto.
    Qed.




  End TODO_MOVE.

  Definition reg_spec := state_t -> state_t -> ext_sigma_t -> vect_t -> Prop.
  Definition post_reg_spec := list (reg_t * reg_spec).
  Definition post_reg_spec_to_prop (spec: post_reg_spec)
            (st: state_t) (sigma: ext_sigma_t) (st': state_t) :=
    Forall (fun '(r, prop) => prop st st' sigma (unsafe_get_reg st' r)) spec.

  Definition custom_spec := state_t -> state_t -> ext_sigma_t -> Prop.

  Inductive CustomProps :=
  | DoInput__Job0__Stage
  | DoInput__Job1__Stage
  | DoStep0__Job0__Stage
  | DoStep0__ext_output_reg
  | DoStep0__finish_clk_inversion
  | DoStep1__Job1__Stage
  | DoStep1__ext_output_reg
  | DoStep1__finish_clk_inversion
  .

  Scheme Equality for CustomProps.

  Definition post_fail_spec := ext_sigma_t -> state_t -> Prop.

  Record postcond_t :=
    { Post_taint_set: result (option taint_env_t) unit;
      Post_custom: list (option CustomProps * custom_spec);
      Post_regs: post_reg_spec;
    }.

  Definition post_custom_to_prop
             (custom: list (option CustomProps * custom_spec))
             (st st': state_t) (sigma: ext_sigma_t) :Prop :=
    Forall (fun '(_, prop) => prop st st' sigma) custom.

  Definition postcond_to_Prop (postcond: postcond_t)
             (st st': state_t) (sigma: ext_sigma_t): Prop :=
    taint_set_to_prop st st' (Post_taint_set postcond) /\
    post_custom_to_prop (Post_custom postcond) st st' sigma /\
    post_reg_spec_to_prop postcond.(Post_regs) st sigma st'.

  Record rule_spec_t :=
    { Pre: state_t -> ext_sigma_t -> Prop;
      Post: postcond_t;
      FailInversion: post_fail_spec
    }.

  Lemma postcond_to_custom_lookup_name:
    forall postcond st st' sigma prop name,
      postcond_to_Prop postcond st st' sigma ->
      find (fun '(opt, _) =>
              match opt with
              | Some name' => CustomProps_beq name name'
              | None => false
              end) (Post_custom postcond) = Some (Some name, prop) ->
      prop st st' sigma.
  Proof.
    intros. unfold postcond_to_Prop in *. propositional.
    unfold post_custom_to_prop in *.
    rewrite Forall_forall in H3.
    apply find_some in H0; propositional.
    specialize H3 with (1 := H2). auto.
  Qed.

  Lemma postcond_to_Prop_lookup_reg:
    forall postcond st st' sigma reg prop,
      postcond_to_Prop postcond st st' sigma ->
      find (fun '(r, _) => Nat.eqb reg r) (Post_regs postcond) = Some (reg, prop) ->
      prop st st' sigma (unsafe_get_reg st' reg).
  Proof.
    intros. unfold postcond_to_Prop in *. propositional.
    unfold post_reg_spec_to_prop in *.
    rewrite Forall_forall in H4.
    apply find_some in H0; propositional.
    specialize H4 with (1 := H2). auto.
  Qed.



  Lemma postcond_to_Prop_implies_taint_set_to_Prop:
    forall postcond st1 st2 sigma,
      postcond_to_Prop postcond st1 st2 sigma ->
      taint_set_to_prop st1 st2 (Post_taint_set postcond).
  Proof.
    intros. destruct H; propositional.
  Qed.


  Lemma postcond_to_Prop_implies_Post_custom:
    forall postcond st1 st2 sigma,
      postcond_to_Prop postcond st1 st2 sigma ->
      post_custom_to_prop (Post_custom postcond) st1 st2 sigma.
  Proof.
    intros. destruct H; propositional.
  Qed.


  Definition oraat_rule_satisfies_spec' int_fn_env struct_env reg_types ext_fn_types
             (spec: rule_spec_t) (rl: action) : Prop :=
    forall st sigma,
    WF_state reg_types st ->
    WF_ext_sigma ext_fn_types sigma ->
    WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
    typecheck_rule reg_types ext_fn_types int_fn_env struct_env rl = Success 0 ->
    spec.(Pre) st sigma ->
    match
      oraat_interp_action sigma int_fn_env struct_env
            (safe_fuel int_fn_env (Datatypes.length int_fn_env) rl) st st true
            GenericGammaEmpty rl with
    | (true, opt) =>
        let st' := match opt with
                   | Some (_, st', _) => st'
                   | None => st
                   end in
        WF_state reg_types st' -> postcond_to_Prop (spec.(Post)) st st' sigma
        /\ match opt with
          | Some _ => True
          | None => (spec.(FailInversion) sigma st)
          end
    | _ => True
    end.


  Definition oraat_rule_satisfies_spec int_fn_env struct_env reg_types ext_fn_types
             (spec: rule_spec_t) (rl: action) : Prop :=
    forall st sigma,
    WF_state reg_types st ->
    WF_ext_sigma ext_fn_types sigma ->
    WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
    typecheck_rule reg_types ext_fn_types int_fn_env struct_env rl = Success 0 ->
    spec.(Pre) st sigma ->
    match oraat_interp_rule sigma int_fn_env struct_env st rl with
    | (true, st') =>
      WF_state reg_types st' ->
      postcond_to_Prop (spec.(Post)) st st' sigma
    | _ => True
    end.

  Lemma oraat_rule_satisfies_spec_implies:
    forall int_fn_env struct_env reg_types ext_fn_types spec rl,
    oraat_rule_satisfies_spec' int_fn_env struct_env reg_types ext_fn_types spec rl ->
    oraat_rule_satisfies_spec int_fn_env struct_env reg_types ext_fn_types spec rl.
  Proof.
    unfold oraat_rule_satisfies_spec, oraat_rule_satisfies_spec', oraat_interp_rule.
    intros; destruct_all_matches; propositional;
    specialize (H st sigma); destruct_all_matches; propositional.
  Qed.


  Lemma oraat_interp_scheduler'_cons__spec:
    forall {rule_name_t: Type}
    sigma int_fn_env struct_env reg_types ext_fn_types
    (st st'': state_t) (rules: rule_name_t -> action) rl s
    (rl_spec: rule_spec_t),
    WF_state reg_types st ->
    WF_ext_sigma ext_fn_types sigma ->
    WF_int_fn_env reg_types ext_fn_types int_fn_env struct_env ->
    typecheck_rule reg_types ext_fn_types int_fn_env struct_env (rules rl) = Success 0 ->
    oraat_rule_satisfies_spec' int_fn_env struct_env reg_types ext_fn_types rl_spec (rules rl) ->
    rl_spec.(Pre) st sigma ->
    oraat_interp_scheduler' sigma int_fn_env struct_env rules st true (Cons rl s) = (true, st'') ->
    exists st', postcond_to_Prop rl_spec.(Post) st st' sigma /\
      oraat_interp_scheduler' sigma int_fn_env struct_env rules st' true s = (true, st'') /\
      WF_state reg_types st'.
  Proof.
    intros * Hst Hext_sigma Hint_fn_env Htype Hspec Hpre Horaat. simpl in *.
    apply oraat_rule_satisfies_spec_implies in Hspec.
    consider oraat_rule_satisfies_spec.
    specialize Hspec with (1 := Hst) (2 := Hext_sigma) (3 := Hint_fn_env) (4 := Htype)
                          (5 := Hpre).
    destruct_match_pairs.
    specialize @oraat_interp_scheduler'_is_safe_generalizes with (1 := Horaat); propositional.
    assert (WF_state reg_types s0) as Hwf_st' by (eapply oraat_interp_rule_safety; eauto).

    consider oraat_interp_rule. bash_destruct Heqp; eauto.
  Qed.

End ORAAT_Infra.

Section RuleSpecs.
  Notation __oraat_rule_satisfies_spec := (oraat_rule_satisfies_spec' Impl.int_fn_env Impl.struct_env Impl.reg_types Impl.ext_fn_types).

  Record rule_spec_t' :=
    { RuleSpec_rl: rule;
      RuleSpec_spec: rule_spec_t;
      RuleSpec_pf: __oraat_rule_satisfies_spec RuleSpec_spec RuleSpec_rl
    }.

  Section InteractWithWorld.
    Definition RlSpec__InteractWithWorld__Post : postcond_t :=
      {| Post_taint_set := taint_rule_from_empty Impl.int_fn_env (Impl.rules Impl.InteractWithWorld);
         Post_custom := [];
         Post_regs := []
      |}.

    Definition RlSpec__InteractWithWorld : rule_spec_t :=
      {| Pre := fun _ _ => True;
         Post := RlSpec__InteractWithWorld__Post;
         FailInversion := fun _ _ => True
      |}.

  End InteractWithWorld.

  Section DoInput.
    Definition RlSpec__DoInput__Post : postcond_t :=
      {| Post_taint_set := taint_rule_from_empty Impl.int_fn_env (Impl.rules Impl.DoInput);
         Post_custom :=
           [(Some DoInput__Job0__Stage,
             fun st st' sigma =>
               (st'.[Impl.REG_job0] <> st.[Impl.REG_job0]) \/
               (st.[Impl.REG_ext_ready_for_job] = option_to_maybe' 1 (Some [false]) /\
                (unsafe_get_field (struct_fields Impl.S_maybe_job_req) FIELD_maybe_valid (success_or_default (sigma Impl.EXTFN_GetJob Ob~0) Ob)) = Ob~1) ->
               unsafe_get_job_stage st'.[Impl.REG_job0] = Impl.ENUM_stage__INIT
            );
           (Some DoInput__Job1__Stage,
             fun st st' sigma =>
               (st'.[Impl.REG_job1] <> st.[Impl.REG_job1]) \/
               (st.[Impl.REG_ext_ready_for_job] = option_to_maybe' 1 (Some [true]) /\
               (unsafe_get_field (struct_fields Impl.S_maybe_job_req) FIELD_maybe_valid (success_or_default (sigma Impl.EXTFN_GetJob Ob~1) Ob) = Ob~1)) ->
               unsafe_get_job_stage st'.[Impl.REG_job1] = Impl.ENUM_stage__INIT
            )
           ];
         Post_regs :=
            [(Impl.REG_job0,
             fun st st' sigma v =>
               v = if bits_eq (st.[Impl.REG_ext_ready_for_job]) (option_to_maybe' 1 (Some [false]))
                      && bits_eq (unsafe_get_field (struct_fields Impl.S_maybe_job_req) FIELD_maybe_valid (success_or_default (sigma Impl.EXTFN_GetJob Ob~0) Ob)) Ob~1 then
                     v
                   else st.[Impl.REG_job0]
            )
           ;(Impl.REG_job1,
             fun st st' sigma v =>
               v = if bits_eq (st.[Impl.REG_ext_ready_for_job]) (option_to_maybe' 1 (Some [true]))
                      && bits_eq (unsafe_get_field (struct_fields Impl.S_maybe_job_req) FIELD_maybe_valid (success_or_default (sigma Impl.EXTFN_GetJob Ob~1) Ob)) Ob~1 then
                     v
                   else st.[Impl.REG_job1]
            )]
      |}.

    Definition RlSpec__DoInput : rule_spec_t :=
      {| Pre := fun _ _ => True;
         Post := RlSpec__DoInput__Post;
         FailInversion := fun _ _ => True
      |}.

  End DoInput.

  Section StepBoxes.
    Definition RlSpec__StepBoxes__Post : postcond_t :=
      {| Post_taint_set := taint_rule_from_empty Impl.int_fn_env (Impl.rules Impl.StepBoxes);
         Post_custom := [];
         Post_regs := []
      |}.


    Definition RlSpec__StepBoxes : rule_spec_t :=
      {| Pre := fun _ _ => True;
         Post := RlSpec__StepBoxes__Post;
         FailInversion := fun _ _ => True
      |}.

  End StepBoxes.

  Section DoStep0.
    Definition RlSpec__DoStep0__Post : postcond_t :=
      {| Post_taint_set := taint_rule_from_empty Impl.int_fn_env (Impl.rules Impl.DoStep0);
         Post_custom := [(Some DoStep0__Job0__Stage,
                          fun st st' sigma =>
                            unsafe_get_job_stage st'.[Impl.REG_job0] <> unsafe_get_job_stage st.[Impl.REG_job0] ->
                            unsafe_get_job_stage st'.[Impl.REG_job0] =
                              if bits_eq (unsafe_get_job_stage st.[Impl.REG_job0]) Impl.ENUM_stage__None then
                                Impl.ENUM_stage__None (* shouldn't happen *)
                              else if bits_eq (unsafe_get_job_stage st.[Impl.REG_job0]) Impl.ENUM_stage__INIT then
                                Impl.ENUM_stage__F
                              else if bits_eq (unsafe_get_job_stage st.[Impl.REG_job0]) Impl.ENUM_stage__F then
                                Impl.ENUM_stage__G
                              else if bits_eq (unsafe_get_job_stage st.[Impl.REG_job0]) Impl.ENUM_stage__G then
                                Impl.ENUM_stage__None
                              else Ob (* ERROR *))
                        ;(Some DoStep0__ext_output_reg,
                           fun st st' sigma =>
                             unsafe_get_job_stage st'.[Impl.REG_job0] = Impl.ENUM_stage__None ->
                             unsafe_get_job_stage st.[Impl.REG_job0] <> Impl.ENUM_stage__None  ->
                             (* st.[Impl.REG_clk] = Ob~0 -> *)
                             unsafe_get_field (struct_fields Impl.S_maybe_sz) FIELD_maybe_valid st'.[Impl.REG_ext_output_reg0] = Ob~1)
                        ;(Some DoStep0__finish_clk_inversion,
                           fun st st' sigma =>
                             unsafe_get_job_stage st'.[Impl.REG_job0] = Impl.ENUM_stage__None ->
                             unsafe_get_job_stage st.[Impl.REG_job0] <> Impl.ENUM_stage__None  ->
                             st.[Impl.REG_clk] = Ob~0)
                        ];
         Post_regs :=
           [(Impl.REG_job0,
             fun st st' sigma v =>
               v = if bits_eq (unsafe_get_job_stage st.[Impl.REG_job0]) Impl.ENUM_stage__None ||
                      bits_eq (unsafe_get_job_stage v) (unsafe_get_job_stage st.[Impl.REG_job0]) then
                     st.[Impl.REG_job0]
                   else if bits_eq (unsafe_get_job_stage v) Impl.ENUM_stage__None then
                      zeroes (struct_sz Impl.S_job_t)
                   else v)
           ;(Impl.REG_job0', fun st st' sigma v => v = st'.[Impl.REG_job0])
           ;(Impl.REG_ext_output_reg0,
               fun st st' sigma v =>
                 unsafe_get_job_stage st'.[Impl.REG_job0] <> Impl.ENUM_stage__None \/
                 unsafe_get_job_stage st.[Impl.REG_job0] = Impl.ENUM_stage__None  \/
                 st.[Impl.REG_clk] <> Ob~0 ->
                 v = option_to_maybe' Impl.sz None
            )
           ;(Impl.G0Box.REG_valid0,
               fun st st' sigma v =>
                 v = if bits_eq (unsafe_get_job_stage st'.[Impl.REG_job0]) Impl.ENUM_stage__G then
                       v
                     else if bits_eq (unsafe_get_job_stage st.[Impl.REG_job0]) Impl.ENUM_stage__G &&
                             bits_eq (unsafe_get_job_stage st'.[Impl.REG_job0]) Impl.ENUM_stage__None then
                            Ob~0
                     else st.[Impl.G0Box.REG_valid0]
            )
           ;(Impl.F0Box.REG_valid0,
               fun st st' sigma v =>
                 v = if bits_eq (unsafe_get_job_stage st'.[Impl.REG_job0]) Impl.ENUM_stage__F then
                       v
                     else if bits_eq (unsafe_get_job_stage st.[Impl.REG_job0]) Impl.ENUM_stage__F &&
                             bits_eq (unsafe_get_job_stage st'.[Impl.REG_job0]) Impl.ENUM_stage__G then
                            Ob~0
                     else st.[Impl.F0Box.REG_valid0]
            )
           ]
      |}.

    Definition RlSpec__DoStep0 : rule_spec_t :=
      {| Pre := fun _ _ => True;
         Post := RlSpec__DoStep0__Post;
         FailInversion := fun _ _ => False
      |}.


  End DoStep0.

  Section DoStep1.
    Definition RlSpec__DoStep1__Post : postcond_t :=
      {| Post_taint_set := taint_rule_from_empty Impl.int_fn_env (Impl.rules Impl.DoStep1);
         Post_custom := [(Some DoStep1__Job1__Stage,
                          fun st st' sigma =>
                            unsafe_get_job_stage st'.[Impl.REG_job1] <> unsafe_get_job_stage st.[Impl.REG_job1] ->
                            unsafe_get_job_stage st'.[Impl.REG_job1] =
                              if bits_eq (unsafe_get_job_stage st.[Impl.REG_job1]) Impl.ENUM_stage__None then
                                Impl.ENUM_stage__None (* shouldn't happen *)
                              else if bits_eq (unsafe_get_job_stage st.[Impl.REG_job1]) Impl.ENUM_stage__INIT then
                                Impl.ENUM_stage__F
                              else if bits_eq (unsafe_get_job_stage st.[Impl.REG_job1]) Impl.ENUM_stage__F then
                                Impl.ENUM_stage__G
                              else if bits_eq (unsafe_get_job_stage st.[Impl.REG_job1]) Impl.ENUM_stage__G then
                                Impl.ENUM_stage__None
                              else [] (* ERROR *) )
                        ;(Some DoStep1__ext_output_reg,
                           fun st st' sigma =>
                             unsafe_get_job_stage st'.[Impl.REG_job1] = Impl.ENUM_stage__None ->
                             unsafe_get_job_stage st.[Impl.REG_job1] <> Impl.ENUM_stage__None ->
                             (* st.[Impl.REG_clk] = Ob~1 -> *)
                             unsafe_get_field (struct_fields Impl.S_maybe_sz) FIELD_maybe_valid st'.[Impl.REG_ext_output_reg1] = Ob~1)
                        ;(Some DoStep1__finish_clk_inversion,
                           fun st st' sigma =>
                             unsafe_get_job_stage st'.[Impl.REG_job1] = Impl.ENUM_stage__None ->
                             unsafe_get_job_stage st.[Impl.REG_job1] <> Impl.ENUM_stage__None  ->
                             st.[Impl.REG_clk] = Ob~1)
                        ];
         Post_regs :=
           [(Impl.REG_job1, fun st st' sigma v =>
                              v = if bits_eq (unsafe_get_job_stage st.[Impl.REG_job1]) Impl.ENUM_stage__None ||
                                       bits_eq (unsafe_get_job_stage v) (unsafe_get_job_stage st.[Impl.REG_job1]) then
                                    st.[Impl.REG_job1]
                                  else if bits_eq (unsafe_get_job_stage v) Impl.ENUM_stage__None then
                                     zeroes (struct_sz Impl.S_job_t)
                                  else v)
           ;(Impl.REG_job1', fun st st' sigma v => v = st'.[Impl.REG_job1])
           ;(Impl.REG_ext_output_reg1,
               fun st st' sigma v =>
                 unsafe_get_job_stage st'.[Impl.REG_job1] <> Impl.ENUM_stage__None \/
                 unsafe_get_job_stage st.[Impl.REG_job1] = Impl.ENUM_stage__None \/
                 st.[Impl.REG_clk] <> Ob~1 ->
                 v = option_to_maybe' Impl.sz None
            )
           ;(Impl.G1Box.REG_valid0,
               fun st st' sigma v =>
                 v = if bits_eq (unsafe_get_job_stage st'.[Impl.REG_job1]) Impl.ENUM_stage__G then
                       v
                     else if bits_eq (unsafe_get_job_stage st.[Impl.REG_job1]) Impl.ENUM_stage__G &&
                             bits_eq (unsafe_get_job_stage st'.[Impl.REG_job1]) Impl.ENUM_stage__None then
                            Ob~0
                     else st.[Impl.G1Box.REG_valid0]
           )
           ;(Impl.F1Box.REG_valid0,
               fun st st' sigma v =>
                 v = if bits_eq (unsafe_get_job_stage st'.[Impl.REG_job1]) Impl.ENUM_stage__F then
                       v
                     else if bits_eq (unsafe_get_job_stage st.[Impl.REG_job1]) Impl.ENUM_stage__F &&
                             bits_eq (unsafe_get_job_stage st'.[Impl.REG_job1]) Impl.ENUM_stage__G then
                            Ob~0
                     else st.[Impl.F1Box.REG_valid0]
            )
           ]
      |}.

    Definition RlSpec__DoStep1 : rule_spec_t :=
      {| Pre := fun _ _ => True;
         Post := RlSpec__DoStep1__Post;
         FailInversion := fun _ _ => False
      |}.

  End DoStep1.

  Section UpdateReady.
    Definition RlSpec__UpdateReady__Post : postcond_t :=
      {| Post_taint_set := taint_rule_from_empty Impl.int_fn_env (Impl.rules Impl.UpdateReady);
         Post_custom := [];
         Post_regs :=
           [(Impl.REG_clk, (fun st st' sigma v => v = neg (st.[Impl.REG_clk])))
           ;(Impl.REG_ext_output_reg,
             (fun st st' sigma v =>
                v = if bits_eq (st.[Impl.REG_clk]) [false] then
                      st.[Impl.REG_ext_output_reg0]
                    else
                      st.[Impl.REG_ext_output_reg1]))
           ; (Impl.REG_ext_ready_for_job,
                fun st st' sigma v =>
                v = if bits_eq (unsafe_get_job_stage (st.[Impl.REG_job0'])) Impl.ENUM_stage__None then
                      (option_to_maybe' 1 (Some Ob~0))
                    else if bits_eq (unsafe_get_job_stage (st.[Impl.REG_job1'])) Impl.ENUM_stage__None then
                      (option_to_maybe' 1 (Some Ob~1))
                    else (option_to_maybe' 1 None)
             )
           ]
      |}.

    Definition RlSpec__UpdateReady : rule_spec_t :=
      {| Pre := fun _ _ => True;
         Post := RlSpec__UpdateReady__Post;
         FailInversion := fun _ _ => True
      |}.



  End UpdateReady.

End RuleSpecs.
Notation __oraat_rule_satisfies_spec := (oraat_rule_satisfies_spec' Impl.int_fn_env Impl.struct_env Impl.reg_types Impl.ext_fn_types).

Module Type ImplementationProofs_Sig.
  Parameter RlSatisfiesSpec__InteractWithWorld :
    __oraat_rule_satisfies_spec RlSpec__InteractWithWorld (Impl.rules Impl.InteractWithWorld).
  Parameter RlSatisfiesSpec__DoInput :
      __oraat_rule_satisfies_spec RlSpec__DoInput (Impl.rules Impl.DoInput).
  Parameter RlSatisfiesSpec__StepBoxes :
      __oraat_rule_satisfies_spec RlSpec__StepBoxes (Impl.rules Impl.StepBoxes).
  Parameter RlSatisfiesSpec__DoStep0 :
      __oraat_rule_satisfies_spec RlSpec__DoStep0 (Impl.rules Impl.DoStep0).
  Parameter RlSatisfiesSpec__DoStep1 :
      __oraat_rule_satisfies_spec RlSpec__DoStep1 (Impl.rules Impl.DoStep1).
  Parameter RlSatisfiesSpec__UpdateReady :
      __oraat_rule_satisfies_spec RlSpec__UpdateReady (Impl.rules Impl.UpdateReady).

End ImplementationProofs_Sig.
Ltac solve_bits :=
  repeat match goal with
  | H: bits_eq ?x ?y = true |- ?x = ?y =>
    apply bits_eq_iff in H; assumption
  | H: bits_eq ?x ?y = true |- ?y = ?x =>
    apply bits_eq_iff in H; symmetry; assumption
  | H: bits_eq ?x ?y = false |- ?x <> ?y =>
    apply bits_neq_iff in H; assumption
  | H: bits_eq ?y ?x = false |- ?x <> ?y =>
    apply bits_neq_iff in H; solve[auto]
  | H1: bits_eq ?x ?y = false,
    H2: bits_eq ?y ?x = true |- _ =>
    rewrite bits_eq_sym in H1; rewrite H1 in H2; discriminate
  end.


Module ScheduleProofs (ImplProofs: ImplementationProofs_Sig).
  Include ImplProofs.

  Section Specs.
    Definition Spec__InteractWithWorld : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.InteractWithWorld;
         RuleSpec_spec := RlSpec__InteractWithWorld;
         RuleSpec_pf := RlSatisfiesSpec__InteractWithWorld
      |}.

    Definition Spec__DoInput : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.DoInput;
         RuleSpec_spec := RlSpec__DoInput;
         RuleSpec_pf := RlSatisfiesSpec__DoInput
      |}.

    Definition Spec__StepBoxes : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.StepBoxes;
         RuleSpec_spec := RlSpec__StepBoxes;
         RuleSpec_pf := RlSatisfiesSpec__StepBoxes
      |}.


     Definition Spec__Step0 : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.DoStep0;
         RuleSpec_spec := RlSpec__DoStep0;
         RuleSpec_pf := RlSatisfiesSpec__DoStep0
      |}.

    Definition Spec__Step1 : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.DoStep1;
         RuleSpec_spec := RlSpec__DoStep1;
         RuleSpec_pf := RlSatisfiesSpec__DoStep1
      |}.

    Definition Spec__UpdateReady : rule_spec_t' :=
      {| RuleSpec_rl := Impl.rules Impl.UpdateReady;
         RuleSpec_spec := RlSpec__UpdateReady;
         RuleSpec_pf := RlSatisfiesSpec__UpdateReady
      |}.

  End Specs.

  Lemma ImplInvariant_implies_step_Success:
    forall impl_st external_world_state_t (ext_st: external_world_state_t) input_machine sigma,
    Impl.wf_sigma sigma ->
    ImplInvariant impl_st ->
    match Impl.step sigma input_machine impl_st ext_st with
    | Success _ => True
    | Failure _ => False
    end.
  Proof.
    intros * Hsigma Hinv.
    consider Impl.step. unfold step. repeat destruct_match; auto.
    consider Impl.koika_step. consider Impl.koika_step'.
    simplify_result.
    specialize @typecheck_schedule_correct with
        (1 := Impl.typecheck_schedule_Success)
        (ext_sigma := sigma (i_get_output input_machine ext_st)) (st := impl_st).
    rewrite Heqr0. intros Hcorrect.
    apply Hcorrect; auto.
    - apply impl_wf_state; auto.
    - apply Impl.wf; auto.
    - unfold WF_int_fn_env.
      apply Impl.typecheck_int_fns_Success.
  Qed.


  Lemma Step_WF_Log:
    forall impl_st (sigma: input_t -> ext_sigma_t) input log ,
      Impl.wf_sigma sigma ->
      ImplInvariant impl_st ->
      interp_scheduler (sigma input) Impl.int_fn_env Impl.struct_env impl_st Impl.rules Impl.schedule = Success log ->
      WF_log Impl.reg_types log.
  Proof.
    intros.
    eapply typecheck_schedule_correct'_WF_log with (1 := Impl.typecheck_schedule_Success); eauto; try ri_solve.
  Qed.

  Ltac step_oraat_scheduler Hsched RlSpec NewSt NewPostCond NewSched NewWfSt :=
    eapply oraat_interp_scheduler'_cons__spec with
      (rl_spec := RlSpec.(RuleSpec_spec)) (reg_types := Impl.reg_types) (ext_fn_types := Impl.ext_fn_types)
    in Hsched; [ | | | | |  apply RlSpec.(RuleSpec_pf) | ]; eauto;
    [ destruct Hsched as (NewSt & NewPostCond & NewSched & NewWfSt)
                      | simpl; try ri_solve ..].
  Ltac rewrite_with_custom name postcond :=
    rewrite (postcond_to_custom_lookup_name _ _ _ _ _ name postcond eq_refl).
  Ltac rewrite_with_custom_in H name postcond :=
    rewrite (postcond_to_custom_lookup_name _ _ _ _ _ name postcond eq_refl) in H.


  Ltac rewrite_with_reg_spec reg postcond :=
    rewrite (postcond_to_Prop_lookup_reg _ _ _ _ reg _ postcond eq_refl).
  Ltac rewrite_with_reg_spec_in H reg postcond :=
    rewrite (postcond_to_Prop_lookup_reg _ _ _ _ reg _ postcond eq_refl) in H.

  Ltac rewrite_no_write reg postcond :=
    rewrite (taint_set_to_prop_no_write' _ _ _ reg
                                         (postcond_to_Prop_implies_taint_set_to_Prop _ _ _ _  postcond) eq_refl).

  Ltac rewrite_no_write_in H reg postcond :=
    rewrite (taint_set_to_prop_no_write' _ _ _ reg
                                         (postcond_to_Prop_implies_taint_set_to_Prop _ _ _ _  postcond) eq_refl) in H.

  Ltac rewrite_no_write_forall reg postcond :=
    match goal with
    | H: reg_in_taint_list' reg _ |- _ =>
      rewrite (taint_set_to_prop_no_write_forall_in_list
               _ _ _ _ reg
              (postcond_to_Prop_implies_taint_set_to_Prop _ _ _ _  postcond) H eq_refl)
    end.

  Ltac split_ors_in H :=
    match type of H with
    | _ \/ _ =>
      destruct H as [H | H]; [ | try split_ors_in H]
    end.


  Lemma Invariant_step_preserved'':
    forall impl_st (sigma: input_t -> ext_sigma_t) input log,
      Impl.wf_sigma sigma ->
      ImplInvariant impl_st ->
      interp_scheduler (sigma input) Impl.int_fn_env Impl.struct_env impl_st Impl.rules Impl.schedule = Success log ->
      WF_log Impl.reg_types log ->
      WF_state Impl.reg_types (commit_update impl_st log) ->
      ImplInvariant (commit_update impl_st log) /\
      ImplPostCond impl_st (commit_update impl_st log) (sigma input).
  Proof.
    intros * pf_wf_sigma HInv Hsched Hwf_log Hwf_state.
    assert (oraat_interp_scheduler' (sigma input) Impl.int_fn_env Impl.struct_env Impl.rules
            (commit_update impl_st log_empty) true Impl.schedule = (true, commit_update impl_st log))
      as Horaat.
    { specialize schedule_does_not_conflict_implies with
          (1 := Impl.oraat_schedule_does_not_conflict); propositional.
        eapply oraat_interp_schedule'_correct with
            (reg_types := Impl.reg_types) (ext_fn_types := Impl.ext_fn_types)
            (taint := SortedRegEnv.empty) (taint' := taint); auto; try ri_solve.
        - apply taint_env_approximates_log_empty.
    }

    rewrite commit_update_empty in Horaat.
    consider Impl.schedule. consider interp_scheduler.

    step_oraat_scheduler Horaat Spec__InteractWithWorld St__World Post__World Sched__World WF__World.
    step_oraat_scheduler Sched__World Spec__DoInput St__Input Post__Input Sched__Input WF__Input.
    step_oraat_scheduler Sched__Input Spec__StepBoxes St__Boxes Post__Boxes Sched__Boxes WF__Boxes.
    step_oraat_scheduler Sched__Boxes Spec__Step0 St__Step0 Post__Step0 Sched__Step0 WF__Step0.
    step_oraat_scheduler Sched__Step0 Spec__Step1 St__Step1 Post__Step1 Sched__Step1 WF__Step1.
    step_oraat_scheduler Sched__Step1 Spec__UpdateReady St__UpdateReady Post__UpdateReady Sched__UpdateReady WF__UpdateReady.
    simpl in Sched__UpdateReady. simplify_tupless.

    constructor; auto; [ constructor | ]; auto.
    - unfold ImplInvariant__ext_ready_for_job.
      rewrite_with_reg_spec Impl.REG_ext_ready_for_job Post__UpdateReady.
      rewrite_no_write Impl.REG_job0 Post__UpdateReady.
      rewrite_no_write Impl.REG_job1 Post__UpdateReady.
      rewrite_no_write Impl.REG_job0 Post__Step1.
      rewrite_no_write Impl.REG_job0' Post__Step1.
      rewrite_with_reg_spec Impl.REG_job1' Post__Step1.
      rewrite_with_reg_spec Impl.REG_job0' Post__Step0.
      reflexivity.
    - intros tag. unfold ImplInvariant__ext_output_reg.
      rewrite_with_reg_spec Impl.REG_clk Post__UpdateReady.
      rewrite_with_reg_spec Impl.REG_ext_output_reg Post__UpdateReady.
      rewrite_no_write Impl.REG_ext_output_reg0 Post__Step1.
      rewrite_no_write Impl.REG_clk Post__Step1.
      rewrite_no_write Impl.REG_clk Post__Step0.
      rewrite_no_write Impl.REG_clk Post__Boxes.
      rewrite_no_write Impl.REG_clk Post__Input.
      rewrite_no_write Impl.REG_clk Post__World.
      destruct tag; simpl.
      + rewrite_no_write Impl.REG_job0 Post__UpdateReady.
        rewrite_no_write Impl.REG_job0 Post__Step1.
        intros * Hclk Hstage.
        apply f_equal with (f := neg) in Hclk; simpl in Hclk.
        rewrite neg_involutive in Hclk. rewrite Hclk. simpl.
        rewrite_with_reg_spec Impl.REG_ext_output_reg0 Post__Step0; auto.
      + rewrite_no_write Impl.REG_job1 Post__UpdateReady.
        intros * Hclk Hstage.
        rewrite_with_reg_spec Impl.REG_ext_output_reg1 Post__Step1; auto.
        assert_if_eq_as Hclk' false.
        { apply f_equal with (f := neg) in Hclk; simpl in Hclk.
          rewrite neg_involutive in Hclk.
          rewrite Hclk; auto.
        }
        reflexivity.
    - intros tag. unfold ImplInvariant__NONE_OR_INIT.
      destruct tag; simpl.
      + rewrite_no_write Impl.REG_job0 Post__UpdateReady.
        rewrite_no_write Impl.REG_job0 Post__Step1.
        intros Hstage reg Htaint_reg; revert Hstage.
        rewrite_no_write_forall reg Post__UpdateReady.
        rewrite_no_write_forall reg Post__Step1.
        unfold reg_in_taint_list' in Htaint_reg; simpl in Htaint_reg; repeat rewrite orb_true_iff in Htaint_reg.
        split_ors_in Htaint_reg; try discriminate; simplify_nat; subst.
        * intros; rewrite_with_reg_spec Impl.F0Box.REG_valid0 Post__Step0.
          destruct_match.
          { apply bits_eq_iff in Heqb.  rewrite Heqb in Hstage. split_cases; discriminate. }
          { destruct (bits_eq (unsafe_get_job_stage St__Boxes.[Impl.REG_job0])
                              (unsafe_get_job_stage St__Step0.[Impl.REG_job0])) eqn:Hchange.
            { apply bits_eq_iff in Hchange.
              rewrite<-Hchange in *.
              destruct_match; auto.
              rewrite_no_write Impl.F0Box.REG_valid0 Post__Boxes.
              rewrite_no_write Impl.F0Box.REG_valid0 Post__Input.
              rewrite_no_write Impl.F0Box.REG_valid0 Post__World.
              rewrite (impl_pf__NONE_OR_INIT _ HInv Tag0); simpl; auto.
              rewrite_no_write_in Hstage Impl.REG_job0 Post__Boxes.
              rewrite_with_reg_spec_in Hstage Impl.REG_job0 Post__Input.
              rewrite_no_write_in Hstage Impl.REG_ext_ready_for_job Post__World.
              rewrite_no_write_in Hstage Impl.REG_job0 Post__World.
              destruct_matches_in_hyp Hstage; auto.
              rewrite (impl_ext_ready_for_job _ HInv) in Heqb1.
              bash_destruct Heqb1. left; solve_bits.
            }
            { apply bits_neq_iff in Hchange.
              rewrite_with_custom_in Hstage DoStep0__Job0__Stage Post__Step0; [ | solve_bits; auto].
              destruct_match; solve_bits; auto.
              rewrite_no_write_in Hstage Impl.REG_job0 Post__Boxes.
              rewrite_no_write Impl.F0Box.REG_valid0 Post__Boxes.
              rewrite_no_write Impl.F0Box.REG_valid0 Post__Input.
              rewrite_no_write Impl.F0Box.REG_valid0 Post__World.
              bash_destruct Hstage; destruct Hstage; solve_bits; try discriminate; try solve[destruct Hstage; discriminate].
              { rewrite (impl_pf__NONE_OR_INIT _ HInv Tag0); simpl; auto.
                rewrite_with_reg_spec_in Heqb1 Impl.REG_job0 Post__Input.
                rewrite_no_write_in Heqb1 Impl.REG_ext_ready_for_job Post__World.
                rewrite_no_write_in Heqb1 Impl.REG_job0 Post__World.
                rewrite (impl_ext_ready_for_job _ HInv) in Heqb1.
                bash_destruct Heqb1; try (solve[left; solve_bits]); discriminate.
              }
              { destruct_with_eqn (bits_eq St__Input.[Impl.REG_job0] St__World.[Impl.REG_job0]).
                { apply bits_eq_iff in Heqb5. rewrite Heqb5 in *.
                  rewrite_no_write_in Heqb4 Impl.REG_job0 Post__World.
                  rewrite (impl_pf_STAGE_G _ HInv Tag0); simpl; solve_bits; auto.
                }
                { apply bits_neq_iff in Heqb5.
                  rewrite_with_custom_in Heqb4 DoInput__Job0__Stage Post__Input; [ | solve_bits]; auto.
                  discriminate.
                }
              }
            }
          }
        * intros; rewrite_with_reg_spec Impl.G0Box.REG_valid0 Post__Step0.
          destruct_match.
          { apply bits_eq_iff in Heqb.  rewrite Heqb in Hstage. split_cases; discriminate. }
          { destruct (bits_eq (unsafe_get_job_stage St__Boxes.[Impl.REG_job0])
                              (unsafe_get_job_stage St__Step0.[Impl.REG_job0])) eqn:Hchange.
            { apply bits_eq_iff in Hchange.
              rewrite<-Hchange in *.
              destruct_match; auto.
              rewrite_no_write Impl.G0Box.REG_valid0 Post__Boxes.
              rewrite_no_write Impl.G0Box.REG_valid0 Post__Input.
              rewrite_no_write Impl.G0Box.REG_valid0 Post__World.
              rewrite (impl_pf__NONE_OR_INIT _ HInv Tag0); simpl; auto.
              rewrite_no_write_in Hstage Impl.REG_job0 Post__Boxes.
              rewrite_with_reg_spec_in Hstage Impl.REG_job0 Post__Input.
              rewrite_no_write_in Hstage Impl.REG_ext_ready_for_job Post__World.
              rewrite_no_write_in Hstage Impl.REG_job0 Post__World.
              destruct_matches_in_hyp Hstage; auto.
              rewrite (impl_ext_ready_for_job _ HInv) in Heqb1.
              bash_destruct Heqb1. left; solve_bits.
            }
            { apply bits_neq_iff in Hchange.
              rewrite_with_custom_in Hstage DoStep0__Job0__Stage Post__Step0; [ | solve_bits; auto].
              destruct_match; solve_bits; auto.
              rewrite_no_write Impl.G0Box.REG_valid0 Post__Boxes.
              rewrite_no_write Impl.G0Box.REG_valid0 Post__Input.
              rewrite_no_write Impl.G0Box.REG_valid0 Post__World.
              bash_destruct Hstage; destruct Hstage; solve_bits; try discriminate; try solve[destruct Hstage; discriminate].
              { rewrite (impl_pf__NONE_OR_INIT _ HInv Tag0); simpl; auto.
                rewrite_no_write_in Heqb1 Impl.REG_job0 Post__Boxes.
                rewrite_with_reg_spec_in Heqb1 Impl.REG_job0 Post__Input.
                rewrite_no_write_in Heqb1 Impl.REG_ext_ready_for_job Post__World.
                rewrite_no_write_in Heqb1 Impl.REG_job0 Post__World.
                rewrite (impl_ext_ready_for_job _ HInv) in Heqb1.
                bash_destruct Heqb1; try (solve[left; solve_bits]); discriminate.
              }
              { apply bits_eq_iff in Heqb4.
                rewrite Heqb4 in Hchange. simpl in Heqb0.
                rewrite_with_custom_in Heqb0 DoStep0__Job0__Stage Post__Step0; [ | rewrite_solve ].
                rewrite Heqb4 in Heqb0. simpl in Heqb0. discriminate.
              }
            }
          }
      + rewrite_no_write Impl.REG_job1 Post__UpdateReady.
        intros Hstage reg Htaint_reg; revert Hstage.
        rewrite_no_write_forall reg Post__UpdateReady.
        unfold reg_in_taint_list' in Htaint_reg; simpl in Htaint_reg; repeat rewrite orb_true_iff in Htaint_reg.
        split_ors_in Htaint_reg; try discriminate; simplify_nat; subst.
        * intros; rewrite_with_reg_spec Impl.F1Box.REG_valid0 Post__Step1.
          destruct_match.
          { apply bits_eq_iff in Heqb. rewrite Heqb in Hstage. split_cases; discriminate. }
          { destruct (bits_eq (unsafe_get_job_stage St__Step0.[Impl.REG_job1])
                              (unsafe_get_job_stage St__Step1.[Impl.REG_job1])) eqn:Hchange.
            { apply bits_eq_iff in Hchange.
              rewrite<-Hchange in *.
              destruct_match; auto.
              rewrite_no_write Impl.F1Box.REG_valid0 Post__Step0.
              rewrite_no_write Impl.F1Box.REG_valid0 Post__Boxes.
              rewrite_no_write Impl.F1Box.REG_valid0 Post__Input.
              rewrite_no_write Impl.F1Box.REG_valid0 Post__World.
              rewrite (impl_pf__NONE_OR_INIT _ HInv Tag1); simpl; auto.
              rewrite_no_write_in Hstage Impl.REG_job1 Post__Step0.
              rewrite_no_write_in Hstage Impl.REG_job1 Post__Boxes.
              rewrite_with_reg_spec_in Hstage Impl.REG_job1 Post__Input.
              rewrite_no_write_in Hstage Impl.REG_ext_ready_for_job Post__World.
              rewrite_no_write_in Hstage Impl.REG_job1 Post__World.
              destruct_matches_in_hyp Hstage; auto.
              rewrite (impl_ext_ready_for_job _ HInv) in Heqb1.
              bash_destruct Heqb1. left; solve_bits.
            }
            { apply bits_neq_iff in Hchange.
              rewrite_with_custom_in Hstage DoStep1__Job1__Stage Post__Step1; [ | solve_bits; auto].
              destruct_match; solve_bits; auto.
              rewrite_no_write_in Hstage Impl.REG_job1 Post__Step0.
              rewrite_no_write_in Hstage Impl.REG_job1 Post__Boxes.
              rewrite_no_write Impl.F1Box.REG_valid0 Post__Step0.
              rewrite_no_write Impl.F1Box.REG_valid0 Post__Boxes.
              rewrite_no_write Impl.F1Box.REG_valid0 Post__Input.
              rewrite_no_write Impl.F1Box.REG_valid0 Post__World.
              bash_destruct Hstage; destruct Hstage; solve_bits; try discriminate; try solve[destruct Hstage; discriminate].
              { rewrite (impl_pf__NONE_OR_INIT _ HInv Tag1); simpl; auto.
                rewrite_with_reg_spec_in Heqb1 Impl.REG_job1 Post__Input.
                rewrite_no_write_in Heqb1 Impl.REG_ext_ready_for_job Post__World.
                rewrite_no_write_in Heqb1 Impl.REG_job1 Post__World.
                rewrite (impl_ext_ready_for_job _ HInv) in Heqb1.
                bash_destruct Heqb1; try (solve[left; solve_bits]); discriminate.
              }
              { destruct_with_eqn (bits_eq St__Input.[Impl.REG_job1] St__World.[Impl.REG_job1]).
                { apply bits_eq_iff in Heqb5. rewrite Heqb5 in *.
                  rewrite_no_write_in Heqb4 Impl.REG_job1 Post__World.
                  rewrite (impl_pf_STAGE_G _ HInv Tag1); simpl; solve_bits; auto.
                }
                { apply bits_neq_iff in Heqb5.
                  rewrite_with_custom_in Heqb4 DoInput__Job1__Stage Post__Input; [ | solve_bits]; auto.
                  discriminate.
                }
              }
            }
          }
        * intros; rewrite_with_reg_spec Impl.G1Box.REG_valid0 Post__Step1.
          destruct_match.
          { apply bits_eq_iff in Heqb.  rewrite Heqb in Hstage. split_cases; discriminate. }
          { destruct (bits_eq (unsafe_get_job_stage St__Step0.[Impl.REG_job1])
                              (unsafe_get_job_stage St__Step1.[Impl.REG_job1])) eqn:Hchange.
            { apply bits_eq_iff in Hchange.
              rewrite<-Hchange in *.
              destruct_match; auto.
              rewrite_no_write Impl.G1Box.REG_valid0 Post__Step0.
              rewrite_no_write Impl.G1Box.REG_valid0 Post__Boxes.
              rewrite_no_write Impl.G1Box.REG_valid0 Post__Input.
              rewrite_no_write Impl.G1Box.REG_valid0 Post__World.
              rewrite (impl_pf__NONE_OR_INIT _ HInv Tag1); simpl; auto.
              rewrite_no_write_in Hstage Impl.REG_job1 Post__Step0.
              rewrite_no_write_in Hstage Impl.REG_job1 Post__Boxes.
              rewrite_with_reg_spec_in Hstage Impl.REG_job1 Post__Input.
              rewrite_no_write_in Hstage Impl.REG_ext_ready_for_job Post__World.
              rewrite_no_write_in Hstage Impl.REG_job1 Post__World.
              destruct_matches_in_hyp Hstage; auto.
              rewrite (impl_ext_ready_for_job _ HInv) in Heqb1.
              bash_destruct Heqb1. left; solve_bits.
            }
            { apply bits_neq_iff in Hchange.
              rewrite_with_custom_in Hstage DoStep1__Job1__Stage Post__Step1; [ | solve_bits; auto].
              destruct_match; solve_bits; auto.
              rewrite_no_write Impl.G1Box.REG_valid0 Post__Step0.
              rewrite_no_write Impl.G1Box.REG_valid0 Post__Boxes.
              rewrite_no_write Impl.G1Box.REG_valid0 Post__Input.
              rewrite_no_write Impl.G1Box.REG_valid0 Post__World.
              bash_destruct Hstage; destruct Hstage; solve_bits; try discriminate; try solve[destruct Hstage; discriminate].
              { rewrite (impl_pf__NONE_OR_INIT _ HInv Tag1); simpl; auto.
                rewrite_no_write_in Heqb1 Impl.REG_job1 Post__Step0.
                rewrite_no_write_in Heqb1 Impl.REG_job1 Post__Boxes.
                rewrite_with_reg_spec_in Heqb1 Impl.REG_job1 Post__Input.
                rewrite_no_write_in Heqb1 Impl.REG_ext_ready_for_job Post__World.
                rewrite_no_write_in Heqb1 Impl.REG_job1 Post__World.
                rewrite (impl_ext_ready_for_job _ HInv) in Heqb1.
                bash_destruct Heqb1; try (solve[left; solve_bits]); discriminate.
              }
              { apply bits_eq_iff in Heqb4.
                rewrite Heqb4 in Hchange. simpl in Heqb0.
                rewrite_with_custom_in Heqb0 DoStep1__Job1__Stage Post__Step1; [ | rewrite_solve ].
                rewrite Heqb4 in Heqb0. simpl in Heqb0. discriminate.
              }
            }
          }
    - intros tag. unfold ImplInvariant__STAGE_F.
      destruct tag; simpl.
      + rewrite_no_write Impl.REG_job0 Post__UpdateReady.
        rewrite_no_write Impl.REG_job0 Post__Step1.
        intros Hstage reg Htaint_reg; revert Hstage.

        rewrite_no_write_forall reg Post__UpdateReady.
        rewrite_no_write_forall reg Post__Step1.
        unfold reg_in_taint_list' in Htaint_reg; simpl in Htaint_reg; repeat rewrite orb_true_iff in Htaint_reg.
        split_ors_in Htaint_reg; try discriminate; simplify_nat; subst.
        intros; rewrite_with_reg_spec Impl.G0Box.REG_valid0 Post__Step0; auto.
        rewrite Hstage. simpl. rewrite andb_false_r.
        rewrite_no_write Impl.G0Box.REG_valid0 Post__Boxes.
        rewrite_no_write Impl.G0Box.REG_valid0 Post__Input.
        rewrite_no_write Impl.G0Box.REG_valid0 Post__World.
        destruct (bits_eq (unsafe_get_job_stage St__Boxes.[Impl.REG_job0])
                          (unsafe_get_job_stage St__Step0.[Impl.REG_job0])) eqn:Hchange.
        { rewrite_with_reg_spec_in Hstage Impl.REG_job0 Post__Step0.
          rewrite bits_eq_sym in Hchange. rewrite Hchange in Hstage. rewrite orb_true_r in Hstage.
          rewrite_no_write_in Hstage Impl.REG_job0 Post__Boxes.
          rewrite_with_reg_spec_in Hstage Impl.REG_job0 Post__Input.
          rewrite_no_write_in Hstage Impl.REG_ext_ready_for_job Post__World.
          bash_destruct Hstage.
          { rewrite (impl_ext_ready_for_job) in Heqb by assumption.
            bash_destruct Heqb.
            rewrite impl_pf__NONE_OR_INIT with (tag := Tag0); simpl; eauto. left; solve_bits.
          }
          { rewrite_no_write_in Hstage Impl.REG_job0 Post__World.
            rewrite (impl_pf_STAGE_F) with (tag := Tag0); simpl; eauto.
          }
        }
        { rewrite_with_custom_in Hstage DoStep0__Job0__Stage Post__Step0; [ | solve_bits].
          bash_destruct Hstage; try discriminate.
          rewrite_no_write_in Heqb0 Impl.REG_job0 Post__Boxes.
          rewrite_with_reg_spec_in Heqb0 Impl.REG_job0 Post__Input.
          bash_destruct Heqb0.
          { rewrite_no_write_in Heqb1 Impl.REG_ext_ready_for_job Post__World.
            rewrite impl_ext_ready_for_job in Heqb1 by assumption. bash_destruct Heqb1.
            rewrite (impl_pf__NONE_OR_INIT) with (tag := Tag0); simpl; eauto; left; solve_bits.
          }
          { rewrite_no_write_in Heqb0 Impl.REG_job0 Post__World.
            rewrite (impl_pf__NONE_OR_INIT) with (tag := Tag0); simpl; eauto; right; solve_bits.
          }
        }
      + rewrite_no_write Impl.REG_job1 Post__UpdateReady.
        intros Hstage reg Htaint_reg; revert Hstage.

        rewrite_no_write_forall reg Post__UpdateReady.
        unfold reg_in_taint_list' in Htaint_reg; simpl in Htaint_reg; repeat rewrite orb_true_iff in Htaint_reg.
        split_ors_in Htaint_reg; try discriminate; simplify_nat; subst.
        intros; rewrite_with_reg_spec Impl.G1Box.REG_valid0 Post__Step1; auto.
        rewrite Hstage. simpl. rewrite andb_false_r.
        rewrite_no_write Impl.G1Box.REG_valid0 Post__Step0.
        rewrite_no_write Impl.G1Box.REG_valid0 Post__Boxes.
        rewrite_no_write Impl.G1Box.REG_valid0 Post__Input.
        rewrite_no_write Impl.G1Box.REG_valid0 Post__World.
        destruct (bits_eq (unsafe_get_job_stage St__Step0.[Impl.REG_job1])
                          (unsafe_get_job_stage St__Step1.[Impl.REG_job1])) eqn:Hchange.
        { rewrite_with_reg_spec_in Hstage Impl.REG_job1 Post__Step1.
          rewrite bits_eq_sym in Hchange. rewrite Hchange in Hstage. rewrite orb_true_r in Hstage.
          rewrite_no_write_in Hstage Impl.REG_job1 Post__Step0.
          rewrite_no_write_in Hstage Impl.REG_job1 Post__Boxes.
          rewrite_with_reg_spec_in Hstage Impl.REG_job1 Post__Input.
          rewrite_no_write_in Hstage Impl.REG_ext_ready_for_job Post__World.
          bash_destruct Hstage.
          { rewrite (impl_ext_ready_for_job) in Heqb by assumption.
            bash_destruct Heqb.
            rewrite impl_pf__NONE_OR_INIT with (tag := Tag1); simpl; eauto. left; solve_bits.
          }
          { rewrite_no_write_in Hstage Impl.REG_job1 Post__World.
            rewrite (impl_pf_STAGE_F) with (tag := Tag1); simpl; eauto.
          }
        }
        { rewrite_with_custom_in Hstage DoStep1__Job1__Stage Post__Step1; [ | solve_bits].
          bash_destruct Hstage; try discriminate.
          rewrite_no_write_in Heqb0 Impl.REG_job1 Post__Step0.
          rewrite_no_write_in Heqb0 Impl.REG_job1 Post__Boxes.
          rewrite_with_reg_spec_in Heqb0 Impl.REG_job1 Post__Input.
          bash_destruct Heqb0.
          { rewrite_no_write_in Heqb1 Impl.REG_ext_ready_for_job Post__World.
            rewrite impl_ext_ready_for_job in Heqb1 by assumption. bash_destruct Heqb1.
            rewrite (impl_pf__NONE_OR_INIT) with (tag := Tag1); simpl; eauto; left; solve_bits.
          }
          { rewrite_no_write_in Heqb0 Impl.REG_job1 Post__World.
            rewrite (impl_pf__NONE_OR_INIT) with (tag := Tag1); simpl; eauto; right; solve_bits.
          }
        }
    - intros tag. unfold ImplInvariant__STAGE_G.
      destruct tag; simpl.
      + rewrite_no_write Impl.REG_job0 Post__UpdateReady.
        rewrite_no_write Impl.REG_job0 Post__Step1.
        intros Hstage reg Htaint_reg; revert Hstage.

        rewrite_no_write_forall reg Post__UpdateReady.
        rewrite_no_write_forall reg Post__Step1.
        unfold reg_in_taint_list' in Htaint_reg; simpl in Htaint_reg; repeat rewrite orb_true_iff in Htaint_reg.
        split_ors_in Htaint_reg; try discriminate; simplify_nat; subst.
        intros; rewrite_with_reg_spec Impl.F0Box.REG_valid0 Post__Step0; auto.
        rewrite Hstage; simpl; rewrite andb_true_r.
        destruct_match; auto.
        rewrite_no_write Impl.F0Box.REG_valid0 Post__Boxes.
        rewrite_no_write Impl.F0Box.REG_valid0 Post__Input.
        rewrite_no_write Impl.F0Box.REG_valid0 Post__World.

        destruct (bits_eq (unsafe_get_job_stage St__Boxes.[Impl.REG_job0])
                          (unsafe_get_job_stage St__Step0.[Impl.REG_job0])) eqn:Hchange.
        { apply bits_eq_iff in Hchange. rewrite<-Hchange in Hstage.
          rewrite_no_write_in Hstage Impl.REG_job0 Post__Boxes.
          destruct_with_eqn (bits_eq St__Input.[Impl.REG_job0] St__World.[Impl.REG_job0]).
          { apply bits_eq_iff in Heqb0. rewrite Heqb0 in *.
            rewrite_no_write_in Hstage Impl.REG_job0 Post__World.
            rewrite (impl_pf_STAGE_G _ HInv Tag0); simpl; solve_bits; auto.
          }
          { apply bits_neq_iff in Heqb0.
            rewrite_with_custom_in Hstage DoInput__Job0__Stage Post__Input; [ | solve_bits]; auto.
            discriminate.
          }
        }
        { rewrite Hstage in Hchange.
          rewrite_with_custom_in Hstage DoStep0__Job0__Stage Post__Step0.
          bash_destruct Hstage; try discriminate.
          rewrite Hstage. solve_bits.
        }
      + rewrite_no_write Impl.REG_job1 Post__UpdateReady.
        intros Hstage reg Htaint_reg; revert Hstage.

        rewrite_no_write_forall reg Post__UpdateReady.
        unfold reg_in_taint_list' in Htaint_reg; simpl in Htaint_reg; repeat rewrite orb_true_iff in Htaint_reg.
        split_ors_in Htaint_reg; try discriminate; simplify_nat; subst.
        intros; rewrite_with_reg_spec Impl.F1Box.REG_valid0 Post__Step1; auto.
        rewrite Hstage; simpl; rewrite andb_true_r.
        destruct_match; auto.
        rewrite_no_write Impl.F1Box.REG_valid0 Post__Step0.
        rewrite_no_write Impl.F1Box.REG_valid0 Post__Boxes.
        rewrite_no_write Impl.F1Box.REG_valid0 Post__Input.
        rewrite_no_write Impl.F1Box.REG_valid0 Post__World.

        destruct (bits_eq (unsafe_get_job_stage St__Step0.[Impl.REG_job1])
                          (unsafe_get_job_stage St__Step1.[Impl.REG_job1])) eqn:Hchange.
        { apply bits_eq_iff in Hchange. rewrite<-Hchange in Hstage.
          rewrite_no_write_in Hstage Impl.REG_job1 Post__Step0.
          rewrite_no_write_in Hstage Impl.REG_job1 Post__Boxes.
          destruct_with_eqn (bits_eq St__Input.[Impl.REG_job1] St__World.[Impl.REG_job1]).
          { apply bits_eq_iff in Heqb0. rewrite Heqb0 in *.
            rewrite_no_write_in Hstage Impl.REG_job1 Post__World.
            rewrite (impl_pf_STAGE_G _ HInv Tag1); simpl; solve_bits; auto.
          }
          { apply bits_neq_iff in Heqb0.
            rewrite_with_custom_in Hstage DoInput__Job1__Stage Post__Input; [ | solve_bits]; auto.
            discriminate.
          }
        }
        { rewrite Hstage in Hchange.
          rewrite_with_custom_in Hstage DoStep1__Job1__Stage Post__Step1.
          bash_destruct Hstage; try discriminate.
          rewrite Hstage. solve_bits.
        }
    - intros tag. unfold ImplInvariant__NONE_zeroed.
      destruct tag; simpl; unfold is_job_reg; intros Hjob__stage reg Hjob__reg; subst reg; simpl;
        revert Hjob__stage.
      + rewrite_no_write Impl.REG_job0 Post__UpdateReady.
        rewrite_no_write Impl.REG_job0 Post__Step1.
        intros Hstage.
        destruct (bits_eq (unsafe_get_job_stage St__Boxes.[Impl.REG_job0]) Impl.ENUM_stage__None) eqn: Hjob0.
        * revert Hjob0. intros.
          rewrite_with_reg_spec Impl.REG_job0 Post__Step0; simpl.
          rewrite Hstage. rewrite Hjob0. simpl.
          revert Hjob0.
          rewrite_no_write Impl.REG_job0 Post__Boxes.
          destruct_with_eqn (bits_eq St__Input.[Impl.REG_job0] St__World.[Impl.REG_job0]).
          { apply bits_eq_iff in Heqb. rewrite Heqb in *.
            rewrite_no_write Impl.REG_job0 Post__World.
            intros Hjob0. apply bits_eq_iff in Hjob0.
            rewrite (impl_pf_job_NONE_zeroed) with (tag := Tag0); simpl; eauto.
            reflexivity.
          }
          { apply bits_neq_iff in Heqb.
            rewrite_with_custom DoInput__Job0__Stage Post__Input; [ | solve_bits]; auto.
            rewrite bits_eq_iff. discriminate.
          }
       * rewrite_with_reg_spec Impl.REG_job0 Post__Step0; auto.
          rewrite Hjob0. rewrite Hstage. rewrite orb_false_l.
          rewrite bits_eq_sym. simpl_match. simpl. reflexivity.
      + rewrite_no_write Impl.REG_job1 Post__UpdateReady.
        intros Hstage.
        destruct (bits_eq (unsafe_get_job_stage St__Step0.[Impl.REG_job1]) Impl.ENUM_stage__None) eqn: Hjob1.
        * revert Hjob1. intros.
          rewrite_with_reg_spec Impl.REG_job1 Post__Step1; simpl.
          rewrite Hstage. rewrite Hjob1. simpl.
          revert Hjob1.
          rewrite_no_write Impl.REG_job1 Post__Step0.
          rewrite_no_write Impl.REG_job1 Post__Boxes.
          destruct_with_eqn (bits_eq St__Input.[Impl.REG_job1] St__World.[Impl.REG_job1]).
          { apply bits_eq_iff in Heqb. rewrite Heqb in *.
            rewrite_no_write Impl.REG_job1 Post__World.
            intros Hjob1. apply bits_eq_iff in Hjob1.
            rewrite (impl_pf_job_NONE_zeroed) with (tag := Tag1); simpl; eauto.
            reflexivity.
          }
          { apply bits_neq_iff in Heqb.
            rewrite_with_custom DoInput__Job1__Stage Post__Input; [ | solve_bits]; auto.
            rewrite bits_eq_iff. discriminate.
          }
       * rewrite_with_reg_spec Impl.REG_job1 Post__Step1; auto.
          rewrite Hjob1. rewrite Hstage. rewrite orb_false_l.
          rewrite bits_eq_sym. simpl_match. simpl. reflexivity.
     - constructor.
       + rewrite_with_reg_spec Impl.REG_clk Post__UpdateReady.
         rewrite_no_write Impl.REG_clk Post__Step1.
         rewrite_no_write Impl.REG_clk Post__Step0.
         rewrite_no_write Impl.REG_clk Post__Boxes.
         rewrite_no_write Impl.REG_clk Post__Input.
         rewrite_no_write Impl.REG_clk Post__World.
         reflexivity.
       + destruct tag; unfold is_job_reg; simpl; intros * Hjob Hjob_reg Hsigma; subst.
         * rewrite_with_reg_spec Impl.REG_ext_output_reg Post__UpdateReady.
           rewrite_no_write Impl.REG_job0 Post__UpdateReady.
           rewrite_with_reg_spec Impl.REG_clk Post__UpdateReady.
           rewrite_no_write Impl.REG_job0 Post__Step1.
           rewrite_no_write Impl.REG_clk Post__Step1.
           rewrite_with_reg_spec Impl.REG_job0 Post__Step0.
           rewrite_no_write Impl.REG_clk Post__Step0.
           rewrite_no_write Impl.REG_clk Post__Boxes.
           rewrite_no_write Impl.REG_job0 Post__Boxes.
           rewrite_no_write Impl.REG_clk Post__Input.
           rewrite_with_reg_spec Impl.REG_job0 Post__Input.
           rewrite_no_write Impl.REG_ext_ready_for_job Post__World.
           rewrite_no_write Impl.REG_job0 Post__World.
           rewrite_no_write Impl.REG_clk Post__World.
           rewrite_no_write Impl.REG_ext_output_reg0 Post__Step1.
           split.
           { destruct Hsigma as [Hsigma | Hsigma].
             - rewrite Hsigma. simpl. rewrite andb_false_r. rewrite Hjob.
               simpl. auto.
             - destruct_match; auto.
               + apply andb_true_iff in Heqb; propositional.
                 apply bits_eq_iff in Heqb0. simpl in Heqb0. congruence.
               + rewrite Hjob. simpl. auto.
           }
           { intros Hclk.
             apply f_equal with (f := neg) in Hclk.
             rewrite neg_involutive in Hclk. rewrite Hclk. simpl.
             rewrite_with_reg_spec Impl.REG_ext_output_reg0 Post__Step0; auto.
             { rewrite_no_write Impl.REG_job0 Post__Boxes.
               rewrite_with_reg_spec Impl.REG_job0 Post__Input.
               rewrite_no_write Impl.REG_ext_ready_for_job Post__World.
               rewrite_no_write Impl.REG_job0 Post__World.
               destruct_match; auto.
               apply andb_true_iff in Heqb; propositional.
               apply bits_eq_iff in Heqb0.
               apply bits_eq_iff in Heqb1.
               destruct Hsigma as [Hsigma | Hsigma].
               { rewrite Hsigma in Heqb1. simpl in Heqb1. discriminate. }
               { simpl in Heqb0. congruence. }
             }
           }
          * rewrite_with_reg_spec Impl.REG_ext_output_reg Post__UpdateReady.
           rewrite_no_write Impl.REG_job1 Post__UpdateReady.
           rewrite_with_reg_spec Impl.REG_clk Post__UpdateReady.
           rewrite_with_reg_spec Impl.REG_job1 Post__Step1.
           rewrite_no_write Impl.REG_clk Post__Step1.
           rewrite_with_reg_spec Impl.REG_job1 Post__Step1.
           rewrite_no_write Impl.REG_clk Post__Step0.
           rewrite_no_write Impl.REG_job1 Post__Step0.
           rewrite_no_write Impl.REG_clk Post__Boxes.
           rewrite_no_write Impl.REG_job1 Post__Boxes.
           rewrite_no_write Impl.REG_clk Post__Input.
           rewrite_with_reg_spec Impl.REG_job1 Post__Input.
           rewrite_no_write Impl.REG_ext_ready_for_job Post__World.
           rewrite_no_write Impl.REG_job1 Post__World.
           rewrite_no_write Impl.REG_clk Post__World.
           rewrite_no_write Impl.REG_ext_output_reg0 Post__Step1.
           split.
           { destruct Hsigma as [Hsigma | Hsigma].
             - rewrite Hsigma. simpl. rewrite andb_false_r. rewrite Hjob.
               simpl. auto.
             - destruct_match; auto.
               + apply andb_true_iff in Heqb; propositional.
                 apply bits_eq_iff in Heqb0. simpl in Heqb0. congruence.
               + rewrite Hjob. simpl. auto.
           }
           { intros Hclk.
             apply f_equal with (f := neg) in Hclk.
             rewrite neg_involutive in Hclk. rewrite Hclk. simpl.
             rewrite_with_reg_spec Impl.REG_ext_output_reg1 Post__Step1; auto.
             rewrite_no_write Impl.REG_job1 Post__Step0.
             rewrite_no_write Impl.REG_job1 Post__Boxes.
             rewrite_with_reg_spec Impl.REG_job1 Post__Input.
             rewrite_no_write Impl.REG_ext_ready_for_job Post__World.
             rewrite_no_write Impl.REG_job1 Post__World.
             destruct_match; auto.
             apply andb_true_iff in Heqb; propositional.
             apply bits_eq_iff in Heqb1.
             apply bits_eq_iff in Heqb0.
             destruct Hsigma as [Hsigma | Hsigma].
             { rewrite Hsigma in Heqb1. simpl in Heqb1. discriminate. }
             { simpl in Heqb0. congruence. }
           }

  Qed.

  Theorem Invariant_step_preserved':
    forall impl_st (sigma: input_t -> ext_sigma_t) input log,
      Impl.wf_sigma sigma ->
      ImplInvariant impl_st ->
      interp_scheduler (sigma input) Impl.int_fn_env Impl.struct_env impl_st Impl.rules Impl.schedule = Success log ->
      WF_log Impl.reg_types log ->
      WF_state Impl.reg_types (commit_update impl_st log) ->
      ImplInvariant (commit_update impl_st log).
  Proof.
    intros. eapply Invariant_step_preserved''; eauto.
  Qed.




End ScheduleProofs.

Module ImplementationProofs : ImplementationProofs_Sig.
    (*! TODO: MOVE *)

    Ltac step_wp_oraat_lib :=
      match goal with
      | |- oraat_wp_action _ _ _ _ _ (invalid _ ) _ _ _ _ =>
        apply oraat_wp_binop
      | |- oraat_wp_action _ _ _ _ _ (valid _ _ ) _ _ _ _ =>
        apply oraat_wp_binop
      | |- oraat_wp_action _ _ _ _ _ (action_struct_init _ _ ) _ _ _ _ =>
        apply oraat_wp_binop
      end.




    Ltac step_wp_oraat :=
      lazymatch goal with
      | |- oraat_wp_action _ _ _ _ _ (Var _) _ _ _ _ =>
       apply oraat_wp_var; [solve_unsafe|]
      | |- oraat_wp_action _ _ _ _ _ (Const _) _ _ _ _ =>
       apply oraat_wp_const; [solve_unsafe|]
      | |- oraat_wp_action _ _ _ _ _ (Bind _ _ _) _ _ _ _ =>
       apply oraat_wp_bind
      | |- oraat_wp_action _ _ _ _ _ (Seq _ _ ) _ _ _ _ =>
       apply oraat_wp_seq
      | |- oraat_wp_action _ _ _ _ _ (If _ _ _) _ _ _ _ =>
        apply oraat_wp_if
      | |- oraat_wp_action _ _ _ _ _ (Assign _ _) _ _ _ _ =>
        apply oraat_wp_assign
      | |- oraat_wp_action _ _ _ _ _ (Zop _ ) _ _ _ _ =>
        apply oraat_wp_zop; [solve_unsafe|]
      | |- oraat_wp_action _ _ _ _ _ (Unop _ _ ) _ _ _ _ =>
        apply oraat_wp_unop
      | |- oraat_wp_action _ _ _ _ _ (Binop _ _ _ ) _ _ _ _ =>
        apply oraat_wp_binop
      | |- oraat_wp_action _ _ _ _ _ (Read P0 _) _ _ _ _ =>
        apply oraat_wp_read0; [solve_unsafe| ]
      | |- oraat_wp_action _ _ _ _ _ (Read P1 _) _ _ _ _ =>
        apply oraat_wp_read1; [solve_unsafe| ]
      | |- oraat_wp_action _ _ _ _ _ (Write _ _ _) _ _ _ _ =>
        apply oraat_wp_write
      | |- oraat_wp_action _ _ _ _ _ (ExternalCall _ _) _ _ _ _ =>
        apply oraat_wp_external_call
      | |- oraat_wp_action _ _ _ _ _ (InternalCall _ _) _ _ _ _ =>
        fail
      | |- oraat_wp_action _ _ _ _ _ _ _ _ _ _ =>
        step_wp_oraat_lib
      | |- _ => progress (step_oraat_simpl)
      end.


    Arguments struct_fields : simpl never.
    (* Arguments unsafe_get_field !flds !fld !v.  *)
    (* Arguments subst_field !fields !fname !arg1 !arg2.  *)
    (* Arguments success_or_default A B !res !v.  *)


Ltac prepare_finish :=
  let Horaat := fresh in
  let Hopt := fresh in
  let Hsuccess := fresh in
  (* intros Horaat Hopt; apply simple_tuple_inversion in Horaat; *)
  (* destruct Horaat; subst; *)
  subst.
  (* apply simple_tuple_inversion in Hopt; *)
  (* destruct Hopt as (Hsuccess & ?); subst; *)
  (* repeat rewrite andb_true_iff in Hsuccess; destruct_ands. *)
    (*! END TODO: MOVE *)
  Ltac apply_taint_safety _sigma :=
    eapply taint_safety_rule with (ext_sigma := _sigma) (struct_defs := Impl.struct_env);
    unfold oraat_interp_rule, taint_rule_from_empty; try simpl_match; auto; repeat destruct_match; auto.

  Lemma RlSatisfiesSpec__InteractWithWorld :
    __oraat_rule_satisfies_spec RlSpec__InteractWithWorld (Impl.rules Impl.InteractWithWorld).
  Proof.
    unfold __oraat_rule_satisfies_spec.
    intros * Hst Hext_sigma Hint_fn_env Htype Hpre.
    destruct oraat_interp_action as (b, opt) eqn:Horaat.
    (* destruct_match_pairs; simplify_tupless; subst. *)
    destruct b; [ intros Hwf_st' | trivial].
    unfold postcond_to_Prop. rewrite and_assoc.
    split; [apply_taint_safety sigma | ].
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.rules, Impl.interact_with_world.
    repeat (repeat step_wp_oraat_safe; simpl). subst.
    repeat constructor.
  Qed.

  Lemma RlSatisfiesSpec__DoInput :
    __oraat_rule_satisfies_spec RlSpec__DoInput (Impl.rules Impl.DoInput).
  Proof.
    unfold __oraat_rule_satisfies_spec.
    unfold oraat_interp_rule.
    intros * Hst Hext_sigma Hint_fn_env Htype Hpre.
    destruct oraat_interp_action as (b, opt) eqn:Horaat.
    destruct b; [ intros Hwf_st' | trivial].
    unfold postcond_to_Prop. rewrite and_assoc.
    split; [apply_taint_safety sigma | ].
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.rules, Impl.do_input.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match.
    - repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match.
      + repeat (repeat step_wp_oraat_safe; simpl).
        destruct_match.
        * repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish; split; [ | auto].
          repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
          { intros. destruct H; [ congruence | ]; propositional.
            rewrite H0 in *. discriminate.
          }
          { destruct_match; auto.
            exfalso.
            assert (st.[Impl.REG_ext_ready_for_job] = (Ob~1 ++ Ob~0)%list) as Hext.
            { apply option_get_fields_eq with (sz := 1); try solve_bits; eauto. }
            rewrite Hext in *.
            setoid_rewrite Heqb0 in Heqb2. congruence.
          }
          { destruct_match; auto. }
        * repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish.
          repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
          { intros. destruct H; [ congruence | ]; propositional.
            rewrite H0 in *. discriminate.
          }
          { destruct_match; auto. }
          { destruct_match; auto.
            exfalso.

            assert (st.[Impl.REG_ext_ready_for_job] = (Ob~1 ++ Ob~1)%list) as Hext.
            { apply option_get_fields_eq with (sz := 1); try solve_bits; eauto.
              apply single_bit_negate with (x := false); auto; simpl.
              apply unsafe_get_field_length; auto.
            }
            rewrite Hext in *. simpl in Heqb.
            setoid_rewrite Heqb0 in Heqb2.
            discriminate.
          }
      + repeat (repeat step_wp_oraat_safe; simpl).
        prepare_finish.
        repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
        { intros. destruct H; [ congruence | ]; propositional.
          rewrite H0 in *. apply bits_neq_iff in Heqb0.
          setoid_rewrite H1 in Heqb0. congruence.
        }
        { intros. destruct H; [ congruence | ]; propositional.
          rewrite H0 in *. apply bits_neq_iff in Heqb0.
          setoid_rewrite H1 in Heqb0. congruence.
        }
        { destruct_match; auto. }
        { destruct_match; auto. }
    - repeat (repeat step_wp_oraat_safe; simpl).
      prepare_finish.
      repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
      { intros; destruct H; [ congruence |]; propositional.
        rewrite H0 in *. discriminate.
      }
      { intros; destruct H; [ congruence |]; propositional.
        rewrite H0 in *. discriminate.
      }
      { destruct_match; auto. }
      { destruct_match; auto. }
  Qed.

  Lemma RlSatisfiesSpec__StepBoxes :
    __oraat_rule_satisfies_spec RlSpec__StepBoxes (Impl.rules Impl.StepBoxes).
  Proof.
    unfold __oraat_rule_satisfies_spec.
    unfold oraat_interp_rule.
    intros * Hst Hext_sigma Hint_fn_env Htype Hpre.
    destruct oraat_interp_action as (b, opt) eqn:Horaat.
    destruct_match_pairs; simplify_tupless; subst.
    destruct b; [ intros Hwf_st' | trivial].
    unfold postcond_to_Prop. repeat rewrite and_assoc.
    split; [apply_taint_safety sigma | ].
    repeat constructor. destruct_match; auto.
  Qed.

Declare Scope wp_notations.
Notation "'_oraat_wp_action' '_' '_' '_' '_' st '(' action ')' '[...]' '_' '_' '_' " :=
  (oraat_wp_action _ _ _ _ st action _ _ _ _)
                                             (at level 200, only printing) : wp_notations.
Open Scope wp_notations.
  Definition function_matches_spec'
    (sigma: ext_sigma_t) (spec: function_spec_t) (fn: int_fn_spec_t) : Prop :=
     function_matches_spec sigma Impl.int_fn_env Impl.struct_env
      (function_spec_to_Prop sigma spec)
      (fn_arg_name fn) (fn_body fn).

  Opaque __fn_call__.

Definition __fnspec__F1Box_Fn_send_req :=
  {| Function_precond := fun _ _ _ => True;
     Function_taint_set := taint_function_body Impl.int_fn_env Impl.F1Box.FN_send_req.(fn_body);
     Function_fail_inversion := fun ext_sigma r r_acc varg =>
                                  func_call_returns ext_sigma Impl.int_fn_env Impl.struct_env Impl.F1Box.FN_can_send_req.(fn_name)
                                                    r r_acc Ob (fun ret => bits_eq ret Ob~1 = false);
     Function_reg_specs := []
  |}.

Definition __fnspec__F0Box_Fn_send_req :=
  {| Function_precond := fun _ _ _ => True;
     Function_taint_set := taint_function_body Impl.int_fn_env Impl.F0Box.FN_send_req.(fn_body);
     Function_fail_inversion := fun ext_sigma r r_acc varg =>
                                  func_call_returns ext_sigma Impl.int_fn_env Impl.struct_env Impl.F0Box.FN_can_send_req.(fn_name)
                                                    r r_acc Ob (fun ret => bits_eq ret Ob~1 = false);
     Function_reg_specs := []
  |}.


Definition __fnspec__G1Box_Fn_send_req :=
  {| Function_precond := fun _ _ _ => True;
     Function_taint_set := taint_function_body Impl.int_fn_env Impl.G1Box.FN_send_req.(fn_body);
     Function_fail_inversion := fun ext_sigma r r_acc varg =>
                                  func_call_returns ext_sigma Impl.int_fn_env Impl.struct_env
                                    Impl.G1Box.FN_can_send_req.(fn_name)
                                                    r r_acc Ob (fun ret => bits_eq ret Ob~1 = false);
     Function_reg_specs := []
  |}.
Definition __fnspec__G0Box_Fn_send_req :=
  {| Function_precond := fun _ _ _ => True;
     Function_taint_set := taint_function_body Impl.int_fn_env Impl.G0Box.FN_send_req.(fn_body);
     Function_fail_inversion := fun ext_sigma r r_acc varg =>
                                  func_call_returns ext_sigma Impl.int_fn_env Impl.struct_env
                                    Impl.G0Box.FN_can_send_req.(fn_name)
                                                    r r_acc Ob (fun ret => bits_eq ret Ob~1 = false);
     Function_reg_specs := []
  |}.


Definition __fnspec__G1Box_Fn_receive_resp :=
  {| Function_precond := fun _ _ _ => True;
     Function_taint_set := taint_function_body Impl.int_fn_env Impl.G1Box.FN_receive_resp.(fn_body);
     Function_fail_inversion := fun ext_sigma r r_acc varg =>
                                  func_call_returns ext_sigma Impl.int_fn_env Impl.struct_env Impl.G1Box.FN_can_receive_resp.(fn_name)
                                                    r r_acc Ob (fun ret => bits_eq ret Ob~1 = false);
     Function_reg_specs := [(Impl.G1Box.REG_valid0, fun _ _ _ v => v = Ob~0)]
  |}.
Definition __fnspec__G0Box_Fn_receive_resp :=
  {| Function_precond := fun _ _ _ => True;
     Function_taint_set := taint_function_body Impl.int_fn_env Impl.G0Box.FN_receive_resp.(fn_body);
     Function_fail_inversion := fun ext_sigma r r_acc varg =>
                                  func_call_returns ext_sigma Impl.int_fn_env Impl.struct_env Impl.G0Box.FN_can_receive_resp.(fn_name)
                                                    r r_acc Ob (fun ret => bits_eq ret Ob~1 = false);
     Function_reg_specs := [(Impl.G0Box.REG_valid0, fun _ _ _ v => v = Ob~0)]
  |}.



Definition __fnspec__F1Box_Fn_receive_resp :=
  {| Function_precond := fun _ _ _ => True;
     Function_taint_set := taint_function_body Impl.int_fn_env Impl.F1Box.FN_receive_resp.(fn_body);
     Function_fail_inversion := fun ext_sigma r r_acc varg =>
                                  func_call_returns ext_sigma Impl.int_fn_env Impl.struct_env Impl.F1Box.FN_can_receive_resp.(fn_name)
                                                    r r_acc Ob (fun ret => bits_eq ret Ob~1 = false);
     Function_reg_specs := [(Impl.F1Box.REG_valid0, fun _ _ _ v => v = Ob~0)]
  |}.
Definition __fnspec__F0Box_Fn_receive_resp :=
  {| Function_precond := fun _ _ _ => True;
     Function_taint_set := taint_function_body Impl.int_fn_env Impl.F0Box.FN_receive_resp.(fn_body);
     Function_fail_inversion := fun ext_sigma r r_acc varg =>
                                  func_call_returns ext_sigma Impl.int_fn_env Impl.struct_env Impl.F0Box.FN_can_receive_resp.(fn_name)
                                                    r r_acc Ob (fun ret => bits_eq ret Ob~1 = false);
     Function_reg_specs := [(Impl.F0Box.REG_valid0, fun _ _ _ v => v = Ob~0)]
  |}.



  Lemma f1_send_req_matches_spec:
    forall sigma,
    function_matches_spec' sigma __fnspec__F1Box_Fn_send_req Impl.F1Box.FN_send_req.
  Proof.
    unfold function_matches_spec', function_matches_spec.
    intros * Horaat.
    set (new_fuel := (safe_fuel Impl.int_fn_env (Datatypes.length Impl.int_fn_env)
                        (fn_body Impl.F1Box.FN_send_req) + fuel)).
    apply oraat_interp_action_increase_fuel with (fuel2 := new_fuel) in Horaat; [ | lia].

    set (safe_fuel _ _ _) in *. compute in n. subst n.
    apply function_spec_to_Prop_implies.
    split.
    { repeat destruct_match; propositional; eapply taint_safety_function; eauto.
    }
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.F1Box.FN_send_req. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl).
    eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as Call__F1Box_FN_can_send_req.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct o as [[[? ?] ?]  | ] eqn:Ret__F1Box_FN_can_send_req; [ | auto]; subst.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HNotCanSendReq.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      simpl.
      unfold func_call_returns. simpl.
      rewrite unfold__fn_call__ in *.
      apply bits_eq_negl in HNotCanSendReq. apply bits_eq_iff in HNotCanSendReq.
      repeat eexists; subst; eauto.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      unfold function_spec_to_Prop. intro Precond.
      repeat constructor.
  Qed.
  Lemma f0_send_req_matches_spec:
    forall sigma,
    function_matches_spec' sigma __fnspec__F0Box_Fn_send_req Impl.F0Box.FN_send_req.
  Proof.
    unfold function_matches_spec', function_matches_spec.
    intros * Horaat.
    set (new_fuel := (safe_fuel Impl.int_fn_env (Datatypes.length Impl.int_fn_env)
                        (fn_body Impl.F0Box.FN_send_req) + fuel)).
    apply oraat_interp_action_increase_fuel with (fuel2 := new_fuel) in Horaat; [ | lia].

    set (safe_fuel _ _ _) in *. compute in n. subst n.
    apply function_spec_to_Prop_implies.
    split.
    { repeat destruct_match; propositional; eapply taint_safety_function; eauto.
    }
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.F0Box.FN_send_req. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl).
    eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as Call__F0Box_FN_can_send_req.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct o as [[[? ?] ?]  | ] eqn:Ret__F0Box_FN_can_send_req; [ | auto]; subst.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HNotCanSendReq.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      simpl.
      unfold func_call_returns. simpl.
      rewrite unfold__fn_call__ in *.
      apply bits_eq_negl in HNotCanSendReq. apply bits_eq_iff in HNotCanSendReq.
      repeat eexists; subst; eauto.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      unfold function_spec_to_Prop. intro Precond.
      repeat constructor.
  Qed.


  Lemma f1_receive_resp_matches_spec:
    forall sigma,
    function_matches_spec' sigma __fnspec__F1Box_Fn_receive_resp Impl.F1Box.FN_receive_resp.
  Proof.
    unfold function_matches_spec', function_matches_spec.
    intros * Horaat.
    apply oraat_interp_action_increase_fuel with
      (fuel2 := safe_fuel Impl.int_fn_env (Datatypes.length Impl.int_fn_env)
                  (fn_body Impl.F1Box.FN_receive_resp) + fuel) in Horaat; [ | lia].
    set (safe_fuel _ _ _) in *. compute in n. subst n.
    apply function_spec_to_Prop_implies.
    split.
    { repeat destruct_match; propositional; eapply taint_safety_function; eauto.
    }
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.F1Box.FN_receive_resp. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl).
    eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as Call__F1Box_FN_can_receive_resp.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct o as [[[? ?] ?]  | ] eqn:Ret__F1Box_FN_can_receive_resp; [ | auto]; subst.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HNotCanReceiveResp.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      simpl.
      unfold func_call_returns. simpl.
      rewrite unfold__fn_call__ in *.
      repeat eexists; eauto.
      apply bits_eq_negl in HNotCanReceiveResp.
      apply bits_eq_iff in HNotCanReceiveResp. subst. auto.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      unfold function_spec_to_Prop. intro Precond.
      repeat constructor.
      simplify_updates.
  Qed.

  Lemma f0_receive_resp_matches_spec:
    forall sigma,
    function_matches_spec' sigma __fnspec__F0Box_Fn_receive_resp Impl.F0Box.FN_receive_resp.
  Proof.
    unfold function_matches_spec', function_matches_spec.
    intros * Horaat.
    apply oraat_interp_action_increase_fuel with
      (fuel2 := safe_fuel Impl.int_fn_env (Datatypes.length Impl.int_fn_env)
                  (fn_body Impl.F0Box.FN_receive_resp) + fuel) in Horaat; [ | lia].
    set (safe_fuel _ _ _) in *. compute in n. subst n.
    apply function_spec_to_Prop_implies.
    split.
    { repeat destruct_match; propositional; eapply taint_safety_function; eauto.
    }
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.F0Box.FN_receive_resp. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl).
    eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as Call__F0Box_FN_can_receive_resp.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct o as [[[? ?] ?]  | ] eqn:Ret__F0Box_FN_can_receive_resp; [ | auto]; subst.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HNotCanReceiveResp.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      simpl.
      unfold func_call_returns. simpl.
      rewrite unfold__fn_call__ in *.
      repeat eexists; eauto.
      apply bits_eq_negl in HNotCanReceiveResp.
      apply bits_eq_iff in HNotCanReceiveResp. subst. auto.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      unfold function_spec_to_Prop. intro Precond.
      repeat constructor.
      simplify_updates.
  Qed.


  Lemma g1_send_req_matches_spec:
    forall sigma,
    function_matches_spec' sigma __fnspec__G1Box_Fn_send_req Impl.G1Box.FN_send_req.
  Proof.
    unfold function_matches_spec', function_matches_spec.
    intros * Horaat.
    apply oraat_interp_action_increase_fuel with
      (fuel2 := safe_fuel Impl.int_fn_env (Datatypes.length Impl.int_fn_env)
                  (fn_body Impl.G1Box.FN_send_req) + fuel) in Horaat; [ | lia].
    set (safe_fuel _ _ _) in *. compute in n. subst n.
    apply function_spec_to_Prop_implies.
    split.
    { repeat destruct_match; propositional; eapply taint_safety_function; eauto.
    }
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.G1Box.FN_send_req. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl).
    eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as Call__G1Box_FN_can_send_req.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct o as [[[? ?] ?]  | ] eqn:Ret__G1Box_FN_can_send_req; [ | auto]; subst.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HNotCanReceiveResp.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      simpl.
      unfold func_call_returns. simpl.
      rewrite unfold__fn_call__ in *.
      repeat eexists; eauto.
      apply bits_eq_negl in HNotCanReceiveResp.
      apply bits_eq_iff in HNotCanReceiveResp. subst. auto.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      unfold function_spec_to_Prop. intro Precond.
      repeat constructor.
  Qed.

  Lemma g0_send_req_matches_spec:
    forall sigma,
    function_matches_spec' sigma __fnspec__G0Box_Fn_send_req Impl.G0Box.FN_send_req.
  Proof.
    unfold function_matches_spec', function_matches_spec.
    intros * Horaat.
    apply oraat_interp_action_increase_fuel with
      (fuel2 := safe_fuel Impl.int_fn_env (Datatypes.length Impl.int_fn_env)
                  (fn_body Impl.G0Box.FN_send_req) + fuel) in Horaat; [ | lia].
    set (safe_fuel _ _ _) in *. compute in n. subst n.
    apply function_spec_to_Prop_implies.
    split.
    { repeat destruct_match; propositional; eapply taint_safety_function; eauto.
    }
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.G0Box.FN_send_req. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl).
    eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as Call__G0Box_FN_can_send_req.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct o as [[[? ?] ?]  | ] eqn:Ret__G0Box_FN_can_send_req; [ | auto]; subst.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HNotCanReceiveResp.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      simpl.
      unfold func_call_returns. simpl.
      rewrite unfold__fn_call__ in *.
      repeat eexists; eauto.
      apply bits_eq_negl in HNotCanReceiveResp.
      apply bits_eq_iff in HNotCanReceiveResp. subst. auto.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      unfold function_spec_to_Prop. intro Precond.
      repeat constructor.
  Qed.



  Lemma g1_receive_resp_matches_spec:
    forall sigma,
    function_matches_spec' sigma __fnspec__G1Box_Fn_receive_resp Impl.G1Box.FN_receive_resp.
  Proof.
    unfold function_matches_spec', function_matches_spec.
    intros * Horaat.
    apply oraat_interp_action_increase_fuel with
      (fuel2 := safe_fuel Impl.int_fn_env (Datatypes.length Impl.int_fn_env)
                  (fn_body Impl.G1Box.FN_receive_resp) + fuel) in Horaat; [ | lia].
    set (safe_fuel _ _ _) in *. compute in n. subst n.
    apply function_spec_to_Prop_implies.
    split.
    { repeat destruct_match; propositional; eapply taint_safety_function; eauto.
    }
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.G1Box.FN_receive_resp. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl).
    eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as Call__G1Box_FN_can_receive_resp.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct o as [[[? ?] ?]  | ] eqn:Ret__G1Box_FN_can_receive_resp; [ | auto]; subst.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HNotCanReceiveResp.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      simpl.
      unfold func_call_returns. simpl.
      rewrite unfold__fn_call__ in *.
      repeat eexists; eauto.
      apply bits_eq_negl in HNotCanReceiveResp.
      apply bits_eq_iff in HNotCanReceiveResp. subst. auto.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      unfold function_spec_to_Prop. intro Precond.
      repeat constructor.
      simplify_updates.
  Qed.

  Lemma g0_receive_resp_matches_spec:
    forall sigma,
    function_matches_spec' sigma __fnspec__G0Box_Fn_receive_resp Impl.G0Box.FN_receive_resp.
  Proof.
    unfold function_matches_spec', function_matches_spec.
    intros * Horaat.
    apply oraat_interp_action_increase_fuel with
      (fuel2 := safe_fuel Impl.int_fn_env (Datatypes.length Impl.int_fn_env)
                  (fn_body Impl.G0Box.FN_receive_resp) + fuel) in Horaat; [ | lia].
    set (safe_fuel _ _ _) in *. compute in n. subst n.
    apply function_spec_to_Prop_implies.
    split.
    { repeat destruct_match; propositional; eapply taint_safety_function; eauto.
    }
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.G0Box.FN_receive_resp. unfold fn_body.
    repeat (repeat step_wp_oraat_safe; simpl).
    eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only | ].
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as Call__G0Box_FN_can_receive_resp.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct o as [[[? ?] ?]  | ] eqn:Ret__G0Box_FN_can_receive_resp; [ | auto]; subst.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as HNotCanReceiveResp.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      simpl.
      unfold func_call_returns. simpl.
      rewrite unfold__fn_call__ in *.
      repeat eexists; eauto.
      apply bits_eq_negl in HNotCanReceiveResp.
      apply bits_eq_iff in HNotCanReceiveResp. subst. auto.
    - repeat (repeat step_wp_oraat_safe; simpl); subst.
      unfold function_spec_to_Prop. intro Precond.
      repeat constructor.
      simplify_updates.
  Qed.

Ltac fn_rewrite_no_write reg prop :=
  rewrite (taint_set_to_prop_no_write' _ _ _ reg prop); [ | reflexivity].
    Arguments fn_body : simpl never.
    Opaque taint_set_to_prop.
    Opaque function_spec_to_Prop.

  Lemma RlSatisfiesSpec__DoStep0 :
    __oraat_rule_satisfies_spec RlSpec__DoStep0 (Impl.rules Impl.DoStep0).
  Proof.
    unfold __oraat_rule_satisfies_spec.
    unfold oraat_interp_rule.
    intros * Hst Hext_sigma Hint_fn_env Htype Hpre.
    destruct oraat_interp_action as (b0, opt) eqn:Horaat.
    destruct_match_pairs; simplify_tupless; subst.
    destruct b0; [ intros Hwf_st' | trivial].
    unfold postcond_to_Prop. repeat rewrite and_assoc.
    split; [apply_taint_safety sigma | ].
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.rules, Impl.do_step0.
    set (safe_fuel _ _ _). compute in n. subst n.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as Match__NONE.
    - cbn - [_Reg]. repeat step_wp_oraat_safe.
      prepare_finish.
      unfold post_reg_spec_to_prop; simpl.
      repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
      + contradiction.
      + apply bits_eq_iff in Match__NONE. rewrite Match__NONE. intros; contradiction.
      + apply bits_eq_iff in Match__NONE. rewrite Match__NONE; simpl; intros; contradiction.
      + apply bits_eq_iff in Match__NONE. rewrite Match__NONE. simpl. reflexivity.
      + apply bits_eq_iff in Match__NONE. rewrite Match__NONE. simpl. reflexivity.
    - repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as Match__INIT.
      + repeat step_wp_oraat_safe; simpl.
        eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | ..].
        * solve_read_only.
        * repeat step_wp_oraat_safe.
          destruct_match_as Call__F0Box_FN_can_send_req.
          repeat step_wp_oraat_safe; subst.
          destruct o as [[[? ?] ?]  | ] eqn:Ret__F1Box_FN_can_send_req; [ | auto].
          repeat step_wp_oraat_safe.
          destruct_match_as Match__F0Box_Fn_can_send_req.
          { repeat step_wp_oraat_safe.
            eapply oraat_wp_internal_call'__safe with (2 := eq_refl) (spec := __fnspec__F0Box_Fn_send_req); [ solve_safe | ..].
            { apply f0_send_req_matches_spec. }
            { repeat (repeat step_wp_oraat_safe; simpl).
              destruct_match_as Call__F0Box_FN_send_req.
              repeat (repeat step_wp_oraat_safe; simpl).
              destruct o0 as [[[? ?] ?]  | ] eqn:Ret__F0Box_FN_send_req; [ | auto].
              { split; [trivial | ].
                intros Htaint__F0Box_Fn_send_req.
                intros Hspecs__F0Box_fn_send_req. inversions Hspecs__F0Box_fn_send_req.
                repeat (repeat step_wp_oraat_safe; simpl).
                prepare_finish.
                unfold post_reg_spec_to_prop; simpl.
                repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
                + apply bits_eq_iff in Match__INIT. rewrite Match__INIT. intros; discriminate.
                + apply bits_eq_iff in Match__INIT. rewrite Match__INIT; simpl; intros; discriminate.
                + apply bits_eq_iff in Match__INIT. rewrite Match__INIT; simpl; reflexivity.
                + apply bits_eq_iff in Match__INIT. rewrite Match__INIT. simpl.
                  erewrite taint_set_to_prop_no_write'; eauto. (* TODO *)
              }
              { subst. repeat step_wp_oraat_safe.
                intro fail_cond. unfold func_call_returns in fail_cond; simpl in fail_cond.
                exfalso.
                destruct fail_cond as (? & ? & ? & ? & fail_cond0 & fail_cond1).
                apply oraat_interp_action_replace_fuel with (1 := Call__F0Box_FN_can_send_req) in fail_cond0.
                simplify. congruence.
              }
            }
          }
          { repeat (repeat step_wp_oraat_safe; simpl).
            prepare_finish.
            unfold post_reg_spec_to_prop; simpl.
            repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
            + contradiction.
            + apply bits_eq_iff in Match__INIT. rewrite Match__INIT; intros; discriminate.
            + apply bits_eq_iff in Match__INIT. rewrite Match__INIT; intros; discriminate.
            + apply bits_eq_iff in Match__INIT. rewrite Match__INIT; simpl; reflexivity.
            + apply bits_eq_iff in Match__INIT. rewrite Match__INIT. simpl. reflexivity.
          }
      + repeat (repeat step_wp_oraat_safe; simpl).
        destruct_match_as Match__F.
        * repeat (repeat step_wp_oraat_safe; simpl).
          eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only| ].
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as Call__G0Box_FN_can_send_req.
          repeat (repeat step_wp_oraat_safe; simpl); subst b.
          destruct o as [[[? ?] ?]  | ] eqn:Ret__G0Box_FN_can_send_req; [ | auto].
          repeat (repeat step_wp_oraat_safe; simpl).
          eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only| ].
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as Call__F0Box_FN_can_receive_resp.
          repeat (repeat step_wp_oraat_safe; simpl); subst b.
          destruct o0 as [[[? ?] ?]  | ] eqn:Ret__F0Box_FN_can_receive_resp; [ | auto].
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as Match__F0_send_req.
          { repeat (repeat step_wp_oraat_safe; simpl).
            eapply oraat_wp_internal_call'__safe with (2 := eq_refl) (spec := __fnspec__F0Box_Fn_receive_resp); [ solve_safe | apply f0_receive_resp_matches_spec | ].
            repeat (repeat step_wp_oraat_safe; simpl).
            destruct_match_as Call__F0Box_FN_receive_resp.
            repeat (repeat step_wp_oraat_safe; simpl); subst b.
            destruct o1 as [[[? ?] ?]  | ] eqn:Ret__F0Box_FN_receive_resp; [ | auto]; subst.
            { split; [trivial | ].
              intros Htaint__F0Box_Fn_receive_resp.
              intros Hspecs__F0Box_fn_receive_resp. inversions Hspecs__F0Box_fn_receive_resp.
              repeat (repeat step_wp_oraat_safe; simpl).
              eapply oraat_wp_internal_call'__safe with (2 := eq_refl) (spec := __fnspec__G0Box_Fn_send_req); [ solve_safe | apply g0_send_req_matches_spec | ].
              repeat (repeat step_wp_oraat_safe; simpl).
              destruct_match_as Call__G0Box_FN_send_req.
              repeat (repeat step_wp_oraat_safe; simpl); subst b.
              destruct o as [[[? ?] ?]  | ] eqn:Ret__G0Box_FN_send_req; [ | auto].
              { split; [trivial | ].
                intros Htaint__G0Box_Fn_send_req
                intros Hspecs__G0Box_fn_send_req. inversions Hspecs__G0Box_fn_send_req.
                repeat (repeat step_wp_oraat_safe; simpl).
                prepare_finish.
                unfold post_reg_spec_to_prop; simpl.
                repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
                + discriminate.
                + discriminate.
                + apply bits_eq_iff in Match__F. rewrite Match__F. simpl. reflexivity.
                + apply bits_eq_iff in Match__F. rewrite Match__F. simpl.
                  fn_rewrite_no_write Impl.F0Box.REG_valid0 Htaint__G0Box_Fn_send_req.
                  assumption.
              }
              { subst. repeat step_wp_oraat_safe.
                intro fail_cond. unfold func_call_returns in fail_cond; simpl in fail_cond.
                exfalso. (* called with different state *)
                destruct fail_cond as (? & ? & ? & ? & fail_cond0 & fail_cond1).

                eapply oraat_interp_action_taint_eq with
                  (1 := Call__G0Box_FN_can_send_req)
                  (fuel3 := safe_fuel Impl.int_fn_env (List.length Impl.int_fn_env) (fn_body Impl.G0Box.FN_can_send_req)) in fail_cond0.
                2 : { reflexivity. }
                2: { apply taint_equiv_read0_refl. }
                2: { apply taint_equiv_acc_state_set_read1 with (1 := Htaint__F0Box_Fn_receive_resp); auto.
                     apply taint_equiv_acc_state_empty.
}
                propositional.
                apply bits_eq_iff in Match__F0_send_req.
                assert (x2 = ones 1).
                { eapply bits_eq_and_true_l; eauto. }
                subst. discriminate.
              }
            }
            { subst. repeat step_wp_oraat_safe.
              intro fail_cond. unfold func_call_returns in fail_cond; simpl in fail_cond.
              exfalso.
              destruct fail_cond as (? & ? & ? & ? & fail_cond0 & fail_cond1).
              apply oraat_interp_action_replace_fuel with (1 := Call__F0Box_FN_can_receive_resp) in fail_cond0.
              apply bits_eq_iff in Match__F0_send_req.
              assert (l0 = ones 1).
              { eapply bits_eq_and_true; eauto. }
              simplify. discriminate.
            }
          }
          { repeat (repeat step_wp_oraat_safe; simpl).
            prepare_finish.
            unfold post_reg_spec_to_prop; simpl.
            repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
            + contradiction.
            + contradiction.
            + contradiction.
            + apply bits_eq_iff in Match__F. rewrite Match__F. simpl. reflexivity.
          }
        * repeat (repeat step_wp_oraat_safe; simpl).
          eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | ..].
          { solve_read_only. }
          { repeat (repeat step_wp_oraat_safe; simpl).
            destruct_match_as Call__G0Box_FN_can_receive_resp.
            repeat (repeat step_wp_oraat_safe; simpl).
            destruct o as [[[? ?] ?]  | ] eqn:Ret__G0Box_FN_can_send_req; [ | auto].
            repeat (repeat step_wp_oraat_safe; simpl). subst.
            destruct_match_as Match_clk_and_G0Box_can_receive.
            { repeat (repeat step_wp_oraat_safe; simpl).
              eapply oraat_wp_internal_call'__safe with (2 := eq_refl) (spec := __fnspec__G0Box_Fn_receive_resp); [ solve_safe | apply g0_receive_resp_matches_spec | ].
              repeat (repeat step_wp_oraat_safe; simpl).
              destruct_match_as Call__G0Box_FN_receive_resp.
              repeat (repeat step_wp_oraat_safe; simpl).
              destruct o as [[[? ?] ?]  | ] eqn:Ret__G0Box_FN_receive_resp; [ | auto].
              { split; [trivial | ].
                intros Htaint__G0Box_Fn_receive_resp.
                intros Hspecs__G0Box_fn_receive_resp.
                repeat (repeat step_wp_oraat_safe; simpl).
                prepare_finish.
                unfold post_reg_spec_to_prop; simpl.
                repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
                + intros Hstage1.
                  destruct_match; auto.
                  exfalso.
                  rewrite case_G with (bs := (unsafe_get_field (struct_fields Impl.S_job_t) Impl.FLD_job_t_stage st.[Impl.REG_job0])) in Heqb; auto; try solve_bits; [discriminate | ].
                  apply unsafe_get_field_length; auto.
                + intros. simplify_updates.
                + intros.
                  move Match_clk_and_G0Box_can_receive at bottom.
                  destruct_with_eqn (bits_eq st.[Impl.REG_clk] Ob~0); solve_bits.
                  destruct (case_singleton_bv l); subst.
                  { erewrite<-is_success_and_length; [ | eauto]; auto. }
                  { discriminate. }
                  { discriminate. }
                + rewrite Match__NONE. rewrite bits_eq_sym.  rewrite Match__NONE. simpl.
                  reflexivity.
                + intros Hstage. destruct Hstage as [? | Hstage_eq]; [ congruence | ].
                  destruct Hstage_eq as [Hstage_eq | Hclk].
                  * rewrite Hstage_eq in Match__NONE. discriminate.
                  * move Match_clk_and_G0Box_can_receive at bottom.
                    apply bits_neq_iff in Hclk. rewrite Hclk in Match_clk_and_G0Box_can_receive.
                    destruct (case_singleton_bv l); subst.
                    { erewrite<-is_success_and_length; [ | eauto]; auto. }
                    { discriminate. }
                    { discriminate. }
                + simpl. rewrite andb_true_r.
                  rewrite case_G with (bs := (unsafe_get_field (struct_fields Impl.S_job_t) Impl.FLD_job_t_stage st.[Impl.REG_job0])); auto; try solve_bits; [ | apply unsafe_get_field_length ;auto]. simpl.
                  inversions Hspecs__G0Box_fn_receive_resp. assumption.
                + simpl. rewrite andb_false_r.
                  erewrite taint_set_to_prop_no_write'; eauto.
              }
              { subst. repeat step_wp_oraat_safe.
                intro fail_cond. unfold func_call_returns in fail_cond; simpl in fail_cond.
                exfalso.
                destruct fail_cond as (? & ? & ? & l2 & fail_cond0 & fail_cond1).
                apply oraat_interp_action_replace_fuel with (1 := Call__G0Box_FN_can_receive_resp) in fail_cond0; simplify.
                apply bits_eq_iff in Match_clk_and_G0Box_can_receive.
                destruct (case_singleton_bv l2); subst.
                { erewrite<-is_success_and_length; [ | eauto]; auto. }
                - discriminate.
                - simpl in *. rewrite andb_false_r in Match_clk_and_G0Box_can_receive. discriminate.
              }
            }
            { repeat (repeat step_wp_oraat_safe; simpl).
              prepare_finish.
              unfold post_reg_spec_to_prop; simpl.
              repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
              + contradiction.
              + intros. contradiction.
              + intros. contradiction.
              + rewrite Match__NONE; simpl. rewrite andb_false_r. destruct_match; auto.
              + rewrite Match_clk_and_G0Box_can_receive. simpl. reflexivity.
            }
          }
  Qed.


  Lemma RlSatisfiesSpec__DoStep1 :
    __oraat_rule_satisfies_spec RlSpec__DoStep1 (Impl.rules Impl.DoStep1).
  Proof.
    unfold __oraat_rule_satisfies_spec.
    unfold oraat_interp_rule.
    intros * Hst Hext_sigma Hint_fn_env Htype Hpre.
    destruct oraat_interp_action as (b0, opt) eqn:Horaat.
    destruct_match_pairs; simplify_tupless; subst.
    destruct b0; [ intros Hwf_st' | trivial].
    unfold postcond_to_Prop. repeat rewrite and_assoc.
    split; [apply_taint_safety sigma | ].
    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.rules, Impl.do_step1.
    set (safe_fuel _ _ _). compute in n. subst n.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match_as Match__NONE.
    - cbn - [_Reg]. repeat step_wp_oraat_safe.
      prepare_finish.
      unfold post_reg_spec_to_prop; simpl.
      repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
      + contradiction.
      + apply bits_eq_iff in Match__NONE. rewrite Match__NONE. intros; contradiction.
      + apply bits_eq_iff in Match__NONE. rewrite Match__NONE; simpl; intros; contradiction.
      + apply bits_eq_iff in Match__NONE. rewrite Match__NONE. simpl. reflexivity.
      + apply bits_eq_iff in Match__NONE. rewrite Match__NONE. simpl. reflexivity.
    - repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match_as Match__INIT.
      + repeat step_wp_oraat_safe; simpl.
        eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | ..].
        * solve_read_only.
        * repeat step_wp_oraat_safe.
          destruct_match_as Call__F1Box_FN_can_send_req.
          repeat step_wp_oraat_safe; subst.
          destruct o as [[[? ?] ?]  | ] eqn:Ret__F1Box_FN_can_send_req; [ | auto].
          repeat step_wp_oraat_safe.
          destruct_match_as Match__F1Box_Fn_can_send_req.
          { repeat step_wp_oraat_safe.
            eapply oraat_wp_internal_call'__safe with (2 := eq_refl) (spec := __fnspec__F1Box_Fn_send_req); [ solve_safe | ..].
            { apply f1_send_req_matches_spec. }
            { repeat (repeat step_wp_oraat_safe; simpl).
              destruct_match_as Call__F1Box_FN_send_req.
              repeat (repeat step_wp_oraat_safe; simpl).
              destruct o0 as [[[? ?] ?]  | ] eqn:Ret__F1Box_FN_send_req; [ | auto].
              { split; [trivial | ].
                intros Htaint__F1Box_Fn_send_req.
                intros Hspecs__F1Box_fn_send_req. inversions Hspecs__F1Box_fn_send_req.
                repeat (repeat step_wp_oraat_safe; simpl).
                prepare_finish.
                unfold post_reg_spec_to_prop; simpl.
                repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
                + apply bits_eq_iff in Match__INIT. rewrite Match__INIT. intros; discriminate.
                + apply bits_eq_iff in Match__INIT. rewrite Match__INIT; simpl; intros; discriminate.
                + apply bits_eq_iff in Match__INIT. rewrite Match__INIT; simpl; reflexivity.
                + apply bits_eq_iff in Match__INIT. rewrite Match__INIT. simpl.
                  erewrite taint_set_to_prop_no_write'; eauto. (* TODO *)
              }
              { subst. repeat step_wp_oraat_safe.
                intro fail_cond. unfold func_call_returns in fail_cond; simpl in fail_cond.
                exfalso.
                destruct fail_cond as (? & ? & ? & ? & fail_cond0 & fail_cond1).
                apply oraat_interp_action_replace_fuel with (1 := Call__F1Box_FN_can_send_req) in fail_cond0.
                simplify. congruence.
              }
            }
          }
          { repeat (repeat step_wp_oraat_safe; simpl).
            prepare_finish.
            unfold post_reg_spec_to_prop; simpl.
            repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
            + contradiction.
            + apply bits_eq_iff in Match__INIT. rewrite Match__INIT; intros; discriminate.
            + apply bits_eq_iff in Match__INIT. rewrite Match__INIT; intros; discriminate.
            + apply bits_eq_iff in Match__INIT. rewrite Match__INIT; simpl; reflexivity.
            + apply bits_eq_iff in Match__INIT. rewrite Match__INIT. simpl. reflexivity.
          }
      + repeat (repeat step_wp_oraat_safe; simpl).
        destruct_match_as Match__F.
        * repeat (repeat step_wp_oraat_safe; simpl).
          eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only| ].
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as Call__G1Box_FN_can_send_req.
          repeat (repeat step_wp_oraat_safe; simpl); subst b.
          destruct o as [[[? ?] ?]  | ] eqn:Ret__G1Box_FN_can_send_req; [ | auto].
          repeat (repeat step_wp_oraat_safe; simpl).
          eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | solve_read_only| ].
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as Call__F1Box_FN_can_receive_resp.
          repeat (repeat step_wp_oraat_safe; simpl); subst b.
          destruct o0 as [[[? ?] ?]  | ] eqn:Ret__F1Box_FN_can_receive_resp; [ | auto].
          repeat (repeat step_wp_oraat_safe; simpl).
          destruct_match_as Match__F1_send_req.
          { repeat (repeat step_wp_oraat_safe; simpl).
            eapply oraat_wp_internal_call'__safe with (2 := eq_refl) (spec := __fnspec__F1Box_Fn_receive_resp); [ solve_safe | apply f1_receive_resp_matches_spec | ].
            repeat (repeat step_wp_oraat_safe; simpl).
            destruct_match_as Call__F1Box_FN_receive_resp.
            repeat (repeat step_wp_oraat_safe; simpl); subst b.
            destruct o1 as [[[? ?] ?]  | ] eqn:Ret__F1Box_FN_receive_resp; [ | auto]; subst.
            { split; [trivial | ].
              intros Htaint__F1Box_Fn_receive_resp.
              intros Hspecs__F1Box_fn_receive_resp. inversions Hspecs__F1Box_fn_receive_resp.
              repeat (repeat step_wp_oraat_safe; simpl).
              eapply oraat_wp_internal_call'__safe with (2 := eq_refl) (spec := __fnspec__G1Box_Fn_send_req); [ solve_safe | apply g1_send_req_matches_spec | ].
              repeat (repeat step_wp_oraat_safe; simpl).
              destruct_match_as Call__G1Box_FN_send_req.
              repeat (repeat step_wp_oraat_safe; simpl); subst b.
              destruct o as [[[? ?] ?]  | ] eqn:Ret__G1Box_FN_send_req; [ | auto].
              { split; [trivial | ].
                intros Htaint__G1Box_Fn_send_req
                intros Hspecs__G1Box_fn_send_req. inversions Hspecs__G1Box_fn_send_req.
                repeat (repeat step_wp_oraat_safe; simpl).
                prepare_finish.
                unfold post_reg_spec_to_prop; simpl.
                repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
                + discriminate.
                + discriminate.
                + apply bits_eq_iff in Match__F. rewrite Match__F. simpl. reflexivity.
                + apply bits_eq_iff in Match__F. rewrite Match__F. simpl.
                  fn_rewrite_no_write Impl.F1Box.REG_valid0 Htaint__G1Box_Fn_send_req.
                  assumption.
              }
              { subst. repeat step_wp_oraat_safe.
                intro fail_cond. unfold func_call_returns in fail_cond; simpl in fail_cond.
                exfalso. (* called with different state *)
                destruct fail_cond as (? & ? & ? & ? & fail_cond0 & fail_cond1).

                eapply oraat_interp_action_taint_eq with
                  (1 := Call__G1Box_FN_can_send_req)
                  (fuel3 := safe_fuel Impl.int_fn_env (List.length Impl.int_fn_env) (fn_body Impl.G1Box.FN_can_send_req)) in fail_cond0.
                2 : { reflexivity. }
                2: { apply taint_equiv_read0_refl. }
                2: { apply taint_equiv_acc_state_set_read1 with (1 := Htaint__F1Box_Fn_receive_resp); auto.
                     apply taint_equiv_acc_state_empty.
}
                propositional.
                apply bits_eq_iff in Match__F1_send_req.
                assert (x2 = ones 1).
                { eapply bits_eq_and_true_l; eauto. }
                subst. discriminate.
              }
            }
            { subst. repeat step_wp_oraat_safe.
              intro fail_cond. unfold func_call_returns in fail_cond; simpl in fail_cond.
              exfalso.
              destruct fail_cond as (? & ? & ? & ? & fail_cond0 & fail_cond1).
              apply oraat_interp_action_replace_fuel with (1 := Call__F1Box_FN_can_receive_resp) in fail_cond0.
              apply bits_eq_iff in Match__F1_send_req.
              assert (l0 = ones 1).
              { eapply bits_eq_and_true; eauto. }
              simplify. discriminate.
            }
          }
          { repeat (repeat step_wp_oraat_safe; simpl).
            prepare_finish.
            unfold post_reg_spec_to_prop; simpl.
            repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
            + contradiction.
            + contradiction.
            + contradiction.
            + apply bits_eq_iff in Match__F. rewrite Match__F. simpl. reflexivity.
          }
        * repeat (repeat step_wp_oraat_safe; simpl).
          eapply @oraat_wp_internal_call__read_only__safe with (2 := eq_refl); [ solve_safe | ..].
          { solve_read_only. }
          { repeat (repeat step_wp_oraat_safe; simpl).
            destruct_match_as Call__G1Box_FN_can_receive_resp.
            repeat (repeat step_wp_oraat_safe; simpl).
            destruct o as [[[? ?] ?]  | ] eqn:Ret__G1Box_FN_can_send_req; [ | auto].
            repeat (repeat step_wp_oraat_safe; simpl). subst.
            destruct_match_as Match_clk_and_G1Box_can_receive.
            { repeat (repeat step_wp_oraat_safe; simpl).
              eapply oraat_wp_internal_call'__safe with (2 := eq_refl) (spec := __fnspec__G1Box_Fn_receive_resp); [ solve_safe | apply g1_receive_resp_matches_spec | ].
              repeat (repeat step_wp_oraat_safe; simpl).
              destruct_match_as Call__G1Box_FN_receive_resp.
              repeat (repeat step_wp_oraat_safe; simpl).
              destruct o as [[[? ?] ?]  | ] eqn:Ret__G1Box_FN_receive_resp; [ | auto].
              { split; [trivial | ].
                intros Htaint__G1Box_Fn_receive_resp.
                intros Hspecs__G1Box_fn_receive_resp.
                repeat (repeat step_wp_oraat_safe; simpl).
                prepare_finish.
                unfold post_reg_spec_to_prop; simpl.
                repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
                + intros Hstage1.
                  destruct_match; auto.
                  exfalso.
                  rewrite case_G with (bs := (unsafe_get_field (struct_fields Impl.S_job_t) Impl.FLD_job_t_stage st.[Impl.REG_job1])) in Heqb; auto; try solve_bits; [discriminate | ].
                  apply unsafe_get_field_length; auto.
                + intros. simplify_updates.
                + intros.
                  move Match_clk_and_G1Box_can_receive at bottom.
                  destruct_with_eqn (bits_eq st.[Impl.REG_clk] Ob~1); solve_bits.
                  destruct (case_singleton_bv l); subst.
                  { erewrite<-is_success_and_length; [ | eauto]; auto. }
                  { discriminate. }
                  { discriminate. }
                + rewrite Match__NONE. rewrite bits_eq_sym.  rewrite Match__NONE. simpl.
                  reflexivity.
                + intros Hstage. destruct Hstage as [? | Hstage_eq]; [ congruence | ].
                  destruct Hstage_eq as [Hstage_eq | Hclk].
                  * rewrite Hstage_eq in Match__NONE. discriminate.
                  * move Match_clk_and_G1Box_can_receive at bottom.
                    apply bits_neq_iff in Hclk. rewrite Hclk in Match_clk_and_G1Box_can_receive.
                    destruct (case_singleton_bv l); subst.
                    { erewrite<-is_success_and_length; [ | eauto]; auto. }
                    { discriminate. }
                    { discriminate. }
                + simpl. rewrite andb_true_r.
                  rewrite case_G with (bs := (unsafe_get_field (struct_fields Impl.S_job_t) Impl.FLD_job_t_stage st.[Impl.REG_job1])); auto; try solve_bits; [ | apply unsafe_get_field_length ;auto]. simpl.
                  inversions Hspecs__G1Box_fn_receive_resp. assumption.
                + simpl. rewrite andb_false_r.
                  erewrite taint_set_to_prop_no_write'; eauto.
              }
              { subst. repeat step_wp_oraat_safe.
                intro fail_cond. unfold func_call_returns in fail_cond; simpl in fail_cond.
                exfalso.
                destruct fail_cond as (? & ? & ? & l2 & fail_cond0 & fail_cond1).
                apply oraat_interp_action_replace_fuel with (1 := Call__G1Box_FN_can_receive_resp) in fail_cond0; simplify.
                apply bits_eq_iff in Match_clk_and_G1Box_can_receive.
                destruct (case_singleton_bv l2); subst.
                { erewrite<-is_success_and_length; [ | eauto]; auto. }
                - discriminate.
                - simpl in *. rewrite andb_false_r in Match_clk_and_G1Box_can_receive. discriminate.
              }
            }
            { repeat (repeat step_wp_oraat_safe; simpl).
              prepare_finish.
              unfold post_reg_spec_to_prop; simpl.
              repeat constructor; unfold unsafe_get_job_stage; simplify_updates.
              + contradiction.
              + intros. contradiction.
              + intros. contradiction.
              + rewrite Match__NONE; simpl. rewrite andb_false_r. destruct_match; auto.
              + rewrite Match_clk_and_G1Box_can_receive. simpl. reflexivity.
            }
          }
  Qed.

  Lemma RlSatisfiesSpec__UpdateReady :
      __oraat_rule_satisfies_spec RlSpec__UpdateReady (Impl.rules Impl.UpdateReady).
  Proof.
    unfold __oraat_rule_satisfies_spec.
    unfold oraat_interp_rule.
    intros * Hst Hext_sigma Hint_fn_env Htype Hpre.
    destruct oraat_interp_action as (b0, opt) eqn:Horaat.
    destruct_match_pairs; simplify_tupless; subst.
    destruct b0; [ intros Hwf_st' | trivial].
    unfold postcond_to_Prop. repeat rewrite and_assoc.

    split; [apply_taint_safety sigma | ].

    revert Horaat.
    eapply oraat_wp_action_correct.
    unfold Impl.rules, Impl.update_ready.
    repeat (repeat step_wp_oraat_safe; simpl).
    destruct_match.
    - repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match.
      + repeat (repeat step_wp_oraat_safe; simpl).
        prepare_finish.
        repeat constructor.
        * simplify_updates.
          apply plus_one_negate; auto.
        * simplify_updates.
        * unfold unsafe_get_job_stage.
          simplify_updates.
      + repeat (repeat step_wp_oraat_safe; simpl).
        prepare_finish.
        repeat constructor.
        * simplify_updates. apply plus_one_negate; auto.
        * simplify_updates.
        * unfold unsafe_get_job_stage. simplify_updates.
    - repeat (repeat step_wp_oraat_safe; simpl).
      destruct_match.
      + repeat (repeat step_wp_oraat_safe; simpl).
        destruct_match.
        * repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish.
          unfold post_reg_spec_to_prop; simpl.
          repeat constructor.
          { simplify_updates. apply plus_one_negate; auto. }
          { simplify_updates. }
          { unfold unsafe_get_job_stage. simplify_updates. }
        * repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish.
          unfold post_reg_spec_to_prop; simpl.
          repeat constructor.
          { simplify_updates. apply plus_one_negate; auto. }
          { simplify_updates. }
          { unfold unsafe_get_job_stage. simplify_updates. }
      + repeat (repeat step_wp_oraat_safe; simpl).
        destruct_match.
        * repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish.
          unfold post_reg_spec_to_prop; simpl.
          repeat constructor.
          { simplify_updates. apply plus_one_negate; auto. }
          { simplify_updates. }
          { unfold unsafe_get_job_stage. simplify_updates. }
        * repeat (repeat step_wp_oraat_safe; simpl).
          prepare_finish.
          unfold post_reg_spec_to_prop; simpl.
          repeat constructor.
          { simplify_updates. apply plus_one_negate; auto. }
          { simplify_updates. }
          { unfold unsafe_get_job_stage. simplify_updates. }
  Qed.
End ImplementationProofs.

Module Proofs := ScheduleProofs (ImplementationProofs).

Section TopLevelProofs.
  Ltac unfold_impl_invariant :=
    unfold WF_state, ImplInvariant__ext_ready_for_job, ImplInvariant__ext_output_reg,
                 ImplInvariant__NONE_OR_INIT, ImplInvariant__STAGE_F,
                 ImplInvariant__STAGE_G, ImplInvariant__NONE_zeroed.


  Ltac solve_initial :=
    repeat match goal with
           | H: reg_in_taint_list _ _ _ _ |- _ =>
             apply regs_in_taint_existsb in H
           | H : existsb (Nat.eqb _) _ = true |- _ =>
             apply existsb_exists in H; propositional
           | H: In ?x _ |- Impl.initial_state ?x = _  =>
             inversions H; [reflexivity |]
           | H: In ?x _ |- Impl.initial_state.[?x] = _  =>
             inversions H; [reflexivity |]
           | _ => simplify
           end.


  Lemma initial_invariant:
    ImplInvariant Impl.initial_state.
    constructor; unfold_impl_invariant.
    - unfold Impl.initial_state; intros; destruct_match; simplify_nat; auto.
      unfold get_reg, Impl.reg_types in *. rewrite SortedRegEnv.opt_get_map.
      destruct_match; simplify; auto.
      destruct_match; simplify; auto.
      + compute in Heqo0. simplify. auto.
      + rewrite zeroes_length. reflexivity.
    - reflexivity.
    - reflexivity.
    - intros. solve_initial. inversions H0.
    - intros. solve_initial. inversions H0.
    - intros. solve_initial. inversions H0.
   - intros. consider is_job_reg; subst.
      destruct tag; reflexivity.
  Qed.

  Theorem Invariant_step_preserved:
    forall impl_st (sigma: input_t -> ext_sigma_t) input log,
      Impl.wf_sigma sigma ->
      ImplInvariant impl_st ->
      interp_scheduler (sigma input) Impl.int_fn_env Impl.struct_env impl_st Impl.rules Impl.schedule = Success log ->
      ImplInvariant (commit_update impl_st log).
  Proof.
    intros * p_sigma HInv Hsched.
    assert (WF_log Impl.reg_types log) by (eapply Proofs.Step_WF_Log; eauto).
    eapply Proofs.Invariant_step_preserved'; eauto.
    eapply WF_commit_update; eauto; ri_solve.
  Qed.

  Theorem impl_step_implies_post:
    forall impl_st (sigma: input_t -> ext_sigma_t) input log,
      Impl.wf_sigma sigma ->
      ImplInvariant impl_st ->
      interp_scheduler (sigma input) Impl.int_fn_env Impl.struct_env impl_st Impl.rules Impl.schedule = Success log ->
      ImplPostCond impl_st (commit_update impl_st log) (sigma input).
  Proof.
    intros * p_sigma HInv Hsched.
    assert (WF_log Impl.reg_types log) by (eapply Proofs.Step_WF_Log; eauto).
    eapply Proofs.Invariant_step_preserved''; eauto.
    eapply WF_commit_update; eauto; ri_solve.
  Qed.

End TopLevelProofs.
