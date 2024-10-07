(* Require Import koika.Frontend. *)
(* Require Koika.Frontend. *)
(* Require Import Koika.Interop. *)
(* Require Koika.Syntax. *)
(* Require Import koika.Frontend. *)
(* Require Import koikaExamples.KoikaConversion. *)

(* Module TestConversion. *)
(*   Require Import rv_cache_isolation.Common. *)
(*   Require Import rv_cache_isolation.Machine. *)
(*   Require Import rv_cache_isolation.External. *)

(*   Module Import Machine := Machine EnclaveParams. *)
(*   Existing Instance Machine.FiniteType_reg_t. *)
(*   Existing Instance FiniteType_ext_fn_t. *)
(*   Existing Instance Machine.Show_reg_t. *)
(*   Existing Instance Machine.Show_ext_fn_t. *)

(*   Definition reg_t := Machine._reg_t. *)
(*   Definition ext_fn_t := Machine._ext_fn_t. *)
(*   Definition reg_to_debug_id (r: reg_t) : debug_id_ty := *)
(*     (Show.show r, N.of_nat (finite_index r)). *)

(*   Definition ext_fn_to_debug_id (extfn: ext_fn_t) : debug_id_ty := *)
(*     (Show.show extfn, N.of_nat (finite_index extfn)). *)

(*   Definition struct_sigs := get_scheduler_structs R Sigma Machine.rules schedule. *)
(*   Definition struct_env := ltac:(_extract_success (struct_sig_to_struct_env struct_sigs)). *)
(*   (* Eval vm_compute in (List.length struct_env). *) *)
(*   (* Eval (beq_dec (nth struct_env  *) *)
(*   (* Eval vm_compute in (struct_env). *) *)
(*   (* Eval vm_compute in (add_structs RV32I.R RV32I.Sigma [] (RV32I.rv_rules Writeback)). *) *)

(*   Definition rules_list : (list (rule_name_t * (@action debug_id_ty))) := *)
(*     Eval vm_compute in *)
(* ltac:(_extract_success (convert_schedule R Sigma reg_to_debug_id ext_fn_to_debug_id struct_sigs Machine.rules schedule)). *)
(*   (* Goal False. *) *)
(*   (* Proof. *) *)
(*   (*   assert (is_success (convert_schedule Machine.lifted_core0_schedule) = true) by vm_reflect. *) *)
(*   (*   assert (is_success (convert_schedule Machine.lifted_mem_schedule) = true) by vm_reflect. *) *)
(*   (*   assert (is_success (convert_schedule Machine.lifted_sm_schedule) = true) by vm_reflect. *) *)
(*   (* Abort. *) *)

(*   Definition core0_schedule := ltac:(_extract_success (convert_scheduler Machine.lifted_core0_schedule)). *)
(*   Definition core1_schedule := ltac:(_extract_success (convert_scheduler Machine.lifted_core1_schedule)). *)
(*   Definition mem_schedule := ltac:(_extract_success (convert_scheduler Machine.lifted_mem_schedule)). *)
(*   Definition sm_schedule := ltac:(_extract_success (convert_scheduler Machine.lifted_sm_schedule)). *)
(*   Definition schedule := ltac:(_extract_success (convert_scheduler schedule)). *)

(*   Definition modular_schedule : list (@scheduler rule_name_t) := *)
(*     [core0_schedule; core1_schedule; mem_schedule; sm_schedule ]. *)

(*   Definition _id {X Y} (x: X * Y):= snd x. *)

(*   Instance EqDec_rule_name_t : EqDec rule_name_t := _. *)

(*   Definition rules (rl: rule_name_t) : @action debug_id_ty := *)
(*     match find (fun '(rl', _) => beq_dec rl' rl) rules_list with *)
(*     | Some (_, rl) => rl *)
(*     | _ => Fail 0 *)
(*     end. *)

(*   Definition id_rules (rl: rule_name_t) : @action N:= *)
(*     id_transform_action snd (rules rl). *)
(*   Definition id_struct_env := (id_transform_struct_env _id struct_env). *)

(*   Lemma impl_interp_modular_schedule : *)
(*     forall sigma st log, *)
(*         interp_scheduler *)
(*           sigma [] id_struct_env (st) id_rules *)
(*                schedule = Success log -> *)
(*       interp_modular_schedule *)
(*           sigma [] *)
(*                id_struct_env *)
(*                id_rules *)
(*                (st) *)
(*                modular_schedule = *)
(*         Success (commit_update st log.(Log__koika), log.(Log__ext)). *)
(*   Proof. *)
(*     intros. eapply check_modular_conflicts_correct. *)
(*     - vm_reflect. *)
(*     - assumption. *)
(*   Qed. *)

(*   Definition reg_env : reg_types_t := *)
(*     map (fun r => (_id (reg_to_debug_id r), type_sz (R r))) (@finite_elements _ FiniteType_reg_t). *)

(*   Definition ext_fn_tys : ext_fn_types_t := *)
(*     map (fun ext => (_id (ext_fn_to_debug_id ext),(type_sz (Sigma ext).(arg1Sig), type_sz ((Sigma ext).(retSig))))) *)
(*         (@finite_elements _ FiniteType_ext_fn_t). *)
(*   Lemma typecheck_schedule_Success : *)
(*     typecheck_schedule reg_env ext_fn_tys [] id_struct_env schedule id_rules = Success tt. *)
(*   Proof. vm_compute. reflexivity. Qed. *)


(*   (* Goal False. *) *)
(*   (*   assert (oraat_ok [] id_rules (SemanticUtils.list_of_schedule core0_schedule) = true) by vm_reflect. *) *)
(*   (*   assert (oraat_ok [] id_rules (SemanticUtils.list_of_schedule core1_schedule) = true) by vm_reflect. *) *)

(*   (*   assert (oraat_ok [] id_rules (SemanticUtils.list_of_schedule sm_schedule) = true) by vm_reflect. *) *)
(*   (*   assert (oraat_ok [] id_rules (SemanticUtils.list_of_schedule mem_schedule) = true) by vm_reflect. *) *)
(*   (* Abort. *) *)

(* End TestConversion. *)

(* (* Record Koika_package_t (pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t : Type) : Type := Build_koika_package_t *) *)
(* (*   { koika_var_names : Show.Show var_t; *) *)
(* (*     koika_fn_names : Show.Show fn_name_t; *) *)
(* (*     koika_reg_names : Show.Show reg_t; *) *)
(* (*     koika_reg_types : reg_t -> type; *) *)
(* (*     koika_reg_init : forall r : reg_t, koika_reg_types r; *) *)
(* (*     koika_reg_finite : FiniteType reg_t; *) *)
(* (*     koika_ext_fn_types : ext_fn_t -> ExternalSignature; *) *)
(* (*     koika_rules : rule_name_t -> TypedSyntax.rule pos_t var_t fn_name_t koika_reg_types koika_ext_fn_types; *) *)
(* (*     koika_rule_external : rule_name_t -> bool; *) *)
(* (*     koika_rule_names : Show.Show rule_name_t; *) *)
(* (*     koika_scheduler : Syntax.scheduler pos_t rule_name_t; *) *)
(* (*     koika_module_name : string }. *) *)
