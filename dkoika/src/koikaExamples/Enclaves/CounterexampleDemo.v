(*! Demo counterexample for SMT toolchain *)
Require Import rv_isolation.Common.
Require Import rv_isolation.SecurityMonitor.
Require Import rv_isolation.RVCore.
Require Import koika.Frontend.
Require Import koikaExamples.Enclaves.Common.
Require Import koikaExamples.Enclaves.TypeDefs.
Require Import koikaExamples.Enclaves.Impl.
Require Import koikaExamples.Enclaves.Spec.
Require Import koikaExamples.Enclaves.Theorem.
Require Import koikaExamples.Enclaves.Utils.
Require Import FunctionalExtensionality.
Require Import koika.Symbolic.
Require Import koikaExamples.Enclaves.ExtractionUtils.
Require Import koika.AnnotatedSyntax.
Require Import koikaExamples.Enclaves.ProofUtils.


Import ListNotations.

Instance Show_core_rule' : Koika.Show.Show rv_rules_t := _.
Instance Show_core_rule : Show rv_rules_t :=
  { show := Show_core_rule'.(Koika.Show.show)}.

Inductive core_custom_prop_names :=
| PurgeReset
| CoreIdSame
| CoreTaint
| CoreExt (id: N)
| CorePurgedPreserve
| CorePurgedMachine
| CorePurgedWait
.

Module Type Core_sig.
  Parameter core_id : ind_core_id.
End Core_sig.

  Import Core.
  Import PfHelpers.
  Existing Instance SecurityMonitor.FiniteType_reg_t.
  Notation finite_elements := FiniteType.finite_elements.

  Definition regs_to_reset core : list debug_id_ty :=
      map reg_to_debug_id
          (Utils.PfHelpers.core_regs_to_reset core).
  Notation reg_t := debug_id_ty.

Module CoreSymbDefs.
  Definition invariant (core: ind_core_id) (reg_fn: reg_t -> sval) : list (core_custom_prop_names * fancy_spred) :=
    [(PurgeReset, {{{ `reg_fn (_crid core purge)` = #(_enum purge_state "Purged") ->
                      {forall x in (regs_to_reset core),
                       `reg_fn x` = #(zeroes (unsafe_lookup_reg_type (_id x)))
                      }
                  }}}
     );
     (CoreIdSame, {{{ `reg_fn (_crid core core_id)` = #(cid_to_bits core)}}})
    ].

  (*! What if PurgeReset is not in our assumption? *)
  Definition pre_conds (core: ind_core_id) (reg_init : reg_t -> sval) : list (core_custom_prop_names * fancy_spred) :=
  (* Now try adding CoreIdSame *)
     [(CoreIdSame, {{{ `reg_init(_crid core core_id)` = #(cid_to_bits core)}}})].

    (* [] (* ++ (invariant core reg_init) *). *)

  Definition ext_empty (extfn: debug_id_ty -> sval): list (core_custom_prop_names * fancy_spred) :=
    map (fun fn => (CoreExt (_id fn), {{{ `extfn fn` = #(zeroes (unsafe_get_ext_fn_arg_type (_id fn))) }}}))
      (map fst ext_fn_tys).
  Definition post_conds' (core: ind_core_id) (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval): list (core_custom_prop_names * fancy_spred) :=
    [(CoreTaint, {{{ forall x in (remove_regs (reg_list) (map reg_to_debug_id (core_regs core))),
                     `reg_final x` = `reg_init x`
                 }}})
    ;(CorePurgedPreserve, {{{ {`reg_init (_crid core purge)` = #(_enum purge_state "Ready") \/
                               `reg_init (_crid core purge)` = #(_enum purge_state "Purged")} ->
                               `reg_final (_crid core purge)` = `reg_init (_crid core purge)`
                              }}})
    ;(CorePurgedMachine, {{{ `reg_init (_crid core purge)` = #(_enum purge_state "Init") ->
                             {`reg_final (_crid core purge)` = #(_enum purge_state "Ready") \/
                              `reg_final (_crid core purge)` = #(_enum purge_state "Init")}
                         }}})
    ;(CorePurgedWait, {{{ `reg_init (_crid core purge)` = #(_enum purge_state "Purged")->
                          {forall x in (map reg_to_debug_id (core_regs core)),
                           `reg_final x` = `reg_init x`
                          }
                      }}})
    ] ++ (ext_empty ext_log).

  Definition post_conds (core: ind_core_id) (reg_init reg_final: reg_t -> sval) (ext_log: debug_id_ty -> sval): list (core_custom_prop_names * fancy_spred) :=
    post_conds' core reg_init reg_final ext_log ++ (invariant core reg_final).

    Definition impl_machine : machine_t :=
      {| file_registers := reg_types;
         file_ext_sigma := ext_fn_tys;
         file_struct_defs := struct_defs;
      |}.
End CoreSymbDefs.

Require Import koikaExamples.Enclaves.External.
Existing Instance Show_rule'.
Existing Instance Show_rule.

Module Type Core0_Defs (EnclaveParams: EnclaveParams_sig)
                       (SecurityParams: SecurityParams_sig EnclaveParams).
  Import SecurityParams.Machine.
  Import SecurityParams.Impl.
  Module Core0Params <: Core_sig.
    Definition core_id := CoreId0.
  End Core0Params.

  Import CoreSymbDefs.

  Section ImplMachine.
    Notation reg_t := (@reg_t debug_id_ty).

    Definition impl_schedule_list : list (Machine.rule_name_t * string) :=
      map (fun rl => (rl, show rl)) (list_of_schedule (core0_schedule)).

    Definition impl_typecheck_fn (rl: action) : result (aaction * nat) unit :=
      typecheck_rule reg_types ext_fn_tys int_fns struct_defs
              (inline_rule int_fns rl).

    Definition impl_schedule :=
      preprocess_schedule impl_typecheck_fn rules impl_schedule_list.

    (* Goal preprocess_schedule_success impl_typecheck_fn rules impl_schedule_list = true. *)
    (* Proof. vm_compute; reflexivity. Qed. *)

  End ImplMachine.
  Definition file: file_t :=
    {| file_machines := Single impl_machine impl_schedule;
       file_assumptions := preprocess_fancy_spreds (pre_conds CoreId0 impl_init );
       file_assertions := preprocess_fancy_spreds (post_conds CoreId0 impl_init impl_final impl_final_ext);
    |}.
End Core0_Defs.

(* Uncomment this out
Module TestCounterexample.
  Module SecurityParams := Empty <+ SecurityParams_sig EnclaveParams.
  Module Core0Defs := Empty <+ Core0_Defs EnclaveParams SecurityParams.

  Module Test0.
    Definition file := Eval vm_compute in Core0Defs.file.
  End Test0.
End TestCounterexample.
Extraction "TestCounterexample.Test0.ml" struct_sz vect_t TestCounterexample.Test0.file.
*)
