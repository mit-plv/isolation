Require Import koika.Frontend.
Require Import koika.AnnotatedSyntax.

  Ltac solve_In_to_find :=
    match goal with
    | |- In ?reg ?regs =>
        let H := fresh in
        assert (find (beq_dec reg) regs = Some reg) as H by reflexivity;
        apply find_some in H; propositional
   | |- In _ _ -> False =>
       eapply In_false; vm_compute; reflexivity
   end.
  Definition remove_regs {T} {EqDec : EqDec T} (reg_base reg_remove: list T) : list T :=
    filter (fun r => match find (fun r' => beq_dec r r') reg_remove with
                  | Some _ => false
                  | _ => true
                  end) reg_base.
  Lemma length_of_nat:
    forall len v,
    Datatypes.length (of_nat len v) = len.
  Proof.
    unfold of_nat. intros. rewrite firstn_fill_length. auto.
  Qed.
