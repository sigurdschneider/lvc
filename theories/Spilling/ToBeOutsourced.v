Require Import List Map Env AllInRel Exp AppExpFree RenameApart RenamedApart.
Require Import IL Annotation AutoIndTac.
Require Import Liveness.Liveness LabelsDefined SetUtil.

(** * ToBeOutsourced *)

(* move somewhere to renamedApart *)
Lemma renamedApart_incl
      (s : stmt)
      (ra : ann (⦃var⦄ * ⦃var⦄))
  :
    renamedApart s ra
    -> match ra with
      | ann1 (D, D') an
        => union_fs (getAnn an) ⊆ D ∪ D'
      | ann2 (D, D') ans ant
        => union_fs (getAnn ans) ⊆ D ∪ D'
          /\ union_fs (getAnn ant) ⊆ D ∪ D'
      | annF (D, D') anF ant
        => (forall (ans : ann (⦃var⦄ * ⦃var⦄)) n,
              get anF n ans
              -> union_fs (getAnn ans) ⊆ D ∪ D')
          /\ union_fs (getAnn ant) ⊆ D ∪ D'
      | _ => True
      end
.
Proof.
  intros.
  invc H; simpl; unfold union_fs; eauto; set_simpl; pe_rewrite; repeat split;
    intros; inv_get; eauto with cset.
Qed.

(* to be moved to lookup_set / map *)
Lemma injective_on_map_inter
      (X : Type)
      `{OrderedType X}
      (D s t : ⦃X⦄)
      (f : X -> X)
  :
    Proper (_eq ==> _eq) f
    -> injective_on D f
    -> s ⊆ D
    -> t ⊆ D
    -> map f (s ∩ t) [=] map f s ∩ map f t
.
Proof.
  intros.
  apply incl_eq.
  - hnf; intros.
    cset_tac'.
    exploit (H1 x x0); eauto. eqs.
    rewrite H10 in *. eauto.
  - hnf; intros.
    cset_tac.
Qed.
