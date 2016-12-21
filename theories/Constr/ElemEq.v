Require Export Setoid Coq.Classes.Morphisms Omega.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import CSetNotation CSetTac CSetBasic.

Definition elem_eq {X} `{OrderedType X} (x y: list X) := of_list x [=] of_list y.

Instance elem_eq_refl X `{OrderedType X} : Reflexive (@elem_eq X _).
hnf; intros. hnf. cset_tac.
Qed.

Definition elem_incl {X} `{OrderedType X} (x y: list X) := of_list x [<=] of_list y.

Instance elem_incl_refl X `{OrderedType X} : Reflexive (@elem_incl _ _).
hnf; intros. hnf. cset_tac.
Qed.

Lemma elem_eq_sym_proof
      (X Y : Type)
      `{OrderedType X}
      `{OrderedType Y}
      (f : list X -> list Y)
  :
    (forall (xl xl' : list X),
      of_list xl ⊆ of_list xl' -> of_list (f xl) ⊆ of_list (f xl'))
    -> (forall (xl xl' : list X),
          elem_eq xl xl' -> elem_eq (f xl)  (f xl'))
.
Proof.
  intros.
  unfold elem_eq in H2.
  unfold elem_eq.
  apply eq_incl in H2 as [incl1 incl2].
  eapply H1 in incl1.
  eapply H1 in incl2.
  apply incl_eq; eauto.
Qed.

Lemma InA_map_inv X Y (R:X->X->Prop) (R':Y->Y->Prop) `{Reflexive _ R'} (f:Y->X) L x
: InA R x (List.map f L)
  -> exists y, InA R' y L /\ R x (f y).
Proof.
  intros. general induction H0; destruct L; simpl in *; inv Heql.
  - eexists y0; split; eauto using InA.
  - edestruct IHInA; try reflexivity; eauto; dcr.
    eexists; split; eauto.
Qed.

Lemma InA_map X Y (R:X->X->Prop) (R':Y->Y->Prop)
      (f:X->Y) (L:list X) x
      `{Proper _ (R ==> R') f}
: InA R x L
  -> InA R' (f x) (List.map f L).
Proof.
  intros IN. general induction IN; simpl in *.
  - econstructor; eauto using InA.
  - econstructor 2; eauto.
Qed.

Lemma elem_eq_map X `{OrderedType X} Y `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f} (L L' : list X)
  : elem_eq L L' -> elem_eq (f ⊝ L) (f ⊝ L') .
Proof.
  apply elem_eq_sym_proof.
  clear L L'; intros ? ? INCL.
  general induction xl;
    simpl in *; eauto.
  - cset_tac.
  - rewrite IHxl with (xl':=xl');
      simpl; eauto.
    + assert (a ∈ of_list xl') as a_in.
      {
        rewrite <- INCL.
        clear; cset_tac.
      }
      enough (f a ∈ of_list (f ⊝ xl')) as sla_in.
      {
        apply incl_singleton in sla_in.
        rewrite add_union_singleton.
        rewrite sla_in.
        clear; cset_tac.
      }
      apply of_list_1.
      apply of_list_1 in a_in.
      eapply InA_map; eauto.
    + rewrite <- INCL.
      clear; cset_tac.
Qed.
