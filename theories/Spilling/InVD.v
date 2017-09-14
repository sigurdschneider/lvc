Require Import List Map Envs AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation AutoIndTac.
Require Import Liveness.Liveness LabelsDefined.

Set Implicit Arguments.

(** * InVD *)

Lemma x_VD (x : var) (VD D Ds D' : ⦃var⦄)
      (H9 : D' [=] {x; Ds})
      (ra_VD : D ∪ D' ⊆ VD)
  : x ∈ VD.
Proof.
  rewrite H9 in ra_VD.
  rewrite <- incl_right in ra_VD.
  apply add_incl in ra_VD as [x_VD _].
  eauto.
Qed.

Lemma Rx_VD (x : var) (R M VD : ⦃var⦄)
      (R_VD : R ⊆ VD) (M_VD : M ⊆ VD)
      (Sp L K Kx : ⦃var⦄)
      (H13 : Sp ⊆ R) (H16 : L ⊆ Sp ∪ M) (x_VD : x ∈ VD)
  : {x; (R \ K ∪ L) \ Kx} ⊆ VD.
Proof.
  apply incl_add_eq.
  split; eauto.
  rewrite H16.
  rewrite H13.
  cset_tac.
Qed.

Lemma R'_VD (R M VD : ⦃var⦄) (R_VD : R ⊆ VD) (M_VD : M ⊆ VD)
      (Sp L K : ⦃var⦄) (H16 : Sp ⊆ R) (H19 : L ⊆ Sp ∪ M)
  : R \ K ∪ L ⊆ VD.
Proof.
  rewrite H19.
  rewrite H16.
  cset_tac.
Qed.

Lemma M'_VD (R M VD : ⦃var⦄) (R_VD : R ⊆ VD) (M_VD : M ⊆ VD)
      (Sp : ⦃var⦄) (H13 : Sp ⊆ R)
  : Sp ∪ M ⊆ VD.
Proof.
  cset_tac.
Qed.

Lemma Rf_VD (R M VD : ⦃var⦄) (R_VD : R ⊆ VD) (M_VD : M ⊆ VD)
      (Sp L K R_f : ⦃var⦄) (Z0 : params) (H11 : Sp ⊆ R) (H12 : L ⊆ Sp ∪ M)
      (H18 : R_f \ of_list Z0 ⊆ R \ K ∪ L)
      (Z_VD : of_list Z0 ⊆ VD)
  : R_f ⊆ VD.
Proof.
  assert (R_f ⊆ R \ K ∪ L ∪ of_list Z0) as H18'.
  {
    rewrite <- H18.
    clear; cset_tac.
  }
  rewrite H18'.
  rewrite H12.
  rewrite H11.
  cset_tac.
Qed.

Lemma Mf_VD (R M VD : ⦃var⦄) (R_VD : R ⊆ VD) (M_VD : M ⊆ VD)
      (Sp M_f : ⦃var⦄) (Z0 : params) (H11 : Sp ⊆ R)
      (H19 : M_f \ of_list Z0 ⊆ Sp ∪ M)
      (Z_VD : of_list Z0 ⊆ VD)
  : M_f ⊆ VD.
Proof.
  assert (M_f ⊆ Sp ∪ M ∪ of_list Z0) as H19'.
  {
    rewrite <- H19.
    clear; cset_tac.
  }
  rewrite H19'.
  rewrite H11.
  clear - R_VD M_VD Z_VD; cset_tac.
Qed.

Lemma disj_empty_cut (s t : ⦃var⦄) (slot : var -> var)
  : t ⊆ s
    -> disj s (map slot s)
    -> s ∩ map slot t [=] ∅ .
Proof.
  intros sub disj.
  apply disj_intersection.
  eapply disj_2_incl; eauto with cset.
Qed.
