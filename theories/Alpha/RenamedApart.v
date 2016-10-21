Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env IL Annotation SetOperations MoreList Indexwise PairwiseDisjoint.

Set Implicit Arguments.

(** * Renamed-apart (formally) *)
(** Every subterm is annotated with two sets [D] and [D'] such that
    [D] contains all free variables of the subterm and [D'] is extactly
    the set of variables that occur in a binding position. *)

Definition defVars (Zs:params * stmt) (a:ann (set var * set var)) := of_list (fst Zs) ∪ snd (getAnn a).

Hint Unfold defVars.

Definition funConstr D Dt (Zs:params * stmt) a :=
  fst (getAnn a) [=] of_list (fst Zs) ∪ D
  /\ NoDupA eq (fst Zs)
  /\ disj (of_list (fst Zs)) D
  /\ disj (of_list (fst Zs) ∪ snd (getAnn a)) Dt.

Inductive renamedApart : stmt -> ann (set var * set var) -> Prop :=
  | renamedApartExp x e s D Ds D' an
    : x ∉ D
      -> Exp.freeVars e ⊆ D
      -> renamedApart s an
      -> D' [=] {x; Ds}
      -> pe (getAnn an) ({x; D}, Ds)
      -> renamedApart (stmtLet x e s) (ann1 (D, D') an)
  | renamedApartIf  D D' Ds Dt e s t ans ant
    : Op.freeVars e ⊆ D
      -> disj Ds Dt
      -> Ds ∪ Dt [=] D'
      -> renamedApart s ans
      -> renamedApart t ant
      -> pe (getAnn ans) (D, Ds)
      -> pe (getAnn ant) (D, Dt)
      -> renamedApart (stmtIf e s t) (ann2 (D, D') ans ant)
  | renamedApartRet D D' e
    : Op.freeVars e ⊆ D
      -> D' [=] ∅
      -> renamedApart (stmtReturn e) (ann0 (D, D'))
  | renamedApartGoto D D' f Y
    : list_union (List.map Op.freeVars Y) ⊆ D
      -> D' [=] ∅
      -> renamedApart (stmtApp f Y) (ann0 (D, D'))
  | renamedApartLet D D' F t Dt ans ant
    : length F = length ans
      -> (forall n Zs a, get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
      -> indexwise_R (funConstr D Dt) F ans
      -> pairwise_ne disj (zip defVars F ans)
      -> renamedApart t ant
      -> pe (getAnn ant) (D, Dt)
      -> list_union (zip defVars F ans) ∪ Dt  [=] D'
      -> renamedApart (stmtFun F t) (annF (D,D') ans ant).

(** ** Morphisms *)

Lemma renamedApart_ext s an an'
  : ann_R (@pe _ _) an an'
  -> renamedApart s an
  -> renamedApart s an'.
Proof.
  intros.
  general induction H0; simpl; invt (ann_R (@pe var _));
  invt (@pe var _); eauto using renamedApart.
  - econstructor; try srewrite c; try srewrite d; eauto.
    rewrite <- (ann_R_get H9). eauto.
  - econstructor; try srewrite c; try srewrite d; eauto.
    + rewrite <- (ann_R_get H10); eauto.
    + rewrite <- (ann_R_get H11); eauto.

  - econstructor; try srewrite c; try srewrite d; eauto.
  - econstructor; try srewrite c; try srewrite d; eauto.
  - assert (PIR2 Equal (zip defVars F bns) (zip defVars F ans)).
    { eapply zip_ext_PIR2; eauto; try congruence.
      intros. get_functional.
      exploit H14; eauto. unfold defVars.
      rewrite H13. reflexivity.
    }
    econstructor; try srewrite c; try srewrite d; eauto with len.
    + intros. edestruct (get_length_eq _ H13 (eq_sym H12)).
      eapply H1; eauto.
    + hnf; intros. edestruct (get_length_eq _ H13 (eq_sym H12)).
      exploit H2; eauto. destruct H18. dcr.
      exploit H14; eauto. hnf. rewrite <- H10.
      instantiate (1:=Dt).
      rewrite <- H19; eauto.
    + eapply pairwise_disj_PIR2; eauto. symmetry; eauto.
    + rewrite <- H15; eauto.
    + rewrite H8. eauto.
Qed.

Instance renamedApart_morphism
: Proper (eq ==> (ann_R (@pe _ _)) ==> iff) renamedApart.
Proof.
  intros x s t A; subst. intros. split; intros.
  eapply renamedApart_ext; eauto.
  eapply renamedApart_ext; try symmetry; eauto.
Qed.

(** ** Relation to freeVars and occurVars *)
Lemma renamedApart_freeVars s an
  : renamedApart s an -> freeVars s ⊆ fst (getAnn an).
Proof.
  intros. general induction H; simpl; eauto; pe_rewrite.
  - rewrite IHrenamedApart, H0.
    clear_all; cset_tac; intuition.
  - rewrite H, IHrenamedApart1, IHrenamedApart2. cset_tac.
  - rewrite IHrenamedApart.
    rewrite (@list_union_incl _ _ _ _ D); eauto with cset.
    intros ? ? GET. inv_map GET.
    edestruct (get_length_eq _ H7 H); eauto.
    rewrite H1; eauto.
    edestruct H2; eauto; dcr; eauto with cset.
Qed.

Lemma renamedApart_occurVars s an
  : renamedApart s an -> definedVars s [=] snd (getAnn an).
Proof.
  intros.
  general induction H; simpl; eauto;
  pe_rewrite; srewrite D'; eauto with cset.
  - rewrite IHrenamedApart.
    eapply eq_union_lr; eauto.
    eapply list_union_eq; eauto with len.
    intros. inv_map H7. inv_zip H8. get_functional; subst.
    rewrite H1; eauto. unfold defVars. eauto with cset.
Qed.

(* TODO(sigurd) find a home for this definition *)
Definition pminus (D'':set var) (s:set var * set var) :=
  match s with
    | pair s s' => (s \ D'', s')
  end.

Instance pminus_morphism
: Proper (Equal ==> (@pe _ _) ==> (@pe _ _) ) pminus.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl; econstructor. rewrite H1, <- H. reflexivity.
  eauto.
Qed.

Instance mapAnn_pminus_morphism G'
  : Proper (ann_R (@pe _ _) ==> ann_R (@pe _ _)) (mapAnn (pminus G')).
Proof.
  unfold Proper, respectful; intros.
  general induction H; simpl; constructor; eauto with len pe.
  - intros. inv_map H4. inv_map H5. eauto.
Qed.

Lemma renamedApart_minus D an an' s
  : disj (occurVars s) D
    -> renamedApart s an
    -> ann_R (@pe _ _) an' (mapAnn (pminus D) an)
    -> renamedApart s an'.
Proof.
  intros DISJ RN PE. revert an' PE.
  induction RN; indros; try rewrite PE; simpl in * |- *.
  - econstructor; eauto 20 with cset pe ann.
  - econstructor; eauto with cset pe ann.
  - econstructor; eauto with cset.
  - econstructor; eauto with cset.
  - econstructor; eauto with cset len.
    + intros ? ? ? GET1 GET2. inv_map GET2. eapply H1; eauto.
      eapply disj_1_incl; eauto.
      rewrite <- get_list_union_map; eauto. cset_tac.
    + hnf; intros ? ? ? GET1 GET2.
      inv_map GET2. edestruct H2; eauto; dcr. instantiate (1:=Dt).
      hnf. rewrite getAnn_mapAnn.
      destruct (getAnn x); simpl in *.
      assert (disj (of_list (fst a)) D).
      eapply disj_1_incl; eauto.
      rewrite <- get_list_union_map; eauto. cset_tac; intuition.
      split. rewrite H7.
      revert H8; unfold disj; clear_all; cset_tac; intuition; eauto.
      eauto with cset.
    + eapply pairwise_disj_PIR2; eauto.
      eapply zip_ext_PIR2; eauto. rewrite map_length; eauto.
      intros ? ? ? ? ? GET1 GET2 GET3 GET4. get_functional; subst.
      inv_map GET4.
      unfold defVars. rewrite getAnn_mapAnn. destruct (getAnn y); reflexivity.
    + eauto with cset pe ann.
    + rewrite list_union_eq; eauto with len.
      intros ? ? ? GET1 GET2. inv_zip GET1. inv_zip GET2. inv_map H7.
      get_functional; subst. unfold defVars.
      rewrite getAnn_mapAnn. destruct (getAnn x2); simpl. reflexivity.
Qed.

(** ** The two annotating sets are disjoint. *)

Lemma renamedApart_disj s G
: renamedApart s G
  -> disj (fst (getAnn G)) (snd (getAnn G)).
Proof.
  intros. general induction H; simpl; pe_rewrite; try srewrite D'.
  - eauto with cset.
  - eauto with cset.
  - eauto with cset.
  - eauto with cset.
  - eapply disj_app; split; eauto.
    + symmetry. rewrite <- list_union_disjunct.
      intros ? ? GET. inv_zip GET.
      exploit H1; eauto.
      unfold defVars.
      edestruct H2; eauto; dcr. rewrite H10 in H9.
      symmetry.
      eapply disj_app; split.
      symmetry; eauto.
      eauto with cset.
Qed.
