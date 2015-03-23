Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation SetOperations MoreList.

Set Implicit Arguments.

(** * Renamed-apart (formally) *)
(** Every subterm is annotated with two sets [D] and [D'] such that
    [D] contains all free variables of the subterm and [D'] is extactly
    the set of variables that occur in a binding position. *)
Inductive renamedApart : stmt -> ann (set var * set var) -> Prop :=
  | renamedApartExp x e s D D' D'' an
    : x ∉ D
      -> Exp.freeVars e ⊆ D
      -> renamedApart s an
      -> pe (getAnn an) ({x; D}, D')
      -> D'' [=] {x; D'}
      -> renamedApart (stmtLet x e s) (ann1 (D, D'') an)
  | renamedApartIf  D D' Ds Dt e s t ans ant
    : Exp.freeVars e ⊆ D
      -> Ds ∩ Dt [=] ∅
      -> Ds ∪ Dt [=] D'
      -> renamedApart s ans
      -> renamedApart t ant
      -> pe (getAnn ans) (D, Ds)
      -> pe (getAnn ant) (D, Dt)
      -> renamedApart (stmtIf e s t) (ann2 (D, D') ans ant)
  | renamedApartRet D D' e
    : Exp.freeVars e ⊆ D
      -> D' [=] ∅
      -> renamedApart (stmtReturn e) (ann0 (D, D'))
  | renamedApartGoto D D' f Y
    : list_union (List.map Exp.freeVars Y) ⊆ D
      -> D' [=] ∅
      -> renamedApart (stmtApp f Y) (ann0 (D, D'))
  | renamedApartExtern x f Y s D D' D'' an
    : x ∉ D
      -> list_union (List.map Exp.freeVars Y) ⊆ D
      -> renamedApart s an
      -> pe (getAnn an) ({x; D}, D')
      -> D'' [=] {x; D'}
      -> renamedApart (stmtExtern x f Y s) (ann1 (D, D'') an)
  | renamedApartLet D D' s t Ds Dt Z ans ant
    : of_list Z ∩ D [=] ∅
      -> (Ds ++ of_list Z) ∩ Dt [=] ∅
      -> Ds ∪ Dt ∪ of_list Z [=] D'
      -> renamedApart s ans
      -> pe (getAnn ans) (of_list Z ∪ D, Ds)
      -> renamedApart t ant
      -> pe (getAnn ant) (D, Dt)
      -> unique Z
      -> renamedApart (stmtFun Z s t) (ann2 (D,D') ans ant).

(** ** Morphisms *)

Lemma renamedApart_ext s an an'
  : ann_R (@pe _ _) an an'
  -> renamedApart s an
  -> renamedApart s an'.
Proof.
  intros. general induction H0; simpl; invt (ann_R (@pe var _));
          invt (@pe var _); eauto using renamedApart.
  - econstructor. rewrite <- H8; eauto. rewrite <- H8; eauto.
    eapply IHrenamedApart; eauto. rewrite <- H8. rewrite (ann_R_get H9) in H2. eauto.
    rewrite <- H11. eauto.

  - econstructor; eauto. rewrite <- H7; eauto. rewrite <- H12; eauto.
    rewrite <- (ann_R_get H10). rewrite <- H7. eauto.
    rewrite <- (ann_R_get H11). rewrite <- H7. eauto.

  - econstructor; eauto. rewrite <- H5; eauto. rewrite <- H7; eauto.
  - econstructor. rewrite <- H5; eauto. rewrite <- H7; eauto.

  - econstructor. rewrite <- H8; eauto. rewrite <- H8; eauto.
    eapply IHrenamedApart; eauto. rewrite <- H8.
    rewrite <- (ann_R_get H9). eauto. rewrite <- H11; eauto.

  - econstructor; eauto. rewrite <- H8; eauto.
    rewrite <- H13; eauto.
    rewrite <- H8. rewrite <- (ann_R_get H11); eauto.
    rewrite <- H8. rewrite <- (ann_R_get H12); eauto.
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
  intros. general induction H; simpl; eauto.
  - rewrite H0, IHrenamedApart, H2. simpl.
    clear_all; cset_tac; intuition.
  - rewrite H, IHrenamedApart1, IHrenamedApart2. rewrite H4, H5; simpl.
    cset_tac; intuition.
  - rewrite H0, IHrenamedApart, H2; simpl. cset_tac; intuition.
  - rewrite IHrenamedApart1, IHrenamedApart2. inv H3; inv H5; simpl.
    rewrite H10, H13. cset_tac; intuition.
Qed.

Lemma renamedApart_occurVars s an
  : renamedApart s an -> definedVars s [=] snd (getAnn an).
Proof.
  intros. general induction H; simpl; eauto.
  - rewrite H3, IHrenamedApart, H2. simpl.
    clear_all; cset_tac; intuition.
  - rewrite IHrenamedApart1, IHrenamedApart2. rewrite H4, H5; simpl; eauto.
  - cset_tac; intuition; eauto.
  - cset_tac; intuition; eauto.
  - rewrite H3, IHrenamedApart, H2. simpl.
    clear_all; cset_tac; intuition.
  - rewrite IHrenamedApart1, IHrenamedApart2. rewrite H3, H5; simpl. eauto.
Qed.

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
  general induction H; simpl.
  - econstructor; eauto.
    + rewrite H. reflexivity.
  - econstructor; eauto.
    + rewrite H. reflexivity.
  - econstructor; eauto.
    + rewrite H. reflexivity.
Qed.

Lemma not_in_minus X `{OrderedType X} (s t: set X) x
: x ∉ s
  -> x ∉ s \ t.
Proof.
  cset_tac; intuition.
Qed.

Hint Resolve not_in_minus : cset.

Lemma not_incl_minus X `{OrderedType X} (s t u: set X)
: s ⊆ t
  -> disj s u
  -> s ⊆ t \ u.
Proof.
  cset_tac; intuition.
Qed.

Hint Resolve not_incl_minus : cset.
Hint Resolve disj_1_incl disj_2_incl : cset.

Hint Extern 20 (pe ?a ?a) => reflexivity.

Lemma renamedApart_minus D an an' s
  : disj (occurVars s) D
    -> renamedApart s an
    -> ann_R (@pe _ _) an' (mapAnn (pminus D) an)
    -> renamedApart s an'.
Proof.
  intros ? ? PE. general induction H0; try rewrite PE; simpl in * |- *.
  - econstructor; eauto with cset.
    + rewrite getAnn_mapAnn. pe_rewrite.
      econstructor; eauto.
      revert H H4; unfold disj; clear_all; cset_tac; intuition.
      invc H2; eapply H1; eauto.
  - econstructor; [|eapply H0| | | | |]; eauto with cset.
    + rewrite getAnn_mapAnn. pe_rewrite; eauto.
    + rewrite getAnn_mapAnn. pe_rewrite; eauto.
  - econstructor; eauto with cset.
  - econstructor; eauto with cset.
  - econstructor; eauto with cset.
    + rewrite getAnn_mapAnn. pe_rewrite.
      econstructor; eauto.
      revert H H4; unfold disj; clear_all; cset_tac; intuition.
      invc H2; eapply H1; eauto.
  - econstructor; [| |eapply H1| | | | |]; eauto with cset.
    + change (disj (of_list Z) (D \ D0)). rewrite minus_incl; eauto.
    + rewrite getAnn_mapAnn; simpl. pe_rewrite; econstructor; eauto.
      rewrite minus_dist_union. rewrite minus_inane_set; eauto.
      eapply disj_1_incl; eauto with cset.
    + rewrite getAnn_mapAnn; simpl. pe_rewrite; constructor; eauto.
Qed.

(** ** The two annotated sets are disjoint. *)

Lemma renamedApart_disj s G
: renamedApart s G
  -> disj (fst (getAnn G)) (snd (getAnn G)).
Proof.
  intros. general induction H; simpl.
  - rewrite H3. rewrite H2 in *. simpl in *.
    revert IHrenamedApart H. unfold disj.
    clear_all; cset_tac; intuition; cset_tac; eauto.
  - rewrite H4 in *. rewrite H5 in *. simpl in *.
    rewrite <- H1. rewrite disj_app; eauto.
  - rewrite H0. eauto using disj_empty.
  - rewrite H0. eauto using disj_empty.
  - rewrite H3. rewrite H2 in *. simpl in *.
    revert IHrenamedApart H. unfold disj.
    clear_all; cset_tac; intuition; cset_tac; eauto.
  - rewrite <- H1. repeat rewrite disj_app.
    rewrite H3,H5 in *; simpl in *; eauto.
    split. split; eauto. rewrite incl_right; eauto.
    symmetry; eauto.
Qed.



(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
