Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation SetOperations MoreList Indexwise.

Set Implicit Arguments.

(** * Renamed-apart (formally) *)
(** Every subterm is annotated with two sets [D] and [D'] such that
    [D] contains all free variables of the subterm and [D'] is extactly
    the set of variables that occur in a binding position. *)

Definition defVars (Zs:params * stmt) (a:ann (set var * set var)) := of_list (fst Zs) ∪ snd (getAnn a).

Definition pairwise_ne {X} (P:X->X->Prop) (L:list X) :=
  forall n m a b, n <> m -> get L n a -> get L m b -> P a b.

Lemma pairwise_ne_rev X (P:relation X) (L: list X)
: pairwise_ne P L
  -> pairwise_ne P (rev L).
Proof.
  intros; hnf; intros.
  exploit (get_range H1); eauto.
  exploit (get_range H2); eauto.
  eapply get_rev in H1.
  eapply get_rev in H2.
  eapply H; try eapply H1; try eapply H2; eauto.
  rewrite rev_length in H3.
  rewrite rev_length in H4.
  omega.
Qed.

Hint Unfold defVars.

Definition funConstr D Dt (Zs:params * stmt) a :=
  fst (getAnn a) [=] of_list (fst Zs) ∪ D
  /\ unique (fst Zs)
  /\ disj (of_list (fst Zs)) D
  /\ disj (of_list (fst Zs) ∪ snd (getAnn a)) Dt.

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
      -> disj Ds Dt
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

Lemma zip_ext X Y Z (f f':X -> Y -> Z) L L'
 : (forall x y n, get L n x -> get L' n y -> f x y = f' x y) -> zip f L L' = zip f' L L'.
Proof.
  general induction L; destruct L'; simpl; eauto.
  f_equal; eauto using get.
Qed.

Lemma zip_ext_PIR2 X Y Z (f:X -> Y -> Z) X' Y' Z' (f':X'->Y'->Z') (R:Z->Z'->Prop) L1 L2 L1' L2'
: length L1 = length L2
  -> length L1' = length L2'
  -> length L1 = length L1'
  -> (forall n x y x' y', get L1 n x -> get L2 n y -> get L1' n x' -> get L2' n y' -> R (f x y) (f' x' y'))
  -> PIR2 R (zip f L1 L2) (zip f' L1' L2').
Proof.
  intros A B C.
  length_equify. general induction A; inv B; inv C; simpl; eauto 50 using PIR2, get.
Qed.

Definition pairwise_disj_PIR2 X `{OrderedType X} L L'
: pairwise_ne disj L
  -> PIR2 Equal L L'
  -> pairwise_ne disj L'.
Proof.
  unfold pairwise_ne; intros.
  eapply PIR2_nth_2 in H3; eauto; dcr.
  eapply PIR2_nth_2 in H4; eauto; dcr.
  rewrite <- H7, <- H8; eauto.
Qed.


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

  - assert (PIR2 Equal (zip defVars F bns) (zip defVars F ans)).
    { eapply zip_ext_PIR2; eauto; try congruence.
      intros. get_functional; subst.
      exploit H14; eauto. unfold defVars. rewrite H8. reflexivity.
    }
    econstructor; eauto.
    + congruence.
    + intros. edestruct (get_length_eq _ H13 (eq_sym H12)).
      eapply H1; eauto.
    + hnf; intros. edestruct (get_length_eq _ H13 (eq_sym H12)).
      exploit H2; eauto. destruct H18. dcr.
      exploit H14; eauto. hnf. rewrite H19 in *. rewrite <- H10.
      instantiate (1:=Dt).
      intuition eauto.
    + eapply pairwise_disj_PIR2; eauto. symmetry; eauto.
    + rewrite <- H10. rewrite <- H15; eauto.
    + rewrite H8. rewrite <- H16; eauto.
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
  - pe_rewrite. rewrite IHrenamedApart.
    rewrite list_union_incl. instantiate (1:=D). cset_tac; intuition.
    intros. inv_map H7.
    edestruct (get_length_eq _ H8 H); eauto.
    rewrite H1; eauto. edestruct H2; eauto; dcr.
    rewrite H11. clear_all; cset_tac; intuition.
    cset_tac; intuition.
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
  - pe_rewrite. rewrite IHrenamedApart.
    rewrite list_union_eq; eauto.
    rewrite map_length, zip_length2; eauto.
    intros. inv_map H7. inv_zip H8. get_functional; subst.
    rewrite H1; eauto. unfold defVars. cset_tac; intuition.
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
  - econstructor; eauto.
    + rewrite H; reflexivity.
    + repeat rewrite map_length; eauto.
    + intros. inv_map H4. inv_map H5. eauto.
Qed.

Lemma renamedApart_minus D an an' s
  : disj (occurVars s) D
    -> renamedApart s an
    -> ann_R (@pe _ _) an' (mapAnn (pminus D) an)
    -> renamedApart s an'.
Proof.
  intros ? ? PE. general induction H0; try rewrite PE; simpl in * |- *.
  - econstructor; eauto with cset.
    + eapply IHrenamedApart. instantiate (1:=D0). eauto with cset.
      reflexivity.
    + rewrite getAnn_mapAnn. pe_rewrite.
      econstructor; eauto.
      revert H H4; unfold disj; clear_all; cset_tac; intuition eauto.
  - econstructor; [|eapply H0| | | | |]; eauto with cset.
    + eapply (IHrenamedApart1 D0); eauto with cset.
    + eapply (IHrenamedApart2 D0); eauto with cset.
    + rewrite getAnn_mapAnn. pe_rewrite; eauto.
    + rewrite getAnn_mapAnn. pe_rewrite; eauto.
  - econstructor; eauto with cset.
  - econstructor; eauto with cset.
  - econstructor; eauto with cset.
    + eapply IHrenamedApart. instantiate (1:=D0). eauto with cset.
      reflexivity.
    + rewrite getAnn_mapAnn. pe_rewrite.
      econstructor; eauto.
      revert H H4; unfold disj; clear_all; cset_tac; intuition; eauto.
  - econstructor.
    + rewrite map_length; eauto.
    + intros. inv_map H9. eapply H1; eauto.
      eapply disj_1_incl; eauto.
      rewrite <- get_list_union_map; eauto. cset_tac; intuition.
      reflexivity.
    + hnf; intros. inv_map H9. edestruct H2; eauto; dcr. instantiate (1:=Dt).
      hnf. rewrite getAnn_mapAnn.
      destruct (getAnn x); simpl in *.
      assert (disj (of_list (fst a)) D0).
      eapply disj_1_incl; eauto.
      rewrite <- get_list_union_map; eauto. cset_tac; intuition.
      split. rewrite H12.
      revert H13; unfold disj; clear_all; cset_tac; intuition; eauto.
      split; eauto. split; eauto.
      eapply disj_2_incl. eapply H16. eapply incl_minus.
    + eapply pairwise_disj_PIR2; eauto.
      eapply zip_ext_PIR2; eauto. rewrite map_length; eauto.
      intros. get_functional; subst. inv_map H11.
      unfold defVars. rewrite getAnn_mapAnn. destruct (getAnn y); reflexivity.
    + eapply IHrenamedApart. eapply disj_1_incl; eauto with cset.
      reflexivity.
    + rewrite getAnn_mapAnn. pe_rewrite. reflexivity.
    + rewrite list_union_eq; eauto.
      repeat rewrite zip_length2; eauto. rewrite map_length; eauto.
      intros. inv_zip H8. inv_zip H9. inv_map H11.
      get_functional; subst. unfold defVars.
      rewrite getAnn_mapAnn. destruct (getAnn x2); simpl. reflexivity.
Qed.

(** ** The two annotating sets are disjoint. *)

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
  - rewrite <- H6. eapply disj_app; split.
    + symmetry. rewrite <- list_union_disjunct.
      intros. inv_zip H7.
      exploit H1; eauto.
      unfold defVars.
      exploit H2; eauto; dcr.
      change (disj (of_list (fst x) ++ snd (getAnn x0)) D).
      symmetry. destruct H11; dcr.
      eapply disj_app; split. symmetry; eauto.
      rewrite H11 in H10; eauto.
      rewrite incl_right; eauto.
    + pe_rewrite; eauto.
Qed.



(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
