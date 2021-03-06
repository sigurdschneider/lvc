Require Import Util LengthEq Get Drop Map CSet MoreList DecSolve AllInRel.
Require Import Var Val Exp Envs IL OptionR.
Require Import Infra.PartialOrder Terminating Infra.Lattice Annotation AnnP.

Set Implicit Arguments.

Instance ann_P_morph A (P:A->Prop) (R:A->A->Prop) (H:forall x y, R x y -> P x -> P y)
  : Proper (ann_R R ==> impl) (ann_P (A:=A) P).
Proof.
  unfold Proper, respectful, impl.
  intros.
  general induction H0; invt ann_P; eauto using ann_P.
  econstructor; intros; inv_get; eauto using ann_P.
Qed.

Lemma option_map_mon T `{PartialOrder T}  U `{PartialOrder U} (a a':option T) (f f': T -> U)
  : a ⊑ a'
    -> (forall x y, x ⊑ y -> f x ⊑ f' y)
    -> option_map f a ⊑ option_map f' a'.
Proof.
  intros A; inv A; simpl;
    clear_trivial_eqs; simpl; eauto.
Qed.


Definition joinTopAnn A `{JoinSemiLattice A} (a:ann A) (b:A) :=
  setTopAnn a (join (getAnn a) b).


Lemma poLe_zip_setTopAnn X `{PartialOrder X} (A A':list (ann X)) (B B':list X)
  : poLe A A'
    -> poLe B B'
    -> poLe ((@setTopAnn _) ⊜ A B) (@setTopAnn _ ⊜ A' B').
Proof.
  intros LE_A LE_B; simpl in *.
  general induction LE_A; inv LE_B; simpl; eauto using PIR2.
  - econstructor; eauto.
    eapply ann_R_setTopAnn; eauto.
    eapply IHLE_A; eauto.
Qed.

Lemma ann_poLe_joinTopAnn A `{JoinSemiLattice A} (a:A) (b:A) an bn
  : poLe a b
    -> poLe an bn
    -> poLe (joinTopAnn an a) (joinTopAnn bn b).
Proof.
  intros.
  inv H2; simpl; econstructor; try eapply join_struct; eauto.
Qed.

Lemma ann_poEq_joinTopAnn A `{JoinSemiLattice A} (a:A) (b:A) an bn
  : poEq a b
    -> poEq an bn
    -> poEq (joinTopAnn an a) (joinTopAnn bn b).
Proof.
  intros.
  inv H2; simpl; econstructor; eauto;
    rewrite H1, H3; reflexivity.
Qed.

Hint Resolve ann_poEq_joinTopAnn ann_poLe_joinTopAnn poLe_zip_setTopAnn.


Lemma PIR2_zip_joinTopAnn X `{JoinSemiLattice X} (A A':list (ann X)) (B B':list X)
  : poLe A A'
    -> poLe B B'
    -> poLe ((@joinTopAnn _ _ _) ⊜ A B) (@joinTopAnn _ _ _ ⊜ A' B').
Proof.
  intros LE_A LE_B. simpl in *.
  hnf in LE_A.
  general induction LE_A; inv LE_B; simpl; eauto using PIR2.
Qed.

Lemma PIR2_poEq_zip_setTopAnn X `{PartialOrder X} (A A':list (ann X)) (B B':list X)
  : poEq A A'
    -> poEq B B'
    -> poEq ((@setTopAnn _) ⊜ A B) (@setTopAnn _ ⊜ A' B').
Proof.
  intros LE_A LE_B; simpl in *.
  general induction LE_A; inv LE_B; simpl; eauto using PIR2.
  - econstructor; eauto.
    eapply ann_R_setTopAnn; eauto.
    eapply IHLE_A; eauto.
Qed.

Lemma PIR2_poEq_zip_joinTopAnn X `{JoinSemiLattice X} (A A':list (ann X)) (B B':list X)
  : poEq A A'
    -> poEq B B'
    -> poEq ((@joinTopAnn _ _ _) ⊜ A B) (@joinTopAnn _ _ _ ⊜ A' B').
Proof.
  intros LE_A LE_B; simpl in *.
  general induction LE_A; inv LE_B; simpl; eauto using PIR2.
Qed.

Hint Resolve PIR2_zip_joinTopAnn PIR2_poEq_zip_setTopAnn PIR2_poEq_zip_joinTopAnn.


Instance LowerBounded_ann (s:stmt) A `{LowerBounded A}
  : LowerBounded ({ a : ann A | annotation s a }) :=
  {
    bottom := exist _ (setAnn bottom s) _
  }.
Proof.
  - eapply setAnn_annotation.
  - intros []. hnf. simpl.
    general induction a; simpl;
      econstructor; eauto using bottom_least with len.
    + intros; inv_get. exploit H1; eauto.
Defined.




Lemma PIR2_setTopAnn_zip_left X (R:X->X->Prop) `{Reflexive _ R} (A:list (ann X)) B
  : PIR2 R (Take.take ❬A❭ B) (getAnn ⊝ A)
    -> PIR2 (ann_R R) (@setTopAnn _ ⊜ A B) A.
Proof.
  intros P. general induction P; destruct A, B; isabsurd; eauto using PIR2.
  simpl in *. clear_trivial_eqs.
  econstructor; eauto.
  eapply ann_R_setTopAnn_left; eauto.
Qed.

Lemma PIR2_joinTopAnn_zip_left X `{JoinSemiLattice X} (A:list (ann X)) B
  : PIR2 poLe (Take.take ❬A❭ B) (getAnn ⊝ A)
    -> PIR2 poEq (@joinTopAnn _ _ _ ⊜ A B) A.
Proof.
  intros P. general induction P; destruct A,B; isabsurd; eauto using PIR2.
  simpl in *. clear_trivial_eqs.
  econstructor; eauto.
  eapply ann_R_setTopAnn_left; eauto.
  eapply poLe_antisymmetric. rewrite pf.
  rewrite join_idempotent. eauto.
  eapply join_poLe.
Qed.

Hint Resolve PIR2_joinTopAnn_zip_left.

Lemma getAnn_joinTopAnn A `{JoinSemiLattice A} an (a:A)
  : (getAnn (joinTopAnn an a)) = (join (getAnn an) a).
Proof.
  destruct an; simpl; reflexivity.
Qed.

Lemma getAnn_map_joinTopAnn A `{JoinSemiLattice A} an a
  : getAnn ⊝ (@joinTopAnn A _ _ ⊜ an a) = join ⊜ (getAnn ⊝ an) a.
Proof.
  general induction an; simpl; eauto.
  destruct a0; simpl; eauto.
  rewrite IHan. rewrite getAnn_joinTopAnn. reflexivity.
Qed.

Lemma getAnn_map_setTopAnn A an a
  : getAnn ⊝ (@setTopAnn A ⊜ an a) = Take.take ❬an❭ a.
Proof.
  general induction an; simpl; eauto.
  destruct a0; simpl; eauto.
  rewrite getAnn_setTopAnn. f_equal.
  erewrite IHan; eauto.
Qed.

Lemma setTopAnn_map_inv X A B
  : setTopAnn (A:=X) ⊜ A B = A
    -> Take.take ❬A❭ B = getAnn ⊝ A.
Proof.
  intros. general induction A; destruct B; simpl; eauto.
  - exfalso. inv H.
  - simpl in *. inv H.
    rewrite <- ann_R_eq in H1.
    eapply setTopAnn_inv in H1. subst.
    rewrite getAnn_setTopAnn. f_equal.
    rewrite zip_length. rewrite min_l; try omega.
    erewrite IHA; eauto; try omega.
    erewrite getAnn_map_setTopAnn; eauto.
    erewrite IHA; eauto.
    rewrite <- H2. len_simpl.
    decide (length A <= length B).
    rewrite min_l; eauto.
    rewrite min_r; eauto. omega.
Qed.

Lemma joinTopAnn_inv (A : Type) `{JoinSemiLattice A} (an : ann A) (a : A)
  : poEq (joinTopAnn an a) an -> poLe a (getAnn an).
Proof.
  intros.
  rewrite <- H1. rewrite getAnn_joinTopAnn.
  rewrite join_commutative. eapply join_poLe.
Qed.

Hint Resolve joinTopAnn_inv.

Lemma ann_R_joinTopAnn_inv (A : Type) `{JoinSemiLattice A} (an : ann A) (a : A)
  : ann_R poEq (joinTopAnn an a) an -> poLe a (getAnn an).
Proof.
  intros.
  eapply joinTopAnn_inv. eapply H1.
Qed.

Lemma joinTopAnn_map_inv X `{JoinSemiLattice X} A B
  : PIR2 poEq (joinTopAnn (A:=X) ⊜ A B) A
    -> PIR2 poLe (Take.take ❬A❭ B) (getAnn ⊝ A).
Proof.
  intros. general induction A; destruct B; simpl; eauto.
  - exfalso. inv H1.
  - simpl in *. inv H1.
    eapply joinTopAnn_inv in pf.
    econstructor; eauto.
Qed.


Lemma ann_R_setTopAnn_poEq (A : Type) `{PartialOrder A} (a : A) (b : A)
         (an : ann A) (bn : ann A)
  : poEq a b -> poEq an bn -> poEq (setTopAnn an a) (setTopAnn bn b).
Proof.
  intros. eapply ann_R_setTopAnn; eauto.
Qed.

Lemma ann0_poEq A `{PartialOrder A} a b
  : poEq a b
    -> poEq (ann0 a) (ann0 b).
Proof.
  intros. econstructor; eauto.
Qed.

Lemma ann1_poEq A `{PartialOrder A} a b an1 bn1
  : poEq a b
    -> poEq an1 bn1
    -> poEq (ann1 a an1) (ann1 b bn1).
Proof.
  intros. econstructor; eauto.
Qed.

Lemma ann2_poEq A `{PartialOrder A} a b an1 bn1 an2 bn2
  : poEq a b
    -> poEq an1 bn1
    -> poEq an2 bn2
    -> poEq (ann2 a an1 an2) (ann2 b bn1 bn2).
Proof.
  intros. econstructor; eauto.
Qed.

Lemma annF_poEq A `{PartialOrder A} a b an1 bn1 an2 bn2
  : poEq a b
    -> poEq an1 bn1
    -> poEq an2 bn2
    -> poEq (annF a an1 an2) (annF b bn1 bn2).
Proof.
  intros. econstructor; eauto.
  - eapply PIR2_length in H1; eauto.
  - eapply get_PIR2; eauto.
Qed.

Hint Resolve ann0_poEq ann1_poEq ann2_poEq annF_poEq ann_R_setTopAnn_poEq.


Lemma ann_R_setTopAnn_poLe (A : Type) `{PartialOrder A} (a : A) (b : A)
         (an : ann A) (bn : ann A)
  : poLe a b -> poLe an bn -> poLe (setTopAnn an a) (setTopAnn bn b).
Proof.
  intros. eapply ann_R_setTopAnn; eauto.
Qed.

Lemma ann0_poLe A `{PartialOrder A} a b
  : poLe a b
    -> poLe (ann0 a) (ann0 b).
Proof.
  intros. econstructor; eauto.
Qed.

Lemma ann1_poLe A `{PartialOrder A} a b an1 bn1
  : poLe a b
    -> poLe an1 bn1
    -> poLe (ann1 a an1) (ann1 b bn1).
Proof.
  intros. econstructor; eauto.
Qed.

Lemma ann2_poLe A `{PartialOrder A} a b an1 bn1 an2 bn2
  : poLe a b
    -> poLe an1 bn1
    -> poLe an2 bn2
    -> poLe (ann2 a an1 an2) (ann2 b bn1 bn2).
Proof.
  intros. econstructor; eauto.
Qed.

Lemma annF_poLe A `{PartialOrder A} a b an1 bn1 an2 bn2
  : poLe a b
    -> poLe an1 bn1
    -> poLe an2 bn2
    -> poLe (annF a an1 an2) (annF b bn1 bn2).
Proof.
  intros. econstructor; eauto.
  - eapply PIR2_length in H1; eauto.
  - eapply get_PIR2; eauto.
Qed.

Hint Resolve ann0_poLe ann1_poLe ann2_poLe annF_poLe ann_R_setTopAnn_poLe.


Lemma PIR2_poEq_zip (X Y Z : Type) `{PartialOrder X} `{PartialOrder Y}  `{PartialOrder Z}
      (f : X -> Y -> Z) (l1 : 〔X〕) (l2 : 〔Y〕)
      (l1' : 〔X〕) (l2' : 〔Y〕)
      `{Proper _ (poEq ==> poEq ==> poEq) f}
  : poEq l1 l1' -> poEq l2 l2' -> poEq (f ⊜ l1 l2) (f ⊜ l1' l2').
Proof.
  intros P1 P2. hnf in P1.
  general induction P1; inv P2; simpl; econstructor; eauto.
  - eapply H2; eauto.
  - eapply IHP1; eauto.
Qed.

Lemma poEq_drop A `{PartialOrder A} a b n
  : poEq a b
    -> drop n a ≣ drop n b.
Proof.
  intros. eapply PIR2_drop. eauto.
Qed.

Lemma poLe_drop A `{PartialOrder A} a b n
  : poLe a b
    -> drop n a ⊑ drop n b.
Proof.
  intros. eapply PIR2_drop. eauto.
Qed.

Hint Resolve PIR2_poEq_zip poEq_drop poLe_drop.

Lemma setTopAnn_eta_poEq A `{PartialOrder A} (an:ann A) a
  : getAnn an ≣ a
    -> setTopAnn an a ≣ an.
Proof.
  intros; destruct an; simpl in *; subst; eauto.
Qed.


Instance terminating_ann Dom `{PO:PartialOrder Dom}
  : Terminating Dom poLt
    -> Terminating (ann Dom) poLt.
Proof.
  intros Trm a.
  econstructor. intros ? [A _].
  induction A.
  - specialize (Trm b).
    general induction Trm.
    econstructor. intros ? [A B].
    inv A.
    eapply H0; eauto. split; eauto.
  - pose proof (Trm b) as FST. clear A H.
    rename IHA into SND.
    assert (poLe bn bn) by reflexivity.
    revert H. generalize bn at 2 3.
    induction FST as [? ? FST].
    assert (poLe x x) by reflexivity.
    revert H0. generalize x at 2 3.
    induction SND as [? ? SND].
    intros.
    econstructor; intros ? [A B].
    inv A.
    decide (poEq bn bn0).
    + decide (poEq x1 b); eauto.
      exfalso; eapply B; eauto.
    + eapply (SND bn0); eauto.
  - clear H A1 A2 ans ant a.
    assert (poLe bns bns) by reflexivity.
    revert H. generalize bns at 2 3.
    assert (poLe bnt bnt) by reflexivity.
    revert H. generalize bnt at 2 3.
    assert (poLe b b) by reflexivity.
    revert H. generalize b at 2 3.
    specialize (Trm b).
    induction Trm.
    induction IHA1.
    induction IHA2.
    intros.
    econstructor; intros ? [A B].
    inv A.
    decide (poEq b b0).
    + decide (poEq bns bns0).
      * decide (poEq bnt bnt0).
        exfalso; apply B; eauto.
        eapply (H4 bnt0); eauto.
      * eapply (H2 bns0); eauto.
    + eapply (H0 b0); eauto.
  - clear H A.
    pose proof (Trm b) as FST.
    rename IHA into SND.
    assert (TRD:terminates poLt bns). {
      eapply terminates_list_get.
      intros. symmetry in H0; edestruct get_length_eq; eauto.
    }
    clear H0 H1 H2.
    assert (poLe bns bns) by reflexivity.
    revert H. generalize bns at 2 3.
    assert (poLe bnt bnt) by reflexivity.
    revert H. generalize bnt at 2 3.
    assert (poLe b b) by reflexivity.
    revert H. generalize b at 2 3.
    induction FST.
    induction SND.
    induction TRD.
    intros.
    econstructor; intros ? [A B].
    inv A.
    decide (poEq b b0).
    + decide (poEq bns bns0).
      * decide (poEq bnt bnt0).
        -- exfalso; apply B; eauto.
        -- eapply (H2 bnt0); eauto.
      * eapply PIR2_get in H14; eauto.
        eapply (H4 bns0); eauto.
    + eapply PIR2_get in H14; eauto.
      eapply (H0 b0); eauto.
Qed.
