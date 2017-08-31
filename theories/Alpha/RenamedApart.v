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

Instance funConstr_morphism_impl
: Proper (Equal ==> (flip Subset) ==> eq ==> (ann_R (@pe _ _)) ==> impl) funConstr.
Proof.
  unfold Proper, respectful, impl; intros; subst.
  destruct H3; dcr; hnf. rewrite <- H.
  rewrite <- H1. eapply ann_R_get in H2. rewrite <- H2.
  split; eauto. split; eauto. split; eauto.
  rewrite<- H0. eauto.
Qed.

Instance funConstr_morphism_iff
: Proper (Equal ==> Equal ==> eq ==> (ann_R (@pe _ _)) ==> iff) funConstr.
Proof.
  unfold Proper, respectful, flip; split; subst; intros;
    eapply funConstr_morphism_impl; eauto; unfold flip; try symmetry; eauto;
      rewrite H0; eauto.
Qed.

Instance funConstr_morphism_iff_pointwise
  : Proper (Equal ==> Equal ==> (pointwise_relation _ (pointwise_relation _ iff)))
           funConstr.
Proof.
  unfold Proper, respectful, flip; split; subst; intros;
    eapply funConstr_morphism_impl; eauto; unfold flip; try symmetry; eauto;
      rewrite H0; eauto.
Qed.

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
  general induction H0; simpl; invtc (ann_R (@pe var _));
  invtc (@pe var _); eauto using renamedApart.
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
      rewrite H10. reflexivity.
    }
    econstructor; eauto with len.
    + intros; inv_get; eauto.
    + instantiate (1:=Dt).
      hnf; intros. inv_get.
      exploit H14; eauto. rewrite <- H9, <- H16.
      eapply H2; eauto.
    + eapply pairwise_disj_PIR2; eauto. symmetry; eauto.
    + rewrite <- H9, <- H15; eauto.
    + rewrite <- H13, H7. eauto.
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
  intros. general induction H; simpl; eauto; pe_rewrite; set_simpl.
  - rewrite IHrenamedApart, H0.
    clear_all; cset_tac.
  - rewrite H, IHrenamedApart1, IHrenamedApart2. cset_tac.
  - rewrite IHrenamedApart.
    rewrite (@list_union_incl _ _ _ _ D); eauto with cset.
    intros ? ? GET. inv_get.
    rewrite H1; eauto.
    edestruct H2; eauto; dcr; eauto with cset.
Qed.

Instance indexwise_R_morphism_impl A B
: Proper ((pointwise_relation _ (pointwise_relation _ impl)) ==> eq ==> eq ==> impl) (@indexwise_R A B).
Proof.
  unfold Proper, respectful, pointwise_relation, impl, indexwise_R.
  intros; subst. eapply H. eapply H2; eauto.
Qed.

Instance indexwise_R_morphism_iff A B
: Proper ((pointwise_relation _ (pointwise_relation _ iff)) ==> eq ==> eq ==> iff) (@indexwise_R A B).
Proof.
  unfold Proper, respectful, pointwise_relation.
  split; subst; intros; eapply indexwise_R_morphism_impl; eauto;
  unfold pointwise_relation, impl; intros; firstorder.
Qed.


Lemma renamedApart_occurVars s an
  : renamedApart s an -> definedVars s [=] snd (getAnn an).
Proof.
  intros.
  general induction H; simpl; eauto;
  pe_rewrite; srewrite D'; eauto with cset.
  - set_simpl.
    eapply eq_union_lr; eauto.
    eapply list_union_eq; eauto with len.
    intros; inv_get. unfold defVarsZs.
    rewrite H1; eauto. unfold defVars. reflexivity.
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
  - intros; inv_get; eauto.
Qed.

Lemma renamedApart_minus D an an' s
  : disj (occurVars s) D
    -> renamedApart s an
    -> ann_R (@pe _ _) an' (mapAnn (pminus D) an)
    -> renamedApart s an'.
Proof.
  intros DISJ RN PE. revert an' PE.
  induction RN; indros; try rewrite PE; simpl in * |- *; set_simpl.
  - econstructor; eauto 20 with cset pe ann.
  - econstructor; eauto with cset pe ann.
  - econstructor; eauto with cset.
  - econstructor; eauto with cset.
  - econstructor; eauto with cset len.
    + intros ? ? ? GET1 GET2. inv_get. eapply H1; eauto.
      eapply disj_1_incl; eauto.
      rewrite <- get_list_union_map; eauto. cset_tac.
    + hnf; intros ? ? ? GET1 GET2; inv_get.
      edestruct H2; dcr; eauto.
      instantiate (1:=Dt).
      hnf. rewrite getAnn_mapAnn.
      destruct (getAnn x); simpl in *.
      assert (disj (of_list (fst a)) D).
      eapply disj_1_incl; eauto.
      rewrite <- get_list_union_map; eauto. cset_tac; intuition.
      split.
      * set_simpl.
        revert H6; unfold disj; clear_all; cset_tac; intuition; eauto.
      * eauto with cset.
    + eapply pairwise_disj_PIR2; eauto.
      eapply zip_ext_PIR2; eauto. rewrite map_length; eauto.
      intros ? ? ? ? ? GET1 GET2 GET3 GET4. inv_get.
      unfold defVars. rewrite getAnn_mapAnn. destruct (getAnn y); reflexivity.
    + eauto with cset pe ann.
    + rewrite list_union_eq.
      * reflexivity.
      * eauto with len.
      * intros ? ? ? GET1 GET2; inv_get.
        unfold defVars. rewrite getAnn_mapAnn.
        destruct (getAnn x0); simpl. reflexivity.
      * eauto.
Qed.


(** ** The two annotating sets are disjoint. *)

Lemma renamedApart_disj s G
: renamedApart s G
  -> disj (fst (getAnn G)) (snd (getAnn G)).
Proof.
  intros. general induction H; simpl; pe_rewrite; set_simpl.
  - eauto with cset.
  - eauto with cset.
  - eauto with cset.
  - eauto with cset.
  - eapply disj_app; split; eauto.
    + symmetry. rewrite <- list_union_disjunct.
      intros ? ? GET; inv_get.
      exploit H1; eauto.
      unfold defVars.
      edestruct H2; eauto; dcr.
      symmetry.
      eapply disj_app; split.
      symmetry; eauto.
      rewrite H8 in H7.
      eauto with cset.
Qed.

Lemma defVars_take_disj F ans n Zs a
:  pairwise_ne disj (zip defVars F ans)
   -> get F n Zs
   -> get ans n a
   -> disj (defVars Zs a) (list_union zip defVars (take n F) (take n ans)).
Proof.
  intros.
  symmetry. rewrite <- list_union_disjunct; intros; inv_get.
  eapply (H n0 n); eauto using zip_get. omega.
Qed.

Lemma defVars_drop_disj F ans n Zs a
:  pairwise_ne disj (zip defVars F ans)
   -> get F n Zs
   -> get ans n a
   -> disj (defVars Zs a) (list_union zip defVars (drop (S n) F) (drop (S n) ans)).
Proof.
  intros.
  symmetry. rewrite <- list_union_disjunct; intros; inv_get.
  eapply (H (S n + n0) n); eauto using zip_get. omega.
Qed.

Lemma defVars_disj_D F ans D Dt
      (Ddisj: disj D (list_union zip defVars F ans ∪ Dt))
: forall n  DD' Zs, get F n Zs -> get ans n DD' ->
               disj D (defVars Zs DD').
Proof.
  intros.
  eapply disj_2_incl; eauto.
  eapply incl_union_left. eapply incl_list_union; eauto using zip_get.
Qed.


Lemma disj_D_defVars F t ans D D' ant
  : renamedApart (stmtFun F t) (annF (D, D') ans ant)
    -> disj D (list_union zip defVars F ans).
Proof.
  intros.
  exploit renamedApart_disj; eauto; simpl in *.
  eapply disj_2_incl; eauto.
  invt renamedApart.
  rewrite <- H13; eauto with cset.
Qed.

Lemma disj_D_defVars_take F t ans n D D' ant
  : renamedApart (stmtFun F t) (annF (D, D') ans ant)
    -> disj D (list_union zip defVars (take n F) (take n ans)).
Proof.
  intros.
  rewrite <- take_zip, list_union_take_incl.
  eapply disj_D_defVars; eauto.
Qed.

Lemma disj_D_defVars_drop F t ans n D D' ant
  : renamedApart (stmtFun F t) (annF (D, D') ans ant)
    -> disj D (list_union zip defVars (drop n F) (drop n ans)).
Proof.
  intros.
  rewrite <- drop_zip, list_union_drop_incl.
  eapply disj_D_defVars; eauto.
Qed.

Hint Extern 5 =>
      match goal with
      | [ H : renamedApart ?s ?an, H' : pe (getAnn ?an) (?D, ?D') |- disj ?D' ?D ]
        => let H'' := fresh "tmp" in
          pose proof (renamedApart_disj H) as H''; rewrite H' in H''; simpl in H'';
            symmetry; eapply H''
      | [ H : renamedApart ?s ?an, H' : pe (getAnn ?an) (?D, ?D') |- disj ?D ?D' ]
        => let H'' := fresh "tmp" in
          pose proof (renamedApart_disj H) as H''; rewrite H' in H''; simpl in H'';
            eapply H''
      end : cset.


Lemma lv_incl_fst_ra D Dt F ans n a Zs als alv lv
  : Indexwise.indexwise_R (funConstr D Dt) F ans
    -> ( forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          of_list (fst Zs) ⊆ getAnn a /\ getAnn a \ of_list (fst Zs) ⊆ lv)
    -> get ans n a
    -> get F n Zs
    -> get als n alv
    -> lv ⊆ D
    -> getAnn alv ⊆ fst (getAnn a).
Proof.
  intros IDW ZlvIncl Get1 Get2 Get3 incl. edestruct IDW; eauto; dcr.
  rewrite H.
  exploit ZlvIncl; eauto; dcr. rewrite <- incl, <- H5.
  clear; cset_tac; intuition.
Qed.

Lemma disj_lv_take lv n F ans als (Zs:params*stmt) alv t D D' ant a
  : PairwiseDisjoint.pairwise_ne disj (defVars ⊜ F ans)
    -> get als n alv
    -> get F n Zs
    -> get ans n a
    -> (forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          of_list (fst Zs) ⊆ getAnn a /\ getAnn a \ of_list (fst Zs) ⊆ lv)
    -> lv ⊆ D
    -> renamedApart (stmtFun F t) (annF (D, D') ans ant)
    -> disj (getAnn alv) (list_union (defVars ⊜ (take n F) (take n ans))).
Proof.
  intros. exploit H3; eauto; dcr.
  assert (EQ:getAnn alv \ of_list (fst Zs) ∪ of_list (fst Zs)
                    [=] getAnn alv) by cset_tac.
  rewrite <- EQ. symmetry. rewrite disj_app. split; symmetry.
  - eapply disj_1_incl.
    eapply disj_D_defVars_take; eauto using renamedApart.
    eauto with cset.
  - eapply disj_1_incl.
    eapply defVars_take_disj; eauto. unfold defVars.
    eauto with cset.
Qed.

Lemma disj_fst_snd_ra F t D D' ans ant n Zs a
  : renamedApart (stmtFun F t) (annF (D, D') ans ant)
    -> get F n Zs
    -> get ans n a
    -> disj (fst (getAnn a) ∪ snd (getAnn a))
           (list_union (defVars ⊜ (drop (S n) F) (drop (S n) ans))).
Proof.
  intros RA Get1 Get2. invt renamedApart.
  edestruct H7; eauto; dcr. rewrite H.
  rewrite union_comm. rewrite <- union_assoc.
  symmetry; rewrite disj_app; split; symmetry.
  - eapply disj_1_incl. eapply defVars_drop_disj; eauto.
    unfold defVars. clear; cset_tac.
  - eapply disj_D_defVars_drop; eauto.
Qed.

Lemma disj_fst_snd_Dt D Dt F ans t ant a n Zs
  : Indexwise.indexwise_R (funConstr D Dt) F ans
    -> renamedApart t ant
    -> pe (getAnn ant) (D, Dt)
    -> get F n Zs
    -> get ans n a
    -> disj (fst (getAnn a) ∪ snd (getAnn a)) Dt.
Proof.
  intros IDW RA PE Get1 Get2.
  edestruct IDW; eauto; dcr. rewrite H.
  rewrite union_comm. rewrite <- union_assoc.
  symmetry; rewrite disj_app; split;
    symmetry.
  - rewrite union_comm; eauto.
  - eauto with cset.
Qed.

Lemma renamedApart_annotation s ang
: renamedApart s ang
  -> annotation s ang.
Proof.
  intros. general induction H; eauto 20 using @annotation.
Qed.


Lemma ra_incl1 X `{OrderedType X} (D Ds VD:set X) x
  : D ∪ {x; Ds} [<=] VD
    -> {x; D} ∪ Ds [<=] VD.
Proof.
  cset_tac.
Qed.

Lemma ra_incl2 X `{OrderedType X} (D Ds Dt VD:set X)
  : D ∪ (Ds ∪ Dt) [<=] VD
    -> D ∪ Ds [<=] VD.
  cset_tac.
Qed.

Lemma ra_incl3 X `{OrderedType X} (D Ds Dt VD:set X)
  : D ∪ (Ds ∪ Dt) [<=] VD
    -> D ∪ Dt [<=] VD.
  cset_tac.
Qed.

Hint Resolve ra_incl1 ra_incl2 ra_incl3 | 60 : cset.

Lemma ra_incl4 X `{OrderedType X} (D Ds VD:set X) x
  :  {x; D} ∪ Ds [<=] D ∪ {x; Ds}.
Proof.
  cset_tac.
Qed.

Lemma ra_incl5 X `{OrderedType X} (D Ds VD:set X) x
  :  {x; D} ∪ Ds [<=] D ∪ {x; Ds}.
Proof.
  cset_tac.
Qed.

Lemma ra_incl6 X `{OrderedType X} (D Ds Dt VD:set X)
  : D ∪ Ds [<=] D ∪ (Ds ∪ Dt).
  cset_tac.
Qed.

Lemma ra_incl7 X `{OrderedType X} (D Ds Dt VD:set X)
  : D ∪ Dt [<=] D ∪ (Ds ∪ Dt).
  cset_tac.
Qed.

Hint Resolve ra_incl4 ra_incl5 ra_incl6 ra_incl7 : cset.

Lemma ans_incl_D_union D Dt F ans a n
      (IFC:Indexwise.indexwise_R (funConstr D Dt) F ans)
      (GetAns:get ans n a)
      (Len:❬F❭ = ❬ans❭)
  : fst (getAnn a) ∪ snd (getAnn a) [<=] D ∪ (list_union (defVars ⊜ F ans) ∪ Dt).
Proof.
  inv_get. edestruct IFC; eauto; dcr.
  rewrite H0. rewrite <- incl_list_union; eauto using zip_get;[|reflexivity].
  unfold defVars. clear; cset_tac.
Qed.

Hint Resolve ans_incl_D_union | 0 : cset .


Lemma list_union_defVars_decomp F ans (Len:❬F❭ = ❬ans❭)
  : list_union (defVars ⊜ F ans) [=]
               list_union (of_list ⊝ fst ⊝ F) ∪ list_union (snd ⊝ getAnn ⊝ ans).
Proof.
  general induction Len; simpl; eauto.
  - cset_tac.
  - norm_lunion. rewrite IHLen.
    unfold defVars at 1.
    clear_all; cset_tac.
Qed.

Lemma funConstr_disj_Dt D Dt F ans (Len:❬F❭=❬ans❭)
  : Indexwise.indexwise_R (funConstr D Dt) F ans
    -> disj (list_union (of_list ⊝ fst ⊝ F)) Dt.
Proof.
  hnf; intros IW.
  hnf; intros x IN1 IN2.
  eapply list_union_get in IN1.
  destruct IN1; dcr; inv_get; [|cset_tac].
  edestruct IW; eauto; dcr.
  cset_tac.
Qed.

Lemma funConstr_disj_ZL_getAnn ZL (D Dt : ⦃var⦄)  (F : 〔params * stmt〕)
      (ans : 〔ann (⦃var⦄ * ⦃var⦄)〕)
  : Indexwise.indexwise_R (funConstr D Dt) F ans
    -> PairwiseDisjoint.pairwise_ne disj (defVars ⊜ F ans)
    -> disj (list_union (of_list ⊝ ZL)) (list_union (defVars ⊜ F ans) ∪ Dt)
    -> (forall (n : nat) (Zs : params * stmt) (a : ann (⦃var⦄ * ⦃var⦄)),
          get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
    -> ❬F❭ = ❬ans❭
    -> disj (list_union (of_list ⊝ (fst ⊝ F ++ ZL))) (list_union (snd ⊝ getAnn ⊝ ans)).
Proof.
  intros. rewrite List.map_app, list_union_app.
  rewrite list_union_defVars_decomp in *; eauto.
  eapply disj_union_left; symmetry.
  - hnf; intros.
    eapply list_union_get in H4. destruct H4; dcr; [|cset_tac].
    eapply list_union_get in H5. destruct H5; dcr; [|cset_tac].
    decide (x0=x2).
    + subst. inv_get. edestruct H; eauto; dcr.
      exploit H2; eauto. eapply renamedApart_disj in H9.
      rewrite H8 in *. eapply H9; eauto. cset_tac.
    + inv_get. exploit H0; eauto using zip_get.
      eapply (H10 x); unfold defVars. cset_tac. cset_tac.
  - eapply disj_2_incl; eauto. cset_tac.
Qed.

Lemma funConstr_disj_Dt' ZL (D Dt : ⦃var⦄)  (F : 〔params * stmt〕)
      (ans : 〔ann (⦃var⦄ * ⦃var⦄)〕)
  : Indexwise.indexwise_R (funConstr D Dt) F ans
    -> disj (list_union (of_list ⊝ ZL)) (list_union (defVars ⊜ F ans) ∪ Dt)
    -> ❬F❭ = ❬ans❭
    -> disj Dt (list_union (of_list ⊝ (fst ⊝ F ++ ZL))).
Proof.
  intros. rewrite List.map_app, list_union_app.
  eapply disj_union_right; symmetry.
  - eauto using funConstr_disj_Dt.
  - eapply disj_2_incl; eauto.
Qed.

Lemma disj_Dt_getAnn (D Dt : ⦃var⦄) (F : 〔params * stmt〕) (ans : 〔ann (⦃var⦄ * ⦃var⦄)〕)
  : Indexwise.indexwise_R (funConstr D Dt) F ans
    -> ❬F❭ = ❬ans❭
    -> disj Dt (list_union (snd ⊝ getAnn ⊝ ans)).
Proof.
  intros. hnf; intros.
  eapply list_union_get in H2.
  destruct H2. dcr; inv_get.
  - edestruct H; eauto; dcr.
    eapply H10; eauto. cset_tac.
  - cset_tac.
Qed.

Lemma renamedApart_incl
      (s : stmt)
      (ra : ann (⦃var⦄ * ⦃var⦄))
  :
    renamedApart s ra
    -> match ra with
      | ann1 (D, D') an
        => fst (getAnn an) ∪ snd (getAnn an) ⊆ D ∪ D'
      | ann2 (D, D') ans ant
        => fst (getAnn ans) ∪ snd (getAnn ans) ⊆ D ∪ D'
          /\ fst (getAnn ant) ∪ snd (getAnn ant) ⊆ D ∪ D'
      | annF (D, D') anF ant
        => (forall (ans : ann (⦃var⦄ * ⦃var⦄)) n,
              get anF n ans
              -> fst (getAnn ans) ∪ snd (getAnn ans) ⊆ D ∪ D')
          /\ fst (getAnn ant) ∪ snd (getAnn ant) ⊆ D ∪ D'
      | _ => True
      end
.
Proof.
  intros.
  invc H; simpl; eauto; set_simpl; pe_rewrite; repeat split;
    intros; inv_get; eauto with cset.
Qed.


Lemma get_ofl_VD ZL F VD
      (Z_VD : forall (Z : params) (n : nat), get ZL n Z -> of_list Z ⊆ VD)
      D D' Dt ans
      (LEN : ❬F❭ = ❬ans❭)
      (EQ : list_union (defVars ⊜ F ans) ∪ Dt [=] D')
      (ra_VD : D ∪ D' ⊆ VD)
  : forall (Z : params) (n : nat), get (fst ⊝ F ++ ZL) n Z -> of_list Z ⊆ VD.
Proof.
  intros.
  eapply get_app_cases in H as [?|[? ?]]; inv_get; eauto.
  rewrite <- ra_VD. rewrite <- EQ.
  rewrite <- incl_list_union; eauto using zip_get; try reflexivity.
  unfold defVars. cset_tac.
Qed.
