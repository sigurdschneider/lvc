Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation SetOperations MoreList.
Require Import Liveness Restrict RenamedApart LabelsDefined.

Set Implicit Arguments.



Lemma renamedApart_live_functional s ang DL
: renamedApart s ang
  -> paramsMatch s (List.map (snd ∘ @length _) DL)
  -> live_sound Functional DL s (mapAnn fst ang).
Proof.
  intros. general induction H; invt paramsMatch; simpl.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
    rewrite getAnn_mapAnn, H2. simpl; cset_tac; intuition.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
    rewrite getAnn_mapAnn, H4. simpl; cset_tac; intuition.
    rewrite getAnn_mapAnn, H5. simpl; cset_tac; intuition.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
  - inv_map H4. destruct x; unfold comp in H5; simpl in *.
    econstructor; simpl; eauto.
    + intros. eapply live_exp_sound_incl, live_freeVars.
      rewrite <- H. eapply get_list_union_map; eauto.
  - econstructor; eauto.
    intros. eapply live_exp_sound_incl, live_freeVars.
    rewrite <- H0. eapply get_list_union_map; eauto.
    rewrite getAnn_mapAnn, H2. simpl; cset_tac; intuition.
  - econstructor; eauto.
    + rewrite getAnn_mapAnn, H3; simpl. cset_tac; intuition.
    + destruct if; eauto. rewrite getAnn_mapAnn, H3; simpl. cset_tac; intuition.
    + rewrite getAnn_mapAnn, H5; simpl. reflexivity.
Qed.

Lemma renamedApart_live s ang DL i
: renamedApart s ang
  -> paramsMatch s (List.map (snd ∘ @length _) DL)
  -> bounded (List.map (fun x => Some (fst x \ of_list (snd x))) DL) (fst (getAnn ang))
  -> live_sound i DL s (mapAnn fst ang).
Proof.
  intros. general induction H; invt paramsMatch; simpl.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
    eapply IHrenamedApart; eauto.
    rewrite H2; simpl. rewrite <- incl_add'; eauto.
    rewrite getAnn_mapAnn, H2. simpl; cset_tac; intuition.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
    + eapply IHrenamedApart1; eauto.
      rewrite H4; simpl; eauto.
    + eapply IHrenamedApart2; eauto.
      rewrite H5; simpl; eauto.
    + rewrite getAnn_mapAnn, H4. simpl; cset_tac; intuition.
    + rewrite getAnn_mapAnn, H5. simpl; cset_tac; intuition.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
  - inv_map H5. destruct x; unfold comp in *; simpl in *.
    econstructor; simpl; eauto.
    + destruct if; eauto.
      eapply map_get_1 with (f:=fun x : set var * params => ⎣fst x \ of_list (snd x) ⎦) in H3.
      eapply bounded_get; eauto.
    + intros. eapply live_exp_sound_incl, live_freeVars.
      rewrite <- H. eapply get_list_union_map; eauto.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
    eapply IHrenamedApart; eauto.
    rewrite H2; simpl. rewrite <- incl_add'; eauto.
    intros. eapply live_exp_sound_incl, live_freeVars.
    rewrite <- H0. eapply get_list_union_map; eauto.
    rewrite getAnn_mapAnn, H2. simpl; cset_tac; intuition.
  - econstructor; eauto.
    + eapply IHrenamedApart1; eauto; simpl.
      rewrite getAnn_mapAnn, H3; simpl in *.
      split. cset_tac; intuition. rewrite <- incl_right; eauto.
    + eapply IHrenamedApart2; eauto; simpl.
      rewrite getAnn_mapAnn, H3, H5; simpl in *.
      split. cset_tac; intuition. eauto.
    + rewrite getAnn_mapAnn, H3; simpl. cset_tac; intuition.
    + destruct if; eauto. rewrite getAnn_mapAnn, H3; simpl. cset_tac; intuition.
    + rewrite getAnn_mapAnn, H5; simpl. reflexivity.
Qed.


(*Fixpoint list_disjoint (DL:list (set var)) (G:set var) :=
  match DL with
    | nil => True
    | G'::DL => disj G' G /\ list_disjoint DL G
  end.*)

Definition disjoint (DL:list (option (set var))) (G:set var) :=
  forall n s, get DL n (Some s) -> disj s G.

Instance disjoint_morphism_subset
  : Proper (eq ==> Subset ==> flip impl) disjoint.
Proof.
  unfold Proper, respectful, impl, flip, disj, disjoint; intros; subst.
  rewrite H0; eauto.
Qed.

Instance disjoint_morphism
  : Proper (eq ==> Equal ==> iff) disjoint.
Proof.
  unfold Proper, respectful, iff, disjoint; split; intros; subst.
  - rewrite <- H0; eauto.
  - rewrite H0; eauto.
Qed.

Definition disj1 (x:set var) (y: set var * set var) := disj x (snd y).

Lemma disjoint_let D D' D'' x (DL:list (set var * list var)) an
: D''[=]{x; D'}
  -> disjoint (live_globals DL) (D'')
  -> pe (getAnn an) ({x; D}, D')
  -> disjoint (live_globals DL) (snd (getAnn an)).
Proof.
  intros. rewrite H1. rewrite H in *. simpl. rewrite incl_add'; eauto.
Qed.

Lemma disjoint_if1 D D' Ds Dt (DL:list (set var * list var)) an
:  Ds ++ Dt[=]D'
  -> disjoint (live_globals DL) D'
  -> pe (getAnn an) (D, Ds)
  -> disjoint (live_globals DL) (snd (getAnn an)).
Proof.
  intros. rewrite H1. rewrite <- H in *. simpl. rewrite incl_left; eauto.
Qed.

Lemma disjoint_if2 D D' Ds Dt (DL:list (set var * list var)) an
:  Ds ++ Dt[=]D'
  -> disjoint (live_globals DL) D'
  -> pe (getAnn an) (D, Dt)
  -> disjoint (live_globals DL) (snd (getAnn an)).
Proof.
  intros. rewrite H1. rewrite <- H in *. simpl. rewrite incl_right; eauto.
Qed.


Definition Subset1 (x : set var) (y : set var * set var) :=
  match y with
    | (y, _) => x[<=] y
  end.

Instance Subset1_morph
: Proper (Equal ==> @pe _ _ ==> iff) Subset1.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl. rewrite H, H1. reflexivity.
Qed.

Lemma disjoint_fun1 D D' Ds Dt (DL:list (set var * list var)) ans als Z s
:   (Ds ++ Dt) ++ of_list Z[=]D'
    -> disjoint (live_globals DL) D'
    -> pe (getAnn ans) ((of_list Z ++ D)%set, Ds)
    -> ann_R Subset1 als ans
    -> renamedApart s ans
    -> disjoint (live_globals ((getAnn als, Z) :: DL)) (snd (getAnn ans)).
Proof.
  intros. rewrite H1. rewrite <- H in *. simpl in *.
  hnf; intros. inv H4.
  * eapply ann_R_get in H2.
    rewrite H1 in H2. simpl in H2.
    rewrite H2; simpl.
    eapply renamedApart_disj in H3. rewrite H1 in H3. simpl in *.
    rewrite minus_incl; eauto.
  * exploit H0; eauto using map_get_1.
    eapply disj_2_incl; eauto. cset_tac; intuition.
Qed.


Lemma disjoint_fun2 D D' Ds Dt (DL:list (set var * list var)) ant als Z s ans
:   (Ds ++ Dt) ++ of_list Z[=]D'
    -> disjoint (live_globals DL) D'
    -> pe (getAnn ant) (D, Dt)
    -> ann_R Subset1 als ans
    -> renamedApart s ant
    -> pe (getAnn ans) ((of_list Z ++ D)%set, Ds)
    -> (Ds ++ of_list Z) ∩ Dt[=]{}
    -> disjoint (live_globals ((getAnn als, Z) :: DL)) (snd (getAnn ant)).
Proof.
  intros. rewrite H1. rewrite <- H in *. simpl in *.
  hnf; intros. inv H6.
  - eapply ann_R_get in H2. rewrite H4 in H2. simpl in H2.
    rewrite H2; simpl.
    eapply renamedApart_disj in H3. rewrite H1 in H3. simpl in *.
    symmetry. rewrite minus_incl. eapply disj_app. split.
    + symmetry. rewrite incl_right; eauto.
    + symmetry; eauto.
  - exploit H0; eauto using map_get_1.
    eapply disj_2_incl; eauto. cset_tac; intuition.
Qed.

Lemma renamedApart_globals_live s AL alv f ang
: live_sound Imperative AL s alv
  -> renamedApart s ang
  -> isCalled s f
  -> ann_R Subset1 alv ang
  -> disjoint (live_globals AL) (snd (getAnn ang))
  -> exists lvZ, get AL (counted f) lvZ /\ (fst lvZ \ of_list (snd lvZ)) ⊆ getAnn alv.
Proof.
  intros LS RA IC AR.
  general induction IC; invt live_sound; invt renamedApart; invt (@ann_R); simpl in * |- *; eauto.
  - edestruct IHIC; dcr; eauto using disjoint_let.
    + eexists; split; eauto.
      exploit H; eauto. eapply map_get_1 with (f:=live_global); eauto. rewrite H11 in X.
      rewrite <- H7.
      assert (x ∉ fst x0 \ of_list (snd x0)).
      revert X; clear_all; cset_tac; intuition.
      eapply in_disj_absurd in X; eauto; cset_tac; intuition; eauto.
      revert H0 H2; clear_all; cset_tac; intuition.
      invc H. cset_tac; intuition; eauto.
  - edestruct IHIC; dcr; eauto using disjoint_if1.
    eexists; split; eauto. rewrite H2; eauto.
  - edestruct IHIC; dcr; eauto using disjoint_if2.
    eexists; split; eauto. rewrite H2; eauto.
  - edestruct IHIC; dcr; eauto using disjoint_let.
    + eexists; split; eauto.
      exploit H; eauto. eapply map_get_1 with (f:=live_global); eauto.
      rewrite H12 in X. rewrite <- H8.
      assert (x ∉ fst x0 \ of_list (snd x0)).
      revert X; clear_all; cset_tac; intuition.
      eapply in_disj_absurd in X; eauto; cset_tac; intuition; eauto.
      revert H0 H2; clear_all; cset_tac; intuition.
      invc H. cset_tac; intuition; eauto.
  - edestruct IHIC1; eauto; dcr; eauto using disjoint_fun1.
    destruct l; simpl in *. inv H1.
    edestruct IHIC2; eauto using disjoint_fun2; dcr. inv H14; simpl in *.
    eexists; split; eauto.
    eapply ann_R_get in H20.
    eapply ann_R_get in H21.
    rewrite H12 in *. rewrite H15 in *. simpl in *.
    rewrite <- H2 in H18.
    rewrite <- H10 in H. exploit H; eauto. eapply map_get_1 with (f:=live_global); eauto.
    rewrite <- H9, <- H18.
    revert X; clear_all; intros; cset_tac; intuition.
    eapply in_disj_absurd in X; eauto. cset_tac; intuition; eauto.
    cset_tac; intuition.
  - edestruct IHIC; eauto using disjoint_fun2; dcr.
    destruct l; simpl in *. inv H1.
    eexists; split; eauto.
    rewrite H2; eauto.
Qed.

Lemma renamedApart_live_imperative_is_functional s ang DL alv
: renamedApart s ang
  -> noUnreachableCode s
  -> live_sound Imperative DL s alv
  -> ann_R Subset1 alv ang
  -> disjoint (live_globals DL) (snd (getAnn ang))
  -> live_sound FunctionalAndImperative DL s alv.
Proof.
  intros RA NUC LS AR DISJ.
  general induction RA; invt noUnreachableCode; invt live_sound; invt (@ann_R);
  eauto 50 using live_sound, disjoint_let, disjoint_if1, disjoint_if2.
  - econstructor; simpl; eauto.
    + eapply IHRA1; eauto using disjoint_fun1.
    + eapply IHRA2; eauto using disjoint_fun2.
    + simpl in *.
      edestruct (@renamedApart_globals_live t); eauto using disjoint_fun2; simpl in *; dcr.
      inv H6. simpl in *. rewrite H7. eauto.
Qed.

Fixpoint mapAnn2 X X' Y (f:X -> X' -> Y) (a:ann X) (b:ann X') : ann Y :=
  match a, b with
    | ann1 a an, ann1 b bn => ann1 (f a b) (mapAnn2 f an bn)
    | ann2 a an1 an2, ann2 b bn1 bn2 => ann2 (f a b) (mapAnn2 f an1 bn1) (mapAnn2 f an2 bn2)
    | ann0 a, ann0 b => ann0 (f a b)
    | a, b => ann0 (f (getAnn a) (getAnn b))
  end.

Lemma getAnn_mapAnn2 A A' A'' (a:ann A) (b:ann A') (f:A->A'->A'') s
: annotation s a
  -> annotation s b
  -> getAnn (mapAnn2 f a b) = f (getAnn a) (getAnn b).
Proof.
  intros ANa ANb. general induction ANa; inv ANb; simpl; eauto.
Qed.


Lemma renamedApart_annotation s ang
: renamedApart s ang
  -> annotation s ang.
Proof.
  intros. general induction H; eauto 20 using @annotation.
Qed.

Lemma live_exp_sound_meet e D lv
:  Exp.freeVars e[<=]D
   -> live_exp_sound e lv
   -> live_exp_sound e (lv ∩ D).
Proof.
  intros.
  eapply Exp.freeVars_live in H0.
  eapply live_exp_sound_incl; eauto using Exp.live_freeVars.
  rewrite <- H, <- H0. cset_tac; intuition.
Qed.

Definition meet1 (x:set var) (y:set var * set var) :=
  match y with
    | (y, _) => x ∩ y
  end.

Lemma meet1_incl a b
: meet1 a b ⊆ a.
Proof.
  destruct b; simpl. cset_tac; intuition.
Qed.

Lemma meet1_Subset s alv ang
: annotation s alv
  -> annotation s ang
  -> ann_R Subset (mapAnn2 meet1 alv ang) alv.
Proof.
  intros AN1 AN2; general induction AN1; inv AN2; simpl; eauto using @ann_R, meet1_incl.
Qed.

Instance meet1_morphism
: Proper (Subset ==> @pe _ _ ==> Subset) meet1.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl. rewrite H, H1. reflexivity.
Qed.

Instance meet1_morphism'
: Proper (Equal ==> @pe _ _ ==> Equal) meet1.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl. rewrite H, H1. reflexivity.
Qed.


Lemma live_sound_renamedApart_minus s ang DL alv i
: renamedApart s ang
  -> live_sound i DL s alv
  -> bounded (live_globals DL) (fst (getAnn ang))
  -> live_sound i DL s (mapAnn2 meet1 alv ang).
Proof.
  intros RA LS. general induction RA; invt live_sound; simpl;
                eauto using live_sound, live_exp_sound_meet.
  - econstructor; eauto using live_exp_sound_meet.
    eapply IHRA; eauto using disjoint_let.
    + rewrite H1; simpl. rewrite <- incl_add'; eauto.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      rewrite H1; simpl. rewrite <- minus_meet.
      revert H11; clear_all; cset_tac; intuition.
      eapply H11; cset_tac; intuition.
  - econstructor; eauto using live_exp_sound_meet.
    + eapply IHRA1; eauto. rewrite H2; eauto.
    + eapply IHRA2; eauto. rewrite H3; eauto.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      rewrite H2; simpl. rewrite H13. reflexivity.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      rewrite H3; simpl. rewrite H14. reflexivity.
  - econstructor; eauto.
    + destruct if; simpl in *; eauto.
      exploit bounded_get; eauto.
      eapply map_get_1 with (f:=live_global); eauto. simpl in *.
      rewrite <- X. rewrite <- H5. clear_all; cset_tac; intuition.
    + intros. eapply live_exp_sound_meet; eauto.
      rewrite incl_list_union; eauto. eapply map_get_1; eauto.
      reflexivity.
  -  econstructor; eauto using live_exp_sound_meet.
    eapply IHRA; eauto using disjoint_let.
    + rewrite H1; simpl. rewrite <- incl_add'; eauto.
    + intros. eapply live_exp_sound_meet; eauto.
      rewrite incl_list_union; eauto. eapply map_get_1; eauto.
      reflexivity.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      rewrite H1; simpl. rewrite <- minus_meet.
      revert H12; clear_all; cset_tac; intuition.
      eapply H12; cset_tac; intuition.
  - constructor; eauto.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      eapply IHRA1; eauto.
      * eapply live_sound_monotone; eauto.
        econstructor; simpl. rewrite H2; simpl.
        split; eauto. cset_tac; intuition.
        reflexivity.
      * simpl. rewrite H2; simpl; split.
        clear_all; cset_tac; intuition.
        rewrite <- incl_right; eauto.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      eapply IHRA2; eauto.
      * eapply live_sound_monotone; eauto.
        econstructor; simpl. rewrite H2; simpl.
        split; eauto. cset_tac; intuition.
        reflexivity.
      * simpl. rewrite H2, H3; simpl; split; eauto.
        cset_tac; intuition.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      rewrite <- H12. rewrite H2. simpl; clear_all; cset_tac; intuition.
    + destruct if; eauto.
      erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      rewrite H2. simpl. rewrite <- minus_meet.
      revert H14; clear_all; cset_tac; intuition.
    + erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
      rewrite H3; simpl. rewrite H15; reflexivity.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
