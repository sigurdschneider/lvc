Require Import CSet Le ListUpdateAt Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Terminating MoreInversion.
Require Import Val Var Env IL Annotation Infra.Lattice AnnotationLattice.
Require Import DecSolve LengthEq MoreList Status AllInRel OptionR.
Require Import Keep Subterm Analysis CMapPartialOrder DomainSSA CMapTerminating.

Set Implicit Arguments.

Definition forwardF (sT:stmt) (Dom:stmt->Type) (BL:list bool)
           (forward: forall s (ST:subTerm s sT) (d:Dom sT) (anr:ann bool), Dom sT * ann bool * list bool)
           (F:list (params * stmt)) (rF:list (ann bool)) (a:Dom sT)
           (ST:forall n s, get F n s -> subTerm (snd s) sT)
  : Dom sT * list (ann bool) * list bool.
  revert F rF ST a.
  fix g 1. intros.
  destruct F as [|Zs F'].
  - eapply (a, nil, BL).
  - destruct rF as [|b rF'].
    + eapply (a, nil, BL).
    + pose (p:=forward (snd Zs) ltac:(eauto using get) a b).
      pose (q:=g F' rF' ltac:(eauto using get) (fst (fst p))).
      eapply (fst (fst q),
              snd (fst p) :: (snd (fst q)),
              zip join (snd p) (snd q)).
Defined.

Arguments forwardF [sT] [Dom] BL forward F rF a ST.

Fixpoint forwardF_length (sT:stmt) (Dom:stmt->Type) BL forward
           (F:list (params * stmt)) rF a
           (ST:forall n s, get F n s -> subTerm (snd s) sT) {struct F}
  : length (snd (fst (@forwardF sT Dom BL forward F rF a ST))) = min (length F) (length rF).
Proof.
  destruct F as [|Zs F'], rF; simpl; eauto.
Qed.

Lemma forwardF_snd_length (sT:stmt) (Dom:stmt->Type) BL
      (forward: forall s (ST:subTerm s sT) (d:Dom sT) (anr:ann bool), Dom sT * ann bool * list bool)
      (F:list (params * stmt)) rF a
      (ST:forall n Zs, get F n Zs -> subTerm (snd Zs) sT) k
      (LEN:forall n Zs ST d r, get F n Zs -> length (snd (@forward (snd Zs) ST d r)) = k)
      (LenBL: length BL = k)
  : length (snd (@forwardF sT Dom BL forward F rF a ST)) = k.
Proof.
  general induction F; destruct rF; simpl; eauto.
  len_simpl. erewrite IHF; eauto using get.
  erewrite LEN; eauto using get with len.
Qed.

Lemma forwardF_snd_length' (sT:stmt) (Dom:stmt->Type) BL
      (forward: forall s (ST:subTerm s sT) (d:Dom sT) (anr:ann bool), Dom sT * ann bool * list bool)
      (F:list (params * stmt)) rF a
      (ST:forall n Zs, get F n Zs -> subTerm (snd Zs) sT) k
      (LEN:forall n Zs ST d r, get F n Zs -> length (snd (@forward (snd Zs) ST d r)) = k)
      (Leq: k <= length BL) (LenF:❬F❭ > 0) (LenrF:❬rF❭ > 0)
  : length (snd (@forwardF sT Dom BL forward F rF a ST)) = k.
Proof.
  general induction F; destruct rF; simpl in *; eauto; try omega.
  len_simpl.
  destruct F,rF; try now (simpl; try erewrite LEN; try rewrite min_l; eauto using get with len).
  erewrite IHF; eauto using get.
  erewrite LEN; eauto using get with len.
Qed.

Smpl Add
     match goal with
     | [ |- context [ ❬snd (fst (@forwardF ?sT ?Dom ?BL ?f ?F ?rF ?a ?ST))❭ ] ] =>
       rewrite (@forwardF_length sT Dom BL f F rF a ST)
     | [ H : context [ ❬snd (fst (@forwardF ?sT ?Dom ?BL ?f ?F ?rF ?a ?ST))❭ ] |- _ ] =>
       rewrite (@forwardF_length sT Dom BL f F rF a ST) in H
     | [ |- context [ ❬snd (@forwardF ?sT ?Dom ?BL ?f ?F ?rF ?a ?ST)❭ ] ] =>
       erewrite (@forwardF_snd_length sT Dom BL f F rF a ST)
     | [ H : context [ ❬snd (@forwardF ?sT ?Dom ?BL ?f ?F ?rF ?a ?ST)❭ ] |- _ ] =>
       erewrite (@forwardF_snd_length sT Dom BL f F rF a ST) in H
     end : len.

Lemma ZLIncl_ext sT st F t (ZL:list params)
    (EQ:st = stmtFun F t) (ST:subTerm st sT)
    (ZLIncl:list_union (of_list ⊝ ZL) [<=] occurVars sT)
  : list_union (of_list ⊝ (fst ⊝ F ++ ZL)) [<=] occurVars sT.
Proof.
  subst.
  rewrite List.map_app.
  rewrite list_union_app. eapply union_incl_split; eauto.
  pose proof (subTerm_occurVars ST). simpl in *.
  rewrite <- H.
  eapply incl_union_left. eapply list_union_incl; intros; eauto with cset.
  inv_get. eapply incl_list_union. eapply map_get_1; eauto.
  cset_tac.
Qed.

Lemma ZLIncl_App_Z sT ZL n
      (Incl:list_union (of_list ⊝ ZL) [<=] occurVars sT)
  : of_list (nth n ZL (nil : params)) [<=] occurVars sT.
Proof.
  destruct (get_dec ZL n); dcr.
  - erewrite get_nth; eauto. rewrite <- Incl.
    eapply incl_list_union; eauto using zip_get.
  - rewrite not_get_nth_default; eauto.
    simpl. cset_tac.
Qed.

Arguments ZLIncl_App_Z {sT} {ZL} n Incl.

Definition sTDom D sT := VDom (occurVars sT) D.

Fixpoint forward (sT:stmt) (D: Type) `{JoinSemiLattice D}
         (exp_transf : forall U, bool -> VDom U D -> exp -> option D)
         (reach_transf : forall U, bool -> VDom U D -> op -> bool * bool)
         (ZL:list (params)) (ZLIncl:list_union (of_list ⊝ ZL) [<=] occurVars sT)
         (st:stmt) (ST:subTerm st sT) (d:VDom (occurVars sT) D) (anr:ann bool) {struct st}
  :  VDom (occurVars sT) D * ann bool * list bool.
  refine (
      match st as st', anr return st = st' -> VDom (occurVars sT) D * ann bool * list bool with
      | stmtLet x e s as st, ann1 b anr' =>
        fun EQ =>
          let d:VDom (occurVars sT) D := domupdd d (exp_transf _ b d e) (subTerm_EQ_Let_x EQ ST) in
          let '(d', ans', AL) :=
              forward sT D _ _ exp_transf reach_transf
                      ZL ZLIncl s (subTerm_EQ_Let EQ ST) d (setTopAnn anr' b) in
          (d', ann1 b ans', AL)
      | stmtIf e s t, ann2 b anr1 anr2 =>
        fun EQ =>
          let '(b1,b2) := reach_transf _ b d e in
          let '(a', an1, AL1) :=
              @forward _ D _ _ exp_transf reach_transf ZL ZLIncl s
                       (subTerm_EQ_If1 EQ ST) d (setTopAnn anr1 b1) in
          let '(a'', an2, AL2) :=
              @forward _ D _ _ exp_transf reach_transf ZL ZLIncl t
                       (subTerm_EQ_If2 EQ ST) a' (setTopAnn anr2 b2) in
          (a'', ann2 b an1 an2, zip join AL1 AL2)
      | stmtApp f Y as st, ann0 b =>
        fun EQ =>
          let Z := nth (counted f) ZL (nil:list var) in
          let Yc := List.map (Operation ∘ exp_transf _ b d) Y in
          (* we assume renamed apart here, so it's ok to leave definitions
       in d[X <-- Yc] that are /not/ defined at the point where f is defined *)
          let AL := ((fun _ => false) ⊝ ZL) in
          (if b then domjoin_listd d Z Yc (ZLIncl_App_Z (counted f) ZLIncl) else d, ann0 b, list_update_at AL (counted f) b)
      | stmtReturn x as st, ann0 b =>
        fun EQ =>
          (d, ann0 b, ((fun _ => false) ⊝ ZL))
      | stmtFun F t as st, annF b rF r =>
        fun EQ =>
          let ZL' := List.map fst F ++ ZL in
          let '(a', r', AL) :=
              @forward sT D _ _ exp_transf reach_transf ZL' (ZLIncl_ext ZL EQ ST ZLIncl)
                       t (subTerm_EQ_Fun1 EQ ST) d (setTopAnn r b) in
          let '(a'', rF', AL') := @forwardF sT (sTDom D) AL (forward sT D _ _ exp_transf reach_transf ZL' (ZLIncl_ext ZL EQ ST ZLIncl))
                                          F (zip (@joinTopAnn _ _ _) rF AL)
                                          a'(subTerm_EQ_Fun2 EQ ST)  in
          (a'', annF b (zip (@setTopAnn _) rF' AL') r', drop (length F) AL')
      | _, _ => fun _ => (d, anr, ((fun _ => false) ⊝ ZL))
      end eq_refl).
Defined.

Smpl Add 100
     match goal with
     | [ H : context [ ❬list_update_at ?ZL _ _❭ ] |- _ ] =>
       rewrite (list_update_at_length _ ZL) in H
     | [ |- context [ ❬list_update_at ?ZL _ _❭ ] ] =>
       rewrite (list_update_at_length _ ZL)
     end : len.


Lemma forward_length (sT:stmt) D `{JoinSemiLattice D} f fr ZL ZLIncl s (ST:subTerm s sT) d r
  : ❬snd (forward f fr ZL ZLIncl ST d r)❭ = ❬ZL❭.
Proof.
  revert_except s.
  sind s; destruct s, r; simpl; eauto with len;
    repeat let_pair_case_eq; subst; simpl; eauto.
  - len_simpl. rewrite (IH s1), (IH s2); eauto with len.
  - rewrite length_drop_minus.
    len_simpl; try reflexivity.
    + rewrite IH; eauto. len_simpl. omega.
    + intros. rewrite !IH; eauto.
Qed.

Smpl Add 100
     match goal with
     | [ H : context [ ❬snd (@forward ?sT ?D ?PO ?JSL ?f ?fr ?ZL ?ZLIncl ?s ?ST ?d ?r)❭ ] |- _ ] =>
       setoid_rewrite (@forward_length sT D PO JSL f fr ZL ZLIncl s ST d r) in H
     | [ |- context [ ❬snd (@forward ?sT ?D ?PO ?JSL ?f ?fr ?ZL ?ZLIncl ?s ?ST ?d ?r)❭ ] ] =>
       setoid_rewrite (@forward_length sT D PO JSL f fr ZL ZLIncl s ST d r)
     end : len.

Lemma forward_fst_snd_getAnn sT D `{JoinSemiLattice D} f fr ZL ZLIncl
      s (ST:subTerm s sT) d r
  : getAnn (snd (fst (forward f fr ZL ZLIncl ST d r))) = getAnn r.
Proof.
  revert_except s.
  sind s; destruct s, r; simpl; eauto with len;
    repeat let_pair_case_eq; subst; simpl; eauto.
Qed.

Lemma forward_getAnn sT D `{JoinSemiLattice D} f fr ZL ZLIncl s (ST:subTerm s sT) b r r'
  : ann_R poEq (snd (fst (forward f fr ZL ZLIncl ST b r))) r'
    -> getAnn r = getAnn r'.
Proof.
  intros. eapply ann_R_get in H1.
  rewrite forward_fst_snd_getAnn in H1. eauto.
Qed.

Lemma forwardF_mon sT (D:Type) `{JoinSemiLattice D} f fr ZL ZLIncl BL
      (Len:❬BL❭ <= ❬ZL❭)
      (F:list (params * stmt)) STF rF a
  : PIR2 poLe BL (snd (@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) F rF a STF)).
Proof.
  revert rF a.
  induction F; intros; destruct rF; simpl; eauto.
  eapply PIR2_impb_orb_left; eauto with len.
Qed.

Lemma forwardF_mon' sT (D:Type) `{JoinSemiLattice D}
      f fr ZL ZLIncl (F:list (params * stmt)) rF BL STF
       (Len:❬F❭ = ❬rF❭) a
  : PIR2 poEq (getAnn ⊝ rF)
         (getAnn ⊝ snd (fst (@forwardF sT (sTDom D) BL
                                       (forward f fr ZL ZLIncl) F rF a STF))).
Proof.
  general induction Len; intros; simpl; eauto.
  econstructor.
  - setoid_rewrite forward_fst_snd_getAnn. reflexivity.
  - eapply IHLen.
Qed.

Ltac fold_po :=
  repeat match goal with
         | [ H : context [ @ann_R ?A ?A (@poLe ?A ?I) ] |- _ ] =>
           change (@ann_R A A (@poLe A I)) with (@poLe (@ann A) _) in H
         | [ H : context [ PIR2 poLe ?x ?y ] |- _ ] =>
           change (PIR2 poLe x y) with (poLe x y) in H
         | [ |- context [ ann_R poLe ?x ?y ] ] =>
           change (ann_R poLe x y) with (poLe x y)
  end.

Require Import FiniteFixpointIteration.

Lemma forwardF_monotone (sT:stmt) (Dom : stmt -> Type) `{PartialOrder (Dom sT)}
      (forward forward' : forall s : stmt,
          subTerm s sT -> Dom sT -> ann bool -> Dom sT * ann bool * 〔bool〕) F
      (fwdMon:forall  n Zs (GET:get F n Zs) (ST:subTerm (snd Zs) sT),
          forall (d d' : Dom sT),
            d ⊑ d'
            -> forall (r r':ann bool),
              r ⊑ r'
              -> forward (snd Zs) ST d r ⊑ forward' (snd Zs) ST d' r')
  : forall ST,
    forall (d d' : Dom sT),
      d ⊑ d'
      -> forall (rF rF':list (ann bool)),
        rF ⊑ rF'
        -> forall (BL BL':list bool),
          BL ⊑ BL'
        -> forwardF BL forward F rF d ST
                   ⊑  forwardF BL' forward' F rF' d' ST.
Proof.
  intros ST d d' LE_d rF rF' LE_rf.
  general induction F; inv LE_rf; simpl;
    try now (econstructor; simpl; eauto using @ann_R, @PIR2).
  split; [split|].
  - eapply IHF; eauto using get.
    eapply fwdMon; eauto using get.
  - econstructor; eauto.
    eapply fwdMon; eauto using get.
    eapply IHF; eauto using get. eapply fwdMon; eauto using get.
  - eapply PIR2_impb_orb; eauto with len.
    eapply fwdMon; eauto using get.
    eapply IHF; eauto using get. eapply fwdMon; eauto using get.
Qed.

Lemma forwardF_ext (sT:stmt) (Dom : stmt -> Type) `{PartialOrder (Dom sT)}
      (forward forward' : forall s : stmt,
          subTerm s sT -> Dom sT -> ann bool -> Dom sT * ann bool * 〔bool〕) F
      (fwdMon:forall  n Zs (GET:get F n Zs) (ST:subTerm (snd Zs) sT),
          forall (d d' : Dom sT),
            poEq d d'
            -> forall (r r':ann bool),
              poEq r r'
              -> poEq (forward (snd Zs) ST d r) (forward' (snd Zs) ST d' r'))
  : forall ST,
    forall (d d' : Dom sT),
      poEq d d'
      -> forall (rF rF':list (ann bool)),
        poEq rF rF'
        -> forall (BL BL':list bool),
          poEq BL BL'
        -> poEq (forwardF BL forward F rF d ST)
               (forwardF BL' forward' F rF' d' ST).
Proof.
  intros ST d d' LE_d rF rF' LE_rf.
  general induction F; inv LE_rf; simpl;
    try now (econstructor; simpl; eauto using @ann_R, @PIR2).
  split; [split|].
  - eapply IHF; eauto using get.
    eapply fwdMon; eauto using get.
  - econstructor; eauto.
    eapply fwdMon; eauto using get.
    eapply IHF; eauto using get. eapply fwdMon; eauto using get.
  - eapply PIR2_eq_zip; eauto with len.
    eapply fwdMon; eauto using get.
    eapply IHF; eauto using get. eapply fwdMon; eauto using get.
Qed.

Lemma forward_monotone sT D `{JoinSemiLattice D}
      (f: forall U : ⦃nat⦄, bool -> VDom U D -> exp -> ؟ D)
      (fr: forall U : ⦃nat⦄, bool -> VDom U D -> op -> bool * bool)
      (fMon: forall U e (a a':VDom U D), a ⊑ a' -> forall b b', b ⊑ b' -> f _ b a e ⊑ f _ b' a' e)
      (frMon:forall U e (a a':VDom U D),
            a ⊑ a' -> forall b b', b ⊑ b' -> fr _ b a e ⊑ fr _ b' a' e)
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) ZLIncl,
    forall (d d' : VDom (occurVars sT) D), d ⊑ d'
      -> forall (r r':ann bool), r ⊑ r'
      -> forward f fr ZL ZLIncl ST d r ⊑ forward f fr ZL ZLIncl ST d' r'.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  sind s; destruct s; intros ST ZL ZLIncl d d' LE_d r r'  LE_r;
    destruct r; inv LE_r;
      simpl forward; repeat let_pair_case_eq; subst;
        eauto 10 using @ann_R;
        try now (econstructor; simpl; eauto using @ann_R).
  - unfold domupdd. simpl. pose proof (fMon _ e  _ _ LE_d _ _ H3); eauto.
    simpl in *. split; dcr; eauto; [split; eauto|]; simpl;
                  eauto 20 using domupd_le, ann_R_setTopAnn, ann_R.
    + eapply IH; eauto using domupd_le, ann_R_setTopAnn.
    + econstructor; eauto. eapply IH; eauto using domupd_le.
      eauto using ann_R_setTopAnn.
    + eapply IH; eauto using domupd_le, ann_R_setTopAnn.
  - pose proof (fMon _ (Operation e) _ _ LE_d) as LE_f.
    pose proof (frMon _ e _ _ LE_d) as LE_fr.
    pose proof (IH s1 ltac:(eauto) (subTerm_EQ_If1 eq_refl ST) ZL ZLIncl) as LE1; eauto.
    pose proof (IH s2 ltac:(eauto) (subTerm_EQ_If2 eq_refl ST) ZL ZLIncl) as LE2; eauto.
    split; [split|];simpl.
    + eapply LE2; eauto. eapply LE1; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
    + econstructor; eauto.
      eapply LE1; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
      eapply LE2; eauto. eapply LE1; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
    + eapply PIR2_impb_orb; eauto with len.
      * eapply LE1; eauto.
        eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
      * eapply LE2; eauto. eapply LE1; eauto.
        eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
        eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
  - split; [split|]; simpl.
    + repeat (cases; eauto; simpl in *).
      eapply domjoin_list_le; eauto.
      revert fMon LE_d.
      clear_all; intros.
      * general induction Y; eauto.
        simpl List.map. econstructor.
        eapply fMon; eauto.
        eapply IHY; eauto.
      * etransitivity; eauto using domjoin_list_exp.
   + econstructor; eauto.
   + pose proof (@update_at_poLe bool _ _ _ ZL l _ _ H2).
     simpl in *. eauto.
  - split; [split|]; simpl.
    + pose proof (@forwardF_monotone sT (sTDom D) _); eauto.
      eapply H1; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
      eapply PIR2_zip_joinTopAnnO; eauto.
      hnf. eapply PIR2_get; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
    + econstructor; eauto.
      * len_simpl; try reflexivity;
        eauto with len.
      * eapply get_PIR2.
        eapply (@PIR2_zip_setTopAnnO bool PartialOrder_bool).
        pose proof (@forwardF_monotone sT (sTDom D) _); eauto.
        eapply H1; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply (@PIR2_zip_joinTopAnnO bool PartialOrder_bool); eauto.
        eapply PIR2_get; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply forwardF_monotone; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply (@PIR2_zip_joinTopAnnO bool PartialOrder_bool); eauto.
        eapply PIR2_get; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
      * eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
    + eapply PIR2_drop.
      eapply forwardF_monotone; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
      eapply PIR2_zip_joinTopAnnO; eauto.
      hnf. eapply PIR2_get; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
Qed.

Lemma forward_ext sT D `{JoinSemiLattice D}
      (f: forall U : ⦃nat⦄, bool -> VDom U D -> exp -> ؟ D)
      (fr: forall U : ⦃nat⦄, bool -> VDom U D -> op -> bool * bool)
      (fMon: forall U e (a a':VDom U D), a ≣ a' -> forall b b', b ≣ b' -> f _ b a e ≣ f _ b' a' e)
      (frMon:forall U e (a a':VDom U D),
            a ≣ a' -> forall b b', b ≣ b' -> fr _ b a e ≣ fr _ b' a' e)
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) ZLIncl,
    forall (d d' : VDom (occurVars sT) D), d ≣ d'
      -> forall (r r':ann bool), r ≣ r'
      -> forward f fr ZL ZLIncl ST d r ≣ forward f fr ZL ZLIncl ST d' r'.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  sind s; destruct s; intros ST ZL ZLIncl d d' LE_d r r'  LE_r;
    destruct r; inv LE_r;
      simpl forward; repeat let_pair_case_eq; subst;
        eauto 10 using @ann_R;
        try now (econstructor; simpl; eauto using @ann_R).
  - unfold domupdd. simpl. pose proof (fMon _ e  _ _ LE_d _ _ H3); eauto.
    simpl in *. split; dcr; eauto; [split; eauto|]; simpl;
                  eauto 20 using domupd_le, ann_R_setTopAnn, ann_R.
    + eapply IH; eauto using domupd_eq, ann_R_setTopAnn.
    + econstructor; eauto. eapply IH; eauto using domupd_eq.
      eauto using ann_R_setTopAnn.
    + eapply IH; eauto using domupd_eq, ann_R_setTopAnn.
  - pose proof (fMon _ (Operation e) _ _ LE_d) as LE_f.
    pose proof (frMon _ e _ _ LE_d) as LE_fr.
    pose proof (IH s1 ltac:(eauto) (subTerm_EQ_If1 eq_refl ST) ZL ZLIncl) as LE1; eauto.
    pose proof (IH s2 ltac:(eauto) (subTerm_EQ_If2 eq_refl ST) ZL ZLIncl) as LE2; eauto.
    split; [split|];simpl.
    + eapply LE2; eauto. eapply LE1; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
    + econstructor; eauto.
      eapply LE1; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
      eapply LE2; eauto. eapply LE1; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
    + eapply PIR2_eq_zip; eauto.
      * eapply LE1; eauto.
        eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
      * eapply LE2; eauto. eapply LE1; eauto.
        eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
        eapply ann_R_setTopAnn; eauto. eapply LE_fr; eauto.
  - split; [split|]; simpl.
    + repeat (cases; eauto; simpl in *).
      eapply domjoin_list_eq; eauto.
      revert fMon LE_d.
      clear_all; intros.
      * general induction Y; eauto.
        simpl List.map. econstructor.
        eapply fMon; eauto.
        eapply IHY; eauto.
   + econstructor; eauto.
   + inv H2. reflexivity.
  - split; [split|]; simpl.
    + pose proof (@forwardF_ext sT (sTDom D) _); eauto.
      eapply H1; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
      eapply PIR2_poEq_zip_joinTopAnnO; eauto.
      hnf. eapply PIR2_get; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
    + econstructor; eauto.
      * len_simpl; try reflexivity;
        eauto with len.
      * eapply get_PIR2.
        eapply (@PIR2_poEq_zip_setTopAnnO bool PartialOrder_bool).
        eapply forwardF_ext; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply (@PIR2_poEq_zip_joinTopAnnO bool PartialOrder_bool); eauto.
        eapply PIR2_get; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply forwardF_ext; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply (@PIR2_poEq_zip_joinTopAnnO bool PartialOrder_bool); eauto.
        eapply PIR2_get; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
      * eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
    + eapply PIR2_drop.
      eapply forwardF_ext; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
      eapply PIR2_poEq_zip_joinTopAnnO; eauto.
      hnf. eapply PIR2_get; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
Qed.


Lemma forwardF_PIR2 sT D `{JoinSemiLattice D} BL ZL ZLIncl
      (F:list (params * stmt)) sa a (Len1:❬F❭ = ❬sa❭)
      (Len2:❬BL❭ = ❬ZL❭)
      (f: forall U : ⦃nat⦄, bool -> VDom U D -> exp -> ؟ D)
      (fr: forall U : ⦃nat⦄, bool -> VDom U D -> op -> bool * bool)
      (EQ: forall n Zs r (ST:subTerm (snd Zs) sT), get F n Zs -> get sa n r ->
                        poEq (fst (fst (forward f fr ZL ZLIncl ST a r))) a)
      (fExt: forall U e (a a':VDom U D), a ≣ a' -> forall b b', b ≣ b' -> f _ b a e ≣ f _ b' a' e)
      (frExt:forall U e (a a':VDom U D),
            a ≣ a' -> forall b b', b ≣ b' -> fr _ b a e ≣ fr _ b' a' e)
      n r Zs (ST:subTerm (snd Zs) sT) (Getsa:get sa n r) (GetF:get F n Zs) STF
:
  PIR2 impb
       (snd (forward f fr ZL ZLIncl ST a r))
       (snd (@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) F sa a STF)).
Proof.
  general induction n; isabsurd; simpl.
  - eapply PIR2_impb_orb_right.
    + len_simpl; eauto. intros. eauto with len.
    + assert (ST = (STF 0 Zs (getLB xl Zs))).
      eapply subTerm_PI. subst. reflexivity.
  - inv Getsa; inv GetF. simpl.
    eapply PIR2_impb_orb_left; eauto with len.
    etransitivity; [| eapply IHn; eauto using get].
    + setoid_rewrite forward_ext at 2; eauto.
      reflexivity.
      rewrite EQ; eauto using get.
      reflexivity.
    + intros.
      setoid_rewrite EQ at 2; eauto using get.
      rewrite (forward_ext f fr fExt frExt).
      eapply EQ; eauto using get.
      eapply EQ; eauto using get.
      reflexivity.
Qed.



Require Import Take.
Lemma forwardF_get  (sT:stmt) D `{JoinSemiLattice D} BL ZL
      (F:list (params * stmt)) rF a ZLIncl
      f fr
      (ST:forall n s, get F n s -> subTerm (snd s) sT) n aa
           (GetBW:get (snd (fst (@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) F rF a ST))) n aa)
  :
    { Zs : params * stmt &
           {GetF : get F n Zs &
                   { r : ann bool &
                         {GetrF : get rF n r &
                                  { ST' : subTerm (snd Zs) sT &
                                          { ST'' : forall (n0 : nat) (s : params * stmt), get (take n F) n0 s -> subTerm (snd s) sT | aa = snd (fst (forward f fr ZL ZLIncl ST' (fst (fst (@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) (take n F) (take n rF) a ST''))) r))
  } } } } } }.
Proof.
  eapply get_getT in GetBW.
  general induction n.
  - destruct F,rF; inv GetBW; simpl in *.
    simpl. do 6 (eexists; eauto 20 using get).
    + isabsurd.
  - destruct F, rF; isabsurd. inv GetBW.
    edestruct IHn as [Zs [? [? [? [? [? ]]]]]]; eauto; subst. simpl in *. subst.
    assert (STx:forall (n1 : nat) (s : params * stmt),
               get (p::take n F) n1 s -> subTerm (snd s) sT). {
      intros. inv H1; eauto using get.
    }
    assert (STEQ1:(ST 0 p (getLB F p) = (STx 0 p (getLB (take n F) p))))
      by eapply subTerm_PI.
    assert (STEQ2:x3 =
            (fun (n' : nat) (Zs : params * stmt) (H1 : get (take n F) n' Zs) =>
               STx (S n') Zs (getLS p H1)))
      by eapply ProofIrrelevance.proof_irrelevance.

    do 6 (eexists; eauto using get).
    repeat f_equal. eapply STEQ1.
    eapply STEQ2.
Qed.


Require Import FiniteFixpointIteration.


Lemma forward_annotation sT D `{JoinSemiLattice D} s (ST:subTerm s sT)
      f fr ZL ZLIncl d r
      (AN:annotation s r)
  : annotation s (snd (fst (forward f fr ZL ZLIncl ST d r))).
Proof.
  revert ZL ZLIncl d r AN.
  sind s; intros; invt @annotation; simpl;
    repeat let_pair_case_eq; subst; simpl;
      eauto 20 using @annotation, setTopAnn_annotation.
  - econstructor; eauto 20 using setTopAnn_annotation.
    + len_simpl; try reflexivity.
      rewrite H1.
      rewrite !min_l; eauto with len.
      rewrite !min_l; eauto with len.
      rewrite !min_l; eauto with len.
      rewrite !min_l; eauto with len.
      eauto with len.
    + intros; inv_get.
      eapply setTopAnn_annotation; eauto.
      eapply forwardF_get in H6. destruct H6; dcr; subst.
      inv_get. eapply IH; eauto.
      eapply setTopAnn_annotation; eauto.
Qed.


Instance makeForwardAnalysis D
         {PO:PartialOrder D}
         (BSL:JoinSemiLattice D)
         (LB:LowerBounded D)
         (f: forall U : ⦃nat⦄, bool -> VDom U D -> exp -> ؟ D)
         (fr: forall U : ⦃nat⦄, bool -> VDom U D -> op -> bool * bool)
         (fMon: forall U e (a a':VDom U D), a ⊑ a' -> forall b b', b ⊑ b' -> f _ b a e ⊑ f _ b' a' e)
         (frMon:forall U e (a a':VDom U D),
             a ⊑ a' -> forall b b', b ⊑ b' -> fr _ b a e ⊑ fr _ b' a' e)
         (Trm: Terminating D poLt)

  : forall s, Iteration (VDom (occurVars s) D * { a : ann bool | annotation s a }) :=
  {
    step := fun dr =>
             let a := forward f fr nil (incl_empty _ (occurVars s)) (subTerm_refl s)
                             (fst dr) (proj1_sig (snd dr)) in
             (fst (fst a), exist (fun a => annotation s a) (snd (fst a)) _);
    initial_value := bottom
  }.

Proof.
  - subst a.
    eapply forward_annotation; eauto.
    eapply (proj2_sig (snd dr)).
  - eapply bottom_least.
  - eapply terminating_pair; eauto.
    + eapply terminating_Dom; eauto.
    + eapply terminating_sig; eauto.
      eapply terminating_ann.
      eapply terminating_bool.
  - hnf; intros.
    eapply (forward_monotone f fr fMon frMon); eauto.
    eapply H. eapply H.
Defined.

Lemma snd_forwardF_inv (sT:stmt) D `{JoinSemiLattice D} f fr BL ZL ZLIncl F sa AE STF
      (P1:PIR2 (ann_R eq)
               (setTopAnn (A:=bool)
                          ⊜ (snd (fst (@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) F
                                                (joinTopAnn (A:=bool) ⊜ sa BL) AE STF)))
                          (snd (forwardF BL
                                         (forward f fr ZL ZLIncl) F
                                         (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa)
      (Len1:❬F❭ = ❬sa❭) (Len2:❬F❭ <= ❬BL❭) (Len3:❬ZL❭ = ❬BL❭)
  : PIR2 (ann_R eq) (joinTopAnn (A:=bool) ⊜ sa BL) sa.
Proof.
  eapply PIR2_ann_R_get in P1.
  rewrite getAnn_setTopAnn_zip in P1.
  pose proof (PIR2_joinTopAnn_zip_left sa BL).
  eapply H1; clear H1.
  etransitivity.
  eapply PIR2_take.
  eapply (@forwardF_mon sT D _ _ f fr ZL ZLIncl BL ltac:(omega) F STF (joinTopAnn (A:=bool) ⊜ sa BL) AE).
  etransitivity. Focus 2.
  eapply PIR2_R_impl; try eapply P1; eauto.
  assert (❬sa❭ = (Init.Nat.min
          ❬snd
             (fst
                (forwardF BL (forward f fr ZL ZLIncl) F
                   (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))❭
          ❬snd
             (forwardF BL (forward f fr ZL ZLIncl) F (joinTopAnn (A:=bool) ⊜ sa BL)
                       AE STF)❭)). {
    clear P1.
    rewrite forwardF_length.
    erewrite forwardF_snd_length; try reflexivity.
    + repeat rewrite min_l; eauto; len_simpl;
        rewrite Len1; rewrite min_l; omega.
    + intros; len_simpl; eauto.
  }
  rewrite H1. reflexivity.
Qed.

Lemma snd_forwardF_inv' sT D `{JoinSemiLattice D}
      (f: forall U : ⦃nat⦄, bool -> VDom U D -> exp -> ؟ D)
      (fr: forall U : ⦃nat⦄, bool -> VDom U D -> op -> bool * bool)
      BL ZL ZLIncl F sa AE STF
      (P1:PIR2 (ann_R eq)
               (setTopAnn (A:=bool)
                          ⊜ (snd (fst (forwardF BL (forward f fr ZL ZLIncl) F
                                                (joinTopAnn (A:=bool) ⊜ sa BL) AE STF)))
                          (snd (forwardF BL
                                         (forward f fr ZL ZLIncl) F
                                         (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa)
      (Len1:❬F❭ = ❬sa❭) (Len2:❬F❭ <= ❬BL❭) (Len3:❬ZL❭ = ❬BL❭)
  : PIR2 (ann_R eq)
              (snd (fst (@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) F
                                   (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa.
Proof.
  assert (P2:PIR2 poLe (Take.take ❬sa❭
                               (snd (forwardF BL (forward f fr ZL ZLIncl) F
                                              (joinTopAnn (A:=bool) ⊜ sa BL) AE
                                              STF))) (getAnn ⊝ sa)). {
    eapply PIR2_ann_R_get in P1.
    rewrite getAnn_setTopAnn_zip in P1.
     etransitivity. Focus 2.
    eapply PIR2_R_impl; try eapply P1; eauto.
    assert (❬sa❭ = (Init.Nat.min
                      ❬snd
                         (fst
                            (forwardF BL (forward f fr ZL ZLIncl) F
                                      (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))❭
                      ❬snd
                         (forwardF BL (forward f fr ZL ZLIncl) F (joinTopAnn (A:=bool) ⊜ sa BL)
                                   AE STF)❭)). {
      clear P1.
      rewrite forwardF_length.
      erewrite forwardF_snd_length; try reflexivity.
      + repeat rewrite min_l; eauto; len_simpl;
          rewrite Len1; rewrite min_l; omega.
      + intros; len_simpl; eauto.
    }
    rewrite H1. reflexivity.
  }
  assert (PIR2 (ann_R eq) (joinTopAnn (A:=bool) ⊜ sa BL) sa). {
    pose proof (PIR2_joinTopAnn_zip_left sa BL).
    eapply H1; clear H1.
    etransitivity.
    eapply PIR2_take.
    eapply (@forwardF_mon sT D _ _ f fr ZL ZLIncl BL ltac:(omega) F STF (joinTopAnn (A:=bool) ⊜ sa BL) AE). eauto.
  }
  etransitivity; try eapply P1.
  symmetry.
  eapply (PIR2_setTopAnn_zip_left); eauto.
  rewrite <- forwardF_mon';[|len_simpl; rewrite min_l; eauto; omega].
  - len_simpl. rewrite min_r, min_l; eauto; try rewrite Len1; try rewrite min_l; try omega.
    eapply PIR2_ann_R_get in H1.
    rewrite H1.
    eapply PIR2_ann_R_get in P1.
    etransitivity; try eapply P1.
    eapply PIR2_get; intros; inv_get.
    rewrite getAnn_setTopAnn; eauto.
    len_simpl;[| | reflexivity].
    rewrite min_r; try omega.
    repeat rewrite min_l; try omega.
    intros; eauto with len.
Qed.



Lemma snd_forwardF_inv_get sT D `{JoinSemiLattice D} f fr BL ZL ZLIncl F sa AE STF
      (Len1:❬F❭ = ❬sa❭) (Len2:❬F❭ <= ❬BL❭) (Len3:❬ZL❭ = ❬BL❭)
      (P1:PIR2 (ann_R eq)
               (snd (fst (@forwardF sT (sTDom D)  BL (forward f fr ZL ZLIncl) F
                                  (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa)
      (P2:PIR2 (ann_R eq) (joinTopAnn (A:=bool) ⊜ sa BL) sa)
      (EQ: forall n Zs r (ST:subTerm (snd Zs) sT), get F n Zs -> get sa n r ->
                        poEq (fst (fst (forward f fr ZL ZLIncl ST AE r))) AE)
      (fExt: forall U e (a a':VDom U D), a ≣ a' -> forall b b', b ≣ b' -> f _ b a e ≣ f _ b' a' e)
      (frExt:forall U e (a a':VDom U D),
          a ≣ a' -> forall b b', b ≣ b' -> fr _ b a e ≣ fr _ b' a' e)
      n r Zs (Getsa:get sa n r)
      (GetF:get F n Zs) (STZs:subTerm (snd Zs) sT)
  : ann_R eq (snd (fst (forward f fr ZL ZLIncl STZs AE r))) r.
Proof.
  rewrite forwardF_ext in P1; try eapply P2; try reflexivity.
  Focus 2. intros. eapply forward_ext; eauto.
  clear Len3 P2.
  general induction Len1; simpl in *.
  destruct BL; isabsurd; simpl in *. inv Getsa; inv GetF.
  - inv P1.
    assert((STF 0 Zs (@getLB (params * stmt) XL Zs)) = STZs).
    eapply subTerm_PI. rewrite <- H1.
    eapply pf.
  - inv P1.
    eapply IHLen1; eauto using get.
    Focus 2.
    rewrite forwardF_ext; eauto.
    intros. eapply forward_ext; eauto.
    symmetry. eapply EQ; eauto using get. reflexivity.
    simpl. omega.
Qed.
