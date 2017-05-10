Require Import CSet Le ListUpdateAt Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Terminating MoreInversion.
Require Import Val Var Env IL Annotation Infra.Lattice.
Require Import DecSolve LengthEq MoreList Status AllInRel OptionR.
Require Import Keep Subterm Analysis CMapPartialOrder DomainSSA.

Set Implicit Arguments.


Definition joinTopAnn A `{JoinSemiLattice A} (a:ann A) (b:A) :=
  setTopAnn a (join (getAnn a) b).

Definition forwardF (D:Type) (BL:list bool)
           (forward: forall (s:stmt) (d:Dom D) (anr:ann bool),  Dom D * ann bool * list bool)
           (F:list (params * stmt)) (rF:list (ann bool)) (a:Dom D)
  : Dom D * list (ann bool) * list bool.
  revert F rF a.
  fix g 1. intros.
  destruct F as [|Zs F'].
  - eapply (a, nil, BL).
  - destruct rF as [|b rF'].
    + eapply (a, nil, BL).
    + pose (p:=forward (snd Zs) a b).
      pose (q:=g F' rF' (fst (fst p))).
      eapply (fst (fst q),
              snd (fst p) :: (snd (fst q)),
              zip join (snd p) (snd q)).
Defined.

Arguments forwardF [D] BL forward F rF a.

Fixpoint forwardF_length (D:Type) BL forward
           (F:list (params * stmt)) rF a
           {struct F}
  : length (snd (fst (@forwardF D BL forward F rF a))) = min (length F) (length rF).
Proof.
  destruct F as [|Zs F'], rF; simpl; eauto.
Qed.

Lemma forwardF_snd_length (D:Type) BL
      (forward: forall (s:stmt) (d:Dom D) (anr:ann bool), Dom D * ann bool * list bool)
      (F:list (params * stmt)) rF a
      k
      (LEN:forall n Zs d r, get F n Zs -> length (snd (@forward (snd Zs) d r)) = k)
      (LenBL: length BL = k)
  : length (snd (@forwardF D BL forward F rF a)) = k.
Proof.
  general induction F; destruct rF; simpl; eauto.
  len_simpl. erewrite IHF; eauto using get.
  erewrite LEN; eauto using get with len.
Qed.

Lemma forwardF_snd_length' (D:Type) BL
      (forward: forall (s:stmt) (d:Dom D) (anr:ann bool), Dom D * ann bool * list bool)
      (F:list (params * stmt)) rF a
      k
      (LEN:forall n Zs d r, get F n Zs -> length (snd (@forward (snd Zs) d r)) = k)
      (Leq: k <= length BL) (LenF:❬F❭ > 0) (LenrF:❬rF❭ > 0)
  : length (snd (@forwardF D BL forward F rF a)) = k.
Proof.
  general induction F; destruct rF; simpl in *; eauto; try omega.
  len_simpl.
  destruct F,rF; try now (simpl; try erewrite LEN; try rewrite min_l; eauto using get with len).
  erewrite IHF; eauto using get.
  erewrite LEN; eauto using get with len.
Qed.


Smpl Add
     match goal with
     | [ |- context [ ❬snd (fst (@forwardF ?D ?BL ?f ?F ?rF ?a))❭ ] ] =>
       rewrite (@forwardF_length D BL f F rF a)
     | [ H : context [ ❬snd (fst (@forwardF ?D ?BL ?f ?F ?rF ?a))❭ ] |- _ ] =>
       rewrite (@forwardF_length D BL f F rF a) in H
     | [ |- context [ ❬snd (@forwardF ?D ?BL ?f ?F ?rF ?a)❭ ] ] =>
       erewrite (@forwardF_snd_length D BL f F rF a)
     | [ H : context [ ❬snd (@forwardF ?D ?BL ?f ?F ?rF ?a)❭ ] |- _ ] =>
       erewrite (@forwardF_snd_length D BL f F rF a) in H
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

Lemma subTerm_EQ_If_freeVars_e
  : forall (sT st : stmt) (e : op) (s t : stmt),
    st = stmtIf e s t -> subTerm st sT -> Op.freeVars e ⊆ occurVars sT.
Proof.
  intros; subst.
  eapply subTerm_occurVars in H0. simpl in *.
  cset_tac.
Qed.



Fixpoint forward (D: Type) `{JoinSemiLattice D}
           (exp_transf : bool -> Dom D -> exp -> option D)
           (reach_transf : bool -> Dom D -> op -> bool * bool)
           (ZL:list (params))
           (st:stmt) (d:Dom D) (anr:ann bool) {struct st}
  :  Dom D * ann bool * list bool.
  refine (
      match st as st', anr return Dom D * ann bool * list bool with
      | stmtLet x e s as st, ann1 b anr' =>
          let d:Dom D := domupd d x (exp_transf b d e) in
          let '(d', ans', AL) :=
              forward D _ _ exp_transf reach_transf
                      ZL s d (setTopAnn anr' b) in
          (d', ann1 b ans', AL)
      | stmtIf e s t, ann2 b anr1 anr2 =>
          let '(b1,b2) := reach_transf b d e in
          let '(a', an1, AL1) :=
              @forward D _ _ exp_transf reach_transf ZL s
                       d (setTopAnn anr1 b1) in
          let '(a'', an2, AL2) :=
              @forward D _ _ exp_transf reach_transf ZL t
                       a' (setTopAnn anr2 b2) in
          (a'', ann2 b an1 an2, zip join AL1 AL2)
      | stmtApp f Y as st, ann0 b =>
          let Z := nth (counted f) ZL (nil:list var) in
          let Yc := List.map (Operation ∘ exp_transf b d) Y in
          (* we assume renamed apart here, so it's ok to leave definitions
       in d[X <-- Yc] that are /not/ defined at the point where f is defined *)
          let AL := ((fun _ => false) ⊝ ZL) in
          (if b then domjoin_list d Z Yc else d, ann0 b, list_update_at AL (counted f) b)
    | stmtReturn x as st, ann0 b =>
      (d, ann0 b, ((fun _ => false) ⊝ ZL))

    | stmtFun F t as st, annF b rF r =>
        let ZL' := List.map fst F ++ ZL in
        let '(a', r', AL) :=
            @forward D _ _ exp_transf reach_transf ZL'
                     t d (setTopAnn r b) in
        let '(a'', rF', AL') := forwardF AL (forward D _ _ exp_transf reach_transf ZL')
                            F (zip (@joinTopAnn _ _ _) rF AL) a' in
        (a'', annF b (zip (@setTopAnn _) rF' AL') r', drop (length F) AL')
    | _, _ => (d, anr, ((fun _ => false) ⊝ ZL))
      end).
Defined.

Smpl Add 100
     match goal with
     | [ H : context [ ❬list_update_at ?ZL _ _❭ ] |- _ ] =>
       rewrite (list_update_at_length _ ZL) in H
     | [ |- context [ ❬list_update_at ?ZL _ _❭ ] ] =>
       rewrite (list_update_at_length _ ZL)
     end : len.


Lemma forward_length D `{JoinSemiLattice D} f fr ZL s d r
  : ❬snd (forward f fr ZL s d r)❭ = ❬ZL❭.
Proof.
  revert_except s.
  sind s; destruct s, r; simpl; eauto with len;
    repeat let_pair_case_eq; subst; simpl; eauto.
  - len_simpl. rewrite (IH s1), (IH s2); eauto with len.
  - rewrite length_drop_minus.
    erewrite forwardF_snd_length; eauto with len.
    + len_simpl. omega.
Qed.

Lemma forward_fst_snd_getAnn D `{JoinSemiLattice D} f fr ZL s d r
  : getAnn (snd (fst (forward f fr ZL s d r))) = getAnn r.
Proof.
  revert_except s.
  sind s; destruct s, r; simpl; eauto with len;
    repeat let_pair_case_eq; subst; simpl; eauto.
Qed.

Lemma forward_getAnn D `{JoinSemiLattice D} f fr ZL s b r r'
  : ann_R poEq (snd (fst (forward f fr ZL s b r))) r'
    -> getAnn r = getAnn r'.
Proof.
  intros. eapply ann_R_get in H1.
  rewrite forward_fst_snd_getAnn in H1. eauto.
Qed.


Lemma setTopAnn_eta' A (a:ann A)
  : (setTopAnn a (getAnn a)) = a.
Proof.
  destruct a; simpl; eauto.
Qed.

Smpl Add 100
     match goal with
     | [ H : context [ ❬snd (@forward ?D ?PO ?JSL ?f ?fr ?ZL ?s ?d ?r)❭ ] |- _ ] =>
       rewrite (@forward_length D PO JSL f fr ZL s d r) in H
     | [ |- context [ ❬snd (@forward ?D ?PO ?JSL ?f ?fr ?ZL ?s ?d ?r)❭ ] ] =>
       rewrite (@forward_length D PO JSL f fr ZL s d r)
     end : len.

Lemma forwardF_mon (D:Type) `{JoinSemiLattice D} f fr ZL BL (Len:❬BL❭ <= ❬ZL❭)
      (F:list (params * stmt)) rF a
  : PIR2 poLe BL (snd (@forwardF D BL (forward f fr ZL) F rF a)).
Proof.
  revert rF a.
  induction F; intros; destruct rF; simpl; eauto.
  eapply PIR2_impb_orb_left; eauto with len.
Qed.

Lemma forwardF_mon' (D:Type) `{JoinSemiLattice D} f fr ZL (F:list (params * stmt)) rF BL
       (Len:❬F❭ = ❬rF❭) a
  : PIR2 poEq (getAnn ⊝ rF)
         (getAnn ⊝ snd (fst (forwardF BL
                                      (forward f fr ZL) F rF a))).
Proof.
  general induction Len; intros; simpl; eauto.
  econstructor.
  - rewrite forward_fst_snd_getAnn. reflexivity.
  - eapply IHLen.
Qed.

Lemma fold_list_length A B (f:list B -> (list A * bool) -> list B) (a:list (list A * bool)) (b: list B)
  : (forall n aa, get a n aa -> ❬b❭ <= ❬fst aa❭)
    -> (forall aa b, ❬b❭ <= ❬fst aa❭ -> ❬f b aa❭ = ❬b❭)
    -> length (fold_left f a b) = ❬b❭.
Proof.
  intros LEN.
  general induction a; simpl; eauto.
  erewrite IHa; eauto 10 using get with len.
  intros. rewrite H; eauto using get.
Qed.

Lemma fold_list_length' A B (f:list B -> (list A) -> list B) (a:list (list A)) (b: list B)
  : (forall n aa, get a n aa -> ❬b❭ <= ❬aa❭)
    -> (forall aa b, ❬b❭ <= ❬aa❭ -> ❬f b aa❭ = ❬b❭)
    -> length (fold_left f a b) = ❬b❭.
Proof.
  intros LEN.
  general induction a; simpl; eauto.
  erewrite IHa; eauto 10 using get with len.
  intros. rewrite H; eauto using get.
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

Lemma fold_left_join_struct T `{JoinSemiLattice T} (A A':list T) (b b':T)
  : PIR2 poLe A A'
    -> b ⊑ b'
    -> fold_left join A b ⊑ fold_left join A' b'.
Proof.
  intros pir.
  general induction pir; simpl; eauto.
  eapply IHpir.
  eapply join_struct; eauto.
Qed.

Require Import FiniteFixpointIteration.

Lemma option_map_mon T `{PartialOrder T}  U `{PartialOrder U} (a a':option T) (f f': T -> U)
  : a ⊑ a'
    -> (forall x y, x ⊑ y -> f x ⊑ f' y)
    -> option_map f a ⊑ option_map f' a'.
Proof.
  intros A; inv A; simpl;
    clear_trivial_eqs; simpl; eauto using fstNoneOrR.
Qed.

Lemma PIR2_bottom_least A B `{LowerBounded A} (ZL:list B) (l:list A)
  : ❬ZL❭ = ❬l❭
    -> PIR2 poLe (tab (⊥) ‖ZL‖) l.
Proof.
  intros. eapply PIR2_get; intros; inv_get; eauto with len.
  eapply bottom_least.
Qed.

Lemma forwardF_monotone D `{JoinSemiLattice D}
      (forward forward' : stmt -> Dom D -> ann bool -> Dom D * ann bool * 〔bool〕) F
      (fwdMon:forall  n Zs (GET:get F n Zs),
          forall (d d' : Dom D),
            d ⊑ d'
            -> forall (r r':ann bool),
              r ⊑ r'
              -> forward (snd Zs) d r ⊑ forward' (snd Zs) d' r')
  : forall (d d' : Dom D),
      d ⊑ d'
      -> forall (rF rF':list (ann bool)),
        rF ⊑ rF'
        -> forall (BL BL':list bool),
          BL ⊑ BL'
        -> forwardF BL forward F rF d
                   ⊑  forwardF BL' forward' F rF' d'.
Proof.
  intros d d' LE_d rF rF' LE_rf.
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

Lemma PIR2_eq_zip X Y Z (f:X -> Y -> Z) l1 l2 l1' l2'
  : PIR2 eq l1 l1'
    -> PIR2 eq l2 l2'
    -> PIR2 eq (zip f l1 l2) (zip f l1' l2').
Proof.
  intros P1 P2.
  general induction P1; inv P2; simpl; econstructor; eauto.
Qed.

Lemma forwardF_ext D `{JoinSemiLattice D}
      (forward forward' : stmt -> Dom D -> ann bool -> Dom D * ann bool * 〔bool〕) F
      (fwdMon:forall  n Zs (GET:get F n Zs),
          forall (d d' : Dom D),
            poEq d d'
            -> forall (r r':ann bool),
              poEq r r'
              -> poEq (forward (snd Zs) d r) (forward' (snd Zs) d' r'))
  : forall (d d' : Dom D),
      poEq d d'
      -> forall (rF rF':list (ann bool)),
        poEq rF rF'
        -> forall (BL BL':list bool),
          poEq BL BL'
        -> poEq (forwardF BL forward F rF d)
               (forwardF BL' forward' F rF' d').
Proof.
  intros d d' LE_d rF rF' LE_rf.
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

Lemma PIR2_zip_setTopAnnO X `{PartialOrder X} (A A':list (ann X)) (B B':list X)
  : poLe A A'
    -> poLe B B'
    -> poLe ((@setTopAnn _) ⊜ A B) (@setTopAnn _ ⊜ A' B').
Proof.
  intros LE_A LE_B; simpl in *.
  general induction LE_A; inv LE_B; simpl; eauto using PIR2.
  - econstructor; eauto.
    eauto using ann_R_setTopAnn.
Qed.

Lemma ann_poLe_joinTopAnn A `{JoinSemiLattice A} (a:A) (b:A) an bn
  : poLe a b
    -> ann_R poLe an bn
    -> ann_R poLe (joinTopAnn an a) (joinTopAnn bn b).
Proof.
  intros.
  inv H2; simpl; econstructor; try eapply join_struct; eauto.
Qed.

Lemma ann_poEq_joinTopAnn A `{JoinSemiLattice A} (a:A) (b:A) an bn
  : poEq a b
    -> ann_R poEq an bn
    -> ann_R poEq (joinTopAnn an a) (joinTopAnn bn b).
Proof.
  intros.
  inv H2; simpl; econstructor; eauto;
    rewrite H1, H3; reflexivity.
Qed.


Lemma PIR2_zip_joinTopAnnO X `{JoinSemiLattice X} (A A':list (ann X)) (B B':list X)
  : poLe A A'
    -> poLe B B'
    -> poLe ((@joinTopAnn _ _ _) ⊜ A B) (@joinTopAnn _ _ _ ⊜ A' B').
Proof.
  intros LE_A LE_B; simpl in *.
  general induction LE_A; inv LE_B; simpl; eauto using PIR2.
  - econstructor; eauto.
    eauto using ann_poLe_joinTopAnn.
Qed.

Lemma PIR2_poEq_zip_setTopAnnO X `{PartialOrder X} (A A':list (ann X)) (B B':list X)
  : poEq A A'
    -> poEq B B'
    -> poEq ((@setTopAnn _) ⊜ A B) (@setTopAnn _ ⊜ A' B').
Proof.
  intros LE_A LE_B; simpl in *.
  general induction LE_A; inv LE_B; simpl; eauto using PIR2.
  - econstructor; eauto.
    eauto using ann_R_setTopAnn.
Qed.

Lemma PIR2_poEq_zip_joinTopAnnO X `{JoinSemiLattice X} (A A':list (ann X)) (B B':list X)
  : poEq A A'
    -> poEq B B'
    -> poEq ((@joinTopAnn _ _ _) ⊜ A B) (@joinTopAnn _ _ _ ⊜ A' B').
Proof.
  intros LE_A LE_B; simpl in *.
  general induction LE_A; inv LE_B; simpl; eauto using PIR2.
  - econstructor; eauto.
    eauto using ann_poEq_joinTopAnn.
Qed.

Lemma forward_monotone D `{JoinSemiLattice D}
      (f: bool -> DomainSSA.Dom D -> exp -> ؟ D)
      (fr : bool -> Dom D -> op -> bool * bool)
      (fMon: forall e a a', a ⊑ a' -> forall b b', b ⊑ b' -> f b a e ⊑ f b' a' e)
      (frMon:forall e a a',
            a ⊑ a' -> forall b b', b ⊑ b' -> fr b a e ⊑ fr b' a' e)
  : forall (s : stmt) (ZL:list params),
    forall (d d' : Dom D), d ⊑ d'
      -> forall (r r':ann bool), r ⊑ r'
      -> forward f fr ZL s d r ⊑ forward f fr ZL s d' r'.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  sind s; destruct s; intros ZL d d' LE_d r r'  LE_r;
    destruct r; inv LE_r;
      simpl forward; repeat let_pair_case_eq; subst;
        eauto 10 using @ann_R;
        try now (econstructor; simpl; eauto using @ann_R).
  - simpl. pose proof (fMon e  _ _ LE_d _ _ H3); eauto.
    simpl in *. split; dcr; eauto; [split; eauto|]; simpl;
                  eauto 20 using domupd_le, ann_R_setTopAnn, ann_R.
    + eapply IH; eauto using domupd_le, ann_R_setTopAnn.
    + econstructor; eauto. eapply IH; eauto using domupd_le.
      eauto using ann_R_setTopAnn.
    + eapply IH; eauto using domupd_le, ann_R_setTopAnn.
  - pose proof (fMon (Operation e) _ _ LE_d) as LE_f.
    pose proof (frMon e _ _ LE_d) as LE_fr.
    pose proof (IH s1 ltac:(eauto) ZL) as LE1; eauto.
    pose proof (IH s2 ltac:(eauto) ZL) as LE2; eauto.
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
    + eapply forwardF_monotone; eauto.
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
        eapply forwardF_monotone; eauto.
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

Lemma forward_ext D `{JoinSemiLattice D}
      (f: bool -> DomainSSA.Dom D -> exp -> ؟ D)
      (fr : bool -> Dom D -> op -> bool * bool)
      (fMon: forall e a a', a ≣ a' -> forall b b', b ≣ b' -> f b a e ≣ f b' a' e)
      (frMon:forall e a a',
            a ≣ a' -> forall b b', b ≣ b' -> fr b a e ≣ fr b' a' e)
  : forall (s : stmt) (ZL:list params),
    forall (d d' : Dom D), d ≣ d'
      -> forall (r r':ann bool), r ≣ r'
      -> forward f fr ZL s d r ≣ forward f fr ZL s d' r'.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  sind s; destruct s; intros ZL d d' LE_d r r'  LE_r;
    destruct r; inv LE_r;
      simpl forward; repeat let_pair_case_eq; subst;
        eauto 10 using @ann_R;
        try now (econstructor; simpl; eauto using @ann_R).
  - simpl. pose proof (fMon e  _ _ LE_d _ _ H3); eauto.
    simpl in *. split; dcr; eauto; [split; eauto|]; simpl;
                  eauto 20 using domupd_le, ann_R_setTopAnn, ann_R.
    + eapply IH; eauto using domupd_eq, ann_R_setTopAnn.
    + econstructor; eauto. eapply IH; eauto using domupd_eq.
      eauto using ann_R_setTopAnn.
    + eapply IH; eauto using domupd_eq, ann_R_setTopAnn.
  - pose proof (fMon (Operation e) _ _ LE_d) as LE_f.
    pose proof (frMon e _ _ LE_d) as LE_fr.
    pose proof (IH s1 ltac:(eauto) ZL) as LE1; eauto.
    pose proof (IH s2 ltac:(eauto) ZL) as LE2; eauto.
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
    + eapply forwardF_ext; eauto.
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


Lemma forwardF_PIR2  D `{JoinSemiLattice D} BL ZL
      (F:list (params * stmt)) sa a (Len1:❬F❭ = ❬sa❭)
      (Len2:❬BL❭ = ❬ZL❭)
      (f: bool -> DomainSSA.Dom D -> exp -> ؟ D)
      (fr : bool -> Dom D -> op -> bool * bool)
      (EQ: forall n Zs r, get F n Zs -> get sa n r ->
                        poEq (fst (fst (forward f fr ZL (snd Zs) a r))) a)
      (fExt: forall e a a', a ≣ a' -> forall b b', b ≣ b' -> f b a e ≣ f b' a' e)
      (frExt:forall e a a',
            a ≣ a' -> forall b b', b ≣ b' -> fr b a e ≣ fr b' a' e)
      n r Zs (Getsa:get sa n r) (GetF:get F n Zs)
:
  PIR2 impb
       (snd (forward f fr ZL (snd Zs) a r))
       (snd (forwardF BL (forward f fr ZL) F sa a)).
Proof.
  general induction n; isabsurd; simpl.
  - eapply PIR2_impb_orb_right.
    + len_simpl; eauto. intros. eauto with len.
    + reflexivity.
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

Lemma forwardF_get  (sT:stmt) (Dom:stmt->Type) BL ZL
      (F:list (params * stmt)) rF a ZLIncl
      (f : forall (sT : stmt) (ZL : 〔params〕) (s : stmt),
          subTerm s sT ->
          list_union (of_list ⊝ ZL) [<=] occurVars sT
          -> Dom sT -> bool -> Dom sT)
      fr
      (ST:forall n s, get F n s -> subTerm (snd s) sT) n aa
           (GetBW:get (snd (fst (@forwardF Dom BL (@forward sT Dom f fr ZL ZLIncl) F rF a ST))) n aa)
  :
    { Zs : params * stmt &
           {GetF : get F n Zs &
                   { r : ann bool &
                         {GetrF : get rF n r &
                                  { ST' : subTerm (snd Zs) sT &
                                          { ST'' : forall (n0 : nat) (s : params * stmt), get (take n F) n0 s -> subTerm (snd s) sT | aa = snd (fst (forward Dom f fr ZL ZLIncl ST' (fst (fst (@forwardF sT Dom BL (@forward sT Dom f fr ZL ZLIncl) (take n F) (take n rF) a ST''))) r))
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
      intros. inv H; eauto using get.
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

Instance LowerBounded_ann (s:stmt) A `{LowerBounded A}
  : LowerBounded ({ a : ann bool | annotation s a }) :=
  {
    bottom := exist _ (setAnn bottom s) _
  }.
Proof.
  - eapply setAnn_annotation.
  - intros []. simpl.
    general induction a; simpl; eauto using @ann_R.
    + econstructor; eauto with len.
      intros; inv_get. exploit H1; eauto.
Defined.


Lemma forward_annotation Dom sT s (ST:subTerm s sT)
      (f:forall (sT : stmt) (ZL : 〔params〕) (s : stmt),
          subTerm s sT ->
          list_union (of_list ⊝ ZL) [<=] occurVars sT -> Dom sT -> bool -> Dom sT)
      fr
      ZL ZLIncl d r
      (AN:annotation s r)
  : annotation s (snd (fst (forward Dom f fr ZL ZLIncl ST d r))).
Proof.
  revert ST ZL ZLIncl d r AN.
  sind s; intros; invt @annotation; simpl;
    repeat let_pair_case_eq; subst; simpl;
      eauto 20 using @annotation, setTopAnn_annotation.
  - econstructor; eauto 20 using setTopAnn_annotation.
    + len_simpl; try reflexivity.
      rewrite H.
      rewrite !min_l; eauto with len.
      rewrite !min_l; eauto with len.
      rewrite !min_l; eauto with len.
      rewrite !min_l; eauto with len.
      eauto with len.
    + intros; inv_get.
      eapply setTopAnn_annotation; eauto.
      eapply forwardF_get in H4. destruct H4; dcr; subst.
      inv_get. eapply IH; eauto.
      eapply setTopAnn_annotation; eauto.
Qed.


Instance makeForwardAnalysis (Dom:stmt -> Type)
         {PO:forall s, PartialOrder (Dom s)}
         (BSL:forall s, JoinSemiLattice (Dom s))
         (LB: forall s, @LowerBounded (Dom s) (PO s))
         (f: forall (sT : stmt) (ZL : 〔params〕) (s : stmt),
             subTerm s sT ->
             list_union (of_list ⊝ ZL) [<=] occurVars sT -> Dom sT -> bool -> Dom sT)
         (fr:forall (sT : stmt) (e : op),
             Op.freeVars e [<=] occurVars sT -> Dom sT -> bool -> bool * bool)
         (fMon:forall sT s (ST:subTerm s sT) ZL
                 (ZLIncl:list_union (of_list ⊝ ZL) [<=] occurVars sT),
             forall a b, a ⊑ b ->
                    forall r r', r ⊑ r' ->
                            f sT ZL s ST ZLIncl a r ⊑ f sT ZL s ST ZLIncl b r')
         (frMon:forall sT e s (ST:subTerm s sT) FVIncl,
          forall a a',
            a ⊑ a' -> forall b b', b ⊑ b' -> fr sT e FVIncl a b ⊑ fr sT e FVIncl a' b')
         (Trm: forall s, Terminating (Dom s) poLt)

  : forall s, Iteration (Dom s * { a : ann bool | annotation s a }) :=
  {
    step := fun dr =>
             let a := forward Dom f fr nil (incl_empty _ (occurVars s)) (subTerm_refl s)
                             (fst dr) (proj1_sig (snd dr)) in
             (fst (fst a), exist (fun a => annotation s a) (snd (fst a)) _);
    initial_value := bottom
  }.

Proof.
  - subst a.
    eapply forward_annotation; eauto.
    eapply (proj2_sig (snd dr)).
  - eapply s.
  - eapply bottom_least.
  - eapply terminating_pair; eauto.
    eapply terminating_sig; eauto.
    eapply terminating_ann.
    eapply terminating_bool.
  - hnf; intros.
    eapply (forward_monotone Dom f fr (fMon s) (frMon s)); eauto.
    eapply H. eapply H.
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

Lemma snd_forwardF_inv Dom sT f fr BL ZL ZLIncl F sa AE STF
      (P1:PIR2 (ann_R eq)
               (setTopAnn (A:=bool)
                          ⊜ (snd (fst (forwardF BL (@forward sT Dom f fr ZL ZLIncl) F
                                                (joinTopAnn (A:=bool) ⊜ sa BL) AE STF)))
                          (snd (forwardF BL
                                         (@forward _ _ f fr ZL ZLIncl) F
                                         (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa)
      (Len1:❬F❭ = ❬sa❭) (Len2:❬F❭ <= ❬BL❭) (Len3:❬ZL❭ = ❬BL❭)
  : PIR2 (ann_R eq) (joinTopAnn (A:=bool) ⊜ sa BL) sa.
Proof.
  eapply PIR2_ann_R_get in P1.
  rewrite getAnn_setTopAnn_zip in P1.
  pose proof (PIR2_joinTopAnn_zip_left sa BL).
  eapply H; clear H.
  etransitivity.
  eapply PIR2_take.
  eapply (@forwardF_mon sT _ f fr ZL ZLIncl BL ltac:(omega) F (joinTopAnn (A:=bool) ⊜ sa BL) AE STF).
  etransitivity. Focus 2.
  eapply PIR2_R_impl; try eapply P1; eauto.
  assert (❬sa❭ = (Init.Nat.min
          ❬snd
             (fst
                (forwardF BL (@forward _ _ f fr ZL ZLIncl) F
                   (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))❭
          ❬snd
             (forwardF BL (@forward _ _ f fr ZL ZLIncl) F (joinTopAnn (A:=bool) ⊜ sa BL)
                       AE STF)❭)). {
    clear P1.
    rewrite forwardF_length.
    erewrite forwardF_snd_length; try reflexivity.
    + repeat rewrite min_l; eauto; len_simpl;
        rewrite Len1; rewrite min_l; omega.
    + intros; len_simpl; eauto.
  }
  rewrite H. reflexivity.
Qed.

Lemma snd_forwardF_inv' Dom sT f fr BL ZL ZLIncl F sa AE STF
      (P1:PIR2 (ann_R eq)
               (setTopAnn (A:=bool)
                          ⊜ (snd (fst (forwardF BL (@forward Dom sT f fr ZL ZLIncl) F
                                                (joinTopAnn (A:=bool) ⊜ sa BL) AE STF)))
                          (snd (forwardF BL
                                         (@forward _ _ f fr ZL ZLIncl) F
                                         (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa)
      (Len1:❬F❭ = ❬sa❭) (Len2:❬F❭ <= ❬BL❭) (Len3:❬ZL❭ = ❬BL❭)
  : PIR2 (ann_R eq)
              (snd (fst (forwardF BL (@forward Dom sT f fr ZL ZLIncl) F
                                                (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa.
Proof.
  assert (P2:PIR2 poLe (Take.take ❬sa❭
                               (snd (forwardF BL (@forward _ _ f fr ZL ZLIncl) F
                                              (joinTopAnn (A:=bool) ⊜ sa BL) AE
                                              STF))) (getAnn ⊝ sa)). {
    eapply PIR2_ann_R_get in P1.
    rewrite getAnn_setTopAnn_zip in P1.
     etransitivity. Focus 2.
    eapply PIR2_R_impl; try eapply P1; eauto.
    assert (❬sa❭ = (Init.Nat.min
                      ❬snd
                         (fst
                            (forwardF BL (@forward _ _ f fr ZL ZLIncl) F
                                      (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))❭
                      ❬snd
                         (forwardF BL (@forward _ _ f fr ZL ZLIncl) F (joinTopAnn (A:=bool) ⊜ sa BL)
                                   AE STF)❭)). {
      clear P1.
      rewrite forwardF_length.
      erewrite forwardF_snd_length; try reflexivity.
      + repeat rewrite min_l; eauto; len_simpl;
          rewrite Len1; rewrite min_l; omega.
      + intros; len_simpl; eauto.
    }
    rewrite H. reflexivity.
  }
  assert (PIR2 (ann_R eq) (joinTopAnn (A:=bool) ⊜ sa BL) sa). {
    pose proof (PIR2_joinTopAnn_zip_left sa BL).
    eapply H; clear H.
    etransitivity.
    eapply PIR2_take.
    eapply (@forwardF_mon Dom sT f fr ZL ZLIncl BL ltac:(omega) F (joinTopAnn (A:=bool) ⊜ sa BL) AE STF). eauto.
  }
  etransitivity; try eapply P1.
  symmetry.
  eapply (PIR2_setTopAnn_zip_left); eauto.
  rewrite <- forwardF_mon';[|len_simpl; rewrite min_l; eauto; omega].
  - len_simpl. rewrite min_r, min_l; eauto; try rewrite Len1; try rewrite min_l; try omega.
    eapply PIR2_ann_R_get in H.
    rewrite H.
    eapply PIR2_ann_R_get in P1.
    etransitivity; try eapply P1.
    eapply PIR2_get; intros; inv_get.
    rewrite getAnn_setTopAnn; eauto.
    len_simpl;[| | reflexivity].
    rewrite min_r; try omega.
    repeat rewrite min_l; try omega.
    intros; eauto with len.
Qed.



Lemma snd_forwardF_inv_get (Dom:stmt -> Type) sT `{PartialOrder (Dom sT)} f fr BL ZL ZLIncl F sa AE STF
      (Len1:❬F❭ = ❬sa❭) (Len2:❬F❭ <= ❬BL❭) (Len3:❬ZL❭ = ❬BL❭)
      (P1:PIR2 (ann_R eq)
               (snd (fst (forwardF BL (@forward sT Dom f fr ZL ZLIncl) F
                                  (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) sa)
      (P2:PIR2 (ann_R eq) (joinTopAnn (A:=bool) ⊜ sa BL) sa)
      (EQ: forall n Zs r ST, get F n Zs -> get sa n r ->
                        poEq (fst (fst (@forward sT Dom f fr ZL ZLIncl (snd Zs) ST AE r))) AE)
      (fExt: forall (s : stmt) (ST0 : subTerm s sT) (ZL0 : 〔params〕)
               (ZLIncl0 : list_union (of_list ⊝ ZL0) [<=] occurVars sT)
               (a a' : Dom sT),
          a ≣ a' ->
          forall b b' : bool,
            b ≣ b' -> f sT ZL0 s ST0 ZLIncl0 a b ≣ f sT ZL0 s ST0 ZLIncl0 a' b')
      (frExt:  forall (e : op) (s : stmt),
          subTerm s sT ->
          forall (FVIncl : Op.freeVars e [<=] occurVars sT) (a a' : Dom sT),
            a ≣ a' -> forall b b' : bool, b ≣ b' -> fr sT e FVIncl a b ≣ fr sT e FVIncl a' b')
      n r Zs (Getsa:get sa n r)
      (GetF:get F n Zs) STZs
  : ann_R eq (snd (fst (@forward _ _ f fr ZL ZLIncl (snd Zs) STZs AE r))) r.
Proof.
  rewrite forwardF_ext in P1; try eapply P2; try reflexivity.
  Focus 2. intros. eapply forward_ext; eauto.
  clear Len3 P2.
  general induction Len1; simpl in *.
  destruct BL; isabsurd; simpl in *. inv Getsa; inv GetF.
  - inv P1.
    assert((STF 0 Zs (@getLB (params * stmt) XL Zs)) = STZs).
    eapply subTerm_PI. rewrite <- H0.
    eapply pf.
  - inv P1.
    eapply IHLen1; eauto using get.
    Focus 2.
    rewrite forwardF_ext; eauto.
    intros. eapply forward_ext; eauto.
    symmetry. eapply EQ; eauto using get. reflexivity. simpl. omega.
Qed.
