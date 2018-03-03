Require Import CSet Le ListUpdateAt Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Terminating MoreInversion.
Require Import Val Var Envs IL Annotation Infra.Lattice AnnotationLattice.
Require Import DecSolve LengthEq MoreList Status AllInRel OptionR MapDefined.
Require Import Keep Subterm Analysis CMapPartialOrder DomainSSA CMapTerminating.
Require Import RenamedApart Take WithTop.

Set Implicit Arguments.

Arguments poLe : simpl never.
Arguments poEq : simpl never.
Arguments bottom : simpl never.
Arguments comp X Y Z f g / x.

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
          let AL := ((fun _ => bottom) ⊝ ZL) in
          (if b then domjoin_listd d Z Yc (ZLIncl_App_Z (counted f) ZLIncl) else d, ann0 b, list_update_at AL (counted f) b)
      | stmtReturn x as st, ann0 b =>
        fun EQ =>
          (d, ann0 b, ((fun _ => bottom) ⊝ ZL))
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
      | _, _ => fun _ => (d, anr, ((fun _ => bottom) ⊝ ZL))
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
  : (snd (fst (forward f fr ZL ZLIncl ST b r))) ≣ r'
    -> getAnn r = getAnn r'.
Proof.
  intros. eapply ann_R_get in H1.
  rewrite forward_fst_snd_getAnn in H1. eauto.
Qed.



Lemma forwardF_mon sT (D:Type) `{JoinSemiLattice D} f fr ZL ZLIncl BL
      (Len:❬BL❭ <= ❬ZL❭)
      (F:list (params * stmt)) STF rF a
  : poLe BL (snd (@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) F rF a STF)).
Proof.
  revert rF a.
  induction F; intros; destruct rF; simpl; inv_cleanup; eauto with len.
Qed.


Lemma forwardF_mon' sT (D:Type) `{JoinSemiLattice D}
      f fr ZL ZLIncl (F:list (params * stmt)) rF BL STF
       (Len:❬F❭ = ❬rF❭) a
  : PIR2 poEq (getAnn ⊝ rF)
         (getAnn ⊝ snd (fst (@forwardF sT (sTDom D) BL
                                       (forward f fr ZL ZLIncl) F rF a STF))).
Proof.
  general induction Len; intros; simpl; eauto with len.
  econstructor.
  - setoid_rewrite forward_fst_snd_getAnn. reflexivity.
  - eauto.
Qed.

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
  general induction F; intros; inv LE_rf; simpl; eauto; inv_cleanup;
    eauto 50 using get.
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
  general induction F; intros; inv LE_rf; simpl; eauto 100 using get.
Qed.


Lemma forward_monotone sT D `{JoinSemiLattice D}
      (f: forall U : ⦃var⦄, bool -> VDom U D -> exp -> ؟ D)
      (fr: forall U : ⦃var⦄, bool -> VDom U D -> op -> bool * bool)
      (fMon: forall U e (a a':VDom U D), a ⊑ a' -> forall b b', b ⊑ b' -> f _ b a e ⊑ f _ b' a' e)
      (frMon:forall U e (a a':VDom U D),
            a ⊑ a' -> forall b b', b ⊑ b' -> fr _ b a e ⊑ fr _ b' a' e)
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) ZLIncl,
    forall (d d' : VDom (occurVars sT) D), d ⊑ d'
      -> forall (r r':ann bool), r ⊑ r'
      -> forward f fr ZL ZLIncl ST d r ⊑ forward f fr ZL ZLIncl ST d' r'.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  induction s using stmt_ind'; intros ST ZL ZLIncl d d' LE_d r r'  LE_r;
    destruct r; inv LE_r;
      simpl forward; repeat let_pair_case_eq; subst; eauto; inv_cleanup.
  - eauto 100.
  - eauto 100.
  - eapply poLe_struct.
    + eapply poLe_struct; eauto.
      repeat (cases; eauto; simpl in *).
      * eapply poLe_sig_struct.
        eapply domjoin_list_le; eauto.
        eapply poLe_map_nd; eauto.
      * etransitivity; eauto.
        eapply domjoin_list_exp.
    + eapply update_at_poLe; eauto.
  - eapply PIR2_get in H8; eauto.
    eauto 100 using forwardF_monotone.
Qed.

Lemma forward_ext sT D `{JoinSemiLattice D}
      (f: forall U : ⦃var⦄, bool -> VDom U D -> exp -> ؟ D)
      (fr: forall U : ⦃var⦄, bool -> VDom U D -> op -> bool * bool)
      (fMon: forall U e (a a':VDom U D), a ≣ a' -> forall b b', b ≣ b' -> f _ b a e ≣ f _ b' a' e)
      (frMon:forall U e (a a':VDom U D),
            a ≣ a' -> forall b b', b ≣ b' -> fr _ b a e ≣ fr _ b' a' e)
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) ZLIncl,
    forall (d d' : VDom (occurVars sT) D), d ≣ d'
      -> forall (r r':ann bool), r ≣ r'
      -> forward f fr ZL ZLIncl ST d r ≣ forward f fr ZL ZLIncl ST d' r'.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  induction s using stmt_ind'; intros ST ZL ZLIncl d d' LE_d r r'  LE_r;
    destruct r; inv LE_r;
      simpl forward; repeat let_pair_case_eq; subst; inv_cleanup;
        eauto 10.
  - eauto 100.
  - eauto 100 using orb_poEq_proper.
  - split; [split|]; simpl; eauto 20.
    + repeat (cases; eauto; simpl in *).
      eapply poEq_sig_struct.
      eapply domjoin_list_eq; eauto.
      eapply poEq_map_nd; eauto.
  - eapply PIR2_get in H8; eauto.
    eauto 100 using forwardF_ext.
Qed.

Lemma forwardF_ext' sT D `{JoinSemiLattice D}
      (f:forall U : ⦃var⦄, bool -> VDom U D -> exp -> ؟ D)
      (fr:forall U : ⦃var⦄, bool -> VDom U D -> op -> bool * bool) F ZL ZLIncl
      (fMon: forall U e (a a':VDom U D), a ≣ a' -> forall b b', b ≣ b' -> f U b a e ≣ f U b' a' e)
      (frMon:forall U e (a a':VDom U D),
          a ≣ a' -> forall b b', b ≣ b' -> fr U b a e ≣ fr U b' a' e)
  : forall (ST:forall (n : nat) (s : params * stmt), get F n s -> subTerm (snd s) sT)
      (d d':VDom (occurVars sT) D), poEq d d'
                       -> forall (rF rF':list (ann bool)),
                    poEq rF rF'
                    -> forall (BL BL':list bool),
                      poEq BL BL'
                      -> poEq (@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) F rF d ST)
                             (forwardF BL' (forward f fr ZL ZLIncl) F rF' d' ST).
Proof.
  intros.
  eapply forwardF_ext; eauto.
  intros.
  eapply forward_ext; eauto.
Qed.

Lemma forwardF_PIR2 sT D `{JoinSemiLattice D} BL ZL ZLIncl
      (F:list (params * stmt)) sa a (Len1:❬F❭ = ❬sa❭)
      (Len2:❬BL❭ = ❬ZL❭)
      (f: forall U : ⦃var⦄, bool -> VDom U D -> exp -> ؟ D)
      (fr: forall U : ⦃var⦄, bool -> VDom U D -> op -> bool * bool)
      (EQ: forall n Zs r (ST:subTerm (snd Zs) sT), get F n Zs -> get sa n r ->
                        poEq (fst (fst (forward f fr ZL ZLIncl ST a r))) a)
      (fExt: forall U e (a a':VDom U D), a ≣ a' -> forall b b', b ≣ b' -> f _ b a e ≣ f _ b' a' e)
      (frExt:forall U e (a a':VDom U D),
            a ≣ a' -> forall b b', b ≣ b' -> fr _ b a e ≣ fr _ b' a' e)
      n r Zs (ST:subTerm (snd Zs) sT) (Getsa:get sa n r) (GetF:get F n Zs) STF
:
  poLe
       (snd (forward f fr ZL ZLIncl ST a r))
       (snd (@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) F sa a STF)).
Proof.
  general induction n; isabsurd; simpl; inv_cleanup.
  - eapply PIR2_poLe_join_right; eauto with len.
    + assert (ST = (STF 0 Zs (getLB xl Zs))).
      eapply subTerm_PI. subst. reflexivity.
  - inv Getsa; inv GetF. simpl; inv_cleanup.
    eapply PIR2_poLe_join_left; eauto with len.
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
    pose ((fun n1 s => match n1 with
                       | 0 => fun GET => (@ST 0 s ltac:(inv GET; eauto using get))
                       | S n => fun GET => (x3 n s ltac:(inv GET; eauto))
                       end):forall (n1 : nat) (s : params * stmt),
             get (p::take n F) n1 s -> subTerm (snd s) sT) as XX.
    assert (STEQ1:(ST 0 p (getLB F p) = (XX 0 p (getLB (take n F) p)))) by reflexivity.
    assert (STEQ2:x3 =
            (fun (n' : nat) (Zs : params * stmt) (H1 : get (take n F) n' Zs) =>
               XX (S n') Zs (getLS p H1))) by reflexivity.
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

Class UpperBounded (A : Type) `{PartialOrder A} :=
  {
    top : A;
    top_greatest : forall a, poLe a top;
  }.

Arguments UpperBounded A {H}.

Lemma snd_forwardF_inv (sT:stmt) D `{JoinSemiLattice D} f fr BL ZL ZLIncl F sa AE STF
      (P1: (setTopAnn (A:=bool)
                      ⊜ (snd (fst (@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) F
                                             (joinTopAnn (A:=bool) ⊜ sa BL) AE STF)))
                      (snd (forwardF BL
                                     (forward f fr ZL ZLIncl) F
                                     (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) ≣ sa)
      (Len1:❬F❭ = ❬sa❭) (Len2:❬F❭ <= ❬BL❭) (Len3:❬ZL❭ = ❬BL❭)
  : (joinTopAnn (A:=bool) ⊜ sa BL) ≣ sa.
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
      (f: forall U : ⦃var⦄, bool -> VDom U D -> exp -> ؟ D)
      (fr: forall U : ⦃var⦄, bool -> VDom U D -> op -> bool * bool)
      BL ZL ZLIncl F sa AE STF
      (P1: (setTopAnn (A:=bool)
                      ⊜ (snd (fst (forwardF BL (forward f fr ZL ZLIncl) F
                                            (joinTopAnn (A:=bool) ⊜ sa BL) AE STF)))
                      (snd (forwardF BL
                                     (forward f fr ZL ZLIncl) F
                                     (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) ≣ sa)
      (Len1:❬F❭ = ❬sa❭) (Len2:❬F❭ <= ❬BL❭) (Len3:❬ZL❭ = ❬BL❭)
  : (snd (fst (@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) F
                         (joinTopAnn (A:=bool) ⊜ sa BL) AE STF))) ≣ sa.
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
      (P1:(snd (fst (@forwardF sT (sTDom D)  BL (forward f fr ZL ZLIncl) F
                               sa AE STF))) ≣ sa)
      (EQ: forall n Zs r (ST:subTerm (snd Zs) sT), get F n Zs -> get sa n r ->
                        poEq (fst (fst (forward f fr ZL ZLIncl ST AE r))) AE)
      (fExt: forall U e (a a':VDom U D), a ≣ a' -> forall b b', b ≣ b' -> f _ b a e ≣ f _ b' a' e)
      (frExt:forall U e (a a':VDom U D),
          a ≣ a' -> forall b b', b ≣ b' -> fr _ b a e ≣ fr _ b' a' e)
      n r Zs (Getsa:get sa n r)
      (GetF:get F n Zs) (STZs:subTerm (snd Zs) sT)
  : (snd (fst (forward f fr ZL ZLIncl STZs AE r))) ≣ r.
Proof.
  general induction Len1; simpl in *.
  destruct BL; isabsurd; simpl in *. inv Getsa; inv GetF.
  - assert((STF 0 Zs (@getLB (params * stmt) XL Zs)) = STZs).
    eapply subTerm_PI. rewrite <- H1.
    eapply pf.
  - eapply IHLen1; try eassumption.
    Focus 3.
    rewrite forwardF_ext'; eauto.
    symmetry. eapply EQ; eauto using get. reflexivity.
    simpl. omega.
    eauto using get.
    eauto using get.
Qed.

Local Notation "'getD' X" := (proj1_sig (fst (fst X))) (at level 10, X at level 0).


Lemma forwardF_agree (sT:stmt) D `{JoinSemiLattice D}
      (BL:list bool) (G:set var) (F:list (params * stmt)) f fr anF ZL'
      (ZL'Incl: list_union (of_list ⊝ ZL') [<=] occurVars sT)
      (Len1:❬F❭ = ❬anF❭)
      (AN:forall (n : nat) (Zs : params * stmt) (sa:ann bool),
          get anF n sa -> get F n Zs -> annotation (snd Zs) sa)
      (AE:VDom (occurVars sT) D)
      (ST: forall (n : nat) (s : params * stmt), get F n s -> subTerm (snd s) sT)
      (IH:forall (n : nat) (Zs : params * stmt),
          get F n Zs ->
          forall (ZL : 〔params〕) AE (G : ⦃var⦄)
            (ST : subTerm (snd Zs) sT)
            (ZLIncl : list_union (of_list ⊝ ZL) [<=] occurVars sT)
            (anr : ann bool),
            annotation (snd Zs) anr ->
            agree_on (option_R poEq)
                     (G \ (definedVars (snd Zs) ∪ list_union (of_list ⊝ ZL)))
                     (domenv (proj1_sig AE))
                     (domenv (getD
                                (forward f fr ZL ZLIncl ST AE anr))) /\
            agree_on (fstNoneOrR poLe) (G \ definedVars (snd Zs))
                     (domenv (proj1_sig AE))
                     (domenv (getD
                                (forward f fr ZL ZLIncl ST AE anr))))
  : agree_on (option_R poEq)
             (G \ (list_union (defVars' ⊝ F) ∪ list_union (of_list ⊝ ZL')))
             (domenv (proj1_sig AE))
             (domenv (getD (@forwardF sT (sTDom D) BL (forward f fr _ ZL'Incl)
                                      F anF AE ST))) /\
    agree_on (fstNoneOrR poLe)
             (G \ list_union (definedVars ⊝ (snd ⊝ F)))
             (domenv (proj1_sig AE))
             (domenv (getD (@forwardF sT (sTDom D) BL (forward f fr _ ZL'Incl)
                                      F anF AE ST))).
Proof.
  general induction Len1; simpl.
  - split; reflexivity.
  - edestruct (IHLen1 sT D _ _ BL G f fr ZL');
      edestruct (IH 0 x ltac:(eauto using get) ZL' AE G ltac:(eauto using get) ZL'Incl); eauto using get.
    simpl; split; etransitivity; eapply agree_on_incl; eauto.
    + norm_lunion. clear_all. unfold defVars' at 1. cset_tac.
    + norm_lunion. clear_all. cset_tac.
    + norm_lunion. clear_all. cset_tac.
    + norm_lunion. unfold defVars'. clear_all. cset_tac.
Qed.


Lemma forward_agree sT D `{JoinSemiLattice D} f fr
      ZL AE G s (ST:subTerm s sT) ZLIncl anr
      (AN:annotation s anr)
  : agree_on poEq (G \ (definedVars s ∪ list_union (of_list ⊝ ZL)))
             (domenv (proj1_sig AE))
             (domenv (proj1_sig
                        (fst (fst (forward f fr ZL ZLIncl
                                            ST AE anr))))) /\
    agree_on poLe (G \ definedVars s)
             (domenv (proj1_sig AE))
             (domenv (proj1_sig
                        (fst (fst (forward f fr ZL ZLIncl
                                            ST AE anr))))).
Proof.
  revert anr AE G ST ZL ZLIncl AN.
  sind s; destruct s; intros; invt @annotation; intros; simpl in *.
  - destruct e;
      repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
        pe_rewrite; set_simpl.
    + edestruct (IH s ltac:(eauto) (setTopAnn sa a)); clear IH; dcr; try split;
        eauto using setTopAnn_annotation.
      * etransitivity; [|eapply agree_on_incl; eauto]; simpl.
        eapply domupd_dead. cset_tac.
        cset_tac.
        cset_tac.
      * simpl in *.
        eapply agree_on_option_R_fstNoneOrR with (R:=poLe); [|eapply agree_on_incl; eauto|].
        -- eapply domupd_dead; eauto. cset_tac.
        -- cset_tac.
        -- intros. etransitivity; eauto.
    + edestruct (IH s ltac:(eauto) (setTopAnn sa a)); clear IH; dcr; try split;
        eauto using setTopAnn_annotation.
      * etransitivity; [|eapply agree_on_incl; eauto]; simpl.
        simpl in *.
        eapply domupd_dead. cset_tac.
        cset_tac. cset_tac.
      * simpl in *.
        eapply agree_on_option_R_fstNoneOrR with (R:=poLe); [|eapply agree_on_incl; eauto|].
        eapply domupd_dead. cset_tac. cset_tac. cset_tac.
        intros. etransitivity; eauto.
  - repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
      pe_rewrite; set_simpl.
    split.
    + symmetry; etransitivity; symmetry.
      * eapply agree_on_incl.
        -- eapply IH; eauto.
           eapply setTopAnn_annotation; eauto.
        -- cset_tac.
      * symmetry; etransitivity; symmetry.
        -- eapply agree_on_incl. eapply IH; eauto.
           eapply setTopAnn_annotation; eauto.
           cset_tac.
        -- simpl. reflexivity.
    +
      edestruct @IH with (ZL:=ZL)
                              (G:=G)
                              (ST:= (@subTerm_EQ_If1 sT (stmtIf e s1 s2) e s1 s2
                                                     (@eq_refl stmt
                                                               (stmtIf e s1 s2)) ST)) (ZLIncl:=ZLIncl);
        [eauto| |etransitivity;[ eapply agree_on_incl; eauto |eapply agree_on_incl;[eapply IH|]]];
        try eapply setTopAnn_annotation; eauto; cset_tac.
  - set_simpl. unfold domjoin_listd.
    destruct (get_dec ZL l); dcr.
    + cases; eauto; simpl.
      * erewrite get_nth; eauto.
        split.
        eapply agree_on_incl.
        eapply domupd_list_agree; eauto.
        -- rewrite <- incl_list_union; eauto.
           cset_tac. reflexivity.
        -- eapply agree_on_incl.
           eapply domupd_list_agree_poLe; eauto. reflexivity.
      * split; reflexivity.
    + cases; try (split; reflexivity).
      simpl.
      rewrite !not_get_nth_default; eauto.
      split; simpl; reflexivity.
  - split; reflexivity.
  - repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
      pe_rewrite; set_simpl.
    edestruct (IH s ltac:(eauto)) with (ZL:=fst ⊝ F ++ ZL) (anr:=(setTopAnn ta a)); eauto using setTopAnn_annotation.
    rewrite List.map_app in *.
    rewrite list_union_app in *; eauto.
    rewrite list_union_definedVars.
    split.
    + etransitivity.
      * eapply agree_on_incl; eauto.
        clear_all; cset_tac.
      * eapply agree_on_incl.
        eapply forwardF_agree with (ZL':=fst ⊝ F ++ ZL); eauto.
        -- len_simpl. rewrite H3. eauto with len.
        -- intros. inv_get.
           eapply setTopAnn_annotation; eauto.
        -- rewrite List.map_app.
           rewrite list_union_app; eauto.
           instantiate (1:=G).
           rewrite list_union_definedVars'.
           clear_all; cset_tac.
    + etransitivity.
      * eapply agree_on_incl; eauto.
        clear_all; cset_tac.
      * eapply agree_on_incl.
        eapply forwardF_agree with (ZL':=fst ⊝ F ++ ZL); eauto.
        -- len_simpl. rewrite H3. eauto with len.
        -- intros. inv_get.
           eapply setTopAnn_annotation; eauto.
        -- instantiate (1:=G).
           clear_all; cset_tac.
Qed.



Instance makeForwardAnalysis D
         {PO:PartialOrder D}
         (BSL:JoinSemiLattice D) (UB:UpperBounded D)
         (f: forall U : ⦃var⦄, bool -> VDom U D -> exp -> ؟ D)
         (fr: forall U : ⦃var⦄, bool -> VDom U D -> op -> bool * bool)
         (fMon: forall U e (a a':VDom U D), a ⊑ a' -> forall b b', b ⊑ b' -> f _ b a e ⊑ f _ b' a' e)
         (frMon:forall U e (a a':VDom U D),
             a ⊑ a' -> forall b b', b ⊑ b' -> fr _ b a e ⊑ fr _ b' a' e)
         (Trm: Terminating D poLt)
         (s : stmt) ra (RA:renamedApart s ra)
  : Iteration (VDom (occurVars s) D * { a : ann bool | annotation s a }) :=
  {
    step := fun dr =>
             let a := forward f fr nil (incl_empty _ (occurVars s)) (subTerm_refl s)
                             (fst dr) (proj1_sig (snd dr)) in
             (fst (fst a), exist (fun a => annotation s a) (snd (fst a)) _);
  }.
Proof.
  - subst a.
    eapply forward_annotation; eauto.
    eapply (proj2_sig (snd dr)).
  - refine (domjoin_listd bottom (to_list (freeVars s))
                          ((fun _ => Some top) ⊝ (to_list (freeVars s))) _,
            exist _ (@setTopAnn bool (setAnn bottom s) true) _).
    + abstract (rewrite of_list_3;
      rewrite occurVars_freeVars_definedVars; eauto with cset).
    + abstract (eapply setTopAnn_annotation; eapply setAnn_annotation).
  - simpl. split; simpl.
    + eapply domjoin_list_poLe_left.
      * eapply poLe_sig_destruct.
        eapply bottom_least.
      * intros. inv_get.
        edestruct forward_agree with (G:=singleton x); eauto.
        Focus 2.
        -- rewrite <- (H1 x); eauto. simpl.
           rewrite domjoin_list_get; eauto.
           eapply nodup_to_list_eq.
           rewrite renamedApart_occurVars; eauto.
           eapply get_elements_in in H.
           rewrite renamedApart_freeVars in H; eauto.
           eapply renamedApart_disj in RA. cset_tac.
        -- abstract (eapply setTopAnn_annotation; eapply setAnn_annotation).
    + eapply poLe_sig_struct.
      eapply ann_R_setTopAnn_left.
      * rewrite forward_fst_snd_getAnn.
        rewrite getAnn_setTopAnn. reflexivity.
      * eapply ann_bottom. eapply forward_annotation.
        eapply setTopAnn_annotation; eapply setAnn_annotation.
  - hnf; intros. simpl.
    eapply (forward_monotone f fr fMon frMon); eauto.
Defined.


Lemma makeForwardAnalysisSSA_init_env D
         {PO:PartialOrder D}
         (BSL:JoinSemiLattice D) (UB:UpperBounded D)
         (f: forall U : ⦃var⦄, bool -> VDom U D -> exp -> ؟ D)
         (fr: forall U : ⦃var⦄, bool -> VDom U D -> op -> bool * bool)
         (fMon: forall U e (a a':VDom U D), a ⊑ a' -> forall b b', b ⊑ b' -> f _ b a e ⊑ f _ b' a' e)
         (frMon:forall U e (a a':VDom U D),
             a ⊑ a' -> forall b b', b ⊑ b' -> fr _ b a e ⊑ fr _ b' a' e)
         (Trm: Terminating D poLt)
         (s : stmt) ra (RA:renamedApart s ra)
      (x : var)
      (IN : x \In freeVars s)
  : MapInterface.find x
         (proj1_sig
            (fst
               (proj1_sig
                  (safeFixpoint
                     (makeForwardAnalysis D _ _
                                           f fr fMon frMon
                                          Trm s ra RA))))) ===
         ⎣ top ⎦.
Proof.
  eapply safeFixpoint_induction.
  - simpl.
    rewrite <- of_list_3 in IN.
    eapply of_list_get_first in IN; dcr.
    rewrite H0 in *. clear H0.
    exploit (@domupd_list_get_first D _ _ bottom _ (tab ⎣ top ⎦ ‖to_list (freeVars s)‖) _ _ (Some top) H).
    + eapply map_get_eq; eauto.
    + eauto.
    + eapply poLe_antisymmetric; eauto.
      hnf in H0. inv H0. setoid_rewrite <- H3.
      econstructor. eapply top_greatest.
  - intros. destruct a as [? [? ?]].
    simpl.
    edestruct (@forward_agree s D _ _ f fr nil v (singleton x));
      eauto.
    unfold domenv in *.
    exploit (H1 x).
    + exploit renamedApart_disj; eauto.
      rewrite <- renamedApart_occurVars in H3; eauto.
      rewrite <- renamedApart_freeVars in H3; eauto. simpl.
      revert H3 IN. clear_all. cset_tac.
    + simpl in *.
      setoid_rewrite H0 in H3. symmetry; eauto.
Qed.
