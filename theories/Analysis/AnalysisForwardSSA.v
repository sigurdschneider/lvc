Require Import CSet Le ListUpdateAt Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Terminating MoreInversion.
Require Import Val Var Env IL Annotation Infra.Lattice.
Require Import DecSolve LengthEq MoreList Status AllInRel OptionR.
Require Import Keep Subterm Analysis.

Set Implicit Arguments.


Definition anni A (s:stmt) : Type :=
  match s with
  | stmtIf _ _ _ => (bool * bool * A)
  | _ => A
  end.

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

Lemma anni_let A
      (st : stmt) (x : nat) (e : exp) (s : stmt)
      (EQ:st = stmtLet x e s) (d:anni A st) : A.
Proof.
  rewrite EQ in d. simpl in *. eauto.
Defined.

Lemma anni_if A
      (st : stmt) (e : op) (s t : stmt)
      (EQ:st = stmtIf e s t) (d:anni A st) : (bool * bool * A).
Proof.
  rewrite EQ in d. simpl in *. eauto.
Defined.

Lemma anni_app A (st : stmt) f Y
      (EQ:st = stmtApp f Y) (d:anni A st) : A.
Proof.
  rewrite EQ in d. simpl in *. eauto.
Defined.

Arguments anni_if {A} {st} {e} {s} {t} EQ d.

Definition option_extr A (o:option A) (x:A) :=
  match o with
  | Some a => a
  | _ => x
  end.


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

Fixpoint forward (sT:stmt) (Dom: stmt -> Type)
           (ftransform :
              forall sT (ZL:list params) s,
                subTerm s sT
                -> list_union (of_list ⊝ ZL) [<=] occurVars sT
                -> Dom sT -> bool -> anni (Dom sT) s)
           (ZL:list (params)) (ZLIncl:list_union (of_list ⊝ ZL) [<=] occurVars sT)
           (st:stmt) (ST:subTerm st sT) (d:Dom sT) (anr:ann bool) {struct st}
  :  Dom sT * ann bool * list bool.
  refine (
      match st as st', anr return st = st' -> Dom sT  * ann bool * list bool with
      | stmtLet x e s as st, ann1 b anr' =>
        fun EQ =>
          let d:Dom sT := anni_let (Dom sT) EQ (ftransform sT ZL st ST ZLIncl d b) in
          let '(d', ans', AL) :=
              forward sT Dom ftransform ZL ZLIncl s (subTerm_EQ_Let EQ ST) d (setTopAnn anr' b) in
          (d', ann1 b ans', AL)
      | stmtIf x s t, ann2 b anr1 anr2 =>
        fun EQ =>
          let '(b1, b2, a) := anni_if EQ (ftransform sT ZL st ST ZLIncl d b) in
          let '(a', an1, AL1) :=
              @forward sT Dom ftransform ZL ZLIncl s
                       (subTerm_EQ_If1 EQ ST) a (setTopAnn anr1 b1) in
          let '(a'', an2, AL2) :=
              @forward sT Dom ftransform ZL ZLIncl t
                       (subTerm_EQ_If2 EQ ST) a' (setTopAnn anr2 b2) in
          (a'', ann2 b an1 an2, zip join AL1 AL2)
      | stmtApp f Y as st, ann0 b =>
        fun EQ =>
          let d := anni_app (Dom sT) EQ (ftransform sT ZL st ST ZLIncl d b) in
          let AL := ((fun _ => false) ⊝ ZL) in
          (d, ann0 b, list_update_at AL (counted f) b)

    | stmtReturn x as st, ann0 b =>
      fun EQ => (d, ann0 b, ((fun _ => false) ⊝ ZL))

    | stmtFun F t as st, annF b rF r =>
      fun EQ =>
        let ZL' := List.map fst F ++ ZL in
        let '(a', r', AL) :=
            @forward sT Dom ftransform ZL'
                     (@ZLIncl_ext sT _ F t ZL EQ ST ZLIncl)
                     t (subTerm_EQ_Fun1 EQ ST) d (setTopAnn r b) in
        let '(a'', rF', AL') := forwardF AL (forward sT Dom ftransform ZL'
                                     (@ZLIncl_ext sT _ F t ZL EQ ST ZLIncl))
                            F (zip (@setTopAnn _) rF AL) a' (subTerm_EQ_Fun2 EQ ST) in
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


Lemma forward_length sT Dom f ZL ZLIncl s (ST:subTerm s sT) d r
  : ❬snd (forward Dom f ZL ZLIncl ST d r)❭ = ❬ZL❭.
Proof.
  revert_except s.
  sind s; destruct s, r; simpl; eauto with len;
    repeat let_pair_case_eq; subst; simpl; eauto.
  - len_simpl. rewrite (IH s1), (IH s2); eauto with len.
  - rewrite length_drop_minus.
    erewrite forwardF_snd_length; eauto with len.
    + len_simpl. omega.
Qed.

Lemma forward_fst_snd_getAnn sT Dom f ZL ZLIncl s (ST:subTerm s sT) d r
  : getAnn (snd (fst (forward Dom f ZL ZLIncl ST d r))) = getAnn r.
Proof.
  revert_except s.
  sind s; destruct s, r; simpl; eauto with len;
    repeat let_pair_case_eq; subst; simpl; eauto.
Qed.

Lemma forward_getAnn sT Dom f ZL ZLIncl s (ST:subTerm s sT) b r r'
  : ann_R poEq (snd (fst (forward Dom f ZL ZLIncl ST b r))) r'
    -> getAnn r = getAnn r'.
Proof.
  intros. eapply ann_R_get in H.
  rewrite forward_fst_snd_getAnn in H. eauto.
Qed.

Smpl Add 100
     match goal with
     | [ H : context [ ❬snd (@forward ?sT ?Dom ?f ?ZL ?ZLIncl ?s ?ST ?d ?r)❭ ] |- _ ] =>
       rewrite (@forward_length sT Dom f ZL ZLIncl s ST d r) in H
     | [ |- context [ ❬snd (@forward ?sT ?Dom ?f ?ZL ?ZLIncl ?s ?ST ?d ?r)❭ ] ] =>
       rewrite (@forward_length sT Dom f ZL ZLIncl s ST d r)
     end : len.

Lemma forwardF_mon (sT:stmt) (Dom:stmt->Type) f ZL ZLIncl BL (Len:❬BL❭ <= ❬ZL❭)
      (F:list (params * stmt)) rF a
      (ST:forall n Zs, get F n Zs -> subTerm (snd Zs) sT)
  : PIR2 poLe BL (snd (@forwardF sT Dom BL (@forward sT Dom f ZL ZLIncl) F rF a ST)).
Proof.
  revert rF a ST.
  induction F; intros; destruct rF; simpl; eauto.
  eapply PIR2_impb_orb_left; eauto with len.
Qed.

Lemma forwardF_mon' (sT:stmt) (Dom:stmt->Type) f ZL (F:list (params * stmt)) rF ZLIncl BL
       (Len:❬F❭ = ❬rF❭) a
      (ST:forall n Zs, get F n Zs -> subTerm (snd Zs) sT)
: PIR2 poLe (getAnn ⊝ rF) (getAnn ⊝ snd (fst (@forwardF sT Dom BL
                                             (@forward sT Dom f ZL ZLIncl) F rF a ST))).
Proof.
  revert a ST.
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



(*
Lemma get_forwardF  (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)}
           (forward: forall s (ST:subTerm s sT) (d:Dom sT),
                       Dom sT)
           (ZL:list params)
           (F:list (params * stmt)) (a:Dom sT)
           (ST:forall n s, get F n s -> subTerm (snd s) sT) n Zs
  :get F n Zs
   -> { ST' | get (forwardF forward F a ST) n (forward (snd Zs) ST' a) }.
Proof.
  intros GetF.
  eapply get_getT in GetF.
  general induction GetF; try destruct Zs as [Z s]; simpl.
  - eexists; econstructor.
  - edestruct IHGetF; eauto using get.
Qed.


Ltac inv_get_step_analysis_forward :=
  match goal with
  | [ H: get (@forwardF ?sT ?Dom ?PO ?BSL ?f ?F ?a ?ST) ?n ?x |- _ ]
    => eapply (@forwardF_get sT Dom PO BSL f F a ST n x) in H;
      destruct H as [? [? [? ]]]
  end.

Smpl Add inv_get_step_analysis_forward : inv_get.
 *)

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

Instance PO_anni A s `{PartialOrder A}
  : PartialOrder (anni A s).
Proof.
  destruct s; simpl; eauto with typeclass_instances.
Defined.



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

Lemma option_extr_mon T `{PartialOrder T} (a a':option T) b b'
  : a ⊑ a'
    -> b ⊑ b'
    -> (forall x, a' = Some x -> b ⊑ x)
    -> option_extr a b ⊑ option_extr a' b'.
Proof.
  intros A B C; inv A; simpl; eauto.
  destruct a'; clear_trivial_eqs; simpl; eauto.
Qed.

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

Lemma forward_monotone (sT:stmt) (Dom : stmt -> Type) `{PartialOrder (Dom sT)}
      `{@LowerBounded (Dom sT) H}
      (f: forall sT (ZL:list params),
          forall s, subTerm s sT -> list_union (of_list ⊝ ZL) [<=] occurVars sT
               -> Dom sT -> bool -> anni (Dom sT) s)
      (fMon:forall s (ST:subTerm s sT) ZL
          (ZLIncl:list_union (of_list ⊝ ZL) [<=] occurVars sT),
          forall a a',
            a ⊑ a' -> forall b b', b ⊑ b' -> f sT ZL s ST ZLIncl a b ⊑ f sT ZL s ST ZLIncl a' b')
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params)
      (ZLIncl:list_union (of_list ⊝ ZL) [<=] occurVars sT),
    forall (d d' : Dom sT), d ⊑ d'
      -> forall (r r':ann bool), r ⊑ r'
      -> forward Dom f ZL ZLIncl ST d r ⊑ forward Dom f ZL ZLIncl ST d' r'.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  sind s; destruct s; intros ST ZL ZLIncl d d' LE_d r r'  LE_r;
    destruct r; inv LE_r;
      simpl forward; repeat let_pair_case_eq; subst;
        eauto 10 using @ann_R;
        try now (econstructor; simpl; eauto using @ann_R).
  - pose proof (fMon (stmtLet x e s) ST ZL ZLIncl  _ _ LE_d _ _ H3); eauto.
    simpl in *. split; dcr; eauto; [split; eauto|].
    + eapply IH; eauto.
      eauto using ann_R_setTopAnn.
    + econstructor; eauto. eapply IH; eauto.
      eauto using ann_R_setTopAnn.
    + eapply IH; eauto.
      eauto using ann_R_setTopAnn.
  - pose proof (fMon (stmtIf e s1 s2) ST ZL ZLIncl _ _ LE_d) as LE_f.
    pose proof (IH s1 ltac:(eauto) (subTerm_EQ_If1 eq_refl ST) ZL) as LE1; eauto.
    pose proof (IH s2 ltac:(eauto) (subTerm_EQ_If2 eq_refl ST) ZL) as LE2; eauto.
    split; [split|];simpl.
    + eapply LE2; eauto. eapply LE1; eauto. eapply LE_f; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_f; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_f; eauto.
    + econstructor; eauto.
      eapply LE1; eauto. eapply LE_f; eauto.
      eapply ann_R_setTopAnn; eauto. eapply LE_f; eauto.
      eapply LE2; eauto. eapply LE1; eauto.
      eapply LE_f; eauto. eapply ann_R_setTopAnn; eauto.
      eapply LE_f; eauto. eapply ann_R_setTopAnn; eauto.
      eapply LE_f; eauto.
    + eapply PIR2_impb_orb; eauto with len.
      * eapply LE1; eauto. eapply LE_f; eauto.
        eapply ann_R_setTopAnn; eauto. eapply LE_f; eauto.
      * eapply LE2; eauto. eapply LE1; eauto.
        eapply LE_f; eauto. eapply ann_R_setTopAnn; eauto.
        eapply LE_f; eauto. eapply ann_R_setTopAnn; eauto.
        eapply LE_f; eauto.
  - split; [split|]; simpl.
    + eapply (fMon (stmtApp l Y)); eauto.
    + eauto.
    + pose proof (@update_at_poLe bool _ _ _ ZL l _ _ H2).
      simpl in *. eauto.
  - (*assert (MON:
              forall n Zs (GET:get F n Zs) (ST ST'0 : subTerm (snd Zs) sT) (d d' : Dom sT),
                d ⊑ d' ->
                forall r r' : ann bool,
                  r ⊑ r' ->
                  forward Dom f (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST' ZLIncl') ST d r
                          ⊑ forward Dom f (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST' ZLIncl') ST'0 d' r'). {
      intros. eapply IH; eauto.
    }
    pose proof (@forwardF_monotone sT Dom _ (forward Dom f (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST' ZLIncl')) F MON (subTerm_EQ_Fun2 eq_refl ST) (subTerm_EQ_Fun2 eq_refl ST')).*)
    split; [split|]; simpl.
    + eapply forwardF_monotone; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
      eapply PIR2_zip_setTopAnnO; eauto.
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
        eapply (@PIR2_zip_setTopAnnO bool PartialOrder_bool); eauto.
        eapply PIR2_get; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply forwardF_monotone; eauto.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply (@PIR2_zip_setTopAnnO bool PartialOrder_bool); eauto.
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
      eapply PIR2_zip_setTopAnnO; eauto.
      hnf. eapply PIR2_get; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
      eapply IH; eauto.
      eapply ann_R_setTopAnn; eauto.
Qed.

Require Import Take.

Lemma forwardF_get  (sT:stmt) (Dom:stmt->Type) BL ZL
      (F:list (params * stmt)) rF a ZLIncl
      (f : forall (sT : stmt) (ZL : 〔params〕) (s : stmt),
          subTerm s sT ->
          list_union (of_list ⊝ ZL) [<=] occurVars sT
          -> Dom sT -> bool -> anni (Dom sT) s)
      (ST:forall n s, get F n s -> subTerm (snd s) sT) n aa
           (GetBW:get (snd (fst (@forwardF sT Dom BL (@forward sT Dom f ZL ZLIncl) F rF a ST))) n aa)
  :
    { Zs : params * stmt &
           {GetF : get F n Zs &
                   { r : ann bool &
                         {GetrF : get rF n r &
                                  { ST' : subTerm (snd Zs) sT &
                                          { ST'' : forall (n0 : nat) (s : params * stmt), get (take n F) n0 s -> subTerm (snd s) sT | aa = snd (fst (forward Dom f ZL ZLIncl ST' (fst (fst (@forwardF sT Dom BL (@forward sT Dom f ZL ZLIncl) (take n F) (take n rF) a ST''))) r))
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

(*
Lemma forwardF_PIR2  (sT:stmt) (Dom:stmt->Type) BL ZL
      (F:list (params * stmt)) rF a ZLIncl
      (f : forall sT (ZL : 〔params〕) (s : stmt),
          subTerm s sT ->
          list_union (of_list ⊝ ZL) [<=] occurVars sT
          -> Dom sT -> bool -> anni (Dom sT) s) sa
      (ST:forall n s, get F n s -> subTerm (snd s) sT) r Zs ST' n ST''
      (GetrF:get rF n r) (GetF:get F n Zs)
:
  PIR2 impb
       (Take.take ❬F❭
                  (snd
                     (@forward sT Dom f ZL ZLIncl (snd Zs) ST'
                              (fst
                                 (fst
                                    (@forwardF sT Dom
                                       BL
                                       (forward Dom f ZL ZLIncl)
                                       (Take.take n F)
                                       (Take.take n (setTopAnn (A:=bool) ⊜ sa BL))
                                       a ST''))) r)))
       (@getAnn bool
          ⊝ snd
          (fst
             (forwardF
                BL
                (forward Dom f ZL ZLIncl) F
                (setTopAnn (A:=bool) ⊜ sa BL)
                a
                ST))).
Proof.
  general induction F; destruct rF; isabsurd. simpl.
  cases. exfalso. admit.
  destruct sa, BL. simpl. exfalso. admit.
  exfalso; admit. simpl. exfalso; admit.
  simpl. econstructor.
  rewrite forward_fst_snd_getAnn. rewrite getAnn_setTopAnn.
  admit.

  rewrite
  - simpl.
Qed.
 *)

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
          list_union (of_list ⊝ ZL) [<=] occurVars sT -> Dom sT -> bool -> anni (Dom sT) s)
      ZL ZLIncl d r
      (AN:annotation s r)
  : annotation s (snd (fst (forward Dom f ZL ZLIncl ST d r))).
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
             list_union (of_list ⊝ ZL) [<=] occurVars sT -> Dom sT -> bool -> anni (Dom sT) s)
         (fMon:forall sT s (ST:subTerm s sT) ZL
                 (ZLIncl:list_union (of_list ⊝ ZL) [<=] occurVars sT),
             forall a b, a ⊑ b ->
                    forall r r', r ⊑ r' ->
                            f sT ZL s ST ZLIncl a r ⊑ f sT ZL s ST ZLIncl b r')
         (Trm: forall s, Terminating (Dom s) poLt)

  : forall s, Iteration (Dom s * { a : ann bool | annotation s a }) :=
  {
    step := fun dr =>
             let a := forward Dom f nil (incl_empty _ (occurVars s)) (subTerm_refl s)
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
    eapply (forward_monotone Dom f (fMon s)); eauto.
    eapply H. eapply H.
Defined.
