Require Import CSet Le ListUpdateAt Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Terminating.
Require Import Val Var Env IL Annotation Lattice DecSolve LengthEq MoreList Status AllInRel OptionR.
Require Import Keep Subterm Analysis.

Set Implicit Arguments.


Definition forwardF (sT:stmt) (Dom:stmt->Type) `{BoundedSemiLattice (Dom sT)}
           (forward:〔params〕 ->
                    forall s (ST:subTerm s sT) (d:Dom sT) (a:ann (Dom sT)), ann (Dom sT) * 〔Dom sT〕)
           (ZL:list params)
           (F:list (params * stmt)) (anF:list (ann (Dom sT)))
           (ST:forall n s, get F n s -> subTerm (snd s) sT)
  : list (ann (Dom sT) * 〔Dom sT〕).
  revert F anF ST.
  fix g 1. intros.
  destruct F as [|Zs F'].
  - eapply nil.
  - destruct anF as [|a anF'].
    + eapply nil.
    + econstructor 2.
      * refine (forward ZL (snd Zs) _ (getAnn a) a).
        eapply (ST 0 Zs); eauto using get.
      * eapply (g F' anF').
        eauto using get.
Defined.

Arguments forwardF [sT] [Dom] {H} {H0} forward ZL F anF ST : clear implicits.

Fixpoint forwardF_length (sT:stmt) (Dom:stmt->Type) `{BoundedSemiLattice (Dom sT)} forward
           (ZL:list params)
           (F:list (params * stmt)) (anF:list (ann (Dom sT)))
           (ST:forall n s, get F n s -> subTerm (snd s) sT) {struct F}
  : length (forwardF forward ZL F anF ST) = min (length F) (length anF).
Proof.
  destruct F as [|Zs F'], anF; simpl; eauto.
Qed.

Smpl Add
     match goal with
     | [ |- context [ ❬@forwardF ?sT ?Dom ?H ?BSL ?f ?ZL ?F ?anF ?ST❭ ] ] =>
       rewrite (@forwardF_length sT Dom H BSL f ZL F anF ST)
     end : len.

Lemma forwardF_length_ass (sT:stmt) (Dom:stmt->Type) `{BoundedSemiLattice (Dom sT)}
      forward ZL F anF ST k
  : length F = k
    -> length F = length anF
    -> length (forwardF forward ZL F anF ST) = k.
Proof.
  intros. rewrite forwardF_length, <- H2.
  repeat rewrite Nat.min_idempotent; eauto.
Qed.

Hint Resolve @forwardF_length_ass : len.

Fixpoint forward (sT:stmt) (Dom: stmt -> Type) `{BoundedSemiLattice (Dom sT)}
           (ftransform :
              forall sT, list params ->
                    forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
           (ZL:list (params)) (st:stmt) (ST:subTerm st sT) (d:Dom sT) (a:ann (Dom sT)) {struct st}
  :  ann (Dom sT) * list (Dom sT)
  := match st as st', a return st = st' -> ann (Dom sT) * list (Dom sT) with
    | stmtLet x e s as st, ann1 _ ans =>
      fun EQ =>
        let an := ftransform sT ZL st ST d in
        let (ans', AL) := forward Dom ftransform ZL (subTerm_EQ_Let EQ ST)
                                 (getAnni d an) ans in
        (ann1 d ans', AL)
    | stmtIf x s t, ann2 _ ans ant =>
      fun EQ =>
        let an := ftransform sT ZL st ST d in
        let (ans', AL) := forward Dom ftransform ZL (subTerm_EQ_If1 EQ ST)
                                 (getAnniLeft d an) ans in
        let (ant', AL') := forward Dom ftransform ZL (subTerm_EQ_If2 EQ ST)
                                  (getAnniRight d an) ant in
        (ann2 d ans' ant', zip join AL AL')
    | stmtApp f Y as st, ann0 _ as an =>
      fun EQ =>
        let an := ftransform sT ZL st ST d in
        (ann0 d, list_update_at ((fun _ => bottom) ⊝ ZL) (counted f) (getAnni d an))


    | stmtReturn x as st, ann0 _ as an =>
      fun EQ => (ann0 d, (fun _ => bottom) ⊝ ZL)

    | stmtFun F t as st, annF _ anF ant =>
      fun EQ =>
        let ZL' := List.map fst F ++ ZL in
        let (ant', ALt) := forward Dom ftransform ZL' (subTerm_EQ_Fun1 EQ ST)
                                  d ant in
        let anF' := forwardF (forward Dom ftransform) ZL' F anF
                            (subTerm_EQ_Fun2 EQ ST) in
        let AL' := fold_left (zip join) (snd ⊝ anF') ALt in
        (annF d (zip (@setTopAnn _) (fst ⊝ anF') AL') ant',
         drop ❬F❭ AL')
    | _, an => fun EQ => (ann0 d, (fun _ => bottom) ⊝ ZL)
  end eq_refl.

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


Lemma forwardF_get  (sT:stmt) (Dom:stmt->Type) `{BoundedSemiLattice (Dom sT)}
           (forward:〔params〕 ->
                     forall s (ST:subTerm s sT) (d:Dom sT) (a:ann (Dom sT)),
                       ann (Dom sT) * list (Dom sT))
           (ZL:list params)
           (F:list (params * stmt)) (anF:list (ann (Dom sT)))
           (ST:forall n s, get F n s -> subTerm (snd s) sT) aa n
           (GetBW:get (forwardF forward ZL F anF ST) n aa)
      :
        { Zs : params * stmt & {GetF : get F n Zs &
        { a : ann (Dom sT) & { getAnF : get anF n a &
        { ST' : subTerm (snd Zs) sT | aa = forward ZL (snd Zs) ST' (getAnn a) a
        } } } } }.
Proof.
  eapply get_getT in GetBW.
  general induction anF; destruct F as [|[Z s] F']; inv GetBW.
  - exists (Z, s). simpl. do 4 (eexists; eauto 20 using get).
  - edestruct IHanF as [Zs [? [? [? ]]]]; eauto; dcr; subst.
    exists Zs. do 4 (eexists; eauto 20 using get).
Qed.

Lemma get_forwardF  (sT:stmt) (Dom:stmt->Type) `{BoundedSemiLattice (Dom sT)}
           (forward:〔params〕 ->
                     forall s (ST:subTerm s sT) (d:Dom sT) (a:ann (Dom sT)),
                       ann (Dom sT) * list (Dom sT))
           (ZL:list params)
           (F:list (params * stmt)) (anF:list (ann (Dom sT)))
           (ST:forall n s, get F n s -> subTerm (snd s) sT) n Zs a
  :get F n Zs
   -> get anF n a
   -> { ST' | get (forwardF forward ZL F anF ST) n (forward ZL (snd Zs) ST' (getAnn a) a) }.
Proof.
  intros GetF GetAnF.
  eapply get_getT in GetF.
  eapply get_getT in GetAnF.
  general induction GetAnF; destruct Zs as [Z s]; inv GetF; simpl.
  - eexists; econstructor.
  - edestruct IHGetAnF; eauto using get.
Qed.


Ltac inv_get_step1 dummy :=
  first [inv_get_step |
         match goal with
         | [ H: get (@forwardF ?sT ?Dom ?PO ?BSL ?f ?ZL ?F ?anF ?ST) ?n ?x |- _ ]
           => eapply (@forwardF_get sT Dom PO BSL f ZL F anF ST x n) in H;
             destruct H as [? [? [? [? [? ]]]]]
         end
        ].

Tactic Notation "inv_get_step" := inv_get_step1 idtac.
Tactic Notation "inv_get" := inv_get' inv_get_step1.

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

Lemma forward_length (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params),
    forall d (a : ann (Dom sT)), ❬snd (forward Dom f ZL ST d a)❭ = ❬ZL❭.
Proof.
  sind s; destruct s; destruct a; simpl; eauto with len;
    repeat let_pair_case_eq; subst; simpl in *; eauto.
  - rewrite zip_length2; eauto. rewrite IH; eauto; symmetry; eauto.
  - rewrite list_update_at_length; eauto with len.
  - rewrite length_drop_minus.
    rewrite fold_list_length'.
    + rewrite IH; eauto. rewrite app_length, map_length. omega.
    + intros. inv_get. repeat rewrite IH; eauto.
    + intros. rewrite zip_length; eauto.
      eapply min_l; eauto.
Qed.


Smpl Add
     match goal with
     | [ |- context [ ❬snd (@forward ?sT ?Dom ?H ?BSL ?f ?ZL ?s ?ST ?d ?a)❭ ] ] =>
       rewrite (@forward_length sT Dom H BSL f s ST ZL d a)
     end : len.

Lemma forward_length_ass
      (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) k,
    forall d (a : ann (Dom sT)), ❬ZL❭ = k -> ❬snd (forward Dom f ZL ST d a)❭ = k.
Proof.
  intros. rewrite forward_length; eauto.
Qed.

Lemma forward_length_le_ass
      (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) k,
    forall d (a : ann (Dom sT)), ❬ZL❭ <= k -> ❬snd (forward Dom f ZL ST d a)❭ <= k.
Proof.
  intros. rewrite forward_length; eauto.
Qed.

Lemma forward_length_le_ass_right
      (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) k,
    forall d (a : ann (Dom sT)), k <= ❬ZL❭ -> k <= ❬snd (forward Dom f ZL ST d a)❭.
Proof.
  intros. rewrite forward_length; eauto.
Qed.


Hint Resolve @forward_length_ass forward_length_le_ass forward_length_le_ass_right : len.

Lemma forward_annotation sT (Dom:stmt->Type) `{BoundedSemiLattice (Dom sT)} s
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
  : forall ZL d a (ST:subTerm s sT), annotation s a
               -> annotation s (fst (forward Dom f ZL ST d a)).
Proof.
  sind s; intros ZL d a ST Ann; destruct s; inv Ann; simpl;
    repeat let_pair_case_eq; subst; eauto 20 using @annotation, setTopAnn_annotation.
  - econstructor; eauto using setTopAnn_annotation.
    + len_simpl.
      rewrite fold_list_length'; intros; inv_get; eauto with len.
    + intros. inv_get.
      eauto using setTopAnn_annotation, setAnn_annotation.
Qed.

Lemma forward_getAnn' (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT)) s (ST:subTerm s sT) ZL d an
  : getAnn (fst (@forward sT Dom _ _ f ZL s ST d an)) = d.
Proof.
  intros. destruct s, an; simpl in *; eauto;
  repeat let_pair_case_eq; simpl; eauto.
Qed.

Lemma forward_getAnn (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT)) s (ST:subTerm s sT) ZL a an
  : ann_R eq (fst (@forward sT Dom _ _ f ZL s ST a an)) an
    -> getAnn an = a.
Proof.
  intros. eapply ann_R_get in H1.
  rewrite forward_getAnn' in H1. eauto.
Qed.


Ltac simpl_forward_setTopAnn :=
  repeat match goal with
         | [H : ann_R eq (fst (forward ?reachability_transform ?ZL
                                       ?s ?ST ?a ?sa)) ?sa |- _ ] =>
           let X := fresh "H" in
           match goal with
           | [ H' : getAnn sa = a |- _ ] => fail 1
           | _ => exploit (forward_getAnn _ _ _ _ _ H) as X
           end
         end; subst; try eassumption.

Ltac fold_po :=
  repeat match goal with
         | [ H : context [ @ann_R ?A ?A (@poLe ?A ?I) ] |- _ ] =>
           change (@ann_R A A (@poLe A I)) with (@poLe (@ann A) _) in H
         | [ H : context [ PIR2 poLe ?x ?y ] |- _ ] =>
           change (PIR2 poLe x y) with (poLe x y) in H
         | [ |- context [ ann_R poLe ?x ?y ] ] =>
           change (ann_R poLe x y) with (poLe x y)
  end.

Lemma forward_monotone (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
      (fMon:forall s (ST ST':subTerm s sT) ZL,
          forall a b, a ⊑ b -> f sT ZL s ST a ⊑ f sT ZL s ST' b)
  : forall (s : stmt) (ST ST':subTerm s sT) (ZL:list params),
    forall (d d' : Dom sT) (a b : ann (Dom sT)), d ⊑ d' -> a ⊑ b ->
                           forward Dom f ZL ST d a ⊑ forward Dom f ZL ST' d' b.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  sind s; destruct s; intros ST ST' ZL d d' a b LE_d LE; simpl forward; inv LE;
    simpl forward; repeat let_pair_case_eq; subst; eauto 10 using @ann_R;
      try now (econstructor; simpl; eauto using @ann_R).
  - econstructor; simpl; eauto; fold_po.
    + econstructor; eauto; fold_po.
      eapply IH; eauto using poLe_getAnni.
    + eapply IH; eauto using poLe_getAnni.
  - econstructor; simpl; eauto.
    + econstructor; eauto.
      eapply (IH s1); eauto using poLe_getAnniLeft.
      eapply (IH s2); eauto using poLe_getAnniRight.
    +
      eapply PIR2_ojoin_zip.
      * eapply IH; eauto using poLe_getAnniLeft.
      * eapply IH; eauto using poLe_getAnniRight.
  - econstructor; eauto. simpl. econstructor; eauto.
    eapply update_at_poLe.
    eapply poLe_getAnni; eauto.
  - fold_po.
    assert (forall (n : nat) (x x' : ann (Dom sT) * 〔Dom sT〕),
               get (forwardF (forward Dom f) (fst ⊝ F ++ ZL) F ans
                             (subTerm_EQ_Fun2 eq_refl ST)) n x ->
               get (forwardF (forward Dom f) (fst ⊝ F ++ ZL) F bns
                             (subTerm_EQ_Fun2 eq_refl ST')) n x' ->
               x ⊑ x'). {
      intros; inv_get; dcr; eauto.
      eapply IH; eauto.
      exploit H3; eauto.
      eapply ann_R_get; eauto.
    }
    econstructor; simpl; eauto.
    + econstructor; eauto.
      * repeat rewrite zip_length.
        repeat rewrite map_length.
        repeat rewrite forwardF_length.
        repeat rewrite fold_list_length'.
        repeat rewrite forward_length. rewrite H2; reflexivity.
        intros; inv_get; eauto with len.
        intros; rewrite zip_length; eauto with len.
        intros; inv_get; eauto with len.
        intros; rewrite zip_length; eauto with len.
      * intros.
        inv_zip H6; clear H6. inv_map H8; clear H8.
        inv_zip H7; clear H7. inv_map H8; clear H8.
        exploit H5; eauto.
        exploit get_PIR2; [ eapply PIR2_fold_zip_join | eapply H9 | eapply H10 | ].
        eapply PIR2_get. intros. inv_map H12; clear H12. inv_map H11; clear H11.
        eapply H5; eauto.
        repeat rewrite map_length.
        repeat rewrite forwardF_length.
        repeat rewrite forward_length. rewrite H2; reflexivity.
        eapply IH; eauto.
        eapply ann_R_setTopAnn; eauto.
        eapply H8.
      * eapply IH; eauto.
    + eapply PIR2_drop. eapply PIR2_fold_zip_join.
      * eapply PIR2_get; eauto.
        intros. inv_map H6. inv_map H7.
        exploit H5; eauto. eapply H10.
        repeat rewrite map_length.
        repeat rewrite forwardF_length.
        repeat rewrite forward_length. rewrite H2; reflexivity.
      * eapply IH; eauto.
Qed.

Require Import FiniteFixpointIteration.

Instance makeForwardAnalysis (Dom:stmt -> Type)
         `{forall s, PartialOrder (Dom s) }
         (BSL:forall s, BoundedSemiLattice (Dom s))
         (f: forall sT, list params ->
                   forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
         (fMon:forall sT s (ST ST':subTerm s sT) ZL,
             forall a b, a ⊑ b -> f sT ZL s ST a ⊑ f sT ZL s ST' b)
         (Trm: forall s, Terminating (Dom s) poLt)

  : forall s (i:Dom s), Iteration { a : ann (Dom s) | annotation s a } :=
  {
    step := fun X : {a : ann (Dom s) | annotation s a} =>
                      exist (fun a0 : ann (Dom s) => annotation s a0)
                            (fst (forward Dom f nil (subTerm_refl _) i (proj1_sig X)))
                                 (forward_annotation Dom f nil i (subTerm_refl _) _);
    initial_value :=
      exist (fun a : ann (Dom s) => annotation s a)
            (setAnn bottom s)
            (setAnn_annotation bottom s)
  }.
Proof.
  - destruct X; eauto.
  - intros [d Ann]; simpl.
    pose proof (@ann_bottom s (Dom s) _ _ _ Ann).
    eapply H0.
  - intros. eapply terminating_sig.
    eapply terminating_ann. eauto.
  - intros [a Ann] [b Bnn] LE; simpl in *.
    eapply (forward_monotone Dom f (fMon s)); eauto.
Defined.
