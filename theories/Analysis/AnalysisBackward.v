Require Import CSet Le ListUpdateAt Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Terminating.
Require Import Val Var Env IL Annotation Lattice DecSolve LengthEq MoreList Status AllInRel OptionR.
Require Import Keep Subterm Analysis.

Set Implicit Arguments.


Definition backwardF (sT:stmt) (Dom:stmt->Type)
           (backward:〔params〕 -> 〔Dom sT〕 ->
                     forall s (ST:subTerm s sT) (a:ann (Dom sT)),
                       ann (Dom sT))
           (ZL:list params)
           (AL:list (Dom sT))
           (F:list (params * stmt)) (anF:list (ann (Dom sT)))
           (ST:forall n s, get F n s -> subTerm (snd s) sT)
  : list (ann (Dom sT)).
  revert F anF ST.
  fix g 1. intros.
  destruct F as [|Zs F'].
  - eapply nil.
  - destruct anF as [|a anF'].
    + eapply nil.
    + econstructor 2.
      * refine (backward ZL AL (snd Zs) _ a).
        eapply (ST 0 Zs); eauto using get.
      * eapply (g F' anF'); eauto using get.
Defined.

Arguments backwardF [sT] [Dom] backward ZL AL F anF ST.

Fixpoint backwardF_length (sT:stmt) (Dom:stmt->Type)
           (backward:〔params〕 -> 〔Dom sT〕 ->
                     forall s (ST:subTerm s sT) (a:ann (Dom sT)),
                       ann (Dom sT))
           (ZL:list params)
           (AL:list (Dom sT))
           (F:list (params * stmt)) (anF:list (ann (Dom sT)))
           (ST:forall n s, get F n s -> subTerm (snd s) sT) {struct F}
  : length (backwardF backward ZL AL F anF ST) = min (length F) (length anF).
Proof.
  destruct F as [|Zs F'], anF; simpl; eauto.
Qed.

Smpl Add
     match goal with
     | [ |- context [ ❬@backwardF ?sT ?Dom ?f ?ZL ?AL ?F ?anF ?ST❭ ] ] =>
       rewrite (@backwardF_length sT Dom f ZL AL F anF ST)
     | [ H : context [ ❬@backwardF ?sT ?Dom ?f ?ZL ?AL ?F ?anF ?ST❭ ] |- _ ] =>
       rewrite (@backwardF_length sT Dom f ZL AL F anF ST) in H
     end : len.

Lemma backwardF_length_ass sT (Dom:stmt->Type)
      backward ZL (AL:list (Dom sT)) F anF ST k
  : length F = k
    -> length F = length anF
    -> length (backwardF backward ZL AL F anF ST) = k.
Proof.
  intros. rewrite backwardF_length, <- H0, Nat.min_idempotent; eauto.
Qed.

Hint Resolve backwardF_length_ass : len.

Fixpoint backward (sT:stmt) (Dom: stmt -> Type)
           (btransform :
              forall sT, list params -> list (Dom sT) ->
                    forall s, subTerm s sT -> anni (Dom sT) -> Dom sT)
           (ZL:list (params)) (AL:list (Dom sT)) (st:stmt) (ST:subTerm st sT) (a:ann (Dom sT)) {struct st}
  :  ann (Dom sT)
  := match st as st', a return st = st' -> ann (Dom sT) with
    | stmtLet x e s as st, ann1 d ans =>
      fun EQ =>
        let ans' := backward Dom btransform ZL AL (subTerm_EQ_Let EQ ST) ans in
        let ai := anni1 (getAnn ans') in
        let d := (btransform sT ZL AL st ST ai) in
        ann1 d ans'

    | stmtIf x s t, ann2 d ans ant =>
      fun EQ =>
        let ans' := backward Dom btransform ZL AL (subTerm_EQ_If1 EQ ST) ans in
        let ant' := backward Dom btransform ZL AL (subTerm_EQ_If2 EQ ST) ant in
        let ai := anni2 (getAnn ans') (getAnn ant') in
        let d' := (btransform sT ZL AL st ST ai) in
        ann2 d' ans' ant'

    | stmtApp f Y as st, ann0 d as an =>
      fun EQ => ann0 (btransform sT ZL AL st ST anni0)

    | stmtReturn x as st, ann0 d as an =>
      fun EQ =>
        (ann0 (btransform sT ZL AL st ST anni0))

    | stmtFun F t as st, annF d anF ant =>
      fun EQ =>
        let ALinit := getAnn ⊝ anF ++ AL in
        let ZL' := List.map fst F ++ ZL in
        let anF' :=
            @backwardF sT Dom (backward Dom btransform) ZL' ALinit F anF
                       (subTerm_EQ_Fun2 EQ ST)
        in
        let AL' := getAnn ⊝ anF' ++ AL in
        let ant' := backward Dom btransform ZL' AL'
                            (subTerm_EQ_Fun1 EQ ST) ant in
        let ai := anni1 (getAnn ant') in
        let d' := btransform sT ZL' AL' st ST ai in
        annF d' anF' ant'
    | _, an => fun EQ => an
  end eq_refl.

Lemma backwardF_get  (sT:stmt) (Dom:stmt->Type)
           (backward:〔params〕 -> 〔Dom sT〕 ->
                     forall s (ST:subTerm s sT) (a:ann (Dom sT)),
                       ann (Dom sT))
           (ZL:list params)
           (AL:list (Dom sT))
           (F:list (params * stmt)) (anF:list (ann (Dom sT)))
           (ST:forall n s, get F n s -> subTerm (snd s) sT) aa n
           (GetBW:get (backwardF backward ZL AL F anF ST) n aa)
      :
        { Zs : params * stmt & {GetF : get F n Zs &
        { a : ann (Dom sT) & { getAnF : get anF n a &
        { ST' : subTerm (snd Zs) sT | aa = backward ZL AL (snd Zs) ST' a
        } } } } }.
Proof.
  eapply get_getT in GetBW.
  general induction anF; destruct F as [|[Z s] F']; inv GetBW.
  - exists (Z, s). eauto using get.
  - edestruct IHanF as [Zs [? [? [? ]]]]; eauto; dcr.
    subst. exists Zs. eauto 10 using get.
Qed.

Lemma get_backwardF  (sT:stmt) (Dom:stmt->Type)
           (backward:〔params〕 -> 〔Dom sT〕 ->
                     forall s (ST:subTerm s sT) (a:ann (Dom sT)),
                       ann (Dom sT))
           (ZL:list params)
           (AL:list (Dom sT))
           (F:list (params * stmt)) (anF:list (ann (Dom sT)))
           (ST:forall n s, get F n s -> subTerm (snd s) sT) n Zs a
  :get F n Zs
    -> get anF n a
    -> { ST' | get (backwardF backward ZL AL F anF ST) n (backward ZL AL (snd Zs) ST' a)}.
Proof.
  intros GetF GetAnF.
  eapply get_getT in GetF.
  eapply get_getT in GetAnF.
  general induction GetAnF; destruct Zs as [Z s]; inv GetF; simpl.
  - eexists. econstructor.
  - destruct x'0; simpl.
    edestruct IHGetAnF; eauto.
    eexists x0. econstructor. eauto.
Qed.

Ltac inv_get_step_analysis_backward :=
  match goal with
  | [ H: get (backwardF ?f ?ZL ?AL ?F ?anF ?ST) ?n ?x |- _ ]
    => eapply backwardF_get in H;
      destruct H as [? [? [? [? [? ]]]]]
  end.

Smpl Add inv_get_step_analysis_backward : inv_get.

Lemma backward_monotone (sT:stmt) (Dom : stmt -> Type) `{PartialOrder (Dom sT)}
      (f: forall sT, list params -> list (Dom sT) ->
                forall s, subTerm s sT -> anni (Dom sT) -> Dom sT)
      (fMon:forall s (ST:subTerm s sT) ZL AL AL', poLe AL AL' ->
                           forall a b, a ⊑ b -> f sT ZL AL s ST a ⊑ f sT ZL AL' s ST b)
  : forall (s : stmt) (ST:subTerm s sT) ZL AL AL',
    poLe AL AL' ->
    forall a b : ann (Dom sT), annotation s a ->  a ⊑ b ->
                           backward Dom f ZL AL ST a ⊑ backward Dom f ZL AL' ST b.
Proof.
  intros s.
  sind s; destruct s; intros ST ZL AL AL' ALLE d d' Ann LE; simpl backward; inv LE; inv Ann;
    simpl backward; eauto 10 using @ann_R, tab_false_impb, update_at_impb, zip_orb_impb.
  - econstructor; eauto.
    + eapply fMon; eauto.
      econstructor.
      eapply getAnn_poLe. eauto.
    + eapply IH; eauto.
  - econstructor; eauto.
    + simpl; eauto.
      eapply fMon; eauto.
      econstructor; eapply getAnn_poLe.
      eapply (IH s1); eauto.
      eapply (IH s2); eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
  - econstructor; eauto.
  - econstructor; simpl; eauto.
  - assert (AL'LE:getAnn ⊝ ans ++ AL ⊑ getAnn ⊝ bns ++ AL'). {
      eapply PIR2_app; eauto.
      eapply PIR2_get; intros; inv_get.
      eapply getAnn_poLe. eapply H2; eauto. eauto with len.
    }
    assert (getAnn
              ⊝ backwardF (backward Dom f) (fst ⊝ F ++ ZL) (getAnn ⊝ ans ++ AL) F ans
              (subTerm_EQ_Fun2 eq_refl ST) ++ AL
              ⊑ getAnn
              ⊝ backwardF (backward Dom f) (fst ⊝ F ++ ZL) (getAnn ⊝ bns ++ AL') F bns
              (subTerm_EQ_Fun2 eq_refl ST) ++ AL'). {
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 20 with len; intros; inv_get.
      eapply getAnn_poLe.
      assert (x5 = x11) by eapply subTerm_PI; subst.
      eapply IH; eauto.
      exploit H2; eauto.
    }
    econstructor; eauto.
    + eapply fMon; eauto.
      econstructor; eauto.
      eapply getAnn_poLe. eapply IH; eauto.
    + eauto 30 with len.
    + intros; inv_get.
      assert (x9 = x3) by eapply subTerm_PI; subst.
      eapply IH; eauto.
      eapply H2; eauto.
    + eapply IH; eauto.
Qed.

Lemma backward_ext (sT:stmt) (Dom : stmt -> Type) `{PartialOrder (Dom sT)}
      (f: forall sT, list params -> list (Dom sT) ->
                forall s, subTerm s sT -> anni (Dom sT) -> Dom sT)
      (fMon:forall s (ST:subTerm s sT) ZL AL AL',
          AL ≣ AL' -> forall a b, a ≣ b -> f sT ZL AL s ST a ≣ f sT ZL AL' s ST b)
  : forall (s : stmt) (ST:subTerm s sT) ZL AL AL',
    AL ≣ AL' -> forall a b : ann (Dom sT),
      annotation s a -> a ≣ b -> backward Dom f ZL AL ST a ≣ backward Dom f ZL AL' ST b.
Proof.
  intros s.
  sind s; destruct s; intros ST ZL AL AL' ALLE d d' Ann LE; simpl backward; inv LE; inv Ann;
    simpl backward; eauto 10 using @ann_R, tab_false_impb, update_at_impb, zip_orb_impb.
  - econstructor; eauto.
    + eapply fMon; eauto.
      econstructor.
      eapply getAnn_poEq. eauto.
    + eapply IH; eauto.
  - econstructor; eauto.
    + simpl; eauto.
      eapply fMon; eauto.
      econstructor; eapply getAnn_poEq.
      eapply (IH s1); eauto.
      eapply (IH s2); eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
  - econstructor; eauto.
  - econstructor; simpl; eauto.
  - assert (AL'LE:getAnn ⊝ ans ++ AL ≣ getAnn ⊝ bns ++ AL'). {
      eapply PIR2_app; eauto.
      eapply PIR2_get; intros; inv_get.
      eapply getAnn_poEq. eapply H2; eauto. eauto with len.
    }
    assert (getAnn
              ⊝ backwardF (backward Dom f) (fst ⊝ F ++ ZL) (getAnn ⊝ ans ++ AL) F ans
              (subTerm_EQ_Fun2 eq_refl ST) ++ AL
              ≣ getAnn
              ⊝ backwardF (backward Dom f) (fst ⊝ F ++ ZL) (getAnn ⊝ bns ++ AL') F bns
              (subTerm_EQ_Fun2 eq_refl ST) ++ AL'). {
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 20 with len; intros; inv_get.
      eapply getAnn_poEq.
      assert (x5 = x11) by eapply subTerm_PI; subst.
      eapply IH; eauto.
      exploit H2; eauto.
    }
    econstructor; eauto.
    + eapply fMon; eauto.
      econstructor; eauto.
      eapply getAnn_poEq. eapply IH; eauto.
    + eauto 30 with len.
    + intros; inv_get.
      assert (x9 = x3) by eapply subTerm_PI; subst.
      eapply IH; eauto.
      eapply H2; eauto.
    + eapply IH; eauto.
Qed.

Lemma backward_annotation sT (Dom:stmt->Type) `{PartialOrder (Dom sT)} s
      (f: forall sT, list params -> list (Dom sT) ->
                forall s, subTerm s sT -> anni (Dom sT) -> Dom sT)
  : forall ZL AL a (ST:subTerm s sT), annotation s a
               -> annotation s (backward Dom f ZL AL ST a).
Proof.
  sind s; intros ZL AL a ST Ann; destruct s; inv Ann; simpl; eauto using @annotation.
  - econstructor; eauto with len.
    + intros. inv_get.
      * eapply IH; eauto.
Qed.

Require Import FiniteFixpointIteration.

Instance makeBackwardAnalysis (Dom:stmt -> Type)
         `{forall s, PartialOrder (Dom s) }
         (BSL:forall s, BoundedSemiLattice (Dom s))
         (f: forall sT, list params -> list (Dom sT) ->
                   forall s, subTerm s sT -> anni (Dom sT) -> Dom sT)
         (fMon:forall sT s (ST:subTerm s sT) ZL AL AL',
             poLe AL AL' ->
             forall a b, a ⊑ b -> f sT ZL AL s ST a ⊑ f sT ZL AL' s ST b)
         (Trm: forall s, Terminating (Dom s) poLt)
  : forall s, Iteration { a : ann (Dom s) | annotation s a } :=
  {
    step := fun X : {a : ann (Dom s) | annotation s a} =>
             let (a, Ann) := X in
             exist (fun a0 : ann (Dom s) => annotation s a0)
                   (backward Dom f nil nil (subTerm_refl _) a)
                   (backward_annotation Dom f nil nil (subTerm_refl _) Ann);
    initial_value :=
      exist (fun a : ann (Dom s) => annotation s a)
            (setAnn bottom s)
            (setAnn_annotation bottom s)
  }.
Proof.
  - intros [d Ann]; simpl.
    pose proof (@ann_bottom s (Dom s) _ _ _ Ann).
    eapply H0.
  - intros. eapply terminating_sig.
    eapply terminating_ann. eauto.
  - intros [a Ann] [b Bnn] LE; simpl in *.
    eapply (backward_monotone Dom f (fMon s)); eauto.
Defined.
