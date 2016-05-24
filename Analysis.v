Require Import CSet Le ListUpdateAt Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Terminating.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve LengthEq MoreList Status AllInRel OptionR.

Set Implicit Arguments.

(** Specification of an analysis and generic fixpoint iteration algorithm *)

Class Monotone Dom `{PartialOrder Dom} Dom' `{PartialOrder Dom'} (f:Dom->Dom') :=
  monotone : forall a b, poLe a b -> poLe (f a) (f b).

Class Analysis (Dom: Type) := makeAnalysis {
  dom_po :> PartialOrder Dom;
  analysis_step : Dom -> Dom;
  initial_value : Dom;
  initial_value_bottom : forall d, poLe initial_value d;
  finite_height : Terminating Dom poLt;
  step_monotone : Monotone analysis_step
}.

Local Hint Extern 5 =>
match goal with
  [ H : poLe ?d ?d' |- poLe (analysis_step ?d) (analysis_step ?d')] =>
  eapply (step_monotone _ _ H)
end.

Section AnalysisAlgorithm.
  Variable Dom : Type.
  Variable analysis : Analysis Dom.

  Fixpoint safeFirst (d:Dom) (mon:poLe d (analysis_step d)) (trm:terminates poLt d)
    : { d' : Dom | exists n : nat, d' = iter n d (fun _ => analysis_step) /\ poEq (analysis_step d') d' }.
    decide (poLe (analysis_step d) d).
    - eexists (analysis_step d), 1; simpl.
      split; eauto.
      eapply poLe_antisymmetric; eauto.
    - destruct (safeFirst (analysis_step d)) as [d' H]; [ eauto | |].
      + destruct trm. eapply H.
        eapply poLe_poLt; eauto.
      + eexists d'. destruct H as [n' H]. eexists (S n'); simpl. eauto.
  Defined.

  Definition safeFixpoint
    : { d' : Dom | exists n : nat, d' = iter n initial_value (fun _ => analysis_step)
                            /\ poEq (analysis_step d') d' }.
    eapply @safeFirst.
    - eapply initial_value_bottom.
    - eapply finite_height.
  Defined.

End AnalysisAlgorithm.


Inductive anni (A:Type) : Type :=
| anni0 : anni A
| anni1 (a1:A) : anni A
| anni2 (a1:A) (a2:A) : anni A
| anni2opt (a1:option A) (a2:option A) : anni A.

Arguments anni0 [A].


Fixpoint setAnni {A} (a:ann A) (ai:anni A) : ann A :=
  match a, ai with
    | ann1 a an, anni1 a1 => ann1 a (setTopAnn an a1)
    | ann2 a an1 an2, anni2 a1 a2 => ann2 a (setTopAnn an1 a1) (setTopAnn an2 a2)
    | an, _ => an
  end.

Inductive anni_R A B (R : A -> B -> Prop) : anni A -> anni B -> Prop :=
| anni_R0
  : anni_R R anni0 anni0
| anni_R1 a1 a2
  : R a1 a2 -> anni_R R (anni1 a1) (anni1 a2)
| anni_R2 a1 a1' a2 a2'
  : R a1 a2 -> R a1' a2' -> anni_R R (anni2 a1 a1') (anni2 a2 a2')
| anni_R2o o1 o1' o2 o2'
  : option_R R o1 o2 -> option_R R o1' o2' -> anni_R R (anni2opt o1 o1') (anni2opt o2 o2').

Instance anni_R_refl {A} {R} `{Reflexive A R} : Reflexive (anni_R R).
Proof.
  hnf; intros; destruct x; eauto using anni_R, option_R.
  econstructor; reflexivity.
Qed.

Instance anni_R_sym {A} {R} `{Symmetric A R} : Symmetric (anni_R R).
Proof.
  hnf; intros. inv H0; eauto using anni_R.
  econstructor; symmetry; eauto.
Qed.

Instance anni_R_trans A R `{Transitive A R} : Transitive (anni_R R).
Proof.
  hnf; intros ? ? ? B C.
  inv B; inv C; econstructor; eauto.
  - etransitivity; eauto.
  - etransitivity; eauto.
Qed.

Instance anni_R_equivalence A R `{Equivalence A R} : Equivalence (anni_R R).
Proof.
  econstructor; eauto with typeclass_instances.
Qed.

Instance anni_R_anti A R Eq `{EqA:Equivalence _ Eq} `{@Antisymmetric A Eq EqA R}
  : @Antisymmetric _ (anni_R Eq) _ (anni_R R).
Proof.
  intros ? ? B C. inv B; inv C; eauto using anni_R.
  econstructor; eapply option_R_anti; eauto.
Qed.

Instance anni_R_dec A B (R:A->B->Prop)
         `{forall a b, Computable (R a b)} (a:anni A) (b:anni B) :
  Computable (anni_R R a b).
Proof.
  destruct a,b; try dec_solve.
  - decide (R a1 a0); dec_solve.
  - decide (R a1 a0); decide (R a2 a3); dec_solve.
  - decide (option_R R a1 a0); decide (option_R R a2 a3); dec_solve.
Defined.

Instance PartialOrder_ann Dom `{PartialOrder Dom}
: PartialOrder (anni Dom) := {
  poLe := anni_R poLe;
  poLe_dec := @anni_R_dec _ _ poLe poLe_dec;
  poEq := anni_R poEq;
  poEq_dec := @anni_R_dec _ _ poEq poEq_dec;
}.
Proof.
  - intros. inv H0; eauto 20 using @anni_R, poLe_refl.
    econstructor; eapply (@poLe_refl _ (PartialOrder_option Dom)); eauto.
Defined.

Inductive option_Rs A B (R: A -> B -> Prop) : option A -> B -> Prop :=
| option_R_None b : option_Rs R None b
| option_R_Some a b : R a b -> option_Rs R (Some a) b.


Instance PartialOrder_anni Dom `{PartialOrder Dom}
: PartialOrder (anni Dom) := {
  poLe := anni_R poLe;
  poLe_dec := @anni_R_dec _ _ poLe poLe_dec;
  poEq := anni_R poEq;
  poEq_dec := @anni_R_dec _ _ poEq poEq_dec;
}.
Proof.
  - intros. inv H0; eauto 20 using @anni_R, poLe_refl.
    econstructor; eapply (@poLe_refl _ (PartialOrder_option Dom)); eauto.
Defined.

Instance option_Rs_dec A B (R:A->B->Prop)
         `{forall a b, Computable (R a b)} (a:option A) (b:B) :
  Computable (option_Rs R a b).
Proof.
  destruct a; try dec_solve.
  decide (R a b); dec_solve.
Defined.

Inductive anni_Rs A B (R : A -> B -> Prop) : anni A -> B -> Prop :=
| anni_Rs0 b
  : anni_Rs R anni0 b
| anni_Rs1 a1 b
  : R a1 b -> anni_Rs R (anni1 a1) b
| anni_Rs2 a1 a2 b
  : R a1 b -> R a2 b -> anni_Rs R (anni2 a1 a2) b
| anni_Rs2o o1 o2 b
  : option_Rs R o1 b -> option_Rs R o2 b -> anni_Rs R (anni2opt o1 o2) b.

Instance anni_Rs_dec A B (R:A->B->Prop)
         `{forall a b, Computable (R a b)} (a:anni A) (b:B) :
  Computable (anni_Rs R a b).
Proof.
  destruct a; try dec_solve.
  - decide (R a1 b); dec_solve.
  - decide (R a1 b); decide (R a2 b); dec_solve.
  - decide (option_Rs R a1 b); decide (option_Rs R a2 b); dec_solve.
Defined.

Require Import Keep Subterm.

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
  destruct F as [|[Z s] F'], anF as [|a anF'].
  - eapply nil.
  - eapply nil.
  - eapply nil.
  - econstructor 2.
    refine (backward ZL AL s _ a).
    eapply (ST 0 (Z, s)); eauto using get.
    eapply (g F' anF').
    eauto using get.
Defined.

Arguments backwardF [sT] [Dom] backward ZL AL F anF ST : clear implicits.

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
  destruct F as [|[Z s] F'], anF; simpl; eauto.
Qed.

Lemma backwardF_length_ass sT (Dom:stmt->Type)
      backward ZL (AL:list (Dom sT)) F anF ST k
  : length F = k
    -> length F = length anF
    -> length (backwardF backward ZL AL F anF ST) = k.
Proof.
  intros. rewrite backwardF_length, <- H0, Nat.min_idempotent; eauto.
Qed.

Lemma min_idempotent_ass n m k
  : n = k
    -> n = m
    -> min n m = k.
Proof.
  intros. repeat subst. eapply Nat.min_idempotent.
Qed.

Hint Resolve backwardF_length_ass min_idempotent_ass.

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

    | stmtExtern x f Y s as st, ann1 d ans =>
      fun EQ =>
        let ans' := backward Dom btransform ZL AL
                            (subTerm_EQ_Extern EQ ST) ans in
        let ai := anni1 (getAnn ans') in
        let d' := btransform sT ZL AL st ST ai in
        ann1 d' ans'

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

Ltac btransform t H :=
  match goal with
  | [ |- poLe ?a (t ?AL ?s ?d) ] =>
    let LE := fresh "LE" in
    let A := fresh "LE" in
    let B := fresh "LE" in
    pose proof (H AL s d) as LE; inversion LE as [A|A B|A B|A B]; subst; clear LE;
    rename B into LE; rewrite <- LE
  end.

Lemma tab_false_impb Dom `{PartialOrder Dom} AL AL'
  : poLe AL AL'
    -> PIR2 impb (tab false ‖AL‖) (tab false ‖AL'‖).
Proof.
  intros. hnf in H0.
  general induction H0; simpl; unfold impb; eauto using @PIR2.
Qed.

Lemma zip_orb_impb Dom `{PartialOrder Dom} AL AL' BL BL'
  : poLe AL AL'
    -> poLe BL BL'
    -> PIR2 impb (orb ⊜ AL BL) (orb ⊜ AL' BL').
Proof.
  unfold poLe; simpl.
  intros A B.
  general induction A; inv B; simpl; eauto using PIR2.
  - econstructor; eauto.
    unfold impb. destruct x, x0, y, y0; simpl in *; eauto.
Qed.

Lemma update_at_impb Dom `{PartialOrder Dom} AL AL' n
  : poLe AL AL'
    ->  PIR2 impb (list_update_at (tab false ‖AL‖) n true)
            (list_update_at (tab false ‖AL'‖) n true).
Proof.
  unfold poLe; simpl.
  intros A. general induction A; simpl; eauto using PIR2.
  - unfold impb. destruct n; simpl; eauto using @PIR2, tab_false_impb.
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

Ltac inv_get_step1 dummy := first [inv_get_step |
                            match goal with
                            | [ H: get (backwardF ?f ?ZL ?AL ?F ?anF ?ST) ?n ?x |- _ ]
                              => eapply backwardF_get in H;
                                destruct H as [? [? [? [? [? ]]]]]
                            end
                           ].

Tactic Notation "inv_get_step" := inv_get_step1.
Tactic Notation "inv_get" := inv_get' inv_get_step1.

(*
Lemma backward_length sT (Dom:stmt -> Type) `{PartialOrder (Dom sT)}
      (f: forall sT, list params -> list (Dom sT) ->
                forall s, subTerm s sT -> anni (Dom sT) -> Dom sT)
      s b (Ann:annotation s b) (ST:subTerm s sT)
  : forall ZL AL, length (backward Dom f ZL AL ST b) = length AL.
Proof.
  induction Ann; intros; simpl; eauto with len.
  - rewrite zip_length2; eauto. rewrite IHAnn1, IHAnn2; eauto.
  - rewrite list_update_at_length; eauto with len.
  - rewrite length_drop_minus. rewrite fold_list_length; eauto.
    + rewrite IHAnn.
      rewrite app_length. repeat rewrite map_length; eauto.
      rewrite backwardF_length; eauto.
      rewrite H0. rewrite Nat.min_idempotent. omega.
    + intros; inv_get.
      rewrite IHAnn. rewrite app_length. repeat rewrite map_length; eauto.
      rewrite backwardF_length; eauto; simpl.
      erewrite H2; eauto.
      rewrite app_length, map_length. rewrite H0.
      rewrite Nat.min_idempotent. omega.
    + intros; inv_get; eauto with len.
      cases; eauto.
      rewrite zip_length. rewrite min_l; eauto.
Qed.
 *)

Lemma PIR2_impb_orb A A' B B'
  : PIR2 impb A A'
    -> PIR2 impb B B'
    -> PIR2 impb (orb ⊜ A B) (orb ⊜ A' B').
Proof.
  intros AA BB. general induction AA; inv BB; simpl; eauto using @PIR2.
  econstructor; eauto.
  destruct x, x0, y, y0; inv pf0; simpl; eauto.
Qed.

Lemma PIR2_impb_orb_right A A' B
  : length A <= length B
    -> PIR2 impb A A'
    -> PIR2 impb A (orb ⊜ A' B).
Proof.
  intros LEN AA.
  general induction AA; destruct B; simpl in *; isabsurd; eauto using @PIR2.
  econstructor; eauto.
  destruct x, y, b; inv pf; simpl; eauto.
  eapply IHAA; eauto. omega.
Qed.

Lemma PIR2_impb_fold (A A':list (list bool * bool)) (B B':list bool)
  : poLe A A'
    -> poLe B B'
    -> (forall n a, get A n a -> length B <= length (fst a))
    -> poLe (fold_left (fun a (b:list bool * bool) => if snd b then orb ⊜ a (fst b) else a) A B)
           (fold_left (fun a (b:list bool * bool) => if snd b then orb ⊜ a (fst b) else a) A' B').
Proof.
  intros. simpl in *.
  general induction H; simpl; eauto.
  eapply IHPIR2; eauto using PIR2_impb_orb.
  dcr. hnf in H2.
  repeat cases; try congruence; isabsurd; eauto using PIR2_impb_orb, PIR2_impb_orb_right.
  eapply PIR2_impb_orb_right; eauto using get.
  rewrite <- (PIR2_length H2); eauto. eauto using get.
  intros. cases; eauto using get.
  rewrite zip_length3; eauto using get.
Qed.

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
  - econstructor; eauto.
    + eapply fMon; eauto.
      econstructor.
      eapply getAnn_poLe. eapply (IH s); eauto.
    + eapply IH; eauto.
  - assert (AL'LE:getAnn ⊝ ans ++ AL ⊑ getAnn ⊝ bns ++ AL'). {
      eapply PIR2_app; eauto.
      eapply PIR2_get; intros; inv_get.
      eapply getAnn_poLe. eapply H2; eauto. eauto with len.
    }
    assert (getAnn
              ⊝ backwardF (backward Dom f) (fst ⊝ s ++ ZL) (getAnn ⊝ ans ++ AL) s ans
              (subTerm_EQ_Fun2 eq_refl ST) ++ AL
              ⊑ getAnn
              ⊝ backwardF (backward Dom f) (fst ⊝ s ++ ZL) (getAnn ⊝ bns ++ AL') s bns
              (subTerm_EQ_Fun2 eq_refl ST) ++ AL'). {
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 20 with len; intros; inv_get.
      eapply getAnn_poLe.
      assert (x5 = x10) by eapply subTerm_PI; subst.
      eapply IH; eauto.
      exploit H2; eauto.
    }
    econstructor; eauto.
    + eapply fMon; eauto.
      econstructor; eauto.
      eapply getAnn_poLe. eapply IH; eauto.
    + eauto 30 with len.
    + intros; inv_get.
      assert (x8 = x3) by eapply subTerm_PI; subst.
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
  - econstructor; eauto.
    + eapply fMon; eauto.
      econstructor.
      eapply getAnn_poEq. eapply (IH s); eauto.
    + eapply IH; eauto.
  - assert (AL'LE:getAnn ⊝ ans ++ AL ≣ getAnn ⊝ bns ++ AL'). {
      eapply PIR2_app; eauto.
      eapply PIR2_get; intros; inv_get.
      eapply getAnn_poEq. eapply H2; eauto. eauto with len.
    }
    assert (getAnn
              ⊝ backwardF (backward Dom f) (fst ⊝ s ++ ZL) (getAnn ⊝ ans ++ AL) s ans
              (subTerm_EQ_Fun2 eq_refl ST) ++ AL
              ≣ getAnn
              ⊝ backwardF (backward Dom f) (fst ⊝ s ++ ZL) (getAnn ⊝ bns ++ AL') s bns
              (subTerm_EQ_Fun2 eq_refl ST) ++ AL'). {
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 20 with len; intros; inv_get.
      eapply getAnn_poEq.
      assert (x5 = x10) by eapply subTerm_PI; subst.
      eapply IH; eauto.
      exploit H2; eauto.
    }
    econstructor; eauto.
    + eapply fMon; eauto.
      econstructor; eauto.
      eapply getAnn_poEq. eapply IH; eauto.
    + eauto 30 with len.
    + intros; inv_get.
      assert (x8 = x3) by eapply subTerm_PI; subst.
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

Lemma ann_bottom s' (Dom:Type) `{BoundedSemiLattice Dom}
  :  forall (d : ann Dom), annotation s' d -> setAnn bottom s' ⊑ d.
Proof.
  sind s'; destruct s'; simpl; intros d' Ann; inv Ann; simpl; eauto using @ann_R, bottom_least.
  - econstructor; eauto using bottom_least.
    eapply (IH s'); eauto.
  - econstructor; eauto using bottom_least.
    eapply IH; eauto.
    eapply IH; eauto.
  - econstructor. eauto using bottom_least.
    eapply IH; eauto.
  - econstructor; eauto using bottom_least with len.
    + intros; inv_get. eapply IH; eauto.
    + eapply IH; eauto.
Qed.


Instance makeBackwardAnalysis (Dom:stmt -> Type)
         `{forall s, PartialOrder (Dom s) }
         (BSL:forall s, BoundedSemiLattice (Dom s))
         (f: forall sT, list params -> list (Dom sT) ->
                   forall s, subTerm s sT -> anni (Dom sT) -> Dom sT)
         (fMon:forall sT s (ST:subTerm s sT) ZL AL AL',
             poLe AL AL' ->
             forall a b, a ⊑ b -> f sT ZL AL s ST a ⊑ f sT ZL AL' s ST b)
         (Trm: forall s, Terminating (Dom s) poLt)
  : forall s, Analysis { a : ann (Dom s) | annotation s a } :=
  {
    analysis_step := fun X : {a : ann (Dom s) | annotation s a} =>
                      let (a, Ann) := X in
                      exist (fun a0 : ann (Dom s) => annotation s a0)
                            (backward Dom f nil nil (subTerm_refl _) a) (backward_annotation Dom f nil nil (subTerm_refl _) Ann);
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

(*
Definition forwardF Dom
           (forward : forall (st:stmt) (a:list (params * Dom) * ann Dom), list (params * Dom) * ann Dom)

  := fix f (F:list (params * stmt)) (annF: list (ann Dom)) (AL:list (params * Dom)) :=
      match F, annF with
      | (Z, s)::F', ans::annF' => let (AL', annF'') := f F' annF' AL in
                                 let (ALs, ans') := forward s (AL', ans) in
                                 (ALs, ans'::annF'')
      | _, _ => (AL, nil)
      end.

Definition forward Dom
         (ftransform : (list (params * Dom) * ann Dom) -> stmt -> (list (params * Dom) * anni Dom)) :=
  fix forward
      (st:stmt) (a:list (params *Dom) * ann Dom) {struct st}
: list (params * Dom) * ann Dom :=
  match st, a with
    | stmtLet x e s as st, (AL, ann1 d ans) as ann =>
      let (AL', ai) := (ftransform ann st) in
      forward s (AL', setAnni ans ai)
    | stmtIf x s t as st, (AL, ann2 d ans ant) as ann =>
      let (AL, ai) := (ftransform ann st) in
      let (AL', ans') := forward s (AL, setAnni ans ai) in
      let (AL'', ant') := forward t (AL', setAnni ant ai) in
      (AL'', ann2 d ans' ant')
    | stmtApp f Y as st, (AL, ann0 d as an) as ann =>
      let (AL', ai) := ftransform ann st in
      (AL', an)
    | stmtReturn x as st, (AL, ann0 d as an) as ann =>
      let (AL', ai) := ftransform ann st in
      (AL', an)
    | stmtExtern x f Y s as st, (AL, ann1 d ans) as ann =>
      let (AL, ai) := (ftransform ann st) in
      forward s (AL, setAnni ans ai)
    | stmtFun F t as st, (AL, annF d anF ant) as ann =>
      match ftransform ann st with
      | (AL', anniF _ dt') =>
        let (ALt', ant') := forward t (AL', setTopAnn ant dt') in
        let anF' := zip (fun a Zann => setTopAnn a (snd Zann)) anF ALt' in
        let (AL'', anF'') := forwardF forward F anF' ALt' in
        (drop (length F) AL', annF d anF'' ant')
      |  _ => ann
      end
    | _, an => an
  end.
*)



(*
Definition makeForwardAnalysis Dom (BSL:BoundedSemiLattice Dom)
         (ftransform : (list (params * Dom) * ann Dom) -> stmt -> (list (params * Dom) * anni Dom))
: Analysis (ann Dom) :=
makeAnalysis _ (fun s d => Success (snd (forward ftransform s (nil, d)))) (fun s => setAnn s bottom).
 *)

(*
Module SSA.


Definition forwardF Dom
           (forward : forall (st:stmt) (a:list (params * Dom) * Dom),
               status (list (params * Dom) * Dom))

  := fix f (F:list (params * stmt)) (AL:list (params * Dom)) (d: Dom) :=
      match F with
      | (Z, s)::F' => sdo AL'd' <- f F' AL d;
                                 sdo ALsans' <- forward s (fst AL'd', snd AL'd');
                                 Success (fst ALsans', snd ALsans')
      | nil => Success (AL, d)
      end.

  Definition forward Dom {BSL:BoundedSemiLattice Dom}
             (ftransform : stmt -> (list (params * Dom) * Dom) -> (list (params * Dom) * anni Dom)) :=
    fix forward
        (st:stmt) (a:list (params * Dom) * Dom) {struct st}
    : status (list (params * Dom) * Dom) :=
    match st, a with
    | stmtLet x e s as st, (AL, d) =>
      match ftransform st (AL, d) with
      | (AL, anni1 a) => forward s (AL, a)
      | _ => Error "expression transformer failed"
      end
    | stmtIf x s t as st, (AL, d) =>
      match ftransform st (AL, d) with
      | (AL, anni2opt (Some a1) (Some a2)) =>
        sdo ALds <- forward s (AL, a1);
          sdo ALdt <- forward t (fst ALds, a2);
          Success (fst ALdt, join (snd ALds) (snd ALdt))
      | (AL, anni2opt None (Some a2)) =>
        forward t (AL, a2)
      | (AL, anni2opt (Some a1) None) =>
        forward s (AL, a1)
      | _ => Error "condition transformer failed"
      end
    | stmtApp f Y as st, (AL, d) =>
      match ftransform st (AL, d) with
      | (AL, anni1 a) => Success (AL, a)
      | _ => Error "tailcall transformer failed"
      end
    | stmtReturn x as st, (AL, d) =>
      match ftransform st (AL, d) with
      | (AL, anni1 a) => Success (AL, a)
      | _ => Error "return transformer failed"
      end
    | stmtExtern x f Y s as st, (AL, d) =>
      match ftransform st (AL, d) with
      | (AL, anni1 a) => forward s (AL, a)
      | _ => Error "syscall transformer failed"
      end
    | stmtFun F t as st, (AL, d) =>
      match ftransform st (AL, d) with
      | (AL', anniF _ a2) =>
        sdo ALdt <- forward t (AL', a2);
          sdo ALdF <- forwardF forward F (fst ALdt) (snd ALdt);
            Success (drop (length F) (fst ALdF), snd ALdF)
      | _ => Error "function binding transformer failed"
      end
    end.


(*
Lemma forward_FunDom_length Dom {BSL:BoundedSemiLattice Dom} FunDom
         (ftransform : stmt -> (list FunDom * Dom) -> (list FunDom * anni Dom))
         (fmkFunDom : params -> Dom -> FunDom)
         s (AL:list FunDom) (a:Dom) r
 : forward ftransform fmkFunDom s (AL, a) = Success r
   -> length AL = length (fst r).
Proof.
  general induction s; simpl in H.
  let_case_eq.
Qed.
*)

(*
Definition forward Dom FunDom
         (ftransform : stmt -> (list FunDom * Dom) -> (list FunDom * Dom))
         (fmkFunDom : params -> Dom -> FunDom) :=
  fix forward
      (st:stmt) (a:list FunDom * Dom) {struct st}
: list FunDom * Dom :=
  match st, a with
    | stmtLet x e s as st, (AL, d) =>
      forward s (ftransform st (AL, d))
    | stmtIf x s t as st, (AL, d) =>
      forward t (forward s (ftransform st (AL, d)))
    | stmtApp f Y as st, (AL, d) =>
      ftransform st (AL, d)
    | stmtReturn x as st, (AL, d) =>
      ftransform st (AL, d)
    | stmtExtern x f Y s as st, (AL, d) =>
      forward s (ftransform st (AL, d))
    | stmtFun Z s t as st, (AL, d) =>
      forward t (forward s( ftransform st (fmkFunDom Z d::AL, d)))
  end.
*)

  Instance Dom_params_semilattice Dom `{PartialOrder Dom} : PartialOrder (params * Dom) :=
    {
      poLe p p' := fst p = fst p' /\ poLe (snd p) (snd p');
      poLe_dec := _;
      poEq p p' := fst p = fst p' /\ poEq (snd p) (snd p');
      poEq_dec := _
    }.

Definition makeForwardAnalysis Dom (BSL:BoundedSemiLattice Dom)
         (ftransform : stmt -> (list (params * Dom) * Dom) -> (list (params * Dom) * anni Dom))
: Analysis (list (params * Dom) * Dom) :=
makeAnalysis _ (fun s d => forward ftransform s d) (fun s => (nil, bottom)).


(*
Definition makeBackwardAnalysis Dom FunDom (BSL:BoundedSemiLattice Dom)
           (btransform : list FunDom -> stmt -> anni Dom -> Dom)
           (bmkFunDom : params -> ann Dom -> FunDom)
: Analysis Dom :=
makeAnalysis _
             (fun s d => backward btransform bmkFunDom s nil d)
             (fun s => setAnn s bottom).
*)

End SSA.
*)