Require Import CSet Le ListUpdateAt Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Terminating.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve LengthEq MoreList Status AllInRel OptionR.

Set Implicit Arguments.

(** Specification of an analysis and generic fixpoint iteration algorithm *)

Class Monotone Dom `{PartialOrder Dom} Dom' `{PartialOrder Dom'} (f:Dom->Dom') :=
  monotone : forall a b, poLe a b -> poLe (f a) (f b).

Class Analysis (Dom: stmt -> Type) := makeAnalysis {
  dom_po :> forall sT, PartialOrder (Dom sT);
  analysis_step : forall sT, stmt -> Dom sT -> Dom sT;
  initial_value : forall sT, Dom sT;
  initial_value_bottom : forall s d, poLe (initial_value s) d;
  finite_height : forall (sT:stmt), Terminating (Dom sT) poLt;
  step_monotone : forall sT s, Monotone (@analysis_step sT s)
}.

Hint Extern 5 =>
match goal with
  [ H : poLe ?d ?d' |- poLe (analysis_step _ ?s ?d) (analysis_step _ ?s ?d')] =>
  eapply (step_monotone _ s _ _ H)
end.

Section AnalysisAlgorithm.
  Variable Dom : stmt -> Type.
  Variable analysis : Analysis Dom.

  Fixpoint safeFirst (sT s:stmt) (d:Dom sT) (mon:poLe d (analysis_step sT s d)) (trm:terminates poLt d)
    : { d' : Dom sT | exists n : nat, d' = iter n d (fun _ => analysis_step sT s) /\ poEq (analysis_step sT s d') d' }.
    decide (poLe (analysis_step sT s d) d).
    - eexists (analysis_step sT s d), 1; simpl.
      split; eauto.
      eapply poLe_antisymmetric; eauto.
    - destruct (safeFirst sT s (analysis_step sT s d)) as [d' H]; [ eauto | |].
      + destruct trm. eapply H.
        eapply poLe_poLt; eauto.
      + eexists d'. destruct H as [n' H]. eexists (S n'); simpl. eauto.
  Defined.

  Definition safeFixpoint (s:stmt)
    : { d' : Dom s | exists n : nat, d' = iter n (initial_value s) (fun _ => analysis_step s s)
                            /\ poEq (analysis_step s s d') d' }.
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

Require Import Keep.

Definition ifb (b b':bool) := if b then b' else false.

Definition backward Dom
           (btransform : list params -> list (option Dom) -> stmt -> anni (option Dom) -> option Dom) :=
  fix backward
      (ZL:list (params)) (AL:list (option Dom)) (st:stmt) (a:ann (option Dom)) {struct st}
  : ann (option Dom) * list bool :=
  match st, a with
    | stmtLet x e s as st, ann1 d ans =>
      let ans' := backward ZL AL s ans in
      let ai := anni1 (getAnn (fst ans')) in
      let d := (btransform ZL AL st ai) in
      (ann1 d (fst ans'), snd ans')

    | stmtIf x s t as st, ann2 d ans ant =>
      let ans' := backward ZL AL s ans in
      let ant' := backward ZL AL t ant in
      let ai := anni2 (getAnn (fst ans')) (getAnn (fst ant')) in
      let d' := (btransform ZL AL st ai) in
      (ann2 d' (fst ans') (fst ant'), zip orb (snd ans') (snd ant'))

    | stmtApp f Y as st, ann0 d as an =>
      (ann0 (btransform ZL AL st anni0),
       list_update_at (List.map (fun _ => false) AL) (counted f) true)

    | stmtReturn x as st, ann0 d as an =>
      (ann0 (btransform ZL AL st anni0), List.map (fun _ => false) AL)

    | stmtExtern x f Y s as st, ann1 d ans =>
      let ans' := backward ZL AL s ans in
      let ai := anni1 (getAnn (fst ans')) in
      let d' := (btransform ZL AL st ai) in
      (ann1 d' (fst ans'), snd ans')

    | stmtFun F t as st, annF d anF ant =>
      let ALinit := getAnn ⊝ anF ++ AL in
      let ZL' := List.map fst F ++ ZL in
      let anF' := zip (fun Zs => backward ZL' ALinit (snd Zs)) F anF in
      let AL' := getAnn ⊝ (fst ⊝ anF') ++ AL in
      let ant' := backward ZL' AL' t ant in
      let ai := anni1 (getAnn (fst ant')) in
      let d' := btransform ZL' AL' st ai in
      let cll := fold_left (fun ant ans => zip ifb ant ans) (snd ⊝ anF') (snd ant') in
      (annF d' (zip (fun (b:bool) a => if b then a else setTopAnn a None ) cll (fst ⊝ anF')) (fst ant'),
       cll)
    | _, an => (an, List.map (fun x => false) AL)
  end.


Ltac btransform t H :=
  match goal with
  | [ |- poLe ?a (t ?AL ?s ?d) ] =>
    let LE := fresh "LE" in
    let A := fresh "LE" in
    let B := fresh "LE" in
    pose proof (H AL s d) as LE; inversion LE as [A|A B|A B|A B]; subst; clear LE;
    rename B into LE; rewrite <- LE
  end.

Instance getAnn_poLe Dom `{PartialOrder Dom}
  : Proper (poLe ==> poLe) getAnn.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl; eauto.
Qed.

Definition impb (a b:bool) : Prop := if a then b else True.

Instance PartialOrder_bool
: PartialOrder bool := {
  poLe := impb;
  poLe_dec := _;
  poEq := eq;
  poEq_dec := _;
}.
Proof.
  - intros. unfold impb. hnf. destruct d, d'; try dec_solve; eauto.
  - hnf; unfold impb. intros. destruct d,d'; simpl; eauto using bool.
    congruence.
  - hnf; unfold impb. intros. destruct x,y,z; simpl; eauto.
  - hnf; unfold impb. intros. destruct x,y; eauto. exfalso; eauto.
Defined.

Instance implbb_refl : Reflexive impb.
Proof.
  hnf; destruct x; simpl; eauto.
Qed.

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

Hint Extern 5 (Is_true true) => eapply I.

Lemma update_at_impb Dom `{PartialOrder Dom} AL AL' n
  : poLe AL AL'
    ->  PIR2 impb (list_update_at (tab false ‖AL‖) n true)
            (list_update_at (tab false ‖AL'‖) n true).
Proof.
  unfold poLe; simpl.
  intros A. general induction A; simpl; eauto using PIR2.
  - unfold impb. destruct n; simpl; eauto using @PIR2, tab_false_impb.
Qed.

Lemma backward_monotone Dom `{PartialOrder Dom}
      (f : list params -> list (option Dom) -> stmt -> anni (option Dom) -> option Dom)
      (fMon:forall s ZL AL AL', poLe AL AL' ->
                           forall a b, a ⊑ b -> f ZL AL s a ⊑ f ZL AL' s b)
  : forall (s : stmt) ZL AL AL',
    poLe AL AL' ->
    forall a b : ann (؟ Dom), a ⊑ b -> backward f ZL AL s a ⊑ backward f ZL AL' s b.
Proof.
  intros s.
  sind s; destruct s; intros ZL AL AL' ALLE d d' LE; simpl; inv LE; simpl;
    eauto 10 using @ann_R, tab_false_impb, update_at_impb, zip_orb_impb.
  - split; eauto. econstructor; eauto.
    + eapply fMon; eauto.
      econstructor.
      eapply getAnn_poLe. eapply (IH s); eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
  - split. econstructor; eauto.
    + eapply fMon; eauto.
      econstructor; eapply getAnn_poLe.
      eapply (IH s1); eauto.
      eapply (IH s2); eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
    + eapply zip_orb_impb; eauto.
      eapply IH; eauto.
      eapply IH; eauto.
  - split. econstructor; eauto.
    + eapply fMon; eauto.
    + eapply update_at_impb; eauto.
  - split; eauto using tab_false_impb.
    + econstructor; eapply fMon; eauto.
  - split; eauto. econstructor; eauto.
    + eapply fMon; eauto.
      econstructor.
      eapply getAnn_poLe. eapply (IH s); eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
  - assert ( getAnn
               ⊝ fst
               ⊝ (fun Zs : params * stmt => backward f (fst ⊝ s ++ ZL) (getAnn ⊝ ans ++ AL) (snd Zs)) ⊜ s ans ++ AL
               ⊑ getAnn
               ⊝ fst
               ⊝ (fun Zs : params * stmt => backward f (fst ⊝ s ++ ZL) (getAnn ⊝ bns ++ AL') (snd Zs)) ⊜ s
               bns ++ AL'). {
      eapply PIR2_app; eauto.
      eapply PIR2_get; intros; inv_get.
      eapply getAnn_poLe. eapply IH; eauto.
      eapply PIR2_app; eauto.
      eapply PIR2_get; intros; inv_get; try eapply getAnn_poLe; eauto with len.
      exploit H2; eauto. eapply H2; eauto.
      repeat rewrite map_length.
      repeat rewrite zip_length2; eauto.
      admit. admit.
    }
    simpl; split.
    + econstructor; eauto.
      * eapply fMon; eauto.
        econstructor.
        eapply getAnn_poLe. eapply IH; eauto.
      * repeat rewrite zip_length2; eauto. admit.
        admit. admit.
      * intros; inv_get. admit.
      * eapply IH; eauto.
    + admit.
Admitted.

Lemma backward_annotation Dom `{PartialOrder Dom} s
      (f : list params -> list (option Dom) -> stmt -> anni (option Dom) -> option Dom)
  : forall ZL AL sT a, annotation sT a
                  -> annotation sT (fst (backward f ZL AL s a)).
Proof.
  sind s; intros ZL AL sT a Ann; destruct s; inv Ann; simpl; eauto using @annotation.
  - econstructor; eauto.
    + rewrite zip_length2; eauto.
      admit. admit.
    + intros. inv_get.
      destruct x.
      * eapply IH; eauto.
      * eapply setTopAnn_annotation.
        eapply IH; eauto.
Admitted.



Instance PartialOrder_sig Dom `{PartialOrder Dom} (P:Dom -> Prop)
: PartialOrder { x :Dom | P x } := {
  poLe x y := poLe (proj1_sig x) (proj1_sig y);
  poLe_dec := _;
  poEq x y := poEq (proj1_sig x) (proj1_sig y);
  poEq_dec := _;
}.
Proof.
  - econstructor; hnf; intros; destruct x; try destruct y; try destruct z; simpl in *.
    + reflexivity.
    + symmetry; eauto.
    + etransitivity; eauto.
  - intros [a b] [c d]; simpl. eapply poLe_refl.
  - intros [a b] [c d] [e f]; simpl; intros.
    etransitivity; eauto.
  - intros [a b] [c d]; simpl; intros.
    eapply poLe_antisymmetric; eauto.
Defined.


Lemma terminating_sig Dom `{PO:PartialOrder Dom}
  : Terminating Dom poLt
    -> forall P, Terminating { x : Dom | P x } poLt.
Proof.
  intros Trm P [x Px].
  specialize (Trm x).
  induction Trm.
  econstructor.
  intros [y Py] [LE NEQ]; simpl in *.
  eapply H0. split; eauto.
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
         `{forall s, PartialOrder (Dom s)} (BSL:forall s, BoundedSemiLattice (option (Dom s)))
         (f :forall s, list params -> list (option (Dom s)) -> stmt -> anni (option (Dom s)) -> option (Dom s))
         (fMon:forall (s s':stmt) ZL AL AL', poLe AL AL' ->
                                        forall a b, a ⊑ b -> f s ZL AL s' a ⊑ f s ZL AL' s' b)
         (Trm: forall s, Terminating (Dom s) poLt)
  : Analysis (fun s => { a : ann (option (Dom s)) | annotation s a }) :=
             {
               initial_value :=  fun s : stmt =>
                  exist (fun a : ann (؟ (Dom s)) => annotation s a) (setAnn bottom s)
                    (setAnn_annotation bottom s)
             }.
Proof.
  - intros s' s [a Ann].
    exists (fst (backward (f s') nil nil s a)).
    eapply backward_annotation; eauto.
  - intros ? [d Ann]; simpl.
    pose proof (@ann_bottom s (option (Dom s)) _ _ _ Ann).
    eapply H0.
  - intros. eapply terminating_sig.
    eapply terminating_ann. eapply terminating_option. eauto.
  - intros s s' [a Ann] [b Bnn] LE; simpl in *.
    eapply (backward_monotone (f s) (fMon s)); eauto.
Qed.

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