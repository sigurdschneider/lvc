Require Import CSet Le ListUpdateAt Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Terminating.
Require Import Val Var Env IL Annotation Lattice DecSolve LengthEq MoreList Status AllInRel OptionR.

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
    : { d' : Dom | exists n : nat, d' = iter n d analysis_step /\ poEq (analysis_step d') d' }.
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
    : { d' : Dom | exists n : nat, d' = iter n initial_value analysis_step
                            /\ poEq (analysis_step d') d' }.
    eapply @safeFirst.
    - eapply initial_value_bottom.
    - eapply finite_height.
  Defined.

  Lemma safeFixpoint_chain n
    : iter n initial_value analysis_step
           ⊑ iter (S n) initial_value analysis_step.
  Proof.
    induction n.
    - simpl. eapply initial_value_bottom.
    - do 2 rewrite iter_comm.
      eapply step_monotone. eauto.
  Qed.

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

Definition mapAnni {A B} (f:A -> B) (ai:anni A) : anni B :=
  match ai with
    | anni0 => anni0
    | anni1 a1 => anni1 (f a1)
    | anni2 a1 a2 => anni2 (f a1) (f a2)
    | anni2opt o1 o2 => anni2opt (mapOption f o1) (mapOption f o2)
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


Definition getAnni A (a:A) (an:anni A) :=
  match an with
  | anni1 a => a
  | _ => a
  end.

Lemma poLe_getAnni A `{PartialOrder A} (a a':A) an an'
  : poLe a a'
    -> poLe an an'
    -> poLe (getAnni a an) (getAnni a' an').
Proof.
  intros LE LE'; inv LE'; simpl; eauto.
Qed.

Definition getAnniLeft A (a:A) (an:anni A) :=
  match an with
  | anni2 a _ => a
  | _ => a
  end.

Lemma poLe_getAnniLeft A `{PartialOrder A} (a a':A) an an'
  : poLe a a'
    -> poLe an an'
    -> poLe (getAnniLeft a an) (getAnniLeft a' an').
Proof.
  intros LE LE'; inv LE'; simpl; eauto.
Qed.

Definition getAnniRight A (a:A) (an:anni A) :=
  match an with
  | anni2 _ a => a
  | _ => a
  end.

Lemma poLe_getAnniRight A `{PartialOrder A} (a a':A) an an'
  : poLe a a'
    -> poLe an an'
    -> poLe (getAnniRight a an) (getAnniRight a' an').
Proof.
  intros LE LE'; inv LE'; simpl; eauto.
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