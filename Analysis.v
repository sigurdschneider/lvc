Require Import CSet Le ListUpdateAt.

Require Import Plus Util AllInRel Map Terminating.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve LengthEq MoreList Status AllInRel.

Set Implicit Arguments.

(** Specification of an analysis and generic fixpoint iteration algorithm *)

Class Analysis (Dom: Type) := makeAnalysis {
  dom_po :> PartialOrder Dom;
  analysis_step : stmt -> Dom -> Dom;
  initial_value : stmt -> Dom;
  finite_height : Terminating poLt;
  step_monotone : forall s d, poLe d (analysis_step s d);
  step_respectful :> Proper (eq ==> poEq ==> poEq) analysis_step
}.

Section AnalysisAlgorithm.
  Variable Dom : Type.
  Variable analysis : Analysis Dom.

  Fixpoint safeFirst (s:stmt) (d:Dom) (trm:terminates poLt d) : Dom.
    refine (let d' := analysis_step s d in
            if [poLe d' d] then d' else safeFirst s d' _).
    destruct trm. eapply H.
    eapply poLe_poLt; eauto.
    eapply step_monotone.
  Defined.

  Definition safeFixpoint (s:stmt) :=
    @safeFirst s (initial_value s) (finite_height _).

  Fixpoint safeFixpoint_iter s d d' trm
    : @safeFirst s d trm = d'
      -> exists n, d' = iter n d (fun _ => analysis_step s)
        /\ poEq (analysis_step s d') d'.
  Proof.
    intros. destruct trm. simpl in *.
    destruct (decision_procedure (poLe (analysis_step s x) x)).
    + eexists 1; simpl. split; eauto.
      assert (poEq x d').
      pose proof (step_monotone s x).
      rewrite H in p,H0.
      eapply poLe_antisymmetric; eauto.
      rewrite <- H0 at 1. rewrite H. reflexivity.
    + destruct (safeFixpoint_iter _ _ _ _ H) as [n' ?].
      eexists (S n'); eauto.
  Qed.

End AnalysisAlgorithm.



Inductive anni (A:Type) : Type :=
| anni0 : anni A
| anni1 (a1:A) : anni A
| anni2 (a1:A) (a2:A) : anni A
| anni2opt (a1:option A) (a2:option A) : anni A.

Arguments anni A.
Arguments anni0 [A].


Fixpoint setAnni {A} (a:ann A) (ai:anni A) : ann A :=
  match a, ai with
    | ann1 a an, anni1 a1 => ann1 a (setTopAnn an a1)
    | ann2 a an1 an2, anni2 a1 a2 => ann2 a (setTopAnn an1 a1) (setTopAnn an2 a2)
    | an, _ => an
  end.

Inductive option_P {A} (P: A -> Prop) : option A -> Prop :=
| option_P_None : option_P P (None)
| option_R_Some a : P a -> option_P P (Some a).

Inductive anni_P {A} (P : A -> Prop) : anni A -> Prop :=
| anni_P0 : anni_P P anni0
| anni_P1 a : P a -> anni_P P (anni1 a)
| anni_P2 a a' : P a -> P a' -> anni_P P (anni2 a a')
| anni_P2o o o' : option_P P o -> option_P P o' -> anni_P P (anni2opt o o').

Definition backward Dom FunDom
           (btransform : list FunDom -> stmt -> anni Dom -> Dom)
           (bmkFunDom : params -> ann Dom -> FunDom) :=
  fix backward
         (AL:list FunDom) (st:stmt) (a:ann Dom) {struct st} : ann Dom :=
  match st, a with
    | stmtLet x e s as st, ann1 d ans =>
      let ans' := backward AL s ans in
      let ai := anni1 (getAnn ans') in
      let d := (btransform AL st ai) in
      ann1 d ans'
    | stmtIf x s t as st, ann2 d ans ant =>
      let ans' := backward AL s ans in
      let ant' := backward AL t ant in
      let ai := anni2 (getAnn ans') (getAnn ant') in
      let d' := (btransform AL st ai) in
      ann2 d' ans' ant'

    | stmtApp f Y as st, ann0 d as an =>
      ann0 (btransform AL st anni0)

    | stmtReturn x as st, ann0 d as an =>
      ann0 (btransform AL st anni0)

    | stmtExtern x f Y s as st, ann1 d ans =>
      let ans' := backward AL s ans in
      let ai := anni1 (getAnn ans') in
      let d' := (btransform AL st ai) in
      ann1 d' ans'
    | stmtFun F t as st, annF d ans ant =>
      let ans' := zip (fun Zs =>
        backward (zip (fun Zs ans => bmkFunDom (fst Zs) ans) F ans ++ AL) (snd Zs)) F ans in
      let AL' := zip (fun Zs ans => bmkFunDom (fst Zs) ans) F ans' ++ AL in
      let ant' := backward AL' t ant in
      let ai := anni1 (getAnn ant') in
      let d' := btransform AL' st ai in
      annF d' ans' ant'
    | _, an => an
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

Lemma backward_increasing Dom FunDom `{PartialOrder Dom}
      (f : list FunDom -> stmt -> anni Dom -> Dom)
      (fOK:forall AL s ai, anni_P (fun x => poLe x (f AL s ai)) ai)
           (bmkFunDom : params -> ann Dom -> FunDom)
  : forall AL (s : stmt) (d : ann Dom), d ⊑ backward f bmkFunDom AL s d.
Proof.
  intros.
  general induction s; destruct d; simpl; try reflexivity.
  - econstructor.
    btransform f fOK.
    rewrite <- IHs; eauto.

    eapply IHs; eauto.

Qed.

Instance makeBackwardAnalysis Dom FunDom (BSL:BoundedSemiLattice Dom)
           (btransform : list FunDom -> stmt -> anni Dom -> Dom)
           (bmkFunDom : params -> ann Dom -> FunDom) (trm:Terminating poLt)
  : Analysis (ann Dom) := {
                           analysis_step s d := backward btransform bmkFunDom nil s d;
                           initial_value s := setAnn bottom s
                         }.
Proof.
  eapply terminating_ann; eauto.


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