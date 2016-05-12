Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve LengthEq MoreList Status AllInRel.

Set Implicit Arguments.

(** Specification of an analysis and generic fixpoint iteration algorithm *)

Class Analysis (Dom: Type) := makeAnalysis {
  dom_po :> PartialOrder Dom;
  analysis_step : stmt -> Dom -> status Dom;
  initial_value : stmt -> Dom;
  finite_height : terminating poLt;
  step_monotone : forall s d d', analysis_step s d = Success d' -> poLe d d';
  step_respectful :> Proper (eq ==> poEq ==> status_eq poEq) analysis_step
}.

Lemma poLe_poLt Dom `{PartialOrder Dom} d d'
  : poLe d d'
    -> ~ poLe d' d
    -> poLt d d'.
Proof.
  split; eauto. decide (poEq d d'); eauto.
  exfalso; eapply H1; eapply poEq_refl; symmetry; eauto.
Qed.

Section AnalysisAlgorithm.
  Variable Dom : Type.
  Variable analysis : Analysis Dom.

  Fixpoint safeFirst' (s:stmt) (d:Dom) (trm:terminates poLt d) : status Dom.
    refine (sdo d' <- analysis_step s d;
            if [poLt d d'] then safeFirst' s d' _ else  Success d').
    destruct trm. eapply H. eauto.
  Defined.

  Fixpoint safeFirst (s:stmt) (d:Dom) (trm:terminates poLt d) : status Dom.
    case_eq (analysis_step s d); intros d' ?.
    - intros. refine (if [poLe d' d] then Success d' else safeFirst s d' _).
      destruct trm; eapply H0.
      eapply step_monotone in H; eauto.
      eapply poLe_poLt; eauto.
    - eapply (Error d').
  Defined.

  Definition safeFixpoint (s:stmt) :=
    @safeFirst s (initial_value s) (finite_height _).

  Definition step s (d:Dom) :=
    match analysis_step s d with
    | Success d' => d'
    | Error _ => d
    end.

  Fixpoint safeFixpoint_iter s d d' trm
    : @safeFirst s d trm = Success d'
      -> exists n, d' = iter n d (fun _ => step s)
             /\ poEq (step s d') d'.
  Proof.
    intros. destruct trm. simpl in *.
    revert H.
    cut (forall d'' (EQ:analysis_step s x = d''),
            match d'' as s0 return (analysis_step s x = s0 -> status Dom) with
            | Success d'0 =>
              fun H : analysis_step s x = Success d'0 =>
                match decision_procedure (poLe d'0 x) with
                | left _ => Success d'0
                | right x0 => safeFirst s (t d'0 (poLe_poLt x d'0 (step_monotone s x H) x0))
                end
            | Error d'0 => fun _ : analysis_step s x = Error d'0 => Error d'0
            end EQ = Success d' ->
               exists n : nat, d' = iter n x (fun _ : nat => step s) /\ poEq (step s d') d'); eauto.
    intros. destruct d''; [|congruence].
    destruct (decision_procedure (poLe d x)).
    + invc H. eexists 1; simpl. unfold step at 1. rewrite EQ.
      split; eauto.
      pose proof (step_monotone _ _ EQ).
      pose proof (po_antisymmetric _ _ H p).
      unfold step. eapply step_respectful in H0; eauto.
      rewrite EQ in H0. inv H0. symmetry. eauto.
    + destruct (safeFixpoint_iter _ _ _ _ H) as [n' ?].
      eexists (S n'). simpl. unfold step at 1. rewrite EQ. eapply H0.
  Qed.

End AnalysisAlgorithm.

(*
Inductive ann_R_ex {A B} (R:A->B->Prop) : ann A -> ann B -> Prop :=
| annLt0 a b
  : R a b
    -> ann_R_ex R (ann0 a) (ann0 b)
| annLt1A a b an bn
  : R a b
    -> ann_R_ex R (ann1 a an) (ann1 b bn)
| annLt1B a b an bn
  : R a b \/ ann_R R an bn
    -> ann_R_ex R (ann1 a an) (ann1 b bn)
| annLt2 a ans ant b bns bnt
  : R a b \/ ann_R R ans bns \/ ann_R R ant bnt
    -> ann_R_ex R (ann2 a ans ant) (ann2 b bns bnt)
| annLtF a ans b bns ant bnt
  : R a b
    -> length ans = length bns
    -> (exists n a b, get ans n a -> get bns n b -> ann_R R a b) \/ ann_R R ant bnt
    -> ann_R_ex R (annF a ans ant) (annF b bns bnt).

Lemma dom_trm_ann Dom `{PO:PartialOrder Dom}
  : terminating poLt
    -> terminating (fun x y => ann_R poLe x y /\ ann_R_ex (fun x y => ~ poEq x y) x y).
Proof.
  intros Trm a.
  econstructor. intros. dcr.
  general induction H1.
  - specialize (Trm b).
    general induction Trm.
    econstructor. intros ? [A B].
    inv A; inv B.
    eapply H0; eauto. split; eauto.
  - econstructor.
    intros ? [A B]. inv A; inv B.
    +
    decide (poEq a b).
    + exploit IHa; eauto. inv H.
      exploit H0. split. eauto. intro. eapply B. econstructor; eauto.
      specialize (Trm b).


    specialize (Trm a).
    general induction Trm.
    econstructor. intros. destruct H1 as [A B].
    inv A.
    eapply H0; eauto. split; eauto.
    intro. eapply B. econstructor; eauto.
Qed.
*)

Inductive anni (A:Type) : Type :=
| anni0 : anni A
| anni1 (a1:A) : anni A
| anni2 (a1:A) (a2:A) : anni A
| anniF (a1:list A) (a2:A) : anni A
| anni2opt (a1:option A) (a2:option A) : anni A.

Definition anni_getF A (a:anni A) : list A :=
  match a with
    | anniF a1 s2 => a1
    | _ => nil
  end.

Arguments anni A.
Arguments anni0 [A].


Fixpoint setAnni {A} (a:ann A) (ai:anni A) : ann A :=
  match a, ai with
    | ann1 a an, anni1 a1 => ann1 a (setTopAnn an a1)
    | ann2 a an1 an2, anni2 a1 a2 => ann2 a (setTopAnn an1 a1) (setTopAnn an2 a2)
    | annF a an1 an2, anniF a1 a2 => annF a (zip (@setTopAnn _) an1 a1) (setTopAnn an2 a2)
    | an, _ => an
  end.

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
      let ai := anniF (List.map getAnn ans') (getAnn ant') in
      let d' := btransform AL' st ai in
      annF d' ans' ant'
    | _, an => an
  end.

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


Instance PartialOrder_Subset_Equal X `{OrderedType X} U : PartialOrder ({ s : set X | s ⊆ U}) :=
{
  poLe x y := Subset (proj1_sig x) (proj1_sig y);
  poLe_dec x y := @Subset_computable _ _ (proj1_sig x) (proj1_sig y);
  poEq x y := Equal (proj1_sig x) (proj1_sig y);
  poEq_dec x y := @Equal_computable _ _ (proj1_sig x) (proj1_sig y)
}.
Proof.
  - intros [a ?] [b ?]. simpl. intros. rewrite H0. reflexivity.
  - econstructor.
    + hnf; intros. reflexivity.
    + hnf; intros. symmetry; eauto.
    + hnf; intros. etransitivity; eauto.
  - hnf; intros. split; eauto.
Defined.

Instance set_var_semilattice U : BoundedSemiLattice ({ s : set var | s ⊆ U}) := {
  bsl_partial_order := PartialOrder_Subset_Equal _ U;
  bottom := exist _ ∅ (@incl_empty var _ U);
  join x y := exist _ (union (proj1_sig x) (proj1_sig y)) _
}.
Proof.
  - destruct x,y; simpl. cset_tac.
  - hnf; intros. eapply union_idem.
  - hnf; intros. eapply union_comm.
  - hnf; intros. eapply union_assoc.
  - simpl. unfold Proper, respectful; intros. destruct x,y,x0,y0; simpl in * |- *.
    rewrite H, H0. reflexivity.
  - simpl. unfold Proper, respectful; intros. destruct x,y,x0,y0; simpl in * |- *.
    rewrite H, H0. reflexivity.
Defined.

Lemma bunded_set_terminating X `{OrderedType X} U
  : terminating (@poLt _ (@PartialOrder_Subset_Equal X _ U)).
Proof.
  hnf; intros [s Incl].
  remember (cardinal (U \ s)). assert (cardinal (U \ s) <= n) as Le by omega.
  clear Heqn. revert s Incl Le. induction n; intros.
  - econstructor. intros [y ?] [A B]; simpl in *.
    exfalso. eapply B. assert (cardinal (U \ s) = 0) by omega.
    rewrite <- cardinal_Empty in H0.
    eapply empty_is_empty_1 in H0. eapply diff_subset_equal' in H0.
    cset_tac.
  - intros. econstructor. intros [y ?] [A B]; simpl in *.
    eapply IHn.
    assert (~ y ⊆ s) by (intro; eapply B; split; eauto).
    edestruct not_incl_element; eauto; dcr.
    rewrite cardinal_difference'; eauto.
    rewrite cardinal_difference' in Le; eauto.
    erewrite (@cardinal_2 _ _ _ _ (y \ singleton x) y); eauto;
      [|cset_tac| rewrite Add_Equal; cset_tac; decide (x === a); eauto].
    assert (s ⊆ y \ singleton x) by cset_tac.
    eapply cardinal_morph in H1. omega.
Qed.


(*
Definition makeForwardAnalysis Dom (BSL:BoundedSemiLattice Dom)
         (ftransform : (list (params * Dom) * ann Dom) -> stmt -> (list (params * Dom) * anni Dom))
: Analysis (ann Dom) :=
makeAnalysis _ (fun s d => Success (snd (forward ftransform s (nil, d)))) (fun s => setAnn s bottom).
 *)

Definition makeBackwardAnalysis Dom FunDom (BSL:BoundedSemiLattice Dom)
           (btransform : list FunDom -> stmt -> anni Dom -> Dom)
           (bmkFunDom : params -> ann Dom -> FunDom)
: Analysis (ann Dom) :=
makeAnalysis _
             (fun s d => Success (backward btransform bmkFunDom nil s d))
             (fun s => setAnn bottom s).
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
