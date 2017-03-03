Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet ListUpdateAt.
Require Import Val Var Env IL Annotation Infra.Lattice DecSolve Filter.
Require Import Analysis AnalysisForward FiniteFixpointIteration Terminating Subterm.

Remove Hints trans_eq_bool.

Set Implicit Arguments.

Definition reachability_transform (sT:stmt)
           (ZL:list params)
           (st:stmt) (ST:subTerm st sT)
           (d:bool)
  : anni bool :=
  match st with
  | stmtLet x e s => anni1 d
  | stmtIf e s t =>
    anni2 (if [op2bool e = Some false] then false else d)
          (if [op2bool e = Some true] then false else d)
  | stmtApp f Y => anni1 d
  | stmtReturn e => anni1 d
  | _ => anni1 d
  end.


Lemma reachability_transform_monotone (sT s : stmt) (ST ST' : subTerm s sT)
      (ZL : 〔params〕) (a b : bool)
  : a ⊑ b
    -> reachability_transform ZL ST a ⊑ reachability_transform ZL ST' b.
Proof.
  intros; destruct s; simpl; try econstructor; simpl; eauto;
    repeat cases; simpl in *; eauto.
Qed.

Definition reachability_analysis s :=
  makeForwardAnalysis (fun s => bool ) _ _ _
                      reachability_transform
                      reachability_transform_monotone
                      (fun s => terminating_bool) s true.

Definition reachabilityAnalysis s :=
  proj1_sig (proj1_sig (safeFixpoint (reachability_analysis s))).
