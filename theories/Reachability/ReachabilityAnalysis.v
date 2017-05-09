Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet ListUpdateAt.
Require Import Val Var Env IL Annotation Infra.Lattice DecSolve Filter.
Require Import Analysis AnalysisForwardSSA FiniteFixpointIteration Terminating Subterm.

Remove Hints trans_eq_bool.

Set Implicit Arguments.

Definition reachability_transform (sT:stmt)
           (ZL:list params)
           (st:stmt) (ST:subTerm st sT)
           (ZLIncl:list_union (of_list ⊝ ZL) [<=] occurVars sT) (u:unit)
           (d:bool)
  : anni unit st :=
  match st with
  | stmtIf e s t =>
    (if [op2bool e = Some false] then false else d,
     if [op2bool e = Some true] then false else d, u)
  | _ => u
  end.

Lemma reachability_transform_monotone (sT s : stmt) (ST : subTerm s sT)
      (ZL : 〔params〕) (ZLIncl : list_union (of_list ⊝ ZL) [<=] occurVars sT) (a b : unit)
  : a ⊑ b
    ->  forall r r' : bool,
      r ⊑ r'
      -> reachability_transform ZL ST ZLIncl a r ⊑ reachability_transform ZL ST ZLIncl b r'.
Proof.
  intros; destruct s; simpl; try econstructor; simpl; eauto;
    repeat cases; simpl in *; eauto.
Qed.

Definition reachability_analysis s :=
  makeForwardAnalysis (fun s => unit ) _ _
                      reachability_transform
                      reachability_transform_monotone
                      (fun s => Terminating_unit) s.

Definition reachabilityAnalysis s :=
  proj1_sig (safeFixpoint (reachability_analysis s)).
