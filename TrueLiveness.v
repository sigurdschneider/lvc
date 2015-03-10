Require Import AllInRel List Map Env DecSolve.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Filter.
Require Export Liveness.

Set Implicit Arguments.

Local Hint Resolve incl_empty minus_incl incl_right incl_left.


Inductive true_live_sound (i:overapproximation)
  : list (set var *params) -> stmt -> ann (set var) -> Prop :=
| TLOpr x Lv b lv e al
  :  true_live_sound i Lv b al
  -> (x ∈ getAnn al -> live_exp_sound e lv)
  -> (getAnn al\{{x}}) ⊆ lv
  -> (x ∉ getAnn al -> lv ⊆ getAnn al \ {{x}})
  -> true_live_sound i Lv (stmtLet x e b) (ann1 lv al)
| TLIf Lv e b1 b2 lv al1 al2
  :  true_live_sound i Lv b1 al1
  -> true_live_sound i Lv b2 al2
  -> (exp2bool e = None -> live_exp_sound e lv)
  -> (exp2bool e <> Some false -> getAnn al1 ⊆ lv)
  -> (exp2bool e = Some true -> lv ⊆ getAnn al1)
  -> (exp2bool e <> Some true -> getAnn al2 ⊆ lv)
  -> (exp2bool e = Some false -> lv ⊆ getAnn al2)
  -> true_live_sound i Lv (stmtIf e b1 b2) (ann2 lv al1 al2)
| TLGoto l Y Lv lv blv Z
  : get Lv (counted l) (blv,Z)
  -> (if isImperative i then  (blv \ of_list Z ⊆ lv) else True)
  -> argsLive lv blv Y Z
  -> length Y = length Z
  -> true_live_sound i Lv (stmtApp l Y) (ann0 lv)
| TLReturn Lv e lv
  : live_exp_sound e lv
  -> true_live_sound i Lv (stmtReturn e) (ann0 lv)
| TLExtern x Lv b lv Y al f
  : true_live_sound i Lv b al
  -> (forall n y, get Y n y -> live_exp_sound y lv)
  -> (getAnn al\{{x}}) ⊆ lv
  -> x ∈ getAnn al
  -> true_live_sound i Lv (stmtExtern x f Y b) (ann1 lv al)
| TLLet Lv s Z b lv als alb
  : true_live_sound i ((getAnn als,Z)::Lv) s als
  -> true_live_sound i ((getAnn als,Z)::Lv) b alb
  -> (if isFunctional i then (getAnn als \ of_list Z ⊆ lv) else True)
  -> getAnn alb ⊆ lv
  -> true_live_sound i Lv (stmtFun Z s b)(ann2 lv als alb).


Lemma true_live_sound_overapproximation_I Lv s slv
: true_live_sound FunctionalAndImperative Lv s slv -> true_live_sound Imperative Lv s slv.
Proof.
  intros. general induction H; simpl in * |- *; econstructor; simpl; eauto.
Qed.

Lemma true_live_sound_overapproximation_F Lv s slv
: true_live_sound FunctionalAndImperative Lv s slv -> true_live_sound Functional Lv s slv.
Proof.
  intros. general induction H; simpl in * |- *; econstructor; simpl; eauto.
Qed.

Lemma true_live_sound_annotation i Lv s slv
: true_live_sound i Lv s slv -> annotation s slv.
Proof.
  intros. general induction H; econstructor; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
