Require Import List.
Require Export Util Get Drop Var Val Exp Envs Map CSet AutoIndTac MoreList.

Set Implicit Arguments.

(* non-recursive patterns *)
Inductive pattern :=
  | PatternScore
  | PatternVar (x:var)
  | PatternList (Z:list var).

Fixpoint patternVars (p:pattern) : set var :=
  match p with
    | PatternScore => ∅
    | PatternVar x => {{x}}
    | PatternList Z => of_list Z
  end.

Definition patternMatchList
         (patternMatch: pattern -> val -> option (list var * list val)) :=
  fix patternMatchList (Z:list pattern) (vl:list val) {struct Z} : option (list var * list val) :=
  match Z, vl with
    | p::Z', v::vl =>
      mdo l <- patternMatch p v;
        let (varl, vall) := l in
        mdo l' <- patternMatchList Z' vl;
          let (varl', vall') := l' in
          Some ((varl++varl')%list, (vall++vall')%list)
    | nil, nil => Some (nil, nil)
  | _, _ => None
  end.

Fixpoint patternMatch (p:pattern) (v:val) {struct p} : option (list var * list val) :=
  match p, v with
    | PatternScore, _ => Some (nil, nil)
    | PatternVar x, v => Some (x::nil, v::nil)
(*  | PatternList Z, ValTpl vl => if [ length Z = length vl] then
                                   Some (Z, vl)
                                 else
                                   None *)
    | _, _ => None
  end.

Definition patterneq (p q:pattern)
  := forall v, patternMatch p v <> None <-> patternMatch q v <> None.

Instance patterneq_Equivalence_instance : Equivalence patterneq.
constructor; firstorder.
Defined.

Lemma patterneq_some p q v ZVL
: patterneq p q -> patternMatch p v = Some ZVL -> exists ZVL, patternMatch q v = Some ZVL.
Proof.
  intros. specialize (H v).
  destruct (patternMatch q v).
  - eexists; eauto.
  - exfalso. destruct H. eapply H; congruence.
Qed.
