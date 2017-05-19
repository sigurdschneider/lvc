Require Import CSet Le CMap CMapDomain CMapPartialOrder CMapJoinSemiLattice CMapTerminating.

Require Import Plus Util AllInRel CSet OptionR.
Require Import Val Var Env IL Annotation Infra.Lattice DecSolve.
Require Import Analysis.Analysis AnalysisForwardSSA ValueOpts.ConstantPropagation.

Require Import CMap WithTop DomainSSA.

Set Implicit Arguments.

Open Scope map_scope.


Definition Dom := Map [var, withTop val].


Lemma wua_poLe_inv (x y : withUnknown val)
  : poLe x y -> x = y.
Proof.
  intros A; inv A.
  - f_equal. eauto.
  - eauto.
Qed.

Smpl Add 100 match goal with
             | [ H : @poLe (withUnknown val) _ ?x ?y  |- _ ] =>
               eapply wua_poLe_inv in H; subst
             end : inv_trivial.

Require Import MapNotations ListUpdateAt Subterm.

Lemma leMap_op_eval e a b
  : poLe a b
    -> poLe (op_eval (domenv a) e) (op_eval (domenv b) e).
Proof.
  general induction e; simpl; eauto using @fstNoneOrR, @withTop_le.
  - reflexivity.
  - unfold domenv.
    specialize (H n).
    destruct (find n a); eauto using fstNoneOrR.
  - specialize (IHe _ _ H); repeat cases; eauto using fstNoneOrR, @withTop_le.
    reflexivity.
  - specialize (IHe1 _ _ H).
    specialize (IHe2 _ _ H).
    inv IHe1; inv IHe2; repeat cases;
      simpl in *; clear_trivial_eqs;
        eauto using fstNoneOrR, withTop_le.
    + econstructor; econstructor. congruence.
Qed.

Hint Resolve leMap_op_eval.

Lemma eqMap_op_eval e a b
  : poEq a b
    -> poEq (op_eval (domenv a) e) (op_eval (domenv b) e).
Proof.
  general induction e; simpl; eauto using @fstNoneOrR, @withTop_eq, @option_R.
  - reflexivity.
  - unfold domenv.
    specialize (H n).
    destruct (find n a); eauto using fstNoneOrR.
  - specialize (IHe _ _ H); repeat cases; eauto using fstNoneOrR, @withTop_eq, @option_R.
    reflexivity.
  - specialize (IHe1 _ _ H).
    specialize (IHe2 _ _ H).
    inv IHe1; inv IHe2; repeat cases;
      simpl in *; clear_trivial_eqs;
        eauto using fstNoneOrR, withTop_eq, option_R.
    + econstructor; econstructor. congruence.
Qed.

Hint Resolve leMap_op_eval eqMap_op_eval.


Definition DDom (sT:stmt) := { m : Map [var, withTop val] | domain m ⊆ occurVars sT}.

Smpl Add match goal with
         | [ H : poLe _ None |- _ ] => invc H
         | [ H : ⎣ ?x ⎦ <> ⎣ ?x ⎦ |- _ ] => exfalso; apply H; reflexivity
         end : inv_trivial.

Lemma cp_trans_reach_mon
  : forall (sT : stmt) (e : op) (s : stmt),
    subTerm s sT ->
    forall (FVIncl : Op.freeVars e [<=] occurVars sT) (a a' : DDom sT),
      a ⊑ a' ->
      forall b b' : bool,
        b ⊑ b' -> cp_trans_reach e FVIncl a b ⊑ cp_trans_reach e FVIncl a' b'.
Proof.
  intros. pose proof (leMap_op_eval e H0); eauto.
  unfold cp_trans_reach.
  set (X:=op_eval (domenv (proj1_sig a)) e) in *.
  set (Y:=op_eval (domenv (proj1_sig a')) e) in *. clearbody X Y.
  unfold val in *.
  repeat cases; split; simpl fst; simpl snd; eauto; clear_trivial_eqs.
  inv H2; clear_trivial_eqs.
  inv H2; clear_trivial_eqs.
Qed.

Lemma cp_trans_reach_ext
  : forall sT (e : op) (s : stmt),
    subTerm s sT ->
    forall (FVIncl : Op.freeVars e [<=] occurVars sT) (a0 a' : DDom sT),
      a0 ≣ a' ->
      forall b b' : bool,
        b ≣ b' -> cp_trans_reach e FVIncl a0 b ≣ cp_trans_reach e FVIncl a' b'.
Proof.
  intros. exploit (eqMap_op_eval e); eauto. eapply H0.
  unfold cp_trans_reach.
  set (X:=op_eval (domenv (proj1_sig a0)) e) in *.
  set (Y:=op_eval (domenv (proj1_sig a')) e) in *. clearbody X Y.
  repeat cases; split; simpl fst; simpl snd; eauto; clear_trivial_eqs;
  inv H2; clear_trivial_eqs; exfalso; eauto.
Qed.


Definition cp_reach (U : ⦃nat⦄) (b:bool) (d: VDom U (withTop val)) (e:op) : bool * bool :=
  (true, true).

Definition cp_reach (U : ⦃nat⦄) (b:bool) (d: VDom U (withTop val)) (e:op) : bool * bool :=
  (if [op_eval (domenv (proj1_sig d)) e = None] then false
     else if [op_eval (domenv (proj1_sig d)) e = Some (wTA val_false)] then
            false else b,
     if [op_eval (domenv (proj1_sig d)) e = None] then false
     else if [op_eval (domenv (proj1_sig d)) e = Some (wTA val_true)] then
            false else b).

Lemma cp_reach_mon (U : ⦃nat⦄) (e : op) (a a' : VDom U (withTop val))
  : a ⊑ a' -> forall b b' : bool, b ⊑ b' -> cp_reach b a e ⊑ cp_reach b' a' e.
Proof.
  intros. reflexivity.
Qed.

Definition cp_trans (U : ⦃nat⦄) (b:bool) (d: VDom U (withTop val)) (e:exp) : ؟ (withTop val) :=
  match e with
  | Operation e => op_eval (domenv (proj1_sig d)) e
  | _ => Some Top
  end.

Lemma cp_trans_mon (U : ⦃nat⦄) (e : exp) (a a' : VDom U (withTop val))
  : a ⊑ a' -> forall b b' : bool, b ⊑ b' -> @cp_trans U b a e ⊑ @cp_trans U b' a' e.
Proof.
  intros. destruct e; simpl; eauto.
Qed.

Definition constant_propagation_analysis :=
  makeForwardAnalysis _ _ _ cp_trans cp_reach cp_trans_mon cp_reach_mon.
