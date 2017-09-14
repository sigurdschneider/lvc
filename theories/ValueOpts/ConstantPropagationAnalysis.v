Require Import CSet Le CMap CMapDomain CMapPartialOrder CMapJoinSemiLattice CMapTerminating.

Require Import Plus Util AllInRel CSet OptionPO.
Require Import Val Var Envs IL Annotation Infra.Lattice DecSolve.
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
  revert a b.
  general induction e; simpl; eauto.
  - specialize (IHe _ _ H).
    repeat cases; clear_trivial_eqs;
      eauto using poLe_option_None, poLe_withTopLe_top, poLe_Some_struct.
  - specialize (IHe1 _ _ H).
    specialize (IHe2 _ _ H).
    inv IHe1; inv IHe2; repeat cases;
      simpl in *; clear_trivial_eqs;
        eauto using poLe_option_None, poLe_withTopLe_top, poLe_Some_struct.
Qed.

Hint Resolve leMap_op_eval.

Lemma eqMap_op_eval e a b
  : poEq a b
    -> poEq (op_eval (domenv a) e) (op_eval (domenv b) e).
Proof.
  revert a b.
  general induction e; simpl; eauto.
  - specialize (IHe _ _ H).
    repeat cases; clear_trivial_eqs;
      eauto using poLe_option_None, poLe_withTopLe_top, poLe_Some_struct.
  - specialize (IHe1 _ _ H).
    specialize (IHe2 _ _ H).
    inv IHe1; inv IHe2; repeat cases;
      simpl in *; clear_trivial_eqs;
        eauto using poLe_option_None, poLe_withTopLe_top, poLe_Some_struct.
Qed.

Hint Resolve leMap_op_eval eqMap_op_eval.

Definition DDom (sT:stmt) := { m : Map [var, withTop val] | domain m ⊆ occurVars sT}.

Definition cp_reach (U : ⦃var⦄) (b:bool) (d: VDom U (withTop val)) (e:op) : bool * bool :=
  (if [op_eval (domenv (proj1_sig d)) e = None] then false
     else if [op_eval (domenv (proj1_sig d)) e = Some (wTA val_false)] then
            false else b,
     if [op_eval (domenv (proj1_sig d)) e = None] then false
     else if [op_eval (domenv (proj1_sig d)) e = Some (wTA val_true)] then
            false else b).

Lemma cp_reach_mon (U : ⦃var⦄) (e : op) (a a' : VDom U (withTop val))
  : a ⊑ a' -> forall b b' : bool, b ⊑ b' -> cp_reach b a e ⊑ cp_reach b' a' e.
Proof.
  unfold cp_reach.
  intros.
  intros. pose proof (leMap_op_eval e H); eauto.
  set (X:=op_eval (domenv (proj1_sig a)) e) in *.
  set (Y:=op_eval (domenv (proj1_sig a')) e) in *. clearbody X Y.
  unfold val in *.
  repeat cases; split; simpl fst; simpl snd; eauto; clear_trivial_eqs.
Qed.

Lemma cp_reach_ext (U : ⦃var⦄) (e : op) (a a' : VDom U (withTop val))
  : a ≣ a' -> forall b b' : bool, b ≣ b' -> cp_reach b a e ≣ cp_reach b' a' e.
Proof.
  unfold cp_reach.
  intros.
  intros. pose proof (eqMap_op_eval e H); eauto.
  set (X:=op_eval (domenv (proj1_sig a)) e) in *.
  set (Y:=op_eval (domenv (proj1_sig a')) e) in *. clearbody X Y.
  unfold val in *.
  repeat cases; split; simpl fst; simpl snd; eauto; clear_trivial_eqs.
Qed.

Definition cp_trans (U : ⦃var⦄) (b:bool) (d: VDom U (withTop val)) (e:exp) : ؟ (withTop val) :=
  match e with
  | Operation e => op_eval (domenv (proj1_sig d)) e
  | _ => Some Top
  end.

Lemma cp_trans_mon (U : ⦃var⦄) (e : exp) (a a' : VDom U (withTop val))
  : a ⊑ a' -> forall b b' : bool, b ⊑ b' -> @cp_trans U b a e ⊑ @cp_trans U b' a' e.
Proof.
  intros. destruct e; simpl; eauto.
Qed.

Lemma cp_trans_ext (U : ⦃var⦄) (e : exp) (a a' : VDom U (withTop val))
  : a ≣ a' -> forall b b' : bool, b ≣ b' -> @cp_trans U b a e ≣ @cp_trans U b' a' e.
Proof.
  intros. destruct e; simpl; eauto.
Qed.

Instance withTop_OUB A R `{EqDec A R}
  : @UpperBounded (option (withTop A)) _ :=
  { top := Some Top
  }.
- intros.
  destruct a; eauto using poLe_Some_struct, poLe_withTopLe_top.
Defined.

Instance withTop_UB A R `{EqDec A R}
  : @UpperBounded (withTop A) _ :=
  { top := Top
  }.
- intros.
  eauto using poLe_Some_struct, poLe_withTopLe_top.
Defined.

Definition constant_propagation_analysis :=
  makeForwardAnalysis _ _ _ cp_trans cp_reach cp_trans_mon cp_reach_mon
                      _.

Require Import FiniteFixpointIteration.

Definition constantPropagationAnalysis s ra (RA:RenamedApart.renamedApart s ra) :=
  proj1_sig (safeFixpoint (constant_propagation_analysis RA)).
