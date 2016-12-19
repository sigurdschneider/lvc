Require Import Nat Util CSet IL.

Notation "'list_max' L" := (fold_left max L 0) (at level 50).

Lemma list_max_swap L x
: max (list_max L) x = fold_left max L x.
Proof.
  general induction L; simpl; eauto.
  setoid_rewrite <- IHL; eauto.
  setoid_rewrite Max.max_comm at 4.
  rewrite Max.max_assoc; eauto.
Qed.

Lemma list_max_get L n x
: get L n x
  -> x <= list_max L.
Proof.
  intros. general induction L; eauto; invt get; simpl.
  - rewrite <- list_max_swap. eapply Max.le_max_r.
  - rewrite <- list_max_swap. rewrite <- Max.le_max_l; eauto.
Qed.

Inductive exp_vars_bounded : nat -> stmt -> Prop :=
| BoundLet k x e s
  : cardinal (Exp.freeVars e) <= k
    -> exp_vars_bounded k s
    -> k > 0
    -> exp_vars_bounded k (stmtLet x e s)
| BoundReturn k e
  : cardinal (Op.freeVars e) <= k
    -> exp_vars_bounded k (stmtReturn e)
| BoundIf k e s t
  : cardinal (Op.freeVars e) <= k
    -> exp_vars_bounded k s
    -> exp_vars_bounded k t
    -> exp_vars_bounded k (stmtIf e s t)
| BoundApp k f Y
  : exp_vars_bounded k (stmtApp f Y)
| BoundFun k F t
  : (forall n Zs, get F n Zs -> exp_vars_bounded k (snd Zs))
    -> exp_vars_bounded k t
    -> exp_vars_bounded k (stmtFun F t).

Lemma exp_vars_bounded_ge n m s
  : exp_vars_bounded n s
    -> n <= m
    ->  exp_vars_bounded m s.
Proof.
  intros A B.
  general induction A; simpl; econstructor; eauto; omega.
Qed.

Fixpoint exp_vars_bound (s:stmt) : nat :=
  match s with
  | stmtLet x e s0 =>
    max (max (cardinal (Exp.freeVars e)) (exp_vars_bound s0)) 1
  | stmtIf e s1 s2 => max (cardinal (Op.freeVars e)) (max (exp_vars_bound s1) (exp_vars_bound s2))
  | stmtApp l Y => 0
  | stmtReturn e => cardinal (Op.freeVars e)
  | stmtFun F t =>
    max (list_max ((fun Zs => exp_vars_bound (snd Zs)) ⊝ F))
        (exp_vars_bound t)
  end.

Instance max_le_m
  : Proper (le ==> le ==> le) max.
Proof.
  unfold Proper, respectful; intros.
  eapply Nat.max_le_compat; eauto.
Qed.

Lemma exp_vars_bound_sound s
  : exp_vars_bounded (exp_vars_bound s) s.
Proof.
  sind s; destruct s; simpl; econstructor;
    intros; inv_get; eauto using exp_vars_bounded_ge,Max.le_max_r,Max.le_max_l,list_max_get.
  - rewrite <- !Max.le_max_l. reflexivity.
  - eapply exp_vars_bounded_ge; eauto.
    rewrite <- list_max_get; eauto using get.
    eapply Max.le_max_l.
Qed.