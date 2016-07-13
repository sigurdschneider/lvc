Require Import Util DecSolve Val CSet Map MapDefined Get Env Option.
Require Import Arith Exp OptionMap.

Set Implicit Arguments.

Lemma exp_eval_agree E E' e v
: agree_on eq (Exp.freeVars e) E E'
  -> exp_eval E e = v
  -> exp_eval E' e = v.
Proof.
  intros.
  erewrite <- exp_eval_live; eauto.
  eauto using live_exp_sound_incl, live_freeVars.
Qed.

Lemma omap_exp_eval_agree E E' Y v
: agree_on eq (list_union (List.map freeVars Y)) E E'
  -> omap (exp_eval E) Y = v
  -> omap (exp_eval E') Y = v.
Proof.
  intros.
  erewrite omap_agree; eauto.
  intros. eapply exp_eval_agree; eauto.
  eapply agree_on_incl; eauto.
  eapply incl_list_union; eauto using map_get_1.
Qed.

Lemma exp_eval_live_agree E E' e lv v
: live_exp_sound e lv
  -> agree_on eq lv E E'
  -> exp_eval E e = v
  -> exp_eval E' e = v.
Proof.
  intros. erewrite <- exp_eval_live; eauto.
Qed.

Lemma omap_exp_eval_live_agree E E' lv Y v
: (forall n y, get Y n y -> live_exp_sound y lv)
  -> agree_on eq lv E E'
  -> omap (exp_eval E) Y = v
  -> omap (exp_eval E') Y = v.
Proof.
  intros.
  erewrite omap_agree; eauto.
  intros. eapply exp_eval_agree; eauto.
  eapply agree_on_incl; eauto using Exp.freeVars_live.
Qed.

Lemma omap_self_update E Z l
:  omap (exp_eval E) (List.map Var Z) = ⎣l ⎦
   -> E [Z <-- List.map Some l] [-] E.
Proof.
  general induction Z; simpl in * |- *.
  - reflexivity.
  - monad_inv H; simpl.
    rewrite IHZ; eauto.
    hnf; intros; lud. congruence.
Qed.

Lemma omap_var_defined_on Za lv E
: of_list Za ⊆ lv
  -> defined_on lv E
  -> exists l, omap (exp_eval E) (List.map Var Za) = Some l.
Proof.
  intros. general induction Za; simpl.
  - eauto.
  - simpl in *.
    edestruct H0.
    + instantiate (1:=a). cset_tac; intuition.
    + rewrite H1; simpl. edestruct IHZa; eauto.
      cset_tac; intuition.
      rewrite H2; simpl. eauto.
Qed.

Hint Extern 5 =>
match goal with
| [ EQ : ❬?Y❭ = ❬?x❭, OMAP: omap _ ?Y = Some ?l  |- ❬?x❭ = ❬?l❭ ] =>
  rewrite <- EQ; eapply (omap_length _ _ _ _ _ OMAP)
| [ EQ : ❬?Y❭ = ❬?x❭, OMAP: omap _ ?Y = Some ?l  |- ❬?l❭ = ❬?x❭ ] =>
  rewrite <- EQ; symmetry; eapply (omap_length _ _ _ _ _ OMAP)
| [ EQ : ❬?x❭ = ❬?Y❭, OMAP: omap _ ?Y = Some ?l  |- ❬?x❭ = ❬?l❭ ] =>
  rewrite EQ; eapply (omap_length _ _ _ _ _ OMAP)
| [ OMAP: omap _ _ = Some ?l  |- ❬?l❭ = ❬?B❭ ] =>
  etransitivity; [ symmetry; eapply (omap_length _ _ _ _ _ OMAP)|]
| [ EQ : ❬?l❭ = ❬?x❭, OMAP: omap _ ?Y = Some ?l  |- ❬?x❭ = ❬?Y❭ ] =>
  rewrite <- EQ; symmetry; eapply (omap_length _ _ _ _ _ OMAP)
| [ EQ : ❬?x❭ = ❬?l❭, OMAP: omap _ ?Y = Some ?l  |- ❬?x❭ = ❬?Y❭ ] =>
  rewrite EQ; symmetry; eapply (omap_length _ _ _ _ _ OMAP)
end : len.

Hint Extern 5 =>
match goal with
| [ LV : live_exp_sound ?e ?lv, AG: agree_on eq ?lv ?E ?E',
    H1 : exp_eval ?E ?e = _, H2 : exp_eval ?E' ?e = _ |- _ ] =>
  rewrite (exp_eval_live_agree LV AG H1) in H2; try solve [ exfalso; inv H2 ];
    clear_trivial_eqs
end.
