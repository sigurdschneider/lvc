Require Import Util DecSolve Val CSet Map Get Env EnvTy Option.
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
  - monad_inv H; simpl. rewrite IHZ; eauto.
    hnf; intros. lud; congruence.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
