Require Import Util IL RenamedApart LabelsDefined OptionR.
Require Import Annotation Exp SetOperations Liveness.Liveness Restrict.

Set Implicit Arguments.

Lemma plus_minus_eq n m
  : n + m - n = m.
Proof.
  omega.
Qed.

Ltac inv_get_step_some_minus :=
  match goal with
  | [ H : get (?f ⊝ (?g1 ⊝ ?A) \\ (?g2 ⊝ ?B) ++ ?C) ?k _,
          H' : get ?A ?k _ |- _ ] =>
    eapply get_app_lt_1 in H; [| eauto 20 with len]
  | [ H : get (?f ⊝ (?g1 ⊝ ?A) \\ (?g2 ⊝ ?B) ++ ?C) ?k _,
          H' : get ?B ?k _ |- _ ] =>
    eapply get_app_lt_1 in H; [| eauto 20 with len]
  | [ H : get (?f ⊝ (?g1 ⊝ ?A) \\ (?g2 ⊝ ?B) ++ ?C) (❬?B❭ + ?n) _ |- _ ] =>
    let LENEQ := fresh "LenEq" in
    assert (LENEQ:❬f ⊝ (g1 ⊝ A) \\ (g2 ⊝ B)❭ = ❬B❭) by eauto with len;
    rewrite get_app_ge in H;
    [ rewrite LENEQ in H; rewrite plus_minus_eq in H
    | rewrite LENEQ; omega]
  | [ H : get (?f ⊝ (?g1 ⊝ ?A) \\ (?g2 ⊝ ?B) ++ ?C) (❬?A❭ + ?n) _ |- _ ] =>
    let LENEQ := fresh "LenEq" in
    assert (LENEQ:❬f ⊝ (g1 ⊝ A) \\ (g2 ⊝ B)❭ = ❬A❭) by eauto with len;
    rewrite get_app_ge in H;
    [ rewrite LENEQ in H; rewrite plus_minus_eq in H
    | rewrite LENEQ; omega]
  end.

Smpl Add inv_get_step_some_minus : inv_get.

(** * Definition of Coherence: [srd] *)

Inductive srd : list (option (set var)) -> stmt -> ann (set var) -> Prop :=
| srdExp DL x e s lv al
  : srd (restr (getAnn al \ singleton x) ⊝ DL) s al
    -> srd DL (stmtLet x e s) (ann1 lv al)
| srdIf DL e s t lv als alt
  : srd DL s als
    -> srd DL t alt
    -> srd DL (stmtIf e s t) (ann2 lv als alt)
| srdRet e DL lv
  : srd DL (stmtReturn e) (ann0 lv)
| srdGoto DL lv G' f Y
  : get DL (counted f) (Some G')
    -> srd DL (stmtApp f Y) (ann0 lv)
| srdLet DL F t lv als alt
  : length F = length als
    -> (forall n Zs a, get F n Zs -> get als n a ->
                 srd (restr (getAnn a \ of_list (fst Zs)) ⊝
                            (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)) (snd Zs) a)
    -> srd (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL) t alt
    -> srd DL (stmtFun F t) (annF lv als alt).


(** ** Some monotonicity properties *)

Lemma srd_monotone (DL DL' : list (option (set var))) s a
 : srd DL s a
   -> PIR2 (fstNoneOrR Equal) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  - econstructor.
    eapply IHsrd; eauto. eapply restrict_subset; eauto.
  - destruct (PIR2_nth H0 H); eauto; dcr. inv H3.
    econstructor; eauto.
  - econstructor; eauto.
    + intros. eapply H1; eauto.
      repeat rewrite List.map_app.
      eapply PIR2_app; eauto.
      eapply restrict_subset; eauto.
    + eapply IHsrd. eapply PIR2_app; eauto.
Qed.

Lemma srd_monotone2 (DL DL' : list (option (set var))) s a
 : srd DL s a
   -> PIR2 (fstNoneOrR (flip Subset)) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  - econstructor.
    eapply IHsrd; eauto. eapply restrict_subset2; eauto.
  - destruct (PIR2_nth H0 H); eauto; dcr. inv H3.
    econstructor; eauto.
  - econstructor; eauto.
    + intros. eapply H1; eauto.
      repeat rewrite List.map_app.
      eapply PIR2_app; eauto.
      eapply restrict_subset2; eauto.
    + eapply IHsrd. eapply PIR2_app; eauto.
Qed.
