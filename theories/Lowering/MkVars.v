Require Import Util Var Get Coqlib.

Set Implicit Arguments.

Fixpoint mkVars X (L:list X) (f:var) : var * list var :=
  match L with
  | nil => (f, nil)
  | _::L => let f' := Pos.succ f in
           let (f'', xl) := mkVars L f' in
           (f'', f::xl)
  end.


Lemma mkVars_length X (L:list X) f
  : ❬snd (mkVars L f)❭ = ❬L❭.
Proof.
  general induction L; simpl; repeat let_pair_case_eq; eauto; subst; simpl.
  rewrite IHL; eauto.
Qed.

Smpl Add match goal with
         | [ H : context [ ❬snd (@mkVars ?X ?L ?f)❭ ] |- _ ]
           => setoid_rewrite (@mkVars_length X L f) in H
         | [ |- context [ ❬snd (@mkVars ?X ?L ?f)❭ ] ]
           => setoid_rewrite (@mkVars_length X L f)
         end : len.

Lemma mkVars_le X L f
  : (f <= fst (@mkVars X L f))%positive.
Proof.
  general induction L; simpl.
  - reflexivity.
  - let_pair_case_eq; simpl_pair_eqs; subst; simpl.
    rewrite <- IHL. eapply Ple_succ.
Qed.

Lemma mkVars_get_le X (L:list X) f n i
  :  get (snd (mkVars L f)) n i
     -> (f <= i)%positive.
Proof.
  intros GET.
  general induction L; simpl in *.
  - isabsurd.
  - revert GET; let_pair_case_eq; simpl_pair_eqs; subst; simpl.
    intros GET. inv GET.
    + reflexivity.
    + eapply IHL in H3. rewrite <- H3. eapply Ple_succ.
Qed.

Lemma mkVars_get_lt X (L:list X) f n i
  :  get (snd (mkVars L f)) n i
     -> (i < fst (mkVars L f))%positive.
Proof.
  intros GET.
  general induction L; simpl in *.
  - isabsurd.
  - revert GET; let_pair_case_eq; simpl_pair_eqs; subst; simpl.
    intros GET. inv GET.
    + eapply Pos.lt_le_trans. eapply Plt_succ. rewrite <- mkVars_le. reflexivity.
    + eapply IHL; eauto.
Qed.
