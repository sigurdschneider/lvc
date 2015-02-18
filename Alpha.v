Require Import Util Map Env EnvTy Exp IL AllInRel Bisim Computable.

Import F.

Set Implicit Arguments.
Unset Printing Records.

Inductive alpha : env var -> env var -> stmt -> stmt -> Prop :=
| alpha_return ra ira e e'
  : alpha_exp ra ira e e'  -> alpha ra ira (stmtReturn e) (stmtReturn e')
| alpha_goto ra ira l X Y
  : length X = length Y
    -> (forall n x y, get X n x -> get Y n y -> alpha_exp ra ira x y)
    -> alpha ra ira (stmtApp l X) (stmtApp l Y)
| alpha_assign ra ira x y e e' s s'
  : alpha_exp ra ira e e'
  -> alpha (ra[x<-y]) (ira[y <- x]) s s' -> alpha ra ira (stmtLet x e s) (stmtLet y e' s')
| alpha_if ra ira e e' s s' t t'
  : alpha_exp ra ira e e'
  -> alpha ra ira s s'
  -> alpha ra ira t t'
  -> alpha ra ira (stmtIf e s t) (stmtIf e' s' t')
| alpha_extern ra ira x y f Y Y' s s'
  : length Y = length Y'
  -> (forall n x y, get Y n x -> get Y' n y -> alpha_exp ra ira x y)
  -> alpha (ra[x<-y]) (ira[y <- x]) s s'
  -> alpha ra ira (stmtExtern x f Y s) (stmtExtern y f Y' s')
| alpha_let ra ira s s' Z Z' t t'
  : length Z = length Z'
  -> alpha (ra [ Z <-- Z']) (ira [ Z' <-- Z ]) s s'
  -> alpha ra ira t t' -> alpha ra ira (stmtFun Z s t) (stmtFun Z' s' t').

Global Instance alpha_morph
 : Proper ((@feq _ _ _eq) ==> (@feq _ _ _eq) ==> eq ==> eq ==> impl) alpha.
Proof.
  unfold respectful, Proper, impl; intros; subst.
  general induction H3; econstructor; eauto using alpha_exp_morph.
  - eapply IHalpha.
    + rewrite H0; reflexivity.
    + rewrite H1; reflexivity.
  - eapply IHalpha.
    + rewrite H1; reflexivity.
    + rewrite H2; reflexivity.
  - eapply IHalpha1.
    + rewrite H0; reflexivity.
    + rewrite H1; reflexivity.
Qed.

Lemma alpha_refl s
  : alpha id id s s.
Proof.
  general induction s; eauto using alpha, alpha_exp_refl.
  - econstructor. eapply alpha_exp_refl.
    rewrite update_id; eauto.
  - constructor; eauto using lookup_id.
    + intros. get_functional; subst; eauto using alpha_exp_refl.
  - econstructor; eauto.
    + intros. get_functional; subst; eauto using alpha_exp_refl.
    + rewrite update_id; eauto.
  - econstructor; try rewrite update_with_list_id; eauto using length_eq_refl.
Qed.

Lemma alpha_sym ϱ ϱ' s s'
  : alpha ϱ ϱ' s s'
  ->alpha ϱ' ϱ s' s.
Proof.
  intros. general induction H; eauto using alpha, length_eq_sym, alpha_exp_sym.
Qed.

Lemma inverse_on_dead_update X `{OrderedType X} Y `{OrderedType Y} (ra:X->Y) ira (x:X) (y:Y) s
: inverse_on s (ra [x <- y]) (ira [y <- x])
  -> inverse_on (s \ {{x}}) ra ira.
Proof.
  intros. hnf; intros. cset_tac; dcr.
  specialize (H1 _ H3). lud; intuition.
Qed.

Lemma alpha_inverse_on  ϱ ϱ' s t
  : alpha ϱ ϱ' s t -> inverse_on (freeVars s) ϱ ϱ'.
Proof.
  intros A. general induction A; simpl; eauto using alpha_exp_inverse_on.
  + hnf; intros.
    edestruct (list_union_get (List.map Exp.freeVars X)) as [[? []]|]; eauto; dcr.
    edestruct map_get_4; eauto; dcr.
    edestruct get_length_eq; eauto. subst.
    eapply alpha_exp_inverse_on; eauto.
    inv i.
  + eapply inverse_on_union;
    eauto using inverse_on_dead_update, alpha_exp_inverse_on.
  + eapply inverse_on_union; try eapply inverse_on_union; eauto using alpha_exp_inverse_on.
  + eapply inverse_on_union; eauto using inverse_on_dead_update.
    hnf; intros.
    edestruct (list_union_get (List.map Exp.freeVars Y)) as [[? []]|]; eauto; dcr.
    edestruct map_get_4; eauto; dcr; subst.
    edestruct get_length_eq; try eapply H; eauto.
    eapply alpha_exp_inverse_on; eauto.
    inv i.
  + eapply inverse_on_union; eauto.
    eapply update_with_list_inverse_on; eauto.
Qed.

Lemma alpha_agree_on_morph f g ϱ ϱ' s t
  : alpha ϱ ϱ' s t
  -> agree_on _eq (lookup_set ϱ (freeVars s)) g ϱ'
  -> agree_on _eq (freeVars s) f ϱ
  -> alpha f g s t.
Proof.
  intros. general induction H; simpl in * |- *; eauto using alpha, alpha_exp_agree_on_morph.
  - econstructor; intros; eauto.
    eapply alpha_exp_agree_on_morph; eauto.
    eapply agree_on_incl; eauto.
    eapply lookup_set_incl; try now intuition; eauto using get_list_union_map.
    eapply agree_on_incl; eauto using get_list_union_map.
  - econstructor.
    eapply alpha_exp_agree_on_morph; eauto.
    eapply agree_on_incl; eauto.
    eapply lookup_set_incl; try now intuition; eauto using get_list_union_map.
    eapply agree_on_incl; eauto. cset_tac; intuition.
    eapply IHalpha; eauto.
    + eapply agree_on_update_same. reflexivity. eapply agree_on_incl; eauto.
      hnf; intros. eapply lookup_set_spec. intuition.
      cset_tac; eqs. eapply lookup_set_spec in H4.
      destruct H4; dcr. eexists x0. lud.
      split; eqs. cset_tac. left. split; eauto. intuition.
    + eapply agree_on_update_same. reflexivity. eapply agree_on_incl; eauto.
      cset_tac; eqs; intuition.
  - econstructor; eauto.
    + eapply alpha_exp_agree_on_morph; eauto.
      eapply agree_on_incl; eauto.
      eapply lookup_set_incl; try now intuition; eauto using get_list_union_map.
      eapply agree_on_incl; eauto using get_list_union_map. cset_tac; intuition.
    + eapply IHalpha1. eapply agree_on_incl; eauto.
      eapply lookup_set_incl; intuition.
      cset_tac; intuition.
      eapply agree_on_incl; eauto. cset_tac; intuition.
    + eapply IHalpha2. eapply agree_on_incl; eauto.
      eapply lookup_set_incl; intuition.
      cset_tac; intuition.
      eapply agree_on_incl; eauto. cset_tac; intuition.
  - econstructor; eauto.
    + intros. eapply alpha_exp_agree_on_morph; eauto.
      eapply agree_on_incl; eauto.
      eapply lookup_set_incl; try now intuition.
      rewrite get_list_union_map; eauto. eapply incl_right.
      eapply agree_on_incl; eauto using get_list_union_map.
      rewrite get_list_union_map; eauto. eapply incl_right.
    + eapply IHalpha.
      eapply agree_on_update_same. reflexivity. eapply agree_on_incl; eauto.
      hnf; intros. eapply lookup_set_spec. intuition.
      cset_tac; eqs. eapply lookup_set_spec in H5.
      destruct H5; dcr. eexists x0. lud.
      split; eqs. cset_tac. left. split; eauto. intuition.
      eapply agree_on_update_same. reflexivity. eapply agree_on_incl; eauto.
      cset_tac; eqs; intuition.
  - econstructor; eauto.
    eapply IHalpha1; eauto.
    eapply update_with_list_agree; eauto using length_eq_sym.
    eapply agree_on_incl; eauto.
    hnf; intros. eapply lookup_set_spec. intuition.
    cset_tac. eapply lookup_set_spec in H5. destruct H5; dcr.
    exists x. cset_tac. left. intuition. eapply H6.
    rewrite H7. eapply update_with_list_lookup_in; eauto.
    symmetry. symmetry in H7.
    eapply update_with_list_lookup_not_in; eauto.
    intro. eapply H6. rewrite <- H7. eapply update_with_list_lookup_in; eauto.
    intuition.
    eapply update_with_list_agree; eauto.
    eapply agree_on_incl; eauto. eapply union_subset_1.
    eapply IHalpha2; eauto. eapply agree_on_incl; eauto.
    eapply lookup_set_incl; intuition.
    eapply agree_on_incl; eauto. eapply union_subset_2.
Qed.

Lemma alpha_inverse_on_agree f g ϱ ϱ' s t
  : alpha ϱ ϱ' s t
  -> inverse_on (freeVars s) f g
  -> agree_on _eq (freeVars s) f ϱ
  -> alpha f g s t.
Proof.
  intros. eapply alpha_agree_on_morph; eauto.
  symmetry in H1.
  eapply inverse_on_agree_on_2; eauto; try now intuition.
  eapply inverse_on_agree_on; eauto; try intuition.
  eapply alpha_inverse_on in H.
  eapply inverse_on_agree_on; try eassumption; try intuition.
  eapply inverse_on_agree_on_2; eauto; try intuition.
Qed.

Lemma alpha_trans ϱ1 ϱ1' ϱ2 ϱ2' s s' s''
  : alpha ϱ1 ϱ1' s s' -> alpha ϱ2 ϱ2' s' s'' -> alpha (ϱ1 ∘ ϱ2) (ϱ2' ∘ ϱ1') s s''.
Proof.
  intros. general induction H; invt alpha; eauto using alpha_exp_trans, alpha.
  - econstructor; eauto. etransitivity; eauto.
    intros. edestruct (get_length_eq _ H2 H); eauto.
    eapply alpha_exp_trans; eauto.
  - econstructor; eauto using alpha_exp_trans.
    specialize (IHalpha _ _ _ H9).
    eapply alpha_inverse_on in H0.
    eapply alpha_inverse_on_agree; eauto.
    eapply inverse_on_comp; eauto. eapply alpha_inverse_on; eauto.
    symmetry. eapply lookup_set_agree_on_comp. intuition.
    eapply inverse_on_update_lookup_set. intuition. eauto.
  - econstructor; eauto. congruence.
    + intros. edestruct (get_length_eq _ H3 H); eauto.
      eapply alpha_exp_trans; eauto.
    + specialize (IHalpha _ _ _ H12).
      eapply alpha_inverse_on in H1.
      eapply alpha_inverse_on_agree; eauto.
      eapply inverse_on_comp; eauto. eapply alpha_inverse_on; eauto.
      symmetry. eapply lookup_set_agree_on_comp. intuition.
      eapply inverse_on_update_lookup_set. intuition. eauto.
  - econstructor; eauto. congruence.
    specialize (IHalpha1 _ _ _ H10).
    eapply alpha_inverse_on_agree; eauto.
    eapply alpha_inverse_on in IHalpha1.
    pose proof (inverse_on_comp_list _ _ _ H H8 IHalpha1).
    pose proof (inverse_on_sym IHalpha1).
    pose proof H3.
    eapply inverse_on_comp_list in H4; eauto.
    eapply inverse_on_agree_on; eauto.
    symmetry. eapply inverse_on_comp_list; eauto.
    instantiate (1:=ira).
    instantiate (1:=ϱ2'). eapply alpha_inverse_on; eauto.
Qed.

Definition envCorr ra ira (E E':onv val) :=
  forall x y, ra x = y -> ira y = x -> E x = E' y.

Lemma envCorr_idOn_refl (E:onv val)
  : envCorr id id E E.
Proof.
  hnf; intros; firstorder.
Qed.

Inductive approx : list (env var * env var) -> F.block -> F.block ->  Prop :=
| EA2_cons Ral ra ira E E' s s' Z Z'
  : length Z = length Z'
  -> alpha (ra [ Z <-- Z']) (ira [ Z' <-- Z ]) s s'
  -> envCorr ra ira E E'
  -> approx ((ra, ira)::Ral) (F.blockI E Z s) (F.blockI E' Z' s').

Lemma approx_refl Ral b
  : approx ((id,id)::Ral) b b.
Proof.
  destruct b. econstructor; eauto.
  rewrite update_with_list_id. eapply alpha_refl.
  firstorder.
Qed.

Lemma envCorr_update ra ira x y v E E'
  (EC:envCorr ra ira E E')
  : envCorr (ra [x <- y]) (ira [y <- x]) (E [x <- v]) (E' [y <- v]).
Proof.
  hnf; intros; lud.
  + exfalso. eapply H0. reflexivity.
  + exfalso. eapply H1. reflexivity.
  + eapply EC; eauto.
Qed.

Lemma envCorr_update_lists bra bira block_E block_E' block_Z block_Z' ra ira
  E E' X Y (EC':envCorr ra ira E E')
  (LL : lookup_list ra X = Y)
  (LL' : lookup_list ira Y = X)
  (EC: envCorr bra bira block_E block_E')
  (LC: length block_Z = length block_Z')
  (LC': length block_Z = length X)
  (LC'': length block_Z' = length Y)
  : envCorr (bra [ block_Z <-- block_Z' ]) (bira [ block_Z' <-- block_Z ])
  (block_E  [ block_Z <-- lookup_list E X ])
  (block_E' [ block_Z' <-- lookup_list E' Y ]).
Proof.
  eapply length_length_eq in LC.
  eapply length_length_eq in LC'.
  eapply length_length_eq in LC''.
  general induction LC; simpl. destruct X,Y; eauto.
  inversion LC'. subst x0 XL0 X. inv LC''.
  simpl in *; injection LL; injection H2; intros.
  rewrite <- H0 in H3. rewrite <- H in H1. erewrite EC'; eauto.
  eapply envCorr_update; eauto.
Qed.

Lemma envCorr_update_list bra bira block_E block_E' block_Z block_Z' ra ira
  E E' vl (EC':envCorr ra ira E E')
  (EC: envCorr bra bira block_E block_E')
  (LC: length block_Z = length block_Z')
  (LC': length block_Z = length vl)
  : envCorr (bra [ block_Z <-- block_Z' ]) (bira [ block_Z' <-- block_Z ])
  (block_E  [ block_Z <-- vl ])
  (block_E' [ block_Z' <-- vl ]).
Proof.
  eapply length_length_eq in LC.
  eapply length_length_eq in LC'.
  general induction LC; inv LC'; simpl; eauto.
  eapply envCorr_update; eauto.
Qed.

Lemma alpha_exp_eval : forall ra ira e e' E E',
  alpha_exp ra ira e e' ->
  envCorr ra ira E E' ->
  exp_eval E e = exp_eval E' e'.
Proof.
  intros. general induction H; simpl in *; eauto.
  - erewrite IHalpha_exp; eauto.
  - erewrite IHalpha_exp1, IHalpha_exp2; eauto.
Qed.



Inductive alphaSim : F.state -> F.state -> Prop :=
 | alphaSimI ra ira s s' L L' E E' Ral
  (AE:alpha ra ira s s')
  (EA:AIR3 approx Ral L L')
  (EC:envCorr ra ira E E')
   : alphaSim (L, E, s) (L', E', s').


Lemma alphaSim_sim σ1 σ2
: alphaSim σ1 σ2 -> bisim σ1 σ2.
Proof.
  revert σ1 σ2; cofix; intros.
  destruct H; inversion AE; subst ra0 ira0; simpl in * |- *;
  try subst s s'; simpl in * |- *.
  - no_step. simpl. eapply alpha_exp_eval; eauto.
  - destruct (get_dec L (counted l)) as [[[Eb Zb sb]]|].
    decide (length Zb = length Y).
    case_eq (omap (exp_eval E) X); intros.
    + provide_invariants_3. simpl in *.
      one_step; simpl; try congruence; eauto.
      erewrite omap_agree_2; eauto. intros. symmetry.
      eapply alpha_exp_eval. eapply H0; eauto; eauto. hnf; intros; eauto.
      simpl. eapply alphaSim_sim; econstructor; eauto.
      eapply envCorr_update_list; eauto. exploit omap_length; eauto.
      rewrite map_length. congruence.
    + no_step. erewrite omap_agree_2 in H1; try eapply H.
      erewrite H1 in def. congruence.
      intros. eapply alpha_exp_eval. eapply H0; eauto. eauto.
    + provide_invariants_3; simpl in *. no_step. simpl in *.
      get_functional; subst. simpl in *. congruence.
      get_functional; subst. simpl in *. congruence.
    + no_step; eauto. provide_invariants_3; eauto.
  - case_eq (exp_eval E e); intros.
    one_step. erewrite <- alpha_exp_eval; eauto.
    eapply alphaSim_sim; econstructor; eauto using envCorr_update.
    no_step.
    erewrite alpha_exp_eval in H1; eauto. congruence.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    one_step. erewrite <- alpha_exp_eval; eauto.
    eapply alphaSim_sim; econstructor; eauto.
    one_step. erewrite <- alpha_exp_eval; eauto.
    eapply alphaSim_sim; econstructor; eauto.
    no_step; erewrite <- alpha_exp_eval in def; eauto.
    congruence. congruence.
  - remember (omap (exp_eval E) Y); intros. symmetry in Heqo.
    assert (omap (exp_eval E') Y' = o).
    erewrite omap_agree_2; eauto.
    intros. symmetry.
    eapply alpha_exp_eval. eapply H0; eauto; eauto. hnf; intros; eauto.
    destruct o.
    extern_step.
    + eexists; split. econstructor; eauto. congruence.
      eapply alphaSim_sim; econstructor; eauto using envCorr_update.
    + eexists; split. econstructor; eauto. congruence.
      eapply alphaSim_sim; econstructor; eauto using envCorr_update.
    + no_step.
  - one_step. eapply alphaSim_sim.
    econstructor; eauto.
    econstructor; eauto. econstructor; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
