Require Import Util Map Env EnvTy Exp IL ParamsMatch AllInRel Sim.

Import F.

Set Implicit Arguments.

Inductive alpha : env var -> env var -> stmt -> stmt -> Prop :=
| alpha_return ra ira x y 
  : ra x = y -> ira y = x -> alpha ra ira (stmtReturn x) (stmtReturn y)
| alpha_goto ra ira l X Y 
  : lookup_list ra X = Y -> lookup_list ira Y = X 
  -> alpha ra ira (stmtGoto l X) (stmtGoto l Y)
| alpha_assign ra ira x y e e' s s' 
  : alpha_exp ra ira e e' 
  -> alpha (ra[x<-y]) (ira[y <- x]) s s' -> alpha ra ira (stmtExp x e s) (stmtExp y e' s')
| alpha_if ra ira x y s s' t t' 
  : ra x = y -> ira y = x 
  -> alpha ra ira s s'
  -> alpha ra ira t t'
  -> alpha ra ira (stmtIf x s t) (stmtIf y s' t')
| alpha_let ra ira s s' Z Z' t t'
  : length Z = length Z'
  -> alpha (ra [ Z <-- Z']) (ira [ Z' <-- Z ]) s s' 
  -> alpha ra ira t t' -> alpha ra ira (stmtLet Z s t) (stmtLet Z' s' t').
 
Global Instance alpha_morph 
 : Proper (feq ==> feq ==> eq ==> eq ==> impl) alpha.
Proof. 
  unfold respectful, Proper, impl; intros; subst.
  general induction H3; econstructor; eauto;
  try (now rewrite <- H1; eauto);
  try (now rewrite <- H2; eauto).
  eapply alpha_exp_morph; eauto.
  eapply IHalpha. rewrite H0. reflexivity.
  rewrite H1; reflexivity.
  eapply IHalpha1. rewrite H0; reflexivity. 
  rewrite H1; reflexivity.
Qed.

Lemma alpha_refl s
  : alpha id id s s.
Proof.
  general induction s; eauto using alpha. 
  econstructor. eapply alpha_exp_refl.
  rewrite update_id; eauto.
  econstructor; eauto using lookup_id.

  econstructor; try rewrite update_with_list_id; eauto using length_eq_refl.
Qed.
  
Lemma alpha_sym ϱ ϱ' s s'
  : alpha ϱ ϱ' s s'
  ->alpha ϱ' ϱ s' s.
Proof.
  intros. general induction H; eauto using alpha, length_eq_sym.
  econstructor. eapply alpha_exp_sym. eauto. eauto.
Qed.

Lemma alpha_inverse_on  ϱ ϱ' s t
  : alpha ϱ ϱ' s t -> inverse_on (freeVars s) ϱ ϱ'. 
Proof.
  intros A. general induction A; simpl.
  + hnf; intros. cset_tac. rewrite H1. congruence.
  + eapply lookup_list_inverse_on; try intuition.
    rewrite H. rewrite H0. eauto.
  + hnf; intros. cset_tac. destruct H0; dcr.
    specialize (IHA x0 H1). lud.
    eapply alpha_exp_inverse_on; eauto.
  + eapply inverse_on_union. eapply inverse_on_union; eauto.
    hnf; intros; cset_tac. rewrite H1. congruence.
  + eapply inverse_on_union; eauto.
    eapply update_with_list_inverse_on; eauto.
Qed.

Lemma alpha_agree_on_morph f g ϱ ϱ' s t
  : alpha ϱ ϱ' s t 
  -> agree_on (lookup_set ϱ (freeVars s)) g ϱ'
  -> agree_on (freeVars s) f ϱ
  -> alpha f g s t.
Proof. 
  intros. general induction H; eauto; simpl in * |- *.
  + econstructor. rewrite H2; eauto. cset_tac; eauto.
    rewrite H1; eauto. eapply lookup_set_spec. intuition. eexists x; cset_tac; eauto.
  + econstructor. erewrite lookup_list_agree; eauto.
    erewrite lookup_list_agree; eauto. rewrite <- H. rewrite of_list_lookup_list; eauto. 
    intuition.
  + econstructor. eapply alpha_exp_agree_on_morph; eauto.
    eapply agree_on_incl; eauto. eapply lookup_set_incl; eauto. intuition.
    eapply union_subset_2. eapply agree_on_incl; eauto.
    eapply union_subset_2.
    eapply IHalpha; eauto. 
    - eapply agree_on_update_same. eapply agree_on_incl; eauto.
      hnf; intros. eapply lookup_set_spec. intuition.
      cset_tac; eqs. eapply lookup_set_spec in H4.
      destruct H4; dcr. eexists x0. lud.
      split; eqs. cset_tac. left. split; eauto. intuition.
    - eapply agree_on_update_same. eapply agree_on_incl; eauto.
      cset_tac; eqs; intuition. 
  + econstructor; eauto. rewrite H4; eauto. cset_tac; intuition.
    rewrite H3; eauto. eapply lookup_set_spec; try intuition.
    eexists x; cset_tac; intuition.
    - eapply IHalpha1. eapply agree_on_incl; eauto.
      eapply lookup_set_incl; intuition.
      cset_tac; intuition. 
      eapply agree_on_incl; eauto. cset_tac; intuition.
    - eapply IHalpha2. eapply agree_on_incl; eauto.
      eapply lookup_set_incl; intuition.
      cset_tac; intuition. 
      eapply agree_on_incl; eauto. cset_tac; intuition.
  + econstructor; eauto.
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
  -> agree_on (freeVars s) f ϱ
  -> alpha f g s t.
Proof. 
  intros. eapply alpha_agree_on_morph; eauto.
  symmetry in H1.
  eapply inverse_on_agree_on_2; eauto. 
  intuition. intuition. intuition. intuition.
  eapply inverse_on_agree_on; eauto; try intuition.
  eapply alpha_inverse_on in H.
  eapply inverse_on_agree_on; try eassumption; try intuition.
  eapply inverse_on_agree_on_2; eauto; try intuition.
Qed.

Lemma alpha_trans ϱ1 ϱ1' ϱ2 ϱ2' s s' s''
  : alpha ϱ1 ϱ1' s s' -> alpha ϱ2 ϱ2' s' s'' -> alpha (ϱ1 ∘ ϱ2) (ϱ2' ∘ ϱ1') s s''.
Proof.
  intros. general induction H. 
  + inversion H1. econstructor; subst y0 y; eauto. unfold comp. rewrite H6. congruence.
  + inversion H1. econstructor; rewrite comp_lookup_list; try rewrite H; try rewrite H8; eauto.
  + inversion H1. econstructor; eauto. eapply alpha_exp_trans; eauto.
    subst x0 s0 e0 ra0 ira0 s''.
    specialize (IHalpha _ _ _ H9).
    eapply alpha_inverse_on in H0.
    eapply alpha_inverse_on_agree; eauto. 
    eapply inverse_on_comp; eauto. eapply alpha_inverse_on; eauto.
    symmetry. eapply lookup_set_agree_on_comp. intuition.
    eapply inverse_on_update_lookup_set. intuition. eauto.
  + inversion H3. subst ra0 ira0 x0 s0 t0 s''. econstructor.
    unfold comp. congruence. unfold comp. congruence.
    eapply IHalpha1; eauto. eapply IHalpha2; eauto.
  + inversion H2. subst ra0 ira0 Z0 s0 t0 s''.
    econstructor. congruence. 
    specialize (IHalpha1 _ _ _ H10).
    eapply alpha_inverse_on_agree; eauto.
    eapply alpha_inverse_on in IHalpha1.
    pose proof (inverse_on_comp_list _ _ _ H H8 IHalpha1).
    pose proof (inverse_on_sym IHalpha1); try (now intuition).
    pose proof H3.
    eapply inverse_on_comp_list in H4; try (now intuition); eauto.
    eapply inverse_on_agree_on; eauto; try intuition.
    
    symmetry. eapply inverse_on_comp_list; eauto.
    intuition. intuition. instantiate (1:=ira). intuition.
    instantiate (1:=ϱ2'). intuition. eapply alpha_inverse_on; eauto.
    
    eapply IHalpha2; eauto.
Qed.




Definition envCorr ra ira (E E':env val) :=
  forall x y, ra x = y -> ira y = x -> E x = E' y.


Lemma envCorr_idOn_refl (E:env val)
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

Lemma alpha_exp_eval : forall ra ira e e' E E',
  alpha_exp ra ira e e' -> 
  envCorr ra ira E E' -> 
  exp_eval E e = exp_eval E' e'.
Proof.
  intros. general induction H; simpl in *; eauto.
  - erewrite IHalpha_exp1, IHalpha_exp2; eauto.
Qed.



Inductive alphaSim : F.state -> F.state -> Prop :=
 | alphaSimI ra ira s s' L L' E E' Ral
  (AE:alpha ra ira s s')
  (EA:AIR3 approx Ral L L')
  (EC:envCorr ra ira E E')
   : alphaSim (L, E, s) (L', E', s').


Lemma alphaSim_sim σ1 σ2
: alphaSim σ1 σ2 -> sim σ1 σ2.
Proof. 
  revert σ1 σ2; cofix; intros.
  destruct H; inversion AE; subst ra0 ira0; simpl in * |- *;
  try subst s s'; simpl in * |- *.
  + eapply simE; try eapply star_refl; simpl; try stuck.
    erewrite EC; eauto.
  + assert (length X = length Y). {
      rewrite <- H. rewrite lookup_list_length; eauto.
    }
    destruct (get_dec L (counted l)) as [[[Eb Zb sb]]|]; [| try no_step].
    destruct_prop (length Zb = length Y); [| try no_step].
    provide_invariants_3. subst x1 x x0 x2 ; simpl in *.
    one_step; simpl; try congruence; eauto.
    simpl. eapply alphaSim_sim; econstructor; eauto. 
    eapply envCorr_update_lists; eauto; congruence.
    clear H H0; no_step. get_functional; subst; simpl in *; congruence.
    provide_invariants_3; simpl in *; congruence.
    clear H H0; no_step; provide_invariants_3; eauto.
  + case_eq (exp_eval E e); intros.
    eapply simS; try eapply plusO. 
    econstructor; eauto. 
    econstructor; eauto. instantiate (1:=v).
    erewrite <- alpha_exp_eval; eauto.
    eapply alphaSim_sim; econstructor; eauto using envCorr_update.
    eapply simE; try eapply star_refl; eauto; stuck.
    erewrite alpha_exp_eval in H1; eauto. congruence.
  + case_eq (val2bool (E x)); intros. 
    eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto. erewrite <- EC; eauto.
    eapply alphaSim_sim; econstructor; eauto.
    eapply simS; try eapply plusO.
    eapply F.stepIfF; eauto.
    eapply F.stepIfF; eauto. erewrite <- EC; eauto.
    eapply alphaSim_sim; econstructor; eauto.
  + eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    eapply alphaSim_sim.
    econstructor; eauto.
    econstructor; eauto. econstructor; eauto.
Qed.

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
