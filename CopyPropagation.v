Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL ParamsMatch Sim Alpha Coherence Fresh.

Require Import Liveness.

Set Implicit Arguments.
Unset Printing Records.

Fixpoint subst (ϱ:env var) (s:stmt) : stmt :=
  match s with
    | stmtExp x e s => let x' := fresh (lookup_set ϱ (freeVars s)) in
                       stmtExp x' (rename_exp ϱ e) (subst (ϱ[x <- x']) s)
    | stmtIf x s t => stmtIf (ϱ x) (subst ϱ s) (subst ϱ t)
    | stmtGoto l Y => stmtGoto l (lookup_list ϱ Y)
    | stmtReturn x => stmtReturn (ϱ x)
    | stmtLet Z s t => let Z' := fresh_list (lookup_set ϱ (freeVars s)) (length Z) in
                       stmtLet Z' (subst (ϱ[Z <-- Z']) s) (subst ϱ t)
  end.  

Fixpoint copyPropagate (ϱ:var -> var) (s:stmt) : stmt :=
  match s with
   | stmtExp x (Var y) s => copyPropagate (ϱ[x <- ϱ y]) s
   | stmtExp x e s => let x' := fresh (lookup_set ϱ (freeVars s)) in
                        stmtExp x' e (copyPropagate (ϱ[x <- x']) s)
   | stmtIf x s1 s2 => stmtIf (ϱ x) (copyPropagate ϱ s1) (copyPropagate ϱ s2)
   | stmtGoto l Y => stmtGoto l (lookup_list ϱ Y)
   | stmtReturn x => stmtReturn (ϱ x)
   | stmtLet Z s1 s2 => 
     let Z' := fresh_list (lookup_set ϱ (freeVars s1)) (length Z) in
     stmtLet Z' (copyPropagate (ϱ[Z <-- Z']) s1) (copyPropagate ϱ s2)
   end.

Notation "f '[' L ']'" := (lookup_list f L) (at level 70).

Instance ctxeq_equivalence : Equivalence ctxeq.
Proof.
  hnf; intros. constructor.
  hnf; intros. eapply ctxeq_simeq; reflexivity.
  hnf; intros. eapply ctxeq_simeq; eapply ctxeq_simeq in H; symmetry; eauto.
  hnf; intros. eapply ctxeq_simeq. eapply ctxeq_simeq in H; eapply ctxeq_simeq in H0;
                                   transitivity y; eauto.
Qed.

Lemma comp_update (ϱ1: var -> var) x (v:val) (E:var -> val) D
 : x ∈ D ->
   injective_on D ϱ1
   -> agree_on D ((ϱ1 ∘ E) [x <- v]) ((ϱ1 ∘ E[ϱ1 x <- v])).
Proof.
  intros. unfold comp.  hnf; intros. lud.
  rewrite e in H4. exfalso. eapply H4. reflexivity.
  exfalso. eapply H3. eapply H0; eauto. 
Qed.

Lemma comp_update_2 (ϱ1: var -> var) x (v:var) (E:var -> val) D
 : agree_on D ((ϱ1 ∘ E) [x <- E v]) ((ϱ1[x <- v] ∘ E)).
Proof.
  intros. unfold comp.  hnf; intros. lud.
Qed.

Lemma comp_update_3 (ϱ1: var -> var) x (v:val) (E:var -> val) D
 : ϱ1 x = x 
   -> x ∉ lookup_set ϱ1 (D\{{x}})
   -> agree_on D ((ϱ1 ∘ E) [x <- v]) ((ϱ1 ∘ E[x <- v])).
Proof.
  intros. unfold comp.  hnf; intros. lud. 
  rewrite <- H in e. exfalso. eapply H5. rewrite H2. eauto.
  exfalso. eapply H0. eapply lookup_set_spec. intuition. 
  eexists; split; eauto. cset_tac; eauto.
Qed.

Lemma exp_rename_shift E e ϱ
 : exp_eval (ϱ ∘ E) e = exp_eval E (rename_exp ϱ e).
Proof.
  general induction e; simpl; eauto.
  - rewrite IHe1, IHe2; reflexivity.
Qed.

Lemma rename_contr s ϱ ϱ'
: rename ϱ (rename ϱ' s) = rename (ϱ' ∘ ϱ) s.
Proof.
  unfold comp.
  general induction s; simpl;  f_equal; eauto. eapply rename_exp_comp.
  rewrite <- comp_lookup_list. reflexivity.
  rewrite <- comp_lookup_list. reflexivity.
Qed.

Lemma exp_subst_agree (ϱ ϱ':var->var) (E E' : var -> val) (e:exp)
: agree_on (Exp.freeVars e) (ϱ ∘ E) (ϱ' ∘ E')
  -> exp_eval E (rename_exp ϱ e) = exp_eval E' (rename_exp ϱ' e).
Proof.
  general induction e; simpl; eauto. f_equal; eapply H. simpl; cset_tac; eauto.
  - simpl in *. erewrite IHe1, IHe2; try reflexivity; eapply agree_on_incl; eauto;
                cset_tac; intuition.
Qed.


Lemma agree_on_comp_fresh (ϱ:var -> var) (E: var -> var) x x' y (D: set var)
  : x' ∉ lookup_set ϱ D 
    -> agree_on D (ϱ [x <- y] ∘ E)
                (ϱ [x <- x'] ∘ E [x' <- E y]).
Proof.
  intros. hnf; intros. unfold comp.
  lud. exfalso; eauto.
  exfalso. eapply H. eapply lookup_set_spec. intuition. eexists x0; intuition.
Qed.

Lemma agree_on_comp_fresh_both (ϱ ϱ':var -> var) (E E': var -> var) x y y' (v:val) (D: set var)
 : y ∉ lookup_set ϱ D
   -> y' ∉ lookup_set ϱ' D
   -> agree_on (D\{{x}}) (ϱ ∘ E) (ϱ' ∘ E')
   -> agree_on D (ϱ [x <- y] ∘ E [y <- v]) (ϱ' [x <- y'] ∘ E' [y' <- v]).
Proof.
  intros. hnf; intros. simpl. unfold comp.
  lud. hnf in H4; congruence.
  exfalso. eapply H. eapply lookup_set_spec; intuition. eexists x0; intuition.
  exfalso. hnf in H4; congruence.
  exfalso. hnf in H4; congruence.
  exfalso. eapply H0. eapply lookup_set_spec; intuition. eexists x0; intuition.
  eapply H1; eauto. cset_tac; intuition.
Qed.

Lemma agree_on_comp_fresh_both_list (ϱ ϱ':var -> var) (E E': var -> var) Z Y Y' (VL: list val) (D: set var)
 : length Z = length Y
   -> length Y = length Y'
   -> length Y' = length VL
   -> unique Y
   -> unique Y'
   -> (of_list Y) ∩ lookup_set ϱ D [=] ∅
   -> (of_list Y') ∩ lookup_set ϱ' D [=] ∅
   -> agree_on (D\of_list Z) (ϱ ∘ E) (ϱ' ∘ E')
   -> agree_on D (ϱ [Z <-- Y] ∘ E [Y <-- VL]) (ϱ' [Z <-- Y'] ∘ E' [Y' <-- VL]).
Proof.
  intros.
  eapply length_length_eq in H.
  eapply length_length_eq in H0.
  eapply length_length_eq in H1.
  hnf; intros. simpl. unfold comp. destruct_prop (x ∈ of_list Z).
  clear H6.
  general induction H; inv H0; inv H1; simpl in * |- *.
  exfalso. eapply (not_in_empty x); eauto.
  hnf; intros. unfold comp. lud.
  exfalso. eapply H9; reflexivity.
  exfalso. 
  destruct_prop (x0 ∈ of_list XL).
  assert (y ∈ of_list YL). rewrite e.
  eapply update_with_list_lookup_in; eauto using length_eq_length.
  eapply H2. eapply InA_in in H12. eauto.
  assert (ϱ x0 = y).
  eapply update_with_list_lookup_not_in; eauto. 
  refine (not_in_empty y _). rewrite <- H4. cset_tac; intuition.
  exfalso. eapply H8; reflexivity.
  exfalso. eapply H8; reflexivity.
  exfalso. 
  destruct_prop (x0 ∈ of_list XL).
  assert (y0 ∈ of_list YL0). rewrite e.
  eapply update_with_list_lookup_in; eauto using length_eq_length,length_eq_trans.
  eapply H3. eapply InA_in in H12. eauto.
  assert (ϱ' x0 = y0).
  eapply update_with_list_lookup_not_in; eauto. 
  refine (not_in_empty y0 _). rewrite <- H5. cset_tac; intuition.
  eapply (IHlength_eq _ _ _ _ _ _ D); eauto. intuition. intuition.
  cset_tac; intuition. eapply H4; split; eauto. cset_tac; intuition.
  cset_tac; intuition. eapply H5; split; eauto. cset_tac; intuition.
  cset_tac; intuition.
  assert ((ϱ [Z <-- Y]) x = ϱ x). 
  erewrite (update_with_list_lookup_not_in ϱ); eauto.
  assert ((ϱ' [Z <-- Y']) x = ϱ' x). 
  erewrite (update_with_list_lookup_not_in ϱ'); eauto.
  rewrite H8, H9.
  assert ((E [Y <-- VL]) (ϱ x) = E (ϱ x)). 
  erewrite (update_with_list_lookup_not_in E); eauto.
  cset_tac; intuition. eapply H4; split; eauto. 
  eapply lookup_set_spec. intuition. eexists; eauto.
  assert ((E' [Y' <-- VL]) (ϱ' x) = E' (ϱ' x)). 
  erewrite (update_with_list_lookup_not_in E'); eauto.
  cset_tac; intuition. eapply H5; split; eauto. 
  eapply lookup_set_spec. intuition. eexists; eauto.
  rewrite H10, H11. eapply H6. cset_tac; intuition.
Qed.


Lemma subst_fresh L L' (E E':var -> val) s (ϱ ϱ':var->var)
 : simL L L'
   -> agree_on (freeVars s) (ϱ ∘ E) (ϱ' ∘ E')
   -> sim (L, E, subst ϱ s)
          (L', E' , subst ϱ' s).
Proof.
  general induction s; simpl in * |- *.
  case_eq (exp_eval E (rename_exp ϱ e)); intros.
  eapply simS; try eapply plusO.
  constructor; eauto.
  econstructor. erewrite <- exp_subst_agree; eauto. 
  eapply agree_on_incl; eauto. cset_tac; intuition.
  eapply IHs; eauto. 
  eapply agree_on_comp_fresh_both; eauto using fresh_spec.
  eapply agree_on_incl; eauto. cset_tac; intuition.
  eapply simE; try eapply star_refl; simpl; eauto. stuck. stuck.
  erewrite exp_subst_agree in def; eauto. rewrite def in H1. congruence.
  eapply agree_on_incl. eapply agree_on_sym. eauto. cset_tac; intuition.
  + case_eq (val2bool (E (ϱ x))); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto. specialize (H0 x). unfold comp in H0.
    rewrite <- H0; eauto. cset_tac; intuition.
    eapply IHs1; eauto. eapply agree_on_incl; eauto. cset_tac; intuition.
    eapply simS; try eapply plusO.
    econstructor 3; eauto.
    econstructor 3; eauto. specialize (H0 x). unfold comp in H0.
    rewrite <- H0; eauto. cset_tac; intuition.
    eapply IHs2; eauto. eapply agree_on_incl; eauto. cset_tac; intuition.
  + destruct (get_dec L (counted l)). destruct s as [[]].
    destruct_prop (length block_Z = length Y). 
    unfold simL in H.
    edestruct AIR4_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR4_nth as [?[?]]; try eassumption; dcr. 
    simpl in *. repeat get_functional; subst.
    inv H9. eapply simS; try eapply plusO.
    econstructor; eauto. simpl. rewrite lookup_list_length. congruence.
    econstructor; eauto. simpl. rewrite lookup_list_length. congruence.
    simpl. unfold updE. 
    assert (lookup_list E (lookup_list ϱ Y) = lookup_list E' (lookup_list ϱ' Y)).
    repeat rewrite <- comp_lookup_list.
    eauto using lookup_list_agree.
    rewrite H2. eapply H14. repeat rewrite lookup_list_length. congruence. congruence.
    eapply simE; try eapply star_refl; eauto; stuck.
    get_functional; subst. eapply n. simpl in *. rewrite len.
    rewrite lookup_list_length; eauto.
    edestruct AIR4_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR4_nth as [?[?]]; try eassumption; dcr. 
    simpl in *. repeat get_functional; subst.
    inv H9; simpl in *. eapply n. rewrite lookup_list_length in len. congruence.
    eapply simE; try eapply star_refl; eauto; stuck; eauto.
    edestruct AIR4_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption. eauto.
  + eapply simE; try eapply star_refl; simpl; eauto; try stuck. 
    f_equal. eapply H0; simpl; cset_tac; eauto.
  + simpl in * |- *.
    eapply simS; try eapply plusO.
    econstructor. econstructor.
    eapply IHs2; eauto. eapply simL_extension; eauto. 
    hnf; intros. eapply IHs1; eauto. 
    eapply agree_on_comp_fresh_both_list;
      repeat rewrite fresh_list_length; eauto;
      eauto using fresh_list_unique, fresh_list_spec.
    repeat rewrite fresh_list_length in *. congruence. 
    repeat rewrite fresh_list_length in *. 
    
    eapply agree_on_incl; eauto. cset_tac; intuition.
    rewrite fresh_list_length; eauto.
    rewrite fresh_list_length; eauto. 
    eapply agree_on_incl; eauto. cset_tac; intuition.
Qed.

Lemma sim_CP s ϱ 
: simeq (copyPropagate ϱ s) (subst ϱ s).
Proof. 
  general induction s; simpl in * |- *. 
  + destruct e; hnf; intros.
    - one_step. reflexivity. reflexivity. 
      unfold simeq in IHs. eapply IHs; eauto.
    - eapply sim_expansion_closed.
      Focus 2. eapply star_refl.
      Focus 2. eapply S_star. econstructor. simpl. reflexivity. eapply star_refl.
      simpl in * |- *.
      refine (sim_trans (IHs _ _ _) _ ); eauto.
      eapply subst_fresh. eapply simL_refl. eapply agree_on_comp_fresh.
      eapply fresh_spec.
    - 
      exfalso; clear_all; admit.
  + transitivity (stmtIf (ϱ x) (copyPropagate ϱ s1) (subst ϱ s2)). 
    eapply (simeq_contextual (ctxIfT (ϱ x) _ ctxHole)); eauto.
    eapply (simeq_contextual (ctxIfS (ϱ x) ctxHole _)); eauto.
  + eapply simeq_refl.
  + eapply simeq_refl.
  + eapply simeq_trans.
    eapply (simeq_contextual (ctxLetT _ _ ctxHole)); eauto.
    eapply (simeq_contextual (ctxLetS _ ctxHole _)). eapply IHs1; eauto.
Qed.

Lemma lookup_set_id {X} `{H : OrderedType X} (s : set X)
: s [=] lookup_set id s.
Proof.
  unfold lookup_set. 
  hnf; intros. rewrite map_spec; unfold id; simpl; intuition.
  eexists a; intuition. destruct H0; cset_tac.
Qed.

Instance fresh_morph
: Proper (Equal ==> eq) fresh.
Proof.
  unfold Proper, respectful; intros.
  admit.
Qed.

Lemma subst_id s
  : simeq s (subst id s).
Proof.
  general induction s; simpl;
  repeat rewrite <- lookup_set_id.
  
Admitted.

Lemma CP_tv s s' C C' D D'
  : ssa C s C' -> ssa D s' D'
  -> copyPropagate id s = copyPropagate id s'
  -> simeq s s'.
Proof.
  intros. 
  pose proof (simeq_trans (subst_id _) (simeq_sym (sim_CP s _ ))); eauto.
  pose proof (simeq_trans (subst_id _) (simeq_sym (sim_CP s' _ ))); eauto.
  eapply simeq_sym in H3. rewrite <- H1 in H3.
  eapply simeq_trans; eauto.  
Qed.

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
