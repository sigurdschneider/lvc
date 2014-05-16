Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Sim Fresh MoreExp.

Set Implicit Arguments.
Unset Printing Records.

Fixpoint subst (ϱ:env var) (s:stmt) : stmt :=
  match s with
    | stmtExp x e s => let x' := fresh_stable (lookup_set ϱ (freeVars s \ {{x}})) x in
                       stmtExp x' (rename_exp ϱ e) (subst (ϱ[x <- x']) s)
    | stmtIf e s t => stmtIf (rename_exp ϱ e) (subst ϱ s) (subst ϱ t)
    | stmtGoto l Y => stmtGoto l (List.map (rename_exp ϱ) Y)
    | stmtReturn e => stmtReturn (rename_exp ϱ e)
    | stmtLet Z s t => let Z' := fresh_stable_list (lookup_set ϱ (freeVars s \ of_list Z)) Z in
                       stmtLet Z' (subst (ϱ[Z <-- Z']) s) (subst ϱ t)
  end.
Notation "f '[' L ']'" := (lookup_list f L) (at level 70).

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
  general induction s; simpl;  f_equal; eauto using rename_exp_comp, comp_lookup_list.
  rewrite map_map. eapply map_ext_get_eq.
  intros. rewrite rename_exp_comp. reflexivity.
Qed.

Lemma exp_subst_agree (ϱ ϱ':var->var) (E E' : onv val) (e:exp)
: agree_on (Exp.freeVars e) (ϱ ∘ E) (ϱ' ∘ E')
  -> exp_eval E (rename_exp ϱ e) = exp_eval E' (rename_exp ϱ' e).
Proof.
  general induction e; simpl; eauto.
  exploit (H v); simpl. cset_tac; intuition.
  unfold comp in X. simpl in X. inv X; eauto.
  - simpl in *. erewrite IHe1, IHe2; try reflexivity; eapply agree_on_incl; eauto;
                cset_tac; intuition.
Qed.


Lemma agree_on_comp_fresh (ϱ:var -> var) (E: var -> var) x x' y (D: set var)
  : x' ∉ lookup_set ϱ (D \ {{x}})
    -> agree_on D (ϱ [x <- y] ∘ E)
                (ϱ [x <- x'] ∘ E [x' <- E y]).
Proof.
  intros. hnf; intros. unfold comp.
  lud. exfalso; eauto.
  exfalso. eapply H. eapply lookup_set_spec. intuition.
  eexists x0; cset_tac; intuition.
Qed.

Lemma agree_on_comp_fresh_shift X `{Equivalence X} (ϱ:var -> var) (E E': env X) x y (v:X) (D: set var)
 : y ∉ lookup_set ϱ (D\{{x}})
   -> agree_on (D\{{x}}) (ϱ ∘ E) E'
   -> agree_on D (ϱ [x <- y] ∘ E [y <- v]) (E' [x <- v]).
Proof.
  intros. hnf; intros. simpl. unfold comp.
  lud.
  - exfalso. eapply H0. eapply lookup_set_spec; intuition.
    eexists x0; intuition. cset_tac; intuition.
  - exfalso. hnf in H4; congruence.
  - eapply H1; eauto. cset_tac; intuition.
Qed.


Lemma agree_on_comp_fresh_both X `{Equivalence X} (ϱ ϱ':env var) (E E': env X) (x y:var) (y':var) (v:X) (D: set var)
 : y ∉ lookup_set ϱ (D\{{x}})
   -> y' ∉ lookup_set ϱ' (D\{{x}})
   -> agree_on (D\{{x}}) (ϱ ∘ E) (ϱ' ∘ E')
   -> agree_on D (ϱ [x <- y] ∘ E [y <- v]) (ϱ' [x <- y'] ∘ E' [y' <- v]).
Proof.
  intros.
  eapply agree_on_trans. eapply agree_on_comp_fresh_shift; eauto.
  eapply agree_on_sym. eapply agree_on_comp_fresh_shift; eauto using agree_on_refl.
Qed.

Lemma agree_on_comp_fresh_both_list X `{Equivalence X} (ϱ ϱ':var -> var) (E E': env X) Z Y Y' (VL: list X) (D: set var)
 : length Z = length Y
   -> length Y = length Y'
   -> length Y' = length VL
   -> unique Y
   -> unique Y'
   -> (of_list Y) ∩ lookup_set ϱ D [=] ∅
   -> (of_list Y') ∩ lookup_set ϱ' D [=] ∅
   -> agree_on D (ϱ ∘ E) (ϱ' ∘ E')
   -> agree_on (D ∪ of_list Z) (ϱ [Z <-- Y] ∘ E [Y <-- VL]) (ϱ' [Z <-- Y'] ∘ E' [Y' <-- VL]).
Proof.
  intros.
  eapply length_length_eq in H0.
  eapply length_length_eq in H1.
  eapply length_length_eq in H2.
  hnf; intros. simpl. unfold comp. decide (x ∈ of_list Z).
  clear H7.
  general induction H0; inv H1; inv H2; simpl in * |- *.
  exfalso. eapply (not_in_empty x); eauto.
  hnf; intros. unfold comp. lud.
  exfalso. eapply H10; reflexivity.
  exfalso.
  decide (x0 ∈ of_list XL).
  assert (y ∈ of_list YL). rewrite e.
  eapply update_with_list_lookup_in; eauto using length_eq_length.
  eapply H3. eapply InA_in in H13. eauto.
  assert (ϱ x0 = y).
  eapply update_with_list_lookup_not_in; eauto.
  refine (not_in_empty y _). rewrite <- H5. cset_tac; intuition.
  exfalso. eapply H9; reflexivity.
  exfalso. eapply H9; reflexivity.
  exfalso.
  decide (x0 ∈ of_list XL).
  assert (y0 ∈ of_list YL0). rewrite e.
  eapply update_with_list_lookup_in; eauto using length_eq_length,length_eq_trans.
  eapply H4. eapply InA_in in H13. eauto.
  assert (ϱ' x0 = y0).
  eapply update_with_list_lookup_not_in; eauto.
  refine (not_in_empty y0 _). rewrite <- H6. cset_tac; intuition.
  eapply (IHlength_eq _ _ _ _ _ _ _ _ _ D); eauto. intuition. intuition.
  - rewrite <- H5. cset_tac; intuition.
    hnf in H18; hnf in H8; subst a. exfalso.
    eapply (H5 y). split; cset_tac; intuition.
    hnf in H3; hnf in H; subst a. exfalso.
    eapply (H5 y). split; cset_tac; intuition.
  - rewrite <- H6. cset_tac; intuition.
    hnf in H8; subst a. exfalso.
    eapply (H3 y0). split; cset_tac; intuition.
    hnf in H; subst a. exfalso.
    eapply (H3 y0). split; cset_tac; intuition.
  - cset_tac; intuition.
  - cset_tac; intuition.
  - assert ((ϱ [Z <-- Y]) x = ϱ x).
    erewrite (update_with_list_lookup_not_in ϱ); eauto.
    assert ((ϱ' [Z <-- Y']) x = ϱ' x).
    erewrite (update_with_list_lookup_not_in ϱ'); eauto.
    rewrite H9, H10.
    assert ((E [Y <-- VL]) (ϱ x) = E (ϱ x)).
    Lemma update_with_list_lookup_not_in {X} `{OrderedType X} {Y} (f:X->Y) (Z:list X) (Z':list Y) x y
    : x ∉ of_list Z
      -> f [ Z <-- Z' ] x = y
      -> f x = y.
    Proof.
      general induction Z; simpl in * |- *; eauto.
      destruct Z'; eauto. lud. rewrite add_iff in H0.
      exfalso; firstorder.
      eapply IHZ; eauto. intro. eapply H0. eapply add_2; eauto.
    Qed.
    erewrite (update_with_list_lookup_not_in E); eauto.
    cset_tac; intuition. eapply H5; split; eauto.
    eapply lookup_set_spec. intuition. eexists; eauto.
    assert ((E' [Y' <-- VL]) (ϱ' x) = E' (ϱ' x)).
    erewrite (update_with_list_lookup_not_in E'); eauto.
    cset_tac; intuition. eapply H6; split; eauto.
    eapply lookup_set_spec. intuition. eexists; eauto.
    rewrite H11, H12. eapply H7. cset_tac; intuition.
Qed.

Lemma agree_on_comp_fresh_shift_list X `{Equivalence X} (ϱ:env var)
      (E E': env X) Z Y (VL: list X) (D: set var)
 : length Z = length Y
   -> length Y = length VL
   -> unique Y
   -> (of_list Y) ∩ lookup_set ϱ D [=] ∅
   -> agree_on D (ϱ ∘ E) E'
   -> agree_on (D ∪ of_list Z) (ϱ [Z <-- Y] ∘ E [Y <-- VL]) (E' [Z <-- VL]).
Proof.
  intros.
  eapply length_length_eq in H0.
  eapply length_length_eq in H1.
  hnf; intros. simpl. unfold comp. decide (x ∈ of_list Z).
  clear H4.
  general induction H0; inv H1; simpl in * |- *.
  - exfalso. eapply (not_in_empty x); eauto.
  - lud.
    + exfalso. decide (x0 ∈ of_list XL).
      * assert (y ∈ of_list YL).
        { rewrite e.
          eapply update_with_list_lookup_in; eauto using length_eq_length.
        }
        eapply H2. eapply InA_in in H8. eauto.
      * assert (ϱ x0 = y).
        eapply update_with_list_lookup_not_in; eauto.
        refine (not_in_empty y _). rewrite <- H3. cset_tac; intuition.
    + exfalso. eapply H4; reflexivity.
    + eapply (IHlength_eq _ _ _ _ _ _ _ D); eauto. intuition.
      * rewrite <- H3. cset_tac; intuition.
        hnf in H5; subst a. exfalso.
        eapply (H2 y). split; cset_tac; intuition.
        hnf in H; subst a. exfalso.
        eapply (H2 y). split; cset_tac; intuition.
      * cset_tac; intuition.
      * cset_tac; intuition.
  - assert ((ϱ [Z <-- Y]) x = ϱ x).
    erewrite (update_with_list_lookup_not_in ϱ); eauto.
    rewrite H6.
    assert ((E [Y <-- VL]) (ϱ x) = E (ϱ x)).
    erewrite (update_with_list_lookup_not_in E); eauto.
    cset_tac; intuition. eapply H3; split; eauto.
    eapply lookup_set_spec. intuition. eexists; eauto.
    assert ((E' [Z <-- VL]) x = E' x).
    erewrite (update_with_list_lookup_not_in E'); eauto.
    cset_tac; intuition. rewrite H7. rewrite H8.
    eapply H4. eauto.
Qed.

Lemma exp_subst_agree_list E E' Y ϱ ϱ'
:  agree_on (list_union (List.map Exp.freeVars Y)) (ϱ ∘ E) (ϱ' ∘ E')
   -> forall (n : nat) (x y : exp),
       get (List.map (rename_exp ϱ) Y) n x ->
       get (List.map (rename_exp ϱ') Y) n y -> exp_eval E x = exp_eval E' y.
Proof.
  intros. edestruct map_get_4; eauto; dcr; subst.
  edestruct map_get_4; try eapply H0; eauto; dcr; subst.
  get_functional; subst.
  eapply exp_subst_agree. eapply agree_on_incl; eauto.
  eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
Qed.

Lemma subst_fresh L L' (E E':onv val) s (ϱ ϱ':var->var)
 : simL L L'
   -> agree_on (freeVars s) (ϱ ∘ E) (ϱ' ∘ E')
   -> sim (L, E, subst ϱ s)
          (L', E' , subst ϱ' s).
Proof.
  general induction s; simpl in * |- *.
  - case_eq (exp_eval E (rename_exp ϱ e)); intros.
    one_step.
    erewrite <- exp_subst_agree; eauto.
    eapply agree_on_incl; eauto. cset_tac; intuition.
    eapply IHs; eauto.
    eapply agree_on_comp_fresh_both; eauto using fresh_stable_spec.
    eapply agree_on_incl; eauto. cset_tac; intuition.
    no_step.
    erewrite exp_subst_agree in def; eauto. rewrite def in H1. congruence.
    eapply agree_on_incl. eapply agree_on_sym. eauto. cset_tac; intuition.
  - case_eq (exp_eval E (rename_exp ϱ e)); intros.
    pose proof H1. erewrite exp_subst_agree in H2; [|
    eapply agree_on_incl; eauto; eapply incl_right].
    case_eq (val2bool v); intros.
    one_step.
    eapply IHs1; eauto. eapply agree_on_incl; eauto. cset_tac; intuition.
    one_step.
    eapply IHs2; eauto. eapply agree_on_incl; eauto. cset_tac; intuition.
    pose proof H1. erewrite exp_subst_agree in H2; [|
    eapply agree_on_incl; eauto; eapply incl_right].
    no_step.
  - destruct (get_dec L (counted l)). destruct s as [[]].
    decide (length block_Z = length Y).
    case_eq (omap (exp_eval E) (List.map (rename_exp ϱ) Y)); intros.
    + pose proof H1.
      erewrite omap_agree_2 with (L':=List.map (rename_exp ϱ') Y) in H2;
        eauto using exp_subst_agree_list; try repeat rewrite map_length; eauto.
      unfold simL in H.
      edestruct AIR4_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption.
      edestruct AIR4_nth as [?[?]]; try eassumption; dcr.
      simpl in *. repeat get_functional; subst.
      inv H11.
      one_step. simpl. rewrite map_length; congruence.
      simpl. rewrite map_length; congruence.
      exploit (omap_length); eauto. rewrite map_length in X.
      simpl. eapply H16; eauto. rewrite map_length. congruence.
    + no_step.
      erewrite <- omap_agree_2 in def; eauto using exp_subst_agree_list.
      erewrite def in H1. congruence.
      repeat rewrite map_length; eauto.
    + no_step.
      get_functional; subst. eapply n. simpl in *. rewrite len.
      rewrite map_length; eauto.
      edestruct AIR4_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption.
      edestruct AIR4_nth as [?[?]]; try eassumption; dcr.
      simpl in *. repeat get_functional; subst.
      inv H9; simpl in *. eapply n. rewrite map_length in len. congruence.
    + no_step; eauto.
      edestruct AIR4_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption. eauto.
  - no_step. simpl.
    eapply exp_subst_agree; eauto.
  - simpl in * |- *.
    eapply simS; try eapply plusO.
    econstructor. econstructor.
    eapply IHs2; eauto. eapply simL_extension; eauto.
    hnf; intros. eapply IHs1; eauto.
    assert (freeVars s1 ⊆ (freeVars s1 \ of_list Z) ∪ of_list Z). {
      cset_tac; intuition. decide (a ∈ of_list Z); intuition.
    }
    eapply agree_on_incl; eauto.                                                        eapply agree_on_comp_fresh_both_list;
      repeat rewrite fresh_stable_list_length; eauto;
      eauto using fresh_stable_list_unique, fresh_stable_list_spec.
    repeat rewrite fresh_stable_list_length in *. congruence.

    repeat rewrite fresh_stable_list_length in *.
    eapply agree_on_incl; eauto. cset_tac; intuition.
    repeat rewrite fresh_stable_list_length; eauto.
    eapply agree_on_incl; eauto. cset_tac; intuition.
Qed.

Lemma rename_exp_id e
  : rename_exp id e = e.
Proof.
  induction e; simpl; eauto.
  -  rewrite IHe1, IHe2; eauto.
Qed.

Lemma omap_exp_rename_shift_list (E E':onv val) ϱ Y
: agree_on (list_union (List.map Exp.freeVars Y)) E (ϱ ∘ E')
  ->  forall (n : nat) (x y : exp),
       get Y n x -> get (List.map (rename_exp ϱ) Y) n y ->
       exp_eval E x = exp_eval E' y.
Proof.
  intros. edestruct map_get_4; eauto; dcr; subst.
  get_functional; subst.
  rewrite <- exp_rename_shift.
  erewrite exp_eval_agree; eauto.
  eapply agree_on_incl; eauto. symmetry. eauto.
  eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
Qed.

Lemma subst_shift L L' (E E':onv val) s (ϱ:var->var)
 : simL L L'
   -> agree_on (freeVars s) E (ϱ ∘ E')
   -> sim (L, E, s)
          (L', E' , subst ϱ s).
Proof.
  general induction s; simpl in * |- *.
  - case_eq (exp_eval E e); intros.
    one_step.
    erewrite exp_subst_agree; eauto.
    rewrite rename_exp_id; eauto.
    eapply agree_on_incl; eauto. symmetry. eauto. cset_tac; intuition.
    eapply IHs; eauto.
    eapply agree_on_sym.
    eapply agree_on_comp_fresh_shift.
    eapply fresh_stable_spec. eapply agree_on_sym. eapply agree_on_incl; eauto.
    cset_tac; intuition.
    eapply simE; try eapply star_refl; simpl; eauto. stuck. stuck.
    erewrite <- exp_subst_agree with (ϱ:=id) in def; eauto.
    rewrite rename_exp_id in def.
    rewrite def in H1. congruence.
    eapply agree_on_incl. eauto. cset_tac; intuition.
  - remember (exp_eval E e); intros. symmetry in Heqo.
    exploit exp_eval_agree; eauto using agree_on_incl, incl_right.
    rewrite exp_rename_shift in X. destruct o.
    + case_eq (val2bool v); intros.
      one_step.
      eapply IHs1; eauto using agree_on_incl, union_incl_left, incl_left.
      one_step.
      eapply IHs2; eauto.
      eapply agree_on_incl; eauto. eapply union_incl_left, incl_right.
    + no_step.
  - destruct (get_dec L (counted l)). destruct s as [[]].
    decide (length block_Z = length Y).
    remember (omap (exp_eval E) Y). symmetry in Heqo.
    pose proof Heqo.
    erewrite omap_agree_2 with (L':=List.map (rename_exp ϱ) Y) in H1;
      eauto using omap_exp_rename_shift_list; try repeat rewrite map_length; eauto.
    destruct o.
    + unfold simL in H.
      edestruct AIR4_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption.
      edestruct AIR4_nth as [?[?]]; try eassumption; dcr.
      simpl in *. repeat get_functional; subst.
      inv H10.
      one_step. rewrite map_length; simpl; congruence.
      simpl. eapply H15; eauto.
      exploit omap_length; eauto. rewrite map_length in X.
      rewrite map_length; congruence.
    + no_step.
    + no_step.
      get_functional; subst. eapply n. simpl in *. congruence.
      edestruct AIR4_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption.
      edestruct AIR4_nth as [?[?]]; try eassumption; dcr.
      simpl in *. repeat get_functional; subst.
      inv H9; simpl in *. eapply n. rewrite map_length in len. congruence.
    + no_step.
      edestruct AIR4_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption. eauto.
      edestruct AIR4_nth_2 as [?[?[? ]]]; try eassumption; dcr; eauto.
  - no_step; simpl.
    rewrite <- exp_rename_shift. erewrite exp_eval_agree; eauto.
    symmetry; eauto.
  - simpl in * |- *.
    eapply simS; try eapply plusO.
    econstructor. econstructor.
    eapply IHs2; eauto. eapply simL_extension; eauto.
    hnf; intros. eapply IHs1; eauto.
    assert (freeVars s1 ⊆ (freeVars s1 \ of_list Z) ∪ of_list Z). {
      cset_tac; intuition. decide (a ∈ of_list Z); intuition.
    }
    eapply agree_on_incl; eauto.
    (* Why is Coq not doing the right instantiations here? *)
    eapply agree_on_sym.
    eapply agree_on_comp_fresh_shift_list;
      repeat rewrite fresh_stable_list_length; eauto;
      eauto using fresh_stable_list_unique, fresh_stable_list_spec.
    eapply agree_on_sym.
    eapply agree_on_incl; eauto. cset_tac; intuition.
    repeat rewrite fresh_stable_list_length in *. congruence.
    eapply agree_on_incl; eauto. cset_tac; intuition.
Qed.


Lemma lookup_set_id {X} `{H : OrderedType X} (s : set X)
: s [=] lookup_set id s.
Proof.
  unfold lookup_set.
  hnf; intros. rewrite map_spec; unfold id; simpl; intuition.
  eexists a; intuition. destruct H0; cset_tac.
Qed.


Lemma fresh_stable_stable G x
  : x ∉ G -> fresh_stable G x = x.
Proof.
  unfold fresh_stable. destruct if; cset_tac; intuition.
Qed.

Lemma fresh_stable_list_stable G Z
  : of_list Z ∩ G [=] ∅ -> unique Z -> fresh_stable_list G Z = Z.
Proof.
  general induction Z; simpl; eauto.
  f_equal.
  + eapply fresh_stable_stable.
    simpl in *; cset_tac; intuition.
    - eapply H; cset_tac; intuition.
    - eapply H1. eapply InA_in in H3. eauto.
  + simpl in *; dcr.
    rewrite fresh_stable_stable.
    eapply IHZ; eauto.
    cset_tac; intuition. eapply (H a0); cset_tac; intuition.
    eapply H1; hnf in H0; subst. eapply InA_in in H3. eauto.
    cset_tac; intuition. eapply (H a); cset_tac; intuition.
    eapply H1; eapply InA_in in H3; eauto.
Qed.

Instance rename_exp_morphism
  : Proper (feq ==> eq ==> eq) rename_exp.
Proof.
  unfold Proper, respectful; intros; subst.
  general induction y0; simpl; eauto.
  - rewrite H; eauto.
  - erewrite IHy0_1, IHy0_2; eauto.
Qed.


Instance subst_morphism
  : Proper (feq ==> eq ==> simeq) subst.
Proof.
  unfold Proper, respectful; intros; subst.
  hnf; intros. eapply subst_fresh. eapply simL_refl.
  hnf; intros. cbv; rewrite H; eauto using option_eq. reflexivity.
Qed.

Lemma subst_id s
  : simeq s (subst id s).
Proof.
  hnf; intros. eapply subst_shift.
  eapply simL_refl.
  reflexivity.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
