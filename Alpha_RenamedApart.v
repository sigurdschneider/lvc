Require Import Util Map Env EnvTy Exp IL AllInRel Bisim Computable Annotation.
Require Import RenamedApart Alpha.
Import F.

Set Implicit Arguments.
Unset Printing Records.

Lemma exp_rename_renamedApart_all_alpha e e' ϱ ϱ'
: alpha_exp ϱ ϱ' e e'
  -> rename_exp ϱ e = e'.
Proof.
  intros. general induction H; simpl; eauto.
Qed.

Ltac pe_rewrite :=
  repeat
    (match goal with
       | [ H : pe ?an _, H' : context [?an] |- _ ] => rewrite H in H'; simpl in H'
       | [ H : pe ?an _ |-  context [?an] ] => rewrite H; simpl
     end).

Definition combine X `{OrderedType X} Y (D:set X) (ϱ ϱ':X->Y) x :=
  if [x ∈ D] then ϱ x else ϱ' x.


Hint Extern 20 ( ?v ∈ singleton ?v ) =>  eapply singleton_iff; reflexivity.
Hint Extern 20 ( ?s ⊆ ?s ∪ _ ) =>  eapply incl_left.
Hint Extern 20 ( ?s ⊆ _ ∪ ?s ) =>  eapply incl_right.
Hint Extern 20 => match goal with
                   | [ H: ?x ∈ ?s, H': ?x ∉ ?s |- _ ] => exfalso; eapply H', H
                 end.


Lemma combine_agree X `{OrderedType X} Y (D:set X) (ϱ ϱ':X->Y)
: agree_on eq D ϱ (combine D ϱ ϱ').
Proof.
  unfold combine; hnf; intros; simpl.
  destruct if; eauto.
Qed.

Lemma combine_agree' X `{OrderedType X} Y (D D':set X) (ϱ ϱ':X->Y)
: disj D D' -> agree_on eq D ϱ' (combine D' ϱ ϱ').
Proof.
  intros. unfold combine; hnf; intros; simpl.
  destruct if; eauto.
Qed.

Lemma rename_exp_agree ϱ ϱ' e
: agree_on eq (Exp.freeVars e) ϱ ϱ'
  -> rename_exp ϱ e = rename_exp ϱ' e.
Proof.
  intros; general induction e; simpl in *; f_equal;
  eauto 30 using agree_on_incl, incl_left, incl_right.
Qed.

Lemma incl_union_right X `{OrderedType X} s t u
: s ⊆ t -> s ⊆ u ++ t.
Proof.
  cset_tac; intuition.
Qed.

Arguments incl_union_right X [H] s t u _ _ _ .

Lemma incl_union_left X `{OrderedType X} s t u
: s ⊆ t -> s ⊆ t ++ u.
Proof.
  cset_tac; intuition.
Qed.

Arguments incl_union_left X [H] s t u _ _ _ .

Lemma incl_add_right X `{OrderedType X} s t x
: s ⊆ t -> s ⊆ {x; t}.
Proof.
  cset_tac; intuition.
Qed.


Lemma in_add_left X `{OrderedType X} s x
: x ∈ {x; s}.
Proof.
  cset_tac; intuition.
Qed.


Create HintDb cset discriminated.

Hint Resolve agree_on_incl incl_union_left incl_union_right incl_add_right in_add_left
             union_left union_right get_list_union_map lookup_list_agree : cset.

Lemma rename_agree ϱ ϱ' s
: agree_on eq (occurVars s) ϱ ϱ'
  -> rename ϱ s = rename ϱ' s.
Proof with eauto 50 using rename_exp_agree, map_ext_get_eq with cset.
  intros. general induction s; simpl in *; f_equal...
Qed.

Global Instance incl_agree_on_morphism_eq X `{OrderedType X} Y R `{Transitive Y R} `{Symmetric Y R}
: Proper (SetInterface.Subset ==> eq ==> eq ==> flip impl) (agree_on R).
Proof.
  unfold Proper, respectful, agree_on, flip, impl; intros; subst.
  rewrite H2 in H6; eauto.
Qed.

Lemma agree_on_union {X} `{OrderedType X} {Y} (f:X->Y) g D D'
  : eagree_on D f g
  -> eagree_on D' f g
  -> eagree_on (D ∪ D') f g.
Proof.
  intros. hnf; intros. cset_tac. destruct H2; eauto.
Qed.

Lemma list_union_cons X `{OrderedType X} s sl
: list_union sl ⊆ list_union (s :: sl).
Proof.
  unfold list_union; simpl.
  setoid_rewrite SetOperations.list_union_start_swap at 2.
  cset_tac; intuition.
Qed.

Lemma lookup_list_unique X `{OrderedType X} Y (Z:list X) (Z':list Y) f
: length Z = length Z'
  -> unique Z
  -> lookup_list (f [Z <-- Z']) Z = Z'.
Proof.
  intros. length_equify. general induction H0; simpl in *; dcr; eauto.
  - f_equal.
    + lud; intuition.
    + erewrite lookup_list_agree; eauto.
      eapply agree_on_update_dead; try reflexivity.
      eapply fresh_of_list; eauto.
Qed.


Lemma rename_renamedApart_all_alpha s t ang ϱ ϱ'
: renamedApart s ang
  -> alpha ϱ ϱ' s t
  -> exists rho, rename rho s = t /\ agree_on eq (fst (getAnn ang)) ϱ rho.
Proof.
  intros. general induction H0; invt renamedApart; pe_rewrite; simpl.
  - eexists ra. erewrite exp_rename_renamedApart_all_alpha; eauto.
  - eexists ra. split; eauto. f_equal. length_equify.
    clear l H1 H6 H4. clear D D'. general induction H; simpl; eauto.
    f_equal.
    + eapply exp_rename_renamedApart_all_alpha; eauto using get.
    + eapply IHlength_eq; eauto using get, list_union_cons.
  - edestruct IHalpha; eauto; dcr; pe_rewrite.
    eexists x0; split.
    + f_equal; eauto.
      * rewrite <- H4. lud; congruence. cset_tac; intuition.
      * eapply exp_rename_renamedApart_all_alpha.
        eapply alpha_exp_agree_on_morph; eauto.
        instantiate (1:=ira). eauto.
        eapply agree_on_incl. symmetry. eapply agree_on_update_inv; eauto.
        rewrite H6. cset_tac; intuition.
    + eapply agree_on_incl. eapply agree_on_update_inv; eauto.
      cset_tac; intuition.
  - edestruct IHalpha1; eauto; dcr; pe_rewrite.
    edestruct IHalpha2; eauto; dcr; pe_rewrite.
    eexists (combine (D ∪ Ds) x x0); simpl; split.
    + f_equal.
      * erewrite rename_exp_agree. eapply exp_rename_renamedApart_all_alpha; eauto.
        eapply agree_on_incl; eauto. symmetry. etransitivity. eapply H3.
        eauto using combine_agree with cset.
      * erewrite rename_agree; eauto.
        rewrite occurVars_freeVars_definedVars.
        rewrite renamedApart_freeVars; eauto.
        rewrite renamedApart_occurVars; eauto.
        pe_rewrite. symmetry. eapply combine_agree.
      * erewrite rename_agree; eauto.
        rewrite occurVars_freeVars_definedVars.
        rewrite renamedApart_freeVars; eauto.
        rewrite renamedApart_occurVars; eauto.
        pe_rewrite. symmetry.
        eapply agree_on_union.
        etransitivity;[| eapply agree_on_incl; [eapply combine_agree| eapply incl_left]].
        etransitivity; eauto. symmetry; eauto.
        eapply combine_agree'.
        eapply renamedApart_disj in H8. pe_rewrite.
        eapply disj_app; split. eapply disj_sym; eauto.
        symmetry. eapply H5.
    + etransitivity;[| eapply agree_on_incl; [eapply combine_agree| eapply incl_left]]; eauto.
  - edestruct IHalpha; eauto; dcr; pe_rewrite.
    eexists x0; split.
    + f_equal; eauto.
      * rewrite <- H5. lud; congruence. cset_tac; intuition.
      *  length_equify.
         clear H2 IHalpha. general induction H; simpl; eauto.
         f_equal.
         erewrite rename_exp_agree.
         eapply exp_rename_renamedApart_all_alpha; eauto using get.
         symmetry. eapply agree_on_incl.
         eapply agree_on_update_inv; eauto.
         rewrite <- get_list_union_map in H8; eauto using get.
         rewrite H8. cset_tac; intuition.
         simpl in *; eapply IHlength_eq; eauto using get, list_union_cons.
         rewrite list_union_cons; eauto.
    + eapply agree_on_incl. eapply agree_on_update_inv; eauto.
      cset_tac; intuition.
  - edestruct IHalpha1; eauto; dcr; pe_rewrite.
    edestruct IHalpha2; eauto; dcr; pe_rewrite.
    eexists (combine (of_list Z ∪ D ∪ Ds) x x0); simpl; split.
    + f_equal.
      * erewrite lookup_list_agree.
        instantiate (1:=ra [Z <-- Z']).
        eapply lookup_list_unique; eauto.
        eapply agree_on_incl. instantiate (1:=of_list Z ∪ D).
        etransitivity. symmetry.
        eapply agree_on_incl. eapply combine_agree. eauto.
        symmetry; eauto. eauto.
      * erewrite rename_agree; eauto.
        rewrite occurVars_freeVars_definedVars.
        rewrite renamedApart_freeVars; eauto.
        rewrite renamedApart_occurVars; eauto.
        pe_rewrite. symmetry. eapply combine_agree.
      * erewrite rename_agree; eauto.
        rewrite occurVars_freeVars_definedVars.
        rewrite renamedApart_freeVars; eauto.
        rewrite renamedApart_occurVars; eauto.
        pe_rewrite. symmetry.
        eapply agree_on_union.
        etransitivity;[| eapply agree_on_incl; [eapply combine_agree| eauto with cset]].
        etransitivity; eauto. symmetry; eauto.
        eapply agree_on_incl. eapply update_with_list_agree_inv; eauto.
        revert H4; clear_all; cset_tac; intuition; eauto.
        eapply combine_agree'.
        eapply renamedApart_disj in H9; pe_rewrite.
        eapply disj_app; split.
        eapply disj_app; split. symmetry. rewrite incl_right. eauto.
        eapply disj_sym; eauto.
        symmetry. rewrite incl_left. eauto.
    + eapply agree_on_incl.
      etransitivity.
      eapply update_with_list_agree_inv; eauto.
      eapply agree_on_incl.
      eapply combine_agree. clear_all; cset_tac; intuition.
      revert H4; clear_all; cset_tac; intuition; eauto.
Qed.

Require Import ILDB.

Lemma exp_alpha_real ϱ ϱ' e e' symb symb'
: alpha_exp ϱ ϱ' e e'
  -> (forall x y, ϱ x = y -> ϱ' y = x -> pos symb x 0 = pos symb' y 0)
  -> exp_idx symb e = exp_idx symb' e'.
Proof.
  intros. general induction H; simpl in * |- *; eauto.
  - erewrite H1; eauto.
  - erewrite IHalpha_exp; intros; eauto.
  - erewrite IHalpha_exp1; eauto with cset.
    erewrite IHalpha_exp2; eauto with cset.
Qed.

Lemma alpha_real ϱ ϱ' s t symb symb'
: alpha ϱ ϱ' s t
  -> (forall x y, ϱ x = y -> ϱ' y = x -> pos symb x 0 = pos symb' y 0)
  -> stmt_idx s symb = stmt_idx t symb'.
Proof.
  intros. general induction H; simpl in * |- *.
  - erewrite exp_alpha_real; eauto.
  - erewrite smap_agree_2; eauto.
    intros; erewrite exp_alpha_real; eauto.
  - erewrite exp_alpha_real; eauto with cset.
    case_eq (exp_idx symb' e'); intros; simpl; eauto.
    erewrite IHalpha; eauto with cset.
    simpl; intros.
    lud; repeat destruct if; try congruence; intuition.
    exploit H1; eauto. eapply pos_inc with (k':=1); eauto.
  - erewrite exp_alpha_real; eauto with cset.
    erewrite IHalpha1; eauto with cset.
    erewrite IHalpha2; eauto with cset.
  - erewrite smap_agree_2; eauto; [| intros; erewrite exp_alpha_real; eauto].
    erewrite IHalpha; eauto.
    simpl; intros.
    lud; repeat destruct if; try congruence; intuition.
    exploit H1; eauto. eapply pos_inc with (k':=1); eauto.
  - erewrite IHalpha1; eauto with cset.
    erewrite IHalpha2; eauto with cset.
    rewrite H. reflexivity.
    intros.
    decide (x ∈ of_list Z).
    + edestruct (of_list_get_first _ i) as [n]; eauto. dcr. hnf in H6. subst x0.
      rewrite pos_app_in; eauto.
      exploit (update_with_list_lookup_in_list_first ra _ H H7 H9); eauto; dcr.
      assert (x0 = y) by congruence. subst x0. clear_dup.
      edestruct (list_lookup_in_list_first _ _ _ (eq_sym H) H4) as [n'];
        eauto using get_in_of_list; dcr.
      hnf in H8; subst x0.
      rewrite pos_app_in; eauto.
      decide (n < n'). exfalso; exploit H12; eauto.
      decide (n' < n). exfalso; exploit H9; eauto. assert (n = n') by omega. subst n'.
      repeat erewrite get_first_pos; eauto.
      eapply get_in_of_list; eauto.
    + exploit (update_with_list_lookup_not_in ra Z Z' y n); eauto.
      assert ((ira [Z' <-- Z]) y ∉ of_list Z). rewrite H4; eauto.
      eapply lookup_set_update_not_in_Z'_not_in_Z in H5; eauto.
      repeat rewrite pos_app_not_in; eauto.
      exploit (update_with_list_lookup_not_in ira Z' Z x H5); eauto.
      rewrite H. eapply pos_inc; eauto.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
