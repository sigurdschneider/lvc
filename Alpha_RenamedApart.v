Require Import Util Map Env EnvTy Exp IL AllInRel Bisim Computable Annotation.
Require Import Rename RenamedApart Alpha ILDB SetOperations.
Import F.

Set Implicit Arguments.
Unset Printing Records.

(** * Properties of Alpha Equivalence and Renamed Apart Programs *)

(** ** Definition of [combine] *)

Definition combine X `{OrderedType X} Y (D:set X) (ϱ ϱ':X->Y) x :=
  if [x ∈ D] then ϱ x else ϱ' x.

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

(** ** Given an renamedApart program, every alpha-equivalent program
       can be obtained as a renaming according to some [rho] *)

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
         rewrite incl_list_union_cons; eauto.
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

(** ** Alpha Equivalent programs map to identical De-Bruijn terms *)

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
