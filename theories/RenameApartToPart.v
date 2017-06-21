Require Import Util CSet IL Annotation StableFresh InfinitePartition VarP.
Require Import RenameApart RenamedApartAnn RenameApart_VarP.


Definition rename_apart_to_part {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi (s:stmt) :=
  let (xl, fi) := (fresh_list FG fi (to_list (freeVars s))) in
  let s' := (renameApart' FG fi
                       (id [to_list (freeVars s) <-- xl])
                       s) in
  (snd s', renamedApartAnn (snd s') (of_list xl)).

Opaque to_list.

Lemma rename_apart_to_part_renamedApart s
  : RenamedApart.renamedApart (fst (rename_apart_to_part s))
                              (snd (rename_apart_to_part s)).
Proof.
  unfold rename_apart_to_part. simpl.
  eapply renameApart'_renamedApart.
  - rewrite update_with_list_lookup_set_incl; eauto with len.
    rewrite of_list_3; eauto.
  - reflexivity.
Qed.


Lemma rename_apart_to_part_occurVars s
  : fst (getAnn (snd (rename_apart_to_part s)))
        ∪ snd (getAnn (snd (rename_apart_to_part s)))
        [=] occurVars (fst (rename_apart_to_part s)).
Proof.
  unfold rename_apart_to_part; simpl.
  rewrite occurVars_freeVars_definedVars.
  rewrite snd_renamedApartAnn.
  eapply eq_union_lr; eauto.
  rewrite fst_renamedApartAnn.
  rewrite freeVars_renamedApart'.
  - rewrite update_with_list_lookup_list_eq; eauto with len.
    + eapply nodup_to_list_eq.
    + rewrite of_list_3; eauto.
  - rewrite update_with_list_lookup_list_eq; eauto with len.
    + eapply nodup_to_list_eq.
    + rewrite of_list_3; eauto.
Qed.

Lemma rename_to_subset_even (s:stmt)
  : For_all (inf_subset_P even_inf_subset)
            (occurVars (fst (rename_apart_to_part s))).
Proof.
  eapply var_P_occurVars.
  eapply renameApart_var_P.
  - intros. eapply least_fresh_P_full_spec.
  - intros.
    edestruct update_with_list_lookup_in_list; dcr.
    Focus 3. rewrite H3. hnf in H5. subst.
    exploit fresh_list_stable_get; eauto; dcr; subst.
    eapply least_fresh_P_full_spec.
    eauto with len. rewrite of_list_3; eauto.
Qed.
