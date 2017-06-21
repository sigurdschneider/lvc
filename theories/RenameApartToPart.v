Require Import Util CSet IL Annotation StableFresh InfinitePartition VarP.
Require Import RenameApart RenamedApartAnn RenameApart_VarP Fresh Range Setoid.


Definition FG_fast : FreshGen nat :=
  @Build_FreshGen nat
                  (fun n _ => (n, S n))
                  (fun n Z => (range n ❬Z❭, n + ❬Z❭))
                  nats_up_to
                  (fun n s => max n (S (fold Init.Nat.max s 0))).

Lemma nats_up_to_in x i
  : x < i <-> x ∈ nats_up_to i.
Proof.
  induction i; simpl.
  - split. omega. cset_tac.
  - decide (x = i); subst.
    + split. cset_tac. omega.
    + split; intros.
      -- cset_tac'. eapply H0. omega.
      -- cset_tac'.
Qed.

Lemma range_nodup i d
  : NoDupA eq (range i d).
Proof.
  general induction d; simpl; eauto using NoDupA.
  econstructor; eauto.
  intro. eapply InA_eq_of_list in H.
  eapply in_range_x in H. omega.
Qed.


Lemma FGS_fast : FreshGenSpec FG_fast.
  econstructor; simpl.
  - intros. rewrite <- nats_up_to_in. omega.
  - reflexivity.
  - intros; hnf; intros.
    eapply nats_up_to_in in H.
    eapply in_range_x in H0 as [? ?]. omega.
  - intros. cset_tac'.
    + rewrite <- nats_up_to_in in *.
      eapply x_notin_range in n. omega.
    + rewrite <- nats_up_to_in in *.
      eapply in_range_x in H0. omega.
    + rewrite <- nats_up_to_in in *. omega.
  - intros. eapply range_nodup.
  - eauto with len.
  - simpl. cset_tac'.
    eapply nats_up_to_in.
    + rewrite <- Max.le_max_r.
      eapply fresh_spec' in H0. omega.
    + eapply nats_up_to_in in H0.
      eapply nats_up_to_in.
      rewrite <- Max.le_max_l. eauto.
Qed.

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
