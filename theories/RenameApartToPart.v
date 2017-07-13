Require Import Util CSet IL Annotation StableFresh InfinitePartition VarP.
Require Import RenameApart RenamedApartAnn RenameApart_VarP Range Setoid.
Require Import FreshGenInst FreshGen.

Set Implicit Arguments.

Definition rename_apart_to_part {Fi} (FG:FreshGen var Fi) (FGS:FreshGenSpec FG) (s:stmt) :=
  let xlfi := (fresh_list FG (empty_domain FG) (to_list (freeVars s))) in
  let s' := (renameApart FG (snd xlfi)
                       (id [to_list (freeVars s) <-- fst xlfi])
                       s) in
  (snd s', xlfi).


Definition rename_apart_to_part_ra {Fi} (FG:FreshGen var Fi) (FGS:FreshGenSpec FG) (s:stmt) :=
   let xlfi := (fresh_list FG (empty_domain FG) (to_list (freeVars s))) in
   let s' := (renameApart FG (snd xlfi)
                         (id [to_list (freeVars s) <-- fst xlfi])
                         s) in
   renamedApartAnn (snd s') (of_list (fst xlfi)).

Opaque to_list.

Lemma rename_apart_to_part_renamedApart {Fi} (FG:FreshGen var Fi) (FGS:FreshGenSpec FG) s
  : RenamedApart.renamedApart (fst (rename_apart_to_part FGS s))
                              (rename_apart_to_part_ra FGS s).
Proof.
  unfold rename_apart_to_part. simpl.
  eapply renameApart'_renamedApart; eauto.
  - rewrite update_with_list_lookup_set_incl; eauto with len.
    rewrite fresh_list_len; eauto.
    rewrite of_list_3; eauto.
  - rewrite <- fresh_list_domain_spec; eauto with cset.
Qed.


Lemma rename_apart_to_part_occurVars {Fi} (FG:FreshGen var Fi) (FGS:FreshGenSpec FG) s
  : fst (getAnn (rename_apart_to_part_ra FGS s))
        ∪ snd (getAnn (rename_apart_to_part_ra FGS s))
        [=] occurVars (fst (rename_apart_to_part FGS s)).
Proof.
  unfold rename_apart_to_part, rename_apart_to_part_ra; simpl.
  rewrite occurVars_freeVars_definedVars.
  rewrite snd_renamedApartAnn.
  eapply eq_union_lr; eauto.
  rewrite fst_renamedApartAnn.
  rewrite freeVars_renamedApart'; eauto.
  - rewrite update_with_list_lookup_list_eq; eauto with len.
    + rewrite fresh_list_len; eauto.
    + eapply nodup_to_list_eq.
    + rewrite of_list_3; eauto.
  - rewrite update_with_list_lookup_list_eq; eauto with len.
    + rewrite <- fresh_list_domain_spec; eauto.
    + rewrite fresh_list_len; eauto.
    + eapply nodup_to_list_eq.
    + rewrite of_list_3; eauto.
Qed.

Lemma FG_even_fast_inf_subset fi (x:var)
  :  even_inf_subset_pos (fst (FG_even_fast_pos fi x)).
Proof.
  hnf. simpl. destruct fi; simpl. cases; eauto.
Qed.

Local Arguments succ : simpl never.

Lemma even_fast_list_even fi
  :  forall Z (x:var), x \In of_list (fst (fresh_list FG_even_fast_pos fi Z)) ->
            even_inf_subset_pos x.
Proof.
  intros.
  destruct fi.
  eapply of_list_get_first in H; dcr. invc H1.
  simpl in *.
  inv_get.
  rewrite asNat_iter_plus_plus.
  eapply even_add; eauto. eapply even_mult2.
Qed.

Lemma even_fast_update_even E fi (s:set var) t
      (Len:❬to_list s❭ = ❬t❭)
  : forall x : var,
    x \In s ->
    even_inf_subset_pos ((E [to_list s <-- fst (fresh_list FG_even_fast_pos fi t)]) x).
Proof.
  intros.
  rewrite <- of_list_3 in H.
  eapply (update_with_list_lookup_in_list E _ (fst (fresh_list FG_even_fast_pos fi t))) in H; dcr.
    + rewrite H2.
      eapply even_fast_list_even.
      eapply get_in_of_list; eauto.
    + rewrite fresh_list_len; eauto using FGS_even_fast_pos.
Qed.

Lemma rename_to_subset_even s
  : For_all (inf_subset_P even_inf_subset_pos)
            (occurVars (fst (rename_apart_to_part FGS_even_fast_pos s))).
Proof.
  eapply var_P_occurVars.
  eapply renameApart_var_P; eauto using FGS_even_fast_pos.
  - intros. eapply FG_even_fast_inf_subset.
  - intros.
    eapply even_fast_list_even; eauto.
  - intros.
    eapply even_fast_update_even; eauto.
Qed.
