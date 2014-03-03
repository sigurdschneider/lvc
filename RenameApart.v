Require Import CSet Le.

Require Import Plus Util Map.
Require Import Env EnvTy IL Liveness Coherence Alpha ParamsMatch Fresh.
 
Set Implicit Arguments.

(** We first define [rename_apart' ϱ G s], a function that chooses
    a variable fresh for G at every binder, records the choice in ϱ,
    and renames all variables according to ϱ *)

Fixpoint rename_apart' (ϱ:env var) (G:set var) (s:stmt) : set var * stmt:=
match s with
   | stmtExp x e s0 => 
     let y := fresh G in
     let ϱ' := ϱ[x <- y] in 
     let (G', s') := rename_apart' ϱ' (G ∪ {{y}}) s0 in
       (G', stmtExp y (rename_exp ϱ e) s')
   | stmtIf x s1 s2 => 
     let (G', s1') := rename_apart' ϱ G s1 in
     let (G'', s2') := rename_apart' ϱ G' s2 in
      (G'', stmtIf (ϱ x) s1' s2')
   | stmtGoto l Y => (G, stmtGoto l (lookup_list ϱ Y))
   | stmtReturn x => (G, stmtReturn (ϱ x))
   | stmtLet Z s1 s2 => 
     let Y := fresh_list G (length Z) in
     let ϱZ := ϱ [ Z <-- Y ] in
     let (G', s1') := rename_apart' ϱZ (G ∪ of_list Y) s1 in
     let (G'', s2') := rename_apart' ϱ G' s2 in
     (G'', stmtLet Y s1'  s2')
   end.

Fixpoint rename_apart_rho (ϱ:env var) (s:stmt) : env var :=
match s with
   | stmtExp x e s0 => 
     let y := fresh (freeVars s0 \ {{x}}) in
     let ϱ' := ϱ[y <- x] in rename_apart_rho ϱ' s0
   | stmtIf x s1 s2 => 
     let ϱ' := rename_apart_rho ϱ s1 in rename_apart_rho ϱ' s2
   | stmtGoto l Y => ϱ
   | stmtReturn x => ϱ
   | stmtLet Z s1 s2 => 
     let Y := fresh_list (freeVars s1) (length Z) in
     let ϱZ := ϱ [ Z <-- Y ]  in
     let ϱ' := rename_apart_rho ϱZ s1 in rename_apart_rho ϱ' s2 
   end.


Lemma rename_apart_incl ϱ G G' s
  : G ⊆ G' -> G ⊆ fst (rename_apart' ϱ G' s).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl; subst; eauto. 
  eapply IHs. cset_tac. left; eauto.
  eapply IHs2. eapply IHs1. cset_tac. left; eauto.
Qed.

Lemma rename_apart_incl_eq ϱ G G' s G''
  : G ⊆ G' -> G'' = fst (rename_apart' ϱ G' s) -> G ⊆ G''.
Proof.
  intros; subst; eauto using rename_apart_incl.  
Qed.

Lemma rename_apart_notOccur G G' ϱ s
  : G ⊆ G'
  -> lookup_set ϱ (freeVars s) ⊆ G'
  -> notOccur (G \ lookup_set ϱ (freeVars s)) (snd (rename_apart' ϱ G' s)).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl; eauto using notOccur; subst; eauto.

  + econstructor; simpl in *. 
    - intro. eapply fresh_spec. eapply H, minus_incl; eauto.
    - eapply notOccur_incl. Focus 2. eapply IHs. eapply Subset_refl.
      hnf; intros. eapply lookup_set_spec in H1. destruct H1; dcr.
      lud. cset_tac; eauto. eapply union_2. eapply H0. eapply lookup_set_spec. intuition.
      eexists x0; cset_tac; intuition. intuition.
      hnf; intros. cset_tac. left; eauto. intro.
      eapply H3. eapply lookup_set_spec. intuition.
      eapply lookup_set_spec in H1. destruct H1; dcr; eauto. lud.
      rewrite H5 in H2. exfalso. eapply fresh_spec; eauto.
      exists x0. cset_tac; intuition. intuition.
    - eapply notOccur_freeVars. 
      cset_tac; intuition. eapply rename_exp_freeVars in H3.
      eapply H4. eapply lookup_set_incl; eauto; intuition. intuition.

  + econstructor. intro. eapply minus_in_in in H1. eapply H1. eapply lookup_set_spec. intuition.
    eexists x. split; eauto. eapply incl_union. cset_tac. reflexivity.
    eapply notOccur_incl,IHs1.
    eapply incl_minus_lr; eauto. eapply lookup_set_incl. intuition. rewrite union_comm.
    rewrite (union_comm _ (freeVars s1)). rewrite <- union_assoc. now eapply incl_union; eauto.
    now apply Subset_refl.
    simpl in *; eauto. rewrite <- H0. eapply lookup_set_incl. intuition.
    cset_tac; intuition.
    eapply notOccur_incl, IHs2. 
    eapply incl_minus_lr; eauto. eapply lookup_set_incl. intuition. rewrite union_comm.
    rewrite <- union_assoc. now eapply incl_union.
    eapply rename_apart_incl. eapply Subset_refl.
    simpl in *. eapply Subset_trans. Focus 2. eapply rename_apart_incl. reflexivity.
    eapply Subset_trans; eauto. eapply lookup_set_incl. intuition. 
    cset_tac; intuition. 
  + econstructor. rewrite of_list_lookup_list. eapply meet_minus. intuition.
  + econstructor. intro. eapply minus_in_in in H1. decompose records.
    eapply H3. eapply lookup_set_spec. intuition. eexists x; firstorder.

  + econstructor.
    - cset_tac; intuition. rewrite H in H1. 
      eapply (not_in_empty a). rewrite <- (fresh_set_spec G' (length Z)). 
      cset_tac; eauto.
    - eapply notOccur_incl. Focus 2. eapply IHs1. reflexivity.
      rewrite lookup_set_update_with_list_in_union_length. 
      eapply incl_union_lr. simpl in *. eapply Subset_trans;try eassumption.
      eapply lookup_set_incl. intuition.  cset_tac; eauto. reflexivity. intuition.
      rewrite fresh_list_length; eauto.
      
      hnf; intros. cset_tac. left; eauto. intro.
      eapply lookup_set_spec in H1.
      destruct H1; dcr. destruct_prop(x ∈ of_list Z).
      eapply (update_with_list_lookup_in ϱ) with (Z':=fresh_list G' (length Z)) in i; eauto.
      rewrite <- H5 in i. apply (not_in_empty a).
      eapply fresh_set_spec. cset_tac; eauto.
      rewrite fresh_list_length; eauto.
      eapply H3. eapply lookup_set_spec. intuition. 
      rewrite update_with_list_no_update in H5; eauto. eexists x.
      split; eauto. cset_tac; eauto.
      eapply update_with_list_proper.
    - eapply notOccur_incl. Focus 2. eapply IHs2. reflexivity.
      eapply Subset_trans. Focus 2. eapply rename_apart_incl. reflexivity.
      eapply Subset_trans. Focus 2. eapply union_subset_1. 
      simpl in H0. rewrite <- H0. eapply lookup_set_incl. intuition. cset_tac.
      intuition.
      simpl in *. eapply Subset_trans. Focus 2. rewrite <- rename_apart_incl.
      Focus 2. reflexivity. reflexivity.
      eapply incl_minus_lr. cset_tac; intuition.
      eapply lookup_set_incl; cset_tac; intuition.
Qed.
 
Opaque to_list.

Lemma rename_apart_parameters_match {B} `{BlockType B} (L:list B) ϱ s G 
  : labenv_parameters_match L
 -> parameters_match (labenvZ L) s
 -> parameters_match (labenvZ L) (snd (rename_apart' ϱ G s)).
Proof.
  intros. general induction s; simpl; inv H1; eauto using parameters_match;
          repeat let_pair_case_eq; repeat simpl_pair_eqs.
  + subst. econstructor. eapply IHs; eauto.
  + subst. econstructor; eauto.  
  + econstructor; eauto. 
    rewrite lookup_list_length; congruence.
        
  + subst; simpl. 
    destruct (block_ctor s1 Z); dcr; subst.
    assert (labenv_parameters_match (x :: L)).
    hnf; intros. inv H2; simpl; eauto.
    constructor; repeat rewrite fresh_list_length.
    eapply (IHs1 _ _ _ _ _ H2); eauto.
    eapply (IHs2 _ _ _ _ _ H2); eauto. 
Qed.


Lemma rename_apart_ssa' (s:stmt) ϱ G
  : lookup_set ϱ (freeVars s) ⊆ G
  -> ssa G (snd (rename_apart' ϱ G s)) (fst (rename_apart' ϱ G s)).
Proof.
  general induction s; simpl; repeat let_pair_case_eq.
  + subst. econstructor. eapply fresh_spec. simpl in H. 
    rewrite rename_exp_freeVars. eapply Subset_trans; eauto.
    eapply lookup_set_incl. intuition. eapply union_subset_2. intuition.
    eapply IHs. simpl in *. hnf; intros. eapply lookup_set_spec in H0; decompose records.
    lud. rewrite H3. cset_tac. right; eauto. 
    rewrite union_comm. eapply incl_union. rewrite H3. eapply H.
    eapply lookup_set_spec. intuition. eexists x0. split; eauto.
    eapply union_2. eapply in_in_minus; eauto. cset_tac. intuition.

  + subst s0 s4. simpl in H. simpl. rename s3 into Gs2. rename s into Gs1.
    eapply ssaIf with (Ds := Gs1) (Dt := (Gs2 \ (Gs1 \ G))). 
    - eapply H. simpl. eapply lookup_set_spec. intuition. eexists x.
    split; eauto. rewrite union_comm. cset_tac. left; eauto.
    - eapply minus_incl_meet_special. subst; eapply rename_apart_incl. reflexivity.
      subst. eapply rename_apart_incl; reflexivity.
    - eapply minus_incl_special. subst. eapply rename_apart_incl. reflexivity.
    - subst. eapply IHs1. eapply Subset_trans; eauto. eapply lookup_set_incl. intuition.
      eapply Subset_trans; [| eapply union_subset_1]. eapply union_subset_1.
    - assert (G [=] (G \ (Gs1 \ G))). eapply minus_minus_eq.
    rewrite H0 at 1. assert (Gs2 \ (Gs1 \ G) [=] (Gs2 \ (Gs1 \ G)) \ (Gs1 \ G)).
    eapply minus_idem. rewrite H3.
    eapply ssa_minus. 
    eapply notOccur_incl; try eapply rename_apart_notOccur with (G:=Gs1 \ G).
    eapply Subset_trans. rewrite minus_idem. reflexivity. eapply incl_minus_lr.
    reflexivity. eapply Subset_trans; eauto. eapply lookup_set_incl. intuition.
    eapply Subset_trans; [| eapply union_subset_1]. eapply union_subset_2.
    eapply incl_minus.
    subst. eapply Subset_trans. Focus 2. eapply rename_apart_incl. reflexivity.
    rewrite <- H. eapply lookup_set_incl. intuition. cset_tac; eauto.
    assert (G [=] Gs1 \ (Gs1 \ G)). eapply minus_minus_id. subst. eapply rename_apart_incl. reflexivity.
    rewrite H4 at 1. eapply ssa_minus. 
    eapply notOccur_incl; try eapply rename_apart_notOccur with (G:=Gs1 \ G). subst. 
    eapply Subset_trans. rewrite minus_idem. reflexivity. eapply incl_minus_lr.
    reflexivity. eapply Subset_trans; eauto. eapply lookup_set_incl. intuition.
    eapply Subset_trans; [| eapply union_subset_1]. eapply union_subset_2.
    eapply incl_minus.
    subst. eapply Subset_trans. Focus 2. eapply rename_apart_incl. reflexivity.
    rewrite <- H. eapply lookup_set_incl. intuition. cset_tac; eauto.
    subst. eapply IHs2. eapply Subset_trans; eauto using rename_apart_incl.
    eapply lookup_set_incl. intuition. 
    eapply Subset_trans; [| eapply union_subset_1]. eapply union_subset_2.
  
  + econstructor. simpl in H. rewrite of_list_lookup_list; eauto. intuition. reflexivity.
  + econstructor. simpl in H. eapply H. eapply lookup_set_spec. intuition.
    eexists x; cset_tac; firstorder. reflexivity.
  
  + simpl. subst s0 s4. simpl in H. simpl. rename s3 into Gs2. rename s into Gs1.
    eapply ssaLet with (Ds:=Gs1) (Dt:=Gs2 \ (Gs1 \ G)).
    - eapply fresh_set_spec.
    - eapply  minus_incl_meet_special; eauto using rename_apart_incl_eq, incl_refl.
      subst. eapply rename_apart_incl. rewrite union_comm. eapply incl_union.
      subst. eapply rename_apart_incl. eapply Subset_refl.
    - eapply minus_incl_special. subst. eapply rename_apart_incl. reflexivity.
    - subst. rewrite union_comm. eapply IHs1. 
      rewrite lookup_set_update_with_list_in_union_length.
      eapply incl_union_lr; eauto. rewrite <- H.
      eapply lookup_set_incl; eauto. intuition.
      cset_tac; auto. reflexivity. intuition.
      rewrite fresh_list_length; eauto.
    - assert (G [=] (Gs1 \ (Gs1 \ G))). eapply minus_minus_id. subst. eapply rename_apart_incl.
      eapply union_subset_1.
      rewrite H0 at 1. eapply ssa_minus. 
      eapply notOccur_incl; try eapply rename_apart_notOccur with (G:=Gs1 \ G).
      eapply Subset_trans. rewrite minus_idem. reflexivity. eapply incl_minus_lr.
      reflexivity. eapply Subset_trans; eauto. eapply lookup_set_incl. intuition.
      eapply Subset_trans; [| eapply union_subset_2]. reflexivity.
      eapply incl_minus.
      subst. eapply Subset_trans. Focus 2. eapply rename_apart_incl. reflexivity.
      eapply Subset_trans;[|eapply union_subset_1].
      rewrite <- H. eapply lookup_set_incl. intuition. cset_tac; eauto.
      subst. eapply IHs2. eapply rename_apart_incl. 
      eapply Subset_trans; [| eapply union_subset_1]. eapply Subset_trans; eauto.
      eapply lookup_set_incl. intuition. eapply union_subset_2.
Qed.

Lemma rename_apart_alpha' G ϱ ϱ' s
  : lookup_set ϱ (freeVars s) ⊆ G
  -> inverse_on (freeVars s) ϱ ϱ'
  -> alpha ϱ' ϱ (snd (rename_apart' ϱ G s)) s.
Proof.
  general induction s; simpl; repeat let_pair_case_eq; subst; simpl in * |- *; eauto using alpha.
  
  + econstructor. eapply alpha_exp_sym. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl; eauto. cset_tac; eauto. 
    eapply IHs.
    - rewrite lookup_set_update_in_union.
      eapply incl_union_lr; try reflexivity. rewrite <- H.
      eapply lookup_set_incl. intuition. cset_tac; eauto. intuition.
    - eapply inverse_on_update_inverse. intuition. 
      eapply inverse_on_incl; eauto. cset_tac; eauto.
      assert (lookup_set ϱ (freeVars s \ {{x}}) ⊆ 
                         lookup_set ϱ (freeVars s \ {{x}} ∪ Exp.freeVars e)).
      eapply lookup_set_incl. intuition. cset_tac; eauto.
      intro. eapply H1 in H2. eapply H in H2.
      eapply fresh_spec in H2. eauto.
  + econstructor; eauto. 
    - rewrite <- H0; eauto. cset_tac; intuition.
    - eapply IHs1.
      * eapply Subset_trans; eauto. eapply lookup_set_incl; [intuition|].
        rewrite union_assoc, union_comm. eapply incl_union.
      * eapply inverse_on_incl; eauto. rewrite union_assoc, union_comm. eapply incl_union.
    - eapply IHs2; eauto.
      * eapply Subset_trans; eauto using rename_apart_incl. eapply lookup_set_incl; [intuition|].
        rewrite union_comm at 1. rewrite <- union_assoc. eapply incl_union.
      * eapply inverse_on_incl; eauto. 
        rewrite union_comm at 1. rewrite <- union_assoc. eapply incl_union.
  + econstructor. eapply list_eq_eq. pose proof (inverse_on_lookup_list Y H0).
    eapply H1. eapply Subset_refl. reflexivity.

  + econstructor; eauto. rewrite <- H0. reflexivity. cset_tac; eauto.
 
  + econstructor. eapply fresh_list_length.
    - eapply IHs1.
      * rewrite lookup_set_update_with_list_in_union_length.
        eapply incl_union_lr. rewrite <- H.
        eapply lookup_set_incl; intuition. reflexivity.
        intuition. rewrite fresh_list_length; eauto.
      * eapply inverse_on_update_fresh.
        eapply inverse_on_incl; eauto; cset_tac; eauto.
        eapply fresh_list_unique.
        rewrite fresh_list_length; eauto.
        hnf; intros. intro. eapply lookup_set_spec in H2.
        destruct H2; dcr; cset_tac. 
        pose proof (fresh_list_spec G (length Z)).
        assert (x ∈ G). rewrite <- H.
        eapply lookup_set_spec. intuition.
        eexists x0. cset_tac; intuition. 
        eapply (not_in_empty x). 
        eapply fresh_list_spec. cset_tac; eauto. intuition.
    - eapply IHs2.
      * eapply rename_apart_incl. eapply Subset_trans; [| eapply  union_subset_1].
        eapply Subset_trans; eauto. eapply lookup_set_incl;[intuition| eapply incl_union].
      * eapply inverse_on_incl; eauto. eapply incl_union.
Qed.

(** Based on [rename_apart'], we can define a function that renames apart bound variables apart
    and keeps free variables the same *)
Definition rename_apart s := snd (rename_apart' id (freeVars s) s).

Lemma rename_apart_ssa (s:stmt)
  : ssa (freeVars s) (rename_apart s) (fst (rename_apart' id (freeVars s) s)).
Proof.
  eapply rename_apart_ssa'. eapply lookup_set_on_id. eapply Subset_refl.
Qed.

Lemma rename_apart_alpha s
  : alpha id id (rename_apart s) s.
Proof. 
  eapply rename_apart_alpha'.
  + eapply lookup_set_on_id; reflexivity.
  + eapply inverse_on_id.
Qed.

Lemma rename_apart_params_match s
  : params_match nil s -> params_match nil (rename_apart s).
Proof.
  intros. split.
  + eapply rename_apart_parameters_match; isabsurd. eapply H.
  + eapply H.
Qed.

(*
Lemma rename_apart_2 G ϱ ϱ' s s' f g
:  alpha ϱ ϱ' s s'
  -> agree_on (freeVars s') (ϱ' ∘ f) g
  -> rename_apart f G s = rename_apart g G s'. 
Proof.
  intros. general induction H; 
  simpl. f_equal. f_equal. rewrite <- H0. eapply H1. 

  rewrite (IHalpha _ _ (g [y <- fresh G])).

  simpl in H1. eapply agree_on_trans. 
  eapply lookup_set_agree_on_comp. intuition.
  eapply alpha_sym in H0.
  eapply alpha_inverse_on in H0. eapply inverse_on_injective_on in H0.
  intro. eapply lookup_set_spec in H2. destruct H2; dcr.
  specialize (H0 x0 y). 
*)



(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lyn")) ***
*** End: ***
*)
