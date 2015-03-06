Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation SetOperations MoreList.
Require Import Liveness Restrict RenamedApart LabelsDefined.

Set Implicit Arguments.



Lemma renamedApart_live_functional s ang DL
: renamedApart s ang
  -> paramsMatch s (List.map (snd ∘ @length _) DL)
  -> live_sound Functional DL s (mapAnn fst ang).
Proof.
  intros. general induction H; invt paramsMatch; simpl.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
    rewrite getAnn_mapAnn, H2. simpl; cset_tac; intuition.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
    rewrite getAnn_mapAnn, H4. simpl; cset_tac; intuition.
    rewrite getAnn_mapAnn, H5. simpl; cset_tac; intuition.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
  - inv_map H4. destruct x; unfold comp in H5; simpl in *.
    econstructor; simpl; eauto.
    + intros. eapply live_exp_sound_incl, live_freeVars.
      rewrite <- H. eapply get_list_union_map; eauto.
  - econstructor; eauto.
    intros. eapply live_exp_sound_incl, live_freeVars.
    rewrite <- H0. eapply get_list_union_map; eauto.
    rewrite getAnn_mapAnn, H2. simpl; cset_tac; intuition.
  - econstructor; eauto.
    + rewrite getAnn_mapAnn, H3; simpl. cset_tac; intuition.
    + destruct if; eauto. rewrite getAnn_mapAnn, H3; simpl. cset_tac; intuition.
    + rewrite getAnn_mapAnn, H5; simpl. reflexivity.
Qed.

Lemma renamedApart_live s ang DL i
: renamedApart s ang
  -> paramsMatch s (List.map (snd ∘ @length _) DL)
  -> bounded (List.map (fun x => Some (fst x \ of_list (snd x))) DL) (fst (getAnn ang))
  -> live_sound i DL s (mapAnn fst ang).
Proof.
  intros. general induction H; invt paramsMatch; simpl.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
    eapply IHrenamedApart; eauto.
    rewrite H2; simpl. rewrite <- incl_add'; eauto.
    rewrite getAnn_mapAnn, H2. simpl; cset_tac; intuition.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
    + eapply IHrenamedApart1; eauto.
      rewrite H4; simpl; eauto.
    + eapply IHrenamedApart2; eauto.
      rewrite H5; simpl; eauto.
    + rewrite getAnn_mapAnn, H4. simpl; cset_tac; intuition.
    + rewrite getAnn_mapAnn, H5. simpl; cset_tac; intuition.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
  - inv_map H5. destruct x; unfold comp in *; simpl in *.
    econstructor; simpl; eauto.
    + destruct if; eauto.
      eapply map_get_1 with (f:=fun x : set var * params => ⎣fst x \ of_list (snd x) ⎦) in H3.
      eapply bounded_get; eauto.
    + intros. eapply live_exp_sound_incl, live_freeVars.
      rewrite <- H. eapply get_list_union_map; eauto.
  - econstructor; eauto using live_exp_sound_incl, live_freeVars.
    eapply IHrenamedApart; eauto.
    rewrite H2; simpl. rewrite <- incl_add'; eauto.
    intros. eapply live_exp_sound_incl, live_freeVars.
    rewrite <- H0. eapply get_list_union_map; eauto.
    rewrite getAnn_mapAnn, H2. simpl; cset_tac; intuition.
  - econstructor; eauto.
    + eapply IHrenamedApart1; eauto; simpl.
      rewrite getAnn_mapAnn, H3; simpl in *.
      split. cset_tac; intuition. rewrite <- incl_right; eauto.
    + eapply IHrenamedApart2; eauto; simpl.
      rewrite getAnn_mapAnn, H3, H5; simpl in *.
      split. cset_tac; intuition. eauto.
    + rewrite getAnn_mapAnn, H3; simpl. cset_tac; intuition.
    + destruct if; eauto. rewrite getAnn_mapAnn, H3; simpl. cset_tac; intuition.
    + rewrite getAnn_mapAnn, H5; simpl. reflexivity.
Qed.


(*Fixpoint list_disjoint (DL:list (set var)) (G:set var) :=
  match DL with
    | nil => True
    | G'::DL => disj G' G /\ list_disjoint DL G
  end.*)

Definition disjoint (DL:list (set var)) (G:set var) :=
  forall n s, get DL n s -> disj s G.

Instance olist_disjoint_morphism_subset
  : Proper (eq ==> Subset ==> flip impl) disjoint.
Proof.
  unfold Proper, respectful, impl, flip, disj, disjoint; intros; subst.
  rewrite H0; eauto.
Qed.

Instance olist_disjoint_morphism
  : Proper (eq ==> Equal ==> iff) disjoint.
Proof.
  unfold Proper, respectful, iff, disjoint; split; intros; subst.
  - rewrite <- H0; eauto.
  - rewrite H0; eauto.
Qed.

Lemma renamedApart_globals_live s AL alv f ang
: live_sound Imperative AL s alv
  -> renamedApart s ang
  -> isCalled s f
  -> disjoint (List.map fst AL) (snd (getAnn ang))
  -> exists lvZ, get AL (counted f) lvZ /\ (fst lvZ \ of_list (snd lvZ)) \ snd (getAnn ang) ⊆ getAnn alv.
Proof.
  intros LS RA IC.
  general induction IC; invt live_sound; invt renamedApart; simpl in * |- *; eauto.
  - edestruct IHIC; dcr; eauto.
    + rewrite H10; simpl. rewrite incl_add'. rewrite <- H11. eauto.
    + eexists; split; eauto. rewrite H11 in *.
      exploit H. eapply map_get_1; eauto.
      assert (x ∉ fst x0). intro.
      eapply in_disj_absurd in X; eauto. cset_tac; intuition.
      rewrite <- H7. admit.
  - edestruct IHIC; eauto.
    + rewrite H14; simpl. rewrite incl_left. rewrite H10. eauto.
    + dcr. eexists; split; eauto.
      rewrite H14 in H2. simpl in *. rewrite <- H10.
      rewrite <- minus_union. rewrite H2.
      cset_tac; intuition.
  - edestruct IHIC; eauto.
    + rewrite H15; simpl. rewrite incl_right. rewrite H10. eauto.
    + dcr. eexists; split; eauto.
      rewrite H15 in H2. simpl in *. rewrite <- H10.
      rewrite union_comm. rewrite <- minus_union. rewrite H2.
      cset_tac; intuition.
  - eexists; split; eauto. simpl.
    rewrite H3; eapply minus_incl.
  - edestruct IHIC; dcr; eauto.
    + rewrite H11; simpl. rewrite incl_add'. rewrite <- H12. eauto.
    + eexists; split; eauto. rewrite H12 in *.
      exploit H. eapply map_get_1; eauto.
      assert (x ∉ fst x0). intro.
      eapply in_disj_absurd in X; eauto. cset_tac; intuition.
      rewrite <- H8. rewrite H11 in H2. simpl in *.
      admit.
  - edestruct IHIC1; eauto.
    simpl. rewrite H12; simpl.
    admit.
    admit.
  - edestruct IHIC; eauto.
    + rewrite H15; simpl. hnf; intros. inv H0.
      *
Qed.


Lemma renamedApart_live_imperative_is_functional s ang DL alv
: renamedApart s ang
  -> noUnreachableCode s
  -> live_sound Imperative DL s alv
  -> live_sound FunctionalAndImperative DL s alv.
Proof.
  intros. general induction H; invt noUnreachableCode; invt live_sound; eauto using live_sound.
  - econstructor; simpl; eauto.


Qed.



(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
