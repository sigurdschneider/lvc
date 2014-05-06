Require Import Util List OptionMap LengthEq Map Get.

Notation "B[ x ]" := (if [ x ] then true else false).

Fixpoint filter_by {A B} (f:A -> bool) (L:list A) (L':list B) : list B :=
  match L, L' with
    | x :: L, y::L' => if f x then y :: filter_by f L L' else filter_by f L L' 
    | _, _ => nil
  end.

Arguments filter_by [A B] f L L'.


Lemma lookup_list_filter_by_commute A B C (V:A->B) (Z:list C) Y p
: length Z = length Y 
  -> lookup_list V (filter_by p Z Y) =
    filter_by p Z (lookup_list V Y).
Proof.
  intros. eapply length_length_eq in H. 
  general induction H; simpl; eauto.
  + destruct if; simpl; rewrite IHlength_eq; eauto.
Qed.

Lemma filter_incl X `{OrderedType X} lv Y
  : of_list (List.filter (fun y : X => B[y ∈ lv]) Y) ⊆ lv.
Proof.
  general induction Y; simpl. 
  - cset_tac; intuition.
  - decide (a ∈ lv); simpl. cset_tac; intuition. rewrite <- H1; eauto.
    rewrite <- IHY; eauto.
    eauto.
Qed.


Lemma omap_filter_by A B C f p (Y:list A) (l:list B) (Z:list C)
: omap f Y = Some l
  -> length Y = length Z
  -> omap f (filter_by p Z Y) = Some (filter_by p Z l).
Proof.
  intros. eapply length_length_eq in H0. 
  general induction H0; simpl in * |- *; eauto.
  monad_inv H. destruct if; simpl; eauto.
  - rewrite EQ. erewrite IHlength_eq; simpl; eauto.
Qed.

Lemma filter_filter_by_length {X} {Y} (Z:list X) (VL:list Y) 
: length Z = length VL
  -> forall p, length (List.filter p Z) =
    length (filter_by p Z VL).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl; eauto.
  destruct if; simpl. rewrite IHlength_eq; eauto. eauto.
Qed.


Lemma filter_incl2 X `{OrderedType X} (p:X->bool) Z
: of_list (List.filter p Z) ⊆ of_list Z.
Proof.
  general induction Z; simpl.
  - reflexivity.
  - destruct if; simpl. rewrite IHZ; reflexivity.
    rewrite IHZ. cset_tac; intuition.
Qed.

Lemma filter_by_get A B p (Z:list A) (Y:list B) y n
: get (filter_by p Z Y) n y 
  -> length Z = length Y
  -> { n : nat & { z : A | get Y n y /\ get Z n z /\ p z } }.
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; simpl in * |- *; isabsurd.
  destruct if in H. eapply get_getT in H.
  inv H.
  do 2 eexists; repeat split; eauto using get.
  rewrite <- Heq; eauto. eapply I.
  eapply getT_get in X. 
  edestruct IHlength_eq as [? [? [? []]]]; eauto; dcr.
  do 2 eexists; eauto using get.
  edestruct IHlength_eq as [? [? [? []]]]; eauto; dcr.
  do 2 eexists; eauto using get.
Qed.

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
