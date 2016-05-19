Require Import Util List OptionMap LengthEq Map Get.

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
  + cases; simpl; rewrite IHlength_eq; eauto.
Qed.

Lemma of_list_filter X `{OrderedType X} lv Y
  : of_list (List.filter (fun y : X => B[y ∈ lv]) Y) [=] lv ∩ of_list Y.
Proof.
  general induction Y; simpl.
  - cset_tac; intuition.
  - decide (a ∈ lv); simpl.
    rewrite IHY; eauto. cset_tac; intuition.
    rewrite IHY; eauto. cset_tac; intuition.
Qed.


Lemma omap_filter_by A B C f p (Y:list A) (l:list B) (Z:list C)
: omap f Y = Some l
  -> length Y = length Z
  -> omap f (filter_by p Z Y) = Some (filter_by p Z l).
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; simpl in * |- *; eauto.
  monad_inv H. cases; simpl; eauto.
  - rewrite EQ. erewrite IHlength_eq; simpl; eauto.
Qed.

Lemma filter_filter_by_length {X} {Y} (Z:list X) (VL:list Y)
: length Z = length VL
  -> forall p, length (List.filter p Z) =
    length (filter_by p Z VL).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl; eauto.
  cases; simpl. rewrite IHlength_eq; eauto. eauto.
Qed.


Lemma filter_incl2 X `{OrderedType X} (p:X->bool) Z
: of_list (List.filter p Z) ⊆ of_list Z.
Proof.
  general induction Z; simpl.
  - reflexivity.
  - cases; simpl. rewrite IHZ; reflexivity.
    rewrite IHZ. cset_tac; intuition.
Qed.

Lemma filter_by_get A B p (Z:list A) (Y:list B) y n
: get (filter_by p Z Y) n y
  -> { n : nat & { z : A | get Y n y /\ get Z n z /\ p z } }.
Proof.
  intros.
  general induction Z; destruct Y; simpl in * |- *; isabsurd.
  cases in H. eapply get_getT in H.
  inv H.
  do 2 eexists; repeat split; eauto using get.
  rewrite <- Heq; eauto. eapply I.
  eapply getT_get in X.
  edestruct IHZ as [? [? [? []]]]; eauto; dcr.
  do 2 eexists; eauto using get.
  edestruct IHZ as [? [? [? []]]]; eauto; dcr.
  do 2 eexists; eauto using get.
Qed.

Lemma filter_p X p (Z:list X)
: forall n x, get (List.filter p Z) n x -> p x.
Proof.
  intros.
  general induction Z; simpl.
  - isabsurd.
  - simpl in H. cases in H. inv H. rewrite <- Heq. eapply I.
    eapply IHZ; eauto.
    eapply IHZ; eauto.
Qed.

Lemma filter_in X `{OrderedType X} (p:X->bool) `{Proper _ (_eq ==> eq) p} a Z
 :  p a
    -> a \In of_list Z
    -> a \In of_list (List.filter p Z).
Proof.
  general induction Z; simpl in * |- *; eauto.
  - cset_tac. rewrite <- H3 in H1.
    cases; isabsurd. rewrite <- H3. simpl. cset_tac; intuition.
    cases; eauto. simpl. exploit IHZ; eauto. cset_tac; intuition.
Qed.


Lemma agree_on_update_filter X `{OrderedType X} Y `{Equivalence (option Y)}
      (lv:set X) (V: X -> option Y) Z VL
: length Z = length VL
  -> agree_on R lv
             (V [Z <-- List.map Some VL])
             (V [List.filter (fun x => B[x ∈ lv]) Z <--
                             List.map Some (filter_by (fun x => B[x ∈ lv]) Z VL)]).
Proof.
  intros. eapply length_length_eq in H1.
  general induction H1.
  - eapply agree_on_refl. eapply H0.
  - simpl. cases. simpl. eapply agree_on_update_same. reflexivity.
    eapply agree_on_incl. eapply IHlength_eq. eauto. cset_tac; intuition.
    eapply agree_on_update_dead; eauto.
Qed.

Lemma agree_on_update_filter' X `{OrderedType X} Y `{Equivalence (option Y)} (lv:set X) (V V':X -> option Y) Z VL
: length Z = length VL
  -> agree_on R (lv \ of_list Z) V V'
  -> agree_on R lv
             (V [Z <-- List.map Some VL])
             (V' [(List.filter (fun x => B[x ∈ lv]) Z) <-- (List.map Some
                             (filter_by (fun x => B[x ∈ lv]) Z VL))]).
Proof.
  intros.
  eapply agree_on_trans. eapply H0.
  eapply update_with_list_agree; eauto. rewrite map_length; eauto.
  eapply agree_on_update_filter; eauto.
Qed.
