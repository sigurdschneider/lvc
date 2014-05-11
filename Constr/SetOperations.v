Require Export Setoid Coq.Classes.Morphisms.  
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec Get CSet Map.

Lemma fold_union_incl X `{OrderedType.OrderedType X} s u (x:X) y
  : x ∈ y
    -> y ∈ s
    -> x ∈ fold union s u.
Proof.
  revert_except s.
  pattern s. eapply set_induction; intros.
  - exfalso. eapply H0; eauto.
  - rewrite fold_2; eauto. eapply Add_Equal in H2. rewrite H2 in H4.
    cset_tac. destruct H4.
    left. rewrite H4. eauto.
    right. eapply H0; eauto. eapply Equal_ST. eapply union_m.
    hnf; intros. cset_tac; intuition.
Qed.

Lemma transpose_union X `{OrderedType X}
      : transpose Equal union.
Proof.
  hnf; intros. cset_tac; intuition.
Qed.

Lemma transpose_union_subset X `{OrderedType X}
      : transpose Subset union.
Proof.
  hnf; intros. cset_tac; intuition.
Qed.

Lemma fold_union_incl_start X `{OrderedType.OrderedType X} s u (x:X)
  : x ∈ u
    -> x ∈ fold union s u.
Proof.
  revert_except s.
  pattern s. eapply set_induction; intros.
  - rewrite fold_1; eauto using Equal_ST.
  - rewrite fold_2; eauto using Equal_ST, transpose_union. 
    cset_tac. right. eapply H0; eauto.
    eapply union_m.
Qed.

Lemma map_app X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) 
      `{Proper _ (_eq ==> _eq) f} s t 
: map f (s ∪ t) [=] map f s ∪ map f t.
Proof. 
  cset_tac. repeat rewrite map_iff; eauto. 
  split; intros. destruct H2.
  dcr.
  eapply union_cases in H3. firstorder.
  intuition. destruct H3; dcr. eexists; split; eauto. cset_tac; eauto.
  intuition. destruct H3; dcr. eexists; split; eauto. cset_tac; eauto.
Qed.

Lemma map_empty X `{OrderedType X} Y `{OrderedType Y} (f:X->Y) 
      `{Proper _ (_eq ==> _eq) f}
: map f ∅ [=] ∅.
Proof. 
  cset_tac.
  rewrite map_iff; eauto. 
  firstorder. cset_tac; eauto.
Qed.

Instance map_Proper X `{OrderedType X} Y `{OrderedType Y}
  : Proper (@fpeq X Y _eq _ _ ==> _eq ==> _eq) map.
Proof.
  unfold Proper, respectful; intros. inv H1; dcr.
  hnf; intros. repeat rewrite map_iff; eauto.
  intuition. 
  destruct H4; dcr; eexists; split; eauto.
  rewrite <- H2; eauto. rewrite H8. eapply H3.
  destruct H4; dcr; eexists; split; eauto.
  rewrite H2; eauto. rewrite H8. symmetry. eapply H3.
Qed.


Instance fold_union_Proper X `{OrderedType X}
  : Proper (_eq ==> _eq ==> _eq) (fold union).
Proof.
  unfold Proper, respectful.
  intros. revert_except x. pattern x.
  eapply set_induction; intros.
  - repeat rewrite fold_1; eauto.
    rewrite <- H1; eauto.
  - rewrite fold_2; eauto using union_m.
    eapply Add_Equal in H2.
    rewrite H3 in H2.
    eapply Add_Equal in H2.
    symmetry.
    rewrite fold_2; eauto using union_m. 
    rewrite H0; try reflexivity. symmetry; eauto.
    hnf; intros. hnf. cset_tac; intuition.
    hnf; intros. hnf. cset_tac; intuition.    
Qed.

Lemma list_union_start_swap X `{OrderedType X} (L : list (set X)) s
: fold_left union L s[=]s ++ list_union L.
Proof.
  general induction L; unfold list_union; simpl; eauto.
  - cset_tac; intuition.
  - repeat rewrite IHL. cset_tac; intuition.
Qed.

Lemma list_union_app X `{OrderedType X} (L L' : list (set X)) s
: fold_left union (L ++ L') s [=] fold_left union L s ∪ list_union L'.
Proof.
  general induction L; simpl; eauto using list_union_start_swap.
Qed.


Lemma fold_union_app X `{OrderedType X} Gamma Γ'
: fold union (Gamma ∪ Γ') {}[=]
  fold union Gamma {} ∪ fold union Γ' {}.
Proof.
  revert Γ'. pattern Gamma. eapply set_induction.
  - intros. eapply empty_is_empty_1 in H0. 
    rewrite H0. rewrite empty_neutral_union.
    rewrite fold_empty.
    rewrite empty_neutral_union. reflexivity.
  - intros. 
    eapply Add_Equal in H2. rewrite H2.
    assert ({x; s} ++ Γ' [=] (s ++ {x; Γ'})).
    clear_all; cset_tac; intuition.
    rewrite H3. rewrite H0. 
    decide (x ∈ Γ').
    rewrite add_fold; eauto using Equal_ST, union_m, transpose_union.
    rewrite fold_add; eauto using Equal_ST, union_m, transpose_union.
    symmetry. 
    rewrite union_comm. rewrite <- union_assoc.
    rewrite <- (union_comm _ x).
    rewrite (incl_union_absorption _ x). rewrite union_comm. reflexivity.
    hnf; intros. eapply fold_union_incl; eauto. 
    rewrite fold_add; eauto using Equal_ST, union_m, transpose_union.
    rewrite fold_add; eauto using Equal_ST, union_m, transpose_union.
    symmetry. rewrite (union_comm _ x). rewrite union_assoc. reflexivity.
Qed.


Lemma map_single {X} `{OrderedType X} Y `{OrderedType Y} (f:X->Y) 
      `{Proper _ (_eq ==> _eq) f} x
      : map f {{x}} [=] {{f x}}.
Proof.
  hnf; intros. rewrite map_iff; eauto.
  split; intros.
  - destruct H2; dcr. cset_tac. rewrite H4, H3; eauto.
  - cset_tac. eexists x; split; eauto. cset_tac; intuition.
Qed.

Lemma fold_single {X} `{OrderedType X} Y `{Equivalence Y} (f:X->Y->Y) 
      `{Proper _ (_eq ==> R ==> R) f} (x:X) (s:Y)
      : transpose R f
        -> R (fold f {{x}} s) (f x s).
Proof.
  hnf; intros.
  rewrite fold_2; eauto. rewrite fold_empty. reflexivity.
  cset_tac; intuition.
Qed.


Lemma incl_fold_union X `{OrderedType X} s t x
  :  x \In fold union s t
     -> (exists s', s' ∈ s /\ x ∈ s') \/ x ∈ t.
Proof.
  revert_except s. pattern s. eapply set_induction; intros.
  - assert (fold union s0 t [=] t) by
        (rewrite fold_1; eauto using Equal_ST; reflexivity).
    rewrite H2 in H1; eauto.
  - eapply Add_Equal in H2. rewrite H2 in H3.
    decide (x ∈ s0).
    + rewrite fold_add in H3; eauto using union_m, transpose_union_subset.
      cset_tac. destruct H3.
      left. eexists x. split. eapply H2. cset_tac; intuition. eauto.
      edestruct H0; eauto. destruct H4; dcr.
      left; eexists x1; split; eauto. eapply H2. cset_tac; intuition.
      exfalso; eauto.
    + rewrite fold_add with (eqA:=Equal) in H3; eauto using union_m, transpose_union, Equal_ST.
      cset_tac. destruct H3. left; eexists x; split; eauto.
      eapply H2. cset_tac; intuition.
      eapply H0 in H3. destruct H3; eauto.
      destruct H3; dcr. left; eexists x1; split; eauto.
      eapply H2. cset_tac; intuition.
Qed.

Instance fold_union_morphism X `{OrderedType X}
: Proper (Subset ==> Subset ==> Subset) (fold union).
Proof.
  unfold Proper, respectful; intros.
  hnf; intros.
  eapply incl_fold_union in H2. destruct H2. 
  - destruct H2; dcr.
    eapply fold_union_incl; eauto.
  - eapply fold_union_incl_start; eauto.
Qed.


(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
