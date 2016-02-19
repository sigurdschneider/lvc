Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec Get CSet Map AllInRel.

Lemma transpose_union X `{OrderedType X}
      : transpose Equal union.
Proof.
  repeat (hnf; intros). cset_tac; intuition.
Qed.

Lemma transpose_union_eq X `{OrderedType X}
      : transpose _eq union.
Proof.
  repeat (hnf; intros). cset_tac; intuition.
Qed.

Lemma transpose_union_subset X `{OrderedType X}
      : transpose Subset union.
Proof.
  repeat (hnf; intros). cset_tac; intuition.
Qed.

Lemma fold_union_incl X `{OrderedType.OrderedType X} s u (x:X) y
  : x ∈ y
    -> y ∈ s
    -> x ∈ fold union s u.
Proof.
  revert_except s.
  pattern s. eapply set_induction; intros.
  - exfalso. eapply H0; eauto.
  - rewrite fold_2; eauto using transpose_union, Equal_ST, union_m.
    eapply Add_Equal in H2. rewrite H2 in H4.
    cset_tac. destruct H4.
    left. rewrite H4. eauto.
    right. eapply H0; eauto.
Qed.


Lemma fold_union_incl_start X `{OrderedType.OrderedType X} s u (x:X)
  : x ∈ u
    -> x ∈ fold union s u.
Proof.
  revert_except s.
  pattern s. eapply set_induction; intros.
  - rewrite fold_1; eauto using Equal_ST.
  - rewrite fold_2; eauto using Equal_ST, transpose_union, union_m.
    cset_tac. eauto.
Qed.

Lemma map_app X `{OrderedType X} Y `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f} s t
: map f (s ∪ t) [=] map f s ∪ map f t.
Proof.
  cset_tac. repeat rewrite map_iff; eauto.
  split; intros.
  - destruct H2. dcr.
    eapply union_cases in H3. firstorder.
  - intuition.
    + destruct H3; dcr. eexists; split; eauto. cset_tac; eauto.
    + destruct H3; dcr. eexists; split; eauto. cset_tac; eauto.
Qed.

Lemma map_add X `{OrderedType X} Y `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f} x t
: map f ({x; t}) [=] {f x; map f t}.
Proof.
  cset_tac. repeat rewrite map_iff; eauto.
  split; intros; cset_tac.
  - firstorder.
    left. rewrite H2; eauto.
  - intuition; cset_tac; eauto.
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
  - rewrite fold_2; eauto using union_m, transpose_union_eq.
    eapply Add_Equal in H2.
    rewrite H3 in H2.
    eapply Add_Equal in H2.
    symmetry.
    rewrite fold_2; eauto using union_m, transpose_union_eq.
    rewrite H0; try reflexivity. eauto.
Qed.

Lemma list_union_start_swap X `{OrderedType X} (L : list (set X)) s
: fold_left union L s[=]s ++ list_union L.
Proof.
  general induction L; simpl; eauto.
  - cset_tac; intuition.
  - rewrite IHL. symmetry. rewrite IHL.
    hnf; intros. cset_tac; intuition.
Qed.

Lemma list_union_app X `{OrderedType X} (L L' : list (set X)) s
: fold_left union (L ++ L') s [=] fold_left union L s ∪ list_union L'.
Proof.
  general induction L; simpl; eauto using list_union_start_swap.
Qed.

Lemma list_union_cons X `{OrderedType X} s sl
: list_union (s :: sl) [=] s ∪ list_union sl.
Proof.
  simpl. setoid_rewrite list_union_start_swap.
  hnf; intros. cset_tac; intuition.
Qed.

Lemma incl_list_union_cons X `{OrderedType X} s sl
: list_union sl ⊆ list_union (s :: sl).
Proof.
  simpl. setoid_rewrite list_union_start_swap at 2.
  cset_tac; intuition.
Qed.

Hint Resolve incl_list_union_cons : cset.


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
  - destruct H2; dcr. cset_tac; intuition. rewrite H4, H3; eauto.
  - cset_tac; intuition. eexists x; split; eauto.
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

Lemma list_union_minus_dist X `{OrderedType X} D'' s s' L
  :
    s \ D'' [=] s'
 ->  fold_left union L s \ D''
[=] fold_left union (List.map (fun s => s \ D'') L) s'.
Proof.
  general induction L; simpl; eauto.
  - eapply IHL. rewrite <- H0.
    clear_all; cset_tac; intuition.
Qed.

Instance fold_left_union_morphism X `{OrderedType X}:
  Proper (PIR2 Equal ==> Equal ==> Equal) (fold_left union).
Proof.
  unfold Proper, respectful; intros.
  general induction H0; simpl; eauto.
  - rewrite IHPIR2; eauto. reflexivity.
    rewrite H1, pf. reflexivity.
Qed.

Instance fold_left_subset_morphism X `{OrderedType X}:
  Proper (PIR2 Subset ==> Subset ==> Subset) (fold_left union).
Proof.
  unfold Proper, respectful; intros.
  general induction H0; simpl; eauto.
Qed.

Lemma lookup_set_list_union
      X `{OrderedType X } Y `{OrderedType Y} (ϱ:X->Y) `{Proper _ (_eq ==> _eq) ϱ} l s s'
: lookup_set ϱ s[=]s' ->
  lookup_set ϱ (fold_left union l s)
             [=]  fold_left union (List.map (lookup_set ϱ) l) s'.
Proof.
  general induction l; simpl; eauto.
  eapply IHl; eauto. rewrite lookup_set_union; eauto.
  rewrite H2. reflexivity.
Qed.

Lemma list_union_disjunct {X} `{OrderedType X} Y D
:  (forall (n : nat) (D' : set X), get Y n D' -> disj D' D)
   <-> disj (list_union Y) D.
Proof.
  split; intros.
  - eapply disj_intersection.
    eapply set_incl; try now (cset_tac; intuition).
    hnf; intros.
    general induction Y; simpl in * |- *; intuition.
    exploit H0; eauto using get.
    exploit IHY; intros; eauto using get.
    rewrite list_union_start_swap.
    rewrite list_union_start_swap in H1.
    revert H1 H2; clear_all; cset_tac; intuition; eauto.
  - hnf; intros. eapply H0; eauto.
    eapply incl_list_union. eauto. reflexivity. eauto.
Qed.

Lemma list_union_indexwise_ext X `{OrderedType X} Y (f:Y->set X) Z (g:Z -> set X) L L'
: length L = length L'
  -> (forall n y z, get L n y -> get L' n z -> f y [=] g z)
  -> list_union (List.map f L) [=] list_union (List.map g L').
Proof.
  intros. length_equify.
  general induction H0; simpl; eauto.
  rewrite list_union_start_swap.
  setoid_rewrite list_union_start_swap at 2.
  rewrite IHlength_eq, H1; eauto using get; reflexivity.
Qed.

Lemma list_union_rev X `{OrderedType X} (L:list (set X)) s
: fold_left union L s [=] fold_left union (rev L) s.
Proof.
  general induction L; simpl; eauto.
  rewrite list_union_app.
  simpl.
  rewrite IHL.
  rewrite list_union_start_swap.
  setoid_rewrite list_union_start_swap at 2.
  hnf; intros. clear_all; cset_tac; intuition.
Qed.

Require Import Drop.

Lemma list_union_drop_incl X `{OrderedType X} (L L':list (set X)) n
: list_union (drop n L) ⊆ list_union (drop n L')
  -> list_union (drop n L) ⊆ list_union L'.
Proof.
  intros; hnf; intros.
  eapply H0 in H1.
  edestruct list_union_get; eauto; dcr.
  eapply incl_list_union. eauto using get_drop. reflexivity. eauto.
  cset_tac; intuition.
Qed.

Ltac norm_lunion :=
 repeat match goal with
      | [ |- context [ fold_left union ?A ?B ]] =>
        match B with
          | empty => fail 1
          | _ => rewrite (list_union_start_swap _ A B)
        end
    end.

Lemma list_union_eq {X} `{OrderedType X} (L L':list (set X)) (s s':set X)
: length L = length L'
  -> (forall n s t, get L n s -> get L' n t -> s [=] t)
  -> s [=] s'
  -> fold_left union L s [=] fold_left union L' s'.
Proof.
  intros. length_equify.
  general induction H0; simpl; eauto.
  exploit H1; eauto using get. rewrite H2, H3; eauto using get.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
