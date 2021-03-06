Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import Util LengthEq EqDec Get AllInRel.
Require Import CSetNotation CSetTac CSetBasic CSetComputable ElemEq.

Set Implicit Arguments.

Notation "'list_union' L" := (fold_left union L ∅) (at level 40).

Lemma list_union_start {X} `{OrderedType X} (s: set X) L t
: s ⊆ t
  -> s ⊆ fold_left union L t.
Proof.
  intros. general induction L; simpl; eauto.
  eapply IHL; eauto. cset_tac; intuition.
Qed.

Lemma list_union_incl {X} `{OrderedType X} (L:list (set X)) (s s':set X)
  : (forall n t, get L n t -> t ⊆ s')
   -> s ⊆ s'
   -> fold_left union L s ⊆ s'.
Proof.
  intros. general induction L; simpl. eauto.
  assert (a ⊆ s'). eapply H0; eauto using get.
  eapply IHL; eauto. intros. rewrite H0; eauto using get.
  cset_tac; intuition.
Qed.

Lemma incl_list_union {X} `{OrderedType X} (s: set X) L n t u
: get L n t
  -> s ⊆ t
  -> s ⊆ fold_left union L u.
Proof.
  intros. general induction L.
  + simpl. inv H0; eauto.
    - eapply list_union_start; cset_tac; intuition.
Qed.

Lemma list_union_get {X} `{OrderedType X} L (x:X) u
: x ∈ fold_left union L u
  -> { n : nat & { t : set X | get L n t /\ x ∈ t} } + { x ∈ u }.
Proof.
  intros. general induction L; simpl in *; eauto.
  - decide (x ∈ a).
    + left; do 2 eexists; split; eauto using get.
    + edestruct IHL as [[? []]|]; eauto; dcr.
      * left. eauto using get.
      * right. cset_tac; intuition.
Qed.


Lemma get_list_union_map X Y `{OrderedType Y} (f:X -> set Y) L n x
: get L n x
  -> f x [<=] list_union (List.map f L).
Proof.
  intros. eapply incl_list_union.
  + eapply map_get_1; eauto.
  + reflexivity.
Qed.

Lemma get_in_incl X `{OrderedType X} (L:list X) s
: (forall n x, get L n x -> x ∈ s)
  -> of_list L ⊆ s.
Proof.
  intros. general induction L; simpl.
  - cset_tac; intuition.
  - exploit H0; eauto using get.
    exploit IHL; intros; eauto using get.
    cset_tac; intuition.
Qed.

Lemma get_in_of_list X `{OrderedType X} L n x
    : get L n x
      -> x ∈ of_list L.
Proof.
  intros. general induction H0; simpl; cset_tac; intuition.
Qed.

Lemma list_union_start_swap X `{OrderedType X} (L : list (set X)) s
: fold_left union L s [=] s ∪ list_union L.
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

Ltac norm_lunion :=
 repeat match goal with
      | [ |- context [ fold_left union ?A ?B ]] =>
        match B with
          | empty => fail 1
          | _ => rewrite (list_union_start_swap A B)
        end
    end.


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
  general induction H0; simpl; eauto with cset.
  eapply IHPIR2. rewrite H1, pf; eauto.
Qed.

Lemma list_union_eq {X} `{OrderedType X} (L L':list (set X)) (s s':set X)
: length L = length L'
  -> (forall n s t, get L n s -> get L' n t -> s [=] t)
  -> s [=] s'
  -> fold_left union L s [=] fold_left union L' s'.
Proof.
  intros. length_equify.
  general induction H0; simpl; eauto.
  exploit H1; eauto using get.
  rewrite H2, H3; eauto using get.
Qed.

Lemma list_union_f_incl X `{OrderedType X} Y (f g:Y->set X) s
: (forall n y, get s n y -> f y ⊆ g y)
  -> list_union (List.map f s) ⊆ list_union (List.map g s).
Proof.
  intros. general induction s; simpl; eauto.
  norm_lunion.
  rewrite IHs, H0; eauto using get; reflexivity.
Qed.

Lemma list_union_f_eq X `{OrderedType X} Y (f g:Y->set X) s
: (forall n y, get s n y -> f y [=] g y)
  -> list_union (List.map f s) [=] list_union (List.map g s).
Proof.
  intros. general induction s; simpl; eauto.
  norm_lunion.
  rewrite IHs, H0; eauto using get; eauto.
Qed.

Lemma list_union_f_union X `{OrderedType X} Y (f g:Y->set X) s
: list_union (List.map f s) ∪ list_union (List.map g s) [=]
             list_union (List.map (fun x => f x ∪ g x) s).
Proof.
  intros. general induction s; simpl; eauto.
  - cset_tac; intuition.
  - norm_lunion.
    rewrite <- IHs; eauto using get. cset_tac.
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

Require Import CSetDisjoint.

Lemma list_union_disjunct {X} `{OrderedType X} Y D
:  (forall (n : nat) (D' : set X), get Y n D' -> disj D' D)
   <-> disj (list_union Y) D.
Proof.
  split; intros.
  - eapply disj_intersection.
    eapply set_incl;[ cset_tac|].
    hnf; intros.
    general induction Y; simpl in * |- *.
    + cset_tac.
    + exploit H0; eauto using get.
      exploit IHY; intros; eauto using get.
      rewrite list_union_start_swap.
      rewrite list_union_start_swap in H1.
      cset_tac.
  - eapply disj_1_incl; eauto.
    eapply incl_list_union; eauto.
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

Lemma list_union_drop_incl X `{OrderedType X} (L:list (set X)) n
: list_union (drop n L) ⊆ list_union L.
Proof.
  intros; hnf; intros.
  edestruct list_union_get; eauto; dcr.
  eapply incl_list_union; eauto using get_drop. reflexivity.
  cset_tac; intuition.
Qed.

Lemma get_InA_OT X `{OrderedType X} (L:list X) n x
  :  get L n x
     -> InA _eq x L.
Proof.
  intros Get. general induction Get; eauto using InA.
Qed.

Lemma get_InA X (L:list X) n x
  :  get L n x
     -> InA eq x L.
Proof.
  intros Get. general induction Get; eauto using InA.
Qed.

Lemma get_elements_in X `{OrderedType X} s n x
  :  get (elements s) n x
     -> x ∈ s.
Proof.
  intros Get. eapply get_InA_OT in Get.
  rewrite (@InA_in X H) in Get.
  rewrite of_list_elements in Get. eauto.
Qed.


Lemma of_list_get_first X `{OrderedType X} (Z:list X) z
: z ∈ of_list Z
  -> exists n z', get Z n z' /\ z' === z /\ (forall n' z', n' < n -> get Z n' z' -> z' =/= z).
Proof.
  intros. general induction Z; simpl in *.
  decide (z === a).
  - eexists 0, a; repeat split; eauto using get.
    + intros. exfalso. omega.
  - eapply add_iff in H0 as [|].
    + exfalso. cset_tac.
    + edestruct IHZ; eauto. dcr.
      eexists (S x), x0; repeat split; eauto using get.
      * intros. inv H4; intro; eauto. eapply H5; eauto. omega.
Qed.


Lemma get_InA_R X (R:X -> X -> Prop) `{Reflexive X R} (L:list X) n x
  :  Get.get L n x
     -> InA R x L.
Proof.
  revert_until X. clear.
  intros. general induction H0; eauto using InA.
Qed.

Lemma NoDupA_get_neq' X (R:X -> X -> Prop) `{Reflexive X R}
      `{Transitive X R}
      (L:list X) n x m y
  : NoDupA R L
    -> n < m
    -> Get.get L n x
    -> Get.get L m y
    -> ~ R x y.
Proof.
  revert_until X. clear.
  intros.
  general induction H3; invt NoDupA.
  inv H4; try omega.
  eapply get_InA_R in H10; eauto.
  - revert H0 H6 H10 ; clear.
    intros. general induction H10.
    + intro. eapply H6. econstructor; eauto.
    + intro. eapply IHInA; eauto.
  - inv H4; try omega.
    eapply IHget; try eapply H11; eauto; omega.
Qed.

Lemma NoDupA_get_neq X (R:X -> X -> Prop) `{Reflexive X R}
      `{Symmetric X R}
      `{Transitive X R}
      (L:list X) n x m y
  : NoDupA R L
    -> n <> m
    -> Get.get L n x
    -> Get.get L m y
    -> ~ R x y.
Proof.
  intros.
  decide (n < m).
  - eapply NoDupA_get_neq'; eauto.
  - assert (m < n) by omega.
    intro. symmetry in H7.
    eapply NoDupA_get_neq'; eauto.
Qed.


Lemma of_list_list_union
      (X : Type)
      `{OrderedType X}
      (s : ⦃X⦄)
      (L : list ⦃X⦄)
  :
    s ∈ of_list L -> s ⊆ list_union L
.
Proof.
  intro s_in.
  apply of_list_1 in s_in.
  induction s_in;
    simpl in *; eauto.
  - rewrite H0.
    apply list_union_start.
    cset_tac.
  - rewrite list_union_start_swap, IHs_in.
    cset_tac.
Qed.

Lemma list_union_elem_eq_ext
      (X : Type)
      `{OrderedType X}
      (L L' : list ⦃X⦄)
  :
    elem_eq L L'
    -> list_union L [=] list_union L'
.
Proof.
  intros. unfold elem_eq in H0.
  enough (forall (l l' : list ⦃X⦄),
                    of_list l ⊆ of_list l'
                    -> list_union l ⊆ list_union l') as enouf.
  {
    unfold elem_eq.
    apply eq_incl in H0 as [incl1 incl2].
    apply incl_eq; eauto.
  }
  clear L L' H0.
  intros.
  general induction l;
    simpl in *; eauto.
  - cset_tac.
  - norm_lunion.
    rewrite add_union_singleton in H0.
    assert (a ⊆ list_union l') as a_sub.
    {
      apply of_list_list_union; eauto.
      clear IHl; cset_tac.
    }
    rewrite a_sub.
    rewrite IHl with (l':=l'); eauto.
    clear; cset_tac.
    cset_tac.
Qed.
