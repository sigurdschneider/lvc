Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec Get CSetNotation CSetTac CSetComputable.

Definition list_union X `{OrderedType X} (L:list (set X)) :=
  fold_left union L ∅.

Arguments list_union [X] {H} L.

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
  cset_tac; intuition.
Qed.

Lemma incl_list_union {X} `{OrderedType X} (s: set X) L n t u
: get L n t
  -> s ⊆ t
  -> s ⊆ fold_left union L u.
Proof.
  intros. general induction L.
  + inv H0.
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
    cset_tac; intuition. rewrite <- H2; eauto.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
