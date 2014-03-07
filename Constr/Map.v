Require Export Setoid Coq.Classes.Morphisms.  
Require Import EqDec DecidableTactics Util AutoIndTac.
Require Export CSet Containers.SetDecide.

Require Export MapBasics MapLookup MapLookupList MapAgreement MapInjectivity MapUpdate MapAgreeSet InjectiveMapping MapInverse MapComposition.

Lemma fresh_of_list {X} `{OrderedType X} (L:list X) (y:X)
  : Util.fresh y L -> y ∉ of_list L.
Proof.
  general induction L; simpl in *. intro; cset_tac; eauto.
  intro. eapply add_iff in H1. destruct H1.
  eapply H0. constructor. rewrite H1. eauto.
  eapply IHL; eauto. intro. eapply H0. constructor 2. eauto.
Qed.

Lemma inverse_on_update_lookup_set {X} `{OrderedType X} {Y} `{OrderedType Y} (D:set X) (f:X->Y) g 
   `{Proper _ (_eq ==> _eq) f}   x y
  : inverse_on D (f [x <- y]) (g [y <- x])
  -> y ∉ lookup_set f (D\{{x}}).
Proof.
  intros A B. eapply lookup_set_spec in B.
  destruct B as [z]; dcr. cset_tac; eqs.
  specialize (A _ H2). lud. intuition. 
Qed.


Global Instance update_with_list_proper {X} `{OrderedType X} {Y} `{OrderedType Y}
  {Z : list X} {Z' : list Y} {f : X -> Y} `{Proper _ (_eq ==> _eq) f} 
  : Proper (_eq ==> _eq) (update_with_list Z Z' f).
Proof.
  hnf; intros.
  general induction Z; simpl. rewrite H2; eauto.
  destruct Z'. rewrite H2. eauto.
  lud; rewrite H2 in *; try (now exfalso; eauto).
  eapply IHZ; eauto.
Qed.

Lemma lookup_set_update_not_in_Z' {X} `{OrderedType X} {Y} `{OrderedType Y}
  Z Z' f `{Proper _ (_eq ==> _eq) f} x
  : update_with_list Z Z' f x ∉ of_list Z' -> update_with_list Z Z' f x === f x.
Proof.
  general induction Z; simpl in *; eauto.
  destruct Z'; eauto.
  lud. simpl in *; exfalso. eapply H2. eapply add_iff. intuition.
  eapply IHZ; eauto. intro. eapply H2. simpl. eapply add_2; eauto.
Qed.

Lemma lookup_set_update_with_list_in_union {X} `{OrderedType X} {Y} `{OrderedType Y}
  Z Z' f D `{Proper _ (_eq ==> _eq) f}
  : lookup_set (update_with_list Z Z' f) D ⊆ lookup_set f D ∪ of_list Z'.
Proof.
  intros; hnf; intros. eapply lookup_set_spec in H2.
  destruct H2; dcr. destruct_prop (a ∈ of_list Z').
  cset_tac; eauto.
  rewrite H4 in n.
  eapply lookup_set_update_not_in_Z' in n. rewrite n in H4.
  eapply union_2. eapply lookup_set_spec; eauto.
  eauto.
  eapply update_with_list_proper.
Qed.

Lemma lookup_set_update_in_union {X} `{OrderedType X} {Y} `{OrderedType Y}
 f D x y `{Proper _ (_eq ==> _eq) f}
  : lookup_set (f[x <- y]) D ⊆ lookup_set f (D \ {{x}}) ∪ {{y}}.
Proof.
  hnf; intros. eapply lookup_set_spec in H2; destruct H2; dcr.
  lud. cset_tac; eauto. cset_tac; left. eapply lookup_set_spec; eauto.
  eexists x0; cset_tac; eauto. 
  hnf; intros; lud; isabsurd. rewrite H3; eauto.
  hnf; intros; lud; isabsurd. rewrite H3; eauto.
  hnf; intros; lud; isabsurd. rewrite H3; eauto.
Qed.

Lemma lookup_set_update_with_list_in_union_length {X} `{OrderedType X} {Y} `{OrderedType Y}
  Z Z' f D `{Proper _ (_eq ==> _eq) f}
  : length Z = length Z'
    -> lookup_set (update_with_list Z Z' f) D ⊆ (lookup_set f (D \ of_list Z)) ∪ of_list Z'.
Proof.
  intros; hnf; intros. eapply lookup_set_spec in H3.
  destruct H3; dcr. destruct_prop (a ∈ of_list Z').
  cset_tac; eauto.
  destruct_prop(x ∈ of_list Z).
  exfalso. rewrite H5 in n. eapply n. 
  eapply update_with_list_lookup_in; eauto.
  rewrite update_with_list_no_update in H5; eauto.
  eapply union_2. eapply lookup_set_spec; eauto. eexists x. 
  split; eauto. cset_tac; eauto.
  eapply update_with_list_proper.
Qed.

Lemma inverse_on_update_inverse {X} `{OrderedType X} {Y} `{OrderedType Y}
  D x y ϱ ϱ' `{Proper _ (_eq ==> _eq) ϱ}
  : inverse_on (D\{{x}}) ϱ ϱ'
    -> y ∉ lookup_set ϱ (D\{{x}})
    -> inverse_on D (ϱ [x <- y]) (ϱ' [y <- x]).
Proof.
  intros. hnf; intros.
  lud. exfalso. eapply H3; eauto. eapply lookup_set_spec; eauto.
  eexists x0; cset_tac; eauto.
  exfalso; eauto.
  eapply H2. cset_tac; eauto.
Qed.



(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
