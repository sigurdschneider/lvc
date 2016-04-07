Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util AutoIndTac.
Require Export CSet Containers.SetDecide.

Require Export MapBasics MapLookup MapLookupList MapAgreement MapInjectivity MapUpdate MapAgreeSet MapInverse MapComposition.

Lemma inverse_on_update_lookup_set {X} `{OrderedType X} {Y} `{OrderedType Y} (D:set X) (f:X->Y) g
   `{Proper _ (_eq ==> _eq) f}   x y
  : inverse_on D (f [x <- y]) (g [y <- x])
  -> y ∉ lookup_set f (D\{{x}}).
Proof.
  intros A B. eapply lookup_set_spec in B.
  destruct B as [z]; dcr. cset_tac; eqs; intuition.
  specialize (A _ H2). lud; intuition. intuition.
Qed.

Lemma lookup_set_update_with_list_in_union {X} `{OrderedType X} {Y} `{OrderedType Y}
  Z Z' f D `{Proper _ (_eq ==> _eq) f}
  : lookup_set (update_with_list Z Z' f) D ⊆ lookup_set f D ∪ of_list Z'.
Proof.
  intros; hnf; intros. eapply lookup_set_spec in H2.
  destruct H2; dcr. decide (a ∈ of_list Z').
  cset_tac; eauto.
  rewrite H4 in n.
  eapply lookup_set_update_not_in_Z' in n. rewrite n in H4.
  eapply union_2. eapply lookup_set_spec; eauto.
  eauto.
Qed.

Lemma lookup_set_update_in_union {X} `{OrderedType X} {Y} `{OrderedType Y}
 f D x y `{Proper _ (_eq ==> _eq) f}
  : lookup_set (f[x <- y]) D ⊆ lookup_set f (D \ {{x}}) ∪ {{y}}.
Proof.
  hnf; intros. eapply lookup_set_spec in H2; destruct H2; dcr; eauto.
  lud. cset_tac; eauto. cset_tac; left. eapply lookup_set_spec; eauto.
  eexists x0; cset_tac; eauto.
Qed.

Lemma lookup_set_update_with_list_in_union_length {X} `{OrderedType X} {Y} `{OrderedType Y}
  Z Z' f D `{Proper _ (_eq ==> _eq) f}
  : length Z = length Z'
    -> lookup_set (update_with_list Z Z' f) D ⊆ (lookup_set f (D \ of_list Z)) ∪ of_list Z'.
Proof.
  intros; hnf; intros. eapply lookup_set_spec in H3.
  destruct H3; dcr. decide (a ∈ of_list Z').
  cset_tac; eauto.
  decide(x ∈ of_list Z).
  exfalso. rewrite H5 in n. eapply n.
  eapply update_with_list_lookup_in; eauto.
  erewrite update_with_list_no_update in H5; eauto.
  eapply union_2. eapply lookup_set_spec; eauto. eexists x.
  split; eauto. cset_tac; eauto. eauto.
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
