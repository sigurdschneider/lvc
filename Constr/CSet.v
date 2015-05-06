Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec Computable Util.
Require Export CSetNotation CSetTac CSetBasic CSetCases CSetGet CSetComputable CSetDisjoint.

Set Implicit Arguments.

Lemma Proper_eq_fun X H0 (f:X->X)
:  @Proper (X -> X)
           (@respectful X X
                        (@_eq X (@SOT_as_OT X (@eq X) H0))
                        (@_eq X (@SOT_as_OT X (@eq X) H0))) f.
Proof.
  intuition.
Qed.

Hint Resolve Proper_eq_fun.

Hint Resolve incl_empty minus_incl incl_right incl_left : auto.

Definition pe X `{OrderedType X} := prod_eq (@Equal X _ _) (@Equal X _ _).

Instance pe_morphism X `{OrderedType X}
 : Proper (Equal ==> Equal ==> (@pe X _)) pair.
Proof.
  unfold Proper, respectful.
  intros. econstructor; eauto.
Qed.

Instance pe_refl X `{OrderedType X} : Symmetric (@pe _ _).
Proof.
  hnf; intros. inv H0; econstructor; eauto.
  + rewrite H1; eauto; reflexivity.
  + rewrite H2; eauto; reflexivity.
Qed.

Instance pe_sym X `{OrderedType X} : Symmetric (@pe _ _).
Proof.
  hnf; intros. inv H0; econstructor; eauto.
  + rewrite H1; eauto; reflexivity.
  + rewrite H2; eauto; reflexivity.
Qed.

Instance pe_trans X `{OrderedType X} : Transitive (@pe _ _).
Proof.
  hnf; intros ? ? ? B C.
  eapply prod_Equivalence_obligation_3; eauto using Equal_ST.
Qed.

Ltac pe_rewrite :=
  repeat
    (match goal with
       | [ H : pe ?an _, H' : context [?an] |- _ ] => rewrite H in H'; simpl in H'
       | [ H : pe ?an _ |-  context [?an] ] => rewrite H; simpl
     end).


Instance Subset_morphism_2 X `{OrderedType X}
  : Proper (flip Subset ==> Subset ==> impl) (Subset).
Proof.
  unfold Proper, respectful, impl; intros.
  firstorder.
Qed.

Instance Subset_morphism_3 X `{OrderedType X}
  : Proper (Subset ==> flip Subset ==> flip impl) (Subset).
Proof.
  unfold Proper, respectful, impl; intros.
  firstorder.
Qed.

Lemma minus_single_singleton X `{OrderedType X} (s : set X) (x:X)
: s \ singleton x [=] s \ {x; {}}.
Proof.
  cset_tac; intuition.
Qed.

Lemma minus_single_singleton' X `{OrderedType X} (s : set X) (x:X)
: s \ singleton x ⊆ s \ {x; {}}.
Proof.
  cset_tac; intuition.
Qed.

Lemma minus_single_singleton'' X `{OrderedType X} (s : set X) (x:X)
: s \ {x; {}} ⊆ s \ singleton x.
Proof.
  cset_tac; intuition.
Qed.

Lemma fresh_of_list {X} `{OrderedType X} (L:list X) (y:X)
  : Util.fresh y L -> y ∉ of_list L.
Proof.
  general induction L; simpl in *. intro; cset_tac; eauto.
  intro. cset_tac; intuition.
  eapply IHL; eauto. intro. eapply H0. constructor 2. eauto.
Qed.

Hint Extern 20 (?s \ {?x; {}} ⊆ ?s \ singleton ?x) => eapply minus_single_singleton''.
Hint Extern 20 (?s \ singleton ?x ⊆ ?s \ {?x; {}}) => eapply minus_single_singleton'.

Hint Extern 20 (?s \ {?x; {}} [=] ?s \ singleton ?x) => rewrite minus_single_singleton; reflexivity.
Hint Extern 20 (?s \ singleton ?x [=] ?s \ {?x; {}}) => rewrite minus_single_singleton; reflexivity.


Hint Extern 20 (Subset (?a \ _) ?a) => eapply minus_incl.
Hint Extern 20 (Subset (?a \ _) ?a') => (is_evar a ; fail 1)
                                        || (has_evar a ; fail 1)
                                        || (is_evar a' ; fail 1)
                                        || (has_evar a'; fail 1)
                                        || eapply minus_incl.


Hint Extern 10 (Subset ?a (_ ∪ ?a)) => eapply incl_right.


Instance diff_proper_impl X `{OrderedType X}
: Proper (flip Subset ==> Subset ==> flip Subset) diff.
Proof.
  unfold Proper, respectful, flip; intros.
  cset_tac; intuition.
Qed.

Definition max_set {X} `{OrderedType X} (a:set X) (b:set X) :=
  if [SetInterface.cardinal a < SetInterface.cardinal b] then
    b
  else
    a.

Lemma cardinal_difference {X} `{OrderedType X} (s t: set X)
: SetInterface.cardinal (s \ t) <= SetInterface.cardinal s.
Proof.
  erewrite <- (diff_inter_cardinal s t).
  omega.
Qed.

Lemma cardinal_difference' {X} `{OrderedType X} (s t: set X)
: t ⊆ s
  -> SetInterface.cardinal (s \ t) = SetInterface.cardinal s - SetInterface.cardinal t.
Proof.
  intros.
  erewrite <- (diff_inter_cardinal s t).
  assert (s ∩ t [=] t). (cset_tac; intuition; eauto).
  rewrite H1. omega.
Qed.


Instance cardinal_morph {X} `{OrderedType X}
: Proper (@Subset X _ _ ==> Peano.le)  SetInterface.cardinal.
Proof.
  unfold Proper, respectful; intros.
  eapply subset_cardinal; eauto.
Qed.

Lemma cardinal_of_list_unique {X} `{OrderedType X} (Z:list X)
: unique Z -> SetInterface.cardinal (of_list Z) = length Z.
Proof.
  general induction Z; simpl in * |- *.
  - eapply empty_cardinal.
  - dcr. erewrite cardinal_2. rewrite IHZ; eauto.
    intro. eapply H1. eapply InA_in; eauto.
    hnf; cset_tac; intuition.
Qed.


Lemma cardinal_map {X} `{OrderedType X} {Y} `{OrderedType Y} (s: set X) (f:X -> Y) `{Proper _ (_eq ==> _eq) f}
: SetInterface.cardinal (SetConstructs.map f s) <= SetInterface.cardinal s.
Proof.
  pattern s. eapply set_induction.
  - intros. repeat rewrite SetProperties.cardinal_1; eauto.
    hnf. intros; intro. eapply map_iff in H3. dcr.
    eapply H2; eauto. eauto.
  - intros.
    erewrite (SetProperties.cardinal_2 H3 H4); eauto.
    decide (f x ∈ SetConstructs.map f s0).
    + assert (SetConstructs.map f s0 [=] {f x; SetConstructs.map f s0}).
      cset_tac; intuition. rewrite <- H6; eauto.
      rewrite <- H2. rewrite H5.
      assert (SetConstructs.map f s' ⊆ {f x; SetConstructs.map f s0}).
      hnf; intros.
      eapply map_iff in H6.
      cset_tac; intuition; eauto.
      specialize (H4 x0). eapply H4 in H8. destruct H8.
      left. rewrite H6; eauto.
      right. eapply map_iff; eauto. eauto.
      rewrite <- H6. omega.
    + rewrite <- H2. erewrite <- cardinal_2; eauto.
      split; intros.
      decide (f x === y); eauto.
      eapply map_iff in H5; dcr.
      right. eapply map_iff; eauto.
      decide (x0 === x). exfalso. eapply n0. rewrite <- e. eauto.
      eexists x0. split; eauto. specialize (H4 x0).
      rewrite H4 in H7. destruct H7; eauto. exfalso. eapply n1; eauto.
      eauto. eapply map_iff; eauto.
      destruct H5.
      eexists x; split; eauto. eapply H4. eauto.
      eapply map_iff in H5; eauto. dcr.
      eexists x0; split; eauto.
      eapply H4. eauto.
Qed.


Hint Extern 20 ( ?v ∈ singleton ?v ) =>  eapply singleton_iff; reflexivity.
Hint Extern 20 ( ?s ⊆ ?s ∪ _ ) =>  eapply incl_left.
Hint Extern 20 ( ?s ⊆ _ ∪ ?s ) =>  eapply incl_right.
Hint Extern 20 => match goal with
                   | [ H: ?x ∈ ?s, H': ?x ∉ ?s |- _ ] => exfalso; eapply H', H
                 end.

Lemma incl_union_right X `{OrderedType X} s t u
: s ⊆ t -> s ⊆ u ++ t.
Proof.
  cset_tac; intuition.
Qed.

Arguments incl_union_right X [H] s t u _ _ _ .

Lemma incl_union_left X `{OrderedType X} s t u
: s ⊆ t -> s ⊆ t ++ u.
Proof.
  cset_tac; intuition.
Qed.

Arguments incl_union_left X [H] s t u _ _ _ .

Lemma incl_add_right X `{OrderedType X} s t x
: s ⊆ t -> s ⊆ {x; t}.
Proof.
  cset_tac; intuition.
Qed.


Lemma in_add_left X `{OrderedType X} s x
: x ∈ {x; s}.
Proof.
  cset_tac; intuition.
Qed.


Create HintDb cset discriminated.

Hint Resolve incl_union_left incl_union_right incl_add_right in_add_left
             union_left union_right get_list_union_map : cset.
Hint Resolve prod_eq_intro : cset.
Hint Resolve disj_not_in incl_singleton: cset.
Hint Resolve incl_empty : cset.

Hint Resolve add_struct_eq union_struct_eq_1 union_struct_eq_2 disj_struct_1
     disj_struct_1_r disj_struct_2 disj_struct_2_r : cset.

Lemma union_incl_split X `{OrderedType X} s t u
: s ⊆ u -> t ⊆ u -> s ∪ t ⊆ u.
Proof.
  cset_tac; intuition.
Qed.

Hint Resolve union_incl_split : cset.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
