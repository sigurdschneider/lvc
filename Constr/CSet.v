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


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
