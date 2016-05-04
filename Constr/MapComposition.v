Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util LengthEq AutoIndTac.
Require Export CSet Containers.SetDecide.
Require Export MapBasics MapLookup MapLookupList MapInverse.

Set Implicit Arguments.

Definition comp {X Y Z:Type} (f:X -> Y) (g:Y->Z) : X->Z := fun x => g (f x).
Notation "f '∘' g" := (comp f g) (at level 40, left associativity) : fmap_scope.

Open Scope fmap_scope.

Lemma comp_lookup_list X Y Z (f:X -> Y) (g:Y -> Z) L
    : lookup_list (f∘g) L = lookup_list g (lookup_list f L).
Proof.
  general induction L; simpl; eauto.
  f_equal; eauto.
Qed.

Lemma lookup_set_agree_on_comp {X} `{OrderedType X} {Y} `{OrderedType Y} Z (f:X -> Y) (g:Y -> Z)
      `{Proper _ (_eq ==> _eq) f}
      x y z D
: y ∉ lookup_set f (D\{{x}})
  -> agree_on eq D ((f[x<-y]) ∘ (g[y<-z])) ((f ∘ g) [x <- z]).
Proof.
  intros. hnf; intros; unfold comp.
  lud.
  - exfalso; lset_tac.
  - cset_tac; intuition.
Qed.

Lemma inverse_on_comp {X} `{OrderedType X} {Y} `{OrderedType Y} {Z} `{OrderedType Z}
  (f:X -> Y) f' (g:Y -> Z) g' x y z D
: inverse_on D ((f[x<-y]) ∘ (g[y<-z])) ((g'[z<-y]) ∘ (f'[y<-x]))
  -> inverse_on D ((f ∘ g) [x <- z]) ((g' ∘ f') [z <- x]).
Proof.
  intros A. hnf; intros a aInD.
  specialize (A a aInD). unfold comp in A; simpl in A.
  lud; exfalso; eauto.
Qed.

Lemma inverse_on_comp_agree {X} `{OrderedType X} {Y} `{OrderedType Y} {Z} `{OrderedType Z}
  (f:X -> Y) f' (g:Y -> Z) g' x y z D
: inverse_on D ((f[x<-y]) ∘ (g[y<-z])) ((g'[z<-y]) ∘ (f'[y<-x]))
  -> agree_on _eq D ((f[x<-y]) ∘ (g[y<-z])) ((f ∘ g) [x <- z]).
Proof.
  intros A. hnf; intros a aInD.
  specialize (A a aInD). unfold comp in *; simpl in A.
  lud; exfalso; eauto.
Qed.

Lemma incl_minus_union2 X `{OrderedType X} s t
  : s ⊆ (s \ t) ∪ t.
Proof.
  cset_tac.
Qed.

Hint Resolve incl_minus_union2 : cset.

Lemma inverse_on_comp_list {X} `{OrderedType X} {Y} `{OrderedType Y} {Z} `{OrderedType Z}
  (f:X -> Y) (f':Y -> X) (g:Y -> Z) (g': Z -> Y)
  `{Proper _ (_eq ==> _eq) f}  `{Proper _ (_eq ==> _eq) g}
`{Proper _ (_eq ==> _eq) f'}  `{Proper _ (_eq ==> _eq) g'}
XL YL ZL D :
  length XL = length YL
  -> length YL = length ZL

  -> inverse_on D ((update_with_list XL YL f) ∘ (update_with_list YL ZL g))
               ((update_with_list ZL YL g') ∘ (update_with_list YL XL f'))
  -> agree_on _eq D ((update_with_list XL YL f) ∘ (update_with_list YL ZL g)) (update_with_list XL ZL (f ∘ g)).
Proof.
  intros LEN1 LEN2 INV. length_equify.
  general induction LEN1; inv LEN2; simpl in *; eauto.
  specialize (IHLEN1 _ _ _ _ _ _ _ _ _ _ _ _ YL0 (D\ singleton x) X0).
  assert (D ⊆ (D \ singleton x) ∪ singleton x) by eauto with cset.
  eapply agree_on_incl; eauto. eapply agree_on_union.
  - hnf; intros. cset_tac. lud; [ intuition |].
    unfold agree_on in IHLEN1. symmetry. rewrite <- IHLEN1.
    + unfold comp in *. lud. exfalso. exploit INV; eauto. lud; eauto.
    + hnf; intros. cset_tac.
      exploit INV; eauto.
      unfold comp in *. lud; exfalso; eauto.
    + cset_tac; intuition.
  - hnf; intros. cset_tac. unfold comp. lud. exfalso; eauto.
Qed.
