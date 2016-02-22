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
  lud. exfalso. eapply H2. eapply lookup_set_spec; eauto. eexists x0; intuition.
  cset_tac; intuition.
  exfalso; eauto.
Qed.

Lemma inverse_on_comp {X} `{OrderedType X} {Y} `{OrderedType Y} {Z} `{OrderedType Z}
  (f:X -> Y) f' (g:Y -> Z) g' x y z D
: inverse_on D ((f[x<-y]) ∘ (g[y<-z])) ((g'[z<-y]) ∘ (f'[y<-x]))
  -> inverse_on D ((f ∘ g) [x <- z]) ((g' ∘ f') [z <- x]).
Proof.
  intros. hnf; intros; unfold comp in *.
  lud; try (now exfalso; eauto).
  simpl in *. specialize (H2 x0 H3). simpl in H2.
  lud; exfalso; eauto.
  specialize (H2 x0 H3). simpl in H2. lud.
  exfalso; eauto.
Qed.

Lemma inverse_on_comp_agree {X} `{OrderedType X} {Y} `{OrderedType Y} {Z} `{OrderedType Z}
  (f:X -> Y) f' (g:Y -> Z) g' x y z D
: inverse_on D ((f[x<-y]) ∘ (g[y<-z])) ((g'[z<-y]) ∘ (f'[y<-x]))
  -> agree_on _eq D ((f[x<-y]) ∘ (g[y<-z])) ((f ∘ g) [x <- z]).
Proof.
  intros. hnf; intros; unfold comp in *.
  lud; try (now exfalso; eauto).
  specialize (H2 x0 H3). simpl in H2.
  lud; try (now exfalso; eauto).
Qed.

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
  intros. eapply length_length_eq in H6. eapply length_length_eq in H7.
  general induction H6. reflexivity.
  inv H7; simpl in *.
  specialize (IHlength_eq _ _ _ _ _ _ _ _ _ _ _ _ YL0 (D\{{x}}) X0).
  assert (D ⊆ (D \ {{x}}) ∪ {{x}}). cset_tac. decide(a === x); intuition.
  eapply agree_on_incl; eauto. eapply agree_on_union.
  - hnf; intros. cset_tac; eqs. intuition. lud; intuition.
    unfold agree_on in IHlength_eq. symmetry. rewrite <- IHlength_eq.
    + unfold comp. lud. specialize (H8 _ H11). unfold comp in H8. lud.
      exfalso; eauto.
    + hnf; intros. cset_tac; eqs.
      specialize (H8 _ H15).
      unfold comp in H8.
      unfold comp. lud; exfalso; eauto.
    + cset_tac; intuition.
  - hnf; intros. cset_tac; intuition. unfold comp. lud. exfalso; eauto.
Qed.
