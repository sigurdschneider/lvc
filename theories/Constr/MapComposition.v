Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util LengthEq AutoIndTac.
Require Export CSet Containers.SetDecide.
Require Export MapBasics MapLookup MapLookupList MapInverse MapInjectivity.

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
  general induction LEN1; simpl in *; eauto.
  specialize (IHLEN1 _ _ _ _ _ _ _ _ YL0 (D\ singleton x) X0).
  assert (D ⊆ (D \ singleton x) ∪ singleton x) by eauto with cset.
  eapply agree_on_incl; eauto. eapply agree_on_union.
  - hnf; intros. clear H6.
    cset_tac'. lud.
    unfold agree_on in IHLEN1. symmetry. rewrite <- IHLEN1.
    + unfold comp in *. lud. exfalso. exploit INV; eauto. lud; eauto.
    + hnf; intros.
      cset_tac'.
      exploit INV; eauto.
      unfold comp in *. lud; exfalso; eauto.
    + cset_tac.
  - hnf; intros. cset_tac'. unfold comp. lud. exfalso; eauto.
Qed.



Lemma agree_on_update_dead_both_comp_right X `{OrderedType X} Y R
      (lv:set X) (E E':X -> Y) (f:X->X) `{Proper _ (_eq ==> _eq) f} x v v'
  : ~x ∈ lv
    -> disj {x; lv} (map f lv)
    -> agree_on R lv E (f ∘ E')
    -> agree_on R lv (E [x <- v]) (f ∘ (E'[x <- v'])).
Proof.
  intros NotIn Disj Agr; unfold comp.
  hnf; intros. lud; eauto.
  exfalso. eapply (Disj x); eauto with cset.
Qed.


Lemma agree_on_update_map X `{OrderedType X} Y `{OrderedType Y} (V:X->Y) (x:X) (v:Y)
      (f:X->X) D `{Proper _ (_eq ==> _eq) f} `{Proper _ (_eq ==> _eq) V}
  : injective_on {x; D} f
    -> agree_on _eq D ((f ∘ V)[x <- v])  (fun y => V[f x <- v] (f y)).
Proof.
  intros Inj.
  hnf; intros. lud; eauto.
  - exfalso. rewrite H4 in *. eauto.
  - exfalso. eapply Inj in e; eauto with cset.
Qed.

Lemma agree_on_update_list_map X `{OrderedType X} Y `{OrderedType Y} (V:X->Y)
      (L:list X) (L':list Y)
      (Len:❬L❭=❬L'❭) (f:X->X) D `{Proper _ (_eq ==> _eq) f} `{Proper _ (_eq ==> _eq) V}
  : injective_on (D ∪ of_list L) f
    -> agree_on _eq D ((f ∘ V)[L <-- L'])  (fun x => V[f ⊝ L <-- L'] (f x)).
Proof.
  intros Inj.
  hnf; intros.
  decide (x ∈ of_list L).
  - edestruct (of_list_get_first _ i) as [n]; eauto. dcr.
    edestruct update_with_list_lookup_in_list_first; eauto; dcr.
    intros; intro. eapply H8; eauto.
    instantiate (1:=f ∘ V) in H9.
    pose proof (proper_update_with_list _ _ (f ∘ V) L L') as PEQ.
    unfold respectful, Proper, feq in PEQ.
    rewrite PEQ; [| intros; unfold comp; rewrite H4; reflexivity | symmetry; eapply H5]; clear PEQ.
    rewrite H9.
    setoid_rewrite <- H5 in H8.
    eapply injective_on_incl in Inj; [| eapply incl_right].
    edestruct (get_map_first Inj H6 H8); dcr.
    edestruct update_with_list_lookup_in_list_first; try eapply H4; dcr;
      swap 1 3.
    + rewrite <- H5. rewrite H13. inv_get.
      rewrite EQ. reflexivity.
    + eauto.
    + eauto with len.
  - rewrite lookup_set_update_not_in_Z; eauto.
    exploit (@injective_on_not_in_map _ _ _ _ f _ _ H1 n); eauto.
    eapply injective_on_incl; eauto.
    cset_tac.
    rewrite lookup_set_update_not_in_Z; eauto.
Qed.
