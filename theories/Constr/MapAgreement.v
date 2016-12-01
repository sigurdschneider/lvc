Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util AutoIndTac.
Require Export CSet  Containers.SetDecide.
Require Export MapBasics MapLookup.

Set Implicit Arguments.

Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive.

Section MapAgreement.
  Open Scope fmap_scope.

  Variable X : Type.
  Context `{OrderedType X}.

  Variable Y : Type.

  Definition agree_on (R:relation Y) (D:set X) (E E':X -> Y) :=
    forall x, x ∈ D -> R (E x) (E' x).

  Global Instance agree_on_refl R `{Reflexive Y R} L
    : Reflexive (agree_on R L).
  Proof.
    firstorder.
  Qed.

  Global Instance agree_on_sym  R `{Symmetric Y R} L
    : Symmetric (agree_on R L).
  Proof.
    intros; hnf; firstorder.
  Qed.

  Lemma agree_on_trans R `{Transitive Y R} L
    : Transitive (agree_on R L).
  Proof.
    hnf; intros; hnf; intros. transitivity (y x0); eauto.
  Qed.

  Global Instance agree_on_equivalence `{Equivalence Y} {s:set X}
  : Equivalence (agree_on R s).
  Proof.
    econstructor; eauto using agree_on_refl, agree_on_sym, agree_on_trans.
  Qed.

  Lemma agree_on_update (R:relation Y) L (E E':X->Y) (x:X) (v v':Y)
    : R v v' -> agree_on R L E E' -> agree_on R L (E[x<-v]) (E'[x<-v']).
  Proof.
    intros. hnf; intros; lud; eauto.
  Qed.

  Lemma agree_on_incl R (bv lv:set X) (E E': X -> Y)
    : agree_on R lv E E'
    -> bv ⊆ lv
    -> agree_on R bv E E'.
  Proof.
    firstorder.
  Qed.

  Lemma agree_on_update_same (R:relation Y) (lv:set X) (E E':X -> Y) x v v'
  : R v v'
    -> agree_on R (lv \ singleton x) E E'
    -> agree_on R lv (E [x <- v]) (E' [x <- v']).
  Proof.
    intros ? A. hnf; intros; lud; eauto;
    eapply A. eapply in_in_minus; eauto. cset_tac.
  Qed.

  Lemma agree_on_update_any_same (R:relation Y) (lv:set X) (E E':X -> Y) x v v'
  : R v v'
    -> agree_on R lv E E'
    -> agree_on R (lv ∪ singleton x ) (E [x <- v]) (E' [x <- v']).
  Proof.
    intros inR A. hnf; intros; lud; eauto; eapply A.
    eapply union_cases in H0; destruct H0; eauto. cset_tac.
  Qed.

  Lemma agree_on_update_dead R (lv:set X) (E E':X -> Y) x v
    : ~x ∈ lv
    -> agree_on R lv E E'
    -> agree_on R lv (E [x <- v]) E'.
  Proof.
    intros A B.
    hnf; intros; lud. cset_tac.
    eapply B; eauto.
  Qed.

  Lemma agree_on_update_inv R (lv:set X) (E E':X -> Y) x v
  : agree_on R lv (E [x <- v]) E'
    -> agree_on R (lv \ singleton x) E E'.
  Proof.
    intros A B.
    hnf; intros. cset_tac'.
    exploit A; eauto. lud; cset_tac.
  Qed.

  Lemma agree_on_update_dead_both R (lv:set X) (E E':X -> Y) x v v'
    : ~x ∈ lv
    -> agree_on R lv E E'
    -> agree_on R lv (E [x <- v]) (E'[x <- v']).
  Proof.
    intros A B.
    hnf; intros. lud; eauto.
  Qed.

End MapAgreement.

Lemma lookup_set_agree X `{OrderedType X} Y `{OrderedType Y} s (m m':X -> Y)
`{Proper _ (respectful _eq _eq) m} `{Proper _ (respectful _eq  _eq) m'}
: @agree_on _ _ _ _eq s m m' -> lookup_set m s [=] lookup_set m' s.
Proof.
  intros; split; intros.
  - eapply lookup_set_spec; eauto. eapply lookup_set_spec in H4; dcr; eauto.
    eexists x; split; eauto. rewrite H7; eauto. eapply H3; eauto.
  - eapply lookup_set_spec; eauto. eapply lookup_set_spec in H4; dcr; eauto.
    eexists x; split; eauto. rewrite H7; symmetry; eapply H3; eauto.
Qed.

Definition eagree_on X `{OrderedType X} Y R `{Equivalence Y R} D E E'
           := @agree_on X _ Y R D E E'.

Arguments eagree_on {X} {H} {Y} {R} {H0} D E E'.


(*Global Instance test X `{OrderedType X} Y `{Equivalence Y}
: Proper ((@feq X _ _ Y _ _) ==> (@feq X _ _ Y _ _) ==> iff) R.
*)
Global Instance eq_cset_agree_on_morphism X `{OrderedType X} Y R `{Transitive Y R} `{Symmetric Y R}
: Proper (SetInterface.Equal ==> (@feq X Y R) ==> (@feq X Y R) ==> iff) (agree_on R).
Proof.
  unfold Proper, respectful, agree_on; split; intros.
  + rewrite <- H2 in H6. eauto.
  + rewrite H2 in H6. eauto.
Qed.

Global Instance incl_agree_on_morphism X `{OrderedType X} Y R `{Transitive Y R} `{Symmetric Y R}
: Proper (SetInterface.Equal ==> (@feq X Y R) ==> (@feq X Y R) ==> flip impl) (agree_on R).
Proof.
  unfold Proper, respectful, agree_on, flip, impl; intros.
  rewrite H2 in H6; eauto.
Qed.

Global Instance incl_agree_on_morphism_eq X `{OrderedType X} Y R `{Transitive Y R} `{Symmetric Y R}
: Proper (SetInterface.Equal ==> eq ==> eq ==> flip impl) (agree_on R).
Proof.
  unfold Proper, respectful, agree_on, flip, impl; intros; subst.
  rewrite H2 in H6; eauto.
Qed.

Instance agree_on_iff_morph X `{OrderedType X} Y `{OrderedType Y} s
  : Proper (@agree_on X _ Y _eq s ==> @agree_on X _ Y _eq s ==> iff) (@agree_on X _ Y _eq s) | 1.
Proof.
  eapply (PER_morphism (Equivalence_PER (agree_on_equivalence (Y:=Y)))).
Qed.

Instance agree_on_1_iff_morph X `{OrderedType X} Y `{OrderedType Y} s
  : Proper (@agree_on X _ Y _eq s ==> eq ==> iff) (@agree_on X _ Y _eq s) | 1.
Proof.
  unfold Proper, respectful; intros; subst.
  split; intros.
  - etransitivity; [ symmetry; eassumption | eassumption].
  - etransitivity; [ eassumption | eassumption].
Qed.

Instance agree_on_1_iff_morph_eq X `{OrderedType X} Y s
  : Proper (@agree_on X _ Y eq s ==> eq ==> iff) (@agree_on X _ Y eq s) | 1.
Proof.
  unfold Proper, respectful; intros; subst.
  split; intros.
  - etransitivity; [ symmetry; eassumption | eassumption].
  - etransitivity; [ eassumption | eassumption].
Qed.

Instance agree_on_1_impl_morph X `{OrderedType X} Y s
  : Proper (@agree_on X _ Y eq s ==> eq ==> impl) (@agree_on X _ Y eq s) | 1.
Proof.
  unfold Proper, respectful; intros; subst.
  hnf; intros.
  - etransitivity; [ symmetry; eassumption | eassumption].
Qed.


Lemma eagree_on_union {X} `{OrderedType X} {Y} (f:X->Y) g D D'
  : eagree_on D f g
  -> eagree_on D' f g
  -> eagree_on (D ∪ D') f g.
Proof.
  intros. hnf; intros. cset_tac.
Qed.

Lemma agree_on_union {X} `{OrderedType X} {Y} (f:X->Y) R g D D'
  : agree_on R D f g
  -> agree_on R D' f g
  -> agree_on R (D ∪ D') f g.
Proof.
  intros. hnf; intros. cset_tac.
Qed.

Global Instance agree_on_computable {X} `{OrderedType X} {Y} `{OrderedType Y}
 (f g:X->Y) D `{Proper _ (_eq ==> _eq) f} `{Proper _ (_eq ==> _eq) g}
  : Computable (eagree_on D f g).
Proof.
  case_eq (for_all (fun x => @decision_procedure (f x === g x) _) D); intros.
  eapply for_all_iff in H3. left. hnf; intros.
  specialize (H3 _ H4). simpl in H3.
  unfold decision_procedure in H3; simpl in H3.
  destruct (equiv_computable Y (f x) (g x)); isabsurd; eauto.
  hnf; intros. simpl.
  destruct (decision_procedure (f x === g x));
  destruct (decision_procedure (f y === g y)); try reflexivity.
  exfalso. eapply n. rewrite <- H5; eauto.
  exfalso. eapply n. rewrite H5; eauto.

  right. intro.
  change False with (Is_true false). rewrite <- H3.
  eapply Is_true_eq_left. rewrite <- for_all_iff.
  hnf; intros. simpl. specialize (H4 _ H5).
  destruct (equiv_computable Y (f x) (g x)); isabsurd; eauto.
  hnf; intros. simpl.
  destruct (decision_procedure (f x === g x));
  destruct (decision_procedure (f y === g y)); try reflexivity.
  exfalso. eapply n. rewrite <- H5; eauto.
  exfalso. eapply n. rewrite H5; eauto.
Defined.

Lemma map_agree X `{OrderedType X} Y `{OrderedType Y}
      lv (f:X->Y) `{Proper _ (_eq ==> _eq) f} (g:X->Y) `{Proper _ (_eq ==> _eq) g}
: agree_on _eq lv f g
  -> map f lv [=] map g lv.
Proof.
  intros. intro.
  repeat rewrite map_iff; eauto.
  split; intros []; intros; dcr; eexists x; split; eauto.
  + specialize (H3 x H5). rewrite <- H3; eauto.
  + specialize (H3 x H5). rewrite H3; eauto.
Qed.

Hint Extern 10 (agree_on _ _?a ?a) => reflexivity.

Extraction Inline agree_on_computable.

Global Instance incl_agree_on_morphism_flip_impl X `{OrderedType X} Y R `{Transitive Y R} `{Symmetric Y R}
: Proper (SetInterface.Subset ==> eq ==> eq ==> flip impl) (agree_on R).
Proof.
  unfold Proper, respectful, agree_on, flip, impl; intros; subst.
  rewrite H2 in H6; eauto.
Qed.

Hint Resolve agree_on_incl : cset.


Lemma agree_on_comp X `{OrderedType X} Y
      (V V' V'':X->Y) (f:X->X) D `{Proper _ (_eq ==> _eq) f}
  : agree_on eq (map f D) V' V''
    -> agree_on eq D V (fun x => V'' (f x))
    -> agree_on eq D V (fun x => V' (f x)).
Proof.
  intros.
  hnf; intros. rewrite H1; eauto with cset.
Qed.

Lemma agree_on_comp_both X `{OrderedType X} Y
      (V V':X->Y) (f:X->X) D `{Proper _ (_eq ==> _eq) f}
      `{Proper _ (_eq ==> eq) V}
      `{Proper _ (_eq ==> eq) V'}
  : agree_on eq (map f D) V V'
    <-> agree_on eq D (fun x => V (f x)) (fun x => V' (f x)).
Proof.
  split; intros Agr; hnf; intros.
  + rewrite Agr; eauto with cset.
  + eapply map_iff in H3; eauto; dcr.
    exploit (Agr x0); eauto.
    rewrite <- H6 in H3. eauto.
Qed.

Lemma agree_on_empty X `{OrderedType X} Y D (f g:X->Y) R
  : D ⊆ ∅
    -> agree_on R D f g.
Proof.
  unfold agree_on; intros; exfalso; cset_tac.
Qed.
