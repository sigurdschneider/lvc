Require Import Util LengthEq.
Require Import Containers.OrderedType Setoid Coq.Classes.Morphisms Computable
        Coq.Classes.RelationClasses.
Require Import Containers.OrderedTypeEx DecSolve MoreList OrderedTypeEx.
Require Import AllInRel.

Class PartialOrder (Dom:Type) := {
  poLe : Dom -> Dom -> Prop;
  poLe_dec :> forall d d', Computable (poLe d d');
  poEq : Dom -> Dom -> Prop;
  poEq_dec :> forall d d', Computable (poEq d d');
  poEq_equivalence :> Equivalence poEq;
  poLe_refl : forall d d', poEq d d' -> poLe d d';
  poLe_trans :> Transitive poLe;
  poLe_antisymmetric :> Antisymmetric _ poEq poLe;
}.

Instance PartialOrder_poLe_refl Dom `{PartialOrder Dom} : Reflexive poLe.
Proof.
  hnf; intros. eapply poLe_refl. reflexivity.
Qed.

Definition poLt {Dom} `{PartialOrder Dom} x y := poLe x y /\ ~ poEq x y.

Lemma poLt_intro Dom `{PartialOrder Dom} x y
  : poLe x y -> ~ poEq x y -> poLt x y.
Proof.
  firstorder.
Qed.

Lemma poLt_poLe Dom `{PartialOrder Dom} x y
  : poLt x y -> poLe x y.
Proof.
  firstorder.
Qed.

Hint Resolve poLt_intro poLt_poLe.

Notation "s '⊑' t" := (poLe s t) (at level 70, no associativity).
Notation "s '⊏' t" := (poLt s t) (at level 70, no associativity).
Notation "s '≣' t" := (poEq s t) (at level 70, no associativity).

Instance PartialOrder_pair_instance X `{PartialOrder X} Y `{PartialOrder Y}
: PartialOrder (X * Y) := {
  poLe x y := poLe (fst x) (fst y) /\ poLe (snd x) (snd y);
  poLe_dec := _;
  poEq x y := poEq (fst x) (fst y) /\ poEq (snd x) (snd y);
  poEq_dec := _
}.
Proof.
  - econstructor.
    + hnf; intros; split; reflexivity.
    + hnf; intros; dcr; split; symmetry; eauto.
    + hnf; intros; dcr; split; etransitivity; eauto.
  - intros; dcr; split; eapply poLe_refl; eauto.
  - hnf; intros; dcr; split; etransitivity; eauto.
  - hnf; intros; dcr; split; eapply poLe_antisymmetric; eauto.
Defined.

Instance PartialOrder_list_instance X `{PartialOrder X}
: PartialOrder (list X) := {
  poLe := list_eq poLe;
  poLe_dec := _;
  poEq := list_eq poEq;
  poEq_dec := _
}.
Proof.
  - intros. general induction H0; eauto using @list_eq, poLe_refl.
  - intros ? ? ? R1 R2.
    general induction R1; inv R2; eauto using @list_eq, poLe_trans.
  - intros ? ? EQ1 EQ2.
    exploit list_eq_length as LEN; eauto. length_equify.
    general induction LEN; inv EQ1; inv EQ2; eauto using @list_eq, poLe_antisymmetric.
Defined.

Instance poLe_poEq_impl Dom `{PartialOrder Dom}
  : Proper (poEq ==> poEq ==> impl) poLe.
Proof.
  unfold Proper, respectful, impl; intros.
  symmetry in H0.
  - eapply poLe_refl in H0. eapply poLe_refl in H1.
    etransitivity; eauto. etransitivity; eauto.
Qed.

Instance poLe_poEq_flip_impl Dom `{PartialOrder Dom}
  : Proper (poEq ==> poEq ==> flip impl) poLe.
Proof.
  unfold Proper, respectful, flip, impl; intros.
  - eapply poLe_refl in H0. symmetry in H1. eapply poLe_refl in H1.
    etransitivity; eauto. etransitivity; eauto.
Qed.

Instance poLe_poEq_iff Dom `{PartialOrder Dom}
  : Proper (poEq ==> poEq ==> iff) poLe.
Proof.
  unfold Proper, respectful, impl; intros.
  split; intros.
  - rewrite <- H0. rewrite H2. eauto using poLe_refl.
  - rewrite H0. rewrite H1. eauto using poLe_refl.
Qed.

Instance poLt_poLe_impl Dom `{PartialOrder Dom}
  : Proper (flip poLe ==> poLe ==> impl) poLt.
Proof.
  unfold Proper, respectful, flip, impl; intros.
  destruct H2. split; intros.
  - etransitivity; eauto. etransitivity; eauto.
  - intro. eapply H3. eapply poLe_antisymmetric; eauto.
    etransitivity; eauto. rewrite <- H4. eauto.
Qed.

Instance poLt_poLe_flip_impl Dom `{PartialOrder Dom}
  : Proper (poLe ==> flip poLe ==> flip impl) poLt.
Proof.
  unfold Proper, respectful, flip, impl; intros.
  destruct H2. split; intros.
  - etransitivity; eauto. etransitivity; eauto.
  - intro. eapply H3. eapply poLe_antisymmetric; eauto.
    etransitivity; eauto. rewrite <- H4. eauto.
Qed.



Instance PartialOrder_ann Dom `{PartialOrder Dom}
: PartialOrder (list Dom) := {
  poLe := PIR2 poLe;
  poLe_dec := @PIR2_computable _ _ poLe poLe_dec;
  poEq := PIR2 poEq;
  poEq_dec := @PIR2_computable _ _ poEq poEq_dec;
}.
Proof.
  - intros. general induction H0; eauto using @PIR2, poLe_refl.
  - intros ? ? A B. general induction A; inv B; eauto 20 using @PIR2, poLe_antisymmetric.
Defined.
