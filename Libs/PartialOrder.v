Require Import Util LengthEq.
Require Import Containers.OrderedType Setoid Coq.Classes.Morphisms Computable
        Coq.Classes.RelationClasses.
Require Import Containers.OrderedTypeEx DecSolve MoreList OrderedTypeEx.

Class PartialOrder (Dom:Type) := {
  poLe : Dom -> Dom -> Prop;
  poLe_dec :> forall d d', Computable (poLe d d');
  poEq : Dom -> Dom -> Prop;
  poEq_dec :> forall d d', Computable (poEq d d');
  poEq_refl : forall d d', poEq d d' -> poLe d d';
  poEq_equivalence :> Equivalence poEq;
  po_antisymmetric :> Antisymmetric _ poEq poLe;
}.

Definition poLt {Dom} `{PartialOrder Dom} x y := poLe x y /\ ~ poEq x y.

Instance PartialOrder_pair_instance X `{PartialOrder X} Y `{PartialOrder Y}
: PartialOrder (X * Y) := {
  poLe x y := poLe (fst x) (fst y) /\ poLe (snd x) (snd y);
  poLe_dec := _;
  poEq x y := poEq (fst x) (fst y) /\ poEq (snd x) (snd y);
  poEq_dec := _
}.
Proof.
  - intros; dcr; split; eapply poEq_refl; eauto.
  - econstructor.
    + hnf; intros; split; reflexivity.
    + hnf; intros; dcr; split; symmetry; eauto.
    + hnf; intros; dcr; split; etransitivity; eauto.
  - intros. dcr; split; eapply po_antisymmetric; eauto.
Defined.

Instance PartialOrder_list_instance X `{PartialOrder X}
: PartialOrder (list X) := {
  poLe := list_eq poLe;
  poLe_dec := _;
  poEq := list_eq poEq;
  poEq_dec := _
}.
Proof.
  - intros. general induction H0; eauto using @list_eq, poEq_refl.
  - intros ? ? EQ1 EQ2.
    exploit list_eq_length as LEN; eauto. length_equify.
    general induction LEN; inv EQ1; inv EQ2; eauto using @list_eq, po_antisymmetric.
Defined.
