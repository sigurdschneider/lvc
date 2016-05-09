Require Export OrderedType.
Require Export Tactics.

(** * Useful instances of ordered types

   This file corresponds to OrderedTypeEx.v in the standard FSets/FMaps
   library. It contains instances of [OrderedType] for the basic datatypes
   in the library. It also contains generic instances for lists, products,
   pairs and options and tactics that can be useful to design your own
   instance.
   *)

(** ** [Z] *)
Require Import ZArith.
Instance Z_StrictOrder : StrictOrder Zlt (@eq Z) := {
  StrictOrder_Transitive := Zlt_trans;
  StrictOrder_Irreflexive := Zlt_not_eq
}.
Program Instance Z_OrderedType : UsualOrderedType Z := {
  SOT_lt := Zlt;
  SOT_cmp := Zcompare;
  SOT_StrictOrder := Z_StrictOrder
}.
Next Obligation.
  case_eq (Zcompare x y); intro Hcomp; constructor.
  apply Zcompare_Eq_eq; assumption.
  assumption.
  apply Zgt_lt; assumption.
Qed.

(** ** [nat] *)
Instance nat_StrictOrder : StrictOrder lt (@eq nat) := {
  StrictOrder_Transitive := lt_trans
}.
Proof.
  intros x y H abs; rewrite abs in H; exact (lt_irrefl y H).
Qed.

Fixpoint nat_compare (n m : nat) :=
  match n, m with
    | O, O => Eq
    | _, O => Gt
    | O, _ => Lt
    | S n, S m => nat_compare n m
  end.
Property nat_compare_eq :
  forall n m : nat, nat_compare n m = Eq -> n = m.
Proof.
  induction n; destruct m; simpl; intro H; try congruence.
  rewrite (IHn _ H); reflexivity.
Qed.
Property nat_compare_lt :
  forall n m : nat, nat_compare n m = Lt -> n < m.
Proof.
  induction n; destruct m; simpl; intro H; try congruence.
  omega. generalize (IHn _ H); omega.
Qed.
Property nat_compare_gt :
  forall n m : nat, nat_compare n m = Gt -> m < n.
Proof.
  induction n; destruct m; simpl; intro H; try congruence.
  omega. generalize (IHn _ H); omega.
Qed.

Program Instance nat_OrderedType : UsualOrderedType nat := {
  SOT_lt := lt;
  SOT_cmp := nat_compare;
  SOT_StrictOrder := nat_StrictOrder
}.
Next Obligation.
  case_eq (nat_compare x y); intro Hcomp; constructor.
  apply nat_compare_eq; assumption.
  apply nat_compare_lt; assumption.
  apply nat_compare_gt in Hcomp; omega.
Qed.

(** ** [N] *)
Require Import NArith Ndec.
Instance N_StrictOrder :
  StrictOrder (fun p q => Nleb q p = false) (@eq N) := {
  StrictOrder_Transitive := Nltb_trans
}.
Proof.
  intros x y H abs; rewrite abs in H; rewrite Nleb_refl in H; discriminate.
Qed.
Program Instance N_OrderedType : UsualOrderedType N := {
  SOT_lt := fun p q => Nleb q p = false;
  SOT_cmp := Ncompare;
  SOT_StrictOrder := N_StrictOrder
}.
Next Obligation.
  case_eq (Ncompare x y); intro Hcomp; constructor.
  apply Ncompare_Eq_eq; assumption.
  assert (H := Nleb_Nle y x); destruct (Nleb y x); auto.
  assert (H' := (proj1 H) (refl_equal _)); unfold Nle in H'.
  rewrite <- Ncompare_antisym in H'; rewrite Hcomp in H';
    contradiction H'; auto.
  assert (H := Nleb_Nle x y); destruct (Nleb x y); auto.
  assert (H' := (proj1 H) (refl_equal _)); unfold Nle in H'.
  congruence.
Qed.

(** ** [positive] *)
Instance positive_StrictOrder : StrictOrder Plt (@eq positive) := {
  StrictOrder_Transitive := Plt_trans
}.
Proof.
  intros x y H abs; rewrite abs in H; exact (Plt_irrefl y H).
Qed.
Program Instance positive_OrderedType : UsualOrderedType positive := {
  SOT_lt := Plt;
  SOT_cmp := fun p q => Pcompare p q Eq;
  SOT_StrictOrder := positive_StrictOrder
}.
Next Obligation.
  case_eq (Pcompare x y Eq); intro Hcomp; constructor.
  apply Pcompare_Eq_eq; assumption.
  assumption.
  apply ZC1; assumption.
Qed.

(** This [OrderedType] instance provided for positive numbers correspond
   to the intuitive mathematical ordering of positives.
   Another instance can be provided which compares bits
   left-to-right, it is more efficient and can be used in certain setting
   when the meaning of the ordering used does not matter. By default, the
   instance used is the first, canonical one ; this is ensured using
   the priority setting.
   *)
Fixpoint Plt_l2r (p q : positive) :=
  match p, q with
    | xO p', xO q' => Plt_l2r p' q'
    | xO _, _ => True
    | _, xO _ => False
    | xH, xH => False
    | xH, _ => True
    | _, xH => False
    | xI p', xI q' => Plt_l2r p' q'
  end.

Property Plt_l2r_trans :
  forall p q r, Plt_l2r p q -> Plt_l2r q r -> Plt_l2r p r.
Proof.
  induction p; destruct q; destruct r; intros; simpl in *;
    try tauto; eauto.
Qed.
Property Plt_l2r_irrefl :
  forall p q, Plt_l2r p q -> p = q -> False.
Proof.
  induction p; intros; subst; simpl in *; try tauto; eauto.
Qed.
Instance positive_l2r_StrictOrder : StrictOrder Plt_l2r (@eq positive) | 10 := {
  StrictOrder_Transitive := Plt_l2r_trans;
  StrictOrder_Irreflexive := Plt_l2r_irrefl
}.

Fixpoint Pcompare_l2r (p q : positive) :=
  match p, q with
    | xO p', xO q' => Pcompare_l2r p' q'
    | xO _, _ => Lt
    | _, xO _ => Gt
    | xH, xH => Eq
    | xH, _ => Lt
    | _, xH => Gt
    | xI p', xI q' => Pcompare_l2r p' q'
  end.
Property Pcompare_l2r_spec :
  forall p q, compare_spec (@eq _) Plt_l2r p q (Pcompare_l2r p q).
Proof.
  induction p; destruct q; simpl; try (constructor; simpl; auto).
  destruct (IHp q); constructor; simpl; auto; congruence.
  destruct (IHp q); constructor; simpl; auto; congruence.
Qed.
Program Instance positive_l2r_OrderedType : UsualOrderedType positive | 4 := {
  SOT_lt := Plt_l2r;
  SOT_cmp := Pcompare_l2r;
  SOT_StrictOrder := positive_l2r_StrictOrder;
  SOT_compare_spec := Pcompare_l2r_spec
}.

(** ** [Q] *)
Require Import QArith.
Instance Q_StrictOrder : StrictOrder Qlt Qeq := {
  StrictOrder_Transitive := Qlt_trans;
  StrictOrder_Irreflexive := Qlt_not_eq
}.
Program Instance Q_OrderedType : OrderedType Q := {
  _eq := Qeq;
  _lt := Qlt;
  _cmp := Qcompare;
  OT_Equivalence := _;
  OT_StrictOrder := Q_StrictOrder
}.
Next Obligation.
  case_eq (Qcompare x y); intro Hcomp; constructor.
  rewrite Qeq_alt; assumption.
  rewrite Qlt_alt; assumption.
  rewrite Qgt_alt; assumption.
Qed.

(** ** [bool] *)
Require Import Bool.
Inductive bool_lt : bool -> bool -> Prop :=
| bool_lt_intro : bool_lt false true.
Program Instance bool_StrictOrder : StrictOrder bool_lt (@eq bool).
Next Obligation.
  intros x y z H1 H2; inversion H1; subst; inversion H2; subst.
Qed.
Next Obligation.
  inversion H; discriminate.
Qed.

Definition bool_cmp (x y : bool) :=
  match x, y with
    | false, true => Lt
    | true, false => Gt
    | false, false | true, true => Eq
  end.
Program Instance bool_OrderedType : UsualOrderedType bool := {
  SOT_lt := bool_lt;
  SOT_cmp := bool_cmp;
  SOT_StrictOrder := bool_StrictOrder
}.
Next Obligation.
  destruct x; destruct y; constructor; auto; constructor.
Qed.

(** ** [unit] *)
Program Instance unit_StrictOrder : StrictOrder (fun _ _ => False) (@eq unit).
Next Obligation. congruence. Qed.


Program Instance unit_OrderedType : UsualOrderedType unit := {
  SOT_lt := fun _ _ => False;
  SOT_cmp := fun _ _ => Eq;
  SOT_StrictOrder := unit_StrictOrder
}.
Next Obligation.
  constructor; destruct x; destruct y; reflexivity.
Qed.

Generalizable All Variables.
(** ** Products

   The product type [A * B] of two ordered types [A] and [B] is an
   ordered type as well, where equality is pointwise equality and
   the ordering is lexicographic.
*)
Inductive prod_eq {A B}
  (eqA : relation A) (eqB : relation B) : (A * B) -> (A * B) -> Prop :=
| prod_eq_intro :
  forall a b c d, eqA a c -> eqB b d -> prod_eq eqA eqB (a,b) (c,d).
Program Instance prod_Equivalence `(Equivalence A eqA, Equivalence B eqB) :
  Equivalence (prod_eq eqA eqB).
Next Obligation. (* reflexivity *)
  inductive_refl.
Qed.
Next Obligation. (* symmetry *)
  inductive_sym.
Qed.
Next Obligation. (* transitivity *)
  inductive_trans.
Qed.

Instance prod_eq_fst_morphism X Y R R'
: Proper (@prod_eq X Y R R' ==> R) fst.
Proof.
  unfold Proper, respectful; intros.
  inversion H; simpl; eauto.
Qed.

Instance prod_eq_snd_morphism X Y R R'
: Proper (@prod_eq X Y R R' ==> R') snd.
Proof.
  unfold Proper, respectful; intros.
  inversion H; simpl; eauto.
Qed.

Inductive prod_lt {A B}
  (eqA ltA : relation A) (ltB : relation B) : (A * B) -> (A * B) -> Prop :=
| prod_lt_1 :
  forall a b c d, ltA a c -> prod_lt eqA ltA ltB (a, b) (c, d)
| prod_lt_2 :
  forall a b c d, eqA a c -> ltB b d -> prod_lt eqA ltA ltB (a, b) (c, d).
Program Instance prod_StrictOrder `(OrderedType A, OrderedType B) :
  StrictOrder (@prod_lt A B _eq _lt _lt) (@prod_eq A B _eq _eq).
Next Obligation. (* transitivity *)
  inductive_lexico_trans.
Qed.
Next Obligation. (* irreflexivity *)
  revert H1; generalize (a0, b0) (a, b).
  inductive_irrefl.
Qed.
Program Instance prod_UsualStrictOrder
  `(UsualOrderedType A, UsualOrderedType B) :
  StrictOrder (@prod_lt A B (@Logic.eq _) _lt _lt) (@Logic.eq _).
Next Obligation. (* transitivity *)
  do 4 intro; inversion_clear 0; intro; inversion_clear 0;
    subst; try (constructor; auto; solve_by_trans_modulo).
Qed.
Next Obligation. (* irreflexivity *)
  intro E; inversion E; subst; clear E.
  revert H1; generalize (a, b).
  destruct p; intros; inversion H1; subst; order.
Qed.

Definition prod_compare `{OrderedType A, OrderedType B} (x y : A * B) :=
  let (a, b) := x in
    let (c, d) := y in
      match a =?= c with
        | Eq => b =?= d
        | Lt => Lt | Gt => Gt
      end.
Program Instance prod_OrderedType `(OrderedType A, OrderedType B) :
  OrderedType (A * B) := {
  _eq := @prod_eq A B _eq _eq;
  _lt := @prod_lt A B _eq _lt _lt;
  _cmp := prod_compare;
  OT_Equivalence := prod_Equivalence _ _;
  OT_StrictOrder := prod_StrictOrder _ _
}.
Next Obligation.
  generalize (a0, b0) (a, b); solve_compare_spec.
Qed.

Program Instance prod_UsualOrderedType
  `(UsualOrderedType A, UsualOrderedType B) : UsualOrderedType (A * B) := {
 SOT_lt := @prod_lt A B (@Logic.eq _) SOT_lt SOT_lt;
 SOT_cmp := prod_compare;
 SOT_StrictOrder := prod_UsualStrictOrder _ _
}.
Next Obligation.
  simpl; destruct (compare_dec a0 a); try do 2 constructor; auto.
  destruct (compare_dec b0 b); constructor; auto.
  constructor 2; auto. rewrite H1, H2; auto. constructor 2; try symmetry; auto.
Qed.

(** ** Products, revisited

   There is another, less canonical, way to compare products : by simply
   ignoring the second component of the pair. We give it higher priority
   than the first one because it should probably not be used by default.
   It is used when comparing pairs (key, value) in a map for instance,
   where only the first component matters.

   NB : it is fundamental that this instance be local, hence we define
   it in a section. Otherwise, even with a very high priority setting,
   it will be used instead of the normal [prod_OrderedType] for a
   product [A * B] as soon as the ordered type for [B] is complicated
   enough. To use this instance, it shall be specified manually.
   *)
Section AsymProd.
  Inductive asym_prod_eq {A} (B : Type)
    (eqA : relation A) : (A * B) -> (A * B) -> Prop :=
  | asym_prod_eq_intro :
    forall a b c d, eqA a c -> asym_prod_eq B eqA (a,b) (c,d).
  Program Instance asym_prod_Equivalence `(Equivalence A eqA) (B : Type) :
    Equivalence (asym_prod_eq B eqA) | 4.
  Next Obligation. (* reflexivity *)
    inductive_refl.
  Qed.
  Next Obligation. (* symmetry *)
    inductive_sym.
  Qed.
  Next Obligation. (* transitivity *)
    inductive_trans.
  Qed.

  Inductive asym_prod_lt {A} (B : Type)
    (ltA : relation A) : (A * B) -> (A * B) -> Prop :=
  | asym_prod_lt_1 :
    forall a b c d, ltA a c -> asym_prod_lt B ltA (a, b) (c, d).
  Program Instance asym_prod_StrictOrder `(OrderedType A) (B : Type) :
    StrictOrder (@asym_prod_lt A B _lt) (@asym_prod_eq A B _eq) | 4.
  Next Obligation. (* transitivity *)
    inductive_lexico_trans.
  Qed.
  Next Obligation. (* irreflexivity *)
    revert H0; generalize (a0, b0) (a, b).
    inductive_irrefl.
  Qed.

  Definition asym_prod_compare `{OrderedType A} {B : Type} (x y : A * B) :=
    fst x =?= fst y.
  Local Program Instance asym_prod_OrderedType `(OrderedType A) (B : Type) :
    OrderedType (A * B) := {
      _eq := @asym_prod_eq A B _eq;
      _lt := @asym_prod_lt A B _lt;
      _cmp := asym_prod_compare;
      OT_Equivalence := asym_prod_Equivalence _ _;
      OT_StrictOrder := asym_prod_StrictOrder _ _
    }.
  Next Obligation.
    unfold asym_prod_compare; simpl.
    destruct (compare_dec a0 a); try do 2 constructor; auto.
  Qed.
End AsymProd.

(** ** Sums *)
Inductive sum_eq {A B}
  (eqA : relation A) (eqB : relation B) : (A + B) -> (A + B) -> Prop :=
| sum_eq_inl : forall a a', eqA a a' -> sum_eq eqA eqB (inl _ a) (inl _ a')
| sum_eq_inr : forall b b', eqB b b' -> sum_eq eqA eqB (inr _ b) (inr _ b').
Program Instance sum_Equivalence `(Equivalence A eqA, Equivalence B eqB) :
  Equivalence (sum_eq eqA eqB).
Next Obligation. (* reflexivity *)
  inductive_refl.
Qed.
Next Obligation. (* symmetry *)
  inductive_sym.
Qed.
Next Obligation. (* transitivity *)
  inductive_trans.
Qed.

Inductive sum_lt {A B}
  (ltA : relation A) (ltB : relation B) : (A + B) -> (A + B) -> Prop :=
| sum_lt_inl :
  forall a a', ltA a a' -> sum_lt ltA ltB (inl _ a) (inl _ a')
| sum_lt_trans :
  forall a b, sum_lt ltA ltB (inl _ a) (inr _ b)
| sum_lt_inr :
  forall b b', ltB b b' -> sum_lt ltA ltB (inr _ b) (inr _ b').
Program Instance sum_StrictOrder
  `(StrictOrder A ltA eqA, StrictOrder B ltB eqB) :
  StrictOrder (sum_lt ltA ltB) (sum_eq eqA eqB).
Next Obligation. (* transitivity *)
  inductive_lexico_trans.
Qed.
Next Obligation. (* irreflexivity *)
  revert x y H1; inductive_irrefl.
Qed.
Instance sum_UsualStrictOrder
  `(StrictOrder A ltA (@Logic.eq _), StrictOrder B ltB (@Logic.eq _)) :
  StrictOrder (sum_lt ltA ltB) (@Logic.eq _).
Proof.
  constructor.
  inductive_lexico_trans.
  intros; intro E; inversion E; subst; clear E.
  destruct y; inversion H1; subst; order.
Qed.

Definition sum_compare `{OrderedType A, OrderedType B} (x y : A + B) :=
  match x, y with
    | inl a, inl a' => a =?= a'
    | inl _, inr _ => Lt
    | inr _, inl _ => Gt
    | inr b, inr b' => b =?= b'
  end.
Program Instance sum_OrderedType `(OrderedType A, OrderedType B) :
  OrderedType (A+B) := {
  _eq := @sum_eq A B _eq _eq;
  _lt := @sum_lt A B _lt _lt;
  _cmp := sum_compare;
  OT_Equivalence := sum_Equivalence _ _;
  OT_StrictOrder := sum_StrictOrder OT_StrictOrder OT_StrictOrder
}.
Next Obligation.
  generalize x y; solve_compare_spec.
Qed.
Program Instance sum_UsualOrderedType
  `(UsualOrderedType A, UsualOrderedType B) :
  UsualOrderedType (A+B) := {
  SOT_lt := @sum_lt A B _lt _lt;
  SOT_cmp := sum_compare;
  SOT_StrictOrder := sum_UsualStrictOrder SOT_StrictOrder SOT_StrictOrder
}.
Next Obligation.
  destruct x as [a|b]; destruct y as [c|d]; simpl; try (do 2 constructor).
  destruct (compare_dec a c); try do 2 constructor; auto.
  constructor; rewrite H1; auto.
  destruct (compare_dec b d); try do 2 constructor; auto.
  constructor; rewrite H1; auto.
Qed.

(** ** Lists of comparable elements

   The list type [list A] of an ordered type [A] is an ordered type
   as well, where equality is pointwise equality and
   the ordering is lexicographic.
   *)
Require Import List.
Inductive list_eq {A} (eqA : relation A) : list A -> list A -> Prop :=
| list_eq_nil : list_eq eqA nil nil
| list_eq_cons :
  forall a a' l l', eqA a a' -> list_eq eqA l l' ->
    list_eq eqA (cons a l) (cons a' l').
Program Instance list_Equivalence `(Equivalence A eqA) :
  Equivalence (list_eq eqA).
Next Obligation. (* reflexivity *)
  unfold Reflexive; rinductive_refl.
Qed.
Next Obligation. (* symmetry *)
  unfold Symmetric; rinductive_sym.
Qed.
Next Obligation. (* transitivity *)
  rinductive_trans.
Qed.

Lemma list_eq_length A R l l'
  : @list_eq A R l l' -> length l = length l'.
Proof.
  intros. induction H; simpl; eauto.
Qed.


Inductive list_lt {A} (ltA eqA : relation A) : list A -> list A -> Prop :=
| list_lt_nil :
  forall a l, list_lt ltA eqA nil (cons a l)
| list_lt_cons_1 :
  forall a a' l l', ltA a a' -> list_lt ltA eqA (cons a l) (cons a' l')
| list_lt_cons_2 :
  forall a a' l l', eqA a a' -> list_lt ltA eqA l l' ->
    list_lt ltA eqA (cons a l) (cons a' l').
Program Instance list_StrictOrder `(OrderedType A) :
  StrictOrder (@list_lt A _lt _eq) (@list_eq A _).
Next Obligation. (* transitivity *)
  intros nx ny nz nHlt1; revert nz; induction nHlt1;
    do 2 intro; inversion_clear 0;
      try now (constructor; try solve_by_trans_modulo).
  constructor 3; order.
Qed.
Next Obligation. (* irreflexivity *)
  generalize x y H0; rinductive_irrefl.
Qed.
Program Instance list_UsualStrictOrder `(UsualOrderedType A) :
  StrictOrder (@list_lt A _lt (@Logic.eq _)) (@Logic.eq _).
Next Obligation. (* irreflexivity *)
  intro E; inversion E; subst; clear E.
  revert y H0; induction y; intro H0; inversion H0; subst; auto; order.
Qed.

Fixpoint list_compare `{OrderedType A} (x y : list A) :=
  match x, y with
    | nil, nil => Eq
    | nil, cons _ _ => Lt
    | cons _ _, nil => Gt
    | cons a l, cons a' l' =>
      match a =?= a' with
        | Eq => list_compare l l'
        | Lt => Lt
        | Gt => Gt
      end
  end.
Program Instance list_OrderedType `(OrderedType A) :
  OrderedType (list A) := {
  _eq := @list_eq A _eq;
  _lt := @list_lt A _lt _eq;
  _cmp := list_compare;
  OT_Equivalence := list_Equivalence OT_Equivalence;
  OT_StrictOrder := list_StrictOrder _
}.
Next Obligation.
  revert y; induction x; destruct y; simpl; try (do 2 constructor).
  destruct (compare_dec a a0); try do 2 constructor; auto.
  destruct (IHx y); constructor.
  constructor 3; auto.
  constructor 2; auto.
  constructor 3; auto; symmetry; auto.
Qed.
Program Instance list_UsualOrderedType `(UsualOrderedType A) :
  UsualOrderedType (list A) := {
  SOT_lt := @list_lt A _lt (@Logic.eq _);
  SOT_cmp := list_compare;
  SOT_StrictOrder := list_UsualStrictOrder _
}.
Next Obligation.
  revert y; induction x; destruct y; simpl; try (do 2 constructor).
  destruct (compare_dec a a0); try do 2 constructor; auto.
  destruct (IHx y); constructor.
  constructor 3; auto.
  congruence.
  constructor 3; auto; symmetry; auto.
Qed.

(** ** Options *)
Inductive option_eq {A} (eqA : relation A) : option A -> option A -> Prop :=
| option_eq_None : option_eq eqA None None
| option_eq_Some : forall a a', eqA a a' -> option_eq eqA (Some a) (Some a').
Program Instance option_Equivalence `(Equivalence A eqA) :
  Equivalence (option_eq eqA).
Next Obligation. (* reflexivity *)
  inductive_refl.
Qed.
Next Obligation. (* symmetry *)
  inductive_sym.
Qed.
Next Obligation. (* transitivity *)
  inductive_trans.
Qed.

Inductive option_lt {A} (ltA : relation A) : option A -> option A -> Prop :=
| option_lt_None :
  forall a, option_lt ltA None (Some a)
| option_lt_Some :
  forall a a', ltA a a' -> option_lt ltA (Some a) (Some a').
Program Instance option_StrictOrder `(OrderedType A) :
  StrictOrder (@option_lt A _lt) (@option_eq A _) | 10.
Next Obligation. (* transitivity *)
  inductive_lexico_trans.
Qed.
Next Obligation. (* irreflexivity *)
  revert x y H0; inductive_irrefl.
Qed.
Program Instance option_UsualStrictOrder `(UsualOrderedType A) :
  StrictOrder (@option_lt A _lt) (@Logic.eq _) | 10.
Next Obligation. (* irreflexivity *)
  intro E; inversion E; subst; clear E.
  revert y H0; induction y; intro H0; inversion H0; subst; auto; order.
Qed.

Definition option_compare `{OrderedType A} (x y : option A) :=
  match x, y with
    | None, None => Eq
    | None, Some _ => Lt
    | Some _, None => Gt
    | Some a, Some a' => a =?= a'
  end.
Program Instance option_OrderedType `(OrderedType A) :
  OrderedType (option A) := {
  _eq := @option_eq A _eq;
  _lt := @option_lt A _lt;
  _cmp := option_compare;
  OT_Equivalence := option_Equivalence OT_Equivalence;
  OT_StrictOrder := option_StrictOrder _
}.
Next Obligation.
  revert x y; solve_compare_spec.
Qed.
Program Instance option_UsualOrderedType `(UsualOrderedType A) :
  UsualOrderedType (option A) := {
  SOT_lt := @option_lt A _lt;
  SOT_cmp := option_compare;
  SOT_StrictOrder := option_UsualStrictOrder _
}.
Next Obligation.
  destruct x; destruct y; simpl; try (do 2 constructor).
  destruct (compare_dec a a0); try do 2 constructor; auto.
  constructor; congruence.
Qed.