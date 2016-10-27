Require Export OrderedType.
Require Import SetoidList.
Require OrderedTypeEx.
Require MapInterface.

Generalizable All Variables.

(** This file corresponds to [FMapList.v] in the standard library
   and implements finite maps as ordered lists of bindings. The
   corresponding [FMap] and [FMapSpecs] instances are defined in
   the file [MapListInstance.v].
   *)

Module MapList.
(** The type of maps from elements of type [key] to elements
   of type [elt] is a list of pairs [key * elt].
   It will be without duplicates, and ordered with respect
   to the comparison inferred by the typeclasses mechanism. *)
Definition dict (key : Type) `{OrderedType key} (elt : Type) :=
  list (key * elt).

Section MapDefinitions.
  Variable key : Type.
  Hypothesis (comparedec : OrderedType key).

  Variable elt : Type.
  Let t := dict key.

  Import KeyOrderedType.
  Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

  Definition empty : t elt := nil.
  Definition is_empty (l : t elt) : bool := if l then true else false.

  Function mem (k : key) (s : t elt) {struct s} : bool :=
    match s with
      | nil => false
      | (k',_) :: l =>
        match k =?= k' with
          | Lt => false
          | Eq => true
          | Gt => mem k l
        end
    end.

  Function find (k:key) (s: t elt) {struct s} : option elt :=
    match s with
      | nil => None
      | (k',x)::s' =>
        match k =?= k' with
          | Lt => None
          | Eq => Some x
          | Gt => find k s'
        end
    end.

  Function add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
    match s with
      | nil => (k,x) :: nil
      | (k',y) :: l =>
        match k =?= k' with
          | Lt => (k,x)::s
          | Eq => (k,x)::l
          | Gt => (k',y) :: add k x l
        end
    end.

  Function remove (k : key) (s : t elt) {struct s} : t elt :=
    match s with
      | nil => nil
      | (k',x) :: l =>
        match k =?= k' with
          | Lt => s
          | Eq => l
          | Gt => (k',x) :: remove k l
        end
    end.

  Function insert (k : key) (d : elt) (f : elt -> elt) (s : t elt)
    {struct s} : t elt :=
    match s with
      | nil => (k, d)::nil
      | (k', y) :: l =>
        match k =?= k' with
          | Lt => (k, d)::s
          | Eq => (k, f y)::l
          | Gt => (k', y) :: insert k d f l
        end
    end.

  Function adjust (k : key) (f : elt -> elt) (s : t elt) {struct s} : t elt :=
    match s with
      | nil => nil
      | (k', y) :: l =>
        match k =?= k' with
          | Lt => s
          | Eq => (k, f y)::l
          | Gt => (k', y) :: adjust k f l
        end
    end.

  Definition elements (m: t elt) := m.
  Definition cardinal (m: t elt) := length m.

  Definition choose (m : t elt) : option (key * elt) :=
    match m with
      | nil => None
      | (x,e)::_ => Some (x, e)
    end.

  Function fold (A:Type)(f:key->elt->A->A)(m:t elt) (acc:A) {struct m} : A :=
    match m with
      | nil => acc
      | (k,e)::m' => fold A f m' (f k e acc)
    end.

  Function equal (cmp:elt->elt->bool)(m m' : t elt) { struct m } : bool :=
    match m, m' with
      | nil, nil => true
      | (x,e)::l, (x',e')::l' =>
        match x =?= x' with
          | Eq => if cmp e e' then equal cmp l l' else false
          | _ => false
        end
      | _, _ => false
    end.

  Variable elt':Type.

  Fixpoint map (f:elt -> elt') (m:t elt) {struct m} : t elt' :=
    match m with
      | nil => nil
      | (k,e)::m' => (k,f e) :: map f m'
    end.

  Fixpoint mapi (f: key -> elt -> elt') (m:t elt) {struct m} : t elt' :=
    match m with
      | nil => nil
      | (k,e)::m' => (k,f k e) :: mapi f m'
    end.

  Variable elt'' : Type.
  Variable f : option elt -> option elt' -> option elt''.

  Definition option_cons {A:Type}(k:key)(o:option A)(l:list (key*A)) :=
    match o with
      | Some e => (k,e)::l
      | None => l
    end.

  Fixpoint map2_l (m : t elt) : t elt'' :=
    match m with
      | nil => nil
      | (k,e)::l => option_cons k (f (Some e) None) (map2_l l)
    end.

  Fixpoint map2_r (m' : t elt') : t elt'' :=
    match m' with
      | nil => nil
      | (k,e')::l' => option_cons k (f None (Some e')) (map2_r l')
    end.

  Fixpoint map2 (m : t elt) : t elt' -> t elt'' :=
    match m with
      | nil => map2_r
      | (k,e) :: l =>
        fix map2_aux (m' : t elt') : t elt'' :=
        match m' with
          | nil => map2_l m
          | (k',e') :: l' =>
            match k =?= k' with
              | Lt => option_cons k (f (Some e) None) (map2 l m')
              | Eq => option_cons k (f (Some e) (Some e')) (map2 l l')
              | Gt => option_cons k' (f None (Some e')) (map2_aux l')
            end
        end
    end.
End MapDefinitions.

Implicit Arguments Empty [[key] [elt] [comparedec]].
Implicit Arguments
  empty [[key] [elt] [comparedec]].
Implicit Arguments
  is_empty [[key] [elt] [comparedec]].
Implicit Arguments
  mem [[key] [elt] [comparedec]].
Implicit Arguments
  find [[key] [elt] [comparedec]].
Implicit Arguments
  add [[key] [elt] [comparedec]].
Implicit Arguments
  remove [[key] [elt] [comparedec]].
Implicit Arguments
  insert [[key] [elt] [comparedec]].
Implicit Arguments
  adjust [[key] [elt] [comparedec]].
Implicit Arguments
  equal [[key] [elt] [comparedec]].
Implicit Arguments
  fold [[key] [comparedec] [elt] [A]].
Implicit Arguments
  elements [[key] [elt] [comparedec]].
Implicit Arguments
  choose [[key] [elt] [comparedec]].
Implicit Arguments
  map [[key] [elt] [elt'] [comparedec]].
Implicit Arguments
  mapi [[key] [elt] [elt'] [comparedec]].
Implicit Arguments
  map2 [[key] [elt] [elt'] [elt''] [comparedec]].

(** Maps seen as an OrderedType : list comparison based
   solely on the first component. *)
Import OrderedTypeEx.
(* Definition map_eq `{OrderedType A} (B : Type) : relation (dict A B) := *)
(*   @list_eq (A*B) (asym_prod_eq B _eq). *)
(* Definition map_Equivalence `{OrderedType A} (B : Type) :  *)
(*   Equivalence (map_eq B) := @list_Equivalence (A*B) _ _. *)
(* Existing Instance map_Equivalence. *)

(* Goal forall n : dict nat Prop, n === n. *)
(* Abort. *)

(* Definition map_lt `{OrderedType A} (B : Type) : relation (dict A B) := *)
(*   @list_lt (A*B) (asym_prod_lt B _lt) (asym_prod_eq B _eq). *)
(* Definition map_StrictOrder `{OrderedType A} (B : Type) :  *)
(*   StrictOrder (map_lt B) (map_eq B) :=  *)
(*   @list_StrictOrder (A*B) (asym_prod_OrderedType _ B). *)
(* Existing Instance map_StrictOrder. *)

(* Goal forall n : dict nat Prop, n <<< n. *)
(* Abort. *)

(* Definition map_compare `{OrderedType A} (B : Type) :  *)
(*   dict A B -> dict A B -> comparison :=  *)
(*   @list_compare (A*B) (asym_prod_OrderedType _ B). *)
Definition map_OrderedType `{OrderedType A} (B : Type) :
  OrderedType (dict A B) :=
  @list_OrderedType (A*B) (asym_prod_OrderedType _ B).
Existing Instance map_OrderedType.

Set Implicit Arguments.
Unset Strict Implicit.

Module Import K := KeyOrderedType.
Section MapSpecs.
  Variable key : Type.
  Context `{key_OT : OrderedType key}.
  Variable elt : Type.

  Notation eqk := (eqk (elt:=elt)).
  Notation eqke := (eqke (elt:=elt)).
  Notation ltk := (ltk (elt:=elt)).
  Notation MapsTo := (MapsTo (elt:=elt)).
  Notation In := (In (elt:=elt)).
  Notation Sort := (sort ltk).
  Notation Inf := (lelistA (ltk)).

  Lemma empty_1 : Empty (elt:=elt) empty.
  Proof.
    intros a e.
    intro abs.
    inversion abs.
  Qed.
  Hint Resolve empty_1.

  Lemma empty_sorted : Sort empty.
  Proof.
    unfold empty; auto.
  Qed.

  Lemma is_empty_1 :forall m, Empty (elt:=elt) m -> is_empty m = true.
  Proof.
    intros m.
    case m;auto.
    intros (k,e) l inlist.
    absurd (InA eqke (k, e) ((k, e) :: l)).
    apply inlist. constructor; split; reflexivity.
  Qed.

  Lemma is_empty_2 : forall m, is_empty m = true -> Empty (elt:=elt) m.
  Proof.
    intros m.
    case m;auto.
    intros p l abs.
    inversion abs.
  Qed.

  Lemma mem_1 : forall m (Hm:Sort m) x, In x m -> mem x m = true.
  Proof.
    intros m Hm x; generalize Hm; clear Hm.
    functional induction (mem x m);intros sorted belong1;trivial.

    inversion belong1. inversion H.

    absurd (In x ((k', _x) :: l));try assumption.
    apply Sort_Inf_NotIn with _x; auto.
    destruct (compare_dec x k'); try discriminate; eauto.

    apply IHb.
    elim (sort_inv sorted);auto.
    elim (In_inv belong1);auto.
    intro abs.
    destruct (compare_dec x k'); try discriminate; order.
  Qed.

  Lemma mem_2 : forall m (Hm:Sort m) x, mem x m = true -> In x m.
  Proof.
    intros m Hm x; generalize Hm; clear Hm; unfold K.In, K.MapsTo.
    functional induction (mem x m); intros sorted hyp;
      try ((inversion hyp);fail);
        destruct (compare_dec x k'); try discriminate.
    exists _x; auto; constructor; split; auto.
    induction IHb; auto.
    exists x0; auto.
    inversion_clear sorted; auto.
  Qed.

  Lemma find_2 :  forall m x e, find x m = Some e -> MapsTo x e m.
  Proof.
    intros m x. unfold K.MapsTo.
    functional induction (find x m);simpl;intros e' eqfind;
      inversion eqfind; auto; destruct (compare_dec x k'); try discriminate.
    constructor; split; auto.
  Qed.

  Lemma find_1 :  forall m (Hm:Sort m) x e, MapsTo x e m -> find x m = Some e.
  Proof.
    intros m Hm x e; generalize Hm; clear Hm; unfold K.MapsTo.
    functional induction (find x m);simpl; subst; try clear H_eq_1.

    inversion 2.

    inversion_clear 2; destruct (compare_dec x k'); try discriminate.
    clear e1;compute in H0; destruct H0;order.
    clear e1;generalize (Sort_In_cons_1 Hm (InA_eqke_eqk H0)); compute; order.

    destruct (compare_dec x k'); try discriminate.
    clear e1;inversion_clear 2.
    compute in H1; destruct H1; intuition congruence.
    generalize (Sort_In_cons_1 Hm (InA_eqke_eqk H1)); compute; order.

    destruct (compare_dec x k'); try discriminate.
    clear e1; do 2 inversion_clear 1; auto.
    compute in H3; destruct H3; order.
  Qed.

  Lemma add_1 : forall m (x y : key) e, x === y -> MapsTo y e (add x e m).
  Proof.
    intros m x y e; generalize y; clear y.
    unfold K.MapsTo.
    functional induction (add x e m); simpl.
    constructor; split; auto.
    constructor; split; auto.
    constructor; split; auto.
    destruct (compare_dec x k'); try discriminate; intuition.
  Qed.

  Lemma add_2 : forall m (x y : key) e e',
    x =/= y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
    intros m x  y e e'.
    generalize y e; clear y e; unfold K.MapsTo.
    functional induction (add x e' m); simpl; auto;
      destruct (compare_dec x k'); try discriminate; clear e0.

    intros y' e'' eqky'; inversion_clear 1; destruct H1; simpl in *.
    order.
    auto.
    auto.
    intros y' e'' eqky'; inversion_clear 1; intuition.
  Qed.

  Lemma add_3 : forall m (x y : key) e e',
    x =/= y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
    intros m x y e e'. generalize y e; clear y e; unfold K.MapsTo.
    functional induction (add x e' m); simpl; intros.
    apply (In_inv_3 H0); compute; auto.
    apply (In_inv_3 H0); compute; auto.
    constructor 2; apply (In_inv_3 H0); compute; auto.
    inversion_clear H0; auto.
  Qed.

  Lemma add_Inf : forall m(x x':key)(e e':elt),
    Inf (x',e') m -> ltk (x',e') (x,e) -> Inf (x',e') (add x e m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x'',e'').
    inversion_clear H.
    compute in H0,H1.
    simpl; destruct (compare_dec x x''); intuition.
  Qed.
  Hint Resolve add_Inf.

  Lemma add_sorted : forall m (Hm:Sort m) x e, Sort (add x e m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x',e').
    simpl; destruct (compare_dec x x'); intuition; inversion_clear Hm; auto.
    constructor; auto.
    apply Inf_eq with (x',e'); auto.
  Qed.

  Lemma remove_1 : forall m (Hm:Sort m) x y, x === y -> ~ In y (remove x m).
  Proof.
    intros m Hm x y; generalize Hm; clear Hm.
    functional induction (remove x m); simpl; intros; subst;
      try (destruct (compare_dec x k'); try discriminate).

    red; inversion 1; inversion H1.

    apply Sort_Inf_NotIn with x0; auto.
    clear e0; constructor; compute; order.

    clear e0;inversion_clear Hm.
    apply Sort_Inf_NotIn with x0; auto.
    apply Inf_eq with (k',x0);auto; unfold K.eqk; transitivity x; auto.

    clear e0;inversion_clear Hm.
    assert (notin:~ In y (remove x l)) by auto.
    intros (x1,abs).
    inversion_clear abs.
    unfold K.eqk in H3; destruct H3; order.
    simpl in LT; order.
    apply notin; exists x1; auto.
  Qed.

  Lemma remove_2 : forall m (Hm:Sort m) x y e,
    x =/= y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
    intros m Hm x y e; generalize Hm; clear Hm; unfold K.MapsTo.
    functional induction (remove x m);subst;auto;
      match goal with
        | [H: compare ?x ?y = _ |- _ ] =>
          destruct (compare_dec x y); try discriminate; clear H
        | _ => idtac
      end.

    inversion_clear 3; auto.
    compute in H2; destruct H2; order.

    inversion_clear 1; inversion_clear 2; auto.
  Qed.

  Lemma remove_3 : forall m (Hm:Sort m) x y e,
    MapsTo y e (remove x m) -> MapsTo y e m.
  Proof.
    intros m Hm x y e; generalize Hm; clear Hm; unfold K.MapsTo.
    functional induction (remove x m);subst;auto.
    inversion_clear 1; inversion_clear 1; auto.
  Qed.

  Lemma remove_Inf : forall m(Hm : Sort m)(x x':key)(e':elt),
    Inf (x',e') m -> Inf (x',e') (remove x m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x'',e'').
    inversion_clear H.
    compute in H0.
    simpl; destruct (compare_dec x x''); intuition.
    inversion_clear Hm.
    apply Inf_lt with (x'',e''); auto.
  Qed.
  Hint Resolve remove_Inf.

  Lemma remove_sorted : forall m (Hm:Sort m) x, Sort (remove x m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x',e').
    simpl; destruct (compare_dec x x'); intuition; inversion_clear Hm; auto.
  Qed.

  (** Extra insertion w/ combine functions *)
  Lemma insert_1 : forall m (Hm:Sort m) (x y : key) e d f,
    x === y -> MapsTo y e m -> MapsTo y (f e) (insert x d f m).
  Proof.
    intros m Hm x y e; generalize y; clear y.
    unfold K.MapsTo.
    functional induction (add x e m); simpl;
      try (intros; destruct (compare_dec x k'); try discriminate; clear e1).
    intros; inversion H0.
    inversion H0; subst.
    destruct H3; simpl in *; order.
    inversion Hm; subst.
    assert (HH  : k' <<< y0) by (exact (Sort_In_cons_1 Hm (InA_eqke_eqk H3))).
    order.
    inversion H0; subst.
    destruct H3; simpl in *; subst; constructor; split; auto.
    assert (HH  : k' <<< y0) by (exact (Sort_In_cons_1 Hm (InA_eqke_eqk H3))).
    order.
    inversion H0; subst.
    destruct H3; simpl in *; order.
    inversion Hm; auto.
  Qed.

  Lemma insert_2 : forall m (Hm:Sort m) (x y : key) d f,
    x === y -> ~ In y m -> MapsTo y d (insert x d f m).
  Proof.
    intros m Hm x y d f; generalize y; clear y.
    unfold K.MapsTo.
    functional induction (insert x d f m); simpl;
      try (intros; destruct (compare_dec x k'); try discriminate; clear e0).
    constructor; split; auto.
    constructor; split; auto.
    intros; contradiction H0; exists y; constructor; split; auto; simpl; order.
    inversion Hm; subst; constructor 2; apply IHd0; auto.
    intros [e He]; apply H0; exists e; right; auto.
  Qed.

  Lemma insert_3 : forall m (x y : key) e d f,
    x =/= y -> MapsTo y e m -> MapsTo y e (insert x d f m).
  Proof.
    intros m x y e d f.
    generalize y e; clear y e; unfold K.MapsTo.
    functional induction (insert x d f m); simpl; auto;
      destruct (compare_dec x k'); try discriminate; clear e0.

    intros y' e'' eqky'; inversion_clear 1; destruct H1; simpl in *.
    order.
    auto.
    auto.
    intros y' e'' eqky'; inversion_clear 1; intuition.
  Qed.

  Lemma insert_4 : forall m (x y : key) e d f,
    x =/= y -> MapsTo y e (insert x d f m) -> MapsTo y e m.
  Proof.
    intros m x y e d f. generalize y e; clear y e; unfold K.MapsTo.
    functional induction (insert x d f m); simpl; intros.
    apply (In_inv_3 H0); compute; auto.
    apply (In_inv_3 H0); compute; auto.
    constructor 2; apply (In_inv_3 H0); compute; auto.
    inversion_clear H0; auto.
  Qed.

  Lemma insert_Inf : forall m(x x':key) d f (e e':elt),
    Inf (x',e') m -> ltk (x',e') (x,e) -> Inf (x',e') (insert x d f m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x'',e'').
    inversion_clear H.
    compute in H0,H1.
    simpl; destruct (compare_dec x x''); intuition.
  Qed.
  Hint Resolve insert_Inf.

  Lemma insert_sorted : forall m (Hm:Sort m) x d f, Sort (insert x d f m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x',e').
    simpl; destruct (compare_dec x x'); intuition; inversion_clear Hm; auto.
    constructor; auto.
    apply Inf_eq with (x',e'); auto.
    constructor; auto.
    apply insert_Inf with d; auto.
  Qed.

  Lemma adjust_1 : forall m (Hm:Sort m) (x y : key) e f,
    x === y -> MapsTo y e m -> MapsTo y (f e) (adjust x f m).
  Proof.
    intros m Hm x y e; generalize y; clear y.
    unfold K.MapsTo.
    functional induction (add x e m); simpl;
      try (intros; destruct (compare_dec x k'); try discriminate; clear e1).
    intros; inversion H0.
    inversion H0; subst.
    destruct H3; simpl in *; order.
    inversion Hm; subst.
    assert (HH  : k' <<< y0) by (exact (Sort_In_cons_1 Hm (InA_eqke_eqk H3))).
    order.
    inversion H0; subst.
    destruct H3; simpl in *; subst; constructor; split; auto.
    assert (HH  : k' <<< y0) by (exact (Sort_In_cons_1 Hm (InA_eqke_eqk H3))).
    order.
    inversion H0; subst.
    destruct H3; simpl in *; order.
    inversion Hm; auto.
  Qed.

  Lemma adjust_2 : forall m (x y : key) e f,
    x =/= y -> MapsTo y e m -> MapsTo y e (adjust x f m).
  Proof.
    intros m x y e f.
    generalize y e; clear y e; unfold K.MapsTo.
    functional induction (adjust x f m); simpl; auto;
      destruct (compare_dec x k'); try discriminate; clear e0.

    intros y' e'' eqky'; inversion_clear 1; destruct H1; simpl in *.
    order.
    auto.
    auto.
    intros y' e'' eqky'; inversion_clear 1; intuition.
  Qed.

  Lemma adjust_3 : forall m (x y : key) e f,
    x =/= y -> MapsTo y e (adjust x f m) -> MapsTo y e m.
  Proof.
    intros m x y e f. generalize y e; clear y e; unfold K.MapsTo.
    functional induction (adjust x f m); simpl; intros; auto.
    constructor 2; apply (In_inv_3 H0); compute; auto.
    inversion_clear H0; auto.
  Qed.

  Lemma adjust_Inf : forall m(x x':key) f (e e':elt),
    Inf (x',e') m -> ltk (x',e') (x,e) -> Inf (x',e') (adjust x f m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x'',e'').
    inversion_clear H.
    compute in H0,H1.
    simpl; destruct (compare_dec x x''); intuition.
  Qed.
  Hint Resolve adjust_Inf.

  Lemma adjust_sorted : forall m (Hm:Sort m) x f, Sort (adjust x f m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x',e').
    simpl; destruct (compare_dec x x'); intuition; inversion_clear Hm; auto.
    constructor; auto.
    apply Inf_eq with (x',e'); auto.
    constructor; auto.
    apply adjust_Inf with e'; auto.
  Qed.

  Lemma elements_1 : forall m x e,
    MapsTo x e m -> InA eqke (x,e) (elements m).
  Proof.
    auto.
  Qed.

  Lemma elements_2 : forall m x e,
    InA eqke (x,e) (elements m) -> MapsTo x e m.
  Proof.
    auto.
  Qed.

  Lemma elements_3 : forall m (Hm:Sort m), sort ltk (elements m).
  Proof.
    auto.
  Qed.

  Lemma elements_3w : forall m (Hm:Sort m), NoDupA eqk (elements m).
  Proof.
    intros.
    apply Sort_NoDupA.
    apply elements_3; auto.
  Qed.

  Lemma fold_1 : forall m (A:Type)(i:A)(f:key->elt->A->A),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof.
    intros; functional induction (fold f m i); auto.
  Qed.

  Definition Equivb cmp m m' :=
    (forall k, In k m <-> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

  Lemma equal_1 : forall m (Hm:Sort m) m' (Hm': Sort m') cmp,
    Equivb cmp m m' -> equal cmp m m' = true.
  Proof.
    intros m Hm m' Hm' cmp; generalize Hm Hm'; clear Hm Hm'.
    functional induction (equal cmp m m'); simpl; subst; auto; unfold Equivb;
      intuition; subst.

    destruct (compare_dec x x') as [Hcomp|Hcomp|Hcomp];
      try discriminate; clear e2.
    apply IHb; auto.
    inversion_clear Hm; auto.
    inversion_clear Hm'; auto.
    unfold Equivb; intuition.
    destruct (H0 k).
    assert (In k ((x,e) ::l)).
    destruct H as (e'', hyp); exists e''; constructor 2; auto.
    destruct (In_inv (H2 H4)); auto.
    inversion_clear Hm.
    elim (Sort_Inf_NotIn H6 H7).
    destruct H as (e'', hyp); exists e''; auto.
    apply MapsTo_eq with k; auto; order.
    destruct (H0 k).
    assert (In k ((x',e') ::l')).
    destruct H as (e'', hyp); exists e''; constructor 2; auto.
    destruct (In_inv (H3 H4)); auto.
    inversion_clear Hm'.
    elim (Sort_Inf_NotIn H6 H7).
    destruct H as (e'', hyp); exists e''; auto.
    apply MapsTo_eq with k; auto; order.
    apply H1 with k; constructor 2; auto.

    destruct (compare_dec x x') as [Hcomp|Hcomp|Hcomp];
      try discriminate; clear e2.
    destruct (H0 x).
    assert (In x ((x',e')::l')).
    apply H; auto.
    exists e; constructor 1; split; auto.
    destruct (In_inv H3).
    rewrite <- e3, <- (H1 x e e'); auto; constructor 1; split; auto.
    inversion_clear Hm'.
    assert (Inf (x,e) l').
    apply Inf_eq with (x',e'); auto.
    elim (Sort_Inf_NotIn H5 H7 H4).

    destruct (compare_dec x x') as [Hcomp|Hcomp|Hcomp];
      try contradiction; clear y.
    destruct (H0 x).
    assert (In x ((x',e')::l')).
    apply H; auto.
    exists e; constructor 1; split; auto.
    destruct (In_inv H3).
    order.
    inversion_clear Hm'.
    assert (Inf (x,e) l').
    apply Inf_lt with (x',e'); auto.
    elim (Sort_Inf_NotIn H5 H7 H4).

    destruct (H0 x').
    assert (In x' ((x,e)::l)).
    apply H2; auto.
    exists e'; constructor 1; split; auto.
    destruct (In_inv H3).
    order.
    inversion_clear Hm.
    assert (Inf (x',e') l).
    apply Inf_lt with (x,e); auto.
    elim (Sort_Inf_NotIn H5 H7 H4).

    destruct m;
      destruct m';try contradiction.

    clear H1;destruct p as (k,e).
    destruct (H0 k).
    destruct H1.
    exists e; constructor; split; auto.
    inversion H1.

    destruct p as (x,e).
    destruct (H0 x).
    destruct H.
    exists e; constructor; split; auto.
    inversion H.

    destruct p;destruct p0;contradiction.
  Qed.


  Lemma equal_2 : forall m (Hm:Sort m) m' (Hm:Sort m') cmp,
    equal cmp m m' = true -> Equivb cmp m m'.
  Proof.
    intros m Hm m' Hm' cmp; generalize Hm Hm'; clear Hm Hm'.
    functional induction (equal cmp m m'); simpl; subst;auto; unfold Equivb;
      intuition; try discriminate; subst;
        try match goal with H: compare ?x ?y = _ |- _ =>
              destruct (compare_dec x y); try discriminate; clear H
            end.

    inversion H0.

    inversion_clear Hm;inversion_clear Hm'.
    destruct (IHb H2 H4 H).
    destruct (In_inv H0).
    exists e'; constructor; split; trivial; transitivity x; auto.
    destruct (H6 k).
    destruct (H9 H8) as (e'',hyp).
    exists e''; constructor 2; auto.

    inversion_clear Hm;inversion_clear Hm'.
    destruct (IHb H2 H4 H).
    destruct (In_inv H0).
    exists e; constructor; split; trivial; transitivity x'; auto.
    destruct (H6 k).
    destruct (H10 H8) as (e'',hyp).
    exists e''; constructor 2; auto.

    inversion_clear Hm;inversion_clear Hm'.
    destruct (IHb H3 H5 H).
    inversion_clear H0.
    destruct H9; simpl in *; subst.
    inversion_clear H1.
    destruct H9; simpl in *; subst; auto.
    elim (Sort_Inf_NotIn H5 H6).
    exists e'0; apply MapsTo_eq with k; auto; order.
    inversion_clear H1.
    destruct H0; simpl in *; subst; auto.
    elim (Sort_Inf_NotIn H3 H4).
    exists e0; apply MapsTo_eq with k; auto; order.
    apply H8 with k; auto.
  Qed.

  (** This lemma isn't part of the spec of [Equivb],
     but is used in [FMapAVL] *)
  Lemma equal_cons : forall cmp l1 l2 x y, Sort (x::l1) -> Sort (y::l2) ->
    eqk x y -> cmp (snd x) (snd y) = true ->
    (Equivb cmp l1 l2 <-> Equivb cmp (x :: l1) (y :: l2)).
  Proof.
    intros.
    inversion H; subst.
    inversion H0; subst.
    destruct x; destruct y; compute in H1, H2.
    split; intros.
    apply equal_2; auto.
    simpl.
    destruct (compare_dec k k0); try solve [order].
    rewrite H2; simpl.
    apply equal_1; auto.
    apply equal_2; auto.
    generalize (equal_1 H H0 H3).
    simpl.
    destruct (compare_dec k k0); try solve [order].
    rewrite H2; simpl; auto.
  Qed.

End MapSpecs.

Section MapSpecs2.
  Variable key : Type.
  Context `{key_OT : OrderedType key}.
  Variables elt elt' : Type.

  Let t elt := dict key elt.

  (** Specification of [map] *)
  Lemma map_1 : forall (m:t elt)(x:key)(e:elt)(f:elt->elt'),
    MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof.
    intros m x e f.
    (* functional induction map elt elt' f m.  *) (* Marche pas ??? *)
    induction m.
    inversion 1.

    destruct a as (x',e').
    simpl.
    inversion_clear 1.
    constructor 1.
    unfold eqke in *; simpl in *; intuition; subst; auto.
    constructor 2.
    unfold MapsTo in *; auto.
  Qed.

  Lemma map_2 : forall (m:t elt)(x:key)(f:elt->elt'),
    In x (map f m) -> In x m.
  Proof.
    intros m x f.
    (* functional induction map elt elt' f m. *) (* Marche pas ??? *)
    induction m; simpl.
    intros (e,abs).
    inversion abs.

    destruct a as (x',e).
    intros hyp.
    inversion hyp. clear hyp.
    inversion H; subst; rename x0 into e'.
    exists e; constructor.
    unfold eqke in *; simpl in *; intuition.
    destruct IHm as (e'',hyp).
    exists e'; auto.
    exists e''.
    constructor 2; auto.
  Qed.

  Lemma map_lelistA : forall (m: t elt)(x:key)(e:elt)(e':elt')(f:elt->elt'),
    lelistA (ltk (elt:=elt)) (x,e) m ->
    lelistA (ltk (elt:=elt')) (x,e') (map f m).
  Proof.
    induction m; simpl; auto.
    intros.
    destruct a as (x0,e0).
    inversion_clear H; auto.
  Qed.

  Hint Resolve map_lelistA.

  Lemma map_sorted : forall (m: t elt)
    (Hm : sort (ltk (elt:=elt)) m)(f:elt -> elt'),
    sort (ltk (elt:=elt')) (map f m).
  Proof.
    induction m; simpl; auto.
    intros.
    destruct a as (x',e').
    inversion_clear Hm.
    constructor; auto.
    exact (map_lelistA _ _ H0).
  Qed.

  (** Specification of [mapi] *)

  Lemma mapi_1 : forall (m:t elt)(x:key)(e:elt)(f:key->elt->elt'),
    MapsTo x e m ->
    exists y, y === x /\ MapsTo x (f y e) (mapi f m).
  Proof.
    intros m x e f.
    (* functional induction mapi elt elt' f m. *) (* Marche pas ??? *)
    induction m.
    inversion 1.

    destruct a as (x',e').
    simpl.
    inversion_clear 1.
    exists x'.
    destruct H0; simpl in *.
    split; auto.
    constructor 1.
    unfold eqke in *; simpl in *; intuition; subst; auto.
    destruct IHm as (y, hyp); auto.
    exists y; intuition; constructor 2; auto.
  Qed.

  Lemma mapi_2 : forall (m:t elt)(x:key)(f:key->elt->elt'),
    In x (mapi f m) -> In x m.
  Proof.
    intros m x f.
    (* functional induction mapi elt elt' f m. *) (* Marche pas ??? *)
    induction m; simpl.
    intros (e,abs).
    inversion abs.

    destruct a as (x',e).
    intros hyp.
    inversion hyp. clear hyp.
    inversion H; subst; rename x0 into e'.
    exists e; constructor.
    unfold eqke in *; simpl in *; intuition.
    destruct IHm as (e'',hyp).
    exists e'; auto.
    exists e''.
    constructor 2; auto.
  Qed.

  Lemma mapi_lelistA : forall (m: t elt)(x:key)(e:elt)(f:key->elt->elt'),
    lelistA (ltk (elt:=elt)) (x,e) m ->
    lelistA (ltk (elt:=elt')) (x,f x e) (mapi f m).
  Proof.
    induction m; simpl; auto.
    intros.
    destruct a as (x',e').
    inversion_clear H; auto.
  Qed.

  Hint Resolve mapi_lelistA.

  Lemma mapi_sorted : forall m (Hm : sort (ltk (elt:=elt)) m)
    (f: key ->elt -> elt'),
    sort (ltk (elt:=elt')) (mapi f m).
  Proof.
    induction m; simpl; auto.
    intros.
    destruct a as (x',e').
    inversion_clear Hm; auto.
  Qed.

End MapSpecs2.
Section MapSpecs3.
  Variable key : Type.
  Context `{key_OT : OrderedType key}.
  Variables elt elt' elt'' : Type.
  Variable f : option elt -> option elt' -> option elt''.

  Let t elt := dict key elt.

(** [map2] *)
  Notation oee' := (option elt * option elt')%type.
  Fixpoint combine (m : t elt) : t elt' -> t oee' :=
    match m with
      | nil => map (fun e' => (None,Some e'))
      | (k,e) :: l =>
        fix combine_aux (m':t elt') : list (key * oee') :=
        match m' with
          | nil => map (fun e => (Some e,None)) m
          | (k',e') :: l' =>
            match k =?= k' with
              | Lt => (k,(Some e, None))::combine l m'
              | Eq => (k,(Some e, Some e'))::combine l l'
              | Gt => (k',(None,Some e'))::combine_aux l'
            end
        end
    end.

  Definition fold_right_pair (A B C:Type)(f: A->B->C->C)(l:list (A*B))(i:C) :=
    List.fold_right (fun p => f (fst p) (snd p)) i l.

  Definition map2_alt m m' :=
    let m0 : t oee' := combine m m' in
      let m1 : t (option elt'') := map (fun p => f (fst p) (snd p)) m0 in
        fold_right_pair (@option_cons key elt'') m1 nil.

  Lemma map2_alt_equiv : forall m m', map2_alt m m' = map2 f m m'.
  Proof.
    unfold map2_alt.
    induction m.
    simpl; auto; intros.
    (* map2_r *)
    induction m'; try destruct a; simpl; auto.
    rewrite IHm'; auto.
    (* fin map2_r *)
    induction m'; destruct a.
    simpl.
    (* map2_l *)
    clear IHm.
    match goal with |- option_cons _ _ _ ?X = option_cons _ _ _ ?Y =>
      cut (X = Y); [intro H; rewrite H; auto |]
    end.
    induction m; try destruct a; simpl; auto.
    rewrite IHm; auto.
    (* fin map2_l *)
    destruct a0.
    simpl.
    destruct (compare_dec k k0); simpl;
      match goal with |- option_cons _ _ _ ?X = option_cons _ _ _ ?Y =>
        cut (X = Y); [intro H2; rewrite H2; auto |]
      end.
    apply IHm.
    apply IHm.
    apply IHm'.
  Qed.

  Lemma combine_lelistA :
    forall m m' (x:key)(e:elt)(e':elt')(e'':oee'),
      lelistA (ltk (elt:=elt)) (x,e) m ->
      lelistA (ltk (elt:=elt')) (x,e') m' ->
      lelistA (ltk (elt:=oee')) (x,e'') (combine m m').
  Proof.
    induction m.
    intros.
    simpl.
    exact (map_lelistA _ _ H0).
    induction m'.
    intros.
    destruct a.
    replace (combine ((k, e0) :: m) nil) with
      (map (fun e => (Some e,None (A:=elt'))) ((k,e0)::m)); auto.
    exact (map_lelistA _ _ H).
    intros.
    simpl.
    destruct a as (k,e0); destruct a0 as (k',e0').
    destruct (compare_dec k k').
    inversion_clear H; auto.
    inversion_clear H; auto.
    inversion_clear H0; auto.
  Qed.
  Hint Resolve combine_lelistA.

  Lemma combine_sorted :
    forall m (Hm : sort (ltk (elt:=elt)) m) m'
      (Hm' : sort (ltk (elt:=elt')) m'),
      sort (ltk (elt:=oee')) (combine m m').
  Proof.
    induction m.
    intros; clear Hm.
    simpl.
    apply map_sorted; auto.
    induction m'.
    intros; clear Hm'.
    destruct a.
    replace (combine ((k, e) :: m) nil) with
      (map (fun e => (Some e,None (A:=elt'))) ((k,e)::m)); auto.
    apply map_sorted; auto.
    intros.
    simpl.
    destruct a as (k,e); destruct a0 as (k',e').
    destruct (compare_dec k k').
    inversion_clear Hm.
    constructor; auto.
    assert (lelistA (ltk (elt:=elt')) (k, e') ((k',e')::m')) by auto.
    exact (combine_lelistA _ H1 H2).
    inversion_clear Hm; inversion_clear Hm'.
    constructor; auto.
    assert (lelistA (ltk (elt:=elt')) (k, e') m')
      by (apply Inf_eq with (k',e'); auto).
    exact (combine_lelistA _ H1 H4).
    inversion_clear Hm; inversion_clear Hm'.
    constructor; auto.
    change (lelistA (ltk (elt:=oee')) (k', (None, Some e'))
      (combine ((k,e)::m) m')).
    assert (lelistA (ltk (elt:=elt)) (k', e) ((k,e)::m)) by auto.
    exact (combine_lelistA _  H4 H3).
  Qed.

  Lemma map2_sorted :
    forall m (Hm : sort (ltk (elt:=elt)) m)
      m' (Hm' : sort (ltk (elt:=elt')) m'),
      sort (ltk (elt:=elt'')) (map2 f m m').
  Proof.
    intros.
    rewrite <- map2_alt_equiv.
    unfold map2_alt.
    assert (H0:=combine_sorted Hm Hm').
    set (l0:=combine m m') in *; clearbody l0.
    set (f':= fun p : oee' => f (fst p) (snd p)).
    assert (H1:=map_sorted (elt' := option elt'') H0 f').
    set (l1:=map f' l0) in *; clearbody l1.
    clear f' f H0 l0 Hm Hm' m m'.
    induction l1.
    simpl; auto.
    inversion_clear H1.
    destruct a; destruct o; auto.
    simpl.
    constructor; auto.
    clear IHl1.
    induction l1.
    simpl; auto.
    destruct a; destruct o; simpl; auto.
    inversion_clear H0; auto.
    inversion_clear H0.
    red in H1; simpl in H1.
    inversion_clear H.
    apply IHl1; auto.
    apply Inf_lt with (k0, None (A:=elt'')); auto.
  Qed.

  Definition at_least_one (o:option elt)(o':option elt') :=
    match o, o' with
      | None, None => None
      | _, _  => Some (o,o')
    end.

  Lemma combine_1 :
    forall m (Hm : sort (ltk (elt:=elt)) m)
      m' (Hm' : sort (ltk (elt:=elt')) m') (x:key),
      find x (combine m m') = at_least_one (find x m) (find x m').
  Proof.
    induction m.
    intros.
    simpl.
    induction m'.
    intros; simpl; auto.
    simpl; destruct a.
    simpl; destruct (compare_dec x k); simpl; auto.
    inversion_clear Hm'; auto.
    induction m'.
    (* m' = nil *)
    intros; destruct a; simpl.
    destruct (compare_dec x k); simpl; auto.
    inversion_clear Hm; clear Hm' IHm.
    induction m; simpl; auto.
    inversion_clear H1.
    destruct a.
    simpl; destruct (compare_dec x k0); simpl; auto.
    apply IHm. inversion H0; auto.
    inversion H0; auto; subst. apply Inf_lt with (k0, e0); auto.
    (* m' <> nil *)
    intros.
    destruct a as (k,e); destruct a0 as (k',e'); simpl.
    inversion Hm; inversion Hm'; subst.
    destruct (compare_dec k k'); simpl; destruct (compare_dec x k); simpl; auto.
    destruct (compare_dec x k'); auto; solve [false_order].
    destruct (compare_dec x k'); auto; solve [false_order].
    destruct (compare_dec x k'); simpl; auto.
    rewrite IHm; auto; simpl; rewrite (elim_compare_lt H3); auto.
    rewrite IHm; auto; simpl; rewrite (elim_compare_eq H3); auto.
    rewrite IHm; auto; simpl; rewrite (elim_compare_gt H3); auto.

    destruct (compare_dec x k'); auto; solve [false_order].
    destruct (compare_dec x k'); auto; solve [false_order].
    destruct (compare_dec x k'); auto; solve [false_order].

    destruct (compare_dec x k'); simpl; auto.
    rewrite IHm'; simpl; auto; rewrite (elim_compare_lt H0); auto.
    destruct (compare_dec x k'); auto; try solve [false_order].
    rewrite IHm'; simpl; auto; rewrite (elim_compare_eq H0); auto.
    destruct (compare_dec x k'); auto; try solve [false_order].
    rewrite IHm'; simpl; auto; rewrite (elim_compare_gt H0); auto.
  Qed.

  Definition at_least_one_then_f (o:option elt)(o':option elt') :=
    match o, o' with
      | None, None => None
      | _, _  => f o o'
    end.

  Lemma map2_0 :
    forall m (Hm : sort (ltk (elt:=elt)) m)
      m' (Hm' : sort (ltk (elt:=elt')) m') (x:key),
      find x (map2 f m m') = at_least_one_then_f (find x m) (find x m').
  Proof.
    intros.
    rewrite <- map2_alt_equiv.
    unfold map2_alt.
    assert (H:=combine_1 Hm Hm' x).
    assert (H2:=combine_sorted Hm Hm').
    set (f':= fun p : oee' => f (fst p) (snd p)).
    set (m0 := combine m m') in *; clearbody m0.
    set (o:=find x m) in *; clearbody o.
    set (o':=find x m') in *; clearbody o'.
    clear Hm Hm' m m'.
    generalize H; clear H.
    match goal with |- ?m=?n -> ?p=?q =>
      assert ((m=n->p=q)/\(m=None -> p=None)); [|intuition] end.
    induction m0; simpl in *; intuition.
    destruct o; destruct o'; simpl in *; try discriminate; auto.
    destruct a as (k,(oo,oo')); simpl in *.
    inversion_clear H2.
    destruct (compare_dec x k); simpl in *.
    (* x < k *)
    destruct (f' (oo,oo')); simpl.
    rewrite (elim_compare_lt H2).
    destruct o; destruct o'; simpl in *; try discriminate; auto.
    destruct (IHm0 H0) as (H3,_); apply H3; auto.
    rewrite <- H.
    case_eq (find x m0); intros; auto.
    assert (ltk (elt:=oee') (x,(oo,oo')) (k,(oo,oo'))).
    red; auto.
    destruct (Sort_Inf_NotIn H0 (Inf_lt H5 H1)).
    exists p; apply find_2; auto.
    (* x = k *)
    assert (at_least_one_then_f o o' = f oo oo').
    destruct o; destruct o'; simpl in *; inversion_clear H; auto.
    rewrite H3.
    unfold f'; simpl.
    destruct (f oo oo'); simpl.
    rewrite (elim_compare_eq H2); auto.
    destruct (IHm0 H0) as (_,H4); apply H4; auto.
    case_eq (find x m0); intros; auto.
    assert (eqk (elt:=oee') (k,(oo,oo')) (x,(oo,oo'))).
    red; auto.
    destruct (Sort_Inf_NotIn H0 (Inf_eq (eqk_sym H6) H1)).
    exists p; apply find_2; auto.
    (* k < x *)
    unfold f'; simpl.
    destruct (f oo oo'); simpl.
    rewrite (elim_compare_gt H2); auto.
    destruct (IHm0 H0) as (H3,_); apply H3; auto.
    destruct (IHm0 H0) as (H3,_); apply H3; auto.

    (* None -> None *)
    destruct a as (k,(oo,oo')).
    simpl.
    inversion_clear H2.
    destruct (compare_dec x k).
    (* x < k *)
    unfold f'; simpl.
    destruct (f oo oo'); simpl.
    rewrite (elim_compare_lt H2); auto.
    destruct (IHm0 H0) as (_,H4); apply H4; auto.
    case_eq (find x m0); intros; auto.
    assert (ltk (elt:=oee') (x,(oo,oo')) (k,(oo,oo'))).
    red; auto.
    destruct (Sort_Inf_NotIn H0 (Inf_lt H5 H1)).
    exists p; apply find_2; auto.
    (* x = k *)
    discriminate.
    (* k < x *)
    unfold f'; simpl.
    destruct (f oo oo'); simpl.
    rewrite (elim_compare_gt H2); auto.
    destruct (IHm0 H0) as (_,H4); apply H4; auto.
    destruct (IHm0 H0) as (_,H4); apply H4; auto.
  Qed.

  (** Specification of [map2] *)

  Lemma map2_1 :
    forall m (Hm : sort (ltk (elt:=elt)) m)
      m' (Hm' : sort (ltk (elt:=elt')) m')(x:key),
      In x m \/ In x m' ->
      find x (map2 f m m') = f (find x m) (find x m').
  Proof.
    intros.
    rewrite map2_0; auto.
    destruct H as [(e,H)|(e,H)].
    rewrite (find_1 Hm H).
    destruct (find x m'); simpl; auto.
    rewrite (find_1 Hm' H).
    destruct (find x m); simpl; auto.
  Qed.

  Lemma map2_2 :
    forall m (Hm : sort (ltk (elt:=elt)) m)
      m' (Hm' : sort (ltk (elt:=elt')) m')(x:key),
      In x (map2 f m m') -> In x m \/ In x m'.
  Proof.
    intros.
    destruct H as (e,H).
    generalize (map2_0 Hm Hm' x).
    rewrite (find_1 (map2_sorted Hm Hm') H).
    generalize (@find_2 _ _ _ m x).
    generalize (@find_2 _ _ _ m' x).
    destruct (find x m);
      destruct (find x m'); simpl; intros.
    left; exists e0; auto.
    left; exists e0; auto.
    right; exists e0; auto.
    discriminate.
  Qed.

End MapSpecs3.

End MapList.

Module M := MapList.

Structure dict (key : Type) `{OrderedType key} (elt : Type) := Build_dict {
  this :> M.dict key elt;
  sorted : sort (M.K.ltk (elt:=elt)) this
}.
Implicit Arguments this [[key] [elt] [H]].
Implicit Arguments Build_dict [[key] [elt] [H] [this]].
Implicit Arguments sorted [[key] [elt] [H]].

Section MapDefinitions.
  Variable key : Type.
  Hypothesis (comparedec : OrderedType key).
  Variables elt elt' elt'' : Type.

  Let t elt := dict key elt.

  Implicit Types m : t elt.
  Implicit Types x y : key.
  Implicit Types e : elt.

  Definition empty : t elt := Build_dict (M.empty_sorted elt).
  Definition is_empty m : bool := M.is_empty m.(this).
  Definition mem x m : bool := M.mem x m.(this).
  Definition add x e m : t elt := Build_dict (M.add_sorted m.(sorted) x e).
  Definition find x m : option elt := M.find x m.(this).
  Definition remove x m : t elt := Build_dict (M.remove_sorted m.(sorted) x).
  Definition insert x d f m : t elt :=
    Build_dict (M.insert_sorted m.(sorted) x d f).
  Definition adjust x f m : t elt :=
    Build_dict (M.adjust_sorted m.(sorted) x f).
  Definition map f m : t elt' := Build_dict (M.map_sorted m.(sorted) f).
  Definition mapi (f:key->elt->elt') m : t elt' :=
    Build_dict (M.mapi_sorted m.(sorted) f).
  Definition map2 f m (m':t elt') : t elt'' :=
    Build_dict (M.map2_sorted f m.(sorted) m'.(sorted)).
  Definition elements m : list (key*elt) := @M.elements _ _ elt m.(this).
  Definition choose m : option (key*elt) := @M.choose _ _ elt m.(this).
  Definition cardinal m := length m.(this).
  Definition fold (A:Type)(f:key->elt->A->A) m (i:A) : A :=
    @M.fold _ _ elt A f m.(this) i.
  Definition equal cmp m m' : bool := @M.equal _ _ elt cmp m.(this) m'.(this).

  Definition MapsTo x e m : Prop := M.K.MapsTo x e m.(this).
  Definition In x m : Prop := M.K.In x m.(this).
  Definition Empty m : Prop := M.Empty m.(this).

  Definition Equal m m' := forall y, find y m = find y m'.
  Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
    (forall k, In k m <-> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
  Definition Equivb cmp m m' : Prop := @M.Equivb _ _ elt cmp m.(this) m'.(this).

  Definition eq_key : (key*elt) -> (key*elt) -> Prop := @M.K.eqk _ _ elt.
  Definition eq_key_elt : (key*elt) -> (key*elt) -> Prop:= @M.K.eqke _ _ elt.
  Definition lt_key : (key*elt) -> (key*elt) -> Prop := @M.K.ltk _ _ elt.

  (** Specs *)
  Lemma MapsTo_1 : forall m x y e, x === y -> MapsTo x e m -> MapsTo y e m.
  Proof. intros m; exact (@M.K.MapsTo_eq _ _ elt m.(this)). Qed.

  Lemma mem_1 : forall m x, In x m -> mem x m = true.
  Proof. intros m; exact (@M.mem_1 _ _ elt m.(this) m.(sorted)). Qed.
  Lemma mem_2 : forall m x, mem x m = true -> In x m.
  Proof. intros m; exact (@M.mem_2 _ _ elt m.(this) m.(sorted)). Qed.

  Lemma empty_1 : Empty empty.
  Proof. exact (@M.empty_1 _ _ elt). Qed.

  Lemma is_empty_1 : forall m, Empty m -> is_empty m = true.
  Proof. intros m; exact (@M.is_empty_1 _ _ elt m.(this)). Qed.
  Lemma is_empty_2 :  forall m, is_empty m = true -> Empty m.
  Proof. intros m; exact (@M.is_empty_2 _ _ elt m.(this)). Qed.

  Lemma add_1 : forall m x y e, x === y -> MapsTo y e (add x e m).
  Proof. intros m; exact (@M.add_1 _ _ elt m.(this)). Qed.
  Lemma add_2 : forall m x y e e',
    x =/= y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof. intros m; exact (@M.add_2 _ _ elt m.(this)). Qed.
  Lemma add_3 : forall m x y e e',
    x =/= y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof. intros m; exact (@M.add_3 _ _ elt m.(this)). Qed.

  Lemma remove_1 : forall m x y, x === y -> ~ In y (remove x m).
  Proof. intros m; exact (@M.remove_1 _ _ elt m.(this) m.(sorted)). Qed.
  Lemma remove_2 : forall m x y e,
    x =/= y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof. intros m; exact (@M.remove_2 _ _ elt m.(this) m.(sorted)). Qed.
  Lemma remove_3 : forall m x y e, MapsTo y e (remove x m) -> MapsTo y e m.
  Proof. intros m; exact (@M.remove_3 _ _ elt m.(this) m.(sorted)). Qed.

  Lemma find_1 : forall m x e, MapsTo x e m -> find x m = Some e.
  Proof. intros m; exact (@M.find_1 _ _ elt m.(this) m.(sorted)). Qed.
  Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
  Proof. intros m; exact (@M.find_2 _ _ elt m.(this)). Qed.

  Lemma insert_1 : forall m x y e d f,
    x === y -> MapsTo y e m -> MapsTo y (f e) (insert x d f m).
  Proof. intros m; exact (M.insert_1 m.(sorted)). Qed.
  Lemma insert_2 : forall m x y d f,
    x === y -> ~ In y m -> MapsTo y d (insert x d f m).
  Proof. intros m; exact (M.insert_2 m.(sorted)). Qed.
  Lemma insert_3 : forall m x y e d f,
    x =/= y -> MapsTo y e m -> MapsTo y e (insert x d f m).
  Proof. intros m; exact (@M.insert_3 _ _ elt m.(this)). Qed.
  Lemma insert_4 : forall m x y e d f,
    x =/= y -> MapsTo y e (insert x d f m) -> MapsTo y e m.
  Proof. intros m; exact (@M.insert_4 _ _ elt m.(this)). Qed.

  Lemma adjust_1 : forall m x y e f,
    x === y -> MapsTo y e m -> MapsTo y (f e) (adjust x f m).
  Proof. intros m; exact (M.adjust_1 m.(sorted)). Qed.
  Lemma adjust_2 : forall m x y e f,
    x =/= y -> MapsTo y e m -> MapsTo y e (adjust x f m).
  Proof. intros m; exact (@M.adjust_2 _ _ elt m.(this)). Qed.
  Lemma adjust_3 : forall m x y e f,
    x =/= y -> MapsTo y e (adjust x f m) -> MapsTo y e m.
  Proof. intros m; exact (@M.adjust_3 _ _ elt m.(this)). Qed.

  Lemma elements_1 : forall m x e,
    MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
  Proof. intros m; exact (@M.elements_1 _ _ elt m.(this)). Qed.
  Lemma elements_2 : forall m x e,
    InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
  Proof. intros m; exact (@M.elements_2 _ _ elt m.(this)). Qed.
  Lemma elements_3 : forall m, sort lt_key (elements m).
  Proof. intros m; exact (@M.elements_3 _ _ elt m.(this) m.(sorted)). Qed.
  Lemma elements_3w : forall m, NoDupA eq_key (elements m).
  Proof. intros m; exact (@M.elements_3w _ _ elt m.(this) m.(sorted)). Qed.

  Lemma cardinal_1 : forall m, cardinal m = length (elements m).
  Proof. intros; reflexivity. Qed.

  Lemma fold_1 : forall m (A : Type) (i : A) (f : key -> elt -> A -> A),
    fold A f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof. intros m; exact (@M.fold_1 _ _ elt m.(this)). Qed.

  Lemma equal_1 : forall m m' cmp, Equivb cmp m m' -> equal cmp m m' = true.
  Proof.
    intros m m';
      exact (@M.equal_1 _ _ elt m.(this) m.(sorted) m'.(this) m'.(sorted)).
  Qed.
  Lemma equal_2 : forall m m' cmp, equal cmp m m' = true -> Equivb cmp m m'.
  Proof.
    intros m m';
      exact (@M.equal_2 _ _ elt m.(this) m.(sorted) m'.(this) m'.(sorted)).
  Qed.

End MapDefinitions.
Section MoreDefinitions.
  Variable key : Type.
  Hypothesis (comparedec : OrderedType key).

  Let t elt := dict key elt.
  Implicit Types x y : key.

  Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
    MapsTo _ _ _ x e m -> MapsTo _ _ _ x (f e) (map _ _ _ _ f m).
  Proof. intros elt elt' m; exact (@M.map_1 _ _ elt elt' m.(this)). Qed.
  Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
    In _ _ _ x (map _ _ _ _ f m) -> In _ _ _ x m.
  Proof. intros elt elt' m; exact (@M.map_2 _ _ elt elt' m.(this)). Qed.

  Lemma mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
    (f:key->elt->elt'), MapsTo _ _ _ x e m ->
    exists y, y === x /\ MapsTo _ _ _ x (f y e) (mapi _ _ _ _ f m).
  Proof. intros elt elt' m; exact (@M.mapi_1 _ _ elt elt' m.(this)). Qed.
  Lemma mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
    (f:key->elt->elt'), In _ _ _ x (mapi _ _ _ _ f m) -> In _ _ _ x m.
  Proof. intros elt elt' m; exact (@M.mapi_2 _ _ elt elt' m.(this)). Qed.

  Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''),
    In _ _ _ x m \/ In _ _ _ x m' ->
    find _ _ _ x (map2 _ _ _ _ _ f m m') = f (find _ _ _ x m) (find _ _ _ x m').
  Proof.
    intros elt elt' elt'' m m' x f;
      exact (@M.map2_1 _ _ elt elt' elt''
        f m.(this) m.(sorted) m'.(this) m'.(sorted) x).
  Qed.
  Lemma map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
    (x:key)(f:option elt->option elt'->option elt''),
    In _ _ _ x (map2 _ _ _ _ _ f m m') -> In _ _ _ x m \/ In _ _ _ x m'.
  Proof.
    intros elt elt' elt'' m m' x f;
      exact (@M.map2_2 _ _ elt elt' elt''
        f m.(this) m.(sorted) m'.(this) m'.(sorted) x).
  Qed.
End MoreDefinitions.

Import OrderedTypeEx.
(** A dictionary [key, elt] can be seen as an OrderedType if the type of elements
   is also an OrderedType (only the fact that [key] is an OrderedType is required
   to build the dictionary). In that case, the equality is standard pointwise
   equality on the lists (since they are sorted, it amounts to saying that two
   maps are equal iff equal keys map to equal data). *)

Definition map_eq `{OrderedType A, OrderedType B} : relation (dict A B) :=
  fun x y => @list_eq (A*B) (prod_eq _eq _eq) x.(this) y.(this).
Program Instance map_eq_Equivalence `{OrderedType A, OrderedType B} :
  Equivalence (@map_eq A _ B _).
Next Obligation.
  intro x; destruct x; unfold map_eq; simpl; reflexivity.
Qed.
Next Obligation.
  intros x y; destruct x; destruct y; unfold map_eq; simpl; symmetry; auto.
Qed.
Next Obligation.
  intros x y z; destruct x; destruct y; destruct z;
    unfold map_eq; simpl; transitivity this1; auto.
Qed.

Definition map_lt `{OrderedType A, OrderedType B} : relation (dict A B) :=
  fun x y => @list_lt (A*B)
    (prod_lt _eq _lt _lt) (prod_eq _eq _eq) x.(this) y.(this).
Program Instance map_lt_StrictOrder `{OA:OrderedType A, OB: OrderedType B} :
  StrictOrder (@map_lt A _ B _) (@map_eq A _ B _).
Next Obligation.
  intros x y z; destruct x; destruct y; destruct z; unfold map_lt; simpl.
  destruct (@list_StrictOrder (A*B) (prod_OrderedType _ _)).
  exact (@StrictOrder_Transitive this0 this1 this2).
Qed.
Next Obligation.
  destruct x; destruct y; unfold map_lt, map_eq in *; simpl in *.
  destruct (@list_StrictOrder (A*B) (prod_OrderedType _ _)).
  exact (@StrictOrder_Irreflexive this0 this1 H).
Qed.

(** The inferred equality [map_eq] corresponds to pointwise equality *)
Theorem map_eq_iff `{HA : OrderedType A, HB : OrderedType B} :
  forall m m', map_eq m m' <->
    MapInterface.Equal_kw
    (fun k v m => exists v', v === v' /\ MapsTo A _ B k v' m) m m'.
Proof.
  intros [m wfm] [m' wf'm].
  assert (cutsort : forall l (x a : A * B), sort KeyOrderedType.ltk l ->
    lelistA KeyOrderedType.ltk a l -> InA KeyOrderedType.eqke x l ->
    KeyOrderedType.ltk a x).
  apply SortA_InfA_InA; try solve [intuition].
  apply KeyOrderedType.eqke_Equiv.
  constructor; repeat intro; unfold KeyOrderedType.ltk in *; order.
  intros x x' [Hx Hx'] y y' [Hy Hy']; red; simpl in *; intros; subst.
  unfold KeyOrderedType.ltk; rewrite Hx, Hy; tauto.

  unfold map_eq, MapInterface.Equal_kw,
    MapsTo, KeyOrderedType.MapsTo; simpl.
  revert m' wf'm; induction m; intros; destruct m'.
  split; intro. intros; reflexivity. constructor.
  split; intro. inversion H.
  destruct p as [k' v']; assert (H' := H k' v'); clear H; simpl in H'.
  destruct (proj2 H') as [? [_ abs]]; [|inversion abs].
  exists v'; split; [reflexivity | left; auto].
  (* -> *)
  split; intro. inversion H.
  destruct a as [k' v']; assert (H' := H k' v'); clear H; simpl in H'.
  destruct (proj1 H') as [? [_ abs]]; [|inversion abs].
  exists v'; split; [reflexivity | left; auto].
  inversion_clear wfm; inversion_clear wf'm.
  split; intro.
  inversion H3; subst; clear H3.
  destruct a as [k v]; intros k' v'.
  inversion H7; subst; clear H7.
  rewrite (IHm H _ H1) in H9; clear IHm H H1.
  split; intros [v'' [Hv'' HIn]].
  inversion HIn; subst; clear HIn.
  inversion_clear H1; simpl in *; subst; exists d; split; auto.
  transitivity v; assumption.
  left; constructor; auto. transitivity k; assumption.
  destruct (proj1 (H9 k' v'')); [exists v''; split; auto|].
  exists x; split; intuition. transitivity v''; assumption.
  inversion HIn; subst; clear HIn.
  inversion_clear H1; simpl in *; subst; exists v; split; auto.
  transitivity d; auto.
  left; constructor; auto. transitivity c; auto.
  destruct (proj2 (H9 k' v'')); [exists v''; split; auto|].
  exists x; split; intuition. transitivity v''; auto.
  (* <- *)
  destruct a as [k v]; destruct p as [a b].
  assert (Hcut : k === a /\ v === b).
  destruct (proj1 (H3 k v)) as [k'' [Heq'' Hin'']]; [exists v; split; auto|].
  inversion Hin''; subst; clear Hin''.
  inversion_clear H5; simpl in *; subst. constructor; auto.
  destruct (proj2 (H3 a b)) as [a' [Heq' Hin']]; [exists b; split; auto|].
  inversion Hin'; subst; clear Hin'.
  inversion_clear H6; simpl in *; subst; constructor; auto.
  assert (R := cutsort _ _ _ H H0 H6).
  assert (R' := cutsort _ _ _ H1 H2 H5).
  compute in R, R'. contradiction (lt_not_gt R R').

  constructor.
  constructor; destruct Hcut; auto.
  rewrite IHm by assumption.
  intros g h; split; intros [h' [Hh' Hinh']].
  destruct (proj1 (H3 g h')) as [h'' [Hh'' Hinh'']]; [exists h'; split; auto|].
  inversion Hinh''; auto; subst.
  2:(exists h''; split; [transitivity h'; assumption | auto]).
  inversion_clear H5; simpl in *; subst.
  assert (R := cutsort _ _ _ H H0 Hinh').
  compute in R; rewrite H4 in R; contradiction (lt_not_eq R (proj1 Hcut)).
  destruct (proj2 (H3 g h')) as [h'' [Hh'' Hinh'']]; [exists h'; split; auto|].
  inversion Hinh''; auto; subst.
  2:(exists h''; split; [transitivity h'; assumption | auto]).
  inversion_clear H5; simpl in *; subst.
  assert (R := cutsort _ _ _ H1 H2 Hinh').
  compute in R; rewrite H4 in R; contradiction (lt_not_eq R).
  symmetry; exact (proj1 Hcut).
Qed.

Definition map_cmp `{OrderedType A, OrderedType B} :=
  fun x y => @list_compare (A*B) (prod_OrderedType _ _) x.(this) y.(this).
Lemma map_cmp_spec `{OrderedType A, OrderedType B} :
  forall (x y : dict A B), compare_spec map_eq map_lt x y (map_cmp x y).
Proof.
  destruct x; destruct y; unfold map_cmp; simpl.
  set (C := @list_OrderedType (A*B) (prod_OrderedType _ _)).
  change (compare_spec map_eq map_lt
    (Build_dict sorted0) (Build_dict sorted1)
    (@compare (M.dict A B) C this0 this1)).
  destruct (compare_dec this0 this1); constructor; auto.
Qed.

Program Instance map_OrderedType `{OrderedType A, OrderedType B}
  : OrderedType (dict A B) := {
    _eq := @map_eq A _ B _;
    _lt := @map_lt A _ B _;
    _cmp := @map_cmp A _ B _;
    OT_Equivalence := map_eq_Equivalence;
    OT_StrictOrder := map_lt_StrictOrder
}.
Next Obligation.
  destruct x; destruct y; unfold map_cmp; simpl.
  set (C := @list_OrderedType (A*B) (prod_OrderedType _ _)).
  change (compare_spec map_eq map_lt
    (Build_dict sorted0) (Build_dict sorted1)
    (@compare (M.dict A B) C this0 this1)).
  destruct (compare_dec this0 this1); constructor; auto.
Qed.

Program Instance map_SpecificOrderedType `{OrderedType A, OrderedType B}
  : SpecificOrderedType _ (MapInterface.Equal_kw
    (fun k v m => exists v', v === v' /\ MapsTo A _ B k v' m)) := {
    SOT_Equivalence := MapInterface.Equal_kw_Equivalence _;
    SOT_lt := @map_lt A H B H0;
    SOT_cmp := @map_cmp A H B H0
  }.
Next Obligation.
  destruct (map_lt_StrictOrder (A:=A)).
  constructor.
  exact StrictOrder_Transitive.
  repeat intro; refine (StrictOrder_Irreflexive x y H1 _).
  change (map_eq x y). rewrite map_eq_iff. exact H2.
Qed.
Next Obligation.
  destruct (map_cmp_spec (B:=B) x y); constructor; auto.
  rewrite <- map_eq_iff; assumption.
Qed.