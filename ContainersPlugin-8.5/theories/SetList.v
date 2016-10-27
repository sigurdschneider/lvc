Require Import OrderedTypeEx.
Require Import SetoidList.
Require Import Morphisms Program.Basics.

Generalizable All Variables.

(** This file corresponds to [FSetList.v] in the standard library
   and implements finite sets as ordered lists. The corresponding
   [FSet] and [FSetSpecs] instances are defined in
   the file [SetListInstance.v].
   *)

Module SetList.
  (** The type of sets of elements of type [A] is a list.
     It will be without duplicates, and ordered with respect
     to the comparison inferred by the typeclasses mechanism. *)
  Definition set (A : Type) `{OrderedType A} := list A.

  Section SetDefinitions.
    Variable elt : Type.
    Hypothesis (comparedec : OrderedType elt).

    Let t := (set elt).

    Definition empty : t := nil.
    Definition is_empty (s : t) : bool := if s then true else false.

    Fixpoint mem (x : elt) (s : t) {struct s} : bool :=
      match s with
        | nil => false
        | y :: l =>
          match x =?= y with
            | Lt => false
            | Eq => true
            | Gt => mem x l
          end
      end.

    Fixpoint add (x : elt) (s : t) {struct s} : t :=
      match s with
        | nil => x :: nil
        | y :: l =>
          match x =?= y with
            | Lt => x :: s
            | Eq => s
            | Gt => y :: add x l
          end
      end.

    Definition singleton (x : elt) : t := x :: nil.

    Fixpoint remove (x : elt) (s : t) {struct s} : t :=
      match s with
        | nil => nil
        | y :: l =>
          match x =?= y with
            | Lt => s
            | Eq => l
            | Gt => y :: remove x l
          end
      end.

    Fixpoint union (s : t) : t -> t :=
      match s with
        | nil => fun s' => s'
        | x :: l =>
          (fix union_aux (s' : t) : t :=
            match s' with
              | nil => s
              | x' :: l' =>
                match x =?= x' with
                  | Lt => x :: union l s'
                  | Eq => x :: union l l'
                  | Gt => x' :: union_aux l'
                end
            end)
      end.

    Fixpoint inter (s : t) : t -> t :=
      match s with
        | nil => fun _ => nil
        | x :: l =>
          (fix inter_aux (s' : t) : t :=
            match s' with
              | nil => nil
              | x' :: l' =>
                match x =?= x' with
                  | Lt => inter l s'
                  | Eq => x :: inter l l'
                  | Gt => inter_aux l'
                end
            end)
      end.

    Fixpoint diff (s : t) : t -> t :=
      match s with
        | nil => fun _ => nil
        | x :: l =>
          (fix diff_aux (s' : t) : t :=
            match s' with
              | nil => s
              | x' :: l' =>
                match x =?= x' with
                  | Lt => x :: diff l s'
                  | Eq => diff l l'
                  | Gt => diff_aux l'
                end
            end)
      end.

    Fixpoint equal (s s' : t) : bool :=
      match s, s' with
        | nil, nil => true
        | x :: l, x' :: l' =>
          match x =?= x' with
            | Eq => equal l l'
            | _ => false
          end
        | _, _ => false
      end.

    Fixpoint subset (s s' : t) {struct s'} : bool :=
      match s, s' with
        | nil, _ => true
        | x :: l, x' :: l' =>
          match x =?= x' with
            | Lt => false
            | Eq => subset l l'
            | Gt => subset s l'
          end
        | _, _ => false
      end.

    Fixpoint fold {B : Type} (f : elt -> B -> B) (s : t) (i : B) : B :=
      match s with
        | nil => i
        | x :: l => fold f l (f x i)
      end.

    Definition map_monotonic {B : Type} `{OrderedType B}
      (f : elt -> B) (s : t) : set B :=
        List.map f s.

    Fixpoint filter (f : elt -> bool) (s : t) {struct s} : t :=
      match s with
        | nil => nil
        | x :: l => if f x then x :: filter f l else filter f l
      end.

    Fixpoint for_all (f : elt -> bool) (s : t) {struct s} : bool :=
      match s with
        | nil => true
        | x :: l => if f x then for_all f l else false
      end.

    Fixpoint exists_ (f : elt -> bool) (s : t) {struct s} : bool :=
      match s with
        | nil => false
        | x :: l => if f x then true else exists_ f l
      end.

    Fixpoint partition (f : elt -> bool) (s : t) {struct s} : t * t :=
      match s with
        | nil => (nil, nil)
        | x :: l =>
          let (s1, s2) := partition f l in
            if f x then (x :: s1, s2) else (s1, x :: s2)
      end.

    Definition cardinal (s : t) : nat := length s.

    Definition elements (x : t) : list elt := x.

    Definition min_elt (s : t) : option elt :=
      match s with
        | nil => None
        | x :: _ => Some x
      end.

    Fixpoint max_elt (s : t) : option elt :=
      match s with
        | nil => None
        | x :: nil => Some x
        | _ :: l => max_elt l
      end.

    Definition choose := min_elt.

    Notation In := (@InA elt _eq).
    Definition Equal s s' := forall a : elt, In a s <-> In a s'.
    Definition Subset s s' := forall a : elt, In a s -> In a s'.
    Definition Empty s := forall a : elt, ~ In a s.
    Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
    Definition Exists (P : elt -> Prop) (s : t) := exists x, In x s /\ P x.
  End SetDefinitions.

  Implicit Arguments empty [[elt] [comparedec]].
  Implicit Arguments is_empty [[elt] [comparedec]].
  Implicit Arguments mem [[elt] [comparedec]].
  Implicit Arguments add [[elt] [comparedec]].
  Implicit Arguments singleton [[elt] [comparedec]].
  Implicit Arguments remove [[elt] [comparedec]].
  Implicit Arguments union [[elt] [comparedec]].
  Implicit Arguments inter [[elt] [comparedec]].
  Implicit Arguments diff [[elt] [comparedec]].
  Implicit Arguments equal [[elt] [comparedec]].
  Implicit Arguments subset [[elt] [comparedec]].
  Implicit Arguments map_monotonic [[elt] [comparedec] [B] [H]].
  Implicit Arguments fold [[elt] [comparedec] [B]].
  Implicit Arguments filter [[elt] [comparedec]].
  Implicit Arguments for_all [[elt] [comparedec]].
  Implicit Arguments exists_ [[elt] [comparedec]].
  Implicit Arguments partition [[elt] [comparedec]].
  Implicit Arguments cardinal [[elt] [comparedec]].
  Implicit Arguments elements [[elt] [comparedec]].
  Implicit Arguments min_elt [[elt] [comparedec]].
  Implicit Arguments max_elt [[elt] [comparedec]].
  Implicit Arguments choose [[elt] [comparedec]].
  Implicit Arguments Equal [[elt] [comparedec]].
  Implicit Arguments Subset [[elt] [comparedec]].
  Implicit Arguments Empty [[elt] [comparedec]].
  Implicit Arguments For_all [[elt] [comparedec]].
  Implicit Arguments Exists [[elt] [comparedec]].

  Definition map {A : Type} `{OrderedType A} {B : Type} `{OrderedType B}
    (f : A -> B) (s : set A) : set B :=
      fold (fun a sb => add (f a) sb) s empty.
  Implicit Arguments map [[A] [H] [B] [H0]].

  (** Sets seen as a CompareDec (uses list_CompareDec, but in an opaque way) *)
  Definition set_eq `{OrderedType A} : relation (set A) := @list_eq A _eq.
  Definition set_Equivalence `{OrderedType A} : Equivalence set_eq
    := @list_Equivalence A _eq _.

  Definition set_lt `{OrderedType A} : relation (set A) := @list_lt A _lt _eq.
  Definition set_StrictOrder `{OrderedType A} : StrictOrder set_lt set_eq
    := @list_StrictOrder A _.

  Definition set_compare `{OrderedType A} : set A -> set A -> comparison
    := list_compare.
  Definition set_OrderedType `{OrderedType A} : OrderedType (set A) :=
    @list_OrderedType A _.
  Typeclasses Opaque set.

  Set Implicit Arguments.
  Unset Strict Implicit.
  Section SetSpecs.
    Variable A : Type.
    Hypothesis (comparedec : OrderedType A).

    Let elt := A.
    Let t := (set elt).

    Notation Sort := (@sort elt _lt).
    Notation Inf := (@lelistA elt _lt).
    Notation In := (@InA elt _eq).

    Hint Extern 2 (In ?x (?x::_)) => constructor; reflexivity.

    Section AboutSort.
      Lemma In_eq : forall l x y, x === y -> In x l -> In y l.
      Proof. apply InA_eqA; auto. Qed.
      Global Instance In_eq_m : Proper (_eq ==> (@eq (list A)) ==> iff) In.
      Proof.
        repeat intro; subst; split; apply In_eq; auto.
      Qed.

      Lemma ListIn_In : forall l x, List.In x l -> In x l.
      Proof. apply In_InA; auto. Qed.

      Lemma Inf_lt : forall l x y, x <<< y -> Inf y l -> Inf x l.
      Proof. apply InfA_ltA; auto. Qed.
      Global Instance Inf_lt_m :
        Proper (_lt --> (@eq (list A)) ==> impl) Inf.
      Proof.
        repeat intro; subst; apply Inf_lt with x; auto.
      Qed.

      Lemma Inf_eq : forall l x y, x === y -> Inf y l -> Inf x l.
      Proof. apply InfA_eqA; auto. Qed.
      Global Instance Inf_eq_m : Proper (_eq ++> (@eq (list A)) ==> iff) Inf.
      Proof.
        repeat intro; subst; split; apply Inf_eq; auto.
      Qed.

      Lemma Sort_Inf_In :
        forall {l x a}, Sort l -> Inf a l -> In x l -> a <<< x.
      Proof.
        apply SortA_InfA_InA; auto.
      Qed.
      Lemma ListIn_Inf :
        forall l x, (forall y, List.In y l -> x <<< y) -> Inf x l.
      Proof. exact (@In_InfA A _lt). Qed.
      Lemma In_Inf : forall l x, (forall y, In y l -> x <<< y) -> Inf x l.
      Proof. apply InA_InfA; auto. Qed.
      Lemma Inf_alt :
        forall l x, Sort l -> (Inf x l <-> (forall y, In y l -> x <<< y)).
      Proof.
        apply InfA_alt; auto.
      Qed.
    End AboutSort.

    Lemma mem_1 :
      forall (s : t) (Hs : Sort s) (x : elt), In x s -> mem x s = true.
    Proof.
      simple induction s; intros.
      inversion H.
      inversion_clear Hs.
      inversion_clear H0; simpl.
      rewrite (elim_compare_eq H3); trivial.
      rewrite elim_compare_gt; auto.
      apply (@Sort_Inf_In l); trivial.
    Qed.

    Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
    Proof.
      simple induction s.
      intros; inversion H.
      intros a l Hrec x.
      simpl.
      destruct (compare_dec x a); intros; try discriminate; auto.
    Qed.

    Lemma add_Inf :
      forall (s : t) (x a : elt), Inf a s -> a <<< x -> Inf a (add x s).
    Proof.
      simple induction s.
      simpl; intuition.
      simpl; intros; destruct (compare_dec x a); intuition; inversion H0;
        intuition.
    Qed.
    Hint Resolve add_Inf.

    Lemma add_sort : forall (s : t) (Hs : Sort s) (x : elt), Sort (add x s).
    Proof.
      simple induction s.
      simpl; intuition.
      simpl; intros; destruct (compare_dec x a); intuition; inversion_clear Hs;
        auto.
    Qed.

    Lemma add_1 :
      forall (s : t) (Hs : Sort s) (x y : elt), x === y -> In y (add x s).
    Proof.
      simple induction s.
      simpl; intuition.
      simpl; intros; destruct (compare_dec x a); inversion_clear Hs; auto.
      constructor; transitivity x; auto.
    Qed.

    Lemma add_2 :
      forall (s : t) (Hs : Sort s) (x y : elt), In y s -> In y (add x s).
    Proof.
      simple induction s.
      simpl; intuition.
      simpl; intros; destruct (compare_dec x a); intuition.
      inversion_clear Hs; inversion_clear H0; auto.
    Qed.

    Lemma add_3 :
      forall (s : t) (Hs : Sort s) (x y : elt),
        x =/= y -> In y (add x s) -> In y s.
    Proof.
      simple induction s.
      simpl; inversion_clear 3; auto; symmetry in H; contradiction.
      simpl; intros a l Hrec Hs x y; destruct (compare_dec x a); intros;
        inversion_clear H1; inversion_clear Hs; auto.
      symmetry in H0; contradiction.
      constructor 2; apply Hrec with x; auto.
    Qed.

    Lemma remove_Inf :
      forall (s : t) (Hs : Sort s) (x a : elt), Inf a s -> Inf a (remove x s).
    Proof.
      simple induction s.
      simpl; intuition.
      simpl; intros; destruct (compare_dec x a); intuition;
        inversion_clear H0; auto.
      inversion_clear Hs; apply Inf_lt with a; auto.
    Qed.
    Hint Resolve remove_Inf.

    Lemma remove_sort :
      forall (s : t) (Hs : Sort s) (x : elt), Sort (remove x s).
    Proof.
      simple induction s.
      simpl; intuition.
      simpl; intros; destruct (compare_dec x a); intuition;
        inversion_clear Hs; auto.
    Qed.

    Lemma remove_1 :
      forall (s : t) (Hs : Sort s) (x y : elt), x === y -> ~ In y (remove x s).
    Proof.
      simple induction s.
      simpl; red; intros; inversion H0.
      simpl; intros; destruct (compare_dec x a); intuition; inversion_clear Hs.
      inversion_clear H2.
      exact (lt_not_eq H1 (transitivity H0 H5)).
      generalize (Sort_Inf_In H3 H4 H5).
      rewrite H0 in H1; apply lt_not_gt; auto.
      generalize (Sort_Inf_In H3 H4 H2).
      rewrite H0 in H1; apply eq_not_gt; auto.
      inversion_clear H2.
      apply (gt_not_eq H1 (transitivity H0 H5)).
      apply (H H3 _ _ H0 H5).
    Qed.

    Lemma remove_2 :
      forall (s : t) (Hs : Sort s) (x y : elt),
        x =/= y -> In y s -> In y (remove x s).
    Proof.
      simple induction s.
      simpl; intuition.
      simpl; intros; destruct (compare_dec x a); intuition; inversion_clear Hs;
        inversion_clear H1; auto.
      destruct H0; transitivity a; auto.
    Qed.

    Lemma remove_3 :
      forall (s : t) (Hs : Sort s) (x y : elt), In y (remove x s) -> In y s.
    Proof.
      simple induction s.
      simpl; intuition.
      simpl; intros a l Hrec Hs x y; destruct (compare_dec x a); intuition.
      inversion_clear Hs; inversion_clear H0; auto.
      constructor 2; apply Hrec with x; auto.
    Qed.

    Lemma singleton_sort : forall x : elt, Sort (singleton x).
    Proof.
      unfold singleton; simpl; auto.
    Qed.

    Lemma singleton_1 : forall x y : elt, In y (singleton x) -> x === y.
    Proof.
      unfold singleton; simpl; intuition.
      inversion_clear H; auto; inversion H0.
    Qed.

    Lemma singleton_2 : forall x y : elt, x === y -> In y (singleton x).
    Proof.
      unfold singleton; simpl; auto.
    Qed.

    Ltac DoubleInd :=
      simple induction s;
        [ simpl; auto; try solve [ intros; inversion H ]
          | intros x l Hrec; simple induction s';
            [ simpl; auto; try solve [ intros; inversion H ]
              | intros x' l' Hrec' Hs Hs'; inversion Hs; inversion Hs'; subst;
                simpl ] ].

    Lemma union_Inf :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
        Inf a s -> Inf a s' -> Inf a (union s s').
    Proof.
      DoubleInd.
      intros i His His'; inversion_clear His; inversion_clear His'.
      destruct (compare x x'); auto.
    Qed.
    Hint Resolve union_Inf.

    Lemma union_sort :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (union s s').
    Proof.
      DoubleInd; destruct (compare_dec x x'); intuition; constructor; auto.
      apply Inf_eq with x'; trivial; apply union_Inf; trivial;
        apply Inf_eq with x; auto.
      change (Inf x' (union (x :: l) l')); auto.
    Qed.

    Lemma union_1 :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
        In x (union s s') -> In x s \/ In x s'.
    Proof.
      DoubleInd; destruct (compare_dec x x'); intuition;
        inversion_clear H0; intuition.
      elim (Hrec (x' :: l') H1 Hs' x0); intuition.
      elim (Hrec l' H1 H5 x0); intuition.
      elim (H3 x0); intuition.
    Qed.

    Lemma union_2 :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
        In x s -> In x (union s s').
    Proof.
      DoubleInd.
      intros i Hi; destruct (compare_dec x x'); intuition;
        inversion_clear Hi; auto.
    Qed.

    Lemma union_3 :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
        In x s' -> In x (union s s').
    Proof.
      DoubleInd.
      intros i Hi; destruct (compare_dec x x'); inversion_clear Hi; intuition.
      constructor; transitivity x'; auto.
    Qed.

    Lemma inter_Inf :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
        Inf a s -> Inf a s' -> Inf a (inter s s').
    Proof.
      DoubleInd.
      intros i His His'; inversion His; inversion His'; subst.
      destruct (compare_dec x x'); intuition.
      apply Inf_lt with x; auto.
      apply H4; auto.
      apply Inf_lt with x'; auto.
    Qed.
    Hint Resolve inter_Inf.

    Lemma inter_sort :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (inter s s').
    Proof.
      DoubleInd; destruct (compare_dec x x'); auto.
      constructor; auto.
      apply Inf_eq with x'; trivial;
        apply inter_Inf; trivial; apply Inf_eq with x; auto.
    Qed.

    Lemma inter_1 :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
        In x (inter s s') -> In x s.
    Proof.
      DoubleInd; destruct (compare_dec x x'); intuition.
      constructor 2; apply Hrec with (x'::l'); auto.
      inversion_clear H0; auto.
      constructor 2; apply Hrec with l'; auto.
    Qed.

    Lemma inter_2 :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
        In x (inter s s') -> In x s'.
    Proof.
      DoubleInd; destruct (compare_dec x x'); intuition; inversion_clear H0.
      constructor 1; transitivity x; auto.
      constructor 2; auto.
    Qed.

    Lemma inter_3 :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
        In x s -> In x s' -> In x (inter s s').
    Proof.
      DoubleInd.
      intros i His His'; destruct (compare_dec x x'); intuition.

      inversion_clear His; auto.
      generalize (Sort_Inf_In Hs' (cons_leA _ _ _ _ H) His').
      intro abs; rewrite H0 in abs; contradiction (lt_antirefl abs).

      inversion_clear His; auto; inversion_clear His'; auto.
      constructor; transitivity x'; auto.

      change (In i (inter (x :: l) l')).
      inversion_clear His'; auto.
      generalize (Sort_Inf_In Hs (cons_leA _ _ _ _ H) His).
      intro abs; rewrite H0 in abs; contradiction (lt_antirefl abs).
    Qed.

    Lemma diff_Inf :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
        Inf a s -> Inf a s' -> Inf a (diff s s').
    Proof.
      DoubleInd.
      intros i His His'; inversion His; inversion His'.
      destruct (compare_dec x x'); intuition.
      apply Hrec; trivial.
      apply Inf_lt with x; auto.
      apply Inf_lt with x'; auto.
      apply H11; trivial.
      apply Inf_lt with x'; auto.
    Qed.
    Hint Resolve diff_Inf.

    Lemma diff_sort :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (diff s s').
    Proof.
      DoubleInd; destruct (compare_dec x x'); auto.
    Qed.

    Lemma diff_1 :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
        In x (diff s s') -> In x s.
    Proof.
      DoubleInd; destruct (compare_dec x x'); intuition.
      inversion_clear H0; auto.
      constructor 2; apply Hrec with (x'::l'); auto.
      constructor 2; apply Hrec with l'; auto.
    Qed.

    Lemma diff_2 :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
        In x (diff s s') -> ~ In x s'.
    Proof.
      DoubleInd.
      intros; intro Abs; inversion Abs.
      destruct (compare_dec x x'); intuition.

      inversion_clear H0.
      generalize (Sort_Inf_In Hs' (cons_leA _ _ _ _ H) H4).
      intro abs; exact (gt_not_eq abs H7).
      apply Hrec with (x'::l') x0; auto.

      inversion_clear H4.
      generalize (Sort_Inf_In H1 H2 (diff_1 H1 H5 H0)).
      apply eq_not_lt; transitivity x'; auto.
      apply Hrec with l' x0; auto.

      inversion_clear H4.
      generalize (Sort_Inf_In Hs (cons_leA _ _ _ _ H) (diff_1 Hs H5 H0)).
      apply eq_not_lt; auto.
      apply H3 with x0; auto.
    Qed.

    Lemma diff_3 :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
        In x s -> ~ In x s' -> In x (diff s s').
    Proof.
      DoubleInd.
      intros i His His'; destruct (compare_dec x x'); intuition;
        inversion_clear His; auto.
      elim His'; constructor; transitivity x; auto.
    Qed.

    Lemma equal_1 :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'),
        Equal s s' -> equal s s' = true.
    Proof.
      simple induction s; unfold Equal.
      intro s'; case s'; auto.
      simpl; intuition.
      elim (H e); intros; assert (Z : In e nil);
        [apply H1; constructor; reflexivity | inversion Z].
      intros x l Hrec s'.
      case s'.
      intros; elim (H x); intros; assert (Z : In x nil);
        [apply H0; constructor; reflexivity | inversion Z].
      intros x' l' Hs Hs'; inversion Hs; inversion Hs'; subst.
      simpl; destruct (compare_dec x x'); intros; auto.

      elim (H0 x); intros.
      assert (Z : In x (x' :: l'));
        [apply H3; constructor; reflexivity | inversion_clear Z].
      contradiction (lt_not_eq H H7).
      generalize (Sort_Inf_In H5 H6 H7); intro abs.
      contradiction (lt_not_gt abs H).

      apply Hrec; intuition; elim (H0 a); intros.
      assert (Z : In a (x' :: l')); auto; inversion_clear Z; auto.
      generalize (Sort_Inf_In H1 H2 H3).
      rewrite H; intro abs; contradiction (gt_not_eq abs H8).
      assert (Z : In a (x :: l)); auto; inversion_clear Z; auto.
      generalize (Sort_Inf_In H5 H6 H3).
      rewrite <- H; intro abs; contradiction (gt_not_eq abs H8).

      elim (H0 x'); intros.
      assert (Z : In x' (x :: l));
        [apply H4; constructor; reflexivity | inversion_clear Z].
      contradiction (gt_not_eq H (symmetry H7)).
      generalize (Sort_Inf_In H1 H2 H7); intro abs.
      contradiction (lt_not_gt abs H).
    Qed.

    Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
    Proof.
      simple induction s; unfold Equal.
      intro s'; case s'; intros.
      intuition.
      simpl in H; discriminate H.
      intros x l Hrec s'.
      case s'.
      intros; simpl in H; discriminate.
      intros x' l'; simpl; destruct (compare_dec x x');
        intros; auto; try discriminate.
      elim (Hrec l' H0 a); intuition; inversion_clear H3; auto.
      constructor; transitivity x; auto.
      constructor; transitivity x'; auto.
    Qed.

    Lemma subset_1 :
      forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'),
        Subset s s' -> subset s s' = true.
    Proof.
      intros s s'; generalize s' s; clear s s'.
      simple induction s'; unfold Subset.
      intro s; case s; auto.
      intros; elim (H e); intros; assert (Z : In e nil); auto; inversion Z.
      intros x' l' Hrec s; case s.
      simpl; auto.
      intros x l Hs Hs'; inversion Hs; inversion Hs'; subst.
      simpl; destruct (compare_dec x x'); intros; auto.

      assert (Z : In x (x' :: l')); auto; inversion_clear Z.
      contradiction (lt_not_eq H H3).
      generalize (Sort_Inf_In H5 H6 H3).
      intro abs; contradiction (lt_not_gt H abs).

      apply Hrec; intuition.
      assert (Z : In a (x' :: l')); auto; inversion_clear Z; auto.
      generalize (Sort_Inf_In H1 H2 H3).
      rewrite H; intro abs; contradiction (gt_not_eq abs H4).

      apply Hrec; intuition.
      assert (Z : In a (x' :: l')); auto; inversion_clear Z; auto.
      inversion_clear H3.
      contradiction (lt_antirefl (x:=a)); rewrite H4 at 1; rewrite H7; auto.
      generalize (Sort_Inf_In H1 H2 H7).
      rewrite H4; intro abs; contradiction (lt_not_gt H abs).
    Qed.

    Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
    Proof.
      intros s s'; generalize s' s; clear s s'.
      simple induction s'; unfold Subset.
      intro s; case s; auto.
      simpl; intros; discriminate H.
      intros x' l' Hrec s; case s.
      intros; inversion H0.
      intros x l; simpl; destruct (compare_dec x x'); intros; auto.
      discriminate.
      inversion_clear H1.
      constructor; transitivity x; auto.
      constructor 2; apply Hrec with l; auto.
      constructor 2; apply Hrec with (x::l); auto.
    Qed.

    Lemma empty_sort : Sort empty.
    Proof.
      unfold empty; constructor.
    Qed.

    Lemma empty_1 : Empty empty.
    Proof.
      unfold Empty, empty; intuition; inversion H.
    Qed.

    Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
    Proof.
      unfold Empty; intro s; case s; simpl; intuition.
      elim (H e); auto; constructor; reflexivity.
    Qed.

    Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
    Proof.
      unfold Empty; intro s; case s; simpl; intuition;
        inversion H0.
    Qed.

    Lemma elements_1 : forall (s : t) (x : elt), In x s -> In x (elements s).
    Proof.
      unfold elements; auto.
    Qed.

    Lemma elements_2 : forall (s : t) (x : elt), In x (elements s) -> In x s.
    Proof.
      unfold elements; auto.
    Qed.

    Lemma elements_3 : forall (s : t) (Hs : Sort s), Sort (elements s).
    Proof.
      unfold elements; auto.
    Qed.
    Lemma elements_3w : forall (s : t) (Hs : Sort s), NoDupA _eq (elements s).
    Proof.
      unfold elements; intros; apply SortA_NoDupA with _lt; auto.
    Qed.

    Lemma min_elt_1 : forall (s : t) (x : elt), min_elt s = Some x -> In x s.
    Proof.
      intro s; case s; simpl; intros; inversion H; auto.
    Qed.

    Lemma min_elt_2 :
      forall (s : t) (Hs : Sort s) (x y : elt),
        min_elt s = Some x -> In y s -> ~ y <<< x.
    Proof.
      simple induction s; simpl.
      intros; inversion H.
      intros a l; case l; intros; inversion H0; inversion_clear H1; subst.
      apply eq_not_lt; auto.
      inversion H2.
      apply eq_not_lt; auto.
      inversion_clear Hs.
      inversion_clear H3.
      generalize (H H1 e y (refl_equal (Some e)) H2).
      intros Hlt abs; apply Hlt; transitivity x; auto.
    Qed.

    Lemma min_elt_3 : forall s : t, min_elt s = None -> Empty s.
    Proof.
      unfold Empty; intro s; case s; simpl; intuition;
        inversion H; inversion H0.
    Qed.

    Lemma max_elt_1 : forall (s : t) (x : elt), max_elt s = Some x -> In x s.
    Proof.
      simple induction s; simpl.
      intros; inversion H.
      intros x l; case l; simpl.
      intuition.
      inversion H0; auto.
      intros.
      constructor 2; apply (H _ H0).
    Qed.

    Lemma max_elt_2 :
      forall (s : t) (Hs : Sort s) (x y : elt),
        max_elt s = Some x -> In y s -> ~ x <<< y.
    Proof.
      simple induction s; simpl.
      intros; inversion H.
      intros x l; case l; simpl.
      intuition.
      inversion H0; subst.
      inversion_clear H1.
      apply (gt_not_eq H2 H3).
      inversion H3.
      intros; inversion_clear Hs; inversion_clear H3; inversion_clear H1.
      assert (In e (e::l0)) by auto.
      generalize (H H2 x0 e H0 H1).
      intros Hlt abs; apply Hlt; transitivity y; auto; rewrite H3; auto.
      exact (H H2 x0 y H0 H3).
    Qed.

    Lemma max_elt_3 : forall s : t, max_elt s = None -> Empty s.
    Proof.
      unfold Empty; simple induction s; simpl.
      red; intros; inversion H0.
      intros x l; case l; simpl; intros.
      inversion H0.
      elim (H H0 e); auto.
    Qed.

    Definition choose_1 :
      forall (s : t) (x : elt), choose s = Some x -> In x s := min_elt_1.

    Definition choose_2 : forall s : t, choose s = None -> Empty s := min_elt_3.

    Lemma choose_3: forall s s', Sort s -> Sort s' -> forall x x',
      choose s = Some x -> choose s' = Some x' -> Equal s s' -> x === x'.
    Proof.
      unfold choose, Equal; intros s s' Hs Hs' x x' Hx Hx' H.
      assert (~x <<< x').
      apply min_elt_2 with s'; auto.
      rewrite <-H; auto using min_elt_1.
      assert (~x' <<< x).
      apply min_elt_2 with s; auto.
      rewrite H; auto using min_elt_1.
      destruct (compare_dec x x'); intuition.
    Qed.

    Lemma fold_1 :
      forall (s : t) (Hs : Sort s) (A : Type) (i : A) (f : elt -> A -> A),
        fold f s i = fold_left (fun a e => f e a) (elements s) i.
    Proof.
      induction s.
      simpl; trivial.
      intros.
      inversion_clear Hs.
      simpl; auto.
    Qed.

    Lemma cardinal_1 :
      forall (s : t) (Hs : Sort s), cardinal s = length (elements s).
    Proof.
      auto.
    Qed.

    Lemma filter_Inf :
      forall (s : t) (Hs : Sort s) (x : elt) (f : elt -> bool),
        Inf x s -> Inf x (filter f s).
    Proof.
      simple induction s; simpl.
      intuition.
      intros x l Hrec Hs a f Ha; inversion_clear Hs; inversion_clear Ha.
      case (f x).
      constructor; auto.
      apply Hrec; auto.
      apply Inf_lt with x; auto.
    Qed.

    Lemma filter_sort :
      forall (s : t) (Hs : Sort s) (f : elt -> bool), Sort (filter f s).
    Proof.
      simple induction s; simpl.
      auto.
      intros x l Hrec Hs f; inversion_clear Hs.
      case (f x); auto.
      constructor; auto.
      apply filter_Inf; auto.
    Qed.

    Lemma filter_1 :
      forall (s : t) (x : elt) (f : elt -> bool)
        `{Proper _ (_eq ==> (@eq bool)) f}, In x (filter f s) -> In x s.
    Proof.
      simple induction s; simpl.
      intros; inversion H0.
      intros x l Hrec a f Hf.
      case (f x); simpl.
      inversion_clear 1.
      constructor; auto.
      constructor 2; apply (Hrec a f Hf); trivial.
      constructor 2; apply (Hrec a f Hf); trivial.
    Qed.

    Lemma filter_2 :
      forall (s : t) (x : elt) (f : elt -> bool)
        `{Proper _ (_eq ==> (@eq bool)) f},
        In x (filter f s) -> f x = true.
    Proof.
      simple induction s; simpl.
      intros; inversion H0.
      intros x l Hrec a f Hf.
      generalize (Hf x); case (f x); simpl; auto.
      inversion_clear 2; auto.
      symmetry; auto.
    Qed.

    Lemma filter_3 :
      forall (s : t) (x : elt) (f : elt -> bool)
        `{Proper _ (_eq ==> (@eq bool)) f},
        In x s -> f x = true -> In x (filter f s).
    Proof.
      simple induction s; simpl.
      intros; inversion H0.
      intros x l Hrec a f Hf.
      generalize (Hf x); case (f x); simpl.
      inversion_clear 2; auto.
      inversion_clear 2; auto.
      rewrite <- (H a (symmetry H1)); intros; discriminate.
    Qed.

    Lemma for_all_1 :
      forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
        For_all (fun x => f x = true) s -> for_all f s = true.
    Proof.
      simple induction s; simpl; auto; unfold For_all.
      intros x l Hrec f Hf.
      generalize (Hf x); case (f x); simpl.
      auto.
      intros; rewrite (H x); auto; reflexivity.
    Qed.

    Lemma for_all_2 :
      forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
        for_all f s = true -> For_all (fun x => f x = true) s.
    Proof.
      simple induction s; simpl; auto; unfold For_all.
      intros; inversion H1.
      intros x l Hrec f Hf.
      intros Z a; intros.
      assert (f x = true).
      generalize Z; case (f x); auto.
      rewrite H0 in Z; simpl in Z.
      inversion_clear H; auto.
      rewrite (Hf a x); auto.
    Qed.

    Lemma exists_1 :
      forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
        Exists (fun x => f x = true) s -> exists_ f s = true.
    Proof.
      simple induction s; simpl; auto; unfold Exists.
      intros.
      elim H0; intuition.
      inversion H2.
      intros x l Hrec f Hf.
      generalize (Hf x); case (f x); simpl.
      auto.
      destruct 2 as [a (A1,A2)].
      inversion_clear A1.
      rewrite <- (H a (symmetry H0)) in A2; discriminate.
      apply Hrec; auto.
      exists a; auto.
    Qed.

    Lemma exists_2 :
      forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
        exists_ f s = true -> Exists (fun x => f x = true) s.
    Proof.
      simple induction s; simpl; auto; unfold Exists.
      intros; discriminate.
      intros x l Hrec f Hf.
      case_eq (f x); intros.
      exists x; auto.
      destruct (Hrec f Hf H0) as [a (A1,A2)].
      exists a; auto.
    Qed.

    Lemma partition_Inf_1 :
      forall (s : t) (Hs : Sort s) (f : elt -> bool) (x : elt),
        Inf x s -> Inf x (fst (partition f s)).
    Proof.
      simple induction s; simpl.
      intuition.
      intros x l Hrec Hs f a Ha; inversion_clear Hs; inversion_clear Ha.
      generalize (Hrec H f a).
      case (f x); case (partition f l); simpl.
      auto.
      intros; apply H2; apply Inf_lt with x; auto.
    Qed.

    Lemma partition_Inf_2 :
      forall (s : t) (Hs : Sort s) (f : elt -> bool) (x : elt),
        Inf x s -> Inf x (snd (partition f s)).
    Proof.
      simple induction s; simpl.
      intuition.
      intros x l Hrec Hs f a Ha; inversion_clear Hs; inversion_clear Ha.
      generalize (Hrec H f a).
      case (f x); case (partition f l); simpl.
      intros; apply H2; apply Inf_lt with x; auto.
      auto.
    Qed.

    Lemma partition_sort_1 :
      forall (s : t) (Hs : Sort s) (f : elt -> bool),
        Sort (fst (partition f s)).
    Proof.
      simple induction s; simpl.
      auto.
      intros x l Hrec Hs f; inversion_clear Hs.
      generalize (Hrec H f); generalize (partition_Inf_1 H f).
      case (f x); case (partition f l); simpl; auto.
    Qed.

    Lemma partition_sort_2 :
      forall (s : t) (Hs : Sort s) (f : elt -> bool),
        Sort (snd (partition f s)).
    Proof.
      simple induction s; simpl.
      auto.
      intros x l Hrec Hs f; inversion_clear Hs.
      generalize (Hrec H f); generalize (partition_Inf_2 H f).
      case (f x); case (partition f l); simpl; auto.
    Qed.

    Lemma partition_1 :
      forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
        Equal (fst (partition f s)) (filter f s).
    Proof.
      simple induction s; simpl; auto; unfold Equal.
      split; auto.
      intros x l Hrec f Hf.
      generalize (Hrec f Hf); clear Hrec.
      destruct partition as [s1 s2]; simpl; intros.
      case (f x); simpl; auto.
      split; inversion_clear 1; auto.
      constructor 2; generalize (proj1 (H a)); auto.
      constructor 2; generalize (proj2 (H a)); auto.
    Qed.

    Lemma partition_2 :
      forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
        Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
    Proof.
      simple induction s; simpl; auto; unfold Equal.
      split; auto.
      intros x l Hrec f Hf.
      generalize (Hrec f Hf); clear Hrec.
      destruct partition as [s1 s2]; simpl; intros.
      case (f x); simpl; auto.
      split; inversion_clear 1; auto.
      constructor 2; generalize (proj1 (H a)); auto.
      constructor 2; generalize (proj2 (H a)); auto.
    Qed.

    Lemma map_monotonic_Inf `{OrderedType B} :
      forall (s : t) (Hs : Sort s) (x : elt)
        (f : elt -> B) `{Proper _ (_lt ==> _lt) f},
        Inf x s -> lelistA _lt (f x) (map_monotonic f s).
    Proof.
      simple induction s; simpl.
      intuition.
      intros x l Hrec Hs a f Hf Ha; inversion_clear Hs; inversion_clear Ha.
      constructor; auto.
    Qed.

    Lemma map_monotonic_sort `{OrderedType B} :
      forall (s : t) (Hs : Sort s)
        (f : elt -> B) `{Proper _ (_lt ==> _lt) f},
        sort _lt (map_monotonic f s).
    Proof.
      simple induction s; simpl.
      auto.
      intros x l Hrec Hs f Hf; inversion_clear Hs.
      constructor; auto.
      apply map_monotonic_Inf; auto.
    Qed.
  End SetSpecs.

  Definition In `{OrderedType A} (x : A) (s : set A) := InA _eq x s.
End SetList.

Module S := SetList.

Structure set (A : Type) `{OrderedType A}
  := Build_set {this :> list A; sorted : sort _lt this}.
Implicit Arguments this [[A] [H]].
Implicit Arguments Build_set [[A] [H] [this]].
Implicit Arguments sorted [[A] [H]].

Section SetDefinitions.
  Variable A : Type.
  Hypothesis (comparedec : OrderedType A).

  Let elt := A.
  Let t := set elt.

  Definition empty : t := Build_set (@S.empty_sort _ _).
  Definition is_empty (s : t) : bool := S.is_empty s.
  Definition mem (x : elt) (s : t) : bool := S.mem x s.
  Definition add (x : elt) (s : t) : t :=
    Build_set (S.add_sort (sorted s) x).
  Definition singleton (x : elt) : t :=
    Build_set (S.singleton_sort _ x).
  Definition remove (x : elt) (s : t) : t :=
    Build_set (S.remove_sort (sorted s) x).
  Definition union (s s' : t) : t :=
    Build_set (S.union_sort (sorted s) (sorted s')).
  Definition inter (s s' : t) : t :=
    Build_set (S.inter_sort (sorted s) (sorted s')).
  Definition diff (s s' : t) : t :=
    Build_set (S.diff_sort (sorted s) (sorted s')).

  Definition equal (s s' : t) : bool := S.equal s s'.
  Definition subset (s s' : t) : bool := S.subset s s'.

  Definition fold {B : Type} (f : elt -> B -> B) (s : t) : B -> B :=
    S.fold f s.
(*   Definition map {B : Type} (f : elt -> B) (s : t) : set B := *)
(*     Build_set (S.map f s. *)
  Definition map_monotonic {B : Type} `{OrderedType B}
    (f : elt -> B) `{Mono : Proper _ (_lt ==> _lt) f} (s : t) : set B :=
      Build_set (S.map_monotonic_sort (sorted s)).

  Definition filter (f : elt -> bool) (s : t) : t :=
    Build_set (S.filter_sort (sorted s) f).
  Definition for_all (f : elt -> bool) (s : t) : bool := S.for_all f s.
  Definition exists_ (f : elt -> bool) (s : t) : bool := S.exists_ f s.
  Definition partition (f : elt -> bool) (s : t) : t * t :=
    let p := S.partition f s in
      (Build_set (this:=fst p) (S.partition_sort_1 (sorted s) f),
        Build_set (this:=snd p) (S.partition_sort_2 (sorted s) f)).

  Definition cardinal (s : t) : nat := S.cardinal s.
  Definition elements (x : t) : list elt := S.elements x.

  Definition min_elt (s : t) : option elt := S.min_elt s.
  Definition max_elt (s : t) : option elt := S.max_elt s.
  Definition choose := min_elt.
End SetDefinitions.

Implicit Arguments empty [[A] [comparedec]].
Implicit Arguments is_empty [[A] [comparedec]].
Implicit Arguments mem [[A] [comparedec]].
Implicit Arguments add [[A] [comparedec]].
Implicit Arguments singleton [[A] [comparedec]].
Implicit Arguments remove [[A] [comparedec]].
Implicit Arguments union [[A] [comparedec]].
Implicit Arguments inter [[A] [comparedec]].
Implicit Arguments diff [[A] [comparedec]].
Implicit Arguments equal [[A] [comparedec]].
Implicit Arguments subset [[A] [comparedec]].
Implicit Arguments map_monotonic [[A] [comparedec] [B] [H] [Mono]].
Implicit Arguments fold [[A] [comparedec] [B]].
Implicit Arguments filter [[A] [comparedec]].
Implicit Arguments for_all [[A] [comparedec]].
Implicit Arguments exists_ [[A] [comparedec]].
Implicit Arguments partition [[A] [comparedec]].
Implicit Arguments cardinal [[A] [comparedec]].
Implicit Arguments elements [[A] [comparedec]].
Implicit Arguments min_elt [[A] [comparedec]].
Implicit Arguments max_elt [[A] [comparedec]].
Implicit Arguments choose [[A] [comparedec]].

Set Implicit Arguments.
Unset Strict Implicit.

Section Spec.
  Variable A : Type.
  Hypothesis (comparedec : OrderedType A).

  Let elt := A.
  Let t := (set elt).

  Variable s s' s'': t.
  Variable x y : elt.

  Definition In (x : elt) (s : t) : Prop := InA _eq x s.(this).
  Definition Equal (s s':t) : Prop := forall a : elt, In a s <-> In a s'.
  Definition Subset (s s':t) : Prop := forall a : elt, In a s -> In a s'.
  Definition Empty (s:t) : Prop := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop)(s:t) : Prop := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop)(s:t) : Prop := exists x, In x s /\ P x.

  Lemma In_1 : x === y -> In x s -> In y s.
  Proof. exact (fun H H' => S.In_eq H H'). Qed.

  Lemma mem_1 : In x s -> mem x s = true.
  Proof. exact (fun H => S.mem_1 s.(sorted) H). Qed.
  Lemma mem_2 : mem x s = true -> In x s.
  Proof. exact (fun H => S.mem_2 H). Qed.

  Lemma equal_1 : Equal s s' -> equal s s' = true.
  Proof. exact (S.equal_1 s.(sorted) s'.(sorted)). Qed.
  Lemma equal_2 : equal s s' = true -> Equal s s'.
  Proof. exact (fun H => S.equal_2 H). Qed.

  Lemma subset_1 : Subset s s' -> subset s s' = true.
  Proof. exact (S.subset_1 s.(sorted) s'.(sorted)). Qed.
  Lemma subset_2 : subset s s' = true -> Subset s s'.
  Proof. exact (fun H => S.subset_2 H). Qed.

  Lemma empty_1 : Empty empty.
  Proof. eapply S.empty_1. Qed.

  Lemma is_empty_1 : Empty s -> is_empty s = true.
  Proof. exact (fun H => S.is_empty_1 H). Qed.
  Lemma is_empty_2 : is_empty s = true -> Empty s.
  Proof. exact (fun H => S.is_empty_2 H). Qed.

  Lemma add_1 : x === y -> In y (add x s).
  Proof. exact (fun H => S.add_1 s.(sorted) H). Qed.
  Lemma add_2 : In y s -> In y (add x s).
  Proof. exact (fun H => S.add_2 s.(sorted) x H). Qed.
  Lemma add_3 : x =/= y -> In y (add x s) -> In y s.
  Proof. exact (fun H => S.add_3 s.(sorted) H). Qed.

  Lemma remove_1 : x === y -> ~ In y (remove x s).
  Proof. exact (fun H => S.remove_1 s.(sorted) H). Qed.
  Lemma remove_2 : x =/= y -> In y s -> In y (remove x s).
  Proof. exact (fun H H' => S.remove_2 s.(sorted) H H'). Qed.
  Lemma remove_3 : In y (remove x s) -> In y s.
  Proof. exact (fun H => S.remove_3 s.(sorted) H). Qed.

  Lemma singleton_1 : In y (singleton x) -> x === y.
  Proof. exact (fun H => S.singleton_1 H). Qed.
  Lemma singleton_2 : x === y -> In y (singleton x).
  Proof. exact (fun H => S.singleton_2 H). Qed.

  Lemma union_1 : In x (union s s') -> In x s \/ In x s'.
  Proof. exact (fun H => S.union_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma union_2 : In x s -> In x (union s s').
  Proof. exact (fun H => S.union_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma union_3 : In x s' -> In x (union s s').
  Proof. exact (fun H => S.union_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma inter_1 : In x (inter s s') -> In x s.
  Proof. exact (fun H => S.inter_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma inter_2 : In x (inter s s') -> In x s'.
  Proof. exact (fun H => S.inter_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma inter_3 : In x s -> In x s' -> In x (inter s s').
  Proof. exact (fun H => S.inter_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma diff_1 : In x (diff s s') -> In x s.
  Proof. exact (fun H => S.diff_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma diff_2 : In x (diff s s') -> ~ In x s'.
  Proof. exact (fun H => S.diff_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma diff_3 : In x s -> ~ In x s' -> In x (diff s s').
  Proof. exact (fun H => S.diff_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma fold_1 : forall (A : Type) (i : A) (f : elt -> A -> A),
    fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof. exact (S.fold_1 s.(sorted)). Qed.

  Lemma cardinal_1 : cardinal s = length (elements s).
  Proof. exact (S.cardinal_1 s.(sorted)). Qed.

  Section Filter.

    Variable f : elt -> bool.
    Lemma filter_1 `{Proper _ (_eq ==> (@eq bool)) f} :
      In x (filter f s) -> In x s.
    Proof. intros; eapply S.filter_1 with (f := f); auto. Qed.
    Lemma filter_2 `{Proper _ (_eq ==> (@eq bool)) f} :
      In x (filter f s) -> f x = true.
    Proof. intros; eapply S.filter_2 with (s := s); auto. Qed.
    Lemma filter_3 `{Proper _ (_eq ==> (@eq bool)) f} :
      In x s -> f x = true -> In x (filter f s).
    Proof. apply S.filter_3; auto. Qed.

    Lemma for_all_1 `{Proper _ (_eq ==> (@eq bool)) f} :
      For_all (fun x => f x = true) s -> for_all f s = true.
    Proof. apply S.for_all_1; auto. Qed.
    Lemma for_all_2 `{Proper _ (_eq ==> (@eq bool)) f} :
      for_all f s = true -> For_all (fun x => f x = true) s.
    Proof. apply S.for_all_2; auto. Qed.

    Lemma exists_1 `{Proper _ (_eq ==> (@eq bool)) f} :
      Exists (fun x => f x = true) s -> exists_ f s = true.
    Proof. apply S.exists_1; auto. Qed.
    Lemma exists_2 `{Proper _ (_eq ==> (@eq bool)) f} :
      exists_ f s = true -> Exists (fun x => f x = true) s.
    Proof. apply S.exists_2; auto. Qed.

    Lemma partition_1 `{Proper _ (_eq ==> (@eq bool)) f} :
      Equal (fst (partition f s)) (filter f s).
    Proof. apply (@S.partition_1 _ _ s f); auto. Qed.
    Lemma partition_2 `{Proper _ (_eq ==> (@eq bool)) f} :
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
    Proof. apply (@S.partition_2 _ _ s f); auto. Qed.

  End Filter.

  Lemma elements_1 : In x s -> InA _eq x (elements s).
  Proof. exact (fun H => S.elements_1 H). Qed.
  Lemma elements_2 : InA _eq x (elements s) -> In x s.
  Proof. exact (fun H => S.elements_2 H). Qed.
  Lemma elements_3 : sort _lt (elements s).
  Proof. exact (S.elements_3 s.(sorted)). Qed.
  Lemma elements_3w : NoDupA _eq (elements s).
  Proof. exact (S.elements_3w s.(sorted)). Qed.

  Lemma min_elt_1 : min_elt s = Some x -> In x s.
  Proof. exact (fun H => S.min_elt_1 H). Qed.
  Lemma min_elt_2 : min_elt s = Some x -> In y s -> ~ y <<< x.
  Proof. exact (fun H => S.min_elt_2 s.(sorted) H). Qed.
  Lemma min_elt_3 : min_elt s = None -> Empty s.
  Proof. exact (fun H => S.min_elt_3 H). Qed.

  Lemma max_elt_1 : max_elt s = Some x -> In x s.
  Proof. exact (fun H => S.max_elt_1 H). Qed.
  Lemma max_elt_2 : max_elt s = Some x -> In y s -> ~ x <<< y.
  Proof. exact (fun H => S.max_elt_2 s.(sorted) H). Qed.
  Lemma max_elt_3 : max_elt s = None -> Empty s.
  Proof. exact (fun H => S.max_elt_3 H). Qed.

  Lemma choose_1 : choose s = Some x -> In x s.
  Proof. exact (fun H => S.choose_1 H). Qed.
  Lemma choose_2 : choose s = None -> Empty s.
  Proof. exact (fun H => S.choose_2 H). Qed.
  Lemma choose_3 : choose s = Some x -> choose s' = Some y ->
    Equal s s' -> x === y.
  Proof. eapply S.choose_3; apply sorted. Qed.
End Spec.
Unset Implicit Arguments.

Require SetInterface.
(** Sets seen as an OrderedType with equality the pointwise equality [Equal] *)
Definition Equal_Equivalence `{OrderedType A} : Equivalence (@Equal A _) :=
  SetInterface.Equal_pw_Equivalence (set A) A (@In _ H).

Lemma Equal_set_eq `{HA : OrderedType A} :
  forall s s', Equal s s' <-> S.set_eq s s'.
Proof.
  intros [s Hs] [s' Hs']; simpl.
  unfold Equal, In; simpl; unfold SetList.set_eq.
  revert s' Hs Hs'; induction s; destruct s'; intros Hs Hs'; split; intro H.
  constructor.
  intro; split; intro abs; inversion abs.
  assert (abs : InA _eq a nil). rewrite H; constructor; auto. inversion abs.
  inversion H.
  assert (abs : InA _eq a nil). rewrite <-H; constructor; auto. inversion abs.
  inversion H.

  inversion Hs; inversion Hs'; subst.
  rewrite Inf_alt in H3 by auto; rewrite Inf_alt in H7 by auto.
  assert (Heq : a === a0).
  assert (Ha : InA _eq a (a0 :: s')). rewrite <- H; constructor; auto.
  assert (Ha' : InA _eq a0 (a :: s)). rewrite H; constructor; auto.
  inversion Ha; inversion Ha'; subst; auto.
  apply False_rec; apply (lt_not_gt (x:=a) (y:=a0)); auto.
  constructor; auto; rewrite <- IHs; auto.
  intro z; split; intro Hz.
  assert (Rz : InA _eq z (a0::s')). rewrite <- H; constructor 2; auto.
  inversion Rz; subst; auto;
    contradiction (lt_not_eq (H3 z Hz)); transitivity a0; auto.
  assert (Rz : InA _eq z (a::s)). rewrite H; constructor 2; auto.
  inversion Rz; subst; auto;
    contradiction (lt_not_eq (H7 z Hz)); transitivity a; auto.

  inversion H; subst; inversion Hs; inversion Hs'; subst.
  rewrite Inf_alt in H4 by auto; rewrite Inf_alt in H9 by auto.
  rewrite <- IHs in H5 by auto.
  intro z; split; intro Hz; inversion Hz; subst.
  constructor; transitivity a; auto.
  constructor 2; rewrite <- H5; auto.
  constructor; transitivity a0; auto.
  constructor 2; rewrite H5; auto.
Qed.

Definition set_lt `{OrderedType A} : relation (set A) := S.set_lt.
Program Definition set_StrictOrder `{OrderedType A} :
  @StrictOrder _ set_lt (@Equal A _) Equal_Equivalence :=
  Build_StrictOrder _ _ _ _ _ _.
Next Obligation.
  intros x y z H1 H2. unfold set_lt, S.set_lt in *.
  now transitivity y.
Qed.
Next Obligation.
  change (~Equal x y); rewrite Equal_set_eq.
  apply lt_not_eq; auto.
Qed.

Definition set_compare `{OrderedType A} : set A -> set A -> comparison :=
  S.set_compare.

Program Instance set_OrderedType `{OrderedType A} :
  SpecificOrderedType (set A) (@Equal A _) := {
    SOT_Equivalence := Equal_Equivalence;
    SOT_lt := set_lt;
    SOT_StrictOrder := set_StrictOrder;
    SOT_cmp := set_compare
}.
Next Obligation.
  change (compare_spec (@Equal _ _) set_lt x y ((this x) =?= (this y))).
  destruct (compare_dec (this x) (this y)); constructor; auto.
  rewrite Equal_set_eq; auto.
Qed.
