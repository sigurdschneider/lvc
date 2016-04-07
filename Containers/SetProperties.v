Require Import SetInterface SetFacts SetDecide.
Set Implicit Arguments.
Unset Strict Implicit.

Generalizable All Variables.
Local Open Scope set_scope.

(** This file corresponds to [FSetProperties.v] in the standard
   library and provides the same results for the typeclass-based
   version.
   *)
Hint Unfold transpose compat_op.

Lemma In_dec : forall `{HF : @FSetSpecs A HA F}
  x s, {In x s} + {~ In x s}.
Proof.
  intros; generalize (mem_iff s x); case (mem x s); intuition.
Qed.

Definition Add `{HF : @FSetSpecs A HA F} x s s' :=
  forall y, In y s' <-> x === y \/ In y s.

Lemma Add_Equal `{HF : @FSetSpecs A HA F} :
  forall x s s', Add x s s' <-> s' [=] add x s.
Proof.
  unfold Add.
  split; intros.
  red; intros.
  rewrite H; clear H.
  fsetdec.
  fsetdec.
Qed.

Ltac expAdd := intros; repeat rewrite Add_Equal in *.

Section BasicProperties.
  Context `{HF : @FSetSpecs elt Helt F}.
  Variable s s' s'' s1 s2 s3 : set elt.
  Variable x x' : elt.

  Lemma equal_refl : s[=]s.
  Proof. fsetdec. Qed.

  Lemma equal_sym : s[=]s' -> s'[=]s.
  Proof. fsetdec. Qed.

  Lemma equal_trans : s1[=]s2 -> s2[=]s3 -> s1[=]s3.
  Proof. fsetdec. Qed.

  Lemma subset_refl : s[<=]s.
  Proof. fsetdec. Qed.

  Lemma subset_trans : s1[<=]s2 -> s2[<=]s3 -> s1[<=]s3.
  Proof. fsetdec. Qed.

  Lemma subset_antisym : s[<=]s' -> s'[<=]s -> s[=]s'.
  Proof. fsetdec. Qed.

  Lemma subset_equal : s[=]s' -> s[<=]s'.
  Proof. fsetdec. Qed.

  Lemma subset_empty : empty[<=]s.
  Proof. fsetdec. Qed.

  Lemma subset_remove_3 : s1[<=]s2 -> remove x s1 [<=] s2.
  Proof. fsetdec. Qed.

  Lemma subset_diff : s1[<=]s3 -> diff s1 s2 [<=] s3.
  Proof. fsetdec. Qed.

  Lemma subset_add_3 : In x s2 -> s1[<=]s2 -> add x s1 [<=] s2.
  Proof. fsetdec. Qed.

  Lemma subset_add_2 : s1[<=]s2 -> s1[<=] add x s2.
  Proof. fsetdec. Qed.

  Lemma in_subset : In x s1 -> s1[<=]s2 -> In x s2.
  Proof. fsetdec. Qed.

  Lemma double_inclusion : s1[=]s2 <-> s1[<=]s2 /\ s2[<=]s1.
  Proof. intuition fsetdec. Qed.

  Lemma empty_is_empty_1 : Empty s -> s[=]empty.
  Proof. fsetdec. Qed.

  Lemma empty_is_empty_2 : s[=]empty -> Empty s.
  Proof. fsetdec. Qed.

  Lemma add_equal : In x s -> add x s [=] s.
  Proof. fsetdec. Qed.

  Lemma add_add : add x (add x' s) [=] add x' (add x s).
  Proof. fsetdec. Qed.

  Lemma remove_equal : ~ In x s -> remove x s [=] s.
  Proof. fsetdec. Qed.

  Lemma Equal_remove : s[=]s' -> remove x s [=] remove x s'.
  Proof. fsetdec. Qed.

  Lemma add_remove : In x s -> add x (remove x s) [=] s.
  Proof. fsetdec. Qed.

  Lemma remove_add : ~In x s -> remove x (add x s) [=] s.
  Proof. fsetdec. Qed.

  Lemma singleton_equal_add : singleton x [=] add x empty.
  Proof. fsetdec. Qed.

  Lemma remove_singleton_empty :
    In x s -> remove x s [=] empty -> singleton x [=] s.
  Proof. fsetdec. Qed. (** Bizarrement long ! *)

  Lemma union_sym : union s s' [=] union s' s.
  Proof. fsetdec. Qed.

  Lemma union_subset_equal : s[<=]s' -> union s s' [=] s'.
  Proof. fsetdec. Qed.

  Lemma union_equal_1 : s[=]s' -> union s s'' [=] union s' s''.
  Proof. fsetdec. Qed.

  Lemma union_equal_2 : s'[=]s'' -> union s s' [=] union s s''.
  Proof. fsetdec. Qed.

  Lemma union_assoc : union (union s s') s'' [=] union s (union s' s'').
  Proof. fsetdec. Qed.

  Lemma add_union_singleton : add x s [=] union (singleton x) s.
  Proof. fsetdec. Qed.

  Lemma union_add : union (add x s) s' [=] add x (union s s').
  Proof. fsetdec. Qed.

  Lemma union_remove_add_1 :
    union (remove x s) (add x s') [=] union (add x s) (remove x s').
  Proof. fsetdec. Qed.

  Lemma union_remove_add_2 :
    In x s -> union (remove x s) (add x s') [=] union s s'.
  Proof. fsetdec. Qed.

  Lemma union_subset_1 : s [<=] union s s'.
  Proof. fsetdec. Qed.

  Lemma union_subset_2 : s' [<=] union s s'.
  Proof. fsetdec. Qed.

  Lemma union_subset_3 : s[<=]s'' -> s'[<=]s'' -> union s s' [<=] s''.
  Proof. fsetdec. Qed.

  Lemma union_subset_4 : s[<=]s' -> union s s'' [<=] union s' s''.
  Proof. fsetdec. Qed.

  Lemma union_subset_5 : s[<=]s' -> union s'' s [<=] union s'' s'.
  Proof. fsetdec. Qed.

  Lemma empty_union_1 : Empty s -> union s s' [=] s'.
  Proof. fsetdec. Qed.

  Lemma empty_union_2 : Empty s -> union s' s [=] s'.
  Proof. fsetdec. Qed.

  Lemma not_in_union : ~In x s -> ~In x s' -> ~In x (union s s').
  Proof. fsetdec. Qed.

  Lemma inter_sym : inter s s' [=] inter s' s.
  Proof. fsetdec. Qed.

  Lemma inter_subset_equal : forall s s', s[<=]s' -> inter s s' [=] s.
  Proof. fsetdec. Qed.

  Lemma inter_equal_1 : s[=]s' -> inter s s'' [=] inter s' s''.
  Proof. fsetdec. Qed.

  Lemma inter_equal_2 : s'[=]s'' -> inter s s' [=] inter s s''.
  Proof. fsetdec. Qed.

  Lemma inter_assoc : inter (inter s s') s'' [=] inter s (inter s' s'').
  Proof. fsetdec. Qed.

  Lemma union_inter_1 :
      inter (union s s') s'' [=] union (inter s s'') (inter s' s'').
  Proof. fsetdec. Qed.

  Lemma union_inter_2 :
      union (inter s s') s'' [=] inter (union s s'') (union s' s'').
  Proof. fsetdec. Qed.

  Lemma inter_add_1 : In x s' -> inter (add x s) s' [=] add x (inter s s').
  Proof. fsetdec. Qed.

  Lemma inter_add_2 : ~ In x s' -> inter (add x s) s' [=] inter s s'.
  Proof. fsetdec. Qed.

  Lemma empty_inter_1 : Empty s -> Empty (inter s s').
  Proof. fsetdec. Qed.

  Lemma empty_inter_2 : Empty s' -> Empty (inter s s').
  Proof. fsetdec. Qed.

  Lemma inter_subset_1 : inter s s' [<=] s.
  Proof. fsetdec. Qed.

  Lemma inter_subset_2 : inter s s' [<=] s'.
  Proof. fsetdec. Qed.

  Lemma inter_subset_3 : s''[<=]s -> s''[<=]s' -> s''[<=] inter s s'.
  Proof. fsetdec. Qed.

  Lemma empty_diff_1 : Empty s -> Empty (diff s s').
  Proof. fsetdec. Qed.

  Lemma empty_diff_2 : Empty s -> diff s' s [=] s'.
  Proof. fsetdec. Qed.

  Lemma diff_subset : diff s s' [<=] s.
  Proof. fsetdec. Qed.

  Lemma diff_subset_equal : s[<=]s' -> diff s s' [=] empty.
  Proof. fsetdec. Qed.

  Lemma remove_diff_singleton : remove x s [=] diff s (singleton x).
  Proof. fsetdec. Qed.

  Lemma diff_inter_empty : inter (diff s s') (inter s s') [=] empty.
  Proof. fsetdec. Qed.

  Lemma diff_inter_all : union (diff s s') (inter s s') [=] s.
  Proof. fsetdec. Qed.

  Lemma Add_add : Add x s (add x s).
  Proof. expAdd; fsetdec. Qed.

  Lemma Add_remove : In x s -> Add x (remove x s) s.
  Proof. expAdd; fsetdec. Qed.

  Lemma union_Add : Add x s s' -> Add x (union s s'') (union s' s'').
  Proof. expAdd; rewrite Add_Equal in H; fsetdec. Qed.

  Lemma inter_Add :
    In x s'' -> Add x s s' -> Add x (inter s s'') (inter s' s'').
  Proof. (* expAdd; rewrite Add_Equal in H0; fsetdec. Qed. *) (** trop lent *)
    expAdd; rewrite Add_Equal in H0; rewrite H0; clear H0; fsetdec.
  Qed.

  Lemma union_Equal : In x s'' -> Add x s s' -> union s s'' [=] union s' s''.
  Proof. (* expAdd; rewrite Add_Equal in H0; fsetdec. Qed.  *) (** trop lent *)
    expAdd; rewrite Add_Equal in H0; rewrite H0; clear H0; fsetdec.
  Qed.

  Lemma inter_Add_2 : ~In x s'' -> Add x s s' -> inter s s'' [=] inter s' s''.
  Proof.
    expAdd; rewrite Add_Equal in H0; rewrite H0; clear H0; fsetdec.
  Qed.

End BasicProperties.

Hint Immediate @equal_sym @add_remove @remove_add @union_sym @inter_sym: set.
Hint Resolve @equal_refl @equal_trans @subset_refl @subset_equal
  @subset_antisym @subset_trans @subset_empty @subset_remove_3 @subset_diff
  @subset_add_3 @subset_add_2 @in_subset @empty_is_empty_1 @empty_is_empty_2
  @add_equal @remove_equal @singleton_equal_add @union_subset_equal
  @union_equal_1 @union_equal_2 @union_assoc @add_union_singleton @union_add
  @union_subset_1 @union_subset_2 @union_subset_3 @inter_subset_equal
  @inter_equal_1 @inter_equal_2 @inter_assoc @union_inter_1 @union_inter_2
  @inter_add_1 @inter_add_2 @empty_inter_1 @empty_inter_2 @empty_union_1
  @empty_union_2 @empty_diff_1 @empty_diff_2 @union_Add @inter_Add
  @union_Equal @inter_Add_2 @not_in_union @inter_subset_1 @inter_subset_2
  @inter_subset_3 @diff_subset @diff_subset_equal @remove_diff_singleton
  @diff_inter_empty @diff_inter_all @Add_add @Add_remove @Equal_remove
  @add_add : set.

(** * Properties of elements *)
Lemma elements_Empty `{HF : @FSetSpecs A HA F} :
  forall s, Empty s <-> elements s = nil.
Proof.
  intros.
  unfold Empty.
  split; intros.
  assert (forall a, ~ List.In a (elements s)).
  red; intros.
  apply (H a).
  rewrite elements_iff.
  rewrite InA_alt; exists a; auto.
  destruct (elements s) as [|e ?]; auto.
  elim (H0 e); simpl; auto.
  red; intros.
  rewrite elements_iff in H0.
  rewrite InA_alt in H0; destruct H0.
  rewrite H in H0; destruct H0 as (_,H0); inversion H0.
Qed.

Lemma elements_empty `{HF : @FSetSpecs A HA F} :
  elements empty = nil.
Proof.
  intros; rewrite <-elements_Empty; auto with set.
Qed.

(** * Conversions between lists and sets *)
Definition of_list `{HF : @FSetSpecs A HA F} (l : list A) :=
  List.fold_right add empty l.

Definition to_list `{HF : @FSetSpecs A HA F} :=
  elements.

Lemma of_list_1 `{HF : @FSetSpecs A HA F} :
  forall l x, In x (of_list l) <-> InA _eq x l.
Proof.
  induction l; simpl; intro x.
  rewrite empty_iff, InA_nil. intuition.
  rewrite add_iff, InA_cons, IHl. intuition.
Qed.

Lemma of_list_2 `{HF : @FSetSpecs A HA F} :
  forall l, equivlistA _eq (to_list (of_list l)) l.
Proof.
  unfold to_list; red; intros.
  rewrite <- elements_iff; apply of_list_1.
Qed.

Lemma of_list_3 `{HF : @FSetSpecs A HA F} :
  forall s, of_list (to_list s) [=] s.
Proof.
  unfold to_list; red; intros.
  rewrite of_list_1; symmetry; apply elements_iff.
Qed.

(** * Fold *)

Section Fold.
  Notation NoDup := (NoDupA _eq).
  Notation InA := (InA _eq).
  Notation t := (set _).

  Context `{HF : @FSetSpecs elt Helt F}.
  Let t := set elt.
  Hint Extern 1 (Equivalence _) => apply OT_Equivalence.

  (** ** Induction principles for fold (contributed by S. Lescuyer) *)

  (** In the following lemma, the step hypothesis is deliberately restricted
      to the precise set s we are considering. *)
  Theorem fold_rec :
    forall (A:Type)(P : t -> A -> Type)(f : elt -> A -> A)(i:A)(s:t),
      (forall s', Empty s' -> P s' i) ->
      (forall x a s' s'', In x s -> ~In x s' -> Add x s' s'' ->
        P s' a -> P s'' (f x a)) ->
      P s (fold f s i).
  Proof.
    intros A P f i s Pempty Pstep.
    rewrite fold_1, <- fold_left_rev_right.
    set (l:=rev (elements s)).
    assert (Pstep' : forall x a s' s'', InA x l -> ~In x s' -> Add x s' s'' ->
      P s' a -> P s'' (f x a)).
    intros; eapply Pstep; eauto.
    rewrite elements_iff, <- InA_rev; auto.
    assert (Hdup : NoDup l) by
      (unfold l; apply NoDupA_rev; eauto using elements_3w).
    assert (Hsame : forall x, In x s <-> InA x l) by
      (unfold l; intros; rewrite elements_iff, InA_rev; intuition).
    clear Pstep; clearbody l; revert s Hsame; induction l.
    (* empty *)
    intros s Hsame; simpl.
    apply Pempty. intro x. rewrite Hsame, InA_nil; intuition.
    (* step *)
    intros s Hsame; simpl.
    apply Pstep' with (of_list l); auto.
    inversion_clear Hdup; rewrite of_list_1; auto.
    red. intros. rewrite Hsame, of_list_1, InA_cons; intuition.
    apply IHl.
    intros; eapply Pstep'; eauto.
    inversion_clear Hdup; auto.
    exact (of_list_1 l).
  Qed.

  (** Same, with [empty] and [add] instead of [Empty] and [Add]. In this
      case, [P] must be compatible with equality of sets *)
  Theorem fold_rec_bis :
    forall (A:Type)(P : t -> A -> Type)(f : elt -> A -> A)(i:A)(s:t),
      (forall s s' a, s[=]s' -> P s a -> P s' a) ->
      (P empty i) ->
      (forall x a s', In x s -> ~In x s' -> P s' a -> P (add x s') (f x a)) ->
      P s (fold f s i).
  Proof.
    intros A P f i s Pmorphism Pempty Pstep.
    apply fold_rec; intros.
    apply Pmorphism with empty; auto with set.
    rewrite Add_Equal in H1; auto with set.
    apply Pmorphism with (add x s'); auto with set.
  Qed.

  Lemma fold_rec_nodep :
    forall (A:Type)(P : A -> Type)(f : elt -> A -> A)(i:A)(s:t),
     P i -> (forall x a, In x s -> P a -> P (f x a)) ->
     P (fold f s i).
  Proof.
    intros; apply (fold_rec_bis (P := fun _ => P)); auto.
  Qed.

  (** [fold_rec_weak] is a weaker principle than [fold_rec_bis] :
      the step hypothesis must here be applicable to any [x].
      At the same time, it looks more like an induction principle,
      and hence can be easier to use. *)
  Lemma fold_rec_weak :
    forall (A:Type)(P : t -> A -> Type)(f : elt -> A -> A)(i:A),
    (forall s s' a, s[=]s' -> P s a -> P s' a) ->
    P empty i ->
    (forall x a s, ~In x s -> P s a -> P (add x s) (f x a)) ->
    forall s, P s (fold f s i).
  Proof.
    intros; apply fold_rec_bis; auto.
  Qed.

  Lemma fold_rel :
    forall (A B:Type)(R : A -> B -> Type)
     (f : elt -> A -> A)(g : elt -> B -> B)(i : A)(j : B)(s : t),
     R i j ->
     (forall x a b, In x s -> R a b -> R (f x a) (g x b)) ->
     R (fold f s i) (fold g s j).
  Proof.
    intros A B R f g i j s Rempty Rstep.
    do 2 rewrite fold_1, <- fold_left_rev_right.
    set (l:=rev (elements s)).
    assert (Rstep' : forall x a b, InA x l -> R a b -> R (f x a) (g x b)) by
      (intros; apply Rstep; auto; rewrite elements_iff, <- InA_rev; auto).
    clearbody l; clear Rstep s.
    induction l; simpl; auto.
  Qed.

  (** From the induction principle on [fold], we can deduce some general
      induction principles on sets. *)
  Lemma set_induction :
    forall P : t -> Type,
      (forall s, Empty s -> P s) ->
      (forall s s', P s -> forall x, ~In x s -> Add x s s' -> P s') ->
      forall s, P s.
  Proof.
    intros; apply
      (@fold_rec _ (fun s _ => P s) (fun _ _ => tt) tt s); eauto.
  Qed.

  Lemma set_induction_bis :
    forall P : t -> Type,
      (forall s s', s [=] s' -> P s -> P s') ->
      P empty ->
      (forall x s, ~In x s -> P s -> P (add x s)) ->
      forall s, P s.
  Proof.
    intros.
    apply (@fold_rec_bis _ (fun s _ => P s) (fun _ _ => tt) tt s);
      eauto.
  Qed.

  (** [fold] can be used to reconstruct the same initial set. *)
  Lemma fold_identity : forall s, fold add s empty [=] s.
  Proof.
    intros.
    apply fold_rec with (P:=fun s acc => acc[=]s); auto with set.
    intros. rewrite H2; rewrite Add_Equal in H1; auto with set.
  Qed.

  (** ** Alternative (weaker) specifications for [fold] *)

  (** When [FSets] was first designed, the order in which Ocaml's [Set.fold]
      takes the set elements was unspecified. This specification reflects
      this fact:
  *)
  Lemma fold_0 :
    forall s (A : Type) (i : A) (f : elt -> A -> A),
      exists l : list elt,
        NoDup l /\
        (forall x : elt, In x s <-> InA x l) /\
        fold f s i = fold_right f i l.
  Proof.
    intros; exists (rev (elements s)); split.
    apply NoDupA_rev; eauto with set.
    split; intros.
    rewrite elements_iff; do 2 rewrite InA_alt.
    split; destruct 1;
      generalize (In_rev (elements s) x0); exists x0; intuition.
    rewrite fold_left_rev_right.
    apply fold_1.
  Qed.

  (** An alternate (and previous) specification for [fold] was based on
      the recursive structure of a set. It is now lemmas [fold_1] and
      [fold_2]. *)
  Lemma fold_1 :
   forall s (A : Type) {eqA : A -> A -> Prop}
     `{st : Equivalence A eqA} (i : A) (f : elt -> A -> A),
   Empty s -> eqA (fold f s i) i.
  Proof.
    unfold Empty; intros; destruct (fold_0 s i f) as (l,(H1, (H2, H3))).
    rewrite H3; clear H3.
    generalize H H2; clear H H2; case l; simpl; intros.
    reflexivity.
    elim (H e).
    elim (H2 e); intuition.
  Qed.

  Lemma fold_2 :
   forall s s' x (A : Type) {eqA : A -> A -> Prop}
     `{st : Equivalence A eqA} (i : A) (f : elt -> A -> A)
     `{Proper _ (_eq ==> eqA ==> eqA) f},
   transpose eqA f ->
   ~ In x s -> Add x s s' -> eqA (fold f s' i) (f x (fold f s i)).
  Proof.
    intros; destruct (fold_0 s i f) as (l,(Hl, (Hl1, Hl2)));
      destruct (fold_0 s' i f) as (l',(Hl', (Hl'1, Hl'2))).
    rewrite Hl2; rewrite Hl'2; clear Hl2 Hl'2.
    apply fold_right_add with (eqA:=_eq)(eqB:=eqA); auto.
    rewrite <- Hl1; auto.
    intros a; rewrite InA_cons; rewrite <- Hl1; rewrite <- Hl'1;
      rewrite (H2 a); intuition.
  Qed.

  (** In fact, [fold] on empty sets is more than equivalent to
      the initial element, it is Leibniz-equal to it. *)

  Lemma fold_1b :
    forall s (A : Type)(i : A) (f : elt -> A -> A),
      Empty s -> (fold f s i) = i.
  Proof.
    intros.
    rewrite fold_1; auto.
  Qed.

  Section Fold_More.
    Variable A : Type.
    Context `{st : Equivalence A eqA}.
    Variable (f:elt->A->A).
    Context {Comp : Proper (_eq ==> eqA ==> eqA) f}.
    Hypothesis Ass : transpose eqA f.

    Lemma fold_commutes :
      forall i s x, eqA (fold f s (f x i)) (f x (fold f s i)).
    Proof.
      intros.
      apply fold_rel with (R:=fun u v => eqA u (f x v)); intros.
      reflexivity.
      transitivity (f x0 (f x b)); auto; rewrite H0; reflexivity.
    Qed.

    (** ** Fold is a morphism *)
    Lemma fold_init : forall i i' s, eqA i i' -> eqA (fold f s i) (fold f s i').
    Proof.
      intros. apply fold_rel with (R:=eqA); auto.
      intros; rewrite H1; reflexivity.
    Qed.

    Lemma fold_equal :
      forall i s s', s[=]s' -> eqA (fold f s i) (fold f s' i).
    Proof.
      intros i s; pattern s; apply set_induction; clear s; intros.
      transitivity i.
      apply fold_1; auto.
      symmetry; apply fold_1; auto.
      rewrite <- H0; auto.
      transitivity (f x (fold f s i)).
      apply (fold_2 (eqA := eqA)); auto.
      symmetry; apply (fold_2 (eqA := eqA)); auto.
      unfold Add in *; intros.
      rewrite <- H2; auto.
    Qed.

    (** ** Fold and other set operators *)

    Lemma fold_empty : forall i, fold f empty i = i.
    Proof.
      intros; apply fold_1b; auto with set.
    Qed.

    Lemma fold_add : forall i s x, ~In x s ->
      eqA (fold f (add x s) i) (f x (fold f s i)).
    Proof.
      intros; apply (fold_2 (st:=st)); auto with set.
    Qed.

    Lemma add_fold :
      forall i s x, In x s -> eqA (fold f (add x s) i) (fold f s i).
    Proof.
      intros; apply fold_equal; auto with set.
    Qed.

    Lemma remove_fold_1 :
      forall i s x, In x s -> eqA (f x (fold f (remove x s) i)) (fold f s i).
    Proof.
      intros.
      symmetry.
      apply (fold_2 (st:=st)); auto with set.
    Qed.

    Lemma remove_fold_2 :
      forall i s x, ~In x s -> eqA (fold f (remove x s) i) (fold f s i).
    Proof.
      intros.
      apply fold_equal; auto with set.
    Qed.

    Lemma fold_union_inter :
      forall i s s',
        eqA (fold f (union s s') (fold f (inter s s') i))
        (fold f s (fold f s' i)).
    Proof.
      intros; pattern s; apply set_induction; clear s; intros.
      transitivity (fold f s' (fold f (inter s s') i)).
      apply fold_equal; auto with set.
      transitivity (fold f s' i).
      apply fold_init; auto.
      apply fold_1; auto with set.
      symmetry; apply fold_1; auto.
      rename s'0 into s''.
      destruct (In_dec x s').
      (* In x s' *)
      transitivity
        (fold f (union s'' s') (f x (fold f (inter s s') i))); auto with set.
      apply fold_init; auto.
      apply (fold_2 (eqA:=eqA)); auto with set.
      rewrite inter_iff; intuition.
      transitivity (f x (fold f s (fold f s' i))).
      transitivity (fold f (union s s') (f x (fold f (inter s s') i))).
      apply fold_equal; auto.
      apply equal_sym; apply union_Equal with x; auto with set.
      transitivity (f x (fold f (union s s') (fold f (inter s s') i))).
      apply fold_commutes; auto.
      apply Comp; auto.
      symmetry; apply (fold_2 (eqA:=eqA)); auto.
      (* ~(In x s') *)
      transitivity (f x (fold f (union s s') (fold f (inter s'' s') i))).
      apply (fold_2 (eqA:=eqA)); auto with set.
      transitivity (f x (fold f (union s s') (fold f (inter s s') i))).
      apply Comp;auto.
      apply fold_init;auto.
      apply fold_equal;auto.
      apply equal_sym; apply inter_Add_2 with x; auto with set.
      transitivity (f x (fold f s (fold f s' i))).
      apply Comp; auto.
      symmetry; apply (fold_2 (eqA:=eqA)); auto.
    Qed.

    Lemma fold_diff_inter :
      forall i s s',
        eqA (fold f (diff s s') (fold f (inter s s') i)) (fold f s i).
    Proof.
      intros.
      transitivity (fold f (union (diff s s') (inter s s'))
        (fold f (inter (diff s s') (inter s s')) i)).
      symmetry; apply fold_union_inter; auto.
      transitivity (fold f s (fold f (inter (diff s s') (inter s s')) i)).
      apply fold_equal; auto with set.
      apply fold_init; auto.
      apply (fold_1 (eqA:=eqA)); auto with set.
    Qed.

    Lemma fold_union :
      forall i s s', (forall x, ~(In x s/\In x s')) ->
        eqA (fold f (union s s') i) (fold f s (fold f s' i)).
    Proof.
      intros.
      transitivity (fold f (union s s') (fold f (inter s s') i)).
      apply fold_init; auto.
      symmetry; apply fold_1; auto with set.
      unfold Empty; intro a; generalize (H a); set_iff; tauto.
      apply fold_union_inter; auto.
    Qed.
  End Fold_More.

  Lemma fold_plus :
   forall s p, fold (fun _ => S) s p = fold (fun _ => S) s 0 + p.
  Proof.
    intros. apply fold_rel with (R:=fun u v => u = v + p); simpl; auto.
  Qed.
End Fold.

(** * Cardinal *)

(** ** Characterization of cardinal in terms of fold *)

Lemma cardinal_fold `{HF : @FSetSpecs elt Helt F} :
  forall s, cardinal s = fold (fun _ => S) s 0.
Proof.
  intros; rewrite cardinal_1; rewrite SetInterface.fold_1; auto.
  symmetry; apply fold_left_length; auto.
Qed.

(** ** Old specifications for [cardinal]. *)

Lemma cardinal_0 `{HF : @FSetSpecs elt Helt F} :
  forall s, exists l : list elt,
    NoDupA _eq l /\
    (forall x : elt, In x s <-> InA _eq x l) /\
    cardinal s = length l.
Proof.
  intros; exists (elements s); intuition.
  apply cardinal_1.
Qed.

Lemma cardinal_1 `{HF : @FSetSpecs elt Helt F} :
  forall s, Empty s -> cardinal s = 0.
Proof.
  intros; rewrite cardinal_fold; apply fold_1; auto.
Qed.

Lemma cardinal_2 `{HF : @FSetSpecs elt Helt F} :
  forall s s' x, ~ In x s -> Add x s s' -> cardinal s' = S (cardinal s).
Proof.
  intros; do 2 rewrite cardinal_fold.
  change S with ((fun _ => S) x).
  apply (fold_2 (eqA:=@eq _)) ; auto.
  repeat intro; vm_compute; congruence.
Qed.

(** ** Cardinal and (non-)emptiness *)

Lemma cardinal_Empty `{HF : @FSetSpecs elt Helt F} :
  forall s, Empty s <-> cardinal s = 0.
Proof.
  intros.
  rewrite elements_Empty, SetInterface.cardinal_1.
  destruct (elements s); intuition; discriminate.
Qed.

Lemma cardinal_inv_1 `{HF : @FSetSpecs elt Helt F} :
  forall s, cardinal s = 0 -> Empty s.
Proof.
  intros; rewrite cardinal_Empty; auto.
Qed.
Hint Resolve @cardinal_inv_1.

Lemma cardinal_inv_2 `{HF : @FSetSpecs elt Helt F} :
  forall s n, cardinal s = S n -> { x : elt | In x s }.
Proof.
  intros; rewrite SetInterface.cardinal_1 in H.
  generalize (elements_2 (s:=s)).
  destruct (elements s); try discriminate.
  exists e; auto.
Qed.

Lemma cardinal_inv_2b `{HF : @FSetSpecs elt Helt F} :
  forall s, cardinal s <> 0 -> { x : elt | In x s }.
Proof.
  intros s;
    generalize (@cardinal_inv_2 _ _ _ _ s); destruct cardinal;
    [intuition|eauto].
Qed.

(** ** Cardinal is a morphism *)

Lemma Equal_cardinal `{HF : @FSetSpecs elt Helt F} :
  forall s s', s[=]s' -> cardinal s = cardinal s'.
Proof.
  symmetry.
  remember (cardinal s) as n; symmetry in Heqn; revert s s' Heqn H.
  induction n; intros.
  apply cardinal_1; rewrite <- H; auto.
  destruct (cardinal_inv_2 Heqn) as (x,H2).
  revert Heqn.
  rewrite (cardinal_2 (s:=remove x s) (s':=s) (x:=x)); auto with set.
  rewrite (cardinal_2 (s:=remove x s') (s':=s') (x:=x)); eauto with set.
Qed.

Instance cardinal_m `{HF : @FSetSpecs elt Helt F} :
  Proper (Equal ==> @eq nat) cardinal.
Proof.
  repeat intro; auto using Equal_cardinal.
Qed.

Hint Resolve @Add_add @Add_remove @Equal_remove @cardinal_inv_1 @Equal_cardinal.

(** ** Cardinal and set operators *)

Lemma empty_cardinal `{HF : @FSetSpecs elt Helt F} :
  cardinal empty = 0.
Proof.
  intros; rewrite cardinal_fold; apply fold_1; auto with set.
Qed.

Hint Immediate @empty_cardinal @cardinal_1 : set.

Lemma singleton_cardinal `{HF : @FSetSpecs elt Helt F} :
  forall x, cardinal (singleton x) = 1.
Proof.
  intros.
  rewrite (singleton_equal_add x).
  replace 0 with (cardinal empty); auto with set.
  apply cardinal_2 with x; auto with set. fsetdec.
Qed.

Hint Resolve @singleton_cardinal: set.

Lemma diff_inter_cardinal `{HF : @FSetSpecs elt Helt F} :
  forall s s', cardinal (diff s s') + cardinal (inter s s') = cardinal s .
Proof.
  intros; do 3 rewrite cardinal_fold.
  rewrite <- fold_plus.
  apply fold_diff_inter with (eqA:=@Logic.eq nat); auto.
  repeat intros; vm_compute; congruence.
Qed.

Lemma union_cardinal `{HF : @FSetSpecs elt Helt F} :
  forall s s', (forall x, ~(In x s/\In x s')) ->
    cardinal (union s s')=cardinal s+cardinal s'.
Proof.
  intros; do 3 rewrite cardinal_fold.
  rewrite <- fold_plus.
  apply (fold_union (eqA:=@eq _)); auto.
  repeat intros; vm_compute; congruence.
Qed.

Lemma subset_cardinal `{HF : @FSetSpecs elt Helt F} :
  forall s s', s[<=]s' -> cardinal s <= cardinal s' .
Proof.
  intros.
  rewrite <- (diff_inter_cardinal s' s).
  rewrite (inter_sym s' s).
  rewrite (inter_subset_equal H); auto with arith.
Qed.

Lemma subset_cardinal_lt `{HF : @FSetSpecs elt Helt F} :
  forall s s' x, s[<=]s' -> In x s' -> ~In x s -> cardinal s < cardinal s'.
Proof.
  intros.
  rewrite <- (diff_inter_cardinal s' s).
  rewrite (inter_sym s' s).
  rewrite (inter_subset_equal H).
  generalize (@cardinal_inv_1 _ _ _ _ (diff s' s)).
  destruct (cardinal (diff s' s)).
  intro H2; destruct (H2 (refl_equal _) x).
  set_iff; auto.
  intros _.
  change (0 + cardinal s < S n + cardinal s).
  apply Plus.plus_lt_le_compat; auto with arith.
Qed.

Theorem union_inter_cardinal `{HF : @FSetSpecs elt Helt F} :
  forall s s', cardinal (union s s') + cardinal (inter s s') =
    cardinal s  + cardinal s' .
Proof.
  intros.
  do 4 rewrite cardinal_fold.
  do 2 rewrite <- fold_plus.
  apply fold_union_inter with (eqA:=@Logic.eq nat); auto.
  repeat intros; vm_compute; congruence.
Qed.

Lemma union_cardinal_inter `{HF : @FSetSpecs elt Helt F} :
  forall s s', cardinal (union s s') =
    cardinal s + cardinal s' - cardinal (inter s s').
Proof.
  intros.
  rewrite <- union_inter_cardinal.
  rewrite Plus.plus_comm.
  auto with arith.
Qed.

Lemma union_cardinal_le `{HF : @FSetSpecs elt Helt F} :
   forall s s', cardinal (union s s') <= cardinal s  + cardinal s'.
Proof.
  intros; generalize (union_inter_cardinal s s').
  intros; rewrite <- H; auto with arith.
Qed.

Lemma add_cardinal_1 `{HF : @FSetSpecs elt Helt F} :
  forall s x, In x s -> cardinal (add x s) = cardinal s.
Proof.
  auto with set.
Qed.

Lemma add_cardinal_2 `{HF : @FSetSpecs elt Helt F} :
  forall s x, ~In x s -> cardinal (add x s) = S (cardinal s).
Proof.
  intros.
  do 2 rewrite cardinal_fold.
  change S with ((fun _ => S) x);
    apply fold_add with (eqA:=@Logic.eq nat); auto.
  repeat intros; vm_compute; congruence.
Qed.

Lemma remove_cardinal_1 `{HF : @FSetSpecs elt Helt F} :
  forall s x, In x s -> S (cardinal (remove x s)) = cardinal s.
Proof.
  intros.
  do 2 rewrite cardinal_fold.
  change S with ((fun _ =>S) x).
  apply remove_fold_1 with (eqA:=@Logic.eq nat); auto.
  repeat intros; vm_compute; congruence.
Qed.

Lemma remove_cardinal_2 `{HF : @FSetSpecs elt Helt F} :
  forall s x, ~In x s -> cardinal (remove x s) = cardinal s.
Proof.
  auto with set.
Qed.

Hint Resolve @subset_cardinal @union_cardinal @add_cardinal_1 @add_cardinal_2.

(** Now comes some properties specific to the element ordering,
   invalid for Weak Sets. *)
(** First, a specialized version of SortA_equivlistA_eqlistA: *)
Lemma sort_equivlistA_eqlistA
  `{HF : @FSetSpecs elt Helt F} :
  forall l l' : list elt, sort _lt l -> sort _lt l' ->
    equivlistA _eq l l' -> eqlistA _eq l l'.
Proof.
  intros; apply SortA_equivlistA_eqlistA with _lt;
    eauto with typeclass_instances.
Qed.

Definition gtb `{Helt : OrderedType elt} (x y : elt) := x >> y.
Definition leb `{Helt : OrderedType elt} (x : elt) :=
  fun y => negb (x >> y).

Definition elements_lt
  `{HF : @FSetSpecs elt Helt F} x s :=
  List.filter (gtb x) (elements s).
Definition elements_ge
  `{HF : @FSetSpecs elt Helt F} x s :=
  List.filter (leb x) (elements s).

Lemma gtb_1 `{Helt : OrderedType elt} : forall x y, gtb x y = true <-> y <<< x.
Proof.
  intros; unfold gtb; destruct (gt_dec x y); intuition;
    try discriminate; order.
Qed.

Lemma leb_1 `{Helt : OrderedType elt} :
  forall x y, leb x y = true <-> ~y <<< x.
Proof.
  intros; unfold leb, gtb; destruct (gt_dec x y); intuition;
    try discriminate; order.
Qed.

Instance gtb_m `{Helt : OrderedType elt} :
  forall x, Proper (_eq ==> @eq bool) (gtb x).
Proof.
  red; intros x a b H.
  unfold gtb; destruct (gt_dec x a); destruct (gt_dec x b);
    auto; rewrite H in H0; contradiction.
Qed.
Corollary gtb_compat `{Helt : OrderedType elt} :
  forall x, compat_bool _eq (gtb x).
Proof.
  repeat intro; rewrite H; reflexivity.
Qed.

Instance leb_m `{Helt : OrderedType elt} :
  forall x, Proper (_eq ==> @eq bool) (leb x).
Proof.
  red; intros x a b H; unfold leb.
  f_equal; apply gtb_m; auto.
Qed.
Corollary leb_compat `{Helt : OrderedType elt} :
  forall x, compat_bool _eq (leb x).
Proof.
  repeat intro; rewrite H; reflexivity.
Qed.
Hint Resolve @leb_compat @gtb_compat.

(* Ltac normalize_notations := *)
(*   match goal with *)
(*  | H : ?R ?x ?y |- _ => *)
(*    progress ((change (x === y) in H) || (change (x <<< y) in H) || *)
(*      (change (x >>> y) in H)); normalize_notations *)
(*  | H : ~(?R ?x ?y) |- _ => *)
(*    progress ((change (x =/= y) in H) || (change (~ x <<< y) in H) || *)
(*      (change (~ y <<< x) in H)); normalize_notations *)
(*  | |- ?R ?x ?y => *)
(*    progress (change (x === y) || change (x <<< y) || change (y <<< x)) *)
(*  | |- ~?R ?x ?y => *)
(*    progress (change (x =/= y) || change (~x <<< y) || change (~y <<< x)) *)
(*  | _ => idtac *)
(*   end. *)

Lemma elements_split
  `{HF : @FSetSpecs elt Helt F} :
  forall x s, elements s = (elements_lt x s ++ elements_ge x s)%list.
Proof.
  unfold elements_lt, elements_ge, leb; intros.
  eapply (@filter_split _ _eq _ _lt); eauto with set typeclass_instances.
  intros; destruct (gt_dec x x0); destruct (gt_dec x y); try discriminate.
  order.
Qed.

Lemma elements_Add
  `{HF : @FSetSpecs elt Helt F} :
  forall s s' x, ~In x s -> Add x s s' ->
    eqlistA _eq (elements s') (elements_lt x s ++ x :: elements_ge x s)%list.
Proof.
  assert (Z : forall x, Proper (_eq ==> eq) (leb x)).
  repeat intro; unfold leb;
    destruct (gt_dec x x0); destruct (gt_dec x y); order.
  assert (Z' : forall x, Proper (_eq ==> eq) (gtb x)).
  repeat intro; unfold gtb;
    destruct (gt_dec x x0); destruct (gt_dec x y); order.
  intros; unfold elements_ge, elements_lt.
  apply sort_equivlistA_eqlistA; auto with set.
  apply (@SortA_app _ _eq); auto.
  apply (@filter_sort _ _eq); auto with set; eauto with set; intros; order.
  constructor; auto.
  apply (@filter_sort _ _eq); auto with set; eauto with set;
    try (intros; order).
  rewrite Inf_alt by
    (apply (@filter_sort _ _eq); eauto with set; intros; order).
  intros; rewrite filter_InA in H1; auto; destruct H1.
  rewrite leb_1 in H2.
  rewrite <- elements_iff in H1.
  assert (x =/= y). intro abs; apply H; rewrite abs; auto. order.
  intros.
  rewrite filter_InA in H1; auto; destruct H1.
  rewrite gtb_1 in H3.
  inversion_clear H2.
  order.
  rewrite filter_InA in H4; auto; destruct H4.
  rewrite leb_1 in H4.
  order.
  red; intros a.
  rewrite InA_app_iff; auto. rewrite InA_cons.
  rewrite !filter_InA; auto.
  do 2 rewrite <- elements_iff.
  rewrite leb_1; rewrite gtb_1.
  rewrite (H0 a); intuition.
  destruct (compare_dec a x); intuition.
  right; right; split; auto.
  order.
Qed.

Definition Above `{HF : @FSetSpecs elt Helt F}
  x s := forall y, In y s -> y <<< x.
Definition Below `{HF : @FSetSpecs elt Helt F}
  x s := forall y, In y s -> x <<< y.

Lemma elements_Add_Above
  `{HF : @FSetSpecs elt Helt F} :
  forall s s' x, Above x s -> Add x s s' ->
    eqlistA _eq (elements s') (elements s ++ x::nil)%list.
Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with set.
  apply (@SortA_app _ _eq); auto with set.
  intros.
  inversion_clear H2.
  rewrite <- elements_iff in H1.
  apply lt_eq with x; auto.
  inversion H3.
  red; intros a.
  rewrite InA_app_iff; auto; rewrite InA_cons; rewrite InA_nil.
  do 2 rewrite <- elements_iff; rewrite (H0 a); intuition.
Qed.

Lemma elements_Add_Below
  `{HF : @FSetSpecs elt Helt F} :
  forall s s' x, Below x s -> Add x s s' ->
    eqlistA _eq (elements s') (x::elements s).
Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with set.
  change (sort _lt ((x::nil) ++ elements s)).
  apply (@SortA_app _ _eq); auto with set.
  intros.
  inversion_clear H1.
  rewrite <- elements_iff in H2.
  apply eq_lt with x; auto.
  inversion H3.
  red; intros a.
  rewrite InA_cons.
  do 2 rewrite <- elements_iff; rewrite (H0 a); intuition.
Qed.

(** Two other induction principles on sets: we can be more restrictive
   on the element we add at each step.  *)
Lemma set_induction_max
  `{HF : @FSetSpecs elt Helt F} :
  forall P : set elt -> Type,
    (forall s, Empty s -> P s) ->
    (forall s s', P s -> forall x, Above x s -> Add x s s' -> P s') ->
    forall s, P s.
Proof.
  intros; remember (cardinal s) as n; revert s Heqn; induction n; intros; auto.
  case_eq (max_elt s); intros.
  apply X0 with (remove e s) e; auto with set.
  apply IHn.
  assert (S n = S (cardinal (remove e s))).
  rewrite Heqn; apply cardinal_2 with e; auto with set.
  inversion H0; auto.
  red; intros.
  rewrite remove_iff in H0; destruct H0.
  generalize (@max_elt_2 _ _ _ _ s e y H H0); order.

  assert (H0:=max_elt_3 H).
  rewrite cardinal_Empty in H0; rewrite H0 in Heqn; inversion Heqn.
Qed.

Lemma set_induction_min
  `{HF : @FSetSpecs elt Helt F} :
  forall P : set elt -> Type,
    (forall s, Empty s -> P s) ->
    (forall s s', P s -> forall x, Below x s -> Add x s s' -> P s') ->
    forall s, P s.
Proof.
  intros; remember (cardinal s) as n; revert s Heqn; induction n; intros; auto.
  case_eq (min_elt s); intros.
  apply X0 with (remove e s) e; auto with set.
  apply IHn.
  assert (S n = S (cardinal (remove e s))).
   rewrite Heqn; apply cardinal_2 with e; auto with set.
  inversion H0; auto.
  red; intros.
  rewrite remove_iff in H0; destruct H0.
  generalize (@min_elt_2 _ _ _ _ s e y H H0); order.

  assert (H0:=min_elt_3 H).
  rewrite cardinal_Empty in H0; auto; rewrite H0 in Heqn; inversion Heqn.
Qed.

(** More properties of [fold] : behavior with respect to Above/Below *)
Lemma fold_3
  `{HF : @FSetSpecs elt Helt F} :
  forall s s' x (A : Type) (eqA : A -> A -> Prop)
    (st : Equivalence eqA) (i : A)
    (f : elt -> A -> A) `{Proper _ (_eq ==> eqA ==> eqA) f},
    Above x s -> Add x s s' -> eqA (fold f s' i) (f x (fold f s i)).
Proof.
  intros.
  do 2 rewrite SetInterface.fold_1.
  do 2 rewrite <- fold_left_rev_right.
  change (f x (fold_right f i (rev (elements s)))) with
    (fold_right f i (rev (x::nil)++rev (elements s))).
  apply (@fold_right_eqlistA _ _eq A eqA st); auto.
  rewrite <- distr_rev.
  apply eqlistA_rev.
  apply elements_Add_Above; auto.
Qed.

Lemma fold_4
  `{HF : @FSetSpecs elt Helt F} :
  forall s s' x (A : Type) (eqA : A -> A -> Prop)
    (st : Equivalence eqA) (i : A)
    (f : elt -> A -> A) `{Proper _ (_eq ==> eqA ==> eqA) f},
    Below x s -> Add x s s' -> eqA (fold f s' i) (fold f s (f x i)).
Proof.
  intros.
  do 2 rewrite SetInterface.fold_1.
  set (g:=fun (a : A) (e : elt) => f e a).
  change (eqA (fold_left g (elements s') i) (fold_left g (x::elements s) i)).
  unfold g.
  do 2 rewrite <- fold_left_rev_right.
  apply (@fold_right_eqlistA elt _eq A eqA st); auto.
  apply eqlistA_rev.
  apply elements_Add_Below; auto.
Qed.

(** The following results have already been proved earlier, *)
(*    but we can now prove them with one hypothesis less: *)
(*    no need for [(transpose eqA f)]. *)
Section FoldOpt.
  Lemma fold_equal_ord
    `{HF : @FSetSpecs elt Helt F} :
    forall (A : Type) {eqA : A -> A -> Prop}
     `{st : Equivalence A eqA} (i : A) (f : elt -> A -> A)
     `{Proper _ (_eq ==> eqA ==> eqA) f},
     forall i s s', s[=]s' -> eqA (fold f s i) (fold f s' i).
  Proof.
    intros; do 2 rewrite SetInterface.fold_1.
    do 2 rewrite <- fold_left_rev_right.
    apply (@fold_right_eqlistA _ _eq A eqA st); auto.
    apply eqlistA_rev.
    apply sort_equivlistA_eqlistA; auto with set.
    red; intro a; do 2 rewrite <- elements_iff; auto.
  Qed.

  Lemma add_fold_ord
    `{HF : @FSetSpecs elt Helt F} :
    forall (A : Type) {eqA : A -> A -> Prop}
     `{st : Equivalence A eqA} (i : A) (f : elt -> A -> A)
     `{Proper _ (_eq ==> eqA ==> eqA) f},
     forall i s x, In x s -> eqA (fold f (add x s) i) (fold f s i).
  Proof.
    intros; apply (fold_equal_ord (st:=st)); auto with set.
  Qed.

  Lemma remove_fold_2_ord
    `{HF : @FSetSpecs elt Helt F} :
    forall (A : Type) {eqA : A -> A -> Prop}
     `{st : Equivalence A eqA} (i : A) (f : elt -> A -> A)
     `{Proper _ (_eq ==> eqA ==> eqA) f},
     forall i s x, ~In x s -> eqA (fold f (remove x s) i) (fold f s i).
  Proof.
    intros; apply (fold_equal_ord (st:=st)); auto with set.
  Qed.
End FoldOpt.

(** An alternative version of [choose_3] *)
Lemma choose_equal
  `{HF : @FSetSpecs elt Helt F} :
  forall s s', Equal s s' ->
  match choose s, choose s' with
    | Some x, Some x' => x === x'
    | None, None => True
    | _, _ => False
  end.
Proof.
  intros s s' H.
  generalize (choose_1 (s:=s))(choose_2 (s:=s))
    (choose_1 (s:=s'))(choose_2 (s:=s'))(choose_3 (s:=s) (s':=s'));
    destruct (choose s); destruct (choose s'); simpl; intuition.
  apply H5 with e; rewrite <-H; auto.
  apply H5 with e; rewrite H; auto.
Qed.

(** * Facts about [For_all] and [Exists]: since these predicates
   quantify over a finite set, they are dual in a classical way when
   they are applied to decidable properties (such as in [for_all]
   and [exists]). *)
Section For_all_Exists.
  Context `{HF : @FSetSpecs elt Helt F}.
  Variable f : elt -> bool.
  Context `{Hf : Proper _ (_eq ==> @eq bool) f}.

  Property For_all_Exists_iff : forall s,
    For_all (fun x => f x = true) s <-> ~ (Exists (fun x => f x = false) s).
  Proof.
    apply set_induction_bis; unfold For_all; unfold Exists; intros;
      split; intros; try intros [w Hw].
    (* morphism *)
    rewrite <- H in Hw.
    apply (proj1 H0); [| exists w; exact Hw].
    intro y; rewrite H; exact (H1 y).
    apply (proj2 H0); [| rewrite H; assumption].
    intros [y Hy]; apply H1; exists y; rewrite <- H; assumption.
    (* init *)
    contradiction (empty_1 (proj1 Hw)).
    contradiction (empty_1 H0).
    (* step *)
    apply (proj1 H0).
    intros; auto with set.
    destruct Hw as [Hw1 Hw2]; exists w; split; auto.
    apply add_3 with x; auto; intro abs.
    rewrite (H1 w) in Hw2; [discriminate | rewrite abs; auto with set].
    rewrite add_iff in H2; destruct H2 as [Hx | Hs].
    rewrite <- Hx; case_eq (f x); auto; intro.
    contradiction H1; exists x; split; [auto with set | assumption].
    apply (proj2 H0); auto.
    intros [w Hw]; apply H1; exists w; intuition (auto with set).
  Qed.

  Property Exists_For_all_iff : forall s,
     Exists (fun x => f x = true) s <-> ~ For_all (fun x => f x = false) s.
  Proof.
    apply set_induction_bis; unfold For_all; unfold Exists; intros;
      split; try intros [w Hw]; try intro Hall.
    (* morphism *)
    rewrite <- H in Hw.
    apply (proj1 H0); [exists w; exact Hw|].
    intro y; rewrite H; exact (Hall y).
    destruct (proj2 H0) as [w Hw].
    intro Z; apply Hall; intros; apply Z; rewrite H; auto.
    exists w; rewrite <- H; auto.
    (* init *)
    contradiction (empty_1 (proj1 Hw)).
    contradiction Hall; intros; contradiction (empty_1 H).
    (* step *)
    apply (proj1 H0).
    destruct Hw as [Hw1 Hw2]; exists w; split; auto.
    apply add_3 with x; auto; intro abs.
    rewrite (Hall w) in Hw2; [discriminate | rewrite abs; auto with set].
    intros; auto with set.
    case_eq (f x); intros.
    exists x; split; auto with set.
    destruct (proj2 H0) as [w Hw].
    intro Z; apply Hall; intros.
    rewrite add_iff in H2; destruct H2; auto. rewrite <- H2; assumption.
    exists w; intuition (auto with set).
  Qed.
End For_all_Exists.

(** * More precise reflexive view of [for_all] and [_exists] than the one
   in [SetFacts] using the duality results above. *)
Section for_all_exists_spec.
  Context `{HF : @FSetSpecs elt Helt F}.
  Variable s : set elt.
  Variable f : elt -> bool.

  CoInductive for_all_spec : bool -> Prop :=
  | for_all_spec_true :
    forall (Htrue : For_all (fun x => f x = true) s), for_all_spec true
  | for_all_spec_false :
    forall w (Hin : In w s) (Hw : f w = false), for_all_spec false.
  CoInductive exists_spec : bool -> Prop :=
  | exists_spec_true :
    forall w (Hin : In w s) (Hw : f w = true), exists_spec true
  | exists_spec_false :
    forall (Hfalse : For_all (fun x => f x = false) s), exists_spec false.

  Context `{Hf : Proper _ (_eq ==> @eq bool) f}.
  Property for_all_dec2 : for_all_spec (for_all f s).
  Proof.
    destruct (@for_all_dec _ _ _ _ s f Hf).
    constructor; assumption.
    set (negf := fun x => negb (f x)).
    assert (Exists (fun x => negf x = true) s).
    rewrite Exists_For_all_iff.
    intro abs; apply Hfalse; repeat intro; generalize (abs x H).
    unfold negf; destruct (f x); auto.
    repeat intro; unfold negf; rewrite H; reflexivity.
    destruct H as [w [Hw1 Hw2]]; constructor 2 with w; auto.
    unfold negf in Hw2; destruct (f w); auto.
  Qed.
  Property exists_dec2 : exists_spec (exists_ f s).
  Proof.
    destruct (@exists_dec _ _ _ _ s f Hf).
    destruct Htrue as [w Hw]; constructor 1 with w; tauto.
    constructor 2.
    repeat intro; case_eq (f x); auto; intros.
    contradiction Hfalse; exists x; tauto.
  Qed.
End for_all_exists_spec.