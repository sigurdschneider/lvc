Require Import SetInterface Program.Basics.
Set Implicit Arguments.
Unset Strict Implicit.

Generalizable All Variables.
Local Open Scope set_scope.

(** This file corresponds to [FSetFacts.v] in the standard library.
   There are additional specifications, for boolean functions in particular,
   in the [InductiveSpec] section at the end of the file.
   *)

(** * Specifications written using equivalences *)
Section IffSpec.
  Context `{HF : @FSetSpecs elt Helt F}.

  Let t := set elt.
  Variable s s' s'' : t.
  Variable x y z : elt.

  Lemma In_eq_iff : x === y -> (In x s <-> In y s).
  Proof.
    split; apply In_1; auto.
  Qed.

  Lemma mem_iff : In x s <-> mem x s = true.
  Proof.
    split; [apply mem_1|apply mem_2].
  Qed.

  Lemma not_mem_iff : ~In x s <-> mem x s = false.
  Proof.
    intros; rewrite mem_iff; destruct (mem x s); intuition.
  Qed.

  Lemma equal_iff : s[=]s' <-> equal s s' = true.
  Proof.
    split; [apply equal_1|apply equal_2].
  Qed.

  Lemma subset_iff : s[<=]s' <-> subset s s' = true.
  Proof.
    split; [apply subset_1|apply subset_2].
  Qed.

  Lemma empty_iff : In x empty <-> False.
  Proof.
    intuition; apply (empty_1 H).
  Qed.

  Lemma is_empty_iff : Empty s <-> is_empty s = true.
  Proof.
    split; [apply is_empty_1|apply is_empty_2].
  Qed.

  Lemma singleton_iff : In y (singleton x) <-> x === y.
  Proof.
    split; [apply singleton_1|apply singleton_2].
  Qed.

  Lemma add_iff : In y (add x s) <-> x === y \/ In y s.
  Proof.
    split; [ | destruct 1; [apply add_1|apply add_2]]; auto.
    destruct (eq_dec x y) as [E|E]; auto.
    intro H; right; exact (add_3 E H).
  Qed.

  Lemma add_neq_iff : x =/= y -> (In y (add x s)  <-> In y s).
  Proof.
    split; [apply add_3|apply add_2]; auto.
  Qed.

  Lemma remove_iff : In y (remove x s) <-> In y s /\ x =/= y.
  Proof.
    split; [split;
      [apply remove_3 with x |] | destruct 1; apply remove_2]; auto.
    intro.
    apply (remove_1 H0 H).
  Qed.

  Lemma remove_neq_iff : x =/= y -> (In y (remove x s) <-> In y s).
  Proof.
    split; [apply remove_3|apply remove_2]; auto.
  Qed.

  Lemma union_iff : In x (union s s') <-> In x s \/ In x s'.
  Proof.
    split; [apply union_1 | destruct 1; [apply union_2|apply union_3]]; auto.
  Qed.

  Lemma inter_iff : In x (inter s s') <-> In x s /\ In x s'.
  Proof.
    split; [split; [apply inter_1 with s' |
      apply inter_2 with s] | destruct 1; apply inter_3]; auto.
  Qed.

  Lemma diff_iff : In x (diff s s') <-> In x s /\ ~ In x s'.
  Proof.
    split; [split; [apply diff_1 with s' |
      apply diff_2 with s] | destruct 1; apply diff_3]; auto.
  Qed.

  Section ForFilter.
    Variable f : elt -> bool.
    Context {Hf : Proper (_eq ==> @eq bool) f}.

    Lemma filter_iff : (In x (filter f s) <-> In x s /\ f x = true).
    Proof.
      split; [split; [apply filter_1 with f |
        apply filter_2 with s] | destruct 1; apply filter_3]; auto.
    Qed.

    Lemma for_all_iff :
      (For_all (fun x => f x = true) s <-> for_all f s = true).
    Proof.
      split; [apply for_all_1 | apply for_all_2]; auto.
    Qed.

    Lemma exists_iff : (Exists (fun x => f x = true) s <-> exists_ f s = true).
    Proof.
      split; [apply exists_1 | apply exists_2]; auto.
    Qed.
  End ForFilter.

  Lemma elements_iff : In x s <-> InA _eq x (elements s).
  Proof.
    split; [apply elements_1 | apply elements_2].
  Qed.

End IffSpec.

(** Useful tactic for simplifying expressions like [In y (add x (union s s'))]*)
Ltac set_iff :=
 repeat (progress (
  rewrite add_iff || rewrite remove_iff || rewrite singleton_iff
  || rewrite union_iff || rewrite inter_iff || rewrite diff_iff
  || rewrite empty_iff)).

(**  * Specifications written using boolean predicates *)
Require Import Bool.
Section BoolSpec.
  Context `{HF : @FSetSpecs elt Helt F}.

  Let t := set elt.
  Variable s s' s'' : t.
  Variable x y z : elt.

  Lemma mem_b : x === y -> mem x s = mem y s.
  Proof.
    intros.
    generalize (mem_iff s x) (mem_iff s y) (In_eq_iff s H).
    destruct (mem x s); destruct (mem y s); intuition.
  Qed.

  Lemma empty_b : mem y empty = false.
  Proof.
    generalize (empty_iff y)(mem_iff empty y).
    destruct (mem y empty); intuition.
  Qed.

  Lemma add_b : mem y (add x s) = (x == y) || mem y s.
  Proof.
    generalize (mem_iff (add x s) y)(mem_iff s y)(add_iff s x y); unfold eqb.
    destruct (eq_dec x y); destruct (mem y s);
      destruct (mem y (add x s)); intuition.
  Qed.

  Lemma add_neq_b : x =/= y -> mem y (add x s) = mem y s.
  Proof.
    intros; generalize (mem_iff (add x s) y)(mem_iff s y)(add_neq_iff s H).
    destruct (mem y s); destruct (mem y (add x s)); intuition.
  Qed.

  Lemma remove_b : mem y (remove x s) = mem y s && negb (x == y).
  Proof.
    generalize (mem_iff (remove x s) y)(mem_iff s y)(remove_iff s x y).
    destruct (eq_dec x y); destruct (mem y s); destruct (mem y (remove x s));
      simpl; intuition; contradiction.
  Qed.

  Lemma remove_neq_b : x =/= y -> mem y (remove x s) = mem y s.
  Proof.
    intros; generalize (mem_iff (remove x s) y) (mem_iff s y)
      (remove_neq_iff s H).
    destruct (mem y s); destruct (mem y (remove x s)); intuition.
  Qed.

  Lemma singleton_b : mem y (singleton x) = (x == y).
  Proof.
    generalize (mem_iff (singleton x) y)(singleton_iff x y); unfold eqb.
    destruct (eq_dec x y); destruct (mem y (singleton x)); intuition.
  Qed.

  Lemma union_b : mem x (union s s') = mem x s || mem x s'.
  Proof.
    generalize (mem_iff (union s s') x)(mem_iff s x)(mem_iff s' x)
      (union_iff s s' x).
    destruct (mem x s); destruct (mem x s');
      destruct (mem x (union s s')); intuition.
  Qed.

  Lemma inter_b : mem x (inter s s') = mem x s && mem x s'.
  Proof.
    generalize (mem_iff (inter s s') x)(mem_iff s x)
      (mem_iff s' x)(inter_iff s s' x).
    destruct (mem x s); destruct (mem x s');
      destruct (mem x (inter s s')); intuition.
  Qed.

  Lemma diff_b : mem x (diff s s') = mem x s && negb (mem x s').
  Proof.
    generalize (mem_iff (diff s s') x)(mem_iff s x)
      (mem_iff s' x)(diff_iff s s' x).
    destruct (mem x s); destruct (mem x s');
      destruct (mem x (diff s s')); simpl; intuition.
  Qed.

  Lemma elements_b : mem x s = existsb (fun y => x == y) (elements s).
  Proof.
    generalize (mem_iff s x)(elements_iff s x)
      (existsb_exists (fun y => x == y) (elements s)).
    rewrite InA_alt.
    destruct (mem x s); destruct (existsb (fun y => x == y)
      (elements s)); auto; intros.
    symmetry.
    rewrite H1.
    destruct H0 as (H0,_).
    destruct H0 as (a,(Ha1,Ha2)); [ intuition |].
    exists a; intuition.
    unfold eqb; destruct (eq_dec x a); auto.
    rewrite <- H.
    rewrite H0.
    destruct H1 as (H1,_).
    destruct H1 as (a,(Ha1,Ha2)); [intuition|].
    exists a; intuition.
    unfold eqb in *; destruct (eq_dec x a); auto; discriminate.
  Qed.

  Variable f : elt->bool.

  Lemma filter_b `{Proper _ (_eq ==> @eq bool) f} :
    mem x (filter f s) = mem x s && f x.
  Proof.
    intros.
    generalize (mem_iff (filter f s) x)(mem_iff s x)(filter_iff (f:=f) s x).
    destruct (mem x s); destruct (mem x (filter f s));
      destruct (f x); simpl; intuition.
  Qed.

  Lemma for_all_b `{Proper _ (_eq ==> @eq bool) f} :
    for_all f s = forallb f (elements s).
  Proof.
    intros.
    generalize (forallb_forall f (elements s))
      (for_all_iff (f:=f) s)(elements_iff s).
    unfold For_all.
    destruct (forallb f (elements s)); destruct (for_all f s); auto; intros.
    rewrite <- H1; intros.
    destruct H0 as (H0,_).
    rewrite (H2 x0) in H3.
    rewrite (InA_alt _eq x0 (elements s)) in H3.
    destruct H3 as (a,(Ha1,Ha2)).
    rewrite (H _ _ Ha1).
    apply H0; auto.
    symmetry.
    rewrite H0; intros.
    destruct H1 as (_,H1).
    apply H1; auto.
    rewrite H2.
    rewrite InA_alt; eauto.
  Qed.

  Lemma exists_b `{Proper _ (_eq ==> @eq bool) f} :
    exists_ f s = existsb f (elements s).
  Proof.
    intros.
    generalize (existsb_exists f (elements s))
      (exists_iff (f:=f) s)(elements_iff s).
    unfold Exists.
    destruct (existsb f (elements s)); destruct (exists_ f s); auto; intros.
    rewrite <- H1; intros.
    destruct H0 as (H0,_).
    destruct H0 as (a,(Ha1,Ha2)); auto.
    exists a; split; auto.
    rewrite H2; rewrite InA_alt; eauto.
    symmetry.
    rewrite H0.
    destruct H1 as (_,H1).
    destruct H1 as (a,(Ha1,Ha2)); auto.
    rewrite (H2 a) in Ha1.
    rewrite (InA_alt _eq a (elements s)) in Ha1.
    destruct Ha1 as (b,(Hb1,Hb2)).
    exists b; auto.
    rewrite <- (H _ _ Hb1); auto.
  Qed.
End BoolSpec.

(** * [Equal] is a setoid equality *)
Instance Equal_ST `{FSet A} : Equivalence Equal.
Proof.
  constructor; red ; intros.
  intro e; tauto.
  intro e; rewrite (H1 e); tauto.
  intro e; transitivity (e \In y); [apply H1 | apply H2].
Qed.

Instance In_m `{HF : @FSetSpecs A HA F} :
  Proper (_eq ==> Equal ==> iff) In.
Proof.
  unfold Equal; intros x y H s s' H0.
  rewrite (In_eq_iff s H); auto.
Qed.

Instance is_empty_m `{HF : @FSetSpecs A HA F} :
  Proper (Equal ==> @eq bool)  is_empty.
Proof.
  unfold Equal; intros s s' H.
  generalize (is_empty_iff s)(is_empty_iff s').
  destruct (is_empty s); destruct (is_empty s');
    unfold Empty; auto; intros.
  symmetry.
  rewrite <- H1; intros a Ha.
  rewrite <- (H a) in Ha.
  destruct H0 as (_,H0).
  exact (H0 (refl_equal true) _ Ha).
  rewrite <- H0; intros a Ha.
  rewrite (H a) in Ha.
  destruct H1 as (_,H1).
  exact (H1 (refl_equal true) _ Ha).
Qed.

Instance Empty_m `{HF : @FSetSpecs A HA F} :
  Proper (Equal ==> iff) Empty.
Proof.
  intros s s' H; do 2 rewrite is_empty_iff; rewrite H; intuition.
Qed.

Instance mem_m `{HF : @FSetSpecs A HA F} :
  Proper (_eq ==> Equal ==> @eq bool) mem.
Proof.
  unfold Equal; intros x y H s s' H0.
  generalize (H0 x); clear H0; rewrite (In_eq_iff s' H).
  generalize (mem_iff s x)(mem_iff s' y).
  destruct (mem x s); destruct (mem y s'); intuition.
Qed.

Instance singleton_m `{HF : @FSetSpecs A HA F} :
  Proper (_eq ==> Equal) singleton.
Proof.
  unfold Equal; intros x y H a.
  do 2 rewrite singleton_iff; split; intros.
  transitivity x; auto.
  transitivity y; auto.
Qed.

Instance add_m `{HF : @FSetSpecs A HA F} :
  Proper (_eq ==> Equal ==> Equal) add.
Proof.
  unfold Equal; intros x y H s s' H0 a.
  do 2 rewrite add_iff; rewrite H; rewrite H0; intuition.
Qed.

Instance remove_m `{HF : @FSetSpecs A HA F} :
  Proper (_eq ==> Equal ==> Equal) remove.
Proof.
  unfold Equal; intros x y H s s' H0 a.
  do 2 rewrite remove_iff; rewrite H; rewrite H0; intuition.
Qed.

Instance union_m `{HF : @FSetSpecs A HA F} :
  Proper (Equal ==> Equal ==> Equal) union.
Proof.
  unfold Equal; intros s s' H s'' s''' H0 a.
  do 2 rewrite union_iff; rewrite H; rewrite H0; intuition.
Qed.

Instance inter_m `{HF : @FSetSpecs A HA F} :
  Proper (Equal ==> Equal ==> Equal) inter.
Proof.
  unfold Equal; intros s s' H s'' s''' H0 a.
  do 2 rewrite inter_iff; rewrite H; rewrite H0; intuition.
Qed.

Instance diff_m `{HF : @FSetSpecs A HA F} :
  Proper (Equal ==> Equal ==> Equal) diff.
Proof.
  unfold Equal; intros s s' H s'' s''' H0 a.
  do 2 rewrite diff_iff; rewrite H; rewrite H0; intuition.
Qed.

Instance Subset_m `{HF : @FSetSpecs A HA F} :
  Proper (Equal ==> Equal ==> iff) Subset.
Proof.
  unfold Equal, Subset; intros s s' H u u' H'; split; intros.
  rewrite <- H'; apply H0; rewrite H; assumption.
  rewrite H'; apply H0; rewrite <- H; assumption.
Qed.

Instance subset_m `{HF : @FSetSpecs A HA F} :
  Proper (Equal ==> Equal ==> @eq bool) subset.
Proof.
  intros s s' H s'' s''' H0.
  generalize (subset_iff s s'') (subset_iff s' s''').
  destruct (subset s s''); destruct (subset s' s'''); auto; intros.
  rewrite H in H1; rewrite H0 in H1; intuition.
  rewrite H in H1; rewrite H0 in H1; intuition.
Qed.

Instance equal_m `{HF : @FSetSpecs A HA F} :
  Proper (Equal ==> Equal ==> @eq bool) equal.
Proof.
  intros s s' H s'' s''' H0.
  generalize (equal_iff s s'') (equal_iff s' s''').
  destruct (equal s s''); destruct (equal s' s'''); auto; intros.
  rewrite H in H1; rewrite H0 in H1; intuition.
  rewrite H in H1; rewrite H0 in H1; intuition.
Qed.

(** * [Subset] is a setoid order *)
Lemma Subset_refl `{HF : @FSetSpecs A HA F} :
  forall s, s[<=]s.
Proof. red; auto. Qed.

Lemma Subset_trans `{HF : @FSetSpecs A HA F} :
  forall s s' s'', s[<=]s'->s'[<=]s''->s[<=]s''.
Proof. unfold Subset; eauto. Qed.

Instance SubsetSetoid `{@FSetSpecs A HA F} :
  PreOrder Subset := {
    PreOrder_Reflexive := Subset_refl;
    PreOrder_Transitive := Subset_trans
}.

(** * Set operations and morphisms *)
Instance In_s_m `{F : FSet A, @FSetSpecs A H F} :
  Proper (_eq ==> Subset ++> impl) In | 1.
Proof.
  simpl_relation; apply H2; rewrite <- H1; auto.
Qed.

Instance Empty_s_m `{F : FSet A, @FSetSpecs A H F} :
  Proper (Subset --> impl) Empty.
Proof.
  simpl_relation; unfold Subset, Empty, impl; intros.
  exact (H2 a (H1 a H3)).
Qed.

Instance add_s_m `{F : FSet A, @FSetSpecs A H F} :
  Proper (_eq ==> Subset ++> Subset) add.
Proof.
  unfold Subset; intros x y H1 s s' H2 a.
  do 2 rewrite add_iff; rewrite H1; intuition.
Qed.

Instance remove_s_m `{F : FSet A, @FSetSpecs A H F} :
  Proper (_eq ==> Subset ++> Subset) remove.
Proof.
  unfold Subset; intros x y H1 s s' H2 a.
  do 2 rewrite remove_iff; rewrite H1; intuition.
Qed.

Instance union_s_m `{@FSetSpecs A HA F} :
  Proper (Subset ++> Subset ++> Subset) union.
Proof.
  unfold Equal; intros s s' H1 s'' s''' H2 a.
  do 2 rewrite union_iff; intuition.
Qed.

Instance inter_s_m `{@FSetSpecs A HA F} :
  Proper (Subset ++> Subset ++> Subset) inter.
Proof.
  unfold Equal; intros s s' H1 s'' s''' H2 a.
  do 2 rewrite inter_iff; intuition.
Qed.

Instance diff_s_m `{@FSetSpecs A HA F} :
  Proper (Subset ++> Subset --> Subset) diff.
Proof.
  unfold Subset; intros s s' H1 s'' s''' H2 a.
  do 2 rewrite diff_iff; intuition.
Qed.

(** [fold], [filter], [for_all], [exists_] and [partition] require
   the  additional hypothesis on [f]. *)
Instance filter_m  `{F : FSet A, @FSetSpecs A H F} :
  forall f `{Proper _ (_eq ==> @eq bool) f},
    Proper (Equal ==> Equal) (filter f).
Proof.
  unfold Equal; intros f Hf s s' H' x.
  repeat rewrite filter_iff; auto. rewrite H'; reflexivity.
Qed.

Lemma filter_ext  `{F : FSet A, @FSetSpecs A H F} :
  forall f f' `{Proper _ (_eq ==> @eq bool) f}, (forall x, f x = f' x) ->
    forall s s', s[=]s' -> filter f s [=] filter f' s'.
Proof.
  intros f f' Hf Hff' s s' Hss' x. do 2 (rewrite filter_iff; auto).
  rewrite Hff', Hss'; intuition.
  red; repeat intro; rewrite <- 2 Hff'; auto.
Qed.

Instance filter_s_m  `{F : FSet A, @FSetSpecs A H F} :
  forall f `{Proper _ (_eq ==> @eq bool) f},
    Proper (Subset ==> Subset) (filter f).
Proof.
  unfold Subset; intros f Hf s s' H' x.
  repeat rewrite filter_iff; auto; intro; intuition.
Qed.

(** * Inductive specifications of boolean functions *)
CoInductive reflects (P : Prop) : bool -> Prop :=
| reflects_true : forall (Htrue : P), reflects P true
| reflects_false : forall (Hfalse : ~P), reflects P false.

Section InductiveSpec.
  Context `{HF : @FSetSpecs elt Helt F}.
  Variables s s' s'' : set elt.
  Variables x y z : elt.

  Property In_dec : reflects (In x s) (mem x s).
  Proof.
    case_eq (mem x s); intro H; constructor.
    apply mem_2; exact H.
    intro abs; rewrite (mem_1 abs) in H; discriminate.
  Qed.

  Property is_empty_dec : reflects (Empty s) (is_empty s).
  Proof.
    case_eq (is_empty s); intro H; constructor.
    apply is_empty_2; exact H.
    intro abs; rewrite (is_empty_1 abs) in H; discriminate.
  Qed.
  Corollary is_empty_dec2 : reflects (s [=] empty) (is_empty s).
  Proof.
    destruct is_empty_dec; constructor.
    intro a; rewrite empty_iff; intuition; contradiction (Htrue a).
    intro R; rewrite R in Hfalse; contradiction Hfalse.
    auto with set typeclass_instances.
  Qed.

  Property equal_dec : reflects (s [=] s') (equal s s').
  Proof.
    case_eq (equal s s'); intro H; constructor.
    apply equal_2; exact H.
    intro abs; rewrite (equal_1 abs) in H; discriminate.
  Qed.

  Property subset_dec : reflects (s [<=] s') (subset s s').
  Proof.
    case_eq (subset s s'); intro H; constructor.
    apply subset_2; exact H.
    intro abs; rewrite (subset_1 abs) in H; discriminate.
  Qed.

  Section Compat.
    Variable f : elt -> bool.
    Context `{Comp : Proper _ (_eq ==> @eq bool) f}.

    Property for_all_dec :
      reflects (For_all (fun x => f x = true) s) (for_all f s).
    Proof.
      case_eq (for_all f s); intro H; constructor.
      apply for_all_2; auto.
      intro abs; rewrite (for_all_1 abs) in H; discriminate.
    Qed.

    Property exists_dec :
      reflects (Exists (fun x => f x = true) s) (exists_ f s).
    Proof.
      case_eq (exists_ f s); intro H; constructor.
      apply exists_2; auto.
      intro abs; rewrite (exists_1 abs) in H; discriminate.
    Qed.
  End Compat.

  CoInductive choose_spec : option elt -> Prop :=
  | choose_spec_Some : forall x (Hin : In x s), choose_spec (Some x)
  | choose_Spec_None : forall (Hempty : Empty s), choose_spec None.
  Property choose_dec : choose_spec (choose s).
  Proof.
    case_eq (choose s); intros; constructor.
    apply choose_1; auto.
    apply choose_2; auto.
  Qed.

  CoInductive min_elt_spec : option elt -> Prop :=
  | min_elt_spec_Some :
    forall x (Hin : In x s) (Hmin : forall y, In y s -> ~y <<< x),
      min_elt_spec (Some x)
  | min_elt_spec_None :
    forall (Hempty : Empty s), min_elt_spec None.
  Property min_elt_dec : min_elt_spec (min_elt s).
  Proof.
    case_eq (min_elt s); intros; constructor.
    apply min_elt_1; auto.
    intro; apply min_elt_2; auto.
    apply min_elt_3; auto.
  Qed.

  Inductive max_elt_spec : option elt -> Prop :=
  | max_elt_spec_Some :
    forall x (Hin : In x s) (Hmin : forall y, In y s -> ~y >>> x),
      max_elt_spec (Some x)
  | max_elt_spec_None :
    forall (Hempty : Empty s), max_elt_spec None.
  Property max_elt_dec : max_elt_spec (max_elt s).
  Proof.
    case_eq (max_elt s); intros; constructor.
    apply max_elt_1; auto.
    intro; apply max_elt_2; auto.
    apply max_elt_3; auto.
  Qed.
End InductiveSpec.