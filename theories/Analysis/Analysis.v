Require Import Util EqDec LengthEq Get Coq.Classes.RelationClasses MoreList AllInRel ListUpdateAt.
Require Import SizeInduction Infra.Lattice OptionR DecSolve.
Require Import Annotation AnnotationLattice.

Set Implicit Arguments.

Inductive anni (A:Type) : Type :=
| anni0 : anni A
| anni1 (a1:A) : anni A
| anni2 (a1:A) (a2:A) : anni A
| anni2opt (a1:option A) (a2:option A) : anni A.

Arguments anni0 [A].

Fixpoint setAnni {A} (a:ann A) (ai:anni A) : ann A :=
  match a, ai with
    | ann1 a an, anni1 a1 => ann1 a (setTopAnn an a1)
    | ann2 a an1 an2, anni2 a1 a2 => ann2 a (setTopAnn an1 a1) (setTopAnn an2 a2)
    | an, _ => an
  end.

Definition mapAnni {A B} (f:A -> B) (ai:anni A) : anni B :=
  match ai with
    | anni0 => anni0
    | anni1 a1 => anni1 (f a1)
    | anni2 a1 a2 => anni2 (f a1) (f a2)
    | anni2opt o1 o2 => anni2opt (mapOption f o1) (mapOption f o2)
  end.

Inductive anni_R A B (R : A -> B -> Prop) : anni A -> anni B -> Prop :=
| anni_R0
  : anni_R R anni0 anni0
| anni_R1 a1 a2
  : R a1 a2 -> anni_R R (anni1 a1) (anni1 a2)
| anni_R2 a1 a1' a2 a2'
  : R a1 a2 -> R a1' a2' -> anni_R R (anni2 a1 a1') (anni2 a2 a2')
| anni_R2o o1 o1' o2 o2'
  : option_R R o1 o2 -> option_R R o1' o2' -> anni_R R (anni2opt o1 o1') (anni2opt o2 o2').

Instance anni_R_refl {A} {R} `{Reflexive A R} : Reflexive (anni_R R).
Proof.
  hnf; intros; destruct x; eauto using anni_R, option_R.
  econstructor; reflexivity.
Qed.

Instance anni_R_sym {A} {R} `{Symmetric A R} : Symmetric (anni_R R).
Proof.
  hnf; intros. inv H0; eauto using anni_R.
  econstructor; symmetry; eauto.
Qed.

Instance anni_R_trans A R `{Transitive A R} : Transitive (anni_R R).
Proof.
  hnf; intros ? ? ? B C.
  inv B; inv C; econstructor; eauto.
  - etransitivity; eauto.
  - etransitivity; eauto.
Qed.

Instance anni_R_equivalence A R `{Equivalence A R} : Equivalence (anni_R R).
Proof.
  econstructor; eauto with typeclass_instances.
Qed.

Instance anni_R_anti A R Eq `{EqA:Equivalence _ Eq} `{@Antisymmetric A Eq EqA R}
  : @Antisymmetric _ (anni_R Eq) _ (anni_R R).
Proof.
  intros ? ? B C. inv B; inv C; eauto using anni_R.
  econstructor; eapply option_R_anti; eauto.
Qed.

Instance anni_R_dec A B (R:A->B->Prop)
         `{forall a b, Computable (R a b)} (a:anni A) (b:anni B) :
  Computable (anni_R R a b).
Proof.
  destruct a,b; try dec_solve.
  - decide (R a1 a0); dec_solve.
  - decide (R a1 a0); decide (R a2 a3); dec_solve.
  - decide (option_R R a1 a0); decide (option_R R a2 a3); dec_solve.
Defined.

Instance PartialOrder_anni Dom `{PartialOrder Dom}
: PartialOrder (anni Dom) := {
  poLe := anni_R poLe;
  poLe_dec := @anni_R_dec _ _ poLe poLe_dec;
  poEq := anni_R poEq;
  poEq_dec := @anni_R_dec _ _ poEq poEq_dec;
}.
Proof.
  - intros. inv H0; eauto 20 using @anni_R, poLe_refl.
    econstructor; eapply (@poLe_refl _ (PartialOrder_option Dom)); eauto.
Defined.


Definition getAnni A (a:A) (an:anni A) :=
  match an with
  | anni1 a => a
  | _ => a
  end.

Lemma poLe_getAnni A `{PartialOrder A} (a a':A) an an'
  : poLe a a'
    -> poLe an an'
    -> poLe (getAnni a an) (getAnni a' an').
Proof.
  intros LE LE'; inv LE'; simpl; eauto.
Qed.

Hint Resolve poLe_getAnni.

Definition getAnniLeft A (a:A) (an:anni A) :=
  match an with
  | anni2 a _ => a
  | _ => a
  end.

Lemma poLe_getAnniLeft A `{PartialOrder A} (a a':A) an an'
  : poLe a a'
    -> poLe an an'
    -> poLe (getAnniLeft a an) (getAnniLeft a' an').
Proof.
  intros LE LE'; inv LE'; simpl; eauto.
Qed.

Hint Resolve poLe_getAnniLeft.

Definition getAnniRight A (a:A) (an:anni A) :=
  match an with
  | anni2 _ a => a
  | _ => a
  end.

Lemma poLe_getAnniRight A `{PartialOrder A} (a a':A) an an'
  : poLe a a'
    -> poLe an an'
    -> poLe (getAnniRight a an) (getAnniRight a' an').
Proof.
  intros LE LE'; inv LE'; simpl; eauto.
Qed.

Hint Resolve poLe_getAnniRight.

Lemma ann_bottom s' (Dom:Type) `{LowerBounded Dom}
  :  forall (d : ann Dom), annotation s' d -> setAnn bottom s' ⊑ d.
Proof.
  sind s'; destruct s'; simpl; intros d' Ann; inv Ann; simpl;
    eauto using bottom_least.
  - econstructor; eauto using bottom_least with len.
    + intros; inv_get. eapply IH; eauto.
    + eapply IH; eauto.
Qed.

Definition setTopAnnO {A} `{LowerBounded A} a (al:option A) :=
  match al with
  | None => setTopAnn a bottom
  | Some al' => setTopAnn a al'
  end.


Lemma PIR2_ojoin_zip A `{JoinSemiLattice A} (a:list A) a' b b'
  : poLe a a'
    -> poLe b b'
    -> poLe (join ⊜ a b) (join ⊜ a' b').
Proof.
  intros. hnf in H1,H2. general induction H1; inv H2; simpl; eauto using PIR2.
  econstructor; eauto.
  rewrite pf, pf0. reflexivity. eapply IHPIR2; eauto.
Qed.

Hint Resolve PIR2_ojoin_zip.

Lemma update_at_poLe A `{LowerBounded A} B (L:list B) n (a:A) b
  : poLe a b
    -> poLe (list_update_at (tab bottom ‖L‖) n a)
            (list_update_at (tab bottom ‖L‖) n b).
Proof.
  intros.
  general induction L; simpl; eauto using PIR2.
  - destruct n; simpl; eauto using @PIR2.
Qed.


Lemma PIR2_fold_zip_join X `{JoinSemiLattice X} (A A':list (list X)) (B B':list X)
  : poLe A A'
    -> poLe B B'
    -> poLe (fold_left (zip join) A B)
           (fold_left (zip join) A' B').
Proof.
  intros. simpl in *.
  general induction H1; simpl; eauto.
Qed.

Hint Resolve PIR2_fold_zip_join.

Lemma tab_false_impb Dom `{PartialOrder Dom} AL AL'
  : poLe AL AL'
    -> poLe (tab false ‖AL‖) (tab false ‖AL'‖).
Proof.
  intros. hnf in H0.
  general induction H0; simpl; unfold impb; eauto.
Qed.

Lemma update_at_impb Dom `{PartialOrder Dom} AL AL' n
  : poLe AL AL'
    ->  poLe (list_update_at (tab false ‖AL‖) n true)
            (list_update_at (tab false ‖AL'‖) n true).
Proof.
  intros A. general induction A; simpl; eauto.
  - destruct n; simpl; eauto using @PIR2, tab_false_impb.
Qed.

Ltac refold_PIR2_PO :=
  match goal with
  | [ H : context [ PIR2 (@poLe ?D _) ] |- _ ] =>
    change (PIR2 (@poLe D _)) with (@poLe (list D) _) in H
  | [ H : context [ PIR2 (@poEq ?D _) ] |- _ ] =>
    change (PIR2 (@poLe D _)) with (@poLe (list D) _) in H
  | [ |- context [ PIR2 (@poLe ?D ?PO) ] ] =>
    change (PIR2 (@poLe D PO)) with (@poLe (list D) _)
  | [ |- context [ PIR2 (@poEq ?D ?PO) ] ] =>
    change (PIR2 (@poEq D PO)) with (@poEq (list D) _)
(*  | [ H : context [ PIR2 (@poEq _ _) ] |- _ ] =>
    let EQ := fresh "PIR2_EQ" in
    assert (EQ:forall X (PO : PartialOrder X) x y,
               PIR2 (@poEq X PO) x y = @poEq (list X) (@PartialOrder_list X PO) x y) by
        (intros; reflexivity);
    setoid_rewrite EQ in H*)
  end.

Smpl Add refold_PIR2_PO : inversion_cleanup.

Ltac refold_ann_PO :=
  match goal with
  | [ H : context [ @ann_R ?A ?A (@poLe ?A ?I) ] |- _ ] =>
    change (@ann_R A A (@poLe A I)) with (@poLe (@ann A) _) in H
  | [ |- context [ ann_R poLe ?x ?y ] ] =>
    change (ann_R poLe x y) with (poLe x y)
  | [ H : context [ @ann_R ?A ?A (@poEq ?A ?I) ] |- _ ] =>
    change (@ann_R A A (@poEq A I)) with (@poEq (@ann A) _) in H
  | [ |- context [ ann_R poEq ?x ?y ] ] =>
    change (ann_R poEq x y) with (poEq x y)
  end.

Smpl Add refold_ann_PO : inversion_cleanup.

Hint Resolve join_struct join_struct_eq.

Lemma PIR2_poLe_join X `{JoinSemiLattice X} (A A' B B':list X)
  : poLe A A'
    -> poLe B B'
    -> poLe (join ⊜ A B) (join ⊜ A' B').
Proof.
  intros AA BB.
  general induction AA; simpl; inv BB; eauto.
Qed.

Hint Resolve PIR2_poLe_join.

Lemma PIR2_impb_orb A A' B B'
  : PIR2 impb A A'
    -> PIR2 impb B B'
    -> PIR2 impb (orb ⊜ A B) (orb ⊜ A' B').
Proof.
  intros. pose proof (@PIR2_poLe_join bool _ _).
  eapply H1; eauto.
Qed.

Smpl Add 10 match goal with
         | [ H : _ < _  |- _ ] => simpl in H
         | [ H :  _ <= _  |- _ ] => simpl in H
         end : inv_trivial.

Smpl Add match goal with
         | [ H : S _ < 0 |- _ ] => exfalso; inv H
         | [ H : S _ <=  0 |- _ ] => exfalso; inv H
         end : inv_trivial.

Hint Resolve join_poLe.

Lemma join_poLe_left X `{JoinSemiLattice X} x y z
  : poLe x y -> poLe x (join y z).
Proof.
  intros LE. rewrite LE. eauto.
Qed.

Lemma join_poLe_right X `{JoinSemiLattice X} x y z
  : poLe x y -> poLe x (join z y).
Proof.
  intros LE. rewrite LE. rewrite join_commutative. eauto.
Qed.

Hint Resolve join_poLe_left join_poLe_right | 50.

Lemma join_poLe_left_inv X `{JoinSemiLattice X} x y z
  : poLe (join y z) x -> poLe y x.
Proof.
  intros LE. rewrite <- LE. eauto.
Qed.

Lemma join_poLe_right_inv X `{JoinSemiLattice X} x y z
  : poLe (join z y) x -> poLe y x.
Proof.
  intros LE. rewrite <- LE. eauto.
Qed.

Hint Resolve le_S_n | 100.

Lemma PIR2_poLe_join_right X `{JoinSemiLattice X} A A' B
  : length A <= length B
    -> poLe A A'
    -> poLe A (join ⊜ A' B).
Proof.
  intros LEN AA.
  general induction AA; destruct B; simpl in *; clear_trivial_eqs; eauto.
Qed.

Lemma PIR2_poLe_join_left X `{JoinSemiLattice X} A A' B
  : length A <= length B
    -> poLe A A'
    -> poLe A (join ⊜ B A').
Proof.
  intros LEN AA.
  general induction AA; destruct B; simpl in *; clear_trivial_eqs; eauto.
Qed.

Hint Resolve PIR2_poLe_join_right PIR2_poLe_join_left | 50.

Smpl Add 50 match goal with
            | [ H : context [ impb ] |- _ ] =>
              change impb with (@poLe bool PartialOrder_bool) in H
            | [ |- context [ impb ] ] =>
              change impb with (@poLe bool PartialOrder_bool)
         end : inversion_cleanup.

Smpl Add 50 match goal with
            | [ H : context [ orb ] |- _ ] =>
              change orb with (@join bool _ bool_joinsemilattice) in H
            | [ |- context [ orb ] ] =>
              change orb with (@join bool _ bool_joinsemilattice)
            end : inversion_cleanup.

Lemma poLe_length X `{PartialOrder X} A B
  : poLe A B
    -> ❬A❭ <= ❬B❭.
Proof.
  intros. hnf in H0. erewrite PIR2_length; eauto.
Qed.

Lemma poLe_length_eq X `{PartialOrder X} A B
  : poLe A B
    -> ❬A❭ = ❬B❭.
Proof.
  intros. hnf in H0. erewrite PIR2_length; eauto.
Qed.

Hint Resolve poLe_length : len.
Hint Resolve poLe_length_eq : len.

Instance poLe_length_proper X `{PartialOrder X}
  : Proper (poLe ==> eq) (@length X).
Proof.
  unfold Proper, respectful; intros.
  eauto with len.
Qed.

Instance poEq_length_proper X `{PartialOrder X}
  : Proper (poEq ==> eq) (@length X).
Proof.
  unfold Proper, respectful; intros.
  eauto with len.
Qed.

Lemma PIR2_impb_fold (A A':list (list bool * bool)) (B B':list bool)
  : poLe A A'
    -> poLe B B'
    -> (forall n a, get A n a -> length B <= length (fst a))
    -> poLe (fold_left (fun a (b:list bool * bool) => if snd b then orb ⊜ a (fst b) else a) A B)
           (fold_left (fun a (b:list bool * bool) => if snd b then orb ⊜ a (fst b) else a) A' B').
Proof.
  intros.
  general induction H; simpl; inv_cleanup; eauto.
  eapply IHPIR2; eauto using PIR2_impb_orb.
  - exploit H1; eauto using get.
    inv pf.
    repeat cases; eauto.
    eapply PIR2_poLe_join_right; eauto using get.
    rewrite <- H3; eauto.
  - intros. cases; eauto using get.
    rewrite zip_length3; eauto using get.
Qed.


Lemma PIR2_zip_join_inv_left X `{JoinSemiLattice X} A B C
  : poLe (join ⊜ A B) C
    -> length A = length B
    -> poLe A C.
Proof.
  intros. length_equify.
  general induction H1; inv H2; simpl in *; clear_trivial_eqs;
    eauto using join_poLe_left_inv.
Qed.

Lemma PIR2_zip_join_inv_right X `{JoinSemiLattice X} A B C
  : poLe (join ⊜ A B) C
    -> length A = length B
    -> poLe B C.
Proof.
  intros.
  general induction H2; inv H1; clear_trivial_eqs; eauto using join_poLe_right_inv.
Qed.

Lemma PIR2_poLe_zip_join_left X `{JoinSemiLattice X} A B
  : length A = length B
    -> poLe A (join ⊜ A B).
Proof.
  intros.
  general induction H1; simpl in *; eauto using PIR2; try solve [ congruence ].
Qed.

Lemma PIR2_zip_join_commutative X `{JoinSemiLattice X} A B
  : poLe (join ⊜ B A) (join ⊜ A B).
Proof.
  intros.
  general induction A; destruct B; simpl in *; eauto.
  eauto using join_commutative.
Qed.

Lemma PIR2_poLe_zip_join_right X `{JoinSemiLattice X} A B
  : length A = length B
    -> poLe B (join ⊜ A B).
Proof.
  intros. rewrite <- PIR2_zip_join_commutative. (* todo: missing morphism *)
  eapply PIR2_poLe_zip_join_left; congruence.
Qed.

Lemma PIR2_fold_zip_join_inv X `{JoinSemiLattice X} A B C
  : poLe (fold_left (zip join) A B) C
    -> (forall n a, get A n a -> length a = length B)
    -> poLe B C.
Proof.
  intros.
  general induction A; simpl in *; eauto.
  eapply IHA; eauto using get.
  rewrite <- H1. eauto.
  eapply PIR2_fold_zip_join; eauto.
  eapply PIR2_poLe_zip_join_left.
  symmetry. eauto using get.
Qed.

Lemma PIR2_fold_zip_join_right X `{JoinSemiLattice X} (A:list X) B C
  : (forall n a, get B n a -> length a = length C)
    -> poLe A C
    -> poLe A (fold_left (zip join) B C).
Proof.
  general induction B; simpl; eauto.
  eapply IHB; intros; eauto using get with len.
  - rewrite zip_length2; eauto using eq_sym, get.
  - rewrite H2. eapply PIR2_poLe_zip_join_left. symmetry. eauto using get.
Qed.

Lemma PIR2_fold_zip_join_left X `{JoinSemiLattice X} (A:list X) B C a k
  : get B k a
    -> poLe A a
    -> (forall n a, get B n a -> length a = length C)
    -> poLe A (fold_left (zip join) B C).
Proof.
  intros.
  general induction B; simpl in *; eauto.
  - inv H1.
    + eapply PIR2_fold_zip_join_right.
      intros. rewrite zip_length2; eauto using eq_sym, get.
      rewrite H2. eapply PIR2_poLe_zip_join_right.
      eauto using eq_sym, get.
    + eapply IHB; eauto using get.
      intros. rewrite zip_length2; eauto using eq_sym, get.
Qed.


Lemma get_union_union_b X `{JoinSemiLattice X} (A:list (list X)) (b:list X) n x
  : get b n x
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> exists y, get (fold_left (zip join) A b) n y /\ poLe x y.
Proof.
  intros GETb LEN. general induction A; simpl in *.
  - eexists x. eauto with cset.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETb (eq_sym H1)) as [y GETa]; eauto.
    exploit (zip_get join GETb GETa).
    + exploit IHA; try eapply GET; eauto.
      rewrite zip_length2; eauto using get with len.
      edestruct H3; dcr; subst. eexists; split; eauto using join_poLe_left_inv.
Qed.

Lemma get_fold_zip_join X (f: X-> X-> X) (A:list (list X)) (b:list X) n
  : (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> n < ❬b❭
    -> exists y, get (fold_left (zip f) A b) n y.
Proof.
  intros LEN. general induction A; simpl in *.
  - edestruct get_in_range; eauto.
  - exploit LEN; eauto using get.
    eapply IHA; eauto using get with len.
Qed.


Lemma get_union_union_A X `{JoinSemiLattice X} (A:list (list X)) a b n k x
  : get A k a
    -> get a n x
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> exists y, get (fold_left (zip join) A b) n y /\ poLe x y.
Proof.
  intros GETA GETa LEN.
  general induction A; simpl in * |- *; isabsurd.
  inv GETA; eauto.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETa H1) as [y GETb].
    exploit (zip_get join GETb GETa).
    exploit (@get_union_union_b _ _ _ A); eauto.
    rewrite zip_length2; eauto using get with len.
    destruct H3; dcr; subst.
    eexists; split; eauto using join_poLe_right_inv.
  - exploit IHA; eauto.
    rewrite zip_length2; eauto using get.
    symmetry; eauto using get.
Qed.


Lemma fold_left_zip_orb_inv A b n
  : get (fold_left (zip orb) A b) n true
    -> get b n true \/ exists k a, get A k a /\ get a n true.
Proof.
  intros Get.
  general induction A; simpl in *; eauto.
  edestruct IHA; dcr; eauto 20 using get.
  inv_get. destruct x, x0; isabsurd; eauto using get.
Qed.

Lemma fold_left_mono A A' b b'
  : poLe A A'
    -> poLe b b'
    -> poLe (fold_left (zip orb) A b) (fold_left (zip orb) A' b').
Proof.
  intros.
  hnf in H. general induction H; simpl; eauto. inv_cleanup.
  - eapply IHPIR2; eauto.
Qed.


Lemma fold_list_length A B (f:list B -> (list A * bool) -> list B) (a:list (list A * bool)) (b: list B)
  : (forall n aa, get a n aa -> ❬b❭ <= ❬fst aa❭)
    -> (forall aa b, ❬b❭ <= ❬fst aa❭ -> ❬f b aa❭ = ❬b❭)
    -> length (fold_left f a b) = ❬b❭.
Proof.
  intros LEN.
  general induction a; simpl; eauto.
  erewrite IHa; eauto 10 using get with len.
  intros. rewrite H; eauto using get.
Qed.

Lemma fold_list_length' A B (f:list B -> (list A) -> list B) (a:list (list A)) (b: list B)
  : (forall n aa, get a n aa -> ❬b❭ <= ❬aa❭)
    -> (forall aa b, ❬b❭ <= ❬aa❭ -> ❬f b aa❭ = ❬b❭)
    -> length (fold_left f a b) = ❬b❭.
Proof.
  intros LEN.
  general induction a; simpl; eauto.
  erewrite IHa; eauto 10 using get with len.
  intros. rewrite H; eauto using get.
Qed.
