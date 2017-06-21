Require Import Util LengthEq.
Require Import Containers.OrderedType Setoid Coq.Classes.Morphisms Computable
        Coq.Classes.RelationClasses.
Require Import Containers.OrderedTypeEx DecSolve MoreList OrderedTypeEx.
Require Import AllInRel.

Create HintDb po discriminated.

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

Arguments poLe : simpl never.
Arguments poEq : simpl never.

Instance poLe_RR X `{PartialOrder X}
  : RewriteRelation (@poLe X _).

Instance poEq_RR X `{PartialOrder X}
  : RewriteRelation (@poEq X _).

Lemma poEq_sym A `{PartialOrder A} x y
  : poEq x y -> poEq y x.
Proof.
  symmetry; eauto.
Qed.

Hint Immediate poEq_sym.

Instance PartialOrder_poLe_refl Dom `{PartialOrder Dom} : Reflexive poLe.
Proof.
  hnf; intros. eapply poLe_refl. reflexivity.
Qed.

Hint Resolve poLe_refl poLe_antisymmetric | 100 : po.

Definition poLt {Dom} `{PartialOrder Dom} x y := poLe x y /\ ~ poLe y x.

Lemma poLt_intro Dom `{PartialOrder Dom} x y
  : poLe x y -> ~ poEq x y -> poLt x y.
Proof.
  firstorder using poLe_antisymmetric.
Qed.

Lemma poLt_poLe Dom `{PartialOrder Dom} x y
  : poLt x y -> poLe x y.
Proof.
  firstorder.
Qed.

Lemma poLt_not_poLe Dom `{PartialOrder Dom} x y
  : poLt x y -> ~ poLe y x.
Proof.
  firstorder.
Qed.

Hint Resolve poLt_intro poLt_poLe poLt_not_poLe | 100 : po.

Lemma poLt_not_poEq Dom `{PartialOrder Dom} x y
  : poLt x y -> ~ poEq y x.
Proof.
  firstorder with po.
Qed.

Lemma poLe_poLt Dom `{PartialOrder Dom} d d'
  : poLe d d'
    -> ~ poLe d' d
    -> poLt d d'.
Proof.
  firstorder.
Qed.

Hint Resolve poLt_intro poLt_poLe poLe_refl poLe_antisymmetric | 100.

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


Lemma poEq_fst A `{PartialOrder A} B `{PartialOrder B} (a b:A * B)
  : poEq a b -> poEq (fst a) (fst b).
  firstorder.
Qed.

Lemma poEq_snd A `{PartialOrder A} B `{PartialOrder B} (a b:A * B)
  : poEq a b -> poEq (snd a) (snd b).
  firstorder.
Qed.

Lemma poEq_struct A `{PartialOrder A} B `{PartialOrder B} (a1 a2:A) (b1 b2:B)
  : poEq a1 a2 -> poEq b1 b2  -> poEq (a1,b1) (a2,b2).
  firstorder.
Qed.

Lemma poLe_fst A `{PartialOrder A} B `{PartialOrder B} (a b:A * B)
  : poLe a b -> poLe (fst a) (fst b).
  firstorder.
Qed.

Lemma poLe_snd A `{PartialOrder A} B `{PartialOrder B} (a b:A * B)
  : poLe a b -> poLe (snd a) (snd b).
  firstorder.
Qed.

Lemma poLe_struct A `{PartialOrder A} B `{PartialOrder B} (a1 a2:A) (b1 b2:B)
  : poLe a1 a2 -> poLe b1 b2  -> poLe (a1,b1) (a2,b2).
  firstorder.
Qed.

Hint Resolve poEq_fst poEq_snd poEq_struct poLe_fst poLe_snd poLe_struct.

Hint Resolve poEq_fst poEq_snd poEq_struct poLe_fst poLe_snd poLe_struct : po.

Instance poEq_pair_proper X `{PartialOrder X} Y `{PartialOrder Y}
  : Proper (poEq ==> poEq ==> poEq) (@pair X Y).
Proof.
  unfold Proper, respectful; intros.
  eapply poEq_struct; eauto.
Qed.

Instance poLe_pair_proper X `{PartialOrder X} Y `{PartialOrder Y}
  : Proper (poLe ==> poLe ==> poLe) (@pair X Y).
Proof.
  unfold Proper, respectful; intros.
  eapply poLe_struct; eauto.
Qed.

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
  - intro. eapply H3.
    etransitivity; eauto. rewrite H4. eauto.
Qed.

Instance poLt_poLe_flip_impl Dom `{PartialOrder Dom}
  : Proper (poLe ==> flip poLe ==> flip impl) poLt.
Proof.
  unfold Proper, respectful, flip, impl; intros.
  destruct H2. split; intros.
  - etransitivity; eauto. etransitivity; eauto.
  - intro. eapply H3.
    etransitivity; eauto. rewrite H4. eauto.
Qed.


Instance poLt_poLe_iff Dom `{PartialOrder Dom}
  : Proper (poEq ==> poEq ==> iff) poLt.
Proof.
  unfold Proper, respectful, flip, impl; intros.
  unfold poLt. rewrite H0, H1. reflexivity.
Qed.

Instance PartialOrder_list Dom `{PartialOrder Dom}
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

Instance poEq_cons X `{PartialOrder X}
  : Proper (poEq ==> poEq ==> poEq) cons.
Proof.
  unfold Proper, respectful; intros.
  econstructor; eauto.
Qed.

Instance poLt_poLe_PIR2_flip_impl Dom `{PartialOrder Dom}
  : (Proper (PIR2 poLe ==> flip poLe ==> flip impl) poLt).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  eapply poLt_poLe_flip_impl; eauto.
Qed.

Hint Extern 5 (poLe ?a ?a) => reflexivity.
Hint Extern 5 (poEq ?a ?a) => reflexivity.
Hint Extern 5 (poLe ?a ?a') => progress (first [has_evar a | has_evar a' | reflexivity]).
Hint Extern 5 (poEq ?a ?a') => progress (first [has_evar a | has_evar a' | reflexivity]).

Hint Extern 10 =>
match goal with
| [ H : poLe ?a ?b, H': poLe ?b ?c |- poLe ?a ?c ] =>
  etransitivity; [ eapply H | eapply H' ]
| [ H : poLe ?a ?b, H': PIR2 _ ?b ?c |- poLe ?a ?c ] =>
  etransitivity; [ eapply H | eapply H' ]
| [ H : poLe ?a ?b, H': poLe ?b ?c, H'' : poLe ?c ?d |- poLe ?a ?d ] =>
  etransitivity; [ eapply H | etransitivity; [ eapply H' | eapply H''] ]
| [ H : PIR2 poLe ?a ?b, H': PIR2 poLe ?b ?c |- PIR2 poLe ?a ?c ] =>
  etransitivity; [ eapply H | eapply H' ]
| [ H : PIR2 poLe ?a ?b, H': PIR2 poLe ?b ?c, H'' : PIR2 poLe ?c ?d |- PIR2 poLe ?a ?d ] =>
  etransitivity; [ eapply H | etransitivity; [ eapply H' | eapply H''] ]
| [ H : poLe ?a ?b, H': PIR2 _ ?b ?c, H'' : poLe ?c ?d |- poLe ?a ?d ] =>
  etransitivity; [ eapply H | etransitivity; [ eapply H' | eapply H''] ]
| [ H : poLe ?a ?b, H' : poLe ?b ?c, H'' : ~ poEq ?b ?c |- poLt ?a ?c ] =>
  rewrite H; eapply (@poLt_intro _ _ _ _ H' H'')
| [ H : poLe ?a ?b, H' : PIR2 _ ?b ?c, H'' : ~ poEq ?b ?c |- poLt ?a ?c ] =>
  rewrite H; eapply poLt_intro; [ eapply H' | eapply H'']
| [ H : poLt ?a ?b, H': poLe ?b ?c |- poLt ?a ?c ] =>
  rewrite <- H'; eapply H
| [ H : poLe ?a ?b, H': poEq ?b ?c |- poLe ?a ?c ] =>
  rewrite <- H'; eapply H
end.


Instance PartialOrder_sig Dom `{PartialOrder Dom} (P:Dom -> Prop)
: PartialOrder { x :Dom | P x } := {
  poLe x y := poLe (proj1_sig x) (proj1_sig y);
  poLe_dec := _;
  poEq x y := poEq (proj1_sig x) (proj1_sig y);
  poEq_dec := _;
}.
Proof.
  - econstructor; hnf; intros; destruct x; try destruct y; try destruct z; simpl in *.
    + reflexivity.
    + symmetry; eauto.
    + etransitivity; eauto.
  - intros [a b] [c d]; simpl. eapply poLe_refl.
  - intros [a b] [c d] [e f]; simpl; intros.
    etransitivity; eauto.
  - intros [a b] [c d]; simpl; intros.
    eapply poLe_antisymmetric; eauto.
Defined.

Instance PartialOrder_bool
: PartialOrder bool := {
  poLe := impb;
  poLe_dec := _;
  poEq := eq;
  poEq_dec := _;
}.
Proof.
  - intros. unfold impb. hnf. destruct d, d'; try dec_solve; eauto.
  - hnf; unfold impb. intros. destruct d,d'; simpl; eauto using bool.
    congruence.
  - hnf; unfold impb. intros. destruct x,y; eauto. exfalso; eauto.
Defined.

Instance fst_poLe Dom `{PartialOrder Dom} Dom' `{PartialOrder Dom'}
  : Proper (poLe ==> poLe) (@fst Dom Dom').
Proof.
  unfold Proper, respectful; intros.
  inv H1; simpl; eauto.
Qed.

Instance snd_poLe Dom `{PartialOrder Dom} Dom' `{PartialOrder Dom'}
  : Proper (poLe ==> poLe) (@snd Dom Dom').
Proof.
  unfold Proper, respectful; intros.
  inv H1; simpl; eauto.
Qed.

Instance fst_poEq Dom `{PartialOrder Dom} Dom' `{PartialOrder Dom'}
  : Proper (poEq ==> poEq) (@fst Dom Dom').
Proof.
  unfold Proper, respectful; intros.
  inv H1; simpl; eauto.
Qed.

Instance snd_poEq Dom `{PartialOrder Dom} Dom' `{PartialOrder Dom'}
  : Proper (poEq ==> poEq) (@snd Dom Dom').
Proof.
  unfold Proper, respectful; intros.
  inv H1; simpl; eauto.
Qed.


Lemma not_poLt_poLe_poEq X `{PartialOrder X} x y
  : ~ x ⊏ y -> poLe x y -> x === y.
Proof.
  intros.
  eapply poLe_antisymmetric; eauto.
  decide_goal; eauto.
  exfalso. eapply H0. split; eauto.
Qed.

Hint Resolve not_poLt_poLe_poEq : po.

Smpl Add 200
     match goal with
     | [ H : ?A === ?B |- _ ] => inv_if_ctor H A B; clear H
     | [ H : @poEq _ _ ?A ?B |- _ ] => inv_if_ctor H A B; clear H
     | [ H : @poLe _ _ ?A ?B |- _ ] => inv_if_ctor H A B; clear H
     | [ H : ~ ?a === ?a |- _ ] => exfalso; eapply H; reflexivity
     end : inv_trivial.



Lemma poEq_pair_inv A `{PartialOrder A} B `{PartialOrder B} (x y:A * B)
  : poEq x y <-> poEq (fst x) (fst y) /\ poEq (snd x) (snd y).
Proof.
  firstorder.
Qed.

Smpl Add 120
     match goal with
     | [ H : poEq (_,_) (_,_) |- _ ] =>
       rewrite poEq_pair_inv in H; simpl fst in H; simpl snd in H;
         let H' := fresh H in destruct H as [H H']
     | [H : poEq ?x ?x |- _ ] => clear H
     end : inv_trivial.


Ltac is_in_context X :=
  match goal with
  | [ H : ?Y  |- _ ] =>
    unify X Y
  end.


Lemma poLe_false x
  : x ⊑ false -> x = false.
Proof.
  destruct x; inversion 1; eauto.
Qed.

Lemma poLe_true x
  : true ⊑ x -> x = true.
Proof.
  destruct x; inversion 1; eauto.
Qed.

Smpl Add match goal with
         | [ H : _ ⊑ false |- _ ] => eapply poLe_false in H; try subst
         | [ H : false ⊑ _ |- _ ] => eapply poLe_false in H; try subst
         end : inv_trivial.


Lemma poLe_sig_struct D `{PartialOrder D} (P: D -> Prop) (x x':D)  pf pf'
  : x ⊑ x'
    -> @poLe _ (@PartialOrder_sig D _ P) (exist P x pf) (exist P x' pf').
Proof.
  intros. simpl. eapply H0.
Qed.

Lemma poLe_sig_struct' D `{PartialOrder D} (P: D -> Prop) (x x':{x : D | P x})
  : proj1_sig x ⊑ proj1_sig x'
    -> x ⊑ x'.
Proof.
  intros. simpl. eapply H0.
Qed.

Lemma poEq_sig_struct D `{PartialOrder D} (P: D -> Prop) (x x':D)  pf pf'
  : x ≣ x'
    -> @poEq _ (@PartialOrder_sig D _ P) (exist P x pf) (exist P x' pf').
Proof.
  intros. simpl. eapply H0.
Qed.

Lemma poEq_sig_struct' D `{PartialOrder D} (P: D -> Prop) (x x':D)  pf pf'
  : @poEq _ (@PartialOrder_sig D _ P) (exist P x pf) (exist P x' pf')
    -> x ≣ x'.
Proof.
  intros. eapply H0.
Qed.

Lemma poLe_sig_struct'' D `{PartialOrder D} (P: D -> Prop) (x x':D)  pf pf'
  : @poLe _ (@PartialOrder_sig D _ P) (exist P x pf) (exist P x' pf')
    -> x ⊑ x'.
Proof.
  intros. eapply H0.
Qed.

Lemma poLe_sig_destruct D `{PartialOrder D} (P: D -> Prop) (x x':{x : D | P x})
  : x ⊑ x'
    -> proj1_sig x ⊑ proj1_sig x'.
Proof.
  intros. eapply H0.
Qed.

Lemma poEq_sig_destruct D `{PartialOrder D} (P: D -> Prop) (x x':{x : D | P x})
  : x ≣ x'
    -> proj1_sig x ≣ proj1_sig x'.
Proof.
  intros. eapply H0.
Qed.

Hint Resolve poLe_sig_destruct poEq_sig_destruct.



Lemma poLe_list_struct A `{PartialOrder A} (a1 a2:A) b1 b2
  : poLe a1 a2 -> poLe b1 b2  -> poLe (a1::b1) (a2::b2).
  intros; econstructor; eauto.
Qed.

Lemma poEq_list_struct A `{PartialOrder A} (a1 a2:A) b1 b2
  : poEq a1 a2 -> poEq b1 b2  -> poEq (a1::b1) (a2::b2).
  intros; econstructor; eauto.
Qed.

Hint Resolve poLe_list_struct poEq_list_struct.

Lemma poLe_map D `{PartialOrder D} D' `{PartialOrder D'} (f g:D -> D') (L L':list D)
      (LEf:forall a b, poLe a b -> poLe (f a) (g b))
      (LE: poLe L L')
  : poLe (f ⊝ L) (g ⊝ L').
Proof.
  general induction LE; simpl; eauto.
Qed.

Lemma poLe_map_nd D D' `{PartialOrder D'} (f g:D -> D') (L:list D)
      (LEf:forall a, poLe (f a) (g a))
  : poLe (f ⊝ L) (g ⊝ L).
Proof.
  general induction L; simpl; eauto.
Qed.

Lemma poEq_map D `{PartialOrder D} D' `{PartialOrder D'} (f g:D -> D') (L L':list D)
      (LEf:forall a b, poEq a b -> poEq (f a) (g b))
      (LE: poEq L L')
  : poEq (f ⊝ L) (g ⊝ L').
Proof.
  general induction LE; simpl; eauto.
Qed.

Lemma poEq_map_nd D D' `{PartialOrder D'} (f g:D -> D') (L:list D)
      (LEf:forall a, poEq (f a) (g a))
  : poEq (f ⊝ L) (g ⊝ L).
Proof.
  general induction L; simpl; eauto.
Qed.


Instance poLe_poLe_impl (Dom : Type) (H : PartialOrder Dom)
  : Proper (poLe --> poLe ==> impl) poLe.
Proof.
  unfold Proper, respectful , flip, impl; intros.
  eauto.
Qed.

Instance poLe_poLe_flip_impl (Dom : Type) (H : PartialOrder Dom)
  : Proper (poLe ==> flip poLe ==> flip impl) poLe.
Proof.
  unfold Proper, respectful, flip, impl; intros ? ? A ? ? B C.
  eauto.
Qed.


Lemma poLe_app X `{PartialOrder X} (L1 L2 : 〔X〕) (L1' L2' : 〔X〕)
  : poLe L1 L1' -> poLe L2 L2' -> poLe (L1 ++ L2) (L1' ++ L2').
Proof.
  intros. eapply PIR2_app; eauto.
Qed.

Lemma poEq_app X `{PartialOrder X} (L1 L2 : 〔X〕) (L1' L2' : 〔X〕)
  : poEq L1 L1' -> poEq L2 L2' -> poEq (L1 ++ L2) (L1' ++ L2').
Proof.
  intros. eapply PIR2_app; eauto.
Qed.

Hint Resolve poLe_app poEq_app.

Lemma poLe_app_proper X `{PartialOrder X}
  : Proper (poLe ==> poLe ==> poLe) (@List.app X).
Proof.
  unfold Proper, respectful; intros; eauto.
Qed.

Lemma poLe_app_proper_funny X `{PartialOrder X} L
  : Proper (flip poLe ==> flip poLe) (@List.app X L).
Proof.
  unfold Proper, respectful, flip; intros; eauto.
Qed.

Lemma poLe_app_proper' X `{PartialOrder X}
  : Proper (flip poLe ==> flip poLe ==> flip poLe) (@List.app X).
Proof.
  unfold Proper, respectful, flip; intros; eauto.
Qed.

Lemma poLe_app_proper_poEq X `{PartialOrder X}
  : Proper (poEq ==> poEq ==> poEq) (@List.app X).
Proof.
  unfold Proper, respectful; intros; eauto.
Qed.
