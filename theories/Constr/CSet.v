Require Export Setoid Coq.Classes.Morphisms Omega.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Export EqDec Computable Util.
Require Export CSetTac CSetBasic CSetCases CSetGet CSetComputable CSetDisjoint CSetNotation.

Set Implicit Arguments.

(* idk who added this *)
Remove Hints trans_eq_bool.

Lemma minus_de_morgan X `{OrderedType X} x s t
  : (x \In s /\ (x \In t -> False) -> False)
    <-> ((x \In s -> False) \/ (x \In t)).
Proof.
  split; intros; dcr.
  - decide (x ∈ s); decide (x ∈ t); eauto.
  - intuition.
Qed.

Lemma in_dneg X `{OrderedType X} M x
  : x ∈ M <-> ~x ∉ M.
Proof.
  split; repeat intro; eauto.
  decide (x ∈ M); eauto.
  exfalso; eauto.
Qed.

Lemma in_dneg' X `{OrderedType X} M x
  : x ∈ M <-> ((x ∈ M -> False )->False).
Proof.
  split; repeat intro; eauto.
  decide (x ∈ M); eauto.
  exfalso; eauto.
Qed.

Smpl Add match goal with
         | [ |- context [(_ \In _ -> False) -> False] ] =>
           setoid_rewrite <- in_dneg'
         | [ |- context [(_ \In _ -> False) -> False] ] =>
           setoid_rewrite <- in_dneg'
         | [ |- context [(_ ∉ _) -> False] ] =>
           setoid_rewrite <- in_dneg
         end : cset.

Hint Resolve incl_empty minus_incl incl_right incl_left : auto.

Definition pe X `{OrderedType X} := prod_eq (@Equal X _ _) (@Equal X _ _).

Instance pe_morphism X `{OrderedType X}
 : Proper (Equal ==> Equal ==> (@pe X _)) pair.
Proof.
  unfold Proper, respectful.
  intros. econstructor; eauto.
Qed.

Instance pe_refl X `{OrderedType X} : Reflexive (@pe _ _).
Proof.
  hnf; intros. destruct x; econstructor; reflexivity.
Qed.

Instance pe_sym X `{OrderedType X} : Symmetric (@pe _ _).
Proof.
  hnf; intros. inv H0; econstructor; eauto.
  + rewrite H1; eauto; reflexivity.
  + rewrite H2; eauto; reflexivity.
Qed.

Instance pe_trans X `{OrderedType X} : Transitive (@pe _ _).
Proof.
  hnf; intros ? ? ? B C.
  eapply Equivalence_Transitive; eauto using Equal_ST.
Qed.

Ltac pe_rewrite :=
  repeat
    (match goal with
     | [ H : pe ?an _, H' : context [?an] |- _ ] =>
       setoid_rewrite H in H'; simpl in H'
     | [ H : pe ?an _ |-  context [?an] ] =>
       setoid_rewrite H; simpl
     end).


Instance Subset_morphism_2 X `{OrderedType X}
  : Proper (flip Subset ==> Subset ==> impl) (Subset).
Proof.
  unfold Proper, respectful, impl; intros.
  firstorder.
Qed.

Instance Subset_morphism_3 X `{OrderedType X}
  : Proper (Subset ==> flip Subset ==> flip impl) (Subset).
Proof.
  unfold Proper, respectful, impl; intros.
  firstorder.
Qed.

Lemma minus_single_singleton X `{OrderedType X} (s : set X) (x:X)
: s \ singleton x [=] s \ {x; {}}.
Proof.
  cset_tac; intuition.
Qed.

Lemma minus_single_singleton' X `{OrderedType X} (s : set X) (x:X)
: s \ singleton x ⊆ s \ {x; {}}.
Proof.
  cset_tac; intuition.
Qed.

Lemma minus_single_singleton'' X `{OrderedType X} (s : set X) (x:X)
: s \ {x; {}} ⊆ s \ singleton x.
Proof.
  cset_tac; intuition.
Qed.

Lemma fresh_of_list {X} `{OrderedType X} (L:list X) (y:X)
  : Util.fresh y L -> y ∉ of_list L.
Proof.
  general induction L; simpl in *. intro; cset_tac; eauto.
  intro. cset_tac; intuition.
  eapply IHL; eauto. intro. eapply H0. constructor 2. eauto.
Qed.

Hint Extern 20 (?s \ {?x; {}} ⊆ ?s \ singleton ?x) => eapply minus_single_singleton''.
Hint Extern 20 (?s \ singleton ?x ⊆ ?s \ {?x; {}}) => eapply minus_single_singleton'.

Hint Extern 20 (?s \ {?x; {}} [=] ?s \ singleton ?x) => rewrite minus_single_singleton; reflexivity.
Hint Extern 20 (?s \ singleton ?x [=] ?s \ {?x; {}}) => rewrite minus_single_singleton; reflexivity.


Hint Extern 20 (Subset (?a \ _) ?a) => eapply minus_incl.
Hint Extern 20 (Subset (?a \ _) ?a') => progress (first [ has_evar a | has_evar a' | eapply minus_incl ]).

Hint Extern 20 (pe ?a ?a) => reflexivity.

Hint Extern 10 (Subset ?a (_ ∪ ?a)) => eapply incl_right.


Instance diff_proper_impl X `{OrderedType X}
: Proper (flip Subset ==> Subset ==> flip Subset) diff.
Proof.
  unfold Proper, respectful, flip; intros.
  cset_tac; intuition.
Qed.

Definition max_set {X} `{OrderedType X} (a:set X) (b:set X) :=
  if [SetInterface.cardinal a < SetInterface.cardinal b] then
    b
  else
    a.

Lemma cardinal_difference {X} `{OrderedType X} (s t: set X)
: SetInterface.cardinal (s \ t) <= SetInterface.cardinal s.
Proof.
  erewrite <- (diff_inter_cardinal s t).
  omega.
Qed.

Lemma cardinal_difference' {X} `{OrderedType X} (s t: set X)
: t ⊆ s
  -> SetInterface.cardinal (s \ t) = SetInterface.cardinal s - SetInterface.cardinal t.
Proof.
  intros.
  erewrite <- (diff_inter_cardinal s t).
  assert (s ∩ t [=] t). (cset_tac; intuition; eauto).
  rewrite H1. omega.
Qed.


Instance cardinal_morph {X} `{OrderedType X}
: Proper (@Subset X _ _ ==> Peano.le)  SetInterface.cardinal.
Proof.
  unfold Proper, respectful; intros.
  eapply subset_cardinal; eauto.
Qed.

Lemma NoDupA_decons A (R:A->A->Prop) x L
  : NoDupA R (x::L)
    -> NoDupA R L.
Proof.
  inversion 1; eauto.
Qed.

Lemma NoDupA_decons_notin X `{OrderedType X} x L
  :  NoDupA _eq (x :: L)
     -> x ∉ of_list L.
Proof.
  inversion 1; subst. rewrite <- InA_in; eauto.
Qed.

Hint Resolve NoDupA_decons NoDupA_decons_notin.

Lemma cardinal_of_list_nodup {X} `{OrderedType X} (Z:list X)
: NoDupA _eq Z -> SetInterface.cardinal (of_list Z) = length Z.
Proof.
  general induction Z; simpl in * |- *.
  - eapply empty_cardinal.
  - dcr. erewrite cardinal_2; eauto.
Qed.

Instance map_morph_Equal X `{OrderedType X} Y `{OrderedType Y}
         (f : X -> Y) `{Proper _ (_eq ==> _eq) f}
  : Proper (Equal ==> Equal) (map f).
Proof.
  unfold Proper, respectful; intros.
  cset_tac.
Qed.

Instance map_morph_Subset X `{OrderedType X} Y `{OrderedType Y}
         (f : X -> Y) `{Proper _ (_eq ==> _eq) f}
  : Proper (Subset ==> Subset) (map f).
Proof.
  unfold Proper, respectful; intros.
  cset_tac.
Qed.


Instance In_morph_Subset Y `{OrderedType Y}
  : Proper (_eq ==> Subset ==> impl) In.
Proof.
  unfold Proper, respectful, impl; intros.
  eapply H1. rewrite <- H0; eauto.
Qed.

Instance In_morph_Equal Y `{OrderedType Y}
  : Proper (_eq ==> Equal ==> iff) In.
Proof.
  unfold Proper, respectful, impl; intros.
  rewrite H0. cset_tac.
Qed.


Lemma cardinal_map {X} `{OrderedType X} {Y} `{OrderedType Y} (s: set X) (f:X -> Y) `{Proper _ (_eq ==> _eq) f}
: SetInterface.cardinal (SetConstructs.map f s) <= SetInterface.cardinal s.
Proof.
  pattern s. eapply set_induction.
  - intros. repeat rewrite SetProperties.cardinal_1; eauto.
    hnf. intros; intro. eapply map_iff in H3. dcr.
    eapply H2; eauto. eauto.
  - intros.
    erewrite (SetProperties.cardinal_2 H3 H4); eauto.
    decide (f x ∈ SetConstructs.map f s0).
    + assert (SetConstructs.map f s0 [=] {f x; SetConstructs.map f s0}). {
        cset_tac. setoid_rewrite <- H8. eauto.
      }
      rewrite <- H2. rewrite H5.
      assert (SetConstructs.map f s' ⊆ {f x; SetConstructs.map f s0}). {
        hnf; intros. rewrite H5. eapply Add_Equal in H4.
        rewrite H4 in H6.
        cset_tac.
      }
      rewrite <- H6. omega.
    + rewrite <- H2. erewrite <- cardinal_2; eauto.
      split; intros.
      * decide (f x === y); eauto. cset_tac.
        decide (x0 === x).
        -- exfalso. eapply n0. rewrite <- e. eauto.
        -- eexists x0. split; eauto. specialize (H4 x0).
           cset_tac.
      * cset_tac.
        -- eexists x; split; eauto. eapply H4; cset_tac.
        -- eexists x0; split; eauto.
           eapply H4. eauto.
Qed.


Hint Extern 20 ( ?v ∈ singleton ?v ) =>  eapply singleton_iff; reflexivity.
Hint Extern 20 ( ?s ⊆ ?s ∪ _ ) =>  eapply incl_left.
Hint Extern 20 ( ?s ⊆ _ ∪ ?s ) =>  eapply incl_right.
Hint Extern 20 => match goal with
                 | [ H: ?x ∈ ?s, H': ?x ∉ ?s |- _ ] => exfalso; eapply H', H
                 | [ H: ?x === ?y, H': ?x =/= ?y |- _ ] => exfalso; eapply H', H
                 | [ H: ?x === ?y, H': ?x === ?y -> False |- _ ]
                   => exfalso; eapply H', H
                 | [ H: ?y === ?x, H': ?x =/= ?y |- _ ] =>
                   exfalso; eapply H'; symmetry; eapply H
                 | [ H: ?y === ?x, H': ?x === ?y -> False |- _ ] =>
                   exfalso; eapply H'; symmetry; eapply H
                 | [ H: ?x =/= ?x |- _ ] => exfalso; eapply H; reflexivity
                 | [ H: ?x === ?x -> False |- _ ] => exfalso; eapply H; reflexivity
                 end.

Hint Resolve incl_union_left incl_union_right incl_add_right in_add_left
     union_left union_right get_list_union_map : cset.
Hint Resolve prod_eq_intro : cset.
Hint Resolve incl_singleton: cset.
Hint Resolve incl_empty : cset.
Hint Resolve add_struct_eq union_struct_eq_1 union_struct_eq_2 : cset.
Hint Resolve union_incl_split : cset.
Hint Resolve not_in_minus : cset.
Hint Resolve not_incl_minus : cset.

(* general hints *)

Hint Resolve equal_minus_empty incl_minus_empty incl_minus_change incl_minus_union
     incl_union_lr incl_union_left incl_union_right incl_singleton union_incl_split
     : cset.

Hint Resolve incl_empty : auto.

Lemma eq_union_lr (X : Type) (H : OrderedType X) (s s' t t' : set X)
  : s [=] s' -> t [=] t' -> s ∪ t [=] s' ∪ t'.
Proof.
  intros A B. rewrite A, B; eauto.
Qed.

Hint Immediate eq_union_lr : cset.

Lemma union_sym_simpl (X : Type) (H : OrderedType X) (s t : set X)
  : s ∪ t [=] t ∪ s.
Proof.
  eapply union_sym.
Qed.

Hint Resolve union_sym_simpl : cset.


Lemma incl_from_union_eq X `{OrderedType X} s t u
  : t [=] s ∪ u
    -> s ⊆ t.
Proof.
  intro eq; rewrite eq. eauto.
Qed.

Hint Extern 0 =>
match goal with
| [ H1 : ?s ⊆ ?t, H2: ?t ⊆ ?u |- ?s ⊆ ?u] => eapply (Subset_trans H1 H2)
| [ H : ?t [=] ?s ∪ ?u |- ?s ⊆ ?t] => eapply (incl_from_union_eq H)
end : cset.

Lemma add_minus_comm X `{OrderedType X} x s t:
  x ∉ t
  -> {x; s} \ t [=] {x; s \ t}.
Proof.
  cset_tac; intuition; eauto.
Qed.

Hint Resolve add_minus_comm : cset.

Create HintDb pe discriminated.

Ltac pe_rewrite_step :=
  match goal with
     | [ H : pe ?an _, H' : context [?an] |- _ ] =>
       setoid_rewrite H in H'; simpl in H'
     | [ H : pe ?an _ |-  context [?an] ] =>
       setoid_rewrite H; simpl
  end.

Hint Extern 1 => pe_rewrite_step : pe.

Hint Extern 10 =>
match goal with
|  [ |- pe (_, _) (_,_) ] => constructor
end : pe.

Lemma add_single_rm_single_incl X `{OrderedType X} x D
  : {x; D} \ singleton x ⊆ D.
Proof.
  cset_tac.
Qed.

Lemma minus_incl_add X `{OrderedType X} x (s t:set X)
:  s \ singleton x ⊆ t
   -> s [<=]{x; t}.
Proof.
  cset_tac.
Qed.

Lemma incl_minus_single_not_in X `{OrderedType X} x D
  : x ∉ D
    -> D ⊆ D \ singleton x.
Proof.
  cset_tac.
Qed.

Lemma minus_minus_minus_add X `{OrderedType X} s t x
  : s \ t \ singleton x ⊆ s \ {x; t}.
Proof.
  cset_tac.
Qed.

Hint Resolve minus_incl_add add_single_rm_single_incl
     incl_minus_single_not_in minus_minus_minus_add equiv_minus_union
  : cset.

Hint Resolve incl_meet_lr incl_meet_split : cset.

Definition lminus X `{OrderedType X} (s:set X) L := s \ of_list L.

Hint Extern 10 =>
match goal with
| [ H : ?a = ?b, H': ?c = ?b |- ?c = ?a ] => eapply (eq_trans H' (eq_sym H))
| [ H : ?b = ?a, H': ?b = ?c |- ?a = ?c ] => eapply (eq_trans (eq_sym H) H')
end : len.

Lemma incl_minus_both X `{OrderedType X} (s t u: set X)
  : s \ u ⊆ t
    -> u ⊆ t
    -> s ⊆ t.
Proof.
  intros. cset_tac. specialize (H0 a). specialize (H1 a).
  cset_tac. decide (a ∈ u); eauto.
Qed.

Hint Extern 5 =>
match goal with
  | [ H1 : ?s \ ?u ⊆ ?t, H2 : ?u ⊆ ?t |- ?s ⊆ ?t ] => eapply (incl_minus_both H1 H2)
end : cset.

Definition elem_eq {X} `{OrderedType X} (x y: list X) := of_list x [=] of_list y.

Instance elem_eq_refl X `{OrderedType X} : Reflexive (@elem_eq X _).
hnf; intros. hnf. cset_tac; intuition.
Qed.

Definition elem_incl {X} `{OrderedType X} (x y: list X) := of_list x [<=] of_list y.

Instance elem_incl_refl X `{OrderedType X} : Reflexive (@elem_incl _ _).
hnf; intros. hnf. cset_tac; intuition.
Qed.

Instance instance_option_eq_trans_R X {R: relation X} `{Transitive _ R}
 : Transitive (option_eq R).
Proof.
  hnf; intros. inv H0; inv H1.
  + econstructor.
  + econstructor; eauto.
Qed.

Instance instance_option_eq_refl_R X {R: relation X} `{Reflexive _ R}
 : Reflexive (option_eq R).
Proof.
  hnf; intros. destruct x.
  + econstructor; eauto.
  + econstructor.
Qed.

Instance instance_option_eq_sym_R X {R: relation X} `{Symmetric _ R}
 : Symmetric (option_eq R).
Proof.
  hnf; intros. inv H0.
  + econstructor.
  + econstructor; eauto.
Qed.

Instance diff_m_eq X `{OrderedType X}
  : Proper (eq ==> eq ==> eq) diff.
Proof.
  unfold Proper, respectful; intros; subst; eauto.
Qed.

Instance Subset_m_eq_eq_flip_impl X `{OrderedType X}
  : (Proper (eq ==> eq ==> flip impl) Subset).
Proof.
  unfold Proper, respectful, flip, impl; intros; subst; eauto.
Qed.

Instance Subset_m_Equal_eq_flip_impl X `{OrderedType X}
  : (Proper (Equal ==> eq ==> flip impl) Subset).
Proof.
  unfold Proper, respectful, flip, impl; intros; subst.
  rewrite H0; eauto.
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



Lemma card_in_of_list X `{OrderedType X} ( l: list X) :
  NoDupA _eq l -> cardinal (of_list l) = length l.
Proof.
induction l; intro noDup; simpl; eauto.
- rewrite add_cardinal_2.
  + inversion_clear noDup. apply IHl in H1. rewrite H1. eauto.
  + inversion_clear noDup. intro no. apply <- InA_in in no. contradiction.
Qed.



Lemma add_cardinal X `{OrderedType X} (s : set X) x
  : cardinal {x; s} <= S (cardinal s).
Proof.
decide (x ∈ s);
  [apply add_cardinal_1 in i; rewrite i
  |apply add_cardinal_2 in n; rewrite n]; cset_tac.
Qed.



Lemma elements_length  X `{OrderedType X} (s : set X)
: length (elements s) = cardinal s.
Proof.
  rewrite SetInterface.cardinal_1. reflexivity.
Qed.



Lemma elements_of_list_size X `{OrderedType X} ( l : list X) :
  NoDupA _eq l -> length (elements (of_list l)) = length l.
intro noDup. rewrite elements_length. apply card_in_of_list.
exact noDup.
Qed.

Lemma hd_in_list  X `{OrderedType X} ( l : list X)  x :
 l <> nil -> InA _eq (hd x l) l.
intro nonNil.
destruct l.
- isabsurd.
- constructor. simpl. eauto.
Qed.


Lemma hd_in_elements X `{OrderedType X} ( s : set X) x:
 ~ s [=] ∅ -> hd x (elements s) ∈ s.
intro nonEmpty.
apply elements_iff.
apply hd_in_list.
rewrite <- elements_nil_eset.
eauto with cset.
Qed.


Lemma list_eq_app X (R: relation X) (l1 l2 l1' l2' : list X)
: list_eq R l1 l1' -> list_eq R l2 l2' -> list_eq R (l1++l2) (l1'++l2').
Proof.
intros eq1 eq2. general induction eq1; eauto using @list_eq.
Qed.

Lemma cardinal_union_difference X `{OrderedType X} (s t u : set X)
: cardinal (s ∪ (t \ u)) <= cardinal (s ∪ t).
Proof.
assert (s ∪ (t \ u) ⊆ s ∪ t). { cset_tac. }
rewrite H0. eauto.
Qed.


Lemma cardinal_set_tl
      (X : Type) `{OrderedType X}
      (s : set X)
      (n : nat)
  :
    cardinal (of_list (elements s)) = S n
    -> cardinal (of_list (tl (elements s))) = n
.
Proof.
  intro card_Sn.
  remember (elements s) as L.
  general induction L; simpl in *; eauto.
  - rewrite add_cardinal_2 in card_Sn.
    + omega.
    + intro N.
      assert (nn := (elements_3w s)).
      rewrite <- HeqL in nn.
      inversion_clear nn.
      apply H0.
      apply <- InA_in.
      assumption.
Qed.

Lemma cardinal_tl
      (X : Type) `{OrderedType X}
      (n : nat)
      (s : set X)
  :
    cardinal s = S n
    -> cardinal (of_list (tl (elements s))) = n
.
Proof.
  induction n; intros card_s.
  - rewrite <- elements_length in card_s.
    assert (tl (elements s) = nil) as tl_nil.
    + destruct (elements s).
      * simpl. reflexivity.
      * simpl in *. assert (length l = 0). { omega. }
        apply length_zero_iff_nil.
        assumption.
    + rewrite tl_nil. simpl. apply empty_cardinal.
  - apply cardinal_set_tl.
    rewrite of_list_elements.
    assumption.
Qed.

Lemma union_exclusive X `{OrderedType X} s t
  : s ∪ t [=] s ∪ (t \ s).
Proof.
  cset_tac.
Qed.


Lemma in_add_right X `{OrderedType X} s x x'
  : x ∈ s -> x ∈ {x'; s}.
Proof.
  cset_tac; intuition.
Qed.

Hint Resolve in_add_right : cset.


Lemma set_decomp X `{OrderedType X} t s
  : s [=] s ∩ t ∪ (s \ t).
Proof.
  cset_tac. decide (a ∈ t); eauto.
Qed.

(* Hint Resolve <- / -> is implicitly local *)
Hint Resolve <- map_iff : cset.
Hint Resolve -> map_iff : cset.

Lemma map_spec_1 : forall (A : Type) (HA : OrderedType A) (B : Type) (HB : OrderedType B) (f : A -> B),
       Proper (_eq ==> _eq) f ->
       forall (s : ⦃A⦄) (b : B), b ∈ map f s -> (exists a : A, a ∈ s /\ b === f a).
  intros; eauto with cset.
Qed.

Lemma map_spec_2 : forall (A : Type) (HA : OrderedType A) (B : Type) (HB : OrderedType B) (f : A -> B),
       Proper (_eq ==> _eq) f ->
       forall (s : ⦃A⦄) (b : B), (exists a : A, a ∈ s /\ b === f a) -> b ∈ map f s.
  intros; eauto with cset.
Qed.

Hint Resolve map_spec_1 map_spec_2 : cset.


Lemma incl_minus_incl_union X `{OrderedType X} s t u
  : s \ t ⊆ u
    -> s ⊆ t ∪ u.
Proof.
  intros. rewrite <- H0. cset_tac.
Qed.

Lemma incl_union_lr_eq X `{OrderedType X} s t u v
  : s ∪ t [=] u
    -> v ∪ t ⊆ v ∪ u.
Proof.
  intros. rewrite <- H0. eauto with cset.
Qed.

Lemma incl_union_eq X `{OrderedType X} s t u
  : s ∪ t [=] u
    -> t ⊆ u.
Proof.
  intros. rewrite <- H0. eauto with cset.
Qed.

Lemma incl_add_union_union X `{OrderedType X} s x t u
  : s [=] {x; t}
    -> {x; u} ∪ t ⊆ u ∪ s.
Proof.
  intros. rewrite H0. cset_tac.
Qed.

Hint Immediate incl_minus_incl_union incl_union_lr_eq incl_union_eq incl_add_union_union : cset.


Lemma filter_add_in X `{OrderedType X} (p:X -> bool) `{Proper _ (_eq ==> eq) p} x s
  : p x -> SetInterface.filter p {x;s} [=] {x; SetInterface.filter p s}.
Proof.
  intros P; split; intros In; cset_tac.
Qed.

Lemma filter_add_notin X `{OrderedType X} (p:X -> bool) `{Proper _ (_eq ==> eq) p} x s
  : ~ p x -> SetInterface.filter p {x;s} [=] SetInterface.filter p s.
Proof.
  intros P; split; intros In; cset_tac.
  - exfalso; eapply P. rewrite H3; eauto.
Qed.

Lemma filter_incl X `{OrderedType X} (p:X -> bool) `{Proper _ (_eq ==> eq) p} s
  : SetInterface.filter p s ⊆ s.
Proof.
  hnf; intros. eapply zfilter_1; eauto.
Qed.

Lemma filter_add_incl X `{OrderedType X} (p:X -> bool) `{Proper _ (_eq ==> eq) p} s x
  : SetInterface.filter p {x; s} ⊆ {x; SetInterface.filter p s}.
Proof.
  decide (p x).
  - rewrite filter_add_in; eauto.
  - rewrite filter_add_notin; eauto with cset.
Qed.


Lemma filter_difference X `{OrderedType X} (p:X->bool) `{Proper _ (_eq ==> eq) p} s t
  : filter p (s \ t) [=] filter p s \ filter p t.
Proof.
  cset_tac. eapply H3; cset_tac.
Qed.

Lemma subset_filter X `{OrderedType X} (p:X->bool) `{Proper _ (_eq ==> eq) p} (lv lv':set X)
  : lv ⊆ lv'
    -> filter p lv ⊆ filter p lv'.
Proof.
  cset_tac.
Qed.

Lemma decide_mem_1 X `{OrderedType X} x (s:set X)
  : (x ∈ s -> False) \/ x ∈ s.
Proof.
  decide (x ∈ s); eauto.
Qed.

Lemma decide_mem_2 X `{OrderedType X} x (s:set X)
  : x ∈ s \/ (x ∈ s -> False).
Proof.
  decide (x ∈ s); eauto.
Qed.

Hint Resolve decide_mem_1 decide_mem_2.