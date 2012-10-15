Require Import Setoid. 
Require List.
Require Import EqDec Util.

Set Implicit Arguments.

Definition fresh X (x:X) (Y:list X) : Type :=
  ~List.In x Y.

Fixpoint unique X (Y:list X) : Type :=
  match Y with
    | nil => True
    | cons x Y' => (fresh x Y' * unique Y')%type
  end.


Module Type CSet.
  Parameter cset    : Type -> Type.
  Parameter empty   : forall {X:Type}, cset X.
  Parameter single  : forall X:Type, X -> cset X.
  Parameter join    : forall X:Type, cset X -> cset X -> cset X.
  Parameter meet    : forall X:Type, cset X -> cset X -> cset X.
  Parameter member  : forall X:Type, X -> cset X -> bool.
  Parameter complement  : forall X:Type, cset X -> cset X.
  Parameter forallb : forall X:Type, cset X -> (X -> bool) -> bool.
  Parameter fold : forall X Y:Type, cset X -> (X -> Y -> Y) -> Y.
  Parameter elements : forall X:Type, cset X -> list X.

  Parameter empty_spec :
    forall X (x:X), member x empty = false.
  Parameter single_spec :
    forall X (x y:X), member x (single y) <-> x = y.

  Parameter union_spec :
    forall X s t (x:X), member x (join s t) = orb  (member x s) (member x t).
  Parameter intersection_spec :
    forall X s t (x:X), member x (meet s t) = andb (member x s) (member x t).

  Parameter complement_spec :
    forall X s (x:X), member x (complement s) = negb (member x s).

  Definition add X (x : X) (s : cset X) := join (single x) s.

  Parameter set_extensionality 
    : forall X (s t : cset X),
      (forall x, member x s = member x t) -> s = t.

  Parameter forallb_spec 
    : forall X s (p:X->bool), forallb s p <-> forall x, member x s -> p x.

  Parameter elements_unique 
    : forall X (s:cset X), unique (elements s).

  Parameter elements_spec
    : forall X (s:cset X) x, member x s <-> List.In x (elements s).

  Definition incl X (s t:cset X) :=
    forall x, member x s -> member x t. 

  Parameter size : forall X : Type, cset X -> nat.

  Parameter size_spec : forall X (s : cset X), size s = length (elements s).
(*
  Parameter set_ind
    : forall X (P:cset X -> Prop), P empty 
      -> (forall (x:X) (s:cset X), P s -> ~member x s -> P (join (single x) s))
      -> forall s:cset X, P s.
*)
End CSet.

Module Type CSetNotation (Import M : CSet).
  Infix "∪" := join (at level 50) : cset_scope.
  Infix "∩" := meet (at level 50) : cset_scope.
  Notation "x '∉' s" := (~member x s) (at level 59) : cset_scope.
  Notation "x '∈' s" := (member x s) (at level 60) : cset_scope.
  Notation "∅" := empty : cset_scope.
  Notation "{{ x , .. , y }}" :=
    (add x .. (add y empty) ..) : cset_scope.
  Notation "s '⊆' t" := (incl s t) (at level 60) : cset_scope.
End CSetNotation.

Module Type CSet' := CSet <+ CSetNotation.

Module Type CSetEquality (Import M : CSet').
  Open Scope cset_scope.
  (** * Extensional equality of sets. *)
  Definition eq_cset X (s t : cset X) : Prop :=
    forall x, member x s = member x t.
  Hint Unfold eq_cset.

  (** Proof that this is indeed an equivalence relation. *)
  Lemma eq_cset_reflexivity X (s : cset X) : eq_cset s s.
  Proof. auto. Qed.

  Lemma eq_cset_symmetry X (s t : cset X) : eq_cset s t -> eq_cset t s.
  Proof. auto. Qed.

  Lemma eq_cset_transitivity X (s t u : cset X) : eq_cset s t -> eq_cset t u -> eq_cset s u.
  Proof. unfold eq_cset. intros. rewrite H. auto. Qed.

  (** Register it as a setoid and proof that all operations are proper morphisms. *)
  Add Parametric Relation X : (cset X) (@eq_cset X)
    reflexivity  proved by (@eq_cset_reflexivity X)
    symmetry     proved by (@eq_cset_symmetry X)
    transitivity proved by (@eq_cset_transitivity X)
    as cset_setoid.

  Add Parametric Morphism X : (@member X)
    with signature eq ==> (@eq_cset X) ==> eq as member_morphism.
  Proof.
    intros x s t A. rewrite A. reflexivity.
  Qed.

  Add Parametric Morphism X : (@join X)
    with signature (@eq_cset X) ==> (@eq_cset X) ==> (@eq_cset X) as join_morphism.
  Proof.
    intros ? ? A ? ? B ?. repeat rewrite union_spec. rewrite A.
    rewrite B. auto.
  Qed.

  Add Parametric Morphism X : (@meet X)
    with signature (@eq_cset X) ==> (@eq_cset X) ==> (@eq_cset X) as meet_morphism.
  Proof.
    intros ? ? A ? ? B ?. repeat rewrite intersection_spec.
    rewrite A. rewrite B. auto.
  Qed.

  Add Parametric Morphism X : (@add X)
    with signature eq ==> (@eq_cset X) ==> (@eq_cset X) as add_morphism.
  Proof.
    intros ? ? ? A ?. unfold add. rewrite A. auto.
  Qed.
End CSetEquality.

Module Type CsetEqualityDec (Import M : CSet') (Import E : CSetEquality M).
End CsetEqualityDec.


Module BSet <: CSet.

  Parameter cset    : Type -> Type.
  Parameter empty   : forall {X:Type}, cset X.
  Parameter single  : forall X:Type, X -> cset X.
  Parameter join    : forall X:Type, cset X -> cset X -> cset X.
  Parameter meet    : forall X:Type, cset X -> cset X -> cset X.
  Parameter member  : forall X:Type, X -> cset X -> bool.
  Parameter forallb : forall X:Type, cset X -> (X -> bool) -> bool.

  Parameter empty_spec :
    forall X (x:X), member x empty = false.
  Parameter single_spec :
    forall X (x y:X), member x (single y) <-> x = y.

  Parameter union_spec :
    forall X s t (x:X), member x (join s t) = orb  (member x s) (member x t).
  Parameter intersection_spec :
    forall X s t (x:X), member x (meet s t) = andb (member x s) (member x t).

  Definition add X (x : X) (s : cset X) := join (single x) s.

  Parameter set_extensionality 
    : forall X (s t : cset X),
      (forall x, member x s = member x t) -> s = t.

  Parameter forallb_spec 
    : forall X s (p:X->bool), forallb s p <-> forall x, member x s -> p x.

  Parameter minus  : forall X:Type, cset X -> cset X -> cset X.

  Parameter minus_spec :
    forall X s t (x:X), member x (minus s t) = andb (member x s) (negb (member x t)).

  Infix "\" := minus (at level 50) : cset_scope.

  Parameter complement  : forall X:Type, cset X -> cset X.

  Parameter complement_spec :
    forall X s (x:X), member x (complement s) = negb (member x s).

  Parameter fold : forall X Y:Type, cset X -> (X -> Y -> Y) -> Y.
  Parameter elements : forall X:Type, cset X -> list X.

  Parameter elements_unique 
    : forall X (s:cset X), unique (elements s).
  
  Definition incl X (s t:cset X) :=
    forall x, member x s -> member x t. 

  Parameter elements_spec
    : forall X (s:cset X) x, member x s <-> List.In x (elements s).

  Parameter size : forall X : Type, cset X -> nat.

  Parameter size_spec : forall X (s : cset X), size s = length (elements s).


  Include CSetNotation.
  Include CSetEquality.
 
  
  Ltac cset_assumption :=
    match goal with
      | [ H : context [ member ?x (join ?s ?t) ] |- _ ] =>
        rewrite (union_spec s t x) in H
      | [ H : context [ member ?x (meet ?s ?t) ] |- _ ] =>
        rewrite (intersection_spec s t x) in H
      | [ H : context [ member ?x (minus ?s ?t) ] |- _ ] =>
        rewrite (minus_spec s t x) in H
      | [ H : context [ member ?x empty ] |- _ ] => 
        rewrite (empty_spec x) in H
      | [ H : context [ Is_true (member ?x (single ?y)) ] |- _ ] => 
        rewrite (single_spec x y) in H
      | [ |- not ?Q ] => intro
      | [ |- ?P = ?Q ] => match type of P with
                            | bool => eapply bool_extensionality; intros
                            | cset _ => eapply set_extensionality; intros
                          end

    (* goal *)
      | [ |- context [ member ?x (join ?s ?t) ]] =>
        rewrite (union_spec s t x)
      | [ |- context [ member ?x (meet ?s ?t) ]] =>
        rewrite (intersection_spec s t x)
      | [ |- context [ member ?x (minus ?s ?t) ]] =>
        rewrite (minus_spec s t x)
      | [ |- context [ member ?x empty ]] => 
        rewrite (empty_spec x)
      | [ |- context [ Is_true (member ?x (single ?y)) ]] => 
        rewrite (single_spec x y) 
    end.

  Ltac cset_tac_step := 
    intros; (try subst); decompose records; destr; cset_assumption ||
      bool_to_prop || bool_to_prop in *.

  Ltac cset_tac :=
    unfold add in *; 
      repeat (cset_tac_step). 

  Lemma single_spec_neq X (x y:X)
    : x ∈ {{y}} -> x = y.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma in_add_case X `{EqDec X eq} s (x y:X)
    : y ∈ {{x}} ∪ s -> x=y \/ (x<>y /\ y ∈ s).
  Proof.
    destruct_prop (x=y); cset_tac; firstorder.
  Qed.

  Lemma neq_not_in_single X (x y:X)
    :  x <> y -> ~x ∈ {{y}}.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_empty X (s:cset X)
    : s\∅ = s.
  Proof.
    cset_tac; firstorder.
  Qed.

  
  Lemma minus_in_in X s t (x:X)
    : x ∈ (s \ t) -> x ∈ s /\ ~x ∈ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma in_in_minus X s t (x:X)
    : x ∈ s -> ~x ∈ t -> x ∈ (s \ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma in_in_neq X s (x y:X)
    : x ∈ s -> ~y ∈ s -> x <> y.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_comm X (s t:cset X)
    : s ∪ t = t ∪ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_inane X s (x:X)
    : x ∉ s
    -> s = (s\{{x}}).
  Proof.
    repeat (cset_tac; subst; firstorder).
  Qed.

  Lemma not_in_empty X (x:X)
    : x ∉ ∅.
  Proof.
    cset_tac; firstorder.
  Qed.


  Lemma minus_inane_set X (s t:cset X)
    : s ∩ t = ∅ -> (s \ t) = s.
  Proof.
    cset_tac; firstorder.
    eapply (not_in_empty x). rewrite <- H.
    cset_tac; firstorder.
  Qed.

  Lemma minus_union_set X (s t:cset X)
    : s ∩ t = ∅ -> ((s ∪ t) \ t) = s.
  Proof.
    cset_tac; firstorder.
    eapply (not_in_empty x). rewrite <- H.
    cset_tac; firstorder.
  Qed.


  Lemma in_minus_neq X s (x y:X)
    : x <> y -> x ∈ s
    -> x ∈ (s\{{y}}).
  Proof.
    repeat (cset_tac; subst; firstorder).
  Qed.

  Lemma add_inane X s (x:X) 
    : x ∈ s
    -> s = ({{x}} ∪ s).
  Proof.
    repeat (cset_tac; subst; firstorder).
  Qed.

  Lemma in_single_union X s (y:X)
    : y ∈ {{y}} ∪ s.
  Proof.
    repeat (cset_tac; subst; firstorder).
  Qed.

  Lemma minus_union X (s t u:cset X)
    : (s \ t \ u) = s \ (t ∪ u).
  Proof.
    repeat (cset_tac; subst; firstorder).
  Qed.

  Lemma incl_empty X (s:cset X)
    : ∅ ⊆ s.
  Proof.
    hnf; intros; cset_tac; firstorder.
  Qed.


  Lemma incl_trans X (s t u:cset X)
    : incl s t -> incl t u -> incl s u.
  Proof.
    firstorder.
  Qed.

  Lemma minus_incl X (s t:cset X)
    : (s\t) ⊆ s.
  Proof.
    hnf; cset_tac; firstorder.
  Qed.

  Lemma empty_neutral_union X (s:cset X)
    : ∅ ∪ s = s.
  Proof.
    cset_tac; firstorder.
  Qed.


  Lemma incl_add X s (x:X)
    :  incl s ({{x}} ∪ s).
  Proof.
    hnf; cset_tac; firstorder.
  Qed.

  Lemma incl_union X (s t:cset X)
    :  incl s (t ∪ s).
  Proof.
    hnf; cset_tac; firstorder.
  Qed.


  Lemma incl_minus X (s t : cset X)
    :  incl (s \ t) s.
  Proof.
    hnf; cset_tac; firstorder.
  Qed.


  Lemma union_assoc X (s t u : cset X)
    : s ∪ t ∪ u = s ∪ (t ∪ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_set_decomp X (s t:cset X)
    : incl s t -> t = s ∪ (t \ s).
  Proof.
    cset_tac; firstorder.
    destruct_prop (x ∈ s); firstorder.
  Qed.

  Lemma incl_union_minus X (s t:cset X)
    : incl s (t ∪ (s \ t)).
  Proof.
    hnf; cset_tac. 
    destruct_prop (x ∈ t); firstorder.
  Qed.

  Lemma union_minus_incl X (s t:cset X)
    : incl ((t ∪ s) \ t) s.
  Proof.
    hnf; cset_tac; firstorder.
  Qed.

  Lemma incl_minus_lr X (s s' t t':cset X)
    : s ⊆ s' -> t ⊆ t' -> s \ t' ⊆ s' \ t.
  Proof.
    intros; hnf in *; hnf; cset_tac; firstorder.
  Qed.


  Lemma union_idem X (s:cset X)
    : s ∪ s = s.
  Proof.
    hnf; cset_tac; firstorder.
  Qed.

  Require Import List.
  
  Fixpoint fromList X(L:list X) :=
    match L with
      | nil => ∅
      | x::L' => {{x}} ∪ fromList L'  
    end.

  Lemma in_fromList X (L:list X) y
    : y ∈ fromList L <-> In y L.
  Proof.
    induction L; split; simpl; intros; cset_tac; firstorder.
  Qed.

  Lemma union_minus X s (x:X)
    : x ∉ s -> s = ({{x}} ∪ s) \ {{x}}.
  Proof.
    repeat (cset_tac; firstorder). 
  Qed.

  Lemma minus_in X s t (x:X)
    : x ∉ s -> x ∉ t -> x ∉ (s ∪ t).
  Proof.
    repeat (cset_tac; firstorder). 
  Qed.

  Lemma union_cases X s t (x:X)
    : x ∈ (s ∪ t) -> x ∈ s \/ x ∈ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma not_in_union_comp A (s t : cset A) x :
    ~x ∈ s /\ ~x ∈ t -> ~x ∈ (s ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma not_in_union_decomp X s t (x:X)
    : x ∉ (s ∪ t) -> x ∉ s /\ x ∉ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_left X s t (x:X)
    : x ∈ s -> x ∈ (s ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_right X s t (x:X)
    : x ∈ t -> x ∈ (s ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma set_fact_1 X `(EqDec X eq) s t (x:X)
    : x ∉ t
    -> {{x}} ∪ (s \ ({{x}} ∪ t)) = {{x}} ∪ s \ t.
  Proof.
    intros.
    cset_tac_step. cset_tac_step. 
    edestruct (union_cases _ _ _ H1); clear H1; repeat (cset_tac; subst; firstorder).
    edestruct (minus_in_in _ _ _ H1); clear H1. 
    edestruct (union_cases _ _ _ H2); clear H2.
    eapply union_left; eauto.
    destruct_prop (x=x0); subst. eapply union_left. cset_tac; firstorder.
    eapply union_right; eauto.
    eapply in_in_minus; eauto. intro. cset_tac; firstorder.
  Qed.

  Lemma set_fact_2 X s t (x:X)
    : (s \ ({{x}} ∪ t)) \ {{x}} = s \ ({{x}} ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma fresh_fromList X (L:list X) y
    : fresh y L -> y ∉ fromList L.
  Proof.
    intros A B. eapply in_fromList in B. firstorder.
  Qed.

  Lemma incl_union_absorption X (s t:cset X)
    : s ⊆ t -> s ∪ t = t.
  Proof.
    intros; hnf in *; hnf; cset_tac; firstorder.
  Qed.

  Lemma incl_union_lr X (s s' t t':cset X)
    : s ⊆ s' -> t ⊆ t' -> s ∪ t ⊆ s' ∪ t'.
  Proof.
    intros; hnf in *; hnf; cset_tac; firstorder.
  Qed.


  Lemma incl_not_in X (ED:EqDec X eq) (x:X) s t
    : x ∉ s -> s\{{x}} ⊆ t -> s ⊆ t.
  Proof.
    intros; hnf; intros. eapply H0.
    destruct_prop (x0=x); subst.
    exfalso. eauto.
    eapply in_in_minus; eauto. cset_tac; firstorder.
  Qed.

  Lemma incl_left X (s t:cset X)
    : s ⊆ (s ∪ t).
  Proof.
    hnf; intros. cset_tac; firstorder.
  Qed.

  Lemma in_meet X (s t:cset X) (x:X)
    : x ∈ s -> x ∈ t -> x ∈ s ∩ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_in X (s t:cset X) (x:X)
    : x ∈ s ∩ t -> x ∈ s /\ x ∈ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_incl X (s t u:cset X) 
    : s ⊆ u -> s ∩ t ⊆ u.
  Proof.
    intros; hnf in *; cset_tac; firstorder.
  Qed.

  Lemma meet_comm X (s t:cset X)
    : s ∩ t = t ∩ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_meet X (s t:cset X)
    : s ⊆ t -> s = s ∩ t.
  Proof.
    repeat (cset_tac; subst; firstorder).
  Qed.

  Lemma incl_refl X (s:cset X)
    : s ⊆ s.
  Proof.
    firstorder.
  Qed.

  Lemma minus_meet X (s t u:cset X)
    : (s \ t) ∩ u = s ∩ u \ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma set_incl X (s t: cset X)
    : s ⊆ t -> t ⊆ s -> t = s.
  Proof.
    intros; hnf in *; cset_tac; firstorder.
  Qed.


  Lemma elements_nil_eset {X : Type} (s : cset X) :
    s = ∅ <-> elements s = nil.
  Proof.
    split; intros.
    rewrite H; clear H.
    remember (@elements X ∅) as l.
    destruct l.
    reflexivity.
    assert (In x (x :: l)) by (apply in_eq).
    rewrite Heql in H.
    rewrite <- elements_spec in H.
    cset_tac. inversion H.

    specialize (elements_spec s); intros.
    rewrite H in H0. simpl in H0.
    cset_tac. specialize (H0 x). tauto. inv H1.
  Qed.

  Lemma fromList_elements X :
    forall s, fromList (@elements X s) = s.
  Proof.
    cset_tac. rewrite in_fromList in H. rewrite elements_spec. assumption.
    rewrite in_fromList. rewrite elements_spec in H. assumption.
  Qed.

  Lemma elements_fromList_in X (l : list X) x :
    In x l <-> In x (elements (fromList l)).
  Proof.
    split; intros.
    rewrite <- elements_spec.
    rewrite in_fromList; assumption.
    rewrite <- elements_spec in H.
    rewrite in_fromList in H; assumption.
  Qed.

  Lemma fromList_eq X :
    forall l l', l = l' -> @fromList X l = @fromList X l'.
  Proof.
    intros.
    destruct l, l'; try (inversion H); try reflexivity.
  Qed.

  Lemma forallb_add {X : Type} {ED:EqDec X eq} (s : cset X) (f : X -> bool) (x : X) : 
    BSet.forallb ({{x}} ∪ s) f = (f x) && (BSet.forallb s f).
  Proof.
    apply eq_bool_prop_intro.
    intros; split; intros.
    rewrite forallb_spec in H.
    bool_to_prop. split.
    eapply H. cset_tac; firstorder.
    rewrite forallb_spec.
    intros.
    eapply H. cset_tac; firstorder.

    bool_to_prop in H.
    invc H.
    rewrite forallb_spec.
    intros.
    destruct_prop (x = x0). subst x0; assumption.
    cset_tac. firstorder.
    rewrite forallb_spec in H1.
    eauto.
  Qed.

  Lemma forallb_false {X : Type} {ED:EqDec X eq} (s : cset X) (f : X -> bool) :
    BSet.forallb s f = false <-> exists x, x ∈ s /\ f x = false.
  Proof.
    rewrite <- negb_true_iff.
    remember (elements s) as l.
    specialize (elements_unique s); intro Huniq.
    rewrite <- Heql in Huniq.
    simpl in Huniq.
    apply fromList_eq in Heql.
    generalize dependent s.
    induction l; intros; split; intros.

    apply Is_true_eq_left in H; bool_to_prop in H; 
       symmetry in Heql; simpl in Heql; rewrite fromList_elements in Heql.
    subst s. rewrite forallb_spec in H. exfalso. apply H. intros. cset_tac. inv H0.
    apply Is_true_eq_true; bool_to_prop;
    symmetry in Heql; simpl in Heql; rewrite fromList_elements in Heql.
    intro. subst s. cset_tac. inv H2.

    simpl in Heql.
    rewrite fromList_elements in Heql.
    specialize (IHl (snd Huniq) (fromList l)).
    rewrite fromList_elements in IHl.
    specialize (IHl (eq_refl (fromList l))).

    rewrite <- Heql in H.
    rewrite forallb_add in H.
    rewrite negb_andb in H.
    apply orb_true_iff in H.
    rewrite negb_true_iff in H.
    inversion H.
    exists a. split.
    rewrite <- Heql.
    apply in_single_union.
    assumption.

    apply IHl in H0.
    inversion H0.
    exists x.
    invc H1.
    split; [ eapply union_right | idtac ]; assumption.
    
    inversion H.
    invc H0.
    apply Is_true_eq_true.
    bool_to_prop; intro.
    rewrite forallb_spec in H0.
    specialize (H0 x H1).
    apply Is_true_eq_true in H0.
    rewrite H2 in H0.
    inversion H0.
  Qed.

  Lemma forallb_eq_funs {X : Type} (s : cset X) (f g : X -> bool) :
    (forall x, x ∈ s -> f x = g x) -> BSet.forallb s f = BSet.forallb s g.
  Proof.  
    intros.
    apply eq_bool_prop_intro.
    repeat rewrite forallb_spec.
    split; intros;
    specialize (H x H1); specialize (H0 x H1); [ rewrite <- H | rewrite H ]; assumption.
  Qed.

  Lemma not_empty_contains_element {X : Type} (s : cset X) :
    s <> ∅ <-> exists x, x ∈ s.
  Proof.
    split; intros.
    remember (elements s) as l.
    generalize dependent s.
    destruct l; intros.
    exfalso. apply H. apply elements_nil_eset. symmetry. assumption.
    specialize (@fromList_elements X s); intros.
    rewrite <- Heql in H0. simpl in H0.
    rewrite <- H0.
    exists x.
    apply in_single_union.

    cset_tac; firstorder.
  Qed.

  (*
  Lemma not_empty_split {X : Type} (s : cset X) :
    s <> ∅ <-> exists x, exists s', ~ x ∈ s' /\ s = {{x}} ∪ s'.
  Proof.
    split; intros.
    apply not_empty_contains_element in H.
    invc H.
    exists x.
    exists (s \ {{x}}).
    split. cset_tac; firstorder.
    eapply incl_set_decomp.
    unfold incl.
    intros.
    cset_tac. invc H; [ subst; assumption | firstorder ].
  
    invc H. invc H0. invc H. intro. apply H0.
    rewrite elements_nil_eset in H.
    specialize (elements_spec ({{x}} ∪ x0)); intros.
    specialize (H1 x).
    rewrite H in H1.
    exfalso. eapply in_nil. apply H1. cset_tac; firstorder.
  Qed.
  *)

  Lemma union_meet_distr_r {A} (s t u : cset A) :
    (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_is_empty {A} (s t : cset A) :
    s ∪ t = ∅ -> (s = ∅ /\ t = ∅).
  Proof.
    cset_tac; firstorder.
    apply (union_left s t) in H0. rewrite H in H0. rewrite empty_spec in H0. assumption.
    apply (union_left t s) in H0. rewrite union_comm in H0. rewrite H in H0. rewrite empty_spec in H0. assumption.
  Qed.

  Lemma smaller_meet_empty {A} (s t u : cset A) :
    (s ∪ t) ∩ u = ∅ -> t ∩ u = ∅.
  Proof.
    intros. cset_tac. 
    rewrite union_meet_distr_r in H.
    specialize (in_meet t u x H1 H2); intros.
    apply union_is_empty in H. invc H. rewrite H4 in H0. rewrite empty_spec in H0. assumption.
    inv H0. inv H0.
  Qed.

  Lemma empty_intersection_in_one_not_other {A} (s t : cset A) x :
    s ∩ t = ∅ -> x ∈ s -> ~ x ∈ t.
  Proof.
    cset_tac. apply (not_in_empty x). rewrite <- H. apply in_meet; assumption.
  Qed.

  Lemma not_empty_split {X : Type} (s : cset X) :
    s <> ∅ <-> exists x, exists s', ~ x ∈ s' /\ s = {{x}} ∪ s'.
  Proof.
    split; intros.
    apply not_empty_contains_element in H.
    inversion H; clear H.
    exists x.
    exists (s \ {{x}}).
    split. cset_tac; firstorder.
    eapply incl_set_decomp.
    unfold incl.
    intros.
    hnf; repeat (cset_tac; firstorder).
  
    cset_tac; firstorder.
    rewrite elements_nil_eset in H.
    specialize (elements_spec ({{x}} ∪ x0)); intros.
    specialize (H1 x).
    unfold add in H1. rewrite H in H1.
    exfalso. eapply in_nil. apply H1. cset_tac; firstorder.
  Qed.

  Lemma meet_assoc X (s t u : cset X)
    : s ∩ t ∩ u = s ∩ (t ∩ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_meet_lr X (s s' t t':cset X)
    : s ⊆ s' -> t ⊆ t' -> s ∩ t ⊆ s' ∩ t'.
  Proof.
    intros; hnf in *; hnf; cset_tac; firstorder.
  Qed.














  Lemma unique_remove {A : Type} (p q : list A) (x : A) :
    unique (p ++ x :: q) -> unique (p ++ q).
  Proof.
    induction p; simpl in *; intros. apply (snd X).
    specialize (IHp (snd X)).
    constructor.
    intro.
    apply (fst X).
    apply in_app_or in H.
    apply in_or_app.
    inversion H; auto. right. simpl. right. assumption.
    assumption.
  Qed.

  Lemma unique_replace {A : Type} (p q : list A) (x y : A) :
    unique (p ++ x :: q) ->
    ~ In y p ->
    ~ In y q ->
    unique (p ++ y :: q).
  Proof.
    intros.
    generalize dependent y.
    generalize dependent q.
    induction p; intros; simpl in *; constructor.
    apply H0. apply (snd X).
    intro.
    apply in_app_or in H1.
    firstorder.

    apply IHp.
    apply (snd X).
    firstorder.
    assumption.
  Qed.   

  Lemma unique_split {A : Type} (p q : list A) (x : A) :
    unique (p ++ x :: q) -> (~ In x p /\ ~ In x q).
  Proof.
    intros.
    induction p.
    simpl in *.
    split; auto. apply (fst X).
    simpl in X.
    specialize (IHp (snd X)).
    inversion IHp.
    split; intro.
    apply H. simpl in H1. inversion H1. subst x.
    exfalso. apply (fst X).
    apply in_or_app. right. simpl. auto.
    assumption.
    auto.
  Qed.

  Lemma length_unique_eq {A : Type} `{EqDec A eq} (l l' : list A) :
    unique l ->
    unique l' ->
    (forall x, In x l <-> In x l') ->
    length l = length l'.
  Proof.
    intros.
    generalize dependent l'.
    induction l; intros.
    destruct l'.
    reflexivity.
    exfalso.
    simpl in H0.
    rewrite H0.
    left. apply (eq_refl a).

    destruct l'; simpl in *.
    exfalso. rewrite <- H0. left; apply (eq_refl a).

    destruct_prop (a = a0).
    subst a0. f_equal.
    apply IHl. apply (snd X). apply (snd X0).
    intros; rewrite <- or_cancel_l.
    apply H0.
    intros. intro. apply (fst X). subst a; assumption.
    intros. intro. apply (fst X0). subst a; assumption.

    assert (In a l') by firstorder.
    apply in_split in H1.
    inversion H1 as [p [q Hpq]]; clear H1.

    assert (length (p ++ a0 :: q) = length l').
    rewrite Hpq.
    repeat rewrite app_length.
    f_equal.
    rewrite <- H1.
    f_equal.
    apply IHl.
    apply (snd X).
    eapply unique_replace.
    assert (unique (p ++ a :: q)) by (rewrite <- Hpq; apply (snd X0)).
    apply X1.
    intro. apply (fst X0). rewrite Hpq. apply in_or_app. auto.
    intro. apply (fst X0). rewrite Hpq. apply in_or_app. right. apply in_cons. assumption.
    
    intros; split; intros; specialize (H0 x).
    specialize (fst X); intros. unfold fresh in X1.
    destruct_prop (a0 = x); apply in_or_app.
    subst x. right. apply in_eq.
    assert (In x l') by firstorder.
    rewrite Hpq in H3.
    apply in_app_or in H3.
    inversion H3. left. assumption. right.
    simpl in H4.
    inversion H4.
    subst a. absurd (In x l); assumption.
    apply in_cons. assumption.

    assert (x <> a).
    intro. apply (fst X).
    subst x.
    apply in_app_or in H2.
    assert (~ In a p /\ ~ In a q).
    apply unique_split. rewrite <- Hpq. apply (snd X0).
    inversion H3. clear H3.
    inversion H2. contradiction.
    simpl in H3. exfalso; firstorder.
    
    destruct_prop (a0 = x). firstorder.
    assert (In x (p ++ a :: q)).
    apply in_app_or in H2.
    inversion H2. apply in_or_app. left. assumption.
    simpl in H4.
    inversion H4. absurd (a0 = x); assumption.
    apply in_or_app. right. simpl. right. assumption.
    rewrite <- Hpq in H4.
    firstorder.
  Qed.

  Lemma fromList_size {A : Type} `{EqDec A eq} (p : list A) :
    unique p -> size (fromList p) = length p.
  Proof.
    induction p; intros. simpl in *.
    rewrite size_spec.
    assert (@elements A ∅ = nil). rewrite <- (elements_nil_eset ∅). reflexivity. 
    rewrite H0. reflexivity.

    symmetry.
    rewrite size_spec.
    eapply length_unique_eq.
    assumption.
    eapply elements_unique.
    apply elements_fromList_in.
  Qed.
  
  Lemma fromList_drop {A : Type} (p q : list A) (x : A) : 
    unique (p ++ x :: q) ->
    fromList (p ++ q) = fromList (p ++ x :: q) \ {{x}}.
  Proof.
    intros.
    induction p; simpl in *.

    erewrite <- union_minus. reflexivity.
    rewrite in_fromList.
    apply (fst X).

    specialize (IHp (snd X)).
    rewrite IHp.
    repeat (cset_tac; firstorder).
  Qed.

  Lemma fromList_drop' {A : Type} (q : list A) (x : A) :
    unique (x :: q) -> fromList q = fromList (x :: q) \ {{x}}.
  Proof.
    intros.
    assert (fromList (nil ++ q) = fromList (nil ++ x :: q) \ {{x}}).
    apply fromList_drop.
    assumption.
    assumption.
  Qed.

  Lemma size_add_disjoint {A : Type} `{EqDec A eq} (s : cset A) (x : A) :
    ~ (x ∈ s) -> size ({{x}} ∪ s) = S (size s).
  Proof.
    intros.
    assert (In x (elements ({{x}} ∪ s))).
    apply elements_spec. repeat (cset_tac; firstorder).
    apply in_split in H1.
    inversion H1 as [p [q Hpq]]; clear H1.
    specialize (elements_unique ({{x}} ∪ s)); intros H1.
    rewrite Hpq in H1.
    apply fromList_eq in Hpq. rewrite fromList_elements in Hpq.
    assert (s = fromList (p ++ q)).
    apply fromList_drop in H1.
    rewrite H1. rewrite <- Hpq. rewrite <- union_minus. reflexivity. assumption.
    rewrite Hpq. rewrite H2.
    repeat rewrite fromList_size.
    repeat rewrite app_length. simpl. omega.
    eapply unique_remove. apply H1. assumption.
  Qed.


  Lemma cset_ind {A : Type} `{EqDec A eq} (P : cset A -> Prop) :
    P ∅ ->
    (forall s x, P s -> ~ x ∈ s -> P ({{x}} ∪ s)) ->
    forall s, P s.
  Proof.
    intros.

    assert (exists l, (forall x, In x l <-> x ∈ s) /\ exists t : unique l, True).
    exists (elements s). split. intros; rewrite elements_spec. reflexivity.
    exists (elements_unique s). constructor.

    inversion H2 as [l Hl]; clear H2.
    generalize dependent s.
    induction l; intros.
    simpl in Hl.
    assert (s = ∅) by (cset_tac; firstorder).
    subst s; assumption.

    inversion Hl; clear Hl.
    inversion H3 as [Hu Hgigo]; clear Hgigo H3.
    assert (s = fromList (a :: l)).
    apply set_extensionality; intros; apply eq_bool_prop_intro.
    rewrite <- H2. rewrite <- in_fromList. reflexivity.

    specialize (fromList_drop' Hu); intros.
    rewrite <- H3 in H4.
    assert (a ∈ s) by (simpl in H2; cset_tac; firstorder).
    assert (s = {{a}} ∪ (fromList l)).
    rewrite H4.
    cset_tac.
    destruct_prop (x = a). firstorder. right. firstorder.
    invc H3. invc H6. assumption. contradiction. tauto.
    
    rewrite H6.
    apply H1; try assumption.
    apply IHl.
    split.
    symmetry. apply in_fromList.
    exists (snd Hu).
    constructor.

    rewrite H4.
    cset_tac; firstorder.
  Qed.

  Lemma minus_dist_union X (s t u:cset X)
    : (s ∪ t) \ u = (s \ u) ∪ (t \ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_dist_intersection X (s t u:cset X)
    : (s ∩ t) \ u = (s \ u) ∩ (t \ u).
  Proof.
    cset_tac; firstorder.
  Qed.


  Lemma incl_not_member X (s t:cset X) x
    : s ⊆ t -> ~x ∈ t -> ~x ∈ s.
  Proof.
    cset_tac; firstorder.
  Qed.
  
  Lemma incl_meet_empty X (s t u:cset X)
    : s ⊆ t -> u ∩ t = empty -> u ∩ s = empty.
  Proof.
    cset_tac; firstorder. change (Is_true false). rewrite <- (empty_spec x).
    rewrite <- H0. rewrite intersection_spec. cset_tac; firstorder.
  Qed.

  Lemma union_incl_split X (s t u : cset X)
    : s ⊆ u -> t ⊆ u -> s ∪ t ⊆ u.
  Proof.
    intros. hnf in *; intros. cset_tac; firstorder.
  Qed.
    
End BSet.

                  


(* 
*** Local Variables: ***
*** coq-load-path: ("../infra") ***
*** End: ***
*)
