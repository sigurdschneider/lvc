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

  Lemma in_add_case X `(EqDec X eq) s (x y:X)
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
    : incl (s\t) s.
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


  Lemma incl_minus_single X s (x:X)
    :  incl (s \ {{x}}) s.
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

  Lemma union_idem X (s t:cset X)
    : s ∪ s ∪ t = s ∪ t.
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

End BSet.


(* 
*** Local Variables: ***
*** coq-load-path: ("../infra") ***
*** End: ***
*)
