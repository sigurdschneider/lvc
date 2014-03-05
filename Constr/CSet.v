Require Export Setoid Coq.Classes.Morphisms.  
Require Import EqDec DecidableTactics Util Get.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import SetDecide.

Global Instance inst_eq_dec_ordered_type X `(OrderedType X)
  : @EqDec X _ OT_Equivalence.
destruct H. hnf; intros. 
case_eq(_cmp x y); intros; 
pose proof (_compare_spec x y ); rewrite H in H0. left.
inv H0. eapply H1.
right. inv H0. destruct OT_StrictOrder. eauto.
right. inv H0. destruct OT_StrictOrder. symmetry. eauto.
Defined.

Infix "∪" := (union) (at level 60) : set_scope.
Infix "∩" := (inter) (at level 60) : set_scope.
Notation "x '∉' s" := (~In x s) (at level 70, no associativity) : set_scope.
Notation "x '∈' s" := (In x s) (at level 70, no associativity) : set_scope.
Notation "∅" := empty : set_scope.
Notation "s ≅ t" := (Equal s t) (at level 70, no associativity) : set_scope. 
Notation "s '⊆' t" := (Subset s t) (at level 70, no associativity) : set_scope.
Notation "{{ x , .. , y }}" := (add x .. (add y empty) .. ) : set_scope. 


Instance inst_computable_In X `(OrderedType X) x s
  : Computable(x ∈ s).
constructor. case_eq (mem x s); intros.
left. eapply mem_iff; eauto.
right. eapply not_mem_iff; eauto.
Defined.

Instance Subset_computable {X} `{OrderedType X} {s t:set X}
  : Computable (Subset s t).
Proof.
  constructor. case_eq (subset s t); intro A.
  + eapply subset_iff in A. intuition.
  + right; intro B. rewrite subset_iff in B. congruence.
Defined.

Instance Equal_computable X `{OrderedType X} (s t:set X) : Computable (s [=] t).
constructor. case_eq (equal s t); intros.
left. eapply equal_iff in H0. eauto.
right. intro. eapply equal_iff in H1. congruence.
Defined.

Extraction Inline inst_computable_In Subset_computable Equal_computable.

Lemma In_add_empty {X} `{OrderedType X} x y
  : In x (add y empty) <-> x === y.
Proof. 
  rewrite add_iff. split; firstorder. 
  exfalso. eapply empty_iff; eauto.
Qed.

Lemma not_In_add_empty {X} `{OrderedType X} x y
  : ~In x (add y empty) <-> x =/= y.
Proof. 
  rewrite add_iff. split; firstorder. 
  intro; firstorder. eapply empty_iff; eauto.
Qed.

Lemma not_in_empty {X} `{OrderedType X} (x:X)
: x ∉ ∅.
Proof.
  hnf; intros. eapply empty_iff in H0; eauto.
Qed.

  Ltac cset_assumption :=
    match goal with
      | [ H : context [ In _ (union ?s ?t) ] |- _ ] =>
        setoid_rewrite (union_iff s t _) in H
      | [ H : context [ In _ (diff ?s ?t) ] |- _ ] =>
        setoid_rewrite (diff_iff s t) in H
      | [ H : context [ In _ (inter ?s ?t) ] |- _ ] =>
        setoid_rewrite (inter_iff s t _) in H
(*      | [ H : context [ member ?x (minus ?s ?t) ] |- _ ] =>
        rewrite (minus_spec _ s t x) in H
      | [ H : context [ member ?x empty ] |- _ ] => 
        rewrite (empty_spec _ x) in H *)
(*      | [ H : context [ member ?x empty ] |- _ ] => 
        rewrite (not_In_add_empty _ x) in H *)
      | [ H : In ?x ?s, H' : ~In ?y ?s |- _ ] =>
        match goal with
          | [ H'' : x =/= y |- _ ] => fail 1
          | [ H'' : x === y |- _ ] => fail 1
          | [ H'' : ~x === y |- _ ] => fail 1
          | [ H'' : ~y === x |- _ ] => fail 1
          | [ H'' : y =/= x |- _ ] => fail 1
          | [ H'' : y === x |- _ ] => fail 1
          | [ |- _ ] => destruct_prop(x === y)
        end
      | [ H : context [ In ?x empty ] |- _ ] => 
        rewrite (empty_iff x) in H
      | [ H : context [ In ?x (add ?y empty) ] |- _ ] => 
        rewrite (In_add_empty x y) in H
(*      | [ H : context [ Is_true (@member _ _ ?x (@single _ ?y)) ] |- _ ] => 
        rewrite (@single_spec _ _ x y) in H *)
(*      | [ H : @eq_cset _ _ ?s ?t, H' : not (Is_true (@member _ _ ?x ?s)) 
        |- not (Is_true (@member _ _ ?x ?t)) ] => rewrite <- H; eauto
      | [ H : @eq_cset _ _ ?t ?s, H' : not (Is_true (@member _ _ ?x ?s)) 
        |- not (Is_true (@member _ _ ?x ?t)) ] => rewrite H; eauto
      | [ |- not ?Q ] => intro
      | [ |- ?P = ?Q ] => match type of P with
                            | bool => eapply bool_extensionality; intros
(*                          | cset _ => eapply set_extensionality; intros *)
                          end
*)
    (* goal *)
      | [ |- context [ In ?x (union ?s ?t) ]] =>
        rewrite (union_iff s t x)
(*      | [ |- @eq_cset _ _ _ _ ] => unfold eq_cset; intro
      | [ H : @eq_cset _ _ ?s ?t, H' : Is_true (member ?x ?s) 
        |- Is_true (member ?x ?t) ] => rewrite <- H; eauto
      | [ H : @eq_cset _ _ ?t ?s, H' : Is_true (member ?x ?s) 
        |- Is_true (member ?x ?t) ] => rewrite H; eauto
      | [ |- context [ @member _ _ ?x (@meet _ _ ?s ?t) ]] =>
        rewrite (@intersection_spec _ _ s t x)
      | [ |- context [ @member _ _ ?x empty ]] => 
        rewrite (@empty_spec _ _ x)
      | [ |- context [ Is_true (@member _ _ ?x (@single _ ?y)) ]] => 
        rewrite (@single_spec _ _ x y) *)
      | [ H : ?x === ?y, H' : In ?x ?s, H'' : ~In ?y ?s |- _ ] => 
        now (exfalso; rewrite H in H'; eauto)
      | [ H : ?x === ?y, H' : In ?y ?s |- In ?x ?s ] => 
        now (rewrite H; eauto)
      | [ H : ?y === ?x, H' : In ?y ?s |- In ?x ?s ] => 
        now (rewrite <- H; eauto)
      | [ H : ?x === ?y, H' : ~In ?y ?s |- ~In ?x ?s ] => 
        now (rewrite H; eauto)
      | [ H : ?y === ?x, H' : ~In ?y ?s |- ~In ?x ?s ] => 
        now (rewrite <- H; eauto)
      | [ |- context [ In ?x (diff ?s ?t) ] ] =>
        rewrite (diff_iff s t)
      | [ |- context [ In ?x (inter ?s ?t) ] ] =>
        rewrite (inter_iff s t)
      | [ |- ?s ≅ ?t] => intro
      | [ H : ?x =/= ?y |- ~In ?x (add ?y empty) ] => 
        now (rewrite not_In_add_empty; eauto)
      | [ |- context [~In ?x (add ?y empty)] ] => 
        rewrite (not_In_add_empty x y)
      | [ |- context [In ?x (add ?y empty)] ] => 
        rewrite (In_add_empty x y)
      | [ |- context [In ?x empty] ] => 
        rewrite (empty_iff x)
      | [ |- context [ ~In ?x empty ] ] => 
        rewrite (empty_iff x)
      | [ |- _ ⊆ _ ] => hnf; intros
      | [ |- context [ In ?x (diff ?s ?t) ]] =>
        intros
      | [ |- context [ In ?x (singleton ?y) ]] =>
        rewrite (singleton_iff y x)
      | [ H : context [ In ?x (singleton ?y) ] |- _ ] =>
        rewrite (singleton_iff y x) in H
      | [ |- context [ In ?y (add ?x ?s) ]] =>
        rewrite (add_iff s x y )
      | [ H : context [ In ?y (add ?x ?s) ] |- _ ] =>
        rewrite (add_iff s x y ) in H
      | [ H : ?A [=] ∅ |- _ ] =>
        assert (A ⊆ ∅); 
          [ let H := fresh "H" in
            edestruct (double_inclusion A ∅) as [[H ?] ?]; eauto| clear H]
      | [ H : ?s ≅ ?t |- _ ] => unfold Equal in H 
      | [ H : ?A ⊆ ∅ |- _ ] => 
        assert (forall a, a ∈ A -> False);[ 
            let a := fresh "a" in let C := fresh "H" in 
                                  intros a C;
                                    eapply (@not_in_empty _ _ a (H _ C))| clear H]
    end.

  Ltac cset_tac_step := 
    intros; (try subst); decompose records; destr; cset_assumption ||
      bool_to_prop || bool_to_prop in *.

  Ltac cset_tac :=
      repeat (cset_tac_step). 

Section theorems.
  Variable X : Type.
  Context `{OrderedType X}.
  
  Lemma single_spec_neq (x y:X)
    : x ∈ {{ y }} -> x === y.
  Proof.
    cset_tac; firstorder. 
  Qed.

  Lemma in_add_case s (x y:X)
    : y ∈ {{x}} ∪ s -> x===y \/ (x =/= y /\ y ∈ s).
  Proof.
    destruct_prop (x===y); cset_tac; firstorder.
  Qed.

  Lemma neq_not_in_single (x y:X)
    :  x =/= y -> ~x ∈ {{y}}.
  Proof.
    cset_tac; firstorder.
  Qed. 

  Lemma minus_empty (s:set X)
    : s \ ∅ ≅ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_in_in s t (x:X)
    : x ∈ (s \ t) -> x ∈ s /\ ~x ∈ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma in_in_minus s t (x:X)
    : x ∈ s -> ~x ∈ t -> x ∈ (s \ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma in_in_neq s (x y:X)
    : x ∈ s -> ~y ∈ s -> x =/= y.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_comm (s t:set X)
    : s ∪ t ≅ t ∪ s .
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_inane s (x:X)
    : x ∉ s
    -> s ≅ (s\{{x}}).
  Proof.
    repeat (cset_tac; firstorder).
  Qed.

 

  Lemma minus_inane_set (s t:set X)
    : s ∩ t ≅ ∅ -> (s \ t) ≅ s.
  Proof. 
    intros.   cset_tac.
    
        
 cset_tac. specialize (H0 a). cset_tac; firstorder.
  Qed.

  Lemma minus_union_set (s t:set X)
    : s ∩ t ≅ ∅ -> ((s ∪ t) \ t) ≅ s.
  Proof. 
    cset_tac. specialize (H0 a). cset_tac; firstorder.
  Qed.


  Lemma in_minus_neq s (x y:X)
    : x =/= y -> x ∈ s
    -> x ∈ (s\{{y}}).
  Proof.
    repeat (cset_tac; firstorder).
  Qed.

  Lemma add_inane s (x:X) 
    : x ∈ s
    -> s ≅ ({{x}} ∪ s).
  Proof.
    repeat (cset_tac; firstorder).
  Qed.

  Lemma in_single_union s (y:X)
    : y ∈ {{y}} ∪ s.
  Proof.
    repeat (cset_tac; subst; firstorder).
  Qed.

  Lemma minus_union (s t u:set X)
    : (s \ t \ u) ≅ s \ (t ∪ u).
  Proof.
    repeat (cset_tac; firstorder).
  Qed.

  Lemma incl_empty (s:set X)
    : ∅ ⊆ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_incl (s t:set X)
    : (s\t) ⊆ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma empty_neutral_union (s:set X)
    : ∅ ∪ s ≅ s.
  Proof.
    cset_tac; firstorder.
  Qed.


  Lemma incl_add s (x:X)
    :  s ⊆ ({{x}} ∪ s).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_union (s t:set X)
    :  s ⊆ (t ∪ s).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_add' (s:set X) x
    :  s ⊆ {x; s}.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma in_add' (s:set X) x
    :  x ∈ {x; s}.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_minus (s t : set X)
    :  (s \ t) ⊆ s.
  Proof.
    cset_tac; firstorder.
  Qed.


  Lemma union_assoc (s t u : set X)
    : s ∪ t ∪ u ≅ s ∪ (t ∪ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_set_decomp (s t:set X)
    : s ⊆ t -> t ≅ s ∪ (t \ s).
  Proof.
    cset_tac; firstorder.
    destruct_prop (a ∈ s); firstorder.
  Qed.

  Lemma incl_union_minus (s t:set X)
    : s ⊆ (t ∪ (s \ t)).
  Proof.
    cset_tac.
    destruct_prop (a ∈ t); firstorder.
  Qed.

  Lemma union_minus_incl (s t:set X)
    : ((t ∪ s) \ t) ⊆ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_minus_lr (s s' t t':set X)
    : s ⊆ s' -> t ⊆ t' -> s \ t' ⊆ s' \ t.
  Proof.
    intros; hnf in *; hnf; cset_tac; firstorder.
  Qed.


  Lemma union_idem (s:set X)
    : s ∪ s ≅ s.
  Proof.
    hnf; cset_tac; firstorder.
  Qed.

  
  Lemma union_minus s (x:X)
    : x ∉ s -> s ≅ ({{x}} ∪ s) \ {{x}}.
  Proof.
    repeat (cset_tac; firstorder). 
  Qed.

  Lemma minus_in s t (x:X)
    : x ∉ s -> x ∉ t -> x ∉ (s ∪ t).
  Proof.
    repeat (cset_tac; firstorder). 
  Qed.

  Lemma union_cases s t (x:X)
    : x ∈ (s ∪ t) -> x ∈ s \/ x ∈ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma not_in_union_comp  (s t : set X) x :
    ~x ∈ s /\ ~x ∈ t -> ~x ∈ (s ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma not_in_union_decomp s t (x:X)
    : x ∉ (s ∪ t) -> x ∉ s /\ x ∉ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_left s t (x:X)
    : x ∈ s -> x ∈ (s ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_right s t (x:X)
    : x ∈ t -> x ∈ (s ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma set_fact_1 s t (x:X)
    : x ∉ t
    -> {{x}} ∪ (s \ ({{x}} ∪ t)) ≅ {{x}} ∪ s \ t.
  Proof.
    intros. cset_tac; firstorder. cset_tac. 
    destruct_prop (a===x); firstorder. 
  Qed.

  Lemma set_fact_2 s t (x:X)
    : (s \ ({{x}} ∪ t)) \ {{x}} ≅ s \ ({{x}} ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.


  Lemma incl_union_absorption (s t:set X)
    : s ⊆ t -> s ∪ t ≅ t.
  Proof.
    intros; hnf in *; hnf; cset_tac; firstorder.
  Qed.

  Lemma incl_union_lr (s s' t t':set X)
    : s ⊆ s' -> t ⊆ t' -> s ∪ t ⊆ s' ∪ t'.
  Proof.
    intros; hnf in *; hnf; cset_tac; firstorder.
  Qed.


  Lemma incl_not_in (x:X) s t
    : x ∉ s -> s\{{x}} ⊆ t -> s ⊆ t.
  Proof.
    cset_tac. specialize (H1 a). cset_tac; firstorder.
  Qed.

  Lemma incl_left (s t:set X)
    : s ⊆ (s ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma in_meet (s t:set X) (x:X)
    : x ∈ s -> x ∈ t -> x ∈ s ∩ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_in (s t:set X) (x:X)
    : x ∈ s ∩ t -> x ∈ s /\ x ∈ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_incl (s t u:set X) 
    : s ⊆ u -> s ∩ t ⊆ u.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_comm (s t:set X)
    : s ∩ t ≅ t ∩ s.
  Proof.
    cset_tac. firstorder.
  Qed.

  Lemma incl_meet (s t:set X)
    : s ⊆ t -> s ≅ s ∩ t.
  Proof.
    repeat (cset_tac; subst; firstorder).
  Qed.


  Lemma minus_meet (s t u:set X)
    : (s \ t) ∩ u ≅ s ∩ u \ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma set_incl (s t: set X)
    : s ⊆ t -> t ⊆ s -> t ≅ s.
  Proof.
    intros; hnf in *; cset_tac; firstorder.
  Qed.


  Lemma elements_nil_eset (s : set X) :
    s ≅ ∅ <-> elements s = nil.
  Proof.
    split; intros.
    remember (elements s). destruct l; eauto.
    assert (x ∈ s). eapply elements_iff.
    rewrite <- Heql. firstorder. 
    exfalso. rewrite H0 in H1. eapply not_in_empty; eauto.

    specialize (elements_iff s); intros.
    rewrite H0 in H1. 
    cset_tac. specialize (H1 a). firstorder. inv H1.
  Qed.

  Lemma union_meet_distr_r (s t u : set X) :
    (s ∪ t) ∩ u ≅ (s ∩ u) ∪ (t ∩ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_is_empty (s t : set X) :
    s ∪ t ≅ ∅ -> (s ≅ ∅ /\ t ≅ ∅).
  Proof.
    cset_tac; specialize (H0 a); cset_tac; firstorder.
  Qed.

  Lemma smaller_meet_empty (s t u : set X) :
    (s ∪ t) ∩ u ≅ ∅ -> t ∩ u ≅ ∅.
  Proof.
    intros. cset_tac; specialize (H0 a); cset_tac; firstorder.
  Qed.

  Lemma empty_intersection_in_one_not_other (s t : set X) x :
    s ∩ t ≅ ∅ -> x ∈ s -> ~ x ∈ t.
  Proof.
    cset_tac. specialize (H0 x); cset_tac; firstorder.
  Qed.

  Lemma meet_assoc (s t u : set X)
    : s ∩ t ∩ u ≅ s ∩ (t ∩ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_meet_lr (s s' t t':set X)
    : s ⊆ s' -> t ⊆ t' -> s ∩ t ⊆ s' ∩ t'.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_in_union (s t : set X) 
    : s ∩ t ⊆ s ∪ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_dist_union (s t u:set X)
    : (s ∪ t) \ u ≅ (s \ u) ∪ (t \ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_dist_intersection (s t u:set X)
    : (s ∩ t) \ u ≅ (s \ u) ∩ (t \ u).
  Proof.
    cset_tac; firstorder.
  Qed.


  Lemma incl_not_member (s t:set X) x
    : s ⊆ t -> ~x ∈ t -> ~x ∈ s.
  Proof.
    cset_tac; firstorder.
  Qed.
  
  Lemma incl_meet_empty (s t u:set X)
    : s ⊆ t -> u ∩ t ≅ empty -> u ∩ s ≅ empty.
  Proof.
    cset_tac. specialize (H1 a); cset_tac; firstorder. 
  Qed.

  Lemma union_incl_split (s t u : set X)
    : s ⊆ u -> t ⊆ u -> s ∪ t ⊆ u.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_incl_special (c c' d : set X)
    : c ⊆ c'
    -> c ∪ (c' \ (c \ d)) ≅ c'.
  Proof.
    cset_tac; firstorder.
    destruct_prop(a ∈ c). firstorder.
    set (b:=c\d). assert (a ∉ b). subst b. cset_tac; firstorder.
    cset_tac; firstorder.
  Qed.

  Lemma union_minus_remove (a b : set X)
        : (a ∪ b) \ a ≅ b \ a.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_incl_meet_special (c c' d : set X)
    : d ⊆ c
    -> c ⊆ c'
    -> c ∩ (c' \ (c \ d)) ≅ d.
  Proof.
    cset_tac; firstorder.
    destruct_prop(a ∈ d); firstorder.
  Qed.

  Lemma minus_incl_meet_special2 (c c' d : set X)
    : c ⊆ d
    -> c ⊆ c'
    -> c ∩ (c' \ (c \ d)) ≅ c.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_minus_id (s t: set X)
    : s ⊆ t
    -> s ≅ t \ (t \ s).
  Proof.
    cset_tac; firstorder. 
    destruct_prop (a ∈ s); firstorder.
  Qed.
  
  Lemma meet_minus (s t : set X)
    : s ∩ (t \ s) ≅ ∅.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_in_left (s t : set X)
    : s ∩ t ⊆ s.
  Proof.
    hnf; intros. cset_tac; firstorder.
  Qed.

  Lemma not_in_meet_empty (D:set X) x
    : ~ x ∈ D
    -> D ∩ {{x}} ≅ ∅.
  Proof.
    cset_tac; firstorder. cset_tac.
  Qed.

  Lemma incl_eq (s t:set X) 
    : s ⊆ t -> t ⊆ s -> t ≅ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma eq_incl (s t:set X) 
    : t ≅ s -> s ⊆ t /\ t ⊆ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  End theorems.

  Section moretheorems.
   
  Require Import List. 
  Variable X : Type.
  Context `{OrderedType X}.

  Hypothesis equiv_is_eq : _eq = eq.


End moretheorems.

Definition addf {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y) :=
  (fun x t => add (f x) t).

Add Parametric Morphism {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
  `{Proper _ (_eq ==> _eq) f}
  : (addf f)
  with signature 
    _eq ==> Equal ==> Equal as addf_morphism.
Proof.
  intros. unfold addf. rewrite H2. rewrite H3. reflexivity.
Qed.

Add Parametric Morphism {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
  : (addf f)
  with signature 
    eq ==> Equal ==> Equal as addf_morphism2.
Proof.
  intros. unfold addf. rewrite H1. reflexivity.
Qed.

Lemma addf_transpose {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
 : transpose Equal (addf f).
Proof.
  hnf; intros.
  unfold addf. hnf. intros. rewrite add_add. split; eauto.
Qed.


Lemma minus_union_both X `{OrderedType X} (s t: set X) x
  : x ∉ s -> s \ t [=] (s ∪ {{x}}) \ (t ∪ {{x}}).
Proof.
  cset_tac; firstorder. intro; firstorder. eapply H0. rewrite <- H3. eauto.
Qed.

Lemma list_eq_eq {X} {L L':list X}
  : list_eq eq L L' <-> L = L'.
Proof.
  split; intros. eapply list_eq_ind; intros; subst; f_equal; eauto.
  general induction L; econstructor; eauto.
Qed.

Lemma minus_idem X `{OrderedType X} (s t:set X)
: s \ t [=] (s \ t) \ t.
Proof.
  cset_tac; intuition.
Qed.

Lemma meet_incl_eq {X} `{OrderedType X} (s s' t t':set X)
: t' ⊆ t -> s ∩ t [=] s' ∩ t -> s ∩ t' [=] s' ∩ t'.
Proof.
  intros; cset_tac; intuition; firstorder.
Qed.

Lemma InA_in {X} `{OrderedType X} x L
 : InA _eq x L <-> x ∈ of_list L.
Proof.
  split; intros. 
  general induction L. inv H0.
  simpl. inv H0. rewrite H2. eapply add_iff; intuition.
  eapply add_iff; intuition.
  general induction L. inv H0.
  simpl in *. eapply add_iff in H0. destruct H0.
  rewrite H0; firstorder.
  constructor 2. eapply IHL; eauto.
Qed.


Lemma minus_minus_eq {X} `{OrderedType X} (s t : set X) 
  : s [=] s \ (t \ s).
Proof.
  cset_tac; firstorder.
Qed.


Lemma union_incl_left {X} `{OrderedType X} (s t u: set X)
: s ⊆ t -> s ⊆ t ∪ u.
Proof.
  cset_tac; intuition.
Qed.

Definition list_union {X} `{OrderedType X} (L:list (set X)) := 
  fold_left union L ∅.

Lemma list_union_incl {X} `{OrderedType X} (L:list (set X)) (s s':set X) 
  : (forall n t, get L n t -> t ⊆ s')
   -> s ⊆ s'
   -> fold_left union L s ⊆ s'.
Proof.
  intros. general induction L; simpl. eauto. 
  assert (a ⊆ s'). eapply H0; eauto using get.
  eapply IHL; eauto. intros. rewrite H0; eauto using get.
  cset_tac; intuition.
  cset_tac; intuition.
Qed.

Lemma list_union_start {X} `{OrderedType X} (s: set X) L t
: s ⊆ t
  -> s ⊆ fold_left union L t.
Proof.
  intros. general induction L; simpl; eauto.
  eapply IHL; eauto. cset_tac; intuition.
Qed.

Lemma incl_list_union {X} `{OrderedType X} (s: set X) L n t u
: get L n t
  -> s ⊆ t
  -> s ⊆ fold_left union L u.
Proof.
  intros. general induction L.
  + inv H0.
  + unfold list_union. simpl. inv H0; eauto.
    - eapply list_union_start; cset_tac; intuition.
Qed.

Lemma of_list_app X `{OrderedType X} (A B: list X)
  : of_list (A ++ B) [=] of_list A ∪ of_list B.
Proof.
  split; intros.
  - rewrite of_list_1 in H0. cset_tac. eapply InA_app in H0.
    repeat rewrite of_list_1. intuition. destruct H; eauto.
  - rewrite of_list_1. eapply InA_app_iff. destruct H; eauto.
    cset_tac. repeat rewrite of_list_1 in H0. intuition.
Qed.



(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lyn")) ***
*** End: ***
*)



