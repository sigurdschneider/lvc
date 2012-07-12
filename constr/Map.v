Require Import List Setoid.
Require Import EqDec DecidableTactics Var Util AutoIndTac.

Lemma Not_Is_true_eq_false : forall x:bool, ~Is_true x -> x = false.
Proof.
  intros. destruct x; eauto. destruct H; eapply I.
Qed.

Lemma eq_false_not_Is_true : forall x:bool, x = false -> ~Is_true x.
Proof.
  intros. destruct x; eauto. congruence.
Qed.


Require Import CSet.

Export BSet.

Set Implicit Arguments.

Lemma neq_symmetry (X : Type) (x y : X) :
  x <> y -> y <> x.
Proof.
  intros A B. destruct A. symmetry in B. assumption.
Qed.



Module Type Map.
  (* An abstract type for environments. *)
  Parameter map    : forall X:Type, X -> Type.
  Parameter empty  : forall X (def:X), map def.
  Parameter lookup : forall X (def:X), map def -> var -> X.
  Parameter update : forall X (def:X), map def -> var -> X -> map def.
  Parameter domain : forall X (def:X), map def -> cset var.
  Parameter lookup_set : forall X (def:X) (m:map def) (s:cset var), cset X.

  Implicit Arguments empty  [X].
  Implicit Arguments lookup [X def].
  Implicit Arguments update [X def].
  Implicit Arguments domain [X def].

  (* Behaviour of empty. *)
  Parameter empty_spec :
    forall (X : Type) (def:X) (k : var),
      lookup (empty def) k = def.
  (* The following two lemmas are enough to abstract the behaviour
     of lookup and update. *)
  Parameter lookup_eq :
    forall (X : Type) (def:X) (m : map def) (k : var) (x : X),
      lookup (update m k x) k = x.
  Parameter lookup_neq :
    forall (X : Type) (def: X) (m : map def) (k l : var) (x : X),
      k <> l -> lookup (update m k x) l = lookup m l.

  Parameter domain_spec :
    forall (X : Type) (def:X) (m : map def) (x : var),
      x ∈ (domain m) <-> lookup m x <> def.

  Parameter lookup_set_spec : forall X (def:X) (m:map def) s y,
    y ∈ lookup_set m s <-> exists x, x ∈ s /\ lookup m x = y.

  Parameter map_extensionality :
    forall (X : Type) (def:X) (f g : map def), 
      (forall x, lookup f x = lookup g x)
      -> f = g.
End Map.

Module Type MapNotation (Import M : Map).
  (** * Notation for maps  *)
  Notation "∅" := empty : map_scope.
  (** There can be no coercion from map X to var -> X because of the
      "uniform inheritance condition". *)
  Notation "m [ x ]" :=
    (lookup m x) (left associativity, at level 69) : map_scope.
  Notation "m [ x <- s ]" :=
    (update m x s) (left associativity, at level 69) : map_scope.
  Delimit Scope map_scope with map.
End MapNotation.

Module Type Map' := Map <+ MapNotation.

Module Type MapEquality (Import M : Map').
  (*Open Scope map_scope.*)

  (** * Extensional equality of maps. *)
  Definition eq_map X (def : X) (f g : map def) : Prop :=
    forall x, lookup f x = lookup g x.
  Implicit Arguments eq_map [X def].
  Hint Unfold eq_map.

  Notation "s === t" :=  (eq_map s t) (at level 70, no associativity).
  Notation "s =/= t" := (~eq_map s t) (at level 70, no associativity).

  (** Proof that this is indeed an equivalence relation. *)
  Lemma eq_map_reflexivity X (def: X) (f : map def) :
    f === f.
  Proof. auto. Qed.

  Lemma eq_map_symmetry X (def: X) (f g : map def) :
    f === g -> g === f.
  Proof. auto. Qed.

  Lemma eq_map_transitivity X (def: X) (f g h : map def) :
    f === g -> g === h -> f === h.
  Proof. unfold eq_map. intros. rewrite H. rewrite <- H0. auto. Qed.

  (** Register it as a setoid and proof that update/lookup are proper morphisms. *)
  Add Parametric Relation (X : Type) (def : X) : (map def) (@eq_map X def)
    reflexivity  proved by (@eq_map_reflexivity  X def)
    symmetry     proved by (@eq_map_symmetry     X def)
    transitivity proved by (@eq_map_transitivity X def)
    as map_setoid.

  Add Parametric Morphism (X : Type) (def:X) : (@lookup X def) with
    signature (@eq_map X def) ==> (@eq var) ==> (@eq X) as lookup_morphism.
  Proof.
    intros x y A v. rewrite A. reflexivity.
  Qed.

  Add Parametric Morphism (X : Type) (def : X) : (@update X def) with
    signature (@eq_map X def) ==> (@eq var) ==> (@eq X) ==> (@eq_map X def)
    as update_morphism.
  Proof.
    intros x y B w t z. destruct_prop (w = z).
      intros. subst. repeat rewrite lookup_eq. reflexivity.
      intros. repeat rewrite lookup_neq; auto.
  Qed.
End MapEquality.

Module Type MapEqualityDec (Import M : Map') (Import E : MapEquality M).
  Parameter eq_map_dec : forall (X : Type) (def: X),
    forall (f g:@map X def), {f === g} + {f =/= g}.
End MapEqualityDec.

Module Type MapTactics (Import M : Map') (Import E : MapEquality M).
  Open Scope map_scope.

  Ltac lookup_neq_tac :=
    match goal with
      | [H : not (eq ?k ?l) |- context[@lookup _ _ (@update _ _ ?m ?k _) ?l]]
        => rewrite (@lookup_neq _ _ _ _ _ _ H)
      | [H : not (eq ?l ?k)  |- context[@lookup _ _ (@update _ _ ?m ?k _) ?l]]
        => rewrite (@lookup_neq _ _ _ _ _ _ (neq_symmetry H))
    end.

  Ltac lookup_neq_tac' :=
    match goal with
      | [H : not (eq ?k ?l), I : context[@lookup _ _ (@update _ _ ?m ?k _) ?l] |- _ ]
        => rewrite (@lookup_neq _ _ _ _ _ _ H) in I
      | [H : not (eq ?l ?k), I : context[@lookup _ _ (@update _ _ ?m ?k _) ?l] |- _ ]
        => rewrite (@lookup_neq _ _ _ _ _ _ (neq_symmetry H)) in I
    end.


  Tactic Notation "simplify" "lookup'" :=
    repeat (subst || rewrite lookup_eq in * || lookup_neq_tac || lookup_neq_tac').

  Lemma update_commute X (def: X) (m : map def) (k l : var) (x y : X) :
    k <> l -> (m[k <- x][l <- y]) === (m[l <- y][k <- x]).
  Proof.
    intros ? j. destruct_prop (j = k); destruct_prop (j = l); simplify lookup'; auto.
    exfalso; auto. 
  Qed.

  Lemma update_shadow X (def: X) (m : map def) (k : var) (x y : X) :
    (m[k <- x][k <- y]) === (m[k <- y]).
  Proof.
    intro l. destruct_prop (k = l); simplify lookup'; auto.
  Qed.

  Lemma update_repeat X (def: X) (m : map def) (k l : var) (x : X) :
    m[l] = x -> m[k <- x][l] = x.
  Proof.
    intros. destruct_prop (l = k); simplify lookup'; auto.
  Qed.

  Lemma update_repeat' X (def: X) (m : map def) (k l : var) :
    m[k <- m[k]][l] = m[l].
  Proof.
    intros. destruct_prop (l = k); simplify lookup'; auto.
  Qed.

  Tactic Notation "simplify" "lookup" :=
    repeat (subst || rewrite lookup_eq in * || rewrite update_shadow in * ||
      rewrite update_repeat' in * 
      || lookup_neq_tac || lookup_neq_tac').

End MapTactics.

Module Type MapMorphism (Import M : Map') (Import E : MapEquality M).
  Open Scope map_scope.

  Parameter map_lift :
    forall X Y Z (defX : X) (defY : Y) (defZ : Z),
    (X -> Y -> Z) -> map defX -> map defY -> map defZ.

  Implicit Arguments map_lift [X Y Z defX defY defZ].

  Parameter map_lift_spec :
    forall X Y Z (defX : X) (defY : Y) (defZ : Z)
      (f : X -> Y -> Z) (m : map defX) (m' : map defY) (k : var),
      (@map_lift _ _ _ _ _ defZ f m m')[k] = f (m[k]) (m'[k]).

  Add Parametric Morphism (X Y Z : Type)
    (defX : X) (defY : Y) (defZ : Z) :
    (@map_lift X Y Z defX defY defZ) with
    signature (@eq (X -> Y -> Z)) ==>
              (@eq_map X defX) ==> (@eq_map Y defY) ==> (@eq_map Z defZ)
    as map_lift_morphism.
  Proof.
    intros f m m' H n n' H' x. repeat rewrite map_lift_spec.
    rewrite H. rewrite H'. reflexivity.
  Qed.
End MapMorphism.

Module Type MapDomain :=
  Map' <+ MapEquality <+ MapTactics <+ MapMorphism.

Global Instance inst_defaulted_bool : Defaulted bool :=
  { default_el := false }.

(*
Module Type StackMap (Import M : Map') (Import E : MapEquality M).
  Open Scope map_scope.

  Parameter push : forall X def, map def -> X -> map X.
  Parameter pop  : forall X def, map def -> map X.

  Parameter push_spec1 : forall X `(Defaulted X) (m : map X) (x : X),
    (push m x)[0] = x.

  Parameter push_spec2 : forall X `(Defaulted X) (m : map X) (x : X),
    forall k, (push m x)[S k] = m[k].

  Parameter pop_spec : forall X `(Defaulted X) (m : map X),
    forall k, (pop m)[k] = m[S k].

  Fixpoint raise X `{Defaulted X} (k : nat) (m : map X) : map X :=
    match k with
      |   O => m
      | S k => push (raise k m) default_el
    end.

  Fixpoint lower X (k : nat) (m : map X) : map X :=
    match k with
      |   O => m
      | S k => pop (lower k m)
    end.

  Lemma raise_spec1 : forall X `(Defaulted X) (m : map X) k,
    forall l, l < k -> (raise k m)[l] = default_el.
  Proof with simpl; eauto using push_spec1.
    intros X H m k l; revert m k H; induction l; simpl; intros.
    inv H0... destruct k. inv H0... simpl. rewrite push_spec2.
    apply IHl. omega.
  Qed.

  Lemma raise_spec2 : forall X `(Defaulted X) (m : map X) k,
    forall l, (raise k m)[k + l] = m[l].
  Proof.
    induction k; simpl; intros. auto. rewrite push_spec2. apply IHk.
  Qed.

  Lemma lower_spec : forall X `(Defaulted X) (m : map X) k,
    forall l, (lower k m)[l] = m[k + l].
  Proof.
    induction k; simpl; intros. auto. rewrite pop_spec. rewrite IHk.
    f_equal. omega.
  Qed.

  Lemma push_injective X `(Defaulted X) (m m' : map X) (x y : X) :
    push m x === push m' y -> m === m' /\ x = y.
  Proof.
    split. intros k. rewrite <- (push_spec2 H m x). rewrite <- (push_spec2 H m' y).
    apply H0. specialize (H0 0). rewrite (push_spec1 H m) in H0.
    rewrite (push_spec1 H m') in H0. assumption.
  Qed.

  Lemma pop_surjective X `(Defaulted X) (m : map X) :
    exists m', pop m' === m.
  Proof.
    exists (push m default_el). intros x. rewrite pop_spec.
    rewrite push_spec2. reflexivity.
  Qed.
End StackMap.
*)
(* Needs an instance of Defaulted. *)
(*
Module ListMap <: Map.
  Definition map    (X : Type) := list X.
  Definition empty  (X : Type) := @nil X.

  Definition lookup (X : Type) (def : Defaulted X) (m : map X) (k : var) :=
    nth k m default_el.

  Fixpoint update (X : Type) (m : map X) (k : var) (x : X) : map X :=
    match m, k with
      | nil,       0 => x :: nil
      | nil,     S k => default_el :: update nil k x
      | _ :: xr,   0 => x :: xr
      | y :: xr, S k => y :: update xr k x
    end.

  Lemma empty_spec (X : Type) (k : var) :
    lookup (empty X) k = None.
  Proof.
    destruct k; simpl; auto.
  Qed.

  Lemma lookup_eq (X : Type) (m : map X) (k : var) (x : X) :
    lookup (update m k x) k = Some x.
  Proof.
    revert m x; induction k; destruct m; simpl; intros;
    unfold lookup in *; simpl in *; auto.
  Qed.

  Lemma lookup_neq (X : Type) (m : map X) (k l : var) (x : X) :
    k <> l -> lookup (update m k x) l = lookup m l.
  Proof.
    revert m l x; induction k; destruct m; unfold lookup in *; simpl in *; intros.
    destruct l. destruct H; auto. destruct l; auto. destruct l; auto.
    destruct H; auto. destruct l; auto. specialize (IHk nil). simpl in IHk.
    specialize (IHk l). destruct l; auto. destruct l; auto.
  Qed.
End ListMap.
*)

Module Type MapAgreement (Import M' : Map') (Import ME : MapEquality M') (Import MT : MapTactics M' ME).
  Open Scope map_scope.

  Definition subMap X (def:X) (m m':map def) :=
    forall x, m[x] <> def -> m[x] = m'[x].
  
  Definition agree_on X (def:X) (D:cset var) (E E':map def) := 
    forall x, x ∈ D -> E[x] = (E'[x]).

  Lemma agree_on_refl X (def:X) L (E:map def) 
    : agree_on L E E.
  Proof.
    firstorder.
  Qed.

  Lemma agree_on_sym X (def:X) L (E E':map def) 
    : agree_on L E E' -> agree_on L E' E.
  Proof.
    firstorder.
  Qed.

  Lemma subMap_agree X (def:X) (m m':map def)
    : subMap m m' <-> agree_on (domain m) m m'.
  Proof.
    split; intros; hnf; intros; eauto.
    eapply H; eauto. eapply domain_spec; eauto.
    rewrite H; eauto. eapply domain_spec; eauto.
  Qed.

  Definition subMap_exc X (def:X) L (m m':map def) :=
    agree_on (domain m \ L) m m'.

  Lemma agree_on_update X (def:X) L E E' x (v:X)
    : @agree_on _ def L E E' -> agree_on L (E[x<-v]) (E'[x<-v]).
  Proof.
    intros. hnf; intros.
    destruct_prop (x=x0); subst; simplify lookup; eauto.
  Qed.

  Lemma agree_on_incl X (def:X) (bv lv:cset var) (E E':map def)
    : agree_on lv E E'
    -> incl bv lv
    -> agree_on bv E E'.
  Proof.
    firstorder.
  Qed.

  Lemma agree_on_update_same X (def:X) (lv:cset var) (E E':map def) x v
    : agree_on (lv\{{x}}) E E'
    -> agree_on lv (E [x <- v]) (E' [x <- v]).
  Proof.
    intros A. hnf; intros.
    destruct_prop (x=x0); subst; simplify lookup;
      eauto using in_in_minus, neq_not_in_single.
  Qed.

  Lemma agree_on_update_dead X (def:X) (lv:cset var) (E E':map def) x v
    : ~x ∈ lv
    -> agree_on lv E E'
    -> agree_on lv (E [x <- v]) E'.
  Proof.
    intros A B.
    hnf; intros. 
    assert (x<>x0) by congruence. 
    simplify lookup; eauto.
  Qed.

  Lemma lookup_set_helper : forall X (def:X) (m:map def) s x,
    x ∈ s -> lookup m x ∈ lookup_set m s.
  Proof.
    intros. eapply lookup_set_spec. eexists x; eauto.
  Qed.

  Lemma lookup_set_incl X (def:X) s t (m:map def)
    : incl s t -> incl (lookup_set m s) (lookup_set m t).
  Proof.
    intros; hnf; intros.
    eapply lookup_set_spec in H0. destruct H0 as [x' [A B]].
    eapply lookup_set_spec. eexists x'; eauto.
  Qed.

  Lemma agree_on_domain X `(EqDec X eq) (def:X) (m m':map def)
    : agree_on (domain m ∪ domain m') m m'
    -> m = m'.
  Proof.
    intros. eapply map_extensionality; intros.
    destruct_prop (x ∈ domain m ∪ domain m'); intros; eauto.
    eapply not_in_union_decomp in n; destruct n.
    erewrite domain_spec in H1. eapply dneg_eq in H1; eauto.
    erewrite domain_spec in H2. eapply dneg_eq in H2; eauto.
    congruence.
  Qed.

  Lemma lookup_set_agree X (def:X) s (m m':map def)
    : agree_on s m m' -> lookup_set m s = lookup_set m' s.
  Proof.
    intros.
    eapply set_extensionality; intros.
    eapply bool_extensionality; intros.
    eapply lookup_set_spec; eauto.
    eapply lookup_set_spec in H0. edestruct H0 as [x' [A B]].
    eexists x'. split; eauto. rewrite <- H; eauto. 
    eapply lookup_set_spec; eauto.
    eapply lookup_set_spec in H0. edestruct H0 as [x' [A B]].
    eexists x'. split; eauto. rewrite H; eauto. 
  Qed.

End MapAgreement.

Module Type MapInjectivity (Import M' : Map') (Import ME : MapEquality M') (Import MT : MapTactics M' ME) (Import MA : MapAgreement M' ME MT).
  Open Scope map_scope.


  Definition injective_on X (def:X) L (ra:map def) :=
    forall x y, x ∈ L -> y ∈ L -> ra[x] = ra[y] -> x = y.

  Lemma injective_on_incl X (def:X) lv bv (ra:map def) (SM:incl bv lv)
    : injective_on lv ra -> injective_on bv ra.
  Proof.
    firstorder.
  Qed.

  Lemma injective_on_dead X (def:X) lv (ra:map def) x v
    : injective_on (lv\{{x}}) ra
    -> injective_on (lv\{{x}}) (ra[x<-v]).
  Proof.
    intros; hnf; intros. 
    destruct_prop (y=x); subst;
      destruct_prop (x0=x); subst; simplify lookup; eauto. 
    cset_tac; firstorder.
    exfalso; cset_tac; firstorder.
  Qed.

  Lemma injective_on_fresh X (def:X) lv (ra:map def) x xr 
    : injective_on (lv\{{x}}) ra
      -> ~xr ∈ lookup_set ra (lv\{{x}})
      -> injective_on ({{x}} ∪ lv) (ra[x <- xr]).
  Proof.
    intros. hnf; intros.
    destruct_prop (x0=x); subst;
      destruct_prop (x=y); subst; simplify lookup; eauto.
    exfalso. eapply H0. eapply lookup_set_spec. eexists y. 
    split; cset_tac; firstorder.
    exfalso. eapply H0. eapply lookup_set_spec. eexists x0. 
    split; cset_tac; firstorder.
    eapply H; try cset_tac; firstorder.
  Qed.

  Lemma injective_on_forget X (def:X) s (f:map def) y
    :injective_on s f
    -> injective_on (s\{{y}}) f.
  Proof.
    intros. hnf; intros.
    assert (y<>y0). intro; subst. cset_tac; firstorder.
    assert (x<>y). intro; subst. cset_tac; firstorder.
    eapply H. cset_tac; firstorder. cset_tac; firstorder.
    simplify lookup; eauto.
  Qed.

  Fixpoint update_with_list X (def:X) XL YL (m:map def) :=
    match XL, YL with
      | x::XL, y::YL => update_with_list XL YL m[x <- y]
      | _, _ => m
    end.

  Inductive inj_mapping X (LV:cset X) : list var -> list X -> Type :=
  | im_nil : inj_mapping LV nil nil
  | im_cons x y XL YL : inj_mapping LV XL YL 
    -> fresh x XL -> fresh y YL -> (~ y ∈ LV) 
    -> inj_mapping LV (x::XL) (y::YL).

  Lemma inj_mapping_length X (LV:cset X) Y Z
    : inj_mapping LV Y Z -> length Y = length Z.
  Proof.
    intros. general induction X0; simpl; eauto.
  Qed.

  Lemma inj_mapping_incl X (L L':cset X) Y Z
    : incl L' L -> inj_mapping L Y Z -> inj_mapping L' Y Z.
  Proof.
    intros. general induction X0; constructor; eauto.
  Qed.

  Lemma ra_insert_allocs_correct' X (def:X) (m:map def) lv XL YL x
    : In x XL
    -> inj_mapping (lookup_set m lv) XL YL
    -> In (update_with_list XL YL m [x]) YL.
  Proof.
    intros.
    general induction X0; simpl in *; intros.
    inv H.
    destruct_prop (x=x0); subst; simplify lookup; eauto.
    right. eapply IHX0; eauto. destruct H; subst; eauto; congruence.
  Qed.

  Lemma ra_insert_allocs_no_param X (def:X) XL YL (m:map def) x
    : ~x ∈ fromList XL
    -> update_with_list XL YL m [x] = m[x].
  Proof.
    general induction XL; simpl; intros; eauto.
    destruct YL; eauto.
    assert (x<>a). intro; subst; cset_tac. eapply H. simpl. cset_tac; firstorder.
    simplify lookup. eapply IHXL; cset_tac; eauto. 
    eapply H. simpl. eapply union_right; eauto.
  Qed.

  Lemma ra_insert_allocs_cases X (def:X) XL YL (m:map def) bv y 
    : inj_mapping (lookup_set m bv) XL YL
    -> y ∈ lookup_set (update_with_list XL YL m) ((fromList XL ∪ bv))
    -> y ∈ lookup_set m bv \/ y ∈ fromList YL.
  Proof.
    intros.
    eapply lookup_set_spec in H; eauto.
    destruct H as [x [A B]].
    destruct_prop (x ∈ fromList XL).
    right. eapply in_fromList. rewrite <- B. eapply ra_insert_allocs_correct'; eauto.
    eapply in_fromList. assumption. 
    left. rewrite <- B. rewrite ra_insert_allocs_no_param; eauto. 
    eapply lookup_set_spec; eauto.
    destruct (union_cases _ _ _ A); firstorder.
  Qed.


  Lemma injective_on_mapping X (def:X) (lv:cset var) (m:map def) (Z:list var) YL
    (rk:injective_on lv m)
    (IM:inj_mapping (lookup_set m lv) Z YL)
    : injective_on (fromList Z ∪ lv) (update_with_list Z YL m).
  Proof.
    general induction IM; simpl.
    rewrite empty_neutral_union; eauto.
    rewrite union_assoc.
    eapply injective_on_fresh.
    eapply injective_on_forget; eauto.
    intro. eapply lookup_set_incl in H; eauto using incl_minus_single.
    edestruct ra_insert_allocs_cases; eauto. eapply f0; eapply in_fromList; eauto.
  Qed.

End MapInjectivity.

Module BMap <: Map.
  (* An abstract type for environments. *)
  Parameter map    : forall X:Type, X -> Type.
  Parameter empty  : forall X (def:X), map def.
  Parameter lookup : forall X (def:X), map def -> var -> X.
  Parameter update : forall X (def:X), map def -> var -> X -> map def.
  Parameter domain : forall X (def:X), map def -> cset var.

  Implicit Arguments empty  [X].
  Implicit Arguments lookup [X def].
  Implicit Arguments update [X def].
  Implicit Arguments domain [X def].

  (* Behaviour of empty. *)
  Parameter empty_spec :
    forall (X : Type) (def:X) (k : var),
      lookup (empty def) k = def.
  (* The following two lemmas are enough to abstract the behaviour
     of lookup and update. *)
  Parameter lookup_eq :
    forall (X : Type) (def:X) (m : map def) (k : var) (x : X),
      lookup (update m k x) k = x.
  Parameter lookup_neq :
    forall (X : Type) (def: X) (m : map def) (k l : var) (x : X),
      k <> l -> lookup (update m k x) l = lookup m l.

  Parameter domain_spec :
    forall (X : Type) (def:X) (m : map def) (x : var),
      x ∈ (domain m) <-> lookup m x <> def.

  Parameter map_extensionality :
    forall (X : Type) (def:X) (f g : map def), 
      (forall x, lookup f x = lookup g x)
      -> f = g.

  Lemma domain_empty X (def:X)
    : domain (empty def) = ∅.
  Proof.
    eapply set_extensionality.
    intros. rewrite BSet.empty_spec. 
    eapply Not_Is_true_eq_false. rewrite domain_spec.
    rewrite empty_spec. congruence.
  Qed.

  Parameter lookup_set : forall X (def:X) (m:map def) (s:cset var), cset X.
  Parameter lookup_set_spec : forall X (def:X) (m:map def) s y,
    y ∈ lookup_set m s <-> exists x, x ∈ s /\ lookup m x = y.




  Include MapNotation.
  Include MapEquality.
  Include MapTactics.
  Include MapAgreement.
  Include MapInjectivity.

  Fixpoint lookup_list X (def:X) (m:map def) (L:list var) : list X :=
    match L with
      | nil => nil
      | x::L => m[x]::lookup_list m L
    end.


  Lemma update_id X (def:X)(m:map def) x
    : m [x <- m[x]] = m.
  Proof.
    eapply map_extensionality.
    intros.
    destruct_prop (x0=x); subst; simplify lookup; eauto. 
  Qed.

  Fixpoint idOn (def:var) (D:list var) :=
    match D with 
      | nil => empty def
      | x::D => idOn def D [x<-x]
    end.

(*  Lemma idOn_domain (def:var) (D:list var) 
    : domain (idOn def D) = D.
  Proof.
  Admitted. 
    

  Lemma idOn_id def D x
    : In x D -> idOn def D [x] = x.
  Proof.
    induction D; simpl; intros. isabsurd. 
    destruct_prop (a=x); subst; simplify lookup; firstorder.
  Qed.    

  Parameter non_element 
    : forall X (def:X) (m:map def), var.
  
  Parameter non_element_spec
    : forall X (def:X) (m:map def), ~In (non_element m) (domain m).

  Lemma non_domain_lookup X (def:X) (m:map def) x
    : ~ x ∈ (domain m) <-> m [x] = def.
  Proof.
  Admitted.
*)

End BMap.


