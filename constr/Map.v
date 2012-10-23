Require Import List Setoid.
Require Import EqDec DecidableTactics Util AutoIndTac.

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
  Parameter map        : forall (W X:Type), Type.
  Parameter empty      : forall {W} {X} (def:X), map W X.
  Parameter lookup     : forall {W} `{EqDec W eq} {X}, map W X -> W -> X.
  Parameter default    : forall {W} {X}, map W X -> X.
  Parameter update     : forall {W} `{EqDec W eq} {X}, map W X -> W -> X -> map W X.
  Parameter domain     : forall {W} `{EqDec W eq} {X}, map W X -> cset W.
  Parameter lookup_set : forall {W} `{EqDec W eq} {X} (m:map W X) (s:cset W), cset X.

  (* Behaviour of empty. *)
  Parameter empty_spec :
    forall W `{EqDec W eq} X (def:X) (k : W),
      lookup (empty def) k = def.

  Parameter default_spec :
    forall (W X : Type) (def:X),
      default (@empty W X def) = def.

  (* The following two lemmas are enough to abstract the behaviour
     of lookup and update. *)
  Parameter lookup_eq :
    forall (W : Type) `{EqDec W eq} X (m : map W X) (k : W) (x : X),
      lookup (update m k x) k = x.

  Parameter lookup_neq :
    forall (W : Type) `{EqDec W eq} X (m : map W X) (k l : W) (x : X),
      k <> l -> lookup (update m k x) l = lookup m l.

  Parameter domain_spec :
    forall (W : Type) `{EqDec W eq} X (m : map W X) (x : W),
      ~x ∈ (domain m) <-> lookup m x = default m.

  Parameter lookup_set_spec : forall W `{EqDec W eq} X (m:map W X) s y,
    y ∈ lookup_set m s <-> exists x, x ∈ s /\ lookup m x = y.

  Parameter map_extensionality :
    forall (W : Type) `{EqDec W eq} X (f g : map W X), 
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
  Definition eq_map {W} `{EqDec W eq} {X} (f g : map W X) : Prop :=
    forall x, lookup f x = lookup g x.

  Hint Unfold eq_map.

  Notation "s === t" :=  (eq_map s t) (at level 70, no associativity).
  Notation "s =/= t" := (~eq_map s t) (at level 70, no associativity).

  (** Proof that this is indeed an equivalence relation. *)
  Lemma eq_map_reflexivity W `{EqDec W eq} X (f : map W X) :
    f === f.
  Proof. auto. Qed.

  Lemma eq_map_symmetry W `{EqDec W eq} X (f g : map W X) :
    f === g -> g === f.
  Proof. auto. Qed.

  Lemma eq_map_transitivity W `{EqDec W eq} X (f g h : map W X) :
    f === g -> g === h -> f === h.
  Proof. unfold eq_map. intros. rewrite H0. rewrite <- H1. auto. Qed.

  (** Register it as a setoid and proof that update/lookup are proper morphisms. *)
  Add Parametric Relation (W X : Type) `{EqDec W eq} : (map W X) (@eq_map W _ _ X)
    reflexivity  proved by (@eq_map_reflexivity W _ _ X)
    symmetry     proved by (@eq_map_symmetry    W _ _ X)
    transitivity proved by (@eq_map_transitivity W _ _ X)
    as map_setoid.

  Add Parametric Morphism (W X : Type) `{EqDec W eq} : (@lookup W _ _ X) with
    signature (@eq_map W _ _ X) ==> (@eq W) ==> (@eq X) as lookup_morphism.
  Proof.
    intros x y A v. rewrite A. reflexivity.
  Qed.

  Add Parametric Morphism (W X : Type) `{EqDec W eq} : (@update W _ _ X ) with
    signature (@eq_map W _ _ X) ==> (@eq W) ==> (@eq X) ==> (@eq_map W _ _ X)
    as update_morphism.
  Proof.
    intros x y B w t z. destruct_prop (w = z).
      intros. subst. repeat rewrite lookup_eq. reflexivity.
      intros. repeat rewrite lookup_neq; auto.
  Qed.
End MapEquality.

Module Type MapEqualityDec (Import M : Map') (Import E : MapEquality M).
  Parameter eq_map_dec : forall (W : Type) `{EqDec W eq} X (def: X),
    forall (f g:@map W X), {f === g} + {f =/= g}.
End MapEqualityDec.

Module Type MapTactics (Import M : Map') (Import E : MapEquality M).
  Open Scope map_scope.

  Ltac lookup_neq_tac :=
    match goal with
      | [H : not (eq ?k ?l) |- context[@lookup _ _ _ _ (@update _ _ _ _ _ ?k _) ?l]]
        => rewrite (@lookup_neq _ _ _ _ _ _ _ _ H)
      | [H : not (eq ?l ?k)  |- context[@lookup _ _ _ _ (@update _ _ _ _ _ ?k _) ?l]]
        => rewrite (@lookup_neq _ _ _ _ _ _ _ _ (neq_symmetry H))
    end.

  Ltac lookup_neq_tac' :=
    match goal with
      | [H : not (eq ?k ?l), I : context[@lookup _ _ _ _ (@update _ _ _ _ ?m ?k _) ?l] |- _ ]
        => rewrite (@lookup_neq _ _ _ _ _ _ _ _ H) in I
      | [H : not (eq ?l ?k), I : context[@lookup _ _ _ _ (@update _ _ _ _ ?m ?k _) ?l] |- _ ]
        => rewrite (@lookup_neq _ _ _ _ _ _ _ _ (neq_symmetry H)) in I
    end.


  Tactic Notation "simplify" "lookup'" :=
    repeat (subst || rewrite lookup_eq in * || lookup_neq_tac || lookup_neq_tac').

  Lemma update_commute W `{EqDec W eq} X (m : map W X) (k l : W) (x y : X) :
    k <> l -> (m[k <- x][l <- y]) === (m[l <- y][k <- x]).
  Proof.
    intros ? j. destruct_prop (j = k); destruct_prop (j = l); simplify lookup'; auto.
    exfalso; auto. 
  Qed.

  Lemma update_shadow W `{EqDec W eq} X (m : map W X) (k : W) (x y : X) :
    (m[k <- x][k <- y]) === (m[k <- y]).
  Proof.
    intro l. destruct_prop (k = l); simplify lookup'; auto.
  Qed.

  Lemma update_repeat W `{EqDec W eq} X (m : map W X) (k l : W) (x : X) :
    m[l] = x -> m[k <- x][l] = x.
  Proof.
    intros. destruct_prop (l = k); simplify lookup'; auto.
  Qed.

  Lemma update_repeat' W `{EqDec W eq} X (m : map W X) (k l : W) :
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
    forall {W} `{EqDec W eq} {X} {Y} {Z},
    (X -> Y -> Z) -> map W X -> map W Y -> map W Z.

  Parameter map_lift_spec :
    forall W `{EqDec W eq} X Y Z (f : X -> Y -> Z) (m : map W X) (m' : map W Y) (k : W),
      (@map_lift _ _ _ _ _ _ f m m')[k] = f (m[k]) (m'[k]).

  Add Parametric Morphism (X Y Z : Type)
    (defX : X) (defY : Y) (defZ : Z) :
    (@map_lift _ _ _ X Y Z) with
    signature (@eq (X -> Y -> Z)) ==>
              (@eq_map _ _ _ X) ==> (@eq_map _ _ _ Y) ==> (@eq_map _ _ _ Z)
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

(*  Definition subMap X (def:X) (m m':map def) :=
    forall x, m[x] <> def -> m[x] = m'[x]. *)
  
  Definition agree_on W `{EqDec W eq} X (D:cset W) (E E':map W X) := 
    forall x, x ∈ D -> E[x] = (E'[x]).

  Lemma agree_on_refl W `{EqDec W eq} X L (E:map W X) 
    : agree_on L E E.
  Proof.
    firstorder.
  Qed.

  Lemma agree_on_sym W `{EqDec W eq} X L (E E':map W X) 
    : agree_on L E E' -> agree_on L E' E.
  Proof.
    firstorder.
  Qed.

  Lemma agree_on_trans W `{EqDec W eq} X L (E E' E'':map W X) 
    : agree_on L E E' -> agree_on L E' E'' -> agree_on L E E''.
  Proof.
    intros; hnf; intros. rewrite H0; eauto. 
  Qed.

(*  Lemma subMap_agree X (def:X) (m m':map def)
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
*)

  Lemma agree_on_incl W `{EqDec W eq} X (bv lv:cset W) (E E':map W X)
    : agree_on lv E E'
    -> incl bv lv
    -> agree_on bv E E'.
  Proof.
    firstorder.
  Qed.

  Lemma agree_on_update_same W `{EqDec W eq} X (lv:cset W) (E E':map W X) x v
    : agree_on (lv\{{x}}) E E'
    -> agree_on lv (E [x <- v]) (E' [x <- v]).
  Proof.
    intros A. hnf; intros.
    destruct_prop (x=x0); subst; simplify lookup;
      eauto using in_in_minus, neq_not_in_single.
  Qed.

  Lemma agree_on_update_any_same W `{EqDec W eq} X (lv:cset W) (E E':map W X) x v
    : agree_on lv E E'
    -> agree_on (lv ∪ {{x}}) (E [x <- v]) (E' [x <- v]).
  Proof.
    intros A. hnf; intros.
    destruct_prop (x=x0); subst; simplify lookup;
      eauto using in_in_minus, neq_not_in_single.
    eapply union_cases in H0; destruct H0; eauto.
    eapply single_spec_neq in H0; congruence.
  Qed.

  Lemma agree_on_update_dead W `{EqDec W eq} X (lv:cset W) (E E':map W X) x v
    : ~x ∈ lv
    -> agree_on lv E E'
    -> agree_on lv (E [x <- v]) E'.
  Proof.
    intros A B.
    hnf; intros. 
    assert (x<>x0) by congruence. 
    simplify lookup; eauto.
  Qed.

  Lemma agree_on_update_dead_both W `{EqDec W eq} X (lv:cset W) (E E':map W X) x v v'
    : ~x ∈ lv
    -> agree_on lv E E'
    -> agree_on lv (E [x <- v]) (E'[x <- v']).
  Proof.
    intros A B. eauto using agree_on_trans, agree_on_update_dead, agree_on_sym.
  Qed.

  Lemma lookup_set_helper : forall W `{EqDec W eq} X (m:map W X) s x,
    x ∈ s -> lookup m x ∈ lookup_set m s.
  Proof.
    intros. eapply lookup_set_spec. eexists x; eauto.
  Qed.

  Lemma lookup_set_incl W `{EqDec W eq} X s t (m:map W X)
    : incl s t -> incl (lookup_set m s) (lookup_set m t).
  Proof.
    intros; hnf; intros.
    eapply lookup_set_spec in H1. destruct H1 as [x' [A B]].
    eapply lookup_set_spec. eexists x'; eauto.
  Qed.

  Lemma lookup_set_union W `{EqDec W eq} X s t (m:map W X)
    : lookup_set m (s ∪ t) = lookup_set m s ∪ lookup_set m t.
  Proof.
  Admitted.

  Lemma lookup_set_minus W `{EqDec W eq} X s t (m:map W X)
    : lookup_set m (s \ t) = lookup_set m s \ (lookup_set m t).
  Proof.
  Admitted.


  Lemma agree_on_domain W `{EqDec W eq} X `(EqDec X eq) (m m':map W X)
    : agree_on (domain m ∪ domain m') m m'
    -> default m = default m'
    -> m = m'.
  Proof.
    intros. eapply map_extensionality; intros.
    destruct_prop (x ∈ domain m ∪ domain m'); intros; eauto.
    eapply not_in_union_decomp in n; destruct n.
    eapply domain_spec in H3. eapply domain_spec in H4. simpl in *; congruence.
  Qed.

  Lemma lookup_set_agree W `{EqDec W eq} X s (m m':map W X)
    : agree_on s m m' -> lookup_set m s = lookup_set m' s.
  Proof.
    intros.
    eapply set_extensionality; intros.
    eapply bool_extensionality; intros.
    eapply lookup_set_spec; eauto.
    eapply lookup_set_spec in H1. edestruct H1 as [x' [A B]].
    eexists x'. split; eauto. rewrite <- H0; eauto. 
    eapply lookup_set_spec; eauto.
    eapply lookup_set_spec in H1. edestruct H1 as [x' [A B]].
    eexists x'. split; eauto. rewrite H0; eauto. 
  Qed.

End MapAgreement.

Module Type MapInjectivity (Import M' : Map') (Import ME : MapEquality M') (Import MT : MapTactics M' ME) (Import MA : MapAgreement M' ME MT).
  Open Scope map_scope.


  Definition injective_on W `{EqDec W eq} X L (ra:map W X) :=
    forall x y, x ∈ L -> y ∈ L -> ra[x] = ra[y] -> x = y.

  Lemma injective_on_incl W `{EqDec W eq} X lv bv (ra:map W X) (SM:incl bv lv)
    : injective_on lv ra -> injective_on bv ra.
  Proof.
    firstorder.
  Qed.

  Lemma injective_on_dead W `{EqDec W eq} X lv (ra:map W X) x v
    : injective_on (lv\{{x}}) ra
    -> injective_on (lv\{{x}}) (ra[x<-v]).
  Proof.
    intros; hnf; intros. 
    destruct_prop (y=x); subst;
      destruct_prop (x0=x); subst; simplify lookup; eauto. 
    cset_tac; firstorder.
    exfalso; cset_tac; firstorder.
  Qed.

  Lemma injective_on_fresh W `{EqDec W eq} X lv (ra:map W X) x xr 
    : injective_on (lv\{{x}}) ra
      -> ~xr ∈ lookup_set ra (lv\{{x}})
      -> injective_on ({{x}} ∪ lv) (ra[x <- xr]).
  Proof.
    intros. hnf; intros.
    destruct_prop (x0=x); subst;
      destruct_prop (x=y); subst; simplify lookup; eauto.
    exfalso. eapply H1. eapply lookup_set_spec. eexists y. 
    split; cset_tac; firstorder.
    exfalso. eapply H1. eapply lookup_set_spec. eexists x0. 
    split; cset_tac; firstorder.
    eapply H0; try cset_tac; firstorder.
  Qed.

  Lemma injective_on_forget W `{EqDec W eq} X s (f:map W X) y
    :injective_on s f
    -> injective_on (s\{{y}}) f.
  Proof.
    intros. hnf; intros.
    assert (y<>y0). intro; subst. cset_tac; firstorder.
    assert (x<>y). intro; subst. cset_tac; firstorder.
    eapply H0. cset_tac; firstorder. cset_tac; firstorder.
    simplify lookup; eauto.
  Qed.

  Fixpoint update_with_list W `{EqDec W eq} X XL YL (m:map W X) :=
    match XL, YL with
      | x::XL, y::YL => update_with_list XL YL m[x <- y]
      | _, _ => m
    end.

  Lemma update_with_list_agree W `{EqDec W eq} X lv (E E':map W X) XL YL
    : agree_on (lv\fromList XL) E E'
    -> length_eq XL YL
    -> agree_on lv (update_with_list XL YL E) (update_with_list XL YL E').
  Proof.
    general induction XL; simpl in * |- *. rewrite minus_empty in H0; eauto.
    inv X0. eapply agree_on_update_same. 
    eapply IHXL; eauto. rewrite minus_union; eauto.
  Qed.

  Lemma update_with_list_no_update W `{EqDec W eq} X (E:map W X) Y Z x
    : x ∉ fromList Z
    -> update_with_list Z Y E [x] = E [x].
  Proof.
    intros. general induction Z; simpl; destruct Y; eauto.
    destruct_prop (a=x); subst; simplify lookup.
    exfalso. eapply H0. simpl; cset_tac; firstorder.
    assert (~x ∈ fromList Z) by (simpl in H0; cset_tac; firstorder).
    eauto.
  Qed.

  Lemma update_with_list_agree_minus W `{EqDec W eq} X lv (E E':map W X) XL YL 
    : length_eq XL YL
    -> agree_on lv E' E 
    -> agree_on (lv\fromList XL) (update_with_list XL YL E') E.
  Proof.
    intros. general induction X0; simpl. rewrite minus_empty. eassumption.
    rewrite union_comm. rewrite <- minus_union. eapply agree_on_update_dead.
    cset_tac; firstorder.
    eauto using agree_on_incl, incl_minus.
  Qed.

  Lemma update_with_list_agree_self W `{EqDec W eq} X lv (E:map W X) XL YL
    : agree_on (lv\fromList XL) (update_with_list XL YL E) E.
  Proof.
    general induction XL; simpl. rewrite minus_empty. eapply agree_on_refl.
    destruct YL. apply agree_on_refl.
    rewrite union_comm. rewrite <- minus_union. eapply agree_on_update_dead.
    cset_tac; firstorder.
    eapply agree_on_incl. eapply IHXL; eauto.
    instantiate (1:=lv). eapply incl_minus.
  Qed.



  Inductive inj_mapping {W} {X} (LV:cset X) : list W -> list X -> Type :=
  | im_nil : inj_mapping LV nil nil
  | im_cons x y XL YL : inj_mapping LV XL YL 
    -> fresh x XL -> fresh y YL -> (~ y ∈ LV) 
    -> inj_mapping LV (x::XL) (y::YL).

  Lemma inj_mapping_length W X (LV:cset X) Y Z
    : @inj_mapping W X LV Y Z -> length Y = length Z.
  Proof.
    intros. general induction X0; simpl; eauto.
  Qed.

  Lemma inj_mapping_incl W X (L L':cset X) Y Z
    : incl L' L -> @inj_mapping W X L Y Z -> inj_mapping L' Y Z.
  Proof.
    intros. general induction X0; constructor; eauto.
  Qed.

  Lemma ra_insert_allocs_correct' W `{EqDec W eq} X (m:map W X) lv XL YL x
    : In x XL
    -> inj_mapping (lookup_set m lv) XL YL
    -> In (update_with_list XL YL m [x]) YL.
  Proof.
    intros.
    general induction X0; simpl in *; intros.
    inv H0.
    destruct_prop (x=x0); subst; simplify lookup; eauto.
    right. eapply IHX0; eauto. destruct H0; subst; eauto; congruence.
  Qed.

  Lemma ra_insert_allocs_no_param W `{EqDec W eq} X XL YL (m:map W X) x
    : ~x ∈ fromList XL
    -> update_with_list XL YL m [x] = m[x].
  Proof.
    general induction XL; simpl; intros; eauto.
    destruct YL; eauto.
    assert (x<>a). intro; subst; cset_tac. eapply H0. simpl. cset_tac; firstorder.
    simplify lookup. eapply IHXL; cset_tac; eauto. 
    eapply H0. simpl. eapply union_right; eauto.
  Qed.

  Lemma ra_insert_allocs_cases W `{EqDec W eq} X XL YL (m:map W X) bv y 
    : inj_mapping (lookup_set m bv) XL YL
    -> y ∈ lookup_set (update_with_list XL YL m) ((fromList XL ∪ bv))
    -> y ∈ lookup_set m bv \/ y ∈ fromList YL.
  Proof.
    intros.
    eapply lookup_set_spec in H0; eauto.
    destruct H0 as [x [A B]].
    destruct_prop (x ∈ fromList XL).
    right. eapply in_fromList. rewrite <- B. eapply ra_insert_allocs_correct'; eauto.
    eapply in_fromList. assumption. 
    left. rewrite <- B. rewrite ra_insert_allocs_no_param; eauto. 
    eapply lookup_set_spec; eauto.
    destruct (union_cases _ _ _ A); firstorder.
  Qed.


  Lemma injective_on_mapping W `{EqDec W eq} X (lv:cset W) (m:map W X) (Z:list W) YL
    (rk:injective_on lv m)
    (IM:inj_mapping (lookup_set m lv) Z YL)
    : injective_on (fromList Z ∪ lv) (update_with_list Z YL m).
  Proof.
    general induction IM; simpl.
    rewrite empty_neutral_union; eauto.
    rewrite union_assoc.
    eapply injective_on_fresh.
    eapply injective_on_forget; eauto.
    intro. eapply lookup_set_incl in H0; eauto using incl_minus.
    edestruct ra_insert_allocs_cases; eauto. eapply f0; eapply in_fromList; eauto.
  Qed.

End MapInjectivity.

Module BMap <: Map.

  Parameter map        : forall (W X:Type), Type.
  Parameter empty      : forall {W} {X} (def:X), map W X.
  Parameter lookup     : forall {W} `{EqDec W eq} {X}, map W X -> W -> X.
  Parameter default    : forall {W} {X}, map W X -> X.
  Parameter update     : forall {W} `{EqDec W eq} {X}, map W X -> W -> X -> map W X.
  Parameter domain     : forall {W} `{EqDec W eq} {X}, map W X -> cset W.
  Parameter lookup_set : forall {W} `{EqDec W eq} {X} (m:map W X) (s:cset W), cset X.

  (* Behaviour of empty. *)
  Parameter empty_spec :
    forall W `{EqDec W eq} X (def:X) (k : W),
      lookup (empty def) k = def.

  Parameter default_spec :
    forall (W X : Type) (def:X),
      default (@empty W X def) = def.

  (* The following two lemmas are enough to abstract the behaviour
     of lookup and update. *)
  Parameter lookup_eq :
    forall (W : Type) `{EqDec W eq} X (m : map W X) (k : W) (x : X),
      lookup (update m k x) k = x.

  Parameter lookup_neq :
    forall (W : Type) `{EqDec W eq} X (m : map W X) (k l : W) (x : X),
      k <> l -> lookup (update m k x) l = lookup m l.

  Parameter domain_spec :
    forall (W : Type) `{EqDec W eq} X (m : map W X) (x : W),
      ~x ∈ (domain m) <-> lookup m x = default m.

  Parameter lookup_set_spec : forall W `{EqDec W eq} X (m:map W X) s y,
    y ∈ lookup_set m s <-> exists x, x ∈ s /\ lookup m x = y.

  Parameter map_extensionality :
    forall (W : Type) `{EqDec W eq} X (f g : map W X), 
      (forall x, lookup f x = lookup g x)
      -> f = g.
(*
  Lemma domain_empty X (def:X)
    : domain (empty def) = ∅.
  Proof.
    eapply set_extensionality.
    intros. rewrite BSet.empty_spec. 
    eapply Not_Is_true_eq_false. intro.
    rewrite empty_spec in H. rewrite default_spec. reflexivity.
  Qed.
*)

  Include MapNotation.
  Include MapEquality.
  Include MapTactics.
  Include MapAgreement.
  Include MapInjectivity.

  Fixpoint lookup_list W `{EqDec W eq} X (m:map W X) (L:list W) : list X :=
    match L with
      | nil => nil
      | x::L => m[x]::lookup_list m L
    end.

  Lemma update_with_list_app X A A' (B B' : list X) E
    : length_eq A B 
    -> update_with_list (A++A') (B++B') E = update_with_list A B (update_with_list A' B' E).
  Proof.
    intros. general induction X0; simpl; eauto.
    rewrite IHX0; eauto.
  Qed.
  
  Lemma lookup_list_app W `{EqDec W eq} X A A' (E:map W X)
    : lookup_list E (A ++ A') = lookup_list E A ++ lookup_list E A'.
  Proof.
    general induction A; simpl; eauto.
    rewrite IHA; eauto.
  Qed.


  Lemma lookup_list_length W `{EqDec W eq} X (m:map W X) (L:list W) 
    : length (lookup_list m L) = length L.
  Proof.
    induction L; simpl; eauto.
  Qed.

  Lemma lookup_list_agree W `{EqDec W eq} X (m m':map W X) (L:list W)
    : agree_on (fromList L) m m'
    -> lookup_list m L = lookup_list m' L.
  Proof.
    general induction L; simpl in * |- *; eauto.
    rewrite H0. f_equal; eauto using agree_on_incl, incl_union.
    cset_tac; firstorder.
  Qed.

  Lemma fromList_lookup_list W `{EqDec W eq} X (m:map W X) L
    : fromList (lookup_list m L) = lookup_set m (fromList L).
  Proof.
    general induction L; simpl. 
    eapply set_extensionality; intros. eapply bool_extensionality; intros.
    cset_tac; firstorder.
    eapply lookup_set_spec in H0. decompose records; cset_tac; firstorder.
    rewrite IHL. eapply set_extensionality; intros.
    eapply bool_extensionality; intros.
    eapply lookup_set_spec. eapply union_cases in H0; destruct H0.
    eexists a; split; eauto. cset_tac; firstorder. cset_tac; firstorder.
    eapply lookup_set_spec in H0. firstorder.
    eexists x0; firstorder. eapply union_right; eauto.
    eapply lookup_set_spec in H0. firstorder.
    edestruct union_cases; eauto. eapply single_spec_neq in H2; subst.
    cset_tac; firstorder.
    eapply union_right. eapply lookup_set_spec. firstorder.
  Qed.


  Lemma update_id W `{EqDec W eq} X (m:map W X) x
    : m [x <- m[x]] = m.
  Proof.
    eapply map_extensionality.
    intros.
    destruct_prop (x0=x); subst; simplify lookup; eauto. 
  Qed.

  Lemma update_with_list_lookup_list W `{EqDec W eq} X (E:map W X) Z
    : update_with_list Z (lookup_list E Z) E = E.
  Proof.
    general induction Z; simpl; eauto.
    rewrite IHZ; eauto using update_id.
  Qed.


  Fixpoint idOn W `{EqDec W eq} (def:W) (D:list W) : map W W:=
    match D with 
      | nil => empty def
      | x::D => idOn def D [x<-x]
    end.

  Fixpoint update_lists W `{EqDec W eq} X (m:map W X) (Z:list W) (ZT:list X) := 
    match Z, ZT with 
      | x::Z, t::ZT => (update_lists m Z ZT)[x<-t]
      | _, _ => m
    end.
  
  Lemma update_lists_no_param W `{EqDec W eq} X (m:map W X) Z ZT x
    : x ∉ fromList Z
    -> update_lists m Z ZT [x] = m[x].
  Proof.
    intros. general induction Z; destruct ZT; simpl; eauto. 
    destruct_prop (a=x); subst; simplify lookup.
    exfalso; eapply H0. simpl; cset_tac; firstorder.
    simpl in H0. assert (~x ∈ fromList Z) by (cset_tac; firstorder).
    eauto.
  Qed.

  Lemma update_lists_lookup_lists W `{EqDec W eq} X (m:map W X) Z
    : update_lists m Z (lookup_list m Z) = m.
  Proof.
    general induction Z; simpl; eauto.
    rewrite IHZ, update_id; eauto.
  Qed.  

  Fixpoint update_list W `{EqDec W eq} X (m:map W X) (f:W -> X) (L:list W) := 
    match L with
      | nil => m
      | x::L => update_list m f L [x <- f x]
    end.

  Lemma update_list_agree_self W `{EqDec W eq} X lv (E:map W X) L f
    : agree_on (lv\fromList L) (update_list E f L) E.
  Proof.
    general induction L; simpl. rewrite minus_empty. eapply agree_on_refl.
    rewrite union_comm. rewrite <- minus_union. eapply agree_on_update_dead.
    cset_tac; firstorder.
    eapply agree_on_incl. eapply IHL; eauto.
    instantiate (1:=lv). eapply incl_minus.
  Qed.

  Lemma update_list_no_upd W `{EqDec W eq} X (m:map W X) f L x
    : x ∉ fromList L
    -> update_list m f L [x] = m [x].
  Proof.
    intros. general induction L; simpl; eauto.
    destruct_prop (a=x); subst; simplify lookup.
    exfalso. eapply H0. simpl; cset_tac; firstorder.
    assert (~x ∈ fromList L) by (simpl in H0; cset_tac; firstorder).
    eauto.
  Qed.

  Lemma update_list_upd W `{EqDec W eq} X (m:map W X) f L x
    : x ∈ fromList L
    -> update_list m f L [x] = f x.
  Proof.
    intros. general induction L; simpl; eauto.
    simpl in *; cset_tac; firstorder.
    destruct_prop (a=x); subst; simplify lookup; eauto.
    assert (x ∈ fromList L) by (simpl in H0; cset_tac; firstorder).
    eauto.
  Qed.

  Definition comp W `{EqDec W eq} Y `{EqDec Y eq} X (rho:map W Y) (m:map Y X) 
    : map W X :=
    update_list (empty (m[default rho])) (fun x => m [rho [x]]) (elements (domain rho)).

  Notation "m '∘' m'" := (comp m m') (at level 40, left associativity) : map_scope.

  Lemma comp_lookup W `{EqDec W eq} Y `{EqDec Y eq} X (rho:map W Y) (m:map Y X) x
    : comp rho m [x] = m [rho [x]].
  Proof.
    unfold comp. 
    destruct_prop (x ∈ fromList (elements (domain rho))).
    rewrite update_list_upd; eauto.
    rewrite update_list_no_upd. rewrite empty_spec. 
    rewrite in_fromList in n. rewrite <- elements_spec in n. 
    eapply domain_spec in n. congruence. eauto.
  Qed.

  Lemma comp_update W `{EqDec W eq} Y `{EqDec Y eq} X (rho:map W Y) (m:map Y X) x y z
    : comp (rho[x<-y]) (m[y<-z]) = comp rho m [x <- z].
  Proof.
    eapply map_extensionality; intros.
    rewrite comp_lookup.
    destruct_prop (x0 = x); subst; simplify lookup; eauto.
    rewrite comp_lookup.
    destruct_prop (y = rho [x0]); subst; simplify lookup; eauto.
    admit.
  Qed.

Parameter agree_set : forall W `{EqDec W eq} X (lv:cset W) (m m':map W X), cset W.

Parameter agree_set_spec
  : forall W `{EqDec W eq} X (lv:cset W) (m m':map W X) x,
    x ∈ agree_set lv m m' <-> x ∈ lv /\ m[x] = m'[x].



Lemma agree_set_agree_on 
  : forall W `{EqDec W eq} X Y (lv:cset W) (D D':map W X) (E E':map W Y),
    agree_on lv D D' -> agree_on (agree_set lv D D') E E' 
    -> agree_on lv E E'.
Proof.
  intros. hnf; intros.
  eapply H1. eapply agree_set_spec; eauto.
Qed.

Lemma agree_on_agree_set W `{EqDec W eq} X (lv:cset W) (D D' D'':map W X)
  : agree_on lv D D' -> agree_set lv D D'' ⊆ agree_set lv D' D''.
Proof.
  intros. hnf; intros. rewrite agree_set_spec in *. 
  rewrite <- H0; firstorder.
Qed.


Lemma agree_set_incl 
  : forall W `{EqDec W eq} X (lv:cset W) (D D':map W X),
    (agree_set lv D D') ⊆ lv.
Proof.
  intros. hnf; intros. eapply agree_set_spec in H0; firstorder.
Qed.


Lemma agree_set_incl_both 
  : forall W `{EqDec W eq} X (lv' lv:cset W) (D D':map W X),
    lv' ⊆ lv -> agree_set lv' D D' ⊆ agree_set lv D D'.
Proof.
  intros. hnf; intros. rewrite agree_set_spec in *; firstorder.
Qed.


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

Definition image W `{EqDec W eq} X (Df:Defaulted X) (f:map W X) := lookup_set f (domain f).

Hypothesis mapjoin : forall W X (m m':map W X) (s:cset W), map W X.

Hypothesis mapjoin_spec 
  : forall W `{EqDec W eq} X (m m':map W X) (s:cset W) x, 
    ((x ∈ s -> mapjoin m m' s [x] = m [x]) /\
    (x ∉ s -> mapjoin m m' s [x] = m' [x])).

Hypothesis neq_domain : forall W `{EqDec W eq} (m:map W W), cset W.

Hypothesis neq_domain_spec 
  : forall W `{EqDec W eq} (m:map W W) x, x ∈ neq_domain m <-> m [x] <> x /\ x ∈ domain m.

End BMap.



(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr" "../il"  "..") ***
*** End: ***
*)
