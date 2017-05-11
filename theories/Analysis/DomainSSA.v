Require Import CSet Le CMap CMapDomain CMapPartialOrder CMapJoinSemiLattice CMapTerminating.

Require Import Plus Util AllInRel CSet OptionR.
Require Import Val Var Env IL Annotation Infra.Lattice DecSolve.
Require Import CMap WithTop.
Require Import MapNotations ListUpdateAt.
Require Import Terminating OptionR.

Set Implicit Arguments.

Open Scope map_scope.

Definition Dom D := Map [var, D].

Definition domupd D (d:Dom D) x (o:option D) : Dom D :=
  match o with
  | Some xv => (d [- x <- xv -])
  | None => remove x d
  end.

Fixpoint domjoin_list D `{JoinSemiLattice D} (m:Dom D) (A:list var) (B:list (option D)) :=
  match A, B with
  | x::A, y::B =>
    domupd (domjoin_list m A B) x (join (find x m) y)
  | _, _ => m
  end.

Definition domenv D (d:Dom D) (x:var) : option D :=
  find x d.

Lemma poLe_option_None X `{PartialOrder X} (x:option X)
  :  ⎣⎦ ⊑ x.
Proof.
  econstructor.
Qed.

Hint Resolve poLe_option_None.

Lemma domupd_le D `{PartialOrder D} (a b: Dom D) v v' x
  : leMap a b
    -> poLe v v'
    -> leMap (domupd a x v) (domupd b x v').
Proof.
  unfold leMap, domupd; intros.
  inv H1.
  - repeat cases; clear_trivial_eqs; mlud; eauto.
  - mlud; eauto.
Qed.

Lemma domjoin_list_le D `{JoinSemiLattice D} (a b: Dom D) Z Y Y'
  : leMap a b
    -> poLe Y Y'
    -> leMap (domjoin_list a Z Y)
            (domjoin_list b Z Y').
Proof.
  general induction Z; simpl domjoin_list; eauto.
  inv H2; eauto.
  - eapply domupd_le.
    + eapply IHZ; eauto.
    + eapply ojoin_poLe; eauto.
Qed.

Lemma domupd_eq D `{PartialOrder D} (a b: Dom D) v v' x
  : eqMap a b
    -> poEq v v'
    -> eqMap (domupd a x v) (domupd b x v').
Proof.
  unfold eqMap, domupd; intros.
  inv H1.
  - eapply eqMap_remove; eauto.
  - repeat cases; clear_trivial_eqs. mlud; eauto.
    econstructor. eauto.
Qed.

Lemma domjoin_list_eq  D `{JoinSemiLattice D} (a b: Dom D) Z Y Y'
  : eqMap a b
    -> poEq Y Y'
    -> eqMap (domjoin_list a Z Y)
            (domjoin_list b Z Y').
Proof.
  general induction Z; simpl domjoin_list; eauto.
  inv H2; eauto.
  - eapply domupd_eq
    + eapply IHZ; eauto.
    + eapply ojoin_poEq; eauto.
Qed.

Lemma domjoin_ne D `{JoinSemiLattice D} (m:Dom D) x y a
  : x =/= y
    -> find x (domupd m y a) = find x m.
Proof.
  unfold domupd; cases; intros; mlud; eauto.
Qed.

Lemma domjoin_list_ne D `{JoinSemiLattice D} (m:Dom D) x Z Y
  : ~ InA eq x Z
    -> find x (domjoin_list m Z Y) === find x m.
Proof.
  intros NI.
  general induction Z; destruct Y; simpl; eauto.
  erewrite domjoin_ne; eauto. eapply IHZ; eauto.
  intro; eapply NI; econstructor. eapply H1.
Qed.

Lemma domjoin_list_exp  D `{JoinSemiLattice D} (m:Dom D) Z Y
  : leMap m (domjoin_list m Z Y).
Proof.
  general induction Z; destruct Y; simpl domjoin_list; eauto;
    try reflexivity.
  unfold ojoin; repeat cases; simpl domupd; eauto.
  - hnf; intros. mlud.
    + rewrite <- e, <- Heq.
      econstructor.
      eapply join_poLe.
    + eapply IHZ.
  - hnf; intros; mlud.
    rewrite Heq, e; eauto.
    eapply IHZ.
  - hnf; intros; mlud.
    rewrite <- e, <- Heq; eauto.
    eapply IHZ.
  - hnf; intros; mlud.
    rewrite <- e, <- Heq; eauto.
    eapply IHZ.
Qed.


Lemma domain_join_sig X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  (x y : {m : Map [X, Y] | domain m [<=] U})
  : domain (proj1_sig x ⊔ proj1_sig y) [<=] U.
Proof.
  destruct x,y; simpl.
  unfold joinMap. rewrite domain_join. cset_tac.
Qed.

Definition joinsig X `{OrderedType X} Y `{JoinSemiLattice Y}  U
           (x y : {m : Map [X, Y] | domain m ⊆ U}) :=
  exist (fun m => domain m ⊆ U) (join (proj1_sig x) (proj1_sig y)) (domain_join_sig x y).

Definition joinsig_idem X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  : forall a : {m : Map [X, Y] | domain m [<=] U}, joinsig a a ≣ a.
Proof.
  - hnf; intros [a ?]. simpl. eapply joinDom_idem.
Qed.

Definition joinsig_sym X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  : forall a b : {m : Map [X, Y] | domain m [<=] U}, joinsig a b ≣ joinsig b a.
Proof.
  - hnf; intros [a ?] [b ?]. eapply joinDom_sym.
Qed.

Definition joinsig_assoc X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  : forall a b c : {m : Map [X, Y] | domain m [<=] U}, joinsig (joinsig a b) c ≣ joinsig a (joinsig b c).
Proof.
  hnf; intros [a ?] [b ?] [c ?]. eapply joinDom_assoc.
Qed.

Definition joinsig_exp X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  : forall a b : {m : Map [X, Y] | domain m [<=] U}, a ⊑ joinsig a b.
Proof.
  hnf; intros [a ?] [b ?]; simpl. eapply joinDom_exp.
Qed.


Instance map_sig_semilattice_bound X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  : JoinSemiLattice ({ m : Map [X, Y] | domain m ⊆ U}) := {
  join x y := joinsig x y
}.
Proof.
  - eapply joinsig_idem.
  - eapply joinsig_sym.
  - eapply joinsig_assoc.
  - eapply joinsig_exp.
  - simpl. unfold Proper, respectful; intros. destruct x,y,x0,y0; simpl in * |- *.
    rewrite H2, H3. reflexivity.
  - simpl. unfold Proper, respectful; intros. destruct x,y,x0,y0; simpl in * |- *.
    rewrite H3, H2. reflexivity.
Defined.

Instance map_sig_lower_bounded X `{OrderedType X} Y `{JoinSemiLattice Y} U
  : LowerBounded { m : Map [X, Y] | domain m ⊆ U} :=
  {
    bottom := exist _ (empty _) (incl_empty _ _)
  }.
Proof.
  intros [a b]; simpl.
  eapply empty_bottom; eauto.
Defined.

Definition VDom U D := { m : Map [var, D] | domain m ⊆ U}.

Lemma domain_domupd_incl  D (m:Dom D) x v
  : domain (domupd m x v) ⊆ {x; domain m}.
Proof.
  unfold domupd; cases.
  - rewrite domain_add. reflexivity.
  - rewrite domain_remove. cset_tac.
Qed.

Lemma domain_domjoin_list_incl D `{JoinSemiLattice D} (m:Dom D) x v
  : domain (domjoin_list m x v) ⊆ of_list x ∪ domain m.
Proof.
  general induction x; destruct v; simpl.
  - cset_tac.
  - cset_tac.
  - cset_tac.
  - rewrite domain_domupd_incl.
    rewrite IHx; eauto. cset_tac.
Qed.

Lemma domupdd_dom D U (d:VDom U D) x v
  : x \In U -> domain (domupd (proj1_sig d) x v) [<=] U.
Proof.
  destruct d; simpl.
  rewrite domain_domupd_incl. intros. cset_tac.
Qed.

Lemma domjoin_list_dom D `{JoinSemiLattice D} U  (d:VDom U D) Z Y
  : of_list Z ⊆ U -> domain (domjoin_list (proj1_sig d) Z Y) [<=] U.
Proof.
  destruct d; simpl.
  rewrite domain_domjoin_list_incl. intros. cset_tac.
Qed.

Definition domupdd D U (d:VDom U D) x (v:option D) (IN:x ∈ U) : VDom U D :=
  (exist _ (domupd (proj1_sig d) x v) (domupdd_dom d v IN)).

Definition domjoin_listd D `{JoinSemiLattice D}
           U (d:VDom U D) Z Y (IN:of_list Z ⊆ U) : VDom U D :=
  (exist _ (domjoin_list (proj1_sig d) Z Y) (domjoin_list_dom d Z Y IN)).
