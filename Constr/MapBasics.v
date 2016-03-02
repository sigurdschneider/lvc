Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util AutoIndTac.
Require Export CSet Containers.SetDecide OrderedTypeEx CSetComputable.

Set Implicit Arguments.

Section feq.
  Variable X : Type.
  Variable Y : Type.
  Variable R : relation Y.


  Definition feq (f g:X -> Y)
    := forall x, R (f x) (g x).

  Global Instance feq_reflexive `{Reflexive _ R}
  : Reflexive feq.
  hnf; intros. hnf; intros. reflexivity.
  Qed.

  Global Instance feq_symmetric `{Symmetric _ R}
  : Symmetric feq.
  hnf; intros. hnf; intros. symmetry. eapply H0; eauto.
  Qed.

  Global Instance feq_transitive `{Transitive Y R}
  : Transitive feq.
  hnf; intros. hnf; intros. transitivity (y x0); eauto.
  Qed.

  Global Instance feq_equivalence `{Equivalence Y R}
  : Equivalence feq.
  constructor; eauto using feq_reflexive, feq_symmetric, feq_transitive.
  Qed.

  Definition fpeq `{OrderedType X} `{OrderedType Y} (f g:X -> Y)
    := feq f g /\ Proper (_eq ==> _eq) f /\ Proper (_eq ==> _eq) g.

(*
Global Instance fpeq_symmetric {X : Type} {Y : Type} `{Equivalence Y}
: Symmetric (@fpeq X _ Y _ ).
hnf; intros. hnf; intros. symmetry. eapply H0; eauto.
Qed.

Global Instance feq_transitive {X : Type} {Y : Type} `{Equivalence Y}
: Transitive (@feq X Y _ _).
hnf; intros. hnf; intros. transitivity (y x0); eauto.
Qed.

Global Instance feq_equivalence {X : Type} {Y : Type} `{Equivalence Y}
       : Equivalence (@feq X Y _ _).
constructor; eauto using feq_reflexive, feq_symmetric, feq_transitive.
Qed.
*)

End feq.

Arguments feq {X} {Y} {R} f g.

Notation "f [-] g" := (@feq _ _ eq f g) (no associativity, at level 70) : fmap_scope.


Lemma equiv_nequiv_combine W `{OrderedType W} (x y z:W)
  : x === y -> y =/= z -> x =/= z.
Proof.
  intros. intro. eapply H1. transitivity x. symmetry; assumption. assumption.
Qed.

Ltac eqs :=
  repeat (match goal with
    | [H : ?l === ?k, H' : ?l =/= ?k |- _ ]
      => exfalso; eapply H'; eauto
    | [H : ?l === ?k, H' : ?k === ?j |- _ ] =>
       match goal with
         | [H' : l === j |- _ ] => fail 1
         | [ |- _ ] => match l with j => fail 2 end
         | [ |- _ ] => assert (l === j) by (transitivity k; eauto)
       end
    | [H : ?l === ?k, H' : ?k =/= ?l |- _ ]
      => exfalso; eapply H'; symmetry; eauto
    | [H : ?l === ?k, H' : ~?k === ?l |- _ ]
      => exfalso; eapply H'; symmetry; eauto
    | [H : ?l === ?k, H' : ?k =/= ?j |- _ ]
      => match goal with
           | [H' : l =/= j |- _ ] => fail 1
           | [ |- _ ] => assert (l =/= j) by (eapply equiv_nequiv_combine; eauto)
         end
    | [H : ~?l === ?k |- _ ] =>
      match goal with
        | [H' : l =/= k |- _ ] => fail 1
        | [ |- _ ] => assert (l =/= k) by (intro; eapply H; eauto); clear H
      end
    | [H : ?l === ?k |- _ ] =>
      match goal with
        | [H' : k === l |- _ ] => fail 1
        | [ |- _ ] => assert (k === l) by (symmetry; eauto)
      end
    | [H : ?l =/= ?k |- _ ] =>
      match goal with
        | [H' : k =/= l |- _ ] => fail 1
        | [ |- _ ] => assert (k =/= l) by (symmetry; eauto)
      end
    | [ |- _ ] => reflexivity
    | [ |- _ ] => symmetry; eassumption
  end).

(*
Lemma foo W `{OrderedType W} (x y z:W)
  : x === y -> y === x -> z === x -> forall x, x.
Proof.
  intros.
  intros. eqs.
Abort.

Lemma foo W `{OrderedType W} (x y:W)
  : ~x === y -> forall x, x.
Proof.
  intros. eqs.
Abort.


Lemma foo W `{OrderedType W} (x y z:W)
  : y =/= z -> forall x, x.
Proof.
  intros.  eqs.
Abort.


Lemma foo W `{OrderedType W} (x y z:W)
  : x === y -> y =/= z -> forall x, x.
Proof.
  Unset Ltac Debug.
  intros.
  Set Ltac Debug.
  eqs.
Qed.


Lemma foo W `{OrderedType W} (x y:W)
  : ~x === y -> y =/= x.
Proof.
  intros. eqs.
Qed.

Lemma foo2 W `{OrderedType W} (x y:W)
  : x === y -> y =/= x -> forall x, x.
Proof.
  intros. eqs.
Qed.

Lemma foo3 W `{OrderedType W} (x y:W)
  : x === y -> True.
intros. eqs.
*)

Section MapUpdate.
  Variable X Y : Type.
  Context `{OrderedType X}.

  Definition update (f:X->Y) (x:X) (y:Y) :=
    fun x' => if [x === x'] then y else f x'.

  Ltac eqdec :=
    match goal with
      | [ |- context[@decision_procedure ?P _ ] ] => decide(P); try eqs
      end.

  Lemma lookup_equiv f x y x'
    : x === x' -> (update f x y) x' = y.
  Proof.
    intros. eqs. unfold update. eqdec.
  Qed.

  Lemma lookup_nequiv f x y x'
    : x =/= x' -> (update f x y) x' = f x'.
  Proof.
    intros. unfold update. eqdec.
  Qed.
End MapUpdate.

Notation "f [ w <- x ]" := (update f w x) (at level 29, left associativity) : fmap_scope.

Ltac lookup_eq_tac :=
  match goal with
    | [H : ?x === ?x' |- context[update ?f ?x ?y ?x'] ]
      => rewrite (lookup_equiv f x y x' H)
    | [H : ?x === ?x', H' : context[update ?f ?x ?y ?x'] |- _ ]
      => rewrite (lookup_equiv f x y x' H) in H'
(*      | [H : ?k === ?l, I : context[find ?k (add ?l ?v ?M)] |- _ ]
        => let H := fresh "H" in assert (H:l === k) by eauto;
          rewrite (MF.add_eq_o M v H) in I; eauto
      | [H : context[([]) [_]] |- _ ]
        => rewrite (MF.empty_o) in H
      | [ |- context[([]) [_]] ]
        => rewrite (MF.empty_o)g *)
  end.

Ltac lookup_neq_tac :=
  match goal with
    | [H : ?x =/= ?x' |- context[update ?f ?x ?y ?x'] ]
      => rewrite (lookup_nequiv f y H)
    | [H : ?x =/= ?x', H' : context[update ?f ?x ?y ?x'] |- _ ]
      => rewrite (lookup_nequiv f y H) in H'
  end.

(*  Ltac lookup_neq_tac' :=
    match goal with
      | [H : not (eq ?k ?l), I : context[find ?k (add ?l _ ?M)] |- _ ]
        => rewrite MF.add_neq_o in I
      | [H : not (eq ?l ?k), I : context[find ?k (add ?l _ ?M)] |- _ ]
        => rewrite MF.add_neq_o in I
      | [H : ~ ?l === ?k, I : context[find ?k (add ?l ?v ?M)] |- _ ]
        => rewrite (MF.add_neq_o M v H) in I
      | [H : ~ ?k === ?l, I : context[find ?k (add ?l ?v ?M)] |- _ ]
        => let H := fresh "H" in assert (H:~ l=== k) by eauto;
          rewrite (MF.add_neq_o M v H) in I
    end.
*)
(*
  Ltac lookup_empty :=
    match goal with
      | [ |- context[ ]]
        => rewrite (@empty_spec W _ _ X def k)
      | [ H : context[@lookup _ _ _ _ (@empty ?W ?X ?def) ?k] |- _ ]
        => rewrite (@empty_spec W _ _ X def k) in H
    end.
*)

(* from Ralf's thesis *)

Tactic Notation "simplify" "lookup'" :=
  repeat (repeat (subst || lookup_eq_tac || lookup_neq_tac); eqs).

Ltac lud :=
  repeat (simplify lookup' || match goal with
    | [ x: _, x': _ |- context[update ?f ?x ?y ?x'] ]
      =>  match goal with
          | [H' : x === x' |- _ ] => fail 1
          | [H' : ~x === x' |- _ ] => fail 1
          | [H' : x =/= x' |- _ ] => fail 1
          | [ |- _ ] => decide(x === x')
          end
    | [ x: _, x': _, H : context[update ?f ?x ?y ?x'] |- _ ]
      => match goal with
          | [H' : x === x' |- _ ] => fail 1
          | [H' : ~x === x' |- _ ] => fail 1
          | [H' : x =/= x' |- _ ] => fail 1
          | [ |- _ ] => decide(x === x')
          end
  end).

Section UpdateFacts.
  Open Scope fmap_scope.

  Variable X Y : Type.
  Context `{OrderedType X}.


  Lemma update_commute (m : X -> Y) x x' y y':
    x =/= x' -> m[x <- y][x' <- y'] [-] m[x' <- y'][x <- y].
  Proof.
    intros ? x''; lud.
  Qed.

  Lemma update_shadow (m : X -> Y) (x : X) (y y' : Y) :
    (m[x <- y][x <- y']) === (m[x <- y']).
  Proof.
    intro l; lud.
  Qed.

  Lemma update_repeat (m : X -> Y) (x x' : X) (y y': Y) :
    m x = y -> m[x <- y] x = y.
  Proof.
    intros; lud.
  Qed.

(*
  Ltac lookup_def_eq_tac :=
    match goal with
      | [H : ?l === ?k |- context[find_def ?k (add ?l ?v ?M)] ]
        => rewrite (add_eq_od M v H)
      | [H : ?l === ?k, I : context[find_def ?k (add ?l ?v ?M)] |- _ ]
        => rewrite (add_eq_od M v H) in I
      | [H : ?k === ?l, I : context[find_def ?k (add ?l ?v ?M)] |- _ ]
        => let H := fresh "H" in assert (H:l === k) by eauto;
          rewrite (add_eq_od M v H) in I; eauto
      | [H : ?k === ?l |- context[find_def ?k (add ?l ?v ?M)] ]
        => let H := fresh "H" in assert (H:l === k) by eauto;
          rewrite (add_eq_od M v H); eauto
      | [ |- context[find_def ?k (add ?k ?v ?M)] ]
        => let H := fresh "H" in assert (H:k === k) by reflexivity;
          rewrite (add_eq_od M v H); eauto
      | [H : ?l === ?k |- find_def ?l ?M = find_def ?k ?M]
        => now (rewrite H; reflexivity)
    end.

  Ltac lookup_def_neq_tac :=
    match goal with
      | [H : ?l =/= ?k |- context[find_def ?k (add ?l _ ?M)] ]
        => rewrite add_neq_od
      | [H : ?k =/= ?l |- context[find_def ?k (add ?l _ ?M)] ]
        => rewrite add_neq_od
      | [H : ~ ?l === ?k |- context[find_def ?k (add ?l ?v ?M)] ]
        => rewrite (add_neq_od M v H)
      | [H : ~ ?k === ?l |- context[find_def ?k (add ?l ?v ?M)] ]
        => let H := fresh "H" in assert (H:~ l=== k) by eauto; rewrite (add_neq_od M v H)
    end.

  Ltac lookup_def_neq_tac' :=
    match goal with
(*      | [H : not (?k === ?l), I : context[find_def ?k (add ?l _ ?M)] |- _ ]
        => rewrite add_neq_od in I
      | [H : not (?l === ?k), I : context[find_def ?k (add ?l _ ?M)] |- _ ]
        => rewrite add_neq_od in I *)
      | [H : ~ ?l === ?k, I : context[find_def ?k (add ?l ?v ?M)] |- _ ]
        => rewrite (add_neq_od M v H) in I
      | [H : ~ ?k === ?l, I : context[find_def ?k (add ?l ?v ?M)] |- _ ]
        => match goal with
             |  [ J : ~ l === k |- _ ] =>
               rewrite (add_neq_od M v J) in I
             |  _ =>
               let H := fresh "H" in assert (H:~ l=== k) by eauto;
                 rewrite (add_neq_od M v H) in I
           end
    end.

  Lemma update_repeat' W `{OrderedType W} X `{Defaulted X} (m : Map[W, X]) (k l : W) :
    m[k <- m[.k.]][.l.] = m[.l.].
  Proof.
    intros. decide (l === k). repeat lookup_def_eq_tac.
    lookup_def_neq_tac; eauto.
  Qed.

  Tactic Notation "simplify" "lookup" :=
    repeat (subst
      || lookup_def_eq_tac || lookup_eq_tac
        || rewrite update_shadow in * || rewrite update_repeat' in *
          || lookup_neq_tac || lookup_def_neq_tac
            || lookup_neq_tac' || lookup_def_neq_tac' ).

*)

End UpdateFacts.
