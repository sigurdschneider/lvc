
Notation "'Sigma' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Lemma test
  : Sigma x y z, x + y = z.
Proof.
  exists 1, 2, 3. auto.
Qed.


Require Import Setoid Morphisms.
Require Export Coq.Classes.Equivalence.

Ltac diverge a := diverge a.

Parameter T : Prop.
Parameter t : T.

Hint Extern 1 (T) => apply t.
Hint Extern 2 (T) => diverge idtac.

Lemma test2 : T.
                Unset Ltac Debug.
                auto.


Require Import List Pos Drop.

Definition test (L : list nat) (F : list nat) (i : nat) (H : length F = length L)
         :
           forall f i' k,
             pos (drop (i - length L + length L) F) f k = Some i' -> True.

Lemma test (L : list nat) (F : list nat) (i : nat) (H : length F = length L)
         :
           forall f i' k,
             pos (drop (i - length L + length L) F) f k = Some i' -> True.
               Typeclasses eauto := debug 5.
               setoid_rewrite <- H at 2.
               Show Proof.
               Check forall (L F: list nat) i f i' k, (PER_morphism (Equivalence_PER OrderedType.SOT_Equivalence)
               (pos (drop (i - length L + length L) F) f k)
               (pos (drop (i - length L + length F) F) f k)
               (reflexive_proper (pos (X:=nat))
                  (drop (i - length L + length L) F)
                  (drop (i - length L + length F) F)
                  (reflexive_proper drop (i - length L + length L)
                     (i - length L + length F)
                     (Reflexive_partial_app_morphism PeanoNat.Nat.add_wd
                        (eq_proper_proxy (i - length L))
                        (length L) (length F) (symmetry H)) F F
                     (eq_proper_proxy F)) f f (eq_proper_proxy f) k k
                  (eq_proper_proxy k)) ⎣ i' ⎦ ⎣ i' ⎦
               (eq_proper_proxy ⎣ i' ⎦)).
               Show Proof.

Check (subrelation_proper all_iff_morphism tt).
   (subrelation_respectful (subrelation_refl (pointwise_relation nat iff))
      iff_flip_impl_subrelation)).
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL Bisim Infra.Status Pos.

Set Implicit Arguments.
Unset Printing Records.



Require Import CSet Le CSetTac IL. (* Le CSetTac IL Annotation *)
(*Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec Get AllInRel.*)
(* Require Import Map.*)


Require Import MapBasics MapLookup MapLookupList MapAgreement.
Require Import MapInjectivity MapUpdate MapAgreeSet MapInverse MapComposition.

Require Import SetOperations.
(*Require Export Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList OptionMap Events Size.
Require Import SetOperations.*)

Goal (exists x, x [<=] x).
  eexists.
  Unset Ltac Debug.
  time eauto. has_evar
Abort.

Inductive f (a b:Type) := F.

Hint Extern 20 (f ?a ?a') => progress (first [ has_evar a | has_evar a' | reflexivity]).
Hint Extern 20 => match goal with
                 | [ H : True |- _ ] => clear H
                 end.

Goal (forall a, exists x, f a x).
  intros. eexists.
  eauto.
