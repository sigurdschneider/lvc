Require Import Var Val Env CSet Map.

Set Implicit Arguments.

Open Scope map_scope.
(** * Types for Environments *)

Definition envOfType (E:onv val) (ET:onv ty) : Prop := 
  forall x t, ET x = Some t -> exists v, E x = Some v /\ valOfType v t.

Definition ompty X : onv X := fun _ => None.

(** Stability under typed update *)
Lemma envOfType_update E (ET:onv ty) (ETd:envOfType E ET) v t (vtd:valOfType v t) x
  : envOfType (E[x<-Some v]) (ET[x<-Some t]).
Proof.
  intros y t'. lud.
  + inversion 1; subst; eauto.
  + eauto.
Qed.

(** Anything is well typed under the empty environment *)
Lemma envOfType_empty E
  : envOfType E (ompty ty).
Proof. 
  intros x t neq. inv neq.
Qed.

(** ** A relation characterizing sub-environment *) 

Definition subEnv Y (E E':onv Y)
  := forall x y, E x = Some y -> E' x = Some y.

Lemma subEnv_refl Y (E:onv Y)
  : subEnv E E.
Proof.
  firstorder.
Qed.
 
Lemma subEnv_empty Y (E:onv Y)
  : subEnv (ompty Y) E.
Proof.
  hnf; intros. inv H.
Qed.

Lemma envOfType_weakening E ET ET'
  : subEnv ET ET' -> envOfType E ET' -> envOfType E ET.
Proof.
  intros A B x t eq. eauto.
Qed.

Lemma subEnv_update Y (ET ET':onv Y) x y
  : subEnv ET ET' -> subEnv (ET[x<-y]) (ET'[x<-y]).
Proof.
  intros; hnf; intros. lud. eauto.
Qed.

Lemma subEnv_trans Y (ET ET' ET'':onv Y)
  : subEnv ET ET' -> subEnv ET' ET'' -> subEnv ET ET''.
Proof.
  intros; hnf; intros. firstorder.
Qed.

(** ** Environment Equivalence at an environment type *)

Definition typed_eq {X Y:Type} (ET:onv Y) (E E': env X) :=
  forall x t, ET x = Some t -> E x = E' x.


Lemma typed_eq_refl (X Y:Type) (ET:onv Y) : forall (E:env X), typed_eq ET E E.
  firstorder.
Qed.

Hint Resolve typed_eq_refl.

Global Instance typed_eq_Refl {X Y Z:Type} {ET:onv Y}
  : Reflexive (typed_eq ET) := @typed_eq_refl X Y ET.

Lemma typed_eq_sym X Y ET : forall E E', @typed_eq X Y ET E E' -> typed_eq ET E' E.
  hnf. unfold typed_eq. intros. symmetry; eauto.
Qed.

Global Instance typed_eq_Sym {X Y ET} `{Defaulted X} : Symmetric (typed_eq ET) := 
  @typed_eq_sym X Y ET.

Lemma typed_eq_trans X Y ET : forall E E' E'',
  @typed_eq X Y ET E E' -> typed_eq ET E' E'' -> typed_eq ET E E''.
  hnf. unfold typed_eq. intros. erewrite H; eauto.
Qed.
  
Global Instance typed_eq_Trans {X Y ET} `{Defaulted X} : Transitive (typed_eq ET) := 
  @typed_eq_trans X Y ET.


Lemma typed_eq_update Y (ET:onv Y) (E E':env val) (y:Y) (x:var) (z:val) 
  : typed_eq ET E E' -> typed_eq (ET [x <- Some y]) (E [x <- z]) (E' [x <- z]).
Proof.
  intros A a t eq. lud. eauto.
Qed.

Lemma typed_eq_empty (Y:Type) (E E':env val)
  : typed_eq (ompty Y) E E'.
Proof.
  intros x t neq. inv neq.
Qed.

Lemma typed_eq_envOfType ET E E'
  : typed_eq ET E E' -> envOfType E ET -> envOfType E' ET.
Proof.
  intros A B x t eq. erewrite <- A; eauto.
Qed.

Lemma typed_eq_weakening Y (ET ET': onv Y) (E E':env val)
  : typed_eq ET E E' -> subEnv ET' ET -> typed_eq ET' E E'.
Proof.
  intros A B x t eq. eauto.
Qed.

(* some orphaned definitions *)

Definition updD (D:env nat) (Z:list var) := 
  update_list D (fun x => S(D x)) Z.

Lemma updD_no_param D Z x
  : x ∉ of_list Z
  -> (updD D Z) x === D x.
Proof. 
  intros; unfold updD. eapply update_list_no_upd; eauto.
Qed.

Lemma updD_param D Z x
  : x ∈ of_list Z
  -> (updD D Z) x === S (D x).
Proof.
  intros. unfold updD. rewrite update_list_upd; intros; eauto.
Qed.



(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
