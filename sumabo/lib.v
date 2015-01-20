Ltac typeof s := let T := type of s in T.

Require Import Coq.Program.Tactics.
Require Import FunctionalExtensionality.

Ltac f_ext := apply functional_extensionality.



Definition _bind (T1 : Type) (T2 : Type) (n : T2 -> nat) := T2.
Notation "{ 'in' T2 'bind' n 'of' T1 }" := (_bind T1 T2 (fun _ => n)) : bind_scope.
Notation "{ 'in' T2 'bind' T1 }" := (_bind T1 T2 (fun _ => 1)) : bind_scope.
Notation "{ 'bind' n 'of' T }" := (_bind T T (fun _ => n)) : bind_scope.
Notation "{ 'bind' T }" := (_bind T T (fun _ => 1)) : bind_scope.
Notation "{ 'in' T2 'as' x 'bind' n 'of' T1 }" := (_bind T1 T2 (fun x => n)) (x ident): bind_scope.

Open Scope bind_scope.

Definition var := nat.

Ltac autorew := repeat match goal with [H : _ |- _] => rewrite H end.

Notation nosimpl t := (let 'tt := tt in t).

Definition id {A} (x : A) := x.
Arguments id {A} x /.
Hint Unfold id.

Definition funcomp {A B C : Type} (f : B -> C) (g : A -> B) x := f(g(x)).
Arguments funcomp {A B C} f g x /. 
Infix "\o" := funcomp (at level 50, left associativity).

Lemma conj' (A B : Prop) : A -> (A -> B) -> A /\ B. 
Proof. tauto. Qed.

Definition iter := nosimpl (fix iter {A} (f : A -> A) n a :=
  match n with
    | 0 => a
    | S n' => f(iter f n' a)
  end). 
Arguments iter {A} f n a.

Lemma iter_S {A} (f : A -> A) n a : iter f (S n) a = f (iter f n a).
Proof. reflexivity. Qed.

Lemma iter_0 {A} (f : A -> A) a : iter f 0 a = a.
Proof. reflexivity. Qed.

Ltac autorevert x := 
  try (match goal with
    | [y : ?Y |- ?claim] =>
      try(match x with y => idtac end; fail 1);
        match goal with [z : _ |- _] => 
          match claim with appcontext[z] => 
            first[
                match Y with appcontext[z] => revert y; autorevert x end 
              | match y with z => revert y; autorevert x end]  
          end
        end 
       end).

Tactic Notation "in_all" tactic(T) :=
  repeat match goal with [H : _ |- _] =>
                  first[T H; try revert H | revert H]
  end; intros.

(** A variant of the do tactical that behaves like a limit to repeat *)

Ltac do_try n t := match n with 0 => idtac | S ?n' => try (progress t; do_try n' t) end.
Tactic Notation (at level 3) "do?" constr(n) tactic3(t) := do_try n t. 


Ltac clear_all := repeat match goal with H : _ |- _ => clear H end.
Ltac is_trivial s := try (assert s; [clear_all; (now idtac || fail 1) | fail]).

Ltac clean := 
  (let T H := let s := typeof H in is_trivial s; clear H in
  in_all T); clear_dups.

Ltac inv H := inversion H; subst; clear H.

Ltac ainv t :=
  clean;
  do? 10 (idtac; match goal with 
        | H : ?s |- _ =>
            progress( 
                (cut True; [ 
                   inv H; t
                 | ]); [(intros _ || trivial) | now idtac ..]; clean
              )
         end).

Tactic Notation "ainv" tactic(t) := ainv t.

Tactic Notation "ainv" := ainv trivial.

Tactic Notation "ren" ident(H) ":" open_constr(T) := 
match goal with [G : T |- _] =>
  let T' := typeof G in unify T T'; rename G into H end.

Tactic Notation "renc" ident(H) ":" open_constr(T) := 
  match goal with [G : appcontext C [T] |- _] =>
                  let TG := typeof G in
                  let CT := context C [T] in
                  unify TG CT;
                  rename G into H 
  end.