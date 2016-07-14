
(* fail 1 will break from the 'match H with', and indicate to
   the outer match that it should consider finding another
   hypothesis, see documentation on match goal and fail
   This tactic is a variation of Tobias Tebbi's revert_except_until *)

Ltac revert_except E :=
  repeat match goal with
           [H : _ |- _] =>
           match H with
             | E => fail 1
             | _ => revert H
               end
         end.

Ltac clear_except E :=
  repeat match goal with
           [H : _ |- _] =>
           match H with
             | E => fail
             | _ => clear H
               end
         end.

Ltac clear_all :=
  repeat match goal with
           [H : _ |- _] =>  clear H
         end.

Ltac revert_all :=
  repeat match goal with
           [H : _ |- _] => revert H
         end.

(*
(* succeed if H has a function type, fail otherwise *)
Ltac is_ftype H :=
  let t := type of H in
    let t' := eval cbv in t in
      match t' with
        | _ -> _ => idtac
      end.
*)
(* match on the type of E and remember each of it's arguments
   that is not a variable by calling tac.
   tac needs to do a remember exactly if x is not a var, and
   fail otherwise. (We need to fail, otherwise the repeat will
   stop prematurely)
   try will silently ignore a fail 0, but will fail if a fail 1 or
   above occurs. Sequentialization makes sure fail 1 is executed
   if is_var is successful, hence try (is_var x; fail 1) will
   fail exactly when x is a var. *)

Class DoNotRemember (T:Type) := DNR { Q:Type }.

Ltac remember_arguments E :=
  let tac x := (try (is_var x; fail 1);
               try (assert (DoNotRemember x) by eauto with typeclass_instances; fail 1 );
               remember (x))
  in
  repeat (match type of E with
    | ?t ?x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => tac x
    | ?t ?x _ _ _ _ _ _ _ _ _ _ _ _ _ _ => tac x
    | ?t ?x _ _ _ _ _ _ _ _ _ _ _ _ _ => tac x
    | ?t ?x _ _ _ _ _ _ _ _ _ _ _ _ => tac x
    | ?t ?x _ _ _ _ _ _ _ _ _ _ _ => tac x
    | ?t ?x _ _ _ _ _ _ _ _ _ _ => tac x
    | ?t ?x _ _ _ _ _ _ _ _ _ => tac x
    | ?t ?x _ _ _ _ _ _ _ _ => tac x
    | ?t ?x _ _ _ _ _ _ _ => tac x
    | ?t ?x _ _ _ _ _ _ => tac x
    | ?t ?x _ _ _ _ _ => tac x
    | ?t ?x _ _ _ _ => tac x
    | ?t ?x _ _ _ => tac x
    | ?t ?x _ _ => tac x
    | ?t ?x _ => tac x
    | ?t ?x => tac x
  end).

(* from Coq.Program.Tactics *)
Ltac clear_dup :=
(*  match goal with
  | [ H : ?X, H' : ?X |- _ ] => clear H' || clear H
  end.*)
  match goal with
  | [ H : ?X |- _ ] =>
    match goal with
    | [ H' : ?Y |- _ ] =>
      match H with
      | H' => fail 2
      | _ => unify X Y ; (clear H' || clear H)
      end
    end
  end.

Ltac clear_if_dup H :=
  match type of H with
    | ?X =>
      match goal with
      | [ H' : ?Y |- _ ] =>
        match H with
        | H' => fail 2
        | _ => unify X Y ; (clear H' || clear H)
        end
      end
  end.

Ltac inv_eqs :=
  repeat (match goal with
              | [ H : @eq _ ?x ?x |- _ ] => clear H
              | [ H : @eq _ ?x ?y |- _ ] => progress (inversion H; subst; try clear_dup)
            end).

(* this is a standard tactic *)
Ltac clear_trivial_eqs :=
  repeat (progress (match goal with
                    | [ H : @eq _ ?x ?x |- _ ] => clear H
                    | [ H : @eq _ ?x ?y |- _ ] => first [ is_var x; subst x | is_var y; subst y ]
                    | [ H : true = false |- _ ] => exfalso; inversion H
                    | [ H : @eq _ (Some ?x) (Some ?y) |- _ ]
                      => let H' := fresh "H" in assert (H':x = y) by congruence; clear H;
                                              first [ is_var x; subst x; clear H'
                                                    | is_var y; subst y; clear H'
                                                    | rename H' into H ]
                    end)).

Tactic Notation "general" "induction" hyp(H) :=
  remember_arguments H; revert_except H;
  induction H; intros; (try inv_eqs); (try clear_trivial_eqs).

Tactic Notation "indros" :=
  intros; (try inv_eqs); (try clear_trivial_eqs).

Module Test.
Require Import List.

Inductive decreasing : list nat -> Prop :=
  | base : decreasing nil
  | step m n L : decreasing (n::L) -> n <= m -> decreasing (m :: n :: L).

Lemma all_zero_by_hand L
  : decreasing (0::L) -> forall x, In x L -> x = 0.
Proof.
  intros. remember (0::L).
  revert dependent L. revert x. induction H; intros.
  inversion Heql.
  inversion Heql. subst. inversion H0; subst; firstorder.
Qed.

Lemma all_zero L
  : decreasing (0::L) -> forall x, In x L -> x = 0.
Proof.
  intros. general induction H.
  inversion H0; subst; firstorder.
Qed.
End Test.