(** Some generally useful tactics. *)

(** The venerable if tactical. (from cocorico) *)
Tactic Notation "if" tactic(t) "then" tactic(t1) "else" tactic(t2) :=
  first [ t; first [ t1 | fail 2 ] | t2 ].

(** Destruct if arguments for case analysis. *)
(*
Tactic Notation "destruct" "if" "in" "*" :=
  repeat (match goal with
    | |-  context [if ?P then _ else _]      => destruct P
    | _ : context [if ?P then _ else _] |- _ => destruct P
  end).
*)

(* Destruct all records, that is, inductive types with a single constructor. *)
Tactic Notation "decompose" "records" :=
  repeat (
    match goal with
      | H: _ |- _ => progress (decompose record H); clear H
    end).

Tactic Notation "dcr" :=
  repeat (
    match goal with
      | H: _ |- _ => progress (decompose record H); clear H
    end).

(* This is a version of subst which doesn't fail and performs local
 * substitutions. This does not handle setoid equalities. *)
Tactic Notation "subst" "++" :=
  repeat (
    match goal with
      | H : _ |- _ => subst H
    end);
  cbv zeta beta in *.

(* This tactic calls intro's on dependent arguments - it strips
   "forall"s from the goal, but leaves simple implications intact. *)
Ltac dependent_intros :=
  repeat match goal with
      | [|- ?A -> ?B] => fail 1
      | [|- ?A ->  _] => intros ?
    end.

Ltac abstract_pair a b :=
  let r := fresh "r" in
    pose (r := (a,b));
      replace (a,b) with r in * by reflexivity;
      replace a with (fst r) in * by reflexivity;
      replace b with (snd r) in * by reflexivity.

(* From Program.Tactics *)
Ltac destruct_one_pair :=
 match goal with
   | [H : (_ /\ _) |- _] => destruct H
   | [H : prod _ _ |- _] => destruct H
 end.

Ltac destruct_pairs := repeat (destruct_one_pair).