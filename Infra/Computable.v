(** * Classical reasoning on decidable propositions.
  There are two principal type classes used here:
  - Computable P means that we can decide {P} + {~P},
  - Decidable P is the same thing in Prop (P \/ ~P).

  Given an instance of Decidable P we can transform a goal
  T |- P into T, ~P |- False and use tauto to get a complete
  decision procedure for classical logic by Glivenko's theorem.
  This is implemented in the dtauto tactic.

  Furthermore there are two tactics dleft, dright which correspond
  to classical_left and classical_right. *)
Require Import Coq.Program.Tactics.
Require Export CoreTactics Bool.

Class Computable (P : Prop) := decision_procedure : { P } + { ~P }.
Opaque decision_procedure.

Arguments decision_procedure P {Computable}.

Local Obligation Tactic := decompose records; firstorder.

(** Propositional formulas over computable atoms are computable. *)
Section ComputableInstances.
  Global Program Instance inst_true_cm  : Computable True.
  Global Program Instance inst_false_cm : Computable False.

  Variable P : Prop.
  Variable H : Computable P.

  Global Program Instance inst_not_cm : Computable (~P).

  Variable Q  : Prop.
  Variable H' : Computable Q.

  Global Program Instance inst_and_cm  : Computable (P /\ Q).
  Global Program Instance inst_or_cm   : Computable (P \/ Q).
  Global Program Instance inst_impl_cm : Computable (P -> Q).
  Global Program Instance inst_iff_cm  : Computable (P <-> Q).
End ComputableInstances.

Extraction Inline inst_true_cm_obligation_1 inst_false_cm_obligation_1
  inst_not_cm_obligation_1 inst_and_cm_obligation_1 inst_or_cm_obligation_1
  inst_impl_cm_obligation_1 inst_iff_cm_obligation_1
  inst_and_cm inst_or_cm inst_impl_cm inst_iff_cm.

(** Lift boolean predicates to computable Props. *)

Coercion Is_true : bool >-> Sortclass.

Global Instance inst_Is_true_cm (b : bool) : Computable (Is_true b).
  destruct b; simpl; firstorder.
Defined.

Extraction Inline inst_Is_true_cm.

(** Classical axioms for decidable predicates. *)
Lemma decidable_xm P `(Computable P) : P \/ ~P.  destruct H; tauto. Qed.
Lemma decidable_dn P `(Computable P) : ~~P -> P. destruct H; tauto. Qed.

Lemma dleft (P Q : Prop) `(Computable Q) :
  (~Q -> P) -> P \/ Q.
Proof.
  destruct H; tauto.
Qed.

Lemma dright (P Q : Prop) `(Computable P) :
  (~P -> Q) -> P \/ Q.
Proof.
  destruct H; tauto.
Qed.

(** dcontra applies double negation to the current goal if it is decidable. *)
Ltac dcontra :=
  (match goal with
     | |- ?H => apply (decidable_dn H _)
   end) || fail "Could not prove that the goal is a decidable proposition.".

(** dtauto does the same thing as tauto with classical the goal is decidable. *)
Ltac dtauto := tauto || (intros; dcontra; tauto) || fail "dtauto failed".

(** Similarly, dleft and dright are the analogs to classical_left/right. *)
Ltac dleft :=
  match goal with
    | |- ?P \/ ?Q => apply (dleft P Q _)
  end.

Ltac dright :=
  match goal with
    | |- ?P \/ ?Q => apply (dright P Q _)
  end.

(** destruct [P] does case analysis on decidable propositions. *)
(* More concretely, if the goal is in Prop then P has to be decidable,
   otherwise P should be computable. *)
Ltac decide_tac P :=
  match goal with
    | |- ?H =>
      match type of H with
        | _    => destruct (@decision_procedure P _) || fail 2 "not a computable proposition."
      end
  end.

Tactic Notation "decide" constr(P) := decide_tac P.

(** Programming with computable Props. *)
Notation "'if' [ P ] 'then' s 'else' t" :=
  (if (@decision_procedure P _) then s else t) (at level 200, right associativity, format
  "'if'  [ P ]  'then'  s  'else'  t").

Extraction Inline decision_procedure.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
