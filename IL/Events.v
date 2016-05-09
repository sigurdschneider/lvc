Require Import List.
Require Export Util Val.

Set Implicit Arguments.

Definition external := nat.

Inductive extern :=
  ExternI {
      extern_fnc : external;
      extern_args : list val;
      extern_res  : val
    }.

Inductive event :=
  | EvtExtern (call:extern)
(*  | EvtTerminate   (res:val) *)
  | EvtTau.

(** ** [filter_tau] *)

Definition filter_tau (o:event) (L:list event) : list event :=
  match o with
      | EvtTau => L
      | e => e :: L
  end.

Lemma filter_tau_nil evt B
 : (filter_tau evt nil ++ B)%list = filter_tau evt B.
Proof.
  destruct evt; simpl; eauto.
Qed.

Lemma filter_tau_app evt A B
 :  (filter_tau evt A ++ B)%list = filter_tau evt (A ++ B).
Proof.
  destruct evt; eauto.
Qed.
