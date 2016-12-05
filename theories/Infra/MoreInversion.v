Require Import Smpl LvcPlugin.

Set Implicit Arguments.

Set Regular Subst Tactic.

Ltac clear_dup_fast :=
  match goal with
  | [ H : ?X, H' : ?X |- _ ] => first [clear H' || clear H]
  end.

Ltac inv_eqs :=
  repeat (match goal with
              | [ H : @eq _ ?x ?x |- _ ] => clear H
              | [ H : @eq _ ?x ?y |- _ ] => progress (inversion H; subst; try clear_dup_fast)
            end).


Smpl Create inv_trivial.

Ltac inv_trivial_base :=
  match goal with
  | [ H : @eq _ ?x ?x |- _ ] => clear H
  | [ H : @eq _ ?x ?y |- _ ] => first [ is_var x; subst x | is_var y; subst y ]
  | [ H : true = false |- _ ] => exfalso; inversion H
  | [ H : false = true |- _ ] => exfalso; inversion H
  | [ H : ?A = ?B |- _ ] => first [ is_constructor_app A;
                                  match B with
                                  | (if _ then _ else _) => fail 1
                                  | _ => inversion H; subst
                                  end
                                | is_constructor_app B;
                                  match A with
                                  | (if _ then _ else _) => fail 1
                                  | _ => inversion H; subst
                                  end
                                ]
(*  | [ H : nil = _ :: _ |- _ ] => exfalso; discriminate H
  | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst *)
  | [ H : ?n <= 0 |- _ ] => is_var n; inversion H; subst; clear H
  | [ H : @eq _ (Some ?x) (Some ?y) |- _ ]
    => let H' := fresh "H" in assert (H':x = y) by congruence; clear H;
                            first [ is_var x; subst x; clear H'
                                  | is_var y; subst y; clear H'
                                  | rename H' into H ]
  end.

Smpl Add inv_trivial_base : inv_trivial.

Ltac clear_trivial_eqs :=
  repeat (smpl inv_trivial; repeat clear_dup_fast).

Tactic Notation "inv" hyp(A) := inversion A; subst.
Tactic Notation "invc" hyp(A) := inversion A; subst; (try clear A).
Tactic Notation "invs" hyp(A) := inversion A; subst; clear_trivial_eqs.
Tactic Notation "invcs" hyp(A) := inversion A; subst; (try clear A); clear_trivial_eqs.

Ltac invt ty :=
  match goal with
      | h: ty |- _ => inv h
      | h: ty _ |- _ => inv h
      | h: ty _ _ |- _ => inv h
      | h: ty _ _ _ |- _ => inv h
      | h: ty _ _ _ _ |- _ => inv h
      | h: ty _ _ _ _ _ |- _ => inv h
      | h: ty _ _ _ _ _ _ |- _ => inv h
      | h: ty _ _ _ _ _ _ _ |- _ => inv h
      | h: ty _ _ _ _ _ _ _ _ |- _ => inv h
      | h: ty _ _ _ _ _ _ _ _ _ |- _ => inv h
  end.

Ltac invts ty :=
  match goal with
      | h: ty |- _ => invs h
      | h: ty _ |- _ => invs h
      | h: ty _ _ |- _ => invs h
      | h: ty _ _ _ |- _ => invs h
      | h: ty _ _ _ _ |- _ => invs h
      | h: ty _ _ _ _ _ |- _ => invs h
      | h: ty _ _ _ _ _ _ |- _ => invs h
      | h: ty _ _ _ _ _ _ _ |- _ => invs h
      | h: ty _ _ _ _ _ _ _ _ |- _ => invs h
      | h: ty _ _ _ _ _ _ _ _ _ |- _ => invs h
  end.
