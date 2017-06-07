Require Import Smpl LvcPlugin Coq.Bool.Bool.

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


Smpl Create inv_trivial [progress].
Smpl Create inversion_cleanup.

Smpl Add
     match goal with
     | [ H : True |- _ ] => clear H
     end : inv_trivial.

Ltac inv_if_ctor H A B :=
  let A' := eval hnf in A in
      let B' := eval hnf in B in
          is_constructor_app A'; is_constructor_app B'; inversion H; subst.

Ltac inv_if_one_ctor H A B :=
  first [ is_constructor_app A; inversion H; subst; clear H
        | is_constructor_app B; inversion H; subst; clear H ].

Ltac inv_trivial_base :=
  match goal with
  | [ H : @eq _ ?x ?x |- _ ] => clear H
  | [ H : @eq _ ?x ?y |- _ ] => first [ is_var x; subst x | is_var y; subst y ]
  | [ H : true = false |- _ ] => exfalso; inversion H
  | [ H : false = true |- _ ] => exfalso; inversion H
(*  | [ H : ?A = ?B |- _ ] => first [ is_constructor_app A;
                                  match B with
                                  | (if _ then _ else _) => fail 1
                                  | _ => inversion H; subst
                                  end
                                | is_constructor_app B;
                                  match A with
                                  | (if _ then _ else _) => fail 1
                                  | _ => inversion H; subst
                                  end
                                ]*)
  | [ H : ?A = ?B |- _ ] => inv_if_ctor H A B
  | [ H : ?n <= 0 |- _ ] => is_var n; inversion H; subst; clear H
  | [ H : @eq _ (Some ?x) (Some ?y) |- _ ]
    => let H' := fresh "H" in assert (H':x = y) by congruence; clear H;
                            first [ is_var x; subst x; clear H'
                                  | is_var y; subst y; clear H'
                                  | rename H' into H ]
  | [ H : ?a <> ?a |- _ ] => exfalso; eapply H; reflexivity
  end.

Smpl Add inv_trivial_base : inv_trivial.

Ltac inv_cleanup :=
  repeat (smpl inversion_cleanup).

Ltac clear_trivial_eqs :=
  repeat (smpl inv_trivial; repeat clear_dup_fast); inv_cleanup.


Tactic Notation "inv" hyp(A) := inversion A; subst; inv_cleanup.
Tactic Notation "invc" hyp(A) := inversion A; subst; (try clear A); inv_cleanup.
Tactic Notation "invs" hyp(A) := inversion A; subst; clear_trivial_eqs; inv_cleanup.
Tactic Notation "invcs" hyp(A) := inversion A; subst; (try clear A); clear_trivial_eqs;
                                 inv_cleanup.

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

Ltac invtc ty :=
  match goal with
      | h: ty |- _ => invc h
      | h: ty _ |- _ => invc h
      | h: ty _ _ |- _ => invc h
      | h: ty _ _ _ |- _ => invc h
      | h: ty _ _ _ _ |- _ => invc h
      | h: ty _ _ _ _ _ |- _ => invc h
      | h: ty _ _ _ _ _ _ |- _ => invc h
      | h: ty _ _ _ _ _ _ _ |- _ => invc h
      | h: ty _ _ _ _ _ _ _ _ |- _ => invc h
      | h: ty _ _ _ _ _ _ _ _ _ |- _ => invc h
  end.

Smpl Add 100
     match goal with
     | [ H : true -> false |- _ ] =>
       exfalso; eapply H; eauto
     | [ H : forall _ : Is_true true, Is_true false |- _ ] =>
       exfalso; eapply H; eauto
     end : inv_trivial.
