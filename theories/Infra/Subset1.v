Require Import CSet Var.
Notation "'Subset1'" := (fun (x : set var) (y : set var * set var) => x ⊆ fst y).


Instance Subset1_morph
: Proper (Equal ==> @pe _ _ ==> iff) Subset1.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl. rewrite H, H1. reflexivity.
Qed.
