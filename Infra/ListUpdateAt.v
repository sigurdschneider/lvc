Require Import Util Get.

Fixpoint list_update_at {X} (L:list X) (n:nat) (v:X)  :=
  match L, n with
  | x::L, 0 => v::L
  | x::L, S n => x::list_update_at L n v
  | _, _ => nil
  end.

Lemma list_update_at_length X (l:list X) off v
  : length (list_update_at l off v) = length l.
Proof.
  general induction l; simpl; eauto.
  - destruct off; simpl; eauto.
Qed.

Lemma list_update_at_get_1 X (l:list X) off v v' n
  : get (list_update_at l off v') n v
    -> n <> off
    -> get l n v.
Proof.
  intros. general induction l; simpl in * |- *; isabsurd.
  - destruct off; simpl in *.
    * inv H; intuition.
    * inv H; intuition (eauto using get).
Qed.

Lemma list_update_at_get_2 X (l:list X) off v v' n
  : get (list_update_at l off v') n v
    -> n = off
    -> v = v'.
Proof.
  intros.
  general induction H; simpl in * |- *; isabsurd.
  - destruct l; simpl in *; isabsurd; congruence.
  - destruct l; simpl in *; isabsurd.
    inv Heql0; eauto.
Qed.

Lemma list_update_at_get_3 X (l:list X) v' v n
  : get l n v'
    -> get (list_update_at l n v) n v.
Proof.
  intros Get.
  general induction Get; simpl in * |- *; eauto with get.
Qed.
