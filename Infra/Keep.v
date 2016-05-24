Require Import Util CSet Get EqDec MoreList AllInRel Relations.

Set Implicit Arguments.

Definition keep X m (AP:list X) :=
  mapi (fun n x => if [n = m] then Some x else None) AP.

Arguments keep [X] m AP.

Lemma keep_Some X AP n (x:X)
  : get AP n x
    -> get (keep n AP) n (Some x).
Proof.
  intros.
  eapply (get_mapi (fun n' x => if [n' = n] then ⎣x⎦ else ⎣⎦)) in H.
  cases in H; eauto.
Qed.

Lemma keep_None X n m AP (x:option X)
  : get (keep n AP) m x -> n <> m -> x = None.
Proof.
  intros. edestruct (mapi_get _ _ H) as [y [A B]].
  cases in B.
  - exfalso; eauto.
  - congruence.
Qed.

Lemma keep_get X AP n m (x:X)
  : get (keep n AP) m (Some x) -> get AP m x /\ n = m.
Proof.
  intros Get. edestruct (mapi_get _ _ Get) as [y [A B]].
  cases in B; easy.
Qed.

Lemma PIR2_ifFstR_keep X (R:relation X) `{Reflexive _ R} n (AP:list X)
  :  PIR2 (ifFstR R) (keep n AP) AP.
Proof.
  unfold keep, mapi. generalize 0.
  general induction AP; simpl.
  - econstructor.
  - cases; eauto using PIR2, @ifFstR.
Qed.
