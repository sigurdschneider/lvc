Require Import Util LengthEq IL RenamedApart LabelsDefined OptionR.
Require Import Keep Drop Take Restrict SetOperations OUnion.
Require Import Annotation Liveness.Liveness PartialOrder.

Set Implicit Arguments.

Definition addParam x (DL:list (set var)) (AP:list (set var)) :=
  zip (fun (DL:set var) AP => if [x ∈ DL]
                   then {x; AP} else AP) DL AP.

Lemma addParam_length x DL AP
 : length DL = length AP
   -> length (addParam x DL AP) = length DL.
Proof.
  intros. unfold addParam. eauto with len.
Qed.

Lemma addParam_zip_lminus_length DL ZL AP x
: length AP = length DL
  -> length DL = length ZL
  -> length (addParam x (DL \\ ZL) AP) = length DL.
Proof.
  eauto with len.
Qed.

Lemma PIR2_addParam DL AP x
  : length AP = length DL
    -> PIR2 Subset AP (addParam x DL AP).
Proof.
  intros A.
  eapply length_length_eq in A.
  general induction A.
  - constructor.
  - econstructor.
    + cases; cset_tac; intuition.
    + exploit (IHA x0); eauto.
Qed.

Lemma addParam_Subset x DL AP
: AP ⊑ DL
  -> addParam x DL AP ⊑ DL.
Proof.
  intros. general induction H; simpl.
  - constructor.
  - econstructor. cases; eauto.
    + hnf. cset_tac.
    + eapply IHPIR2.
Qed.

Lemma addParam_x DL AP x n ap' dl
  : get (addParam x DL AP) n ap'
    -> get DL n dl
    -> x ∉ ap' -> x ∉ dl.
Proof.
  unfold addParam; intros.
  edestruct get_zip as [? []]; eauto; dcr. clear H.
  repeat get_functional; subst.
  cases in H1; simpl in *.
  + cset_tac; intuition.
  + cset_tac; intuition.
Qed.

Lemma PIR2_not_in LV x DL AP
  : PIR2 (ifSndR Subset) (addParam x DL AP) LV
    -> length DL = length AP
    ->  forall (n : nat) (lv0 dl : set var),
        get LV n ⎣lv0 ⎦ -> get DL n dl -> x ∉ lv0 -> x ∉ dl.
Proof.
  intros LEQ LEN. intros. eapply length_length_eq in LEN.
  general induction n; simpl in *.
  - invc LEQ.
    cases in pf.
    + exfalso; cset_tac; intuition.
    + eauto.
  - inv H; inv H0; inv LEN; simpl in *. invc LEQ.
    eauto.
Qed.
