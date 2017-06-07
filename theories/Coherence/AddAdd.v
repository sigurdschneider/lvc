Require Import Util LengthEq IL RenamedApart LabelsDefined OptionR.
Require Import Keep Drop Take Restrict SetOperations OUnion.

Set Implicit Arguments.

Definition addAdd s := (fun (DL:set var) AP => mdo t <- AP; Some ((s ∩ DL) ∪ t)).

Lemma ifSndR_zip_addAdd s DL A B
 : length DL = length A
   -> PIR2 (ifSndR Subset) A B
   -> PIR2 (ifSndR Subset) A (zip (addAdd s) DL B).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; inv H0; simpl.
  - constructor.
  - econstructor; eauto.
    + inv pf; simpl; econstructor.
      * cset_tac; intuition.
Qed.

Lemma ifFstR_addAdds s A B
: PIR2 (ifFstR Subset) B  A
  -> PIR2 (ifFstR Subset) (zip (addAdd s) A B) A.
Proof.
  intros.
  general induction H; simpl.
  + constructor.
  + econstructor; eauto.
    - inv pf; simpl; econstructor.
      * cset_tac; intuition.
Qed.

Lemma PIR2_addAdds s DL b
: length DL = length b
  -> PIR2 ≼ b (zip (addAdd s) DL b).
Proof.
  intros. eapply length_length_eq in H.
  general induction H.
  - econstructor.
  - simpl. econstructor.
    + destruct y.
      * econstructor. cset_tac; intuition.
      * constructor.
    + eauto.
Qed.

Lemma PIR2_addAdds' s DL b c
  : length DL = length b
    -> PIR2 ≼ b c
    -> PIR2 ≼ b (zip (addAdd s) DL c).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; invt PIR2.
  - econstructor.
  - simpl. econstructor.
    + destruct y,y0; simpl; try now econstructor.
      * econstructor. inv pf. cset_tac; intuition.
      * inv pf.
    + eauto.
Qed.

Lemma ifFstR_addAdds2 s A B C
  : PIR2 Subset A C
  -> PIR2 (ifFstR Subset) B C
  -> PIR2 (ifFstR Subset) (zip (addAdd s) A B) C.
Proof.
  intros R1 R2.
  general induction R1; inv R2; simpl; eauto using @PIR2.
  + econstructor; eauto.
    - inv pf0; simpl; econstructor.
      * cset_tac; intuition.
Qed.
