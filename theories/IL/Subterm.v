Require Import List IL.

Set Implicit Arguments.

Inductive subTerm : stmt -> stmt -> Prop :=
| subTerm_refl s : subTerm s s
| subTermExp s x e s' : subTerm s s' -> subTerm s (stmtLet x e s')
| subTermIf1 e s s' t : subTerm s s' -> subTerm s (stmtIf e s' t)
| subTermIf2 e s t t' : subTerm t t' -> subTerm t (stmtIf e s t')
| subTermExtern s x f e s' : subTerm s s' -> subTerm s (stmtExtern x f e s')
| subTermLet1 F t t' : subTerm t t' -> subTerm t (stmtFun F t')
| subTermLet2 s Zs F t n : get F n Zs -> subTerm s (snd Zs) -> subTerm s (stmtFun F t).

Instance subTerm_refl' : Reflexive subTerm.
Proof.
  hnf; intros. eapply subTerm_refl.
Qed.

Instance subTerm_trans : Transitive subTerm.
Proof.
  hnf; intros s t u ST1 ST2.
  general induction ST1; eauto;
  general induction ST2; eauto using subTerm.
Qed.


Lemma subTerm_occurVars s t
  : subTerm s t
    -> occurVars s ⊆ occurVars t.
Proof.
  intros. general induction H; simpl; eauto with cset.
  - eapply incl_union_left.
    eapply incl_list_union. eapply map_get_1; eauto.
    eauto with cset.
Qed.

Lemma subTerm_EQ_Let sT st x e s
  (EQ:st = stmtLet x e s)
  (ST:subTerm st sT)
  : subTerm s sT.
Proof.
  subst st. etransitivity; eauto. econstructor; reflexivity.
Qed.

Lemma subTerm_EQ_If1 sT st x s t
  (EQ:st = stmtIf x s t)
  (ST:subTerm st sT)
  : subTerm s sT.
Proof.
  subst st. etransitivity; eauto. econstructor; reflexivity.
Qed.

Lemma subTerm_EQ_If2 sT st x s t
  (EQ:st = stmtIf x s t)
  (ST:subTerm st sT)
  : subTerm t sT.
Proof.
  subst st. etransitivity; eauto. econstructor; reflexivity.
Qed.

Lemma subTerm_EQ_Extern sT st x f e s
  (EQ:st = stmtExtern x f e s)
  (ST:subTerm st sT)
  : subTerm s sT.
Proof.
  subst st. etransitivity; eauto. econstructor; reflexivity.
Qed.

Lemma subTerm_EQ_Fun1 sT st F t
  (EQ:st = stmtFun F t)
  (ST:subTerm st sT)
  : subTerm t sT.
Proof.
  intros. subst. etransitivity; eauto.
  eapply subTermLet1; eauto. reflexivity.
Qed.

Lemma subTerm_EQ_Fun2 sT st F t
  (EQ:st = stmtFun F t)
  (ST:subTerm st sT)
  : forall (n : nat) (s : params * stmt), get F n s -> subTerm (snd s) sT.
Proof.
  intros. subst. etransitivity; eauto.
  eapply subTermLet2; eauto. reflexivity.
Qed.

Require Import ProofIrrelevance.

Lemma subTerm_PI s s'
      (p p':subTerm s s')
  : p = p'.
Proof.
  eapply proof_irrelevance.
Qed.
