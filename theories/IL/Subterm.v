Require Import List IL DecSolve.

Set Implicit Arguments.

Inductive subTermInd : stmt -> stmt -> Prop :=
| subTermInd_refl s : subTermInd s s
| subTermIndExp s x e s' : subTermInd s s' -> subTermInd s (stmtLet x e s')
| subTermIndIf1 e s s' t : subTermInd s s' -> subTermInd s (stmtIf e s' t)
| subTermIndIf2 e s t t' : subTermInd t t' -> subTermInd t (stmtIf e s t')
| subTermIndLet1 F t t' : subTermInd t t' -> subTermInd t (stmtFun F t')
| subTermIndLet2 s Zs F t n : get F n Zs -> subTermInd s (snd Zs) -> subTermInd s (stmtFun F t).

Instance eq_dec_pair A B  `{EqDec A eq} `{EqDec B eq} : EqDec (A*B) eq.
Proof.
  hnf; intros [] []; unfold equiv, complement.
  decide (a = a0); try dec_solve; subst.
  decide (b = b0); try dec_solve; subst.
  left. eauto.
Defined.

Instance eq_dec_pair_inst A B (x y: A*B) `{Computable (fst x = fst y)}
         `{Computable (snd x = snd y)} : Computable (x = y).
Proof.
  destruct x,y; simpl in *.
  decide (a = a0); try dec_solve; subst.
  decide (b = b0); try dec_solve; subst.
  left. eauto.
Defined.

Ltac decide_tac_rec P :=
  first [ destruct (@decision_procedure P _)
        | let X := fresh "C" in
          first [ assert (X:Computable(P))
                  by eauto 20 using get with typeclass_instances;
                  destruct (@decision_procedure P X)
                | let P' := eval symmetry in P in
                      assert (X:Computable(P'))
                    by eauto 20 using get with typeclass_instances;
                                            destruct (@decision_procedure P' X)
                ]
        ].

Tactic Notation "rdecide" constr(P) := decide_tac_rec P.

Ltac eq_decide :=
    match goal with
  | [ |- {?f ?a ?b ?c = ?f ?a' ?b' ?c'} + {?f ?a ?b ?c <> ?f ?a' ?b' ?c'} ]
    => try rdecide (a = a'); try rdecide (b = b'); try rdecide (c = c'); subst;
        try dec_solve
  | [ |- {?f ?a ?b = ?f ?a' ?b'} + {?f ?a ?b <> ?f ?a' ?b'} ]
    => try rdecide (a = a'); try rdecide (b = b'); subst; try dec_solve
  | [ |- {?f ?a = ?f ?a'} + {?f ?a <> ?f ?a'} ]
    => try rdecide (a = a'); subst; try dec_solve
  end.


Instance list_equal_computable X
  : forall (L L':list X), (forall n x x', get L n x -> get L' n x' -> Computable (x = x'))
                     -> Computable (eq L L').
Proof.
  intros. decide (length L = length L').
  - general induction L; destruct L'; isabsurd; try dec_solve.
    rdecide (a = x); try dec_solve.
    edestruct IHL with (L':=L'); eauto using get; subst; try dec_solve.
  - right; intro; subst. eauto.
Qed.

Instance stmt_eq_dec (s t:stmt) : Computable (s = t).
  revert t; sind s; intros;
    destruct s, t; try dec_solve; hnf; try eq_decide.
Qed.

Instance exists_in_set_computable X (L:list X) (P:X->Prop)
         `{forall n x, get L n x -> Computable (P x)}
  : Computable (exists n x, get L n x /\ P x).
Proof.
  general induction L.
  - dec_solve.
  - rdecide (P a).
    + left. eauto using get.
    + edestruct IHL; dcr; eauto using get.
      * left. dcr. do 2 eauto using get.
      * right. intro. dcr. inv H1; eauto.
Qed.


Lemma subTermInd_dec s t : Computable (subTermInd s t).
Proof.
  revert s.
  sind t; intros; decide (s = t); subst; try dec_solve; destruct t; simpl in *.
  - edestruct (IH t); eauto; dec_solve.
  - edestruct (IH t1); eauto; try dec_solve.
    edestruct (IH t2); eauto; try dec_solve.
  - dec_solve.
  - dec_solve.
  - rdecide (subTermInd s t); try dec_solve.
    rdecide (exists n x, get F n x /\ subTermInd s (snd x)).
    + left. destruct e as [? [? ?]]; dcr.
      eauto using subTermInd.
    + right. intro A; inv A; eauto.
Qed.


Instance subTermInd_refl' : Reflexive subTermInd.
Proof.
  hnf; intros. eapply subTermInd_refl.
Qed.

Instance subTermInd_trans : Transitive subTermInd.
Proof.
  hnf; intros s t u ST1 ST2.
  general induction ST1; eauto;
  general induction ST2; eauto using subTermInd.
Qed.

Lemma subTermInd_occurVars s t
  : subTermInd s t
    -> occurVars s ⊆ occurVars t.
Proof.
  intros. general induction H; simpl; eauto with cset.
  - eapply incl_union_left.
    eapply incl_list_union. eapply map_get_1; eauto.
    eauto with cset.
Qed.

Lemma subTermIndF_occurVars F t sT
  : subTermInd (stmtFun F t) sT
    -> list_union (of_list ⊝ fst ⊝ F) ⊆ occurVars sT.
Proof.
  intros. general induction H; simpl.
  - eapply list_union_incl; intros; eauto with cset.
    inv_get.
    rewrite <- incl_list_union; eauto using map_get_1.
    cset_tac. cset_tac.
  - rewrite IHsubTermInd; eauto. cset_tac.
  - rewrite IHsubTermInd; eauto. cset_tac.
  - rewrite IHsubTermInd; eauto. cset_tac.
  - rewrite IHsubTermInd; eauto.
  - rewrite IHsubTermInd; eauto.
    rewrite <- incl_list_union; eauto using map_get_1.
    instantiate (1:=occurVars (snd Zs)). cset_tac. cset_tac.
Qed.

Definition subTerm (s t:stmt) := sumbool_bool (subTermInd_dec s t) = true.

Require Import Coq.Logic.Eqdep_dec.

Lemma subTerm_PI s t (p1 p2:subTerm s t)
  : p1 = p2.
Proof.
  unfold subTerm in *.
  eapply dec_UIP.
  eapply bool_eqdec.
Qed.

Lemma sTI_sT s sT
  : (sumbool_bool (subTermInd_dec s sT) = true) <-> subTermInd s sT.
Proof.
  split; intros.
  - destruct (subTermInd_dec s sT); eauto; isabsurd.
  - destruct (subTermInd_dec s sT); eauto; isabsurd.
Qed.

Ltac sTE :=  unfold subTerm in *; rewrite sTI_sT in *.

Lemma subTerm_EQ_Let sT st x e s
  (EQ:st = stmtLet x e s)
  (ST:subTerm st sT)
  : subTerm s sT.
Proof.
  subst st; sTE.
  etransitivity; eauto. econstructor; reflexivity.
Qed.

Lemma subTerm_EQ_If1 sT st x s t
  (EQ:st = stmtIf x s t)
  (ST:subTerm st sT)
  : subTerm s sT.
Proof.
  subst st; sTE; etransitivity; eauto. econstructor; reflexivity.
Qed.

Lemma subTerm_EQ_If2 sT st x s t
  (EQ:st = stmtIf x s t)
  (ST:subTerm st sT)
  : subTerm t sT.
Proof.
  subst st; sTE; etransitivity; eauto. econstructor; reflexivity.
Qed.

Lemma subTerm_EQ_Fun1 sT st F t
  (EQ:st = stmtFun F t)
  (ST:subTerm st sT)
  : subTerm t sT.
Proof.
  intros. sTE. subst. etransitivity; eauto.
  eapply subTermIndLet1; eauto. reflexivity.
Qed.

Lemma subTerm_EQ_Fun2 sT st F t
  (EQ:st = stmtFun F t)
  (ST:subTerm st sT)
  : forall (n : nat) (s : params * stmt), get F n s -> subTerm (snd s) sT.
Proof.
  intros. sTE. subst. etransitivity; eauto.
  eapply subTermIndLet2; eauto. reflexivity.
Qed.

Lemma subTerm_occurVars s t
  : subTerm s t
    -> occurVars s ⊆ occurVars t.
Proof.
  intros. sTE.
  eapply subTermInd_occurVars; eauto.
Qed.

Lemma subTerm_refl s
  : subTerm s s.
Proof.
  sTE. econstructor.
Qed.

Lemma subTermF_occurVars F t sT
  : subTerm (stmtFun F t) sT
    -> list_union (of_list ⊝ fst ⊝ F) ⊆ occurVars sT.
Proof.
  sTE. intros.
  eapply subTermIndF_occurVars; eauto.
Qed.
