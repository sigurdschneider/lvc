Require Import List.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh sexp smt nofun terminates bitvec OutVars.

Lemma ssa_impl_eq_val:
forall x (e:exp) s E E' s' D v,
terminates (nil, E, stmtExp x e s) (nil, E', s')
->ssa (stmtExp x e s) D
-> exp_eval E e = Some v
-> E' x = Some v.

Proof.
admit.
(*intros. general induction s. 
inversion H. inversion H2. rewrite <-  H12 in *. clear H12.
- unfold update. rewrite H1 in def. rewrite def. decide (x===x).
  + reflexivity.
  + exfalso; eapply n; reflexivity.
- *)

Lemma zext_nil_eq_O:
forall k, zext k nil = zext k (O::nil).

Proof.
induction k.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Lemma minus_n_0: forall n, n-0 = n.

Proof.
intros; general induction n; eauto.
Qed.

Lemma not_zero_implies_uneq:
forall a b k, bvZero a = false ->b = zext k (O::nil) ->  val2bool(bvEq a b) -> False.

Proof. 
intros. general induction a.
-  destruct a.
   + specialize (IHa (tl (zext k (O::nil))) (k-1)).   simpl in H. specialize (IHa H).  eapply IHa.
     * destruct k; eauto.
       simpl. rewrite zext_nil_eq_O.   erewrite minus_n_0. reflexivity. 
     * destruct k; eauto. simpl in H1.  exfalso. assumption. 
   +  simpl in H1.destruct k;  assumption. 
Qed.

 Lemma guard_true_if_eval:
forall F E e s v,  
 exp_eval E e = Some v 
->  undef e = Some s 
->  models F E s.

Proof.
intros. general induction e; simpl.
- simpl in *. monad_inv H. destruct u.
  + apply (IHe F E s x); eauto.
  + destruct u.
    *  apply (IHe F E s x); eauto. 
    * exfalso; discriminate H0.
- simpl in H.  monad_inv H.  simpl in H0. destruct b.
  +  case_eq (undef e1); case_eq (undef e2); intros.
     *  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0. simpl; split.
        { eapply IHe1; eauto. }
        { eapply IHe2; eauto. }
     * rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe1; eauto. rewrite <- H0; eauto.
     *rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe2; eauto. rewrite <- H0; eauto.
     * rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl. exfalso; discriminate H0.
  + destruct b.
    *  case_eq (undef e1); case_eq (undef e2); intros.
     {  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0. simpl; split.
        - eapply IHe1; eauto. 
        - eapply IHe2; eauto. }
     { rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe1; eauto. rewrite <- H0; eauto. }
     { rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe2; eauto. rewrite <- H0; eauto. }
     { rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl. exfalso; discriminate H0. }
    * destruct b. 
      { case_eq (undef e1); case_eq (undef e2); intros.
        -  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0. simpl; split.
           + eapply IHe1; eauto. 
           + eapply IHe2; eauto. 
        - rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe1; eauto. rewrite <- H0; eauto.
        - rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe2; eauto. rewrite <- H0; eauto.
        - rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl. exfalso; discriminate H0. }
      { destruct b. 
        -  case_eq (undef e1); case_eq (undef e2); intros.
           +  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0. simpl; split.
              * eapply IHe1; eauto. 
              * eapply IHe2; eauto. 
           + rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe1; eauto. rewrite <- H0; eauto.
           + rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe2; eauto. rewrite <- H0; eauto.
            +rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl. exfalso; discriminate H0.
        - destruct b.
          +  case_eq (undef e1); case_eq (undef e2); intros.
             *  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0. simpl; split.
                { eapply IHe1; eauto. }
                { eapply IHe2; eauto. }
             * rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe1; eauto. rewrite <- H0; eauto.
             *rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe2; eauto. rewrite <- H0; eauto.
             * rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl. exfalso; discriminate H0.
          + destruct b.
            * case_eq (undef e1); case_eq (undef e2); intros.
              {  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0.  unfold binop_eval in EQ2.  clear H0. unfold bvDiv in EQ2. simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2. 
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0.  rewrite EQ1 in H0.  simpl in H0. simpl  in A.  
                     eapply  (not_zero_implies_uneq _ _  k) in H0;  eauto.   
                 - split.
                   + eapply IHe1; eauto.
                   + eapply IHe2; eauto.  }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. unfold binop_eval in EQ2. clear H0. unfold bvDiv in EQ2. simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2. 
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0. rewrite EQ1 in H0.  simpl in H0. simpl  in A.  
                     eapply ( not_zero_implies_uneq _ _ k) in H0; eauto.   
                 -  eapply IHe1; eauto. }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. unfold binop_eval in EQ2. clear H0. unfold bvDiv in EQ2. simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2. 
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0.  rewrite EQ1 in H0.  simpl in H0. simpl  in A.  
                     eapply  (not_zero_implies_uneq _ _ k) in H0; eauto.   
                 -  eapply IHe2; eauto. }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. unfold binop_eval in EQ2. clear H0. unfold bvDiv in EQ2. simpl.
                   case_eq(bvZero x0).
                   - intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2. 
                   - intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0. rewrite EQ1 in H0.  simpl in H0. simpl  in A.  
                     eapply  (not_zero_implies_uneq _ _ k) in H0; eauto.    }
                 * case_eq (undef e1); case_eq (undef e2); intros; simpl.
                   { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. simpl; split.
                     - eapply IHe1; eauto.
                     - eapply IHe2; eauto. }
                   { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. simpl.
                     - eapply IHe1; eauto. rewrite <- H3. assumption. }
                   { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. simpl.
                     - eapply IHe2; eauto. rewrite <- H3. assumption. }
                   {  rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. }
      }
Qed.

Lemma models_if_eval :
forall s D E s' E', 
ssa  s D
(*-> (forall x, x ∈ fst (getAnn D) -> E x <> None) *)
(*-> (forall e, exists v, translateExp e = ⎣v⎦) *)
-> agree_on eq (fst (getAnn D)) E E'
-> noFun s 
-> terminates (nil,E, s) (nil, E', s')
->  models (fun (f:pred) (x:vallst) => true)  E'  (translateStmt s source).

Proof.
intros.
general induction H2; simpl.
- assert (X: models (fun (_:pred) (_:vallst) => true) E0 (smtReturn e)).
  + simpl. econstructor.
  + case_eq (undef e); eauto.
    * intros. simpl; split; eauto. 
      eapply (guard_true_if_eval); eauto.
- inversion H; simpl.
  + assert (X: models (fun (_:pred) (_:vallst) => true) E' (smtAnd (constr (Var x) e) (translateStmt b source))).
    * split; simpl.
      {  unfold evalSexp.  
         assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).  
         assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H9;  intros; specialize(H1 x0); specialize (H9 x0); exact (H1 (H9 H4))).
         eapply (exp_eval_agree (E:=E) (E' := E')) in def; eauto.
         - rewrite def. rewrite <- H7 in *. clear H7. rewrite <- H8 in *. clear H8.  simpl.
           assert (X1:E' x = Some v).
           + admit.
(*           eapply (agree_on_update_dead (R:=eq) (lv:=freeVars e) (E:=E) (E':=E')(x:=x) (Some v))in H10; eauto. 
           
           assert ( X1: exp_eval E'  (Var x) = Some v). 
           + eapply (exp_eval_agree (E:=E[x <-Some v]) (E':=E')).
             * eapply agree_on_update_dead. hnf.  cset_tac. simpl in H11.  
             * simpl. unfold update. decide (x === x).
               { reflexivity. }
               { exfalso; apply n; reflexivity. } *)
           + rewrite X1.  unfold val2bool. eapply bvEq_equiv_eq. reflexivity. }
      { rewrite <- H7 in *. inversion H0.  inversion H3. eapply IHterminates; eauto.
        - hnf. cset_tac. admit. }
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E' e s0 v); eauto.
          + assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).  
            assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H10;  intros; specialize(H1 x0); specialize (H10 x0); exact (H1 (H10 H4))).
            eapply (exp_eval_agree (E:=E) (E':=E')); eauto.
          }
  + assert (X: models  (fun (_:pred) (_:vallst) => true) E'( ite e (translateStmt b1 source) (translateStmt b2 source))).
    * simpl. unfold evalSexp.   
      assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).  
      assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H9;  intros; specialize(H1 x); specialize (H9 x); exact (H1 (H9 H4))).
      erewrite (exp_eval_agree (E:=E) (E':=E')); eauto. simpl. rewrite condTrue.
      rewrite <- H7 in *.
      inversion H0; inversion H3.
      eapply IHterminates; eauto.
      admit.
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E' e s0 v); eauto.
          + assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).  
            assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H10;  intros; specialize(H1 x); specialize (H10 x); exact (H1 (H10 H4))).
            eapply (exp_eval_agree (E:=E) (E':=E')); eauto.  }
  +  assert (X: models  (fun (_:pred) (_:vallst) => true) E'( ite e (translateStmt b1 source) (translateStmt b2 source))).
    * simpl. unfold evalSexp.   
      assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).  
      assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H9;  intros; specialize(H1 x); specialize (H9 x); exact (H1 (H9 H4))).
      erewrite (exp_eval_agree (E:=E) (E':=E')); eauto. simpl. rewrite condFalse.
      rewrite <- H7 in *.
      inversion H0; inversion H3.
      eapply IHterminates; eauto.
      admit.
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E' e s0 v); eauto.
          + assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).  
            assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H10;  intros; specialize(H1 x); specialize (H10 x); exact (H1 (H10 H4))).
            eapply (exp_eval_agree (E:=E) (E':=E')); eauto.  }
  + general induction Y; intros.
    * simpl. econstructor.
    * admit. (* TODO: Build List Lemma from guard_true_if_eval *)
  + rewrite <-  H7 in H3. exfalso. inversion H3.
  + rewrite <- H7 in H3. exfalso. inversion H3.
Qed.

Definition smtCheck (s:stmt) (t:stmt) :=
smtAnd (translateStmt s source) (translateStmt t target).

(** Checks wether two lists agree on their values. But the environment needs to be defined on every
variable. Otherwise the result is false **)
Fixpoint agreeOnList (E:onv val) (k:nat) XL YL:=
match k with
| 0 => True
| S k' =>  match XL, YL with
             |nil , nil => True
             | nil, _ => False
             | _, nil => False
             | a::XL', b::YL' => match (exp_eval E a), (exp_eval E b) with
                                   | Some v1, Some v2 => v1 = v2 /\ (agreeOnList E k' XL' YL')
                                   | None, None =>  False
                                   | _,_ => False
                                 end
           end
end.

Lemma not_smtCheck_entails_sat:
forall s t F E XL YL,
~ (models F E (smtCheck s t))
-> noFun s
-> noFun t
-> OutVars XL s
-> OutVars YL t
->List.length XL = List.length YL
-> (forall F V,  models F V (translateStmt s source) -> models F V (translateStmt t source))
-> agreeOnList E (List.length XL) XL YL.

Proof.
intros. general induction s.
- general induction t.
  + 
Qed.

Lemma unsat_is_semeq :
forall s t s' t' E E1 E2 XL YL,
terminates (nil, E , s) (nil, E1, s')
-> terminates (nil, E, t) (nil, E2, t')
-> OutVars XL s
-> OutVars YL t
-> noFun s
-> noFun t
-> agreeOnList E (List.length XL) XL YL.

Proof.
admit.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)