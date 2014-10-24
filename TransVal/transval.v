Require Import List.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh sexp smt nofun terminates bitvec.

Lemma bvEq_equiv_eq:
forall b1 b2, toBool(bvEq b1 b2) <-> eq b1 b2.

Proof.
intros; split; intros.
- general induction b1; destruct b2.
  + reflexivity.
  + simpl in H. exfalso; assumption.
  + simpl in H. exfalso; assumption.
  + destruct a,b.
    * simpl. simpl in H. f_equal. eapply IHb1. assumption.
    * simpl in H; exfalso; assumption.
    * simpl in H; exfalso; assumption.
    * f_equal. simpl in H; eapply IHb1; assumption.
- general induction b1.
  + simpl. econstructor.
  + destruct a.
    * simpl. eapply (IHb1 b1). reflexivity.
    * simpl. eapply (IHb1 b1); reflexivity.
Qed.

Lemma not_zero:
 forall b, bvZero b = false ->  b  <> zext k (O::nil).

Proof.
 intros. general induction b.
 destruct a; simpl; hnf; intros. 
 - rewrite H0 in H. simpl in H. discriminate H.
- rewrite H0 in H.  simpl in H; discriminate H.
Qed.
 
Lemma zext_nil_eq_sext:
  forall k, sext k nil O = zext k nil.

Proof.
  intros; general induction k.
  - simpl. reflexivity.
  - simpl. f_equal; eauto; assumption.
Qed.

Lemma bvEq_eq_refl:
forall a, val2bool (bvEq a a) = true.

Proof.
intros; general induction a.
- eauto.
- simpl. rewrite IHa in *. destruct a; simpl; rewrite IHa; reflexivity.
Qed.

Lemma not_zero_implies_uneq:
forall a b, bvZero a = false ->b = zext k (O::nil) ->  val2bool(bvEq a b) = false.

Proof. 
intros.  induction a.
- simpl.  rewrite H0. reflexivity.
- destruct a. 
  + simpl in H. specialize (IHa H).  admit.
  + simpl in H. rewrite H0. simpl. reflexivity.
Qed.

 Lemma guard_true_if_eval:
forall F E e s v,  
 (*translateExp e = Some x  *)
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
              {  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0.   unfold binop_eval in EQ2.  clear H0. unfold bvDiv in EQ2. simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2. 
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0.  rewrite EQ1 in H0.  simpl in H0. simpl  in A.  
                     erewrite  not_zero_implies_uneq in H0; eauto.   
                 - split.
                   + eapply IHe1; eauto.
                   + eapply IHe2; eauto.  }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. unfold binop_eval in EQ2. clear H0. unfold bvDiv in EQ2. simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2. 
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0. rewrite EQ1 in H0.  simpl in H0. simpl  in A.  
                     erewrite  not_zero_implies_uneq in H0; eauto.   
                 -  eapply IHe1; eauto. }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. unfold binop_eval in EQ2. clear H0. unfold bvDiv in EQ2. simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2. 
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0.  rewrite EQ1 in H0.  simpl in H0. simpl  in A.  
                     erewrite  not_zero_implies_uneq in H0; eauto.   
                 -  eapply IHe2; eauto. }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. unfold binop_eval in EQ2. clear H0. unfold bvDiv in EQ2. simpl.
                   case_eq(bvZero x0).
                   - intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2. 
                   - intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0. rewrite EQ1 in H0.  simpl in H0. simpl  in A.  
                     erewrite  not_zero_implies_uneq in H0; eauto.    }
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
-   case_eq (undef e).
   + simpl; split.
     * eapply (guard_true_if_eval); eauto.
     * econstructor.
   + intros. simpl. econstructor.
- inversion H. 
  + simpl. case_eq (undef e); intros; simpl; split.
    *  eapply(guard_true_if_eval (fun (_:pred) (_:vallst) => true) E' e s0 v); eauto.  assert (freeVars e ⊆ (fst (getAnn D))).
      {  rewrite <- H7 in H0. inversion H0. simpl.  assumption. }
      { eapply (exp_eval_agree (E:= E)); eauto.  cset_tac. hnf in H1. hnf in H10. hnf. intros. specialize (H1 x0). specialize (H10 x0). exact (H1 (H10 H4)). }
    * split; simpl.
      {  unfold evalSexp.  
         assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).  
         eapply (exp_eval_agree (E:=E) (E' := E')) in def.
         - rewrite def.  simpl. (* Wert aus E' für x konstruieren *) admit.
         - cset_tac. hnf; hnf in H1; hnf in H10. hnf; intros; specialize(H1 x0); specialize (H10 x0); exact (H1 (H10 H4)).  }
      { rewrite <- H7 in H0.  inversion H0.  eapply (IHterminates b an); eauto.
        - admit.
        - rewrite <-  H7 in H3. inversion H3.  assumption. }
    * unfold evalSexp.
      assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).  
      eapply (exp_eval_agree (E:=E) (E' := E')) in def.
      { rewrite def.  simpl. (* Wert aus E' für x konstruieren *) admit. }
      { cset_tac. hnf; hnf in H1; hnf in H10. hnf; intros; specialize(H1 x0); specialize (H10 x0); exact (H1 (H10 H4)). }
    *  rewrite <- H7 in H0.  inversion H0.  eapply (IHterminates b an); eauto.
       { admit. }
       { rewrite <-  H7 in H3. inversion H3.  assumption. }
  + simpl.
    assert (X: models (fun (_: pred) (_ : vallst) => true) E' (ite e (translateStmt b1 source) (translateStmt b2 source))). 
    * simpl.
      assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).
      assert (agree_on eq (freeVars e) E E').
      { cset_tac. hnf. hnf in H1; hnf in H9; hnf; intros; specialize(H1 x); specialize (H9 x); exact (H1 (H9 H4)). }
      { eapply (exp_eval_agree (E:=E) (E' := E') ) in def; eauto. unfold evalSexp. rewrite def. rewrite condTrue. admit. }
    * admit.
  + admit. 
  + simpl. admit.
  + rewrite <-  H7 in H3. exfalso. inversion H3.
  + rewrite <- H7 in H3. exfalso. inversion H3.
Qed.

Definition smtCheck (s:stmt) (t:stmt) :=
smtAnd (translateStmt s source) (translateStmt t target).

(** TODO: Why doesn't this work? **)
Fixpoint agreeOnList (E:senv) (XL:list var) (YL:list var):=
match XL, YL with
|nil , nil => True
| nil, _ => False
| _, nil => False
| a::XL', b::YL' => match E a, E b with
                        | Some v1, Some v2 => v1 = v2 /\ (agreeOnList E XL' YL')
                        | None, None =>  (agreeOnList E XL' YL')
                        | _,_ => False
                    end.

(** TODO: Add constraint that XL and YL are the lists of the output variables of the corresponding programs **)
Lemma not_smtCheck_entails_sat:
forall s t E XL YL,
~ (models E (smtCheck s t))
-> (forall p V,  models V (translateStmt s p) -> models V (translateStmt s p))
-> agree_on E XL YL.

Proof.
admit.
Qed.

(** TODO: make lemma definition work and add constraints **)
Lemma unsat_is_semeq :
forall s t s' t' E E1 E2 x y,
(star2 step (nil, E , s) nil (nil, E1, s'))
-> (star2 step (nil, E, t) nil (nil, E2, t'))
-> E1 x = E2 y.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
