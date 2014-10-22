Require Import List.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh sexp smt nofun terminates Subsmt.

Definition lift_env (E:onv val)  :=
fun x => match E x with 
|Some v => v
| _ => default_val
end.

(*
Lemma evals_impl_subexp_eval:
forall E e o e1 e2 v ,
e = BinOp o e1 e2
-> exp_eval E e = Some v
-> exists v1 v2, exp_eval E e1 = Some v1/\ exp_eval E e2 = Some v2.

Proof.
intros. rewrite H in H0. simpl in H0.  case_eq (exp_eval E e1); case_eq (exp_eval E e2); intros.
- exists v1; exists v0; eauto.
-  rewrite H2 in H0. rewrite H1 in H0. simpl in H0. exfalso; discriminate H0.
-  *)

 Lemma guard_true_if_eval:
forall F E e x s v,  
 translateExp e = Some x 
-> undef x = Some s 
->  exp_eval E e = Some v 
->  models F (lift_env E) s.

Proof.
intros. general induction e; simpl in *.
-  destruct u.
  + destruct( translateExp e).
    * inversion H. rewrite <- H3 in H0. monad_inv H1. simpl in H0.  eapply IHe; eauto.
    * exfalso; discriminate H.
  + exfalso. discriminate H.
-  monad_inv H1. destruct  (translateExp e1); destruct (translateExp e2).
   + destruct b. 
     * inversion H. rewrite <- H2 in H0.  simpl in H0.  case_eq (undef s0); case_eq (undef s1); intros; simpl.
       { unfold combine in H0.   rewrite H1 in H0; rewrite H3 in H0. inversion H0; simpl; split.
         - eapply IHe1; eauto.
         - eapply IHe2; eauto.
       }
       { unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. eapply IHe1; eauto. rewrite <- H5; eauto. }
       { unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. eapply IHe2; eauto. rewrite <- H5; eauto. }
       { unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. }
     *  destruct b.
        { inversion H; rewrite <- H2 in H0. simpl in H0; case_eq(undef s0); case_eq (undef s1); intros; simpl.
          - unfold combine in H0. rewrite H1 in H0; rewrite H3 in H0. inversion H0; simpl; split.
            + eapply IHe1; eauto.
            + eapply IHe2; eauto.
          - unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. eapply IHe1; eauto. rewrite <- H5; eauto. 
          - unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. eapply IHe2; eauto. rewrite <- H5; eauto. 
          - unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. 
        }
        { destruct b. 
          -  inversion H; rewrite <- H2 in H0. simpl in H0; case_eq(undef s0); case_eq (undef s1); intros; simpl.
             + unfold combine in H0. rewrite H1 in H0; rewrite H3 in H0. inversion H0; simpl; split.
               * eapply IHe1; eauto.
               * eapply IHe2; eauto.
             + unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. eapply IHe1; eauto. rewrite <- H5; eauto. 
             + unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. eapply IHe2; eauto. rewrite <- H5; eauto. 
             + unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. 
          - destruct b.
            + inversion H; rewrite <- H2 in H0. simpl in H0; case_eq(undef s0); case_eq (undef s1); intros; simpl.
              * unfold combine in H0. rewrite H1 in H0; rewrite H3 in H0. inversion H0; simpl; split.
              {  eapply IHe1; eauto. }
              { eapply IHe2; eauto. }
              * unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. eapply IHe1; eauto. rewrite <- H5; eauto. 
              * unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. eapply IHe2; eauto. rewrite <- H5; eauto. 
              * unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. 
            + destruct b.
              * inversion H; rewrite <- H2 in H0. simpl in H0; case_eq(undef s0); case_eq (undef s1); intros; simpl.
                { unfold combine in H0. rewrite H1 in H0; rewrite H3 in H0. inversion H0; simpl; split. 
                  - eapply IHe1; eauto.
                  - eapply IHe2; eauto. }
                { unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. eapply IHe1; eauto. rewrite <- H5; eauto. }
                { unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. eapply IHe2; eauto. rewrite <- H5; eauto. }
                { unfold combine in H0; rewrite H1 in H0; rewrite H3 in H0; inversion H0. }
              * exfalso; discriminate H.
          }
   + exfalso; discriminate H.
   + exfalso; discriminate H.
   + exfalso; discriminate H.
Qed.

Lemma models_if_eval :
forall s D E s' E', 
ssa  s D
-> (forall x, x ∈ fst (getAnn D) -> E x <> None)
-> (forall e, exists v, translateExp e = ⎣v⎦)
-> noFun s 
-> terminates (nil,E, s) (nil, E', s')
->  models (fun (f:pred) (x:vallst) => true)  (lift_env E')  (translateStmt s source).

Proof.
intros.
general induction H3; simpl. (*pose (F := (fun (f:pred) (x:vallst)=> true)); exists F.*)
-  rewrite H.   case_eq (undef b); intros; simpl; eauto. 
         + split; eauto. eapply (guard_true_if_eval); eauto.
- case_eq (s); intros; simpl. 
  + simpl.  destruct (H2 e).  rewrite H6.  case_eq (undef x0); intros; simpl; split.
    *  rewrite H5 in H. rewrite H5 in H0.  eapply(guard_true_if_eval); eauto.
    * split.
      {  unfold lift_env.  inversion }
      { eapply IHterminates; eauto.
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
