Require Import List.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh sexp smt nofun terminates Subsmt.

Definition lift_env (E:onv val)  :=
fun x => match E x with 
|Some v => v
| _ => default_val
end.

(*
 Lemma guard_truet_if_eval:
forall F E e x s v,  translateExp e = Some x -> undef x = Some s -> exp_eval E e = Some v ->  models F (lift_env E) s.

Proof.
intros. general induction e; simpl in *.
- destruct u.
  + destruct( translateExp e).
    * inversion H. rewrite <- H3 in H0.  case_eq (exp_eval E e); intros.
      {  eapply IHe; eauto. }
      { eapply IHe; eauto. *)

Lemma models_if_eval :
forall s D E s' E', 
ssa  s D
-> (forall x, x ∈ snd (getAnn D) ->E x <> None)
-> (forall e, exists v, translateExp e = ⎣v⎦)
-> noFun s 
-> terminates (nil,E, s) (nil, E', s')
-> exists F, models F  (lift_env E')  (translateStmt s source).

Proof.
intros.
(* inversion F.step *)
general induction H2; simpl.
- exists (fun (f:pred) (x:vallst)=> true). 
   destruct (H1 e).  rewrite H4. case_eq (undef x0); intros.
   + simpl. split.
     * general induction e; simpl in *. 
       { destruct u.  
         - destruct (H1 e). rewrite H6 in H4.  inversion H4. rewrite <- H8 in H5. simpl in *.  eapply IHe; eauto.  
           + inversion H. econstructor; eauto. 
           + inversion H3. econstructor; eauto. inversion H6.   general induction e.
       { simpl in *.  destruct (H1 e).  rewrite H6 in *.  destruct u. 
        -  inversion H4. rewrite <- H8 in H5. simpl in H5.  specialize (IHe x s H2 IHnoFun D E s' E' ). eapply IHe; eauto.
           + inversion H. econstructor; eauto.
           + inversion H3. econstructor; eauto. inversion H7. 
}
     * split.
       { inversion H. inversion H3. inversion H14.
         assert (X: ⎣evalSexp (lift_env E'') x0⎦ = exp_eval E e).
         - rewrite def. f_equal. unfold lift_env. 
         assert ((lift_env E'' x) = exp_eval E x).
  pose (E' := fun x => match E x with | Some v => v | None => default_val end).
  + exists E'. simpl; split; eauto. unfold E'. rewrite H0.

  destruct (undef x).
  + apply (guard_ret_sat_if_terminates F E E' e x); simpl; eauto.
    * econstructor.
    * rewrite H3.  
  assert (A: forall E s E' s', terminates E s E' s' -> undef x =  ) by admit.  
  rewrite (A E (stmtReturn e) E (stmtReturn e)). 
  + exists (fun x => match E x with |Some v => v | None => default_val end); simpl. econstructor.
  + econstructor. 
-  destruct (H2 e). rewrite H3. 
   assert (A: forall E s E' s' x, terminates E s E' s' -> guardList source x (funcApp f x) = funcApp f x) by admit. 
  rewrite (A E (stmtGoto f e) E (stmtGoto f e)).
  + exists (fun x => match E x with |Some v => v | None => default_val end); simpl. admit.
  + econstructor. 
- destruct (H4 c). rewrite H6. 
    assert (A: undef x = ⎣⎦ ) by admit.  
    rewrite A. simpl. exists (fun x => match E x with |Some v => v |None => default_val end); simpl.
    (* TODO: Ersetze überall evalSexp mit exp_eval ?? *)  admit.
- (* analog zu vorher *) admit.
- destruct (H2 e). rewrite H. assert (A: undef x0 = None) by admit. rewrite A. 
  exists (fun x => match E'  x with | Some v => v |None => default_val end). simpl. split.
  + (* Jetzt muss mit ssa konstruiert werden, dass E' x nun genau den Wert hat den evalSexp E e gibt. *)
    assert (B: E' x =  exp_eval E e) by admit.
    rewrite B. destruct  (H1 e). rewrite H5. 
    admit.
  +  inv H0.  
     assert (C: forall e0, exists v, exp_eval (E[x <- exp_eval E e]) e0 = Some v) by admit.
     specialize (IHterminates an F H11 C H2 H4). 
     destruct IHterminates.
     assert (D: x1 = (fun x2 => match E' x2 with | Some v => v |None => default_val end)) by admit.
     rewrite D in H5. assumption.
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
