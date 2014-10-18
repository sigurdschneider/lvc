Require Import List.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh sexp smt nofun terminates Subsmt.

(*
Axiom always_true:
forall s F f x e, (~ subsmt (smtNeg (funcApp f x) ) s) -> evalSpred F f e = true.

Lemma not_occur_neg_call:
forall s f e,   ~ subsmt (smtNeg (funcApp f e)) (translateStmt s source).

Proof.
intros.  general induction s; simpl.
- hnf. intros. apply (IHs  f e0). destruct (translateExp e).
  +  destruct (undef s0).
     *  inversion H.
        { econstructor. exfalso. discriminate H0. }
        { destruct H2.
          -
  + reflexivity.
  + destruct (translateExp e).
    * destruct (undef s0).
      { inversion H.
        - econstructor.
*)

Lemma models_if_eval :
forall s D E s' E' F, 
ssa  s D
(* -> noFun s *)
(* -> noFun s' *)
-> (forall e, exists v, exp_eval E e = Some v)
-> (forall e, exists v, translateExp e = Some v)
-> (forall l, exists arg, translateArgs l = Some arg)
-> terminates E s E' s'
-> exists E'',  models F  E''  (translateStmt s source).

Proof.
intros.
general induction H3; simpl.
- destruct (H1 e). rewrite H3. 
  assert (A: forall E s E' s', terminates E s E' s' -> undef x = ⎣⎦ ) by admit.  
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