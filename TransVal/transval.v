Require Import List.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh sexp smt nofun.

(** TODO: Add constraint that s' must be an expression or a function call **)
Lemma models_if_eval :
forall s D E s' E' F, 
ssa  s D
-> noFun s
-> noFun s'
-> star2 step (nil, E,s) nil (nil, E',s')
(*-> s' = f e \/ s' = e *)
->  models F  E'  (translateStmt s source).

Proof.
intros.
general induction H2.
- general induction s'; simpl.
  + destruct (translateExp e). (* case distinction over wether the exp is translatable or not, maybe induction over exp here *)
    *  destruct (undef s); simpl.  (* case eq wether the expression contains undefined behavior or not , this case follows from induction over exp*)
       {  (* Assumption is now: guard expression can be modelled /\ the values of the constraint are equal /\ by induction the rest can be modeled *)
         admit. }
       { (* Same assumption as before, but no guard expression *)
         admit. }
    * (*the expression could not be translated --> lemma needed for this case that either it cannot occur or that we can get a proof of false from this *)
      admit.
  + destruct (translateExp e). (* same as before *)
    * destruct (undef s); simpl. (* same as before *)
      { (*same as before, additional lemma needed that: then branch in IL <-> then branch in SMT and same for else *)
        admit. }
      { (* and the same  again *) 
      admit. }
    * (* same case as + before *)
      admit.
  + destruct (translateArgs Y). (* case eq wether the arglist can be translatet --> should go through with lemma *)
    * (* special case: function call in IL/F where we do not know what it will return. Is there a Lemma needed for this, what about the guarding list?
           the list should be handleable with the lemma about guard expressions *)
      admit.
    * (* same case as + before *)
      admit.
  + (* TODO: Add the return function to the predicate list and evaluate it here, then the case becomes a copy of the one before *)
    admit.
  + inversion H1. 
  + inversion H1.
- (* induction case. I believe that it is necessary here, to have a stronger evaluation/ simulation relation for the IL/F program. It should be able to give information that
       the program was evaluated to a cf join point (f e or e) *)
  general induction s; simpl. (* every induction case works analog to the non inductive cases before as we can get the result from the IH *)
  + admit.
  + admit.
  + admit.
  + admit.
  + inversion  H1.
  + inversion H1.
Qed.
       

general induction s'; simpl.
  + general induction e.
     * simpl. destruct (E' x). (*TODO: Add assumption that every value is defined *)
       { split.
         -  destruct (bitvec.bvEq b v); simpl. (* Broken Case due to the fact of the value definition assumption lacking *) admit.
         destruct b0.
         + destruct (bitvec.bvToBool l).
           * econstructor.
           * (* Contradiction to ?? *) exfalso. admit.
         + econstructor.
         - apply (IHs' D E' F).
           + inversion H1. assumption.
           + inversion H. rewrite H6. (* TODO: Construct ssa from assumptions *) admit.
             }
     { split.
       - (* TODO Does not work *) admit.
       - apply (IHs' D E' F).
         + inversion H1; assumption.
         + inversion H.  admit. (* see case before *)
     }
       * destruct (translateExp (Var v)); simpl.  (* TODO: Same assumption as last case *)
         {  destruct (undef s).
            - simpl.
  +  destruct (E' x).
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