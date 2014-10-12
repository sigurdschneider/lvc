Require Import List.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh sexp smt nofun.

(* Definition wrapEnv E :=
fun (x:var) =>
 match E x with
|Some v => Some (natToBitvec v)
|None => None
end. *)

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