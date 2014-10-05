Require Import List Specif.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh sexp smt.

Definition wrapEnv E :=
fun (x:var) =>
 match E x with
|Some v => Some (natToBitvec v)
|None => None
end.

(** TODO: Add constraint that s' must be an expression or a function call **)
Lemma models_if_eval :
forall s D E s' E' , 
ssa  s D
-> star2 step (nil, E,s) nil (nil, E',s')
-> forall p, models (wrapEnv E)  (translateStmt s p).

Proof.
admit.
Qed.

Definition smtCheck (s:stmt) (t:stmt) :=
smtAnd (translateStmt s source) (translateStmt t target).

(** TODO: Why doesn't this work? **)
Fixpoint agreeOnList (E:senv) (XL:list var) (YL:list var):=
True.
(*
match XL, YL with
|nil , nil => True
| nil, _ => False
| _, nil => False
| a::XL', b::YL' => match E a, E b with
                        | Some v1, Some v2 => v1 = v2 /\ (agreeOnList E XL' YL')
                        | None, None =>  (agreeOnList E XL' YL')
                        | _,_ => False
                    end
end. *)

(** TODO: Add constraint that XL and YL are the lists of the output variables of the corresponding programs **)
Lemma not_smtCheck_entails_sat:
forall s t E XL YL,
~ (models E (smtCheck s t))
-> (forall p V,  models V (translateStmt s p) -> models V (translateStmt s p))
-> agreeOnList E XL YL.

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