Require Import List Map Env AllInRel Exp.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI.

Fixpoint write_spills (slot: var->var) (xs:list var) (s:stmt) : stmt :=
match xs with
| nil => s
| x::xs => stmtLet (slot x) (Var x) (write_spills slot xs s) 
end.

Fixpoint write_loads (slot: var-> var) (xs:list var) (s:stmt) : stmt :=
match xs with
| nil => s
| x::xs => stmtLet x (Var (slot x)) (write_loads slot xs s)
end.


Fixpoint doSpill (slot: var -> var) (s:stmt) (a:ann (set var * set var)) : stmt :=
match s, a with
| stmtLet x e s, ann1 (Sp,L) a =>
    write_spills slot (to_list Sp)
                 (write_loads slot (to_list L) (stmtLet x e (doSpill slot s a)))
| _,_ => s
end.

      
Theorem spill_sound_correct L E E' : spill_sound k Lsl (R,M) s alv asl
-> (forall x : var, In x R -> E x = E' x)
-> (forall x : var, In x S -> E x = E' (slot x))
-> bisim (L,E,s) (L,E', doSpill slot s asl).

