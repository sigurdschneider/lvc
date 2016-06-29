Require Import List Map Env AllInRel Exp MoreExp.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI.


(* TODO: Read IL/Annotation.v which defines annotations for programs
         and figure out which type X to choose such that ann X is
         the type of spilling annotations. *)

(* TODO: define the algorithm that takes a program and a spilling
         annotation and produces the spilled program
         assume a function [slot : var -> var] that yields the spill
         slot for a given variable *)
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

(* TODO: read Liveness.v and figure out the type of the correctness
         predicate for spilling *)
Inductive spill_sound : nat -> (list (set var * set var)) -> (set var * set var) -> stmt -> ann (set var * set var) -> Prop :=

| SpillLet k Λ R M Sp L K Kx sl x e s
: spill_sound k Λ ({x;(R\K ∪ L)\Kx }, Sp ∪ M) s sl
  -> Exp.freeVars e ⊆ R\K ∪ L
  -> cardinal (R\K ∪ L) <= k
  -> cardinal ({x;((R\K) ∪ L)\Kx }) <= k
  -> spill_sound k Λ (R,M) (stmtLet x e s) (ann1 (Sp,L) sl)

| SpillReturn k Λ R M Sp L K e
: Exp.freeVars e ⊆ R\K ∪ L
  -> cardinal ((R\K) ∪ L) <= k
  -> spill_sound k Λ (R,M) (stmtReturn e) (ann0 (Sp,L))

| SpillIf k Λ R M Sp L K sl_s sl_t e s t
: Exp.freeVars e ⊆ R\K ∪ L
  -> cardinal (R\K ∪ L) <= k
  -> spill_sound k Λ (R\K ∪ L, Sp ∪ M) s sl_s
  -> spill_sound k Λ (R\K ∪ L, Sp ∪ M) t sl_t
  -> spill_sound k Λ (R,M) (stmtIf e s t) (ann2 (Sp,L) sl_s sl_t)

| SpillApp k Λ R M Sp L K f Y R_f M_f
: cardinal (R\K ∪ L) <= k
  -> get Λ (counted f) (R_f,M_f)
  -> R_f ⊆ R\K ∪ L
  -> M_f ⊆ Sp ∪ M
    -> spill_sound k Λ (R,M) (stmtApp f Y) (ann0 (Sp,L))

| SpillFun k Λ R M Sp L K s t sl_s sl_t Z
: cardinal (R\K ∪ L) <= k
  -> spill_sound k (getAnn sl_s::Λ) (getAnn sl_s) s sl_s 
  -> spill_sound k (getAnn sl_s::Λ) (R\K ∪ L, M ∪ Sp) t sl_t
    -> spill_sound k Λ (R,M) (stmtFun ((Z,s)::nil) t)
                   (annF (Sp,L) (sl_s::nil) sl_t)
.

Inductive fv_e_bounded : nat -> stmt -> Prop :=

| BoundLet k x e s
: cardinal (Exp.freeVars e) <= k
  -> fv_e_bounded k s
  -> fv_e_bounded k (stmtLet x e s)

| BoundReturn k e
: cardinal (Exp.freeVars e) <= k
  -> fv_e_bounded k (stmtReturn e)

| BoundIf k e s t
: cardinal (Exp.freeVars e) <= k
  -> fv_e_bounded k s
  -> fv_e_bounded k t
  -> fv_e_bounded k (stmtIf e s t)

| BoundApp k f Y
: fv_e_bounded k (stmtApp f Y)

| BoundFun k Z s t 
: fv_e_bounded k (stmtFun ((Z,s)::nil) t)
.

Fixpoint stupSpill (R : set var) (s : stmt) : ann (set var * set var) := 
match s with
| stmtLet x e t => ann1 (R, Exp.freeVars e)
                        (stupSpill (singleton x) t)
| stmtReturn e => ann0 (R, Exp.freeVars e)
| stmtIf e t v => ann2 (R, Exp.freeVars e)
                       (stupSpill ∅ t) 
                       (stupSpill ∅ v)
| stmtApp f Y => ann0 (R, ∅)
| stmtFun ((Z,t)::nil) v => annF (R, ∅) (stupSpill ∅ t::nil) (stupSpill ∅ v)
| _ => ann0 (∅,∅)
end.




Lemma stupSpill_sat_spillSound (k:nat) (s:stmt) (R R' M : set var) Λ Lv ZL alv :
k > 0
-> freeVars s ⊆ R' ∪ M
-> R' ⊆ R
-> fv_e_bounded k s
-> live_sound Imperative ZL Lv s alv
-> getAnn alv ⊆ R' ∪ M 
-> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ (Lv \\ ZL)
-> spill_sound k Λ (R,M) s (stupSpill R' s).

Proof.
  intros knotzero subs.
  general induction s; invt fv_e_bounded; invt live_sound; simpl in *.
   - simpl. eapply SpillLet with (K := R)(Kx := Exp.freeVars e).
     + eapply IHs; eauto.
       * rewrite <- subs. clear_all. cset_tac. decide (x === a); eauto. 
       * clear_all. eauto with cset.
       * rewrite <- H2. clear - H14. cset_tac. decide (x === a); eauto with cset.
           right. assert (forall y, y ∈ (getAnn al \ singleton x) -> y ∈ lv); 
                eauto with cset.
           eapply H0. cset_tac.
     + eauto with cset.
     + assert (R \ R ∪ Exp.freeVars e [=] Exp.freeVars e). 
       * cset_tac.
       * rewrite H4. auto.
     + assert ({x; R \ R ∪ Exp.freeVars e \ Exp.freeVars e} [=] singleton x).
       * clear_all. cset_tac. 
       * rewrite H4. rewrite singleton_cardinal. auto.
   - eapply SpillIf with (K := R). 
     + eauto with cset.
     + assert (R \ R ∪ Exp.freeVars e [=] Exp.freeVars e). cset_tac.
       rewrite H4. auto.
     + eapply IHs1; eauto with cset.
       rewrite <- subs. clear_all. cset_tac.
     + eapply IHs2; eauto with cset.
       rewrite <- subs. clear_all. cset_tac.
   - assert (get (Lv \\ ZL) (labN l) (blv \ of_list Z)).
     + eapply zip_get_eq; eauto.
     + PIR2_inv. destruct x as [R_f M_f]; simpl in *.
       eapply SpillApp with (K := R); eauto.
       * assert (R\R ∪ ∅ [=] ∅) as empty. 
           clear_all. cset_tac. 
           rewrite empty. rewrite empty_cardinal. omega.
       * rewrite H10. eauto with cset.
       * rewrite H12. rewrite H8. eauto.
   - eapply SpillReturn with (K := R).
     + eauto with cset.
     + assert (R \ R ∪ Exp.freeVars e [=] Exp.freeVars e).
       * cset_tac.
       * rewrite H4. auto.
   - eapply SpillFun with (K := R); simpl in *.
     + assert (R\R ∪ ∅ [=] ∅) as empty. 
       * clear_all. cset_tac. 
       * rewrite empty. rewrite empty_cardinal. omega.
     + admit.
     + admit.    

Qed.



Theorem spill_sound_correct L E E' : spill_sound k Lsl (R,M) s alv asl
-> (forall x : var, In x R -> E x = E' x)
-> (forall x : var, In x S -> E x = E' (slot x))
-> bisim (L,E,s) (L,E', doSpill slot s asl).


(* TODO: define spilling predicate similarily to the liveness predicate
         in Liveness.v *)
