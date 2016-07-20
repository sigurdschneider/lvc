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

| SpillFun k Λ R M Sp L K s t sl_s sl_t Z R_f M_f
: cardinal (R\K ∪ L) <= k
  -> cardinal R_f <= k
  -> R_f ⊆ R\K ∪ Sp ∪ M ∪ of_list Z
  -> M_f ⊆ R\K ∪ Sp ∪ M ∪ of_list Z
  -> spill_sound k ((R_f,M_f)::Λ) (R_f,M_f) s sl_s 
  -> spill_sound k ((R_f,M_f)::Λ) (R\K ∪ L, Sp ∪ M) t sl_t
    -> spill_sound k Λ (R,M) (stmtFun ((Z,s)::nil) t)
                   (annF (Sp,L) (sl_s::nil) sl_t)
.


Inductive spill_sound' : nat -> (list (set var * set var)) -> (set var * set var) -> stmt -> ann (set var * set var * option (set var * set var)) -> Prop :=

| SpillLet' k Λ R M Sp L K Kx sl x e s
: spill_sound' k Λ ({x;(R\K ∪ L)\Kx }, Sp ∪ M) s sl
  -> Exp.freeVars e ⊆ R\K ∪ L
  -> cardinal (R\K ∪ L) <= k
  -> cardinal ({x;((R\K) ∪ L)\Kx }) <= k
  -> spill_sound' k Λ (R,M) (stmtLet x e s) (ann1 (Sp,L,None) sl)

| SpillReturn' k Λ R M Sp L K e
: Exp.freeVars e ⊆ R\K ∪ L
  -> cardinal ((R\K) ∪ L) <= k
  -> spill_sound' k Λ (R,M) (stmtReturn e) (ann0 (Sp,L,None))

| SpillIf' k Λ R M Sp L K sl_s sl_t e s t
: Exp.freeVars e ⊆ R\K ∪ L
  -> cardinal (R\K ∪ L) <= k
  -> spill_sound' k Λ (R\K ∪ L, Sp ∪ M) s sl_s
  -> spill_sound' k Λ (R\K ∪ L, Sp ∪ M) t sl_t
  -> spill_sound' k Λ (R,M) (stmtIf e s t) (ann2 (Sp,L,None) sl_s sl_t)

| SpillApp' k Λ R M Sp L K f Y R_f M_f
: cardinal (R\K ∪ L) <= k
  -> get Λ (counted f) (R_f,M_f)
  -> R_f ⊆ R\K ∪ L
  -> M_f ⊆ Sp ∪ M
    -> spill_sound' k Λ (R,M) (stmtApp f Y) (ann0 (Sp,L,None))

| SpillFun' k Λ R M Sp L K s t sl_s sl_t Z R_f M_f
: cardinal (R\K ∪ L) <= k
  -> cardinal R_f <= k
  -> R_f ⊆ R\K ∪ Sp ∪ M ∪ of_list Z
  -> M_f ⊆ R\K ∪ Sp ∪ M ∪ of_list Z
  -> spill_sound' k ((R_f,M_f)::Λ) (R_f,M_f) s sl_s 
  -> spill_sound' k ((R_f,M_f)::Λ) (R\K ∪ L, Sp ∪ M) t sl_t
    -> spill_sound' k Λ (R,M) (stmtFun ((Z,s)::nil) t)
                   (annF (Sp,L,Some (R_f,M_f)) (sl_s::nil) sl_t)
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
: fv_e_bounded k s
  -> fv_e_bounded k t
  -> fv_e_bounded k (stmtFun ((Z,s)::nil) t)
.

Inductive fns_closed : list (set var * set var) -> set var -> stmt -> Prop := 

| fnsClosedLet Λ X X' x e s
: X [=] X' ∪ singleton x
(*-> Exp.freeVars e ⊆ X*)
-> fns_closed Λ X s
  -> fns_closed Λ X' (stmtLet x e s)

| fnsClosedReturn Λ X e
: (*Exp.freeVars e ⊆ X
  ->*) fns_closed Λ X (stmtReturn e)

| fnsClosedIf Λ X e s t
: (*Exp.freeVars e ⊆ X
->*) fns_closed Λ X s
-> fns_closed Λ X t
  -> fns_closed Λ X (stmtIf e s t)

| fnsClosedApp Λ X f Y R_f M_f
: get Λ (counted f) (R_f,M_f)
(*-> R_f ⊆ X ∪ of_list Y
-> M_f ⊆ X ∪ of_list Y*)
  -> fns_closed Λ X (stmtApp f Y)

| fnsClosedFun Λ X Z s t R_f M_f
: R_f ⊆ X
-> M_f ⊆ X
-> fns_closed ((R_f,M_f)::Λ) X s
-> fns_closed ((R_f,M_f)::Λ) X t
  -> fns_closed Λ X (stmtFun ((Z,s)::nil) t)
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


Fixpoint stupSpill' (R : set var) (s : stmt) (Lv : ann (set var)) : ann (set var * set var * option (set var * set var)) := 
match s,Lv with
| stmtLet x e t, ann1 LV lv => ann1 (R, Exp.freeVars e, None)
                        (stupSpill' (singleton x) t lv)
| stmtReturn e, _ => ann0 (∅, Exp.freeVars e, None)
| stmtIf e t v, ann2 LV lv_s lv_t => ann2 (R, Exp.freeVars e, None)
                       (stupSpill' (Exp.freeVars e) t lv_s) 
                       (stupSpill' (Exp.freeVars e) v lv_t)
| stmtApp f Y, _  => ann0 (R, ∅, None)
| stmtFun ((Z,t)::nil) v, annF LV (lv_t::nil) lv_v  =>
        annF (R, {}, Some ({}, LV)) ((stupSpill' ∅ t lv_t)::nil) 
                                     (stupSpill' ∅ v lv_v)
| _,_ => ann0 (∅, ∅, None)
end.

Lemma union_assoc (X Y Z : set var) : X ∪ (Y ∪ Z) [=] (X ∪ Y) ∪ Z.
Proof.
cset_tac.
Qed.

Lemma stupSpill_sat_spillSound (k:nat) (s:stmt) (R R' M : set var) 
  (Λ : list (set var * set var)) (Lv : list (set var)) (ZL : list params)
  (alv : ann (set var)) :
k > 0
-> R [=] R'
-> freeVars s ⊆ R ∪ M
-> fv_e_bounded k s
-> live_sound Imperative ZL Lv s alv
-> fns_closed Λ (R ∪ M) s
(*-> getAnn alv ⊆ R' ∪ M 
-> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ (Lv \\ ZL) *)
-> spill_sound' k Λ (R,M) s (stupSpill' R' s alv).

Proof.
intro kgeq1. revert R R' M Λ Lv ZL alv. induction s;
  intros R R' M Λ Lv ZL alv ReqR' fvRM fvBound lvSound fClosed;
  inversion_clear fvBound
    as [k0 x0 e0 s0 fvBcard fvBs
       |k0 e0 fvBcard
       |k0 e0 s0 t0 fvBcard fvBs fvBt 
       |k0 f0 Y0 
       |k0 Z0 s0 t0 fvBs fvBt];
  inversion_clear lvSound
    as [ZL0 Lv' x' e' s' lv' al' lvS_s lvS_e lvS_al lvS_x
       |ZL0 Lv' x' e' s1' s2' lv' al1' al2' lvS1 lvS2 lvS_e lvS_al1 lvS_al2 
       |ZL' Lv' x' l' Y' lv' blv' Z' lvS_Z lvS_blv lvS_cnd lvS_YZ lvS_fa  
       |ZL' Lv' x' e' lv' lvS_e 
       | 
       |ZL' Lv' F' t' lv' als' alb' lvS_t lvS_snd lvS_fst lvS_alb];
  inversion_clear fClosed
    as [Λ'' RM RM' x'' e'' s'' fCrm (*fCfv*) fCs
       |Λ'' RM e'' (*fCfv*)
       |Λ'' RM e'' s'' t'' (*fCfv*) fCs fCt
       |Λ'' RM f'' Y'' R_f M_f fCget
       |Λ'' RM Z'' s'' t'' R_f M_f fCsubR fCsubM fCs fCt];
  simpl in *. 

- eapply SpillLet' with (K:= R) (Kx := Exp.freeVars e).
  + assert (seteq : singleton x [=] {x; R\R ∪ Exp.freeVars e \ Exp.freeVars e}).
    { cset_tac. }
    eapply IHs; eauto with cset.
    * rewrite seteq. reflexivity.
    * rewrite <- seteq. rewrite <- ReqR'. rewrite <- fvRM. 
      cset_tac. decide (x === a); eauto with cset.
    * admit. (* how? *)
  + cset_tac.
  + assert (seteq : R \ R ∪ Exp.freeVars e [=] Exp.freeVars e).
    { cset_tac. }
    rewrite seteq. rewrite fvBcard. trivial.
  + assert (seteq :{x; R \ R ∪ Exp.freeVars e \ Exp.freeVars e} [=] singleton x).
    { cset_tac. }
    rewrite seteq. rewrite singleton_cardinal. omega. 
- eapply SpillIf' with (K:= R).
  + cset_tac.
  + assert (seteq : R\R ∪ Exp.freeVars e [=] Exp.freeVars e). { cset_tac. }
    rewrite seteq. rewrite fvBcard. trivial.
  + eapply IHs1; eauto with cset. 
    * cset_tac.
    * rewrite <- ReqR'. rewrite <- fvRM. cset_tac.
    * admit. (* how? *)
  + eapply IHs2; eauto with cset.
    * cset_tac.
    * rewrite <- ReqR'. rewrite <- fvRM. cset_tac.
    * admit. (* how? *)
- (*specialize (exF l Y).
  assert (exists R_f M_f, get Λ (labN l) (R_f, M_f)).
          { apply exF. auto. }
  destruct H3 as [R_f H3].
  destruct H3 as [M_f H3].*)
  eapply SpillApp' with (K:= R) (R_f := R_f) (M_f := M_f).
  + assert (seteq : R \ R ∪ ∅ [=] ∅). { cset_tac. }
    rewrite seteq. rewrite empty_cardinal. omega.
  + eauto.
  + admit.
  + admit.
- eapply SpillReturn' with (K:= R).
  + cset_tac.
  + assert (seteq : R\R ∪ Exp.freeVars e [=] Exp.freeVars e). { cset_tac. }
    rewrite seteq. rewrite fvBcard. trivial.
- destruct alv; inversion lvSound.
  + simpl. eapply SpillFun'. simpl. admit. 
  + simpl. eapply SpillFun' with (K:=R).


Lemma stupSpill_sat_spillSound (k:nat) (s:stmt) (R R' M : set var)
      (Λ : list (set var * set var)) (Lv : list (set var)) (ZL :list params) 
      (alv : ann (set var)) :
k > 0
-> freeVars s ⊆ R' ∪ M
-> R' ⊆ R
-> fv_e_bounded k s
-> live_sound Imperative ZL Lv s alv
-> getAnn alv ⊆ R' ∪ M 
-> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ (Lv \\ ZL)
-> spill_sound k Λ (R,M) s (stupSpill R' s).

Proof.
  intros knotzero subs H H0 H1 H2 H3. 
  general induction s; invt fv_e_bounded; invt live_sound;
 
 simpl in *.
 
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
   - destruct als; [ isabsurd | destruct als; [|isabsurd] ].
     eapply SpillFun with (K := R) (R_f := ∅) (M_f := getAnn a \ of_list Z).  
     + assert (R\R ∪ ∅ [=] ∅) as empty. 
       * clear_all. cset_tac. 
       * rewrite empty. rewrite empty_cardinal. omega.
     + (*specialize IHs with (k := k)
                           (ZL := Z :: ZL)
                           (Lv := getAnn ⊝ als ++ Lv)
                           (R' := R')
                           (R := R)
                           (M := M)
                           (Λ := (getAnn (stupSpill ∅ s0)) ::  Λ)
                           (alv := alb).
       (*rewrite <- surjective_pairing in IHs.*)

       assert (spill_sound k ((getAnn (stupSpill ∅ s0)) ::  Λ) 
                           (R,M) s (stupSpill R' s)).
       apply IHs; eauto with cset.
       * rewrite <- subs. cset_tac. 
       * admit. 
       * rewrite empty_cardinal. admit.*) admit.
     + admit. 
     + admit.
     + admit. 
       
     + specialize IHs with (k:=k)
                           (ZL := fst ⊝ ((Z, s0) :: nil) ++ ZL)
                           (Lv := getAnn ⊝ (a :: nil) ++ Lv)
                           (R':= ∅) 
                           (*(R := R \ R ∪ ∅)
                           (M :=  R' ∪ M)*)
                          (* (Λ := (∅, (getAnn a) \ (of_list Z)) :: Λ)*)
                           (alv := alb).
       eapply IHs; eauto with cset.
       rewrite <- subs. clear. cset_tac.
       simpl. econstructor.
       split; simpl.
          eauto with cset.
          cset_tac. eauto.
          






Theorem spill_sound_correct L E E' : spill_sound k Lsl (R,M) s alv asl
-> (forall x : var, In x R -> E x = E' x)
-> (forall x : var, In x S -> E x = E' (slot x))
-> bisim (L,E,s) (L,E', doSpill slot s asl).


(* TODO: define spilling predicate similarily to the liveness predicate
         in Liveness.v *)
