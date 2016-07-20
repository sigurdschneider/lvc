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


Inductive spill_sound' (k:nat) : 
(list params) -> 
(list (set var * set var)) ->
(set var * set var) -> 
stmt -> 
ann (set var * set var * option (list (set var * set var)))
-> Prop :=

| SpillLet' ZL Λ R M Sp L K Kx sl x e s
: spill_sound' k ZL Λ ({x;(R\K ∪ L)\Kx }, Sp ∪ M) s sl
  -> Exp.freeVars e ⊆ R\K ∪ L
  -> cardinal (R\K ∪ L) <= k
  -> cardinal ({x;((R\K) ∪ L)\Kx }) <= k
  -> spill_sound' k ZL Λ (R,M) (stmtLet x e s) (ann1 (Sp,L,None) sl)

| SpillReturn' ZL Λ R M Sp L K e
: Exp.freeVars e ⊆ R\K ∪ L
  -> cardinal ((R\K) ∪ L) <= k
  -> spill_sound' k ZL Λ (R,M) (stmtReturn e) (ann0 (Sp,L,None))

| SpillIf' ZL Λ R M Sp L K sl_s sl_t e s t
: Exp.freeVars e ⊆ R\K ∪ L
  -> cardinal (R\K ∪ L) <= k
  -> spill_sound' k ZL Λ (R\K ∪ L, Sp ∪ M) s sl_s
  -> spill_sound' k ZL Λ (R\K ∪ L, Sp ∪ M) t sl_t
  -> spill_sound' k ZL Λ (R,M) (stmtIf e s t) (ann2 (Sp,L,None) sl_s sl_t)

| SpillApp' ZL Z Λ R M Sp L K f Y R_f M_f
: cardinal (R\K ∪ L) <= k
  -> get ZL (counted f) Z
  -> get Λ (counted f) (R_f,M_f)
  -> R_f \ of_list Z ⊆ R\K ∪ L
  -> M_f \ of_list Z ⊆ Sp ∪ M
    -> spill_sound' k ZL Λ (R,M) (stmtApp f Y) (ann0 (Sp,L,None))

| SpillFun' (ZL:list params) Λ R M Sp L K t sl_F sl_t (F: list(params*stmt)) rms
: cardinal (R\K ∪ L) <= k
  -> (forall n rm, get rms n rm -> cardinal (fst rm) <= k)
  (*-> R_f ⊆ R\K ∪ Sp ∪ M ∪ of_list Z
  -> M_f ⊆ R\K ∪ Sp ∪ M ∪ of_list Z*)
  -> (forall n Zs rm sl_s, get rms n rm 
     -> get F n Zs
     -> get sl_F n sl_s
     -> spill_sound' k ((List.map fst F) ++ ZL) (rms ++ Λ) rm (snd Zs) sl_s) 
  -> spill_sound' k ((List.map fst F) ++ ZL) (rms ++ Λ) (R\K ∪ L, Sp ∪ M) t sl_t
    -> spill_sound' k ZL Λ (R,M) (stmtFun F t)
                   (annF (Sp,L,Some rms) sl_F sl_t)
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

| BoundFun k F t 
: (forall n Zs, get F n Zs -> fv_e_bounded k (snd Zs))
  -> fv_e_bounded k t
  -> fv_e_bounded k (stmtFun F t)
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


Fixpoint stupSpill' (R : set var) (s : stmt) (Lv : ann (set var)) 
: ann (set var * set var * option (list (set var * set var))) := 
match s,Lv with
| stmtLet x e t, ann1 LV lv => ann1 (R, Exp.freeVars e, None)
                        (stupSpill' (singleton x) t lv)
| stmtReturn e, _ => ann0 (∅, Exp.freeVars e, None)
| stmtIf e t v, ann2 LV lv_s lv_t => ann2 (R, Exp.freeVars e, None)
                       (stupSpill' (Exp.freeVars e) t lv_s) 
                       (stupSpill' (Exp.freeVars e) v lv_t)
| stmtApp f Y, _  => ann0 (R, ∅, None)
| stmtFun F t, annF LV als lv_t =>
    annF (R, ∅, Some (List.map (fun lv => (∅, lv)) (List.map getAnn als)))
           (zip (fun Zs lv => stupSpill' ∅ (snd Zs) lv) F als)
           (stupSpill' ∅ t lv_t)
| _,_ => ann0 (∅, ∅, None)
end.


Lemma stupSpill_sat_spillSound (k:nat) (s:stmt) (R R' M : set var) 
  (Λ : list (set var * set var)) (Lv : list (set var)) (ZL : list params)
  (alv : ann (set var)) :
k > 0
-> R [=] R'
-> getAnn alv ⊆ R ∪ M
-> fv_e_bounded k s
-> live_sound Imperative ZL Lv s alv
-> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ Lv
-> spill_sound' k ZL Λ (R,M) s (stupSpill' R' s alv).

Proof.
intros kgeq1 ReqR' fvRM fvBound lvSound pir2. 
general induction lvSound;
  inversion_clear fvBound
    as [k0 x0 e0 s0 fvBcard fvBs
       |k0 e0 fvBcard
       |k0 e0 s0 t0 fvBcard fvBs fvBt 
       |k0 f0 Y0 
       |k0 Z0 s0 t0 fvBs fvBt];
  simpl in *. 

- eapply SpillLet' with (K:= R) (Kx := Exp.freeVars e).
  + assert (seteq : singleton x [=] {x; R\R ∪ Exp.freeVars e \ Exp.freeVars e}).
    { cset_tac. }
    eapply IHlvSound; eauto with cset.
    * rewrite seteq. reflexivity.
    * rewrite <- seteq. rewrite <- ReqR'. rewrite <- fvRM.
      rewrite <- H0. clear. cset_tac.
      decide (x === a); eauto with cset. 
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
  + eapply IHlvSound1; eauto with cset. 
    * cset_tac.
    * rewrite <- ReqR'. rewrite <- fvRM. cset_tac.
  + eapply IHlvSound2; eauto with cset.
    * cset_tac.
    * rewrite <- ReqR'. rewrite <- fvRM. cset_tac.
- edestruct PIR2_nth_2; eauto using zip_get; dcr. 
  destruct x as [R_f M_f]. simpl in *. 
  eapply SpillApp' with (K:= R) (R_f:= R_f) (M_f:=M_f).
  + assert (seteq : R \ R ∪ ∅ [=] ∅). { cset_tac. }
    rewrite seteq. rewrite empty_cardinal. omega.
  + eauto.
  + eauto. 
  + rewrite H7. clear. eauto with cset.
  + rewrite H8. rewrite H1. rewrite <- ReqR'. eauto. 
- eapply SpillReturn' with (K:= R).
  + cset_tac.
  + assert (seteq : R\R ∪ Exp.freeVars e [=] Exp.freeVars e). { cset_tac. }
    rewrite seteq. rewrite fvBcard. trivial.
- eapply SpillFun' with (K:=R).
  + assert (seteq : R \ R ∪ ∅ [=] ∅). { cset_tac. }
    rewrite seteq. rewrite empty_cardinal. omega.
  + intros ; inv_get. simpl. rewrite empty_cardinal. omega.
  + intros ; inv_get. eapply H1; eauto.
    eapply PIR2_app; eauto.
    eapply PIR2_get; eauto with len.
    intros ; inv_get. simpl. split; eauto with cset.
  + eapply IHlvSound; eauto.
    * cset_tac.
    * rewrite <- ReqR'. rewrite H3. rewrite fvRM. clear. cset_tac.
    * eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros ; inv_get. simpl. split; eauto with cset.
Qed.



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
