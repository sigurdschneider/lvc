Require Import List Map Env AllInRel Exp MoreExp.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI.
Require Import Spilling.


Fixpoint stupSpill (R : set var) (s : stmt) (Lv : ann (set var)) 
: ann (set var * set var * option (list (set var * set var))) := 
match s,Lv with
| stmtLet x e t, ann1 LV lv => ann1 (R, Exp.freeVars e, None)
                        (stupSpill (singleton x) t lv)
| stmtReturn e, _ => ann0 (∅, Exp.freeVars e, None)
| stmtIf e t v, ann2 LV lv_s lv_t => ann2 (R, Exp.freeVars e, None)
                       (stupSpill (Exp.freeVars e) t lv_s) 
                       (stupSpill (Exp.freeVars e) v lv_t)
| stmtApp f Y, _  => ann0 (R, ∅, None)
| stmtFun F t, annF LV als lv_t =>
    annF (R, ∅, Some (List.map (fun lv => (∅, lv)) (List.map getAnn als)))
           (zip (fun Zs lv => stupSpill ∅ (snd Zs) lv) F als)
           (stupSpill ∅ t lv_t)
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
-> spill_sound k ZL Λ (R,M) s (stupSpill R' s alv).

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

- eapply SpillLet with (K:= R) (Kx := Exp.freeVars e).
  + assert (seteq : singleton x [=] {x; (R\R ∪Exp.freeVars e) \Exp.freeVars e}).
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
  + assert (seteq :{x; (R \ R ∪Exp.freeVars e)\ Exp.freeVars e} [=] singleton x).
    { cset_tac. }
    rewrite seteq. rewrite singleton_cardinal. omega. 
- eapply SpillIf with (K:= R).
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
  eapply SpillApp with (K:= R) (R_f:= R_f) (M_f:=M_f).
  + assert (seteq : R \ R ∪ ∅ [=] ∅). { cset_tac. }
    rewrite seteq. rewrite empty_cardinal. omega.
  + eauto.
  + eauto. 
  + rewrite H7. clear. eauto with cset.
  + rewrite H8. rewrite H1. rewrite <- ReqR'. eauto. 
- eapply SpillReturn with (K:= R).
  + cset_tac.
  + assert (seteq : R\R ∪ Exp.freeVars e [=] Exp.freeVars e). { cset_tac. }
    rewrite seteq. rewrite fvBcard. trivial.
- eapply SpillFun with (K:=R).
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
