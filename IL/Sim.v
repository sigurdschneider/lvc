Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL.

Set Implicit Arguments.
Unset Printing Records.

Open Scope map_scope.
(** * Simulation *)
(** A characterization of simulation equivalence on states; works only for deterministic semantics *)
CoInductive sim {S} `{StateType S} {S'} `{StateType S'}  : S -> S' -> Prop :=
  | simS (σ1 σ1':S) (σ2 σ2':S') : (* result σ1 = result σ2 -> *) plus step σ1 σ1' -> plus step σ2 σ2' -> sim σ1' σ2' -> sim σ1 σ2
  | simE (σ1 σ1':S) (σ2 σ2':S') 
    : result σ1' = result σ2' 
      -> star step σ1 σ1'
      -> star step σ2 σ2'
      -> normal step σ1'
      -> normal step σ2' -> sim σ1 σ2.

(** Simulation is an equivalence relation *)
Lemma sim_refl {S} `{StateType S} (σ:S)
      : sim σ σ.
Proof.
  revert σ. cofix.  
  intros. destruct (step_dec σ). inv H0.
  eapply simS; eauto using plusO.
  eapply simE; eauto using star_refl.
Qed.

Lemma sim_sym {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
      : sim σ σ' -> sim σ' σ.
Proof.
  revert σ σ'. cofix; intros.
  inv H1.
  + eapply simS; eauto. 
  + eapply simE; eauto.
Qed.


(** Transitivity is not obvious *)


Inductive terminatesWith {S} `{StateType S} : S -> option val -> Prop :=
| trmWith σ r
  : r = result σ -> normal step σ  -> terminatesWith σ r
| trmWithStep σ σ' v
  : step σ σ' -> terminatesWith σ' v -> terminatesWith σ v.

Lemma terminatesWith_star_normal {S} `{StateType S} s v
  : terminatesWith s v -> exists s', star step s s' /\ normal step s' /\ result s' = v.
Proof.
  intros. general induction H0.
  eexists σ; eauto using star. 
  destruct IHterminatesWith; dcr. eexists x; split; eauto using star.
Qed.

Lemma star_normal_terminatesWith {S} `{StateType S} s s' v
  : star step s s' 
    -> normal step s' 
    -> result s' = v
    -> terminatesWith s v.
Proof.
  intros. general induction H0.
  econstructor; eauto.
  eapply trmWithStep; eauto.
Qed.

Lemma terminatesWith_star {S} `{StateType S} s s' v
  : star step s' s -> terminatesWith s v -> terminatesWith s' v.
Proof.
  intros. general induction H0; eauto.
  eapply trmWithStep; eauto.
Qed.

Lemma terminatesWith_star_2 {S} `{StateType S} s s' v
  : star step s' s -> terminatesWith s' v -> terminatesWith s v.
Proof.
  intros. general induction H0; eauto.
  inv H2. exfalso. eapply H4; firstorder.
  pose proof (step_functional _ _ _ H H3); subst. 
  eapply IHstar; eauto.
Qed.

Lemma terminatesWith_functional {S} `{StateType S} s v v'
  : terminatesWith s v -> terminatesWith s v' -> v = v'.
Proof.
  intros. general induction H0. 
  inv H2. eauto.
  exfalso. firstorder.
  inv H2. 
  exfalso; firstorder.
  rewrite step_functional in H4; eauto.
Qed.

Lemma terminatesWith_terminates {S} `{StateType S} s
  : (exists v, terminatesWith s v) <-> terminates step s.
Proof.
  split; intros. destruct H0.
  general induction H0. constructor; intros. exfalso; firstorder.
  econstructor; intros. rewrite step_functional; eauto.
  general induction H0. 
  destruct (step_dec x). destruct H2. edestruct H0; eauto.
  exists x1. eapply trmWithStep; eauto.
  eexists (result x). econstructor; eauto.
Qed.

(* Termination *)

Lemma divergence_or_termination X (R: X -> X -> Prop) s
  : diverges R s -> terminates R s -> False.
Proof.
  intros. general induction H0.
  inv H1. eauto.
Qed.

Lemma not_terminates_is_divergence S `{StateType S} s
  : ~terminates step s -> diverges step s.
Proof.
  revert s. cofix; intros.
  destruct (step_dec s). 
  + inv H1. econstructor. eauto. 
    eapply not_terminates_is_divergence. intro. eapply H0.
    econstructor; intros; eauto. rewrite step_functional; eauto.
  + exfalso. eapply H0. econstructor; intros. exfalso. firstorder.
Qed.

Definition cobehave {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S') :=
  (diverges step σ1 <-> diverges step σ2) 
  /\ (forall v, terminatesWith σ1 v <-> terminatesWith σ2 v).

Lemma diverges_star {S} `{StateType S} (σ1 σ1':S)
  : diverges step σ1 -> star step σ1 σ1' -> diverges step σ1'.
Proof.
  intros. general induction H1; simpl; eauto using star.
  inv H2. pose proof (step_functional _ _ _ H H3); subst; eauto using diverges.
Qed.

Lemma star_diverges {S} `{StateType S} (σ1 σ1':S)
  : diverges step σ1' -> star step σ1 σ1' -> diverges step σ1.
Proof.
  intros. general induction H1; simpl; eauto using star, diverges.
Qed.

Lemma cobehave_reduction_closed {S} `{StateType S} {S'} `{StateType S'} 
      (σ1 σ1':S) (σ2 σ2':S')
  : cobehave σ1 σ2
    -> star step σ1 σ1' 
    -> star step σ2 σ2'
    -> cobehave σ1' σ2'.
Proof.
  intros.
  destruct H1. split; split; intros.
  eapply diverges_star; eauto. eapply H1. eapply star_diverges; eauto.
  eapply diverges_star; eauto. eapply H1. eapply star_diverges; eauto.
  eapply terminatesWith_star_2; eauto. eapply H4. eapply terminatesWith_star; eauto.
  eapply terminatesWith_star_2; eauto. eapply H4. eapply terminatesWith_star; eauto.
Qed.

Definition obseq (s s':stmt) :=
  forall (L:F.labenv) E, cobehave (L, E, s) (L, E, s').

Lemma sim_codiverge' {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: sim σ1 σ2 -> diverges step σ1 -> diverges (plus step) σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  intros.
  inv H1. eapply DivergesI; eauto. eapply sim_codiverge'; eauto.
  eapply div_ext_plus; eauto. eapply step_functional.
  exfalso. eapply normal_terminates in H6. 
  eapply div_ext_star_2 in H2; eauto.
  eapply divergence_or_termination; eassumption. eapply step_functional.
Qed.

Lemma sim_codiverge {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: sim σ1 σ2 -> diverges step σ1 -> diverges step σ2.
Proof.
  intros. eapply div_plus. eapply (sim_codiverge' H1 H2).
Qed.

Lemma codiverge_sim {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: diverges step σ1 -> diverges step σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  inv H1; inv H2.
  eapply simS; eauto using plus.
Qed.

Lemma sim_step_closed {S} `{StateType S} {S'} `{StateType S'} (σ1 σ1':S) (σ2:S')
 : sim σ1 σ2 -> step σ1 σ1' -> sim σ1' σ2.
Proof.
  revert σ1 σ1' σ2. cofix; intros.
  inv H1. destruct H3. inv H5. 
  eapply simS. rewrite step_functional; eauto.
  eapply plus_trans; eauto. eassumption.
  eapply simE. eauto. rewrite step_functional; eauto. 
  eapply star_trans; eauto using plus_star.
  eauto. eauto.
  eapply simS. rewrite step_functional; eauto. eassumption. eauto.
  eapply simE. eauto. destruct H4. exfalso; firstorder.
  rewrite step_functional; eauto. eauto. eauto. eauto.
Qed.

Lemma sim_coterminatesWith {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: sim σ1 σ2 -> forall v, terminatesWith σ1 v -> terminatesWith σ2 v.
Proof.
  intros. general induction H2. 
  + inv H3. exfalso. eapply H1. destruct H0; firstorder. 
    destruct H4. eapply terminatesWith_star; eauto. econstructor; eauto.
    exfalso. firstorder.
  + eapply IHterminatesWith. 
    pose proof (sim_step_closed _ H3 H0). eauto.
Qed.

Lemma coterminatesWith_sim {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S') v
: terminatesWith σ1 v -> terminatesWith σ2 v -> sim σ1 σ2.
Proof. 
  intros. 
  eapply terminatesWith_star_normal in H1.
  eapply terminatesWith_star_normal in H2.
  destruct H1, H2; dcr.
  eapply simE; eauto using star. congruence.
Qed.

Lemma sim_cobehave {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: sim σ1 σ2 <-> cobehave σ1 σ2.
Proof.
  split. unfold cobehave; split; split; intros.
  + pose proof (sim_codiverge H1 H2); eauto.
  + pose proof (sim_codiverge (sim_sym H1) H2); eauto.
  + eapply (sim_coterminatesWith H1); eassumption.
  + eapply (sim_coterminatesWith (sim_sym H1) H2); eassumption. 
  + revert_all. cofix; intros. 
    destruct (step_dec σ1) as [[]|]; destruct (step_dec σ2) as [[]|].
    - eapply simS; try eapply plusO; try eassumption. 
      eapply sim_cobehave. eapply cobehave_reduction_closed; eauto using star.
    - pose proof (normal_terminates H3). eapply terminatesWith_terminates in H4; destruct H4.
      assert (terminatesWith σ1 x0). eapply H1; eauto.
      eapply coterminatesWith_sim; eauto.
    - pose proof (normal_terminates H2). eapply terminatesWith_terminates in H4; destruct H4.
      assert (terminatesWith σ2 x0). eapply H1; eauto.
      eapply coterminatesWith_sim; eauto.
    - pose proof (normal_terminates H2). eapply terminatesWith_terminates in H4; destruct H4.
      assert (terminatesWith σ2 x). eapply H1; eauto.
      eapply coterminatesWith_sim; eauto.
Qed.

Lemma cobehave_trans {S} `{StateType S} {S'} `{StateType S'} {S''} `{StateType S''} 
(σ1:S) (σ2:S') (σ3:S'')
: cobehave σ1 σ2 -> cobehave σ2 σ3 -> cobehave σ1 σ3.
Proof. 
  unfold cobehave; intros. destruct H2, H3; firstorder.
Qed.

Lemma sim_trans {S1} `{StateType S1} {S2} `{StateType S2} {S3} `{StateType S3}
      (σ1:S1) (σ2:S2) (σ3:S3)
  : sim σ1 σ2 -> sim σ2 σ3 -> sim σ1 σ3.
Proof.
  intros. 
  rewrite sim_cobehave in H2. 
  rewrite sim_cobehave in H3. 
  rewrite sim_cobehave. 
  pose proof (cobehave_trans H2 H3); eauto.
Qed.

Definition simeq (s s':stmt)
  := forall (L:F.labenv) E, sim (L, E, s) (L, E, s').

Global Instance simeq_refl : Reflexive simeq.
cbv; intros; eapply sim_refl.
Qed.

Global Instance simeq_sym : Symmetric simeq.
cbv; intros; eapply sim_sym; eauto.
Qed.

Global Instance simeq_trans : Transitive simeq.
cbv; intros. refine (sim_trans (H _ _) (H0 _ _ )).
Qed.



Lemma obseq_simeq (s s':stmt) 
  : simeq s s' <-> obseq s s'.
Proof.
  unfold simeq, obseq; split; intros; eapply sim_cobehave; eauto.
Qed.

Instance obseq_eq : Equivalence obseq.
econstructor; hnf; intros; eapply obseq_simeq.
eapply simeq_refl.
eapply simeq_sym. eapply obseq_simeq; eauto.
eapply simeq_trans; eapply obseq_simeq; eauto.
Qed.


(** * Contextual Equivalence *)

Inductive stmtCtx : Type :=
| ctxExp    (x : var) (e: exp) (C : stmtCtx) : stmtCtx
| ctxIfS     (x : var) (C : stmtCtx) (t : stmt) : stmtCtx
| ctxIfT     (x : var) (s : stmt) (C : stmtCtx) : stmtCtx
(* block f Z : rt = s in b  *)
| ctxLetS    (Z:params) (C : stmtCtx) (t : stmt) : stmtCtx 
| ctxLetT    (Z:params) (s : stmt) (C : stmtCtx) : stmtCtx
| ctxHole.

Fixpoint fill (ctx:stmtCtx) (s':stmt) : stmt :=
  match ctx with
    | ctxExp x e ctx => stmtExp x e (fill ctx s')
    | ctxIfS x ctx t => stmtIf x (fill ctx s') t
    | ctxIfT x s ctx => stmtIf x s (fill ctx s')
    | ctxLetS Z ctx t => stmtLet Z (fill ctx s') t 
    | ctxLetT Z s ctx => stmtLet Z s (fill ctx s')
    | ctxHole => s'
  end.

Fixpoint fillC (ctx:stmtCtx) (s':stmtCtx) : stmtCtx :=
  match ctx with
    | ctxExp x e ctx => ctxExp x e (fillC ctx s')
    | ctxIfS x ctx t => ctxIfS x (fillC ctx s') t
    | ctxIfT x s ctx => ctxIfT x s (fillC ctx s')
    | ctxLetS Z ctx t => ctxLetS Z (fillC ctx s') t 
    | ctxLetT Z s ctx => ctxLetT Z s (fillC ctx s')
    | ctxHole => s'
  end.

Definition ctxeq (s s':stmt) :=
  forall ctx E, cobehave (nil:list F.block, E, (fill ctx s)) (nil:list F.block, E, (fill ctx s')).
 

(*
Lemma foo s s' E E' Z L t
: simeq s s'
  -> paco0 sim ((F.blockI E' Z s :: L)%list, E, t)
         ((F.blockI E' Z s' :: L)%list, E, t).
Proof.  
  revert s s' E E' Z L t. pcofix foo. intros.
  destruct t. 
  exfalso; clear_all.
  exfalso; clear_all.
  + destruct l. destruct n.
    econstructor. eapply plusO. econstructor; eauto using get. exfalso; clear_all.
    eapply plusO. econstructor; eauto using get. exfalso; clear_all. simpl.
    refine (sim_trans (foo s s' (updE E' E Z Y) E' Z L s H) _). Guarded.
Qed.  
*)

Lemma subst_lemma_div L' s s' E E' Z L t
: obseq s s'
  -> diverges step ((L' ++ F.blockI E' Z s :: L)%list, E, t)
  -> diverges step ((L' ++ F.blockI E' Z s' :: L)%list, E, t).
Proof.
  revert L' s s' E E' Z L t. cofix; intros.
  inv H0; inv H1.
  + econstructor. constructor; eauto. eauto.
  + econstructor. econstructor; eauto. eauto.
  + econstructor. eapply F.stepIfF; eauto. eauto.
  + destruct (get_subst _ _ _ Ldef). 
    econstructor. econstructor. eapply len. eapply get_app; eauto. reflexivity.
    pose proof (get_range H3). rewrite drop_length; eauto.
    rewrite drop_length in H2; eauto.
    destruct H3; dcr; subst; simpl in *.
    econstructor. constructor. instantiate (1:= F.blockI E' Z s').
    simpl. eauto. simpl. rewrite H5. eapply get_length_app.
    reflexivity. simpl. rewrite H5. rewrite drop_length_eq.
    eapply (subst_lemma_div nil); eauto. simpl. 
    rewrite H5 in H2. rewrite drop_length_eq in H2.
    edestruct (H (F.blockI E' Z s :: L) (updE E' E Z Y)). erewrite <- H3. eauto.
    econstructor. econstructor. eapply len.
    rewrite cons_app. rewrite app_assoc. 
    eapply get_app_right; eauto. simpl.
    repeat rewrite app_length; simpl. omega.
    reflexivity. simpl. rewrite drop_length_gr; eauto.
    rewrite drop_length_gr in H2; eauto.
  + econstructor. econstructor.
    rewrite cons_app. rewrite app_assoc.
    eapply (subst_lemma_div (F.blockI E Z0 s0::nil ++ L')%list). eauto.
    simpl in *. eauto.
Qed.

Lemma subst_lemma_trm L' s s' E E' Z L t v
: obseq s s'
  -> terminatesWith ((L' ++ F.blockI E' Z s :: L)%list, E, t) v
  -> terminatesWith ((L' ++ F.blockI E' Z s' :: L)%list, E, t) v.
Proof.
  intros.
  general induction H0.
  + constructor. eauto. hnf; intros. eapply H0.
    destruct H; inv H.
    eexists; econstructor; eauto.
    eexists; econstructor; eauto.
    eexists; eapply F.stepIfF; eauto.
    edestruct (get_subst); eauto.
    econstructor; econstructor; eauto. eapply get_app; eauto.
    destruct H2; dcr. subst. 
    econstructor. econstructor; try (rewrite H4; eapply get_length_app); eauto.
    econstructor; econstructor; eauto. 
    eapply get_app_right. instantiate (1:=S (counted l - S (length L'))). omega.
    econstructor; eauto. 
    econstructor; econstructor; eauto. 
  + inv H.
    eapply trmWithStep. econstructor; eauto.
    eapply IHterminatesWith; eauto.
    eapply trmWithStep. econstructor; eauto.
    eapply IHterminatesWith; eauto.
    eapply trmWithStep. eapply F.stepIfF; eauto.
    eapply IHterminatesWith; eauto.
    destruct (get_subst _ _ _ Ldef).
    eapply trmWithStep. econstructor. eapply len.
    eapply get_app; eauto. reflexivity.
    rewrite drop_length; eauto using get_range.
    eapply IHterminatesWith; eauto.
    rewrite drop_length; eauto using get_range.
    destruct H2; dcr. subst. 
    eapply trmWithStep. econstructor. instantiate (1:=F.blockI E' Z s'). eauto.
    rewrite H4. eapply get_length_app. reflexivity.
    simpl in *. 
    assert (drop (length L') (L' ++ F.blockI E' Z s :: L)
            = (F.blockI E' Z s :: L) % list).
    eapply drop_length_eq.
    pose proof (IHterminatesWith nil _ _ (updE E' E Z Y) E' Z L s H1 eq_refl).
    rewrite H4 in H3. rewrite H2 in H3.
    simpl in *. specialize (H3 eq_refl).
    hnf in H1.
    pose proof (H1 (drop (labN l) (L' ++ F.blockI E' Z s' :: L)) (updE E' E Z Y)).
    eapply H5; rewrite H4. rewrite drop_length_eq. eauto.
    eapply trmWithStep. econstructor. instantiate  (1:=blk); eauto.
    rewrite cons_app; rewrite app_assoc.
    eapply get_app_right; eauto. rewrite app_length; simpl in *. omega.
    reflexivity.
    rewrite drop_length_gr; eauto.
    rewrite drop_length_gr in H0; eauto.
    eapply trmWithStep. econstructor.
    rewrite cons_app. rewrite app_assoc.
    eapply IHterminatesWith; eauto.
Qed.

Lemma subst_lemma s s' E E' Z L t
: obseq s s'
  -> sim ((F.blockI E' Z s :: L)%list, E, t)
         ((F.blockI E' Z s' :: L)%list, E, t). 
Proof.
  intros. rewrite sim_cobehave. 
  split; split; intros
  ; try eapply (subst_lemma_div nil); eauto. symmetry; eauto.
  eapply (subst_lemma_trm nil); eauto.
  eapply (subst_lemma_trm nil); eauto. symmetry; eauto.
Qed.
  

Lemma simeq_contextual s s' ctx
  : simeq s s' -> simeq (fill ctx s) (fill ctx s').
Proof.
  intros. general induction ctx; simpl; hnf; intros.
  + destruct (step_dec (L, E, stmtExp x e (fill ctx s))). destruct H0.
    inv H0.
    eapply simS; simpl; eauto using plus, F.step. eapply IHctx; eauto.
    eapply simE; try eapply star_refl. eauto. eauto.
    simpl. destruct 1. inv H1. eapply H0. 
    econstructor. econstructor; eauto.
  + case_eq (val2bool (E x)); intros.
    eapply simS.
    econstructor. econstructor; eauto.
    econstructor; econstructor; eauto. eapply IHctx; eauto.
    eapply simS.
    econstructor. eapply F.stepIfF; eauto.
    econstructor; eapply F.stepIfF; eauto.
    eapply sim_refl.
  + case_eq (val2bool (E x)); intros.
    eapply simS; auto.
    econstructor. econstructor; eauto.
    econstructor; econstructor; eauto.
    eapply sim_refl.
    eapply simS.
    econstructor. eapply F.stepIfF; eauto.
    econstructor; eapply F.stepIfF; eauto. eapply IHctx; eauto.
  + eapply simS.
    eapply plusO. econstructor.
    eapply plusO. econstructor.
    specialize (IHctx _ _ H).
    eapply obseq_simeq in IHctx.
    pose proof (subst_lemma E E Z L t IHctx). eauto.
  + econstructor.
    econstructor; econstructor.
    econstructor; econstructor.
    eapply IHctx; eauto.
  + eapply H; eauto using lsim_refl.
Qed. 

Lemma fill_fillC C C' s
  :  fill (fillC C C') s = fill C (fill C' s).
Proof.
  general induction C; simpl; f_equal; eauto.
Qed.


Inductive approx : F.block -> F.block -> Prop :=
 | approxI E E' Z s
   : agree_on (freeVars s \ of_list Z) E E'
     -> approx (F.blockI E Z s) (F.blockI E' Z s).

Require Import AllInRel.


Lemma ctx_constr_E E' G G' 
  : exists C, forall E, exists EC, forall (L:list F.block) s, star step (L, E, fill C s) (L, EC, s) 
                    /\ agree_on G EC E'
                    /\ agree_on (G'\G) EC E.
Proof.
  pattern G. eapply set_induction.
  intros. eexists ctxHole. intros. eexists E. 
  split. eapply star_refl. eapply empty_is_empty_1 in H.  rewrite H.
  split. hnf; intros; cset_tac; intuition. eapply agree_on_refl.
  intros. edestruct H as [C' ?].
  eexists (fillC C' (ctxExp x (Con (E' x)) ctxHole)).
  intros. specialize (H2 E). destruct H2 as[EC' ?].
  eexists (EC'[x<-E' x]). intros. rewrite fill_fillC.
  split. simpl. eapply star_right. eapply H2.
  econstructor. simpl; eauto.
  split. hnf; intros. lud; eqs. rewrite e. eauto.
  eapply H2; eauto. edestruct H1. specialize (H6 H3). destruct H6; intuition.
  eapply agree_on_update_dead. cset_tac; intuition. eapply H5. eapply H1; intuition.
  eapply agree_on_incl; eauto. eapply H2; eauto. eapply Add_Equal in H1. 
  rewrite H1. cset_tac; intuition.
Qed.

Lemma ctx_constr (L:list F.block) E G L'
  : exists C E' LC, forall s, star step (L, E, fill C s) ((LC++L)%list, E', s) 
                    /\ agree_on G E E' 
                    /\ PIR2 approx LC L'.
Proof.
  intros. general induction L'.
  + eexists ctxHole, E, nil; simpl. 
    repeat split. eapply star_refl. constructor.
  + destruct a.  
    edestruct (ctx_constr_E block_E (freeVars block_s) ∅) as [CE].
    edestruct (ctx_constr_E E G) as [CE2]. instantiate (1:=∅) in H0.
    edestruct (IHL' L E G) as [CR [ER [LC' ]]].
    specialize (H ER). destruct H as [CEE ?].
    specialize (H0 CEE). destruct H0 as [CEE2 ?].
    eexists (fillC CR (fillC CE (ctxLetT block_Z block_s CE2))).
    eexists CEE2, (F.blockI CEE block_Z block_s:: LC'). 
    intros. rewrite fill_fillC.
    specialize (H (LC'++L)%list (fill (ctxLetT block_Z block_s CE2) s)).
    split. eapply star_trans. eapply H1.
    rewrite fill_fillC. eapply star_trans.
    eapply H. simpl. eapply S_star. econstructor.
    dcr. edestruct H0. eapply H.
    split. eapply agree_on_sym. eapply H0; eauto. 
    econstructor. econstructor. eapply agree_on_incl. eapply H. 
    eapply incl_minus. eapply H1; eauto.
Qed.
  
Lemma sim_freeVars (L L':list F.block) (E E':env var) s
:  agree_on (freeVars s) E E'
   -> PIR2 approx L L'
   -> sim (L, E, s) (L', E', s).
Proof.
  revert L L' E E' s; cofix; intros.
  destruct s; simpl.
  + case_eq (exp_eval E e); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto. erewrite <- exp_eval_live; eauto.
    simpl. eapply live_exp_sound_incl; simpl; eauto using live_freeVars.
    cset_tac; intuition.
    eapply sim_freeVars; eauto. simpl in H.
    eapply agree_on_update_same; eauto. eapply agree_on_incl; eauto.
    cset_tac; intuition.
    eapply simE; try eapply star_refl; eauto; stuck.
    erewrite exp_eval_live in H1; eauto. congruence.
    simpl. eapply live_exp_sound_incl; simpl; eauto using live_freeVars.
    cset_tac; intuition.
  + case_eq (val2bool (E x)); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto. rewrite <- H; simpl; eauto. cset_tac; intuition.
    simpl in *. eapply sim_freeVars; eauto. 
    eapply agree_on_incl; eauto. cset_tac; intuition.
    eapply simS; try eapply plusO.
    eapply F.stepIfF; eauto.
    eapply F.stepIfF; eauto. rewrite <- H; simpl; eauto. cset_tac; intuition.
    simpl in *. eapply sim_freeVars; eauto. 
    eapply agree_on_incl; eauto. cset_tac; intuition.
  + destruct (get_dec L (counted l)). destruct s as [[]].
    destruct_prop (length block_Z = length Y).
    edestruct PIR2_nth; try eassumption; dcr; destruct x.
    inv H3.
    econstructor; try eapply plusO.
    econstructor; eauto. simpl. eauto.
    econstructor; eauto. simpl. eauto.
    simpl. eapply sim_freeVars.
    unfold updE. erewrite lookup_list_agree; eauto.
    eapply update_with_list_agree. eapply agree_on_incl; eauto.
    cset_tac; intuition. rewrite lookup_list_length. eauto.
    eapply PIR2_drop; eauto.
    eapply simE; try eapply star_refl; eauto; stuck; eauto.
    get_functional; subst; simpl in *; congruence.
    edestruct PIR2_nth_2; try eassumption; dcr; eauto.
    repeat get_functional; subst; simpl in *; try congruence. inv H3. 
    simpl in *; congruence.
    eapply simE; try eapply star_refl; auto; stuck; eauto.
    edestruct PIR2_nth_2; try eassumption; dcr; eauto.
  + eapply simE; try eapply star_refl; simpl; try stuck; eauto.
    rewrite H; eauto. simpl; cset_tac; eauto.
  + eapply simS; try eapply plusO.
    econstructor.
    econstructor. Guarded.
    eapply sim_freeVars. eapply agree_on_incl; eauto.
    simpl. cset_tac; intuition.
    econstructor. econstructor; eauto. 
    eapply agree_on_incl; eauto. simpl. cset_tac; intuition. eauto.
Qed.


Lemma sim_coincidence L L' E E' s s'
  : sim (L, E, s) (L, E, s')
    -> agree_on (freeVars s ∪ freeVars s') E E'
    -> PIR2 approx L L'
    -> sim (L', E', s) (L', E', s').
Proof.
  intros. 
  assert (agree_on (freeVars s) E E'). 
  eapply agree_on_incl; intuition (cset_tac; eauto).
  assert (agree_on (freeVars s') E E'). 
  eapply agree_on_incl; try eapply H0. intuition (cset_tac; eauto).
  pose proof (@sim_freeVars L L' E E' s H2 H1).
  pose proof (@sim_freeVars L L' E E' s' H3 H1).
  eapply sim_sym in H4.
  eapply (sim_trans H4 (sim_trans H H5)).
Qed.

Lemma sim_reduction_closed {S} `{StateType S} {S'} `{StateType S'} 
      (σ1 σ1':S) (σ2 σ2':S')
  : sim σ1 σ2
    -> star step σ1 σ1' 
    -> star step σ2 σ2'
    -> sim σ1' σ2'.
Proof.
  intros.
  eapply sim_cobehave in H1. eapply sim_cobehave.
  destruct H1. split; split; intros.
  eapply diverges_star; eauto. eapply H1. eapply star_diverges; eauto.
  eapply diverges_star; eauto. eapply H1. eapply star_diverges; eauto.
  eapply terminatesWith_star_2; eauto. eapply H4. eapply terminatesWith_star; eauto.
  eapply terminatesWith_star_2; eauto. eapply H4. eapply terminatesWith_star; eauto.
Qed.

Lemma sim_expansion_closed {S} `{StateType S} {S'} `{StateType S'} 
      (σ1 σ1':S) (σ2 σ2':S')
  : sim σ1' σ2'
    -> star step σ1 σ1' 
    -> star step σ2 σ2'
    -> sim σ1 σ2.
Proof.
  intros.
  eapply sim_cobehave in H1. eapply sim_cobehave.
  destruct H1. split; split; intros.
  eapply star_diverges; eauto. eapply H1. eapply diverges_star; eauto.
  eapply star_diverges; eauto. eapply H1. eapply diverges_star; eauto.
  eapply terminatesWith_star; eauto. eapply H4. eapply terminatesWith_star_2; eauto.
  eapply terminatesWith_star; eauto. eapply H4. eapply terminatesWith_star_2; eauto.
Qed.

Lemma ctxeq_simeq s s':
  ctxeq s s' <-> simeq s s'.
Proof.
  split; intros. 
  hnf; intros. edestruct (ctx_constr (nil:list F.block) E (freeVars s ∪ freeVars s')) as [C [E' [LC ?]]].
  specialize (H C E); simpl in *. 
  eapply sim_cobehave in H; eauto.
  pose proof (H0 s). specialize (H0 s'); dcr.
  pose proof (sim_reduction_closed H H2 H1).
  repeat rewrite app_nil_r in H0.
  eapply sim_coincidence; eauto.
  symmetry; eauto.
  hnf; intros. 
  eapply sim_cobehave. eapply simeq_contextual; eauto.
Qed.

Instance ctxeq_equivalence : Equivalence ctxeq.
Proof.
  hnf; intros. constructor.
  hnf; intros. eapply ctxeq_simeq; reflexivity.
  hnf; intros. eapply ctxeq_simeq; eapply ctxeq_simeq in H; symmetry; eauto.
  hnf; intros. eapply ctxeq_simeq. eapply ctxeq_simeq in H; eapply ctxeq_simeq in H0;
                                   transitivity y; eauto.
Qed.


Ltac single_step :=
  match goal with
    | [ H : agree_on _ ?E ?E', I : val2bool (?E ?x) = true |- step (_, ?E', stmtIf ?x _ _) _ ] =>
      econstructor; eauto; rewrite <- H; eauto; cset_tac; intuition
    | [ H : agree_on _ ?E ?E', I : val2bool (?E ?x) = false |- step (_, ?E', stmtIf ?x _ _) _ ] =>
      econstructor 3; eauto; rewrite <- H; eauto; cset_tac; intuition
    | [ H : val2bool _ = false |- _ ] => econstructor 3 ; try eassumption; try reflexivity
    | [ H : step (?L, _ , stmtGoto ?l _) _, H': get ?L (counted ?l) _ |- _] =>
      econstructor; try eapply H'; eauto
    | [ H': get ?L (counted ?l) _ |- step (?L, _ , stmtGoto ?l _) _] =>
      econstructor; try eapply H'; eauto
    | _ => constructor; eauto
  end.


Ltac one_step := eapply simS; [ eapply plusO; single_step
                              | eapply plusO; single_step
                              | ].

Ltac no_step := eapply simE; try eapply star_refl; try get_functional; try subst;
                [ try reflexivity
                | stuck
                | stuck  ].


Inductive simB : F.labenv -> F.labenv -> F.block -> F.block -> Prop :=
| simBI L L' E E' Z Z' s s'
  : length Z = length Z'
    -> (forall VL, length VL = length Z -> length Z = length Z' ->
          sim (L, E[Z <-- VL], s) 
              (L', E'[Z' <-- VL], s'))
    -> simB L L' (F.blockI E Z s) (F.blockI E' Z' s').

Definition simL L L' := AIR4 simB L L' L L'.

Lemma simL_refl L : simL L L.
Proof.
  general induction L. econstructor.
  econstructor; eauto. destruct a; econstructor; eauto. intros. eapply sim_refl.
Qed.

Lemma simL_sym L1 L2 L3 L4 : AIR4 simB L1 L2 L3 L4 -> AIR4 simB L2 L1 L4 L3.
Proof.
  intros. general induction H; eauto using AIR4.
  econstructor; eauto.
  destruct pf. 
  econstructor; eauto. intros. refine (sim_sym _). eapply H1; eauto. congruence. 
Qed.

Lemma simL_trans LA1 LA2 LB1 LB2 LC1 LC2 
 : AIR4 simB LA1 LB1 LA2 LB2 -> AIR4 simB LB1 LC1 LB2 LC2
-> AIR4 simB LA1 LC1 LA2 LC2.
Proof.
  intros. general induction H; inv H0; eauto using AIR4.
  econstructor; eauto. inv pf. inv pf0.
  econstructor. congruence.
  intros. refine (sim_trans (H2 _ _ _) (H11 _ _ _)); congruence.
Qed.

Definition simeq2 (s s':stmt)
  := forall (L L':F.labenv) E, simL L L' -> sim (L, E, s) (L', E, s').

Definition fexteq E Z s E' Z' s' := 
  forall VL L L', length VL = length Z -> length Z = length Z' -> simL L L' -> 
                   sim (L, E[Z <-- VL], s) 
                       (L', E'[Z' <-- VL], s').

Lemma fexteq_sym E Z s E' Z' s' 
: fexteq E Z s E' Z' s' <-> fexteq E' Z' s' E Z s.
Proof.
  unfold fexteq; intuition.
  - eapply sim_sym, H, simL_sym; eauto; congruence.
  - eapply sim_sym, H, simL_sym; eauto; congruence.
Qed.

Lemma subst_lemma_div_L L L1 L2 s s' E E1 E2 Z Z' t
: fexteq E1 Z s E2 Z' s'
  -> length Z = length Z'
  -> simL L1 L2
  -> diverges step ((L ++ F.blockI E1 Z s :: L1)%list, E, t)
  -> diverges step ((L ++ F.blockI E2 Z' s' :: L2)%list, E, t).
Proof.
  revert L L1 L2 s s' E E1 E2 Z Z' t. cofix; intros.
  inv H2; inv H3.
  + econstructor. constructor; eauto. eauto.
  + econstructor. econstructor; eauto. eauto.
  + econstructor. eapply F.stepIfF; eauto. eauto. 
  + destruct (get_subst _ _ _ Ldef) as [?|[?|?]]; subst; simpl in *; dcr.
    - econstructor. econstructor. eapply len. eapply get_app; eauto. reflexivity.
      pose proof (get_range H5). rewrite drop_length; eauto.
      rewrite drop_length in H4; eauto.
    - subst; simpl in *. 
      econstructor. constructor. instantiate (1:= F.blockI E2 Z' s').
      simpl. congruence. simpl. rewrite H7. eapply get_length_app.
      reflexivity. simpl. rewrite H7. rewrite drop_length_eq.
      eapply (subst_lemma_div_L nil); eauto. simpl. 
      rewrite H7 in H4. rewrite drop_length_eq in H4. unfold updE.
      specialize (H (lookup_list E Y)).
      pose proof (@sim_codiverge F.state _ F.state _).
      eapply H5; eauto. eapply H. 
      rewrite lookup_list_length. congruence. congruence.
      eapply simL_refl.
    - edestruct (AIR4_length H1); dcr.
      destruct (AIR4_nth' H1 H6) as [? [? [?]]]; dcr.
      inv H15. repeat (get_functional; subst). simpl in *.
      econstructor. econstructor. Focus 2.
      rewrite cons_app. rewrite app_assoc. 
      eapply get_app_right; eauto. simpl.
      repeat rewrite app_length; simpl. omega. simpl. congruence.
      reflexivity. simpl. rewrite drop_length_gr; eauto.
      rewrite drop_length_gr in H4; eauto.
      pose proof (@sim_codiverge F.state _ F.state _).
      eapply H6. eapply H14. rewrite lookup_list_length. congruence. congruence.
      eauto. 
  + econstructor. econstructor.
    rewrite cons_app. rewrite app_assoc.
    eapply (subst_lemma_div_L (F.blockI E Z0 s0::nil ++ L)%list); eauto.
Qed.

Lemma subst_lemma_trm_L L L1 L2 s s' E E1 E2 Z Z' t v
: fexteq E1 Z s E2 Z' s'
  -> length Z = length Z'
  -> simL L1 L2
  -> terminatesWith ((L ++ F.blockI E1 Z s :: L1)%list, E, t) v
  -> terminatesWith ((L ++ F.blockI E2 Z' s' :: L2)%list, E, t) v.
Proof.
  intros LEQ H LEN H0.
  general induction H0.
  + constructor. eauto. hnf; intros. eapply H0.
    destruct H; inv H.
    - eexists; econstructor; eauto.
    - eexists; econstructor; eauto.
    - eexists; eapply F.stepIfF; eauto.
    - edestruct (get_subst) as [|[]]; eauto.
      * econstructor; econstructor; eauto. eapply get_app; eauto.
      * dcr; subst. 
        econstructor. econstructor; try (rewrite H4; eapply get_length_app); eauto.
        simpl in * |- *; congruence.
      * dcr; subst.
        edestruct AIR4_length; try eassumption; dcr.
        edestruct (get_length_eq _ H3 (eq_sym H2)); eauto.
        unfold simL in *. edestruct AIR4_nth as [blk1 [blk2]]; eauto; dcr.
        inv H12; repeat get_functional; subst.
        econstructor; econstructor.
        Focus 2.
        eapply get_app_right. instantiate (1:=S (counted l - S (length L))).
        omega. econstructor; eauto. simpl in * |- *; congruence.
        reflexivity.
    - econstructor; econstructor; eauto. 
  + inv H.
    - eapply trmWithStep. econstructor; eauto.
      eapply IHterminatesWith; eauto.
    - eapply trmWithStep. econstructor; eauto.
      eapply IHterminatesWith; eauto.
    - eapply trmWithStep. eapply F.stepIfF; eauto.
      eapply IHterminatesWith; eauto.
    - destruct (get_subst _ _ _ Ldef) as [|[|]].
      * eapply trmWithStep. econstructor. eapply len.
        eapply get_app; eauto. reflexivity.
        rewrite drop_length; eauto using get_range.
        eapply IHterminatesWith; eauto.
        rewrite drop_length; eauto using get_range.
      * dcr; subst.
        edestruct AIR4_length; eauto; dcr.
        eapply trmWithStep. econstructor.
        Focus 2.
        rewrite H4. eapply get_length_app. 
        simpl in * |- *. congruence. reflexivity.
        simpl.
        rewrite H4 in *. erewrite drop_length_eq in *. 
        simpl in *. rewrite H4. erewrite drop_length_eq. 
        unfold updE.
        refine (sim_coterminatesWith (LEQ (lookup_list E Y) _ _ 
                                               _ _ (simL_refl _)) _).
        rewrite lookup_list_length. congruence. congruence.
        eapply (IHterminatesWith nil); eauto. 
      * dcr.
        edestruct AIR4_length; try eassumption; dcr.
        edestruct get_length_eq; try eassumption.
        edestruct AIR4_nth as [blk1 [blk2]]; dcr; eauto.
        inv H12; repeat get_functional; subst. simpl in *.
        eapply trmWithStep. econstructor.
        Focus 2.
        rewrite cons_app; rewrite app_assoc.
        eapply get_app_right; eauto. rewrite app_length; simpl in *. omega.
        simpl in * |- *; congruence. reflexivity.
        rewrite drop_length_gr; eauto.
        rewrite drop_length_gr in H0; eauto.
        unfold updE.
        simpl. 
        refine (sim_coterminatesWith (H10 _ _ _) _). 
        rewrite lookup_list_length. simpl in *. congruence. congruence.
        eapply H0.
    - eapply trmWithStep. econstructor; eauto.
      rewrite cons_app. rewrite app_assoc.
      eapply IHterminatesWith; eauto.
Qed.


Lemma subst_lemma_L L s s' V E E' Z Z' L1 L2 t
: fexteq E Z s E' Z' s'
  -> length Z = length Z'
  -> simL L1 L2
  -> sim ((L ++ (F.blockI E Z s :: L1))%list, V, t)
         ((L ++ (F.blockI E' Z' s' :: L2))%list, V, t).
Proof.
  intros. rewrite sim_cobehave. 
  split; split; intros.
  - eapply subst_lemma_div_L; eauto. 
  - eapply subst_lemma_div_L. eapply fexteq_sym; eauto. congruence. 
    eapply simL_sym; eauto. eauto.
  - eapply (subst_lemma_trm_L); eauto.
  - eapply (subst_lemma_trm_L). eapply fexteq_sym; eauto. congruence. 
    eapply simL_sym; eauto. eauto.
Qed.


Lemma simL_extension s s' E E' Z Z' L L'
: simL L L' 
  -> fexteq E Z s E' Z' s'
  -> length Z = length Z'
  -> simL (F.blockI E Z s :: L) (F.blockI E' Z' s' :: L').
Proof.
  intros.
  hnf; intros. econstructor; eauto. econstructor; eauto; intros.
  + eapply (@sim_trans F.state _ F.state _ F.state).
    eapply (subst_lemma_L nil); eauto.
    eapply H0; eauto using simL_refl.
Qed.

Lemma simeq2_refl s
  : simeq2 s s.
Proof.
  hnf; general induction s; simpl.
  + case_eq (exp_eval E e); intros.
    - one_step; eauto.
    - no_step; eauto.
  + case_eq(val2bool(E x)); intros; one_step; eauto. 
  + destruct (get_dec L (counted l)). destruct s as [[]].
    destruct_prop (length block_Z = length Y).
    - edestruct AIR4_nth' as [? [? [? ]]]; dcr; try eassumption.
      repeat get_functional; subst. inv H5.
      one_step; simpl in *; eauto. congruence. simpl.
      eapply H10; eauto. rewrite lookup_list_length; eauto. 
    - edestruct AIR4_nth' as [? [? [? ]]]; dcr; try eassumption.
      repeat get_functional; subst. inv H5.
      no_step. repeat get_functional; subst. simpl in *. congruence.
      get_functional; subst. simpl in *. congruence.
    - no_step; eauto.
      exfalso; clear_all; admit.
  + no_step.
  + one_step. eapply IHs2. eapply simL_extension; eauto.
    hnf; intros. eapply IHs1; eauto.
Qed.

Lemma simeq2_simeq s s'
  : simeq s s' <-> simeq2 s s'.
Proof.
  split; unfold simeq2, simeq; intros.
  eapply (sim_trans (H L E) (simeq2_refl _ _ H0)).
  eapply H; eauto using simL_refl.
Qed.

Lemma fexteq_refl E Z s
  : fexteq E Z s E Z s.
Proof.
  hnf; intros. eapply simeq2_refl; eauto. 
Qed.

Lemma simB_refl L L' blk 
: simL L L'
  -> simB L L' blk blk.
Proof.
  intros. destruct blk. econstructor; eauto. intros. eapply simeq2_refl; eauto.
Qed.



(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)

