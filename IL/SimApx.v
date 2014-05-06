Require Import List Infra.Relations.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL Sim AllInRel paco.paco.

Set Implicit Arguments.
Unset Printing Records.


CoInductive simapx {S} `{StateType S} {S'} `{StateType S'}  : S -> S' -> Prop :=
  | simS (σ1 σ1':S) (σ2 σ2':S') : (* result σ1 = result σ2 -> *) plus step σ1 σ1' -> plus step σ2 σ2' -> simapx σ1' σ2' -> simapx σ1 σ2
  | simE (σ1 σ1':S) (σ2 σ2':S') 
    : result σ1' = result σ2'
      -> star step σ1 σ1'
      -> star step σ2 σ2'
      -> normal step σ1'
      -> normal step σ2' -> simapx σ1 σ2
  | simErr (σ1 σ1':S) (σ2:S') 
    : result σ1' = None
      -> star step σ1 σ1'
      -> normal step σ1' -> simapx σ1 σ2.

Inductive psimapx 
          {S} `{StateType S} {S'} `{StateType S'} (psimapx': S -> S' -> Prop)  : S -> S' -> Prop :=
  | psimS (σ1 σ1':S) (σ2 σ2':S') :
      (* result σ1 = result σ2 -> *) 
      plus step σ1 σ1' 
      -> plus step σ2 σ2' 
      -> psimapx' σ1' σ2' 
      -> psimapx psimapx' σ1 σ2
  | psimE (σ1 σ1':S) (σ2 σ2':S') 
    : result σ1' = result σ2'
      -> star step σ1 σ1'
      -> star step σ2 σ2'
      -> normal step σ1'
      -> normal step σ2' -> psimapx psimapx' σ1 σ2
  | psimErr (σ1 σ1':S) (σ2:S') 
    : result σ1' = None
      -> star step σ1 σ1'
      -> normal step σ1' -> psimapx psimapx' σ1 σ2.
Hint Constructors psimapx.

Definition psimapxd {S} `{StateType S} {S'} `{StateType S'}  (σ1:S) (σ2:S')
  := paco2 (@psimapx S _ S' _) bot2 σ1 σ2.
Hint Unfold psimapxd.

Lemma psimapxd_mon {S} `{StateType S} {S'} `{StateType S'} 
: monotone2 (@psimapx S _ S' _).
Proof.
  pmonauto.
Qed.
Hint Resolve psimapxd_mon : paco.

Lemma simapx_psimapxd {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: simapx σ1 σ2 -> psimapxd σ1 σ2.
Proof.
  revert σ1 σ2. pcofix CIH.
  intros. pfold.
  inv H2.
  econstructor; eauto.
  econstructor 2; eauto.
  econstructor 3; eauto.
Qed.

Lemma psimapxd_simapx {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: psimapxd σ1 σ2 -> simapx σ1 σ2.
Proof.
  revert_all; cofix; intros.
  inv H1.
  destruct SIM. 
  - edestruct LE; try eassumption.
    econstructor; eauto. inv H5.
  - econstructor 2; eauto. 
  - econstructor 3; eauto.
Qed.

(** Simulation is an equivalence relation *)
Lemma simapx_refl {S} `{StateType S} (σ:S)
      : simapx σ σ.
Proof.
  revert σ. cofix.  
  intros. destruct (step_dec σ). inv H0.
  eapply simS; eauto using plusO.
  eapply simE; eauto using star_refl.
Qed.

(** Transitivity is not obvious *)

Definition apxbehave {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S') :=
  (diverges step σ1 -> diverges step σ2) 
  /\ (forall v, terminatesWith σ1 (Some v) -> terminatesWith σ2 (Some v)).

Lemma apxbehave_reduction_closed {S} `{StateType S} {S'} `{StateType S'} 
      (σ1 σ1':S) (σ2 σ2':S')
  : apxbehave σ1 σ2
    -> star step σ1 σ1' 
    -> star step σ2 σ2'
    -> apxbehave σ1' σ2'.
Proof.
  intros.
  destruct H1. split; intros.
  eapply diverges_star; eauto. eapply H1. eapply star_diverges; eauto.
  eapply terminatesWith_star_2; eauto. eapply H4. eapply terminatesWith_star; eauto.
Qed.

Lemma simapx_codiverge' {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: simapx σ1 σ2 -> diverges step σ1 -> diverges (plus step) σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  intros.
  inv H1. eapply DivergesI; eauto. eapply simapx_codiverge'; eauto.
  eapply div_ext_plus; eauto. eapply step_functional.
  exfalso. eapply normal_terminates in H6. 
  eapply div_ext_star_2 in H2; eauto.
  eapply divergence_or_termination; eassumption. eapply step_functional.
  exfalso. eapply normal_terminates in H5. 
  eapply div_ext_star_2 in H2; eauto.
  eapply divergence_or_termination; eassumption. eapply step_functional.
Qed.

Lemma simapx_codiverge {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: simapx σ1 σ2 -> diverges step σ1 -> diverges step σ2.
Proof.
  intros. eapply div_plus. eapply (simapx_codiverge' H1 H2).
Qed.

Lemma codiverge_simapx {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: diverges step σ1 -> diverges step σ2 -> simapx σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  inv H1; inv H2.
  eapply simS; eauto using plus.
Qed.

Lemma simapx_step_closed {S} `{StateType S} {S'} `{StateType S'} (σ1 σ1':S) (σ2:S')
 : simapx σ1 σ2 -> step σ1 σ1' -> simapx σ1' σ2.
Proof.
  revert σ1 σ1' σ2. cofix; intros.
  inv H1. destruct H3. inv H5. 
  eapply simS. rewrite step_functional; eauto.
  eapply plus_trans; eauto. eassumption.
  eapply simE. eauto. rewrite step_functional; eauto. 
  eapply star_trans; eauto using plus_star.
  eauto. eauto. 
  eapply simErr; eauto. rewrite step_functional; eauto.
  eapply simS. rewrite step_functional; eauto. eassumption. eauto. 
  eapply simE. eauto. destruct H4. exfalso; firstorder.
  rewrite step_functional; eauto. eauto. eauto. eauto.
  eapply simErr; eauto. destruct H4. exfalso; firstorder.
  rewrite step_functional; eauto.
Qed.

Lemma simapx_coterminatesWith {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: simapx σ1 σ2 -> forall v, terminatesWith σ1 (Some v) -> terminatesWith σ2 (Some v).
Proof.
  intros. remember (Some v). revert Heqo. induction H2; intros.
  + inv H1.
    - exfalso. eapply H3. destruct H4; firstorder. 
    - destruct H5. 
      * eapply terminatesWith_star; eauto. rewrite H4. econstructor; eauto.
      * exfalso. firstorder.
    - destruct H5. 
      * congruence.
      * exfalso. firstorder.
  + eapply IHterminatesWith. 
    pose proof (simapx_step_closed _ H1 H2); eauto. eauto.
Qed.

Lemma coterminatesWith_simapx {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S') v
: terminatesWith σ1 v -> terminatesWith σ2 v -> simapx σ1 σ2.
Proof. 
  intros. 
  eapply terminatesWith_star_normal in H1.
  eapply terminatesWith_star_normal in H2.
  destruct H1, H2; dcr.
  eapply simE; eauto using star. rewrite H6, H8; reflexivity.
Qed.

Require Import Classical.

Lemma sim_apxbehave {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: simapx σ1 σ2 <-> apxbehave σ1 σ2.
Proof.
  split. unfold cobehave; split; intros.
  + pose proof (simapx_codiverge H1 H2); eauto.
  + eapply (simapx_coterminatesWith H1); eassumption.
  + revert_all. cofix; intros.
    destruct (step_dec σ1) as [[]|]; destruct (step_dec σ2) as [[]|].
    - eapply simS; try eapply plusO; try eassumption. 
      eapply sim_apxbehave. eapply apxbehave_reduction_closed; eauto using star.
    - hnf in H1.
      destruct (classic (terminates step σ1)).
      eapply terminatesWith_terminates in H4. destruct H4 as [[]].
      dcr. exploit H6; eauto. eapply coterminatesWith_simapx; eauto.
      edestruct (terminatesWith_star_normal H4); dcr.
      eapply simErr; eauto.
      eapply not_terminates_is_divergence in H4.
      exfalso. eapply H1 in H4. inv H4. eapply H3. eexists; eauto.
    - hnf in H1. case_eq (result σ1); intros.
      dcr. assert (terminatesWith σ1 (Some v)) by (econstructor; eauto).
      exploit H6; eauto. eapply coterminatesWith_simapx; eauto.
      eapply simErr; eauto using star_refl.
    - case_eq (result σ1); intros.
      destruct H1; exploit H5. econstructor; eauto.
      eapply simE; try eapply star_refl; eauto. 
      inv X. congruence. exfalso. eapply H3. eexists; eauto. 
      eapply simErr; eauto using star_refl.
Qed.

Lemma apxbehave_trans {S} `{StateType S} {S'} `{StateType S'} {S''} `{StateType S''} 
(σ1:S) (σ2:S') (σ3:S'')
: apxbehave σ1 σ2 -> apxbehave σ2 σ3 -> apxbehave σ1 σ3.
Proof. 
  unfold cobehave; intros. destruct H2, H3; firstorder.
Qed.

Lemma simapx_trans {S1} `{StateType S1} 
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : simapx σ1 σ2 -> simapx σ2 σ3 -> simapx σ1 σ3.
Proof.
  intros. 
  rewrite sim_apxbehave in H2. 
  rewrite sim_apxbehave in H3. 
  rewrite sim_apxbehave. 
  pose proof (apxbehave_trans H2 H3); eauto.
Qed.

Lemma simapx_expansion_closed {S} `{StateType S} 
      (σ1 σ1':S) {S'} `{StateType S'} (σ2 σ2':S') r
  : paco2 (@psimapx S _ S' _) r σ1' σ2'
    -> star step σ1 σ1' 
    -> star step σ2 σ2'
    -> paco2 (@psimapx S _ S' _) r σ1 σ2.
Proof.
  intros. pinversion H1. subst.
  pfold.
  - econstructor; eauto using star_plus_plus.
  - econstructor; eauto using star_trans.
  - econstructor; eauto using star_trans.
  - eapply psimapxd_mon.
Qed.

Definition ParamRel A := A-> list var -> list var -> Prop.
Definition ArgRel A := A-> list val -> list val -> Prop.

Definition RelsOk A (R:ArgRel A) (R':ParamRel A) :=
  forall a Z Z' VL VL', R' a Z Z' -> R a VL VL' -> length Z = length VL /\ length Z' = length VL'.

(*Inductive simB {A} (R:ArgRel A) (R':ParamRel A) : F.labenv -> F.labenv -> A -> F.block -> F.block -> Prop :=
| simBI a L L' E E' Z Z' s s'
  : R' a Z Z'
    -> (forall VL VL', R a VL VL' -> length Z = length VL -> length Z' = length VL'
                 -> simapx (L, E[Z <-- VL], s) 
                          (L', E'[Z' <-- VL'], s'))
    -> simB R R' L L' a (F.blockI E Z s) (F.blockI E' Z' s').*)

Inductive simB (r:rel2 F.state (fun _ : F.state => F.state)) {A} (R:ArgRel A) (R':ParamRel A) : F.labenv -> F.labenv -> A -> F.block -> F.block -> Prop :=
| simBI a L L' E E' Z Z' s s'
  : R' a Z Z'
    -> (forall E E' Y Y' Yv Y'v, 
         omap (exp_eval E) Y = Some Yv
         -> omap (exp_eval E') Y' = Some Y'v
         -> R a Yv Y'v
(*               -> length Z = length Y
               -> length Z' = length Y' *)
               -> paco2 (@psimapx F.state _ F.state _) r (L, E, stmtGoto (LabI 0) Y) 
                        (L', E', stmtGoto (LabI 0) Y'))
(*    -> (forall VL VL',
         R a VL VL' 
         -> length Z = length VL
         -> length Z' = length VL'
         -> paco2 (@psimapx F.state _ F.state _) r (L, E[Z <-- VL], s) 
                 (L', E'[Z' <-- VL'], s'))*)
    -> simB r R R' L L' a (F.blockI E Z s) (F.blockI E' Z' s').

Definition simL' (r:rel2 F.state (fun _ : F.state => F.state))
           {A} R R' (AL:list A) L L' := AIR5 (simB r R R') L L' AL L L'.

(*
Lemma simL_refl {A} R (AL:list A) L : 
  length AL = length L -> simL R AL L L.
Proof.
  general induction L. destruct AL; isabsurd. constructor.
  destruct AL; isabsurd.
  econstructor; eauto. destruct a; econstructor; eauto. intros. eapply sim_refl.
  eapply IHL. simpl in *; omega.
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
*)

Definition simeq2 r {A} R R' (AL:list A) (s s':stmt)
  := forall (L L':F.labenv) E, simL' r R R' AL L L' -> sim (L, E, s) (L', E, s').

Definition fexteq'
           {A} (R:ArgRel A) R' (a:A) (AL:list A) E Z s E' Z' s' := 
  forall VL VL' L L' (r:rel2 F.state (fun _ : F.state => F.state)),
    R a VL VL' 
    -> simL' r R R' AL L L' 
    -> length Z = length VL
    -> length Z' = length VL'
    -> paco2 (@psimapx F.state _ F.state _) r (L, E[Z <-- VL], s) 
            (L', E'[Z' <-- VL'], s').

Definition fexteq
           {A} (R:ArgRel A) R' (a:A) (AL:list A) E Z s E' Z' s' := 
  forall VL VL' L L',
    R a VL VL' 
    -> simL' bot2 R R' AL L L' 
    -> length Z = length VL
    -> length Z' = length VL'
    -> paco2 (@psimapx F.state _ F.state _) bot2 (L, E[Z <-- VL], s) 
            (L', E'[Z' <-- VL'], s').

(*
Lemma fexteq_sym E Z s E' Z' s' 
: fexteq E Z s E' Z' s' <-> fexteq E' Z' s' E Z s.
Proof.
  unfold fexteq; intuition.
  - eapply sim_sym, H, simL_sym; eauto; congruence.
  - eapply sim_sym, H, simL_sym; eauto; congruence.
Qed.
*)
(*
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
*)

(*
Lemma subst_lemma_L A R (a:A) AL s s' V E E' Z Z' L1 L2 t
: fexteq R a AL E Z s E' Z' s'
  -> length Z = length Z'
  -> simL R AL L1 L2
  -> sim (F.blockI E Z s :: L1, V, t)
         (F.blockI E' Z' s' :: L2, V, t').
*)

Lemma simL_mon (r r0:rel2 F.state (fun _ : F.state => F.state)) A R R' L1 L2 (AL:list A) L1' L2'
:  AIR5 (simB r R R') L1 L2 AL L1' L2'
  -> (forall x0 x1 : F.state, r x0 x1 -> r0 x0 x1)
  -> L1 = L1'  
  -> L2 = L2' 
  ->  AIR5 (simB r0 R R') L1 L2 AL L1' L2'.
Proof.
  intros. general induction H; eauto using AIR5.
  econstructor; eauto.
  inv pf. econstructor; eauto.
  intros. eapply paco2_mon; eauto. 
Qed.



Lemma subst_lemma A R R' (ROK:RelsOk R R') (a:A) AL s s' V V' E E' Z Z' L1 L2 t t' 
: fexteq' R R' a (a::AL) E Z s E' Z' s'
  -> R' a Z Z'
  -> simL' bot2 R R' AL L1 L2
  -> (forall r (L L' : list F.block),
       simL' r R R' (a :: AL) L L' ->
       paco2 (@psimapx F.state _ F.state _) r (L, V, t) (L', V', t'))
  -> paco2 (@psimapx F.state _ F.state _) bot2 (F.blockI E Z s :: L1, V, t)
         (F.blockI E' Z' s' :: L2, V', t').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H3.
  econstructor. econstructor; eauto.
  intros. pfold.
  econstructor; try eapply plusO. 
  econstructor; eauto using get; simpl. edestruct ROK; eauto.
  eapply omap_length in H. congruence.
  econstructor; eauto using get; simpl. edestruct ROK; eauto.
  eapply omap_length in H4. congruence.
  simpl. 
  right. eapply CIH; eauto.
  intros. eapply H0; eauto.
  edestruct ROK; eauto.
  edestruct ROK; eauto.
  eapply simL_mon; eauto. intros; isabsurd.
Qed.

Lemma subst_lemma' r A R R' (ROK:RelsOk R R') (a:A) AL s s' V V' E E' Z Z' L1 L2 t t' 
: fexteq' R R' a (a::AL) E Z s E' Z' s'
  -> R' a Z Z'
  -> simL' r R R' AL L1 L2
  -> (forall r (L L' : list F.block),
       simL' r R R' (a :: AL) L L' ->
       paco2 (@psimapx F.state _ F.state _) r (L, V, t) (L', V', t'))
  -> paco2 (@psimapx F.state _ F.state _) r (F.blockI E Z s :: L1, V, t)
         (F.blockI E' Z' s' :: L2, V', t').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H3.
  econstructor. econstructor; eauto.
  intros. pfold.
  econstructor; try eapply plusO. 
  econstructor; eauto using get; simpl. edestruct ROK; eauto.
  eapply omap_length in H. congruence.
  econstructor; eauto using get; simpl. edestruct ROK; eauto.
  eapply omap_length in H4. congruence.
  simpl. 
  right. eapply CIH; eauto.
  intros. eapply H0; eauto.
  edestruct ROK; eauto.
  edestruct ROK; eauto.
  eapply simL_mon; eauto.
Qed.


Lemma simL_def A (R:ArgRel A) R' a (AL:list A) E0 E'0 Y Y' Yv Y'v
  : 
    omap (exp_eval E0) Y = Some Yv
    -> omap (exp_eval E'0) Y' = Some Y'v
    -> R a Yv Y'v
    -> forall (r : rel2 F.state (fun _ : F.state => F.state))
        (L0 L'0 : list F.block),
        simL' r R R' (a :: AL) L0 L'0 ->
        paco2 (@psimapx F.state _ F.state _) r (L0, E0, stmtGoto (LabI 0) Y)
              (L'0, E'0, stmtGoto (LabI 0) Y').

Proof.
  intros. inv H2.
  inv pf.
  eapply H4; eauto.
Qed.

(*
If we could prove this lemma, we could jail paco in this file.
As long as we have no proof, every transformation must be generalized
by the relation that appears in the definition of psimapxd.

Lemma fexteq_def A R R' (a:A) AL E Z s E' Z' s'
 : fexteq R R' a (a::AL) E Z s E' Z' s'
   -> fexteq' R R' a (a::AL) E Z s E' Z' s'.
Proof.
  unfold fexteq, fexteq'; intros.
  assert (exists L L', simL' bot2 R R' (a::AL) L L').
  destruct H4 as [L1 [L2 ]]. specialize (H _ _ _ _ H0 H4 H2 H3).
  pinversion H. subst.
  
  eapply paco2_mon. eapply H; eauto. eapply simL_mon; eauto.
*)

Lemma simL_extension' r A R R' (ROK:RelsOk R R') (a:A) AL s s' E E' Z Z' L L'
: simL' r R R' AL L L' 
  -> fexteq' R R' a (a::AL) E Z s E' Z' s'
  -> R' a Z Z'
  -> simL' r R R' (a::AL) (F.blockI E Z s :: L) (F.blockI E' Z' s' :: L').
Proof.
  intros.
  hnf; intros. econstructor; eauto. econstructor; eauto; intros.
  + eapply subst_lemma'; eauto.
    eapply simL_def; eauto.
Qed.

(*
Lemma simL_extension A R R' (ROK:RelsOk R R') (a:A) AL s s' E E' Z Z' L L'
: simL' bot2 R R' AL L L' 
  -> fexteq R R' a (a::AL) E Z s E' Z' s'
  -> R' a Z Z'
  -> simL' bot2 R R' (a::AL) (F.blockI E Z s :: L) (F.blockI E' Z' s' :: L').
Proof.
  intros.
  hnf; intros. econstructor; eauto. econstructor; eauto; intros.
  + eapply subst_lemma; eauto. eapply fexteq_def; eauto. 
    eapply simL_def; eauto.
Qed.
*)

Lemma get_drop_lab0 (L:F.labenv) l blk
:  get L (counted l) blk
   -> get (drop (labN l) L) (counted (LabI 0)) blk.
Proof.
  intros. eapply drop_get; simpl. orewrite (labN l + 0 = labN l); eauto.
Qed.

Lemma drop_get_lab0 (L:F.labenv) l blk
: get (drop (labN l) L) (counted (LabI 0)) blk
  -> get L (counted l) blk.
Proof.
  intros. eapply get_drop in H; simpl in *. orewrite (labN l + 0 = labN l) in H; eauto.
Qed.

Lemma sim_drop_shift r l L E Y L' E' Y'
: paco2 (@psimapx F.state _ F.state _) r (drop (labN l) L, E, stmtGoto (LabI 0) Y)
        (drop (labN l) L', E', stmtGoto (LabI 0) Y')
  -> paco2 (@psimapx F.state _ F.state _) r (L, E, stmtGoto l Y)
          (L', E', stmtGoto l Y').
Proof.
  intros. pinversion H; subst.
  eapply plus_destr in H0.
  eapply plus_destr in H1.
  destruct H0; destruct H1; dcr. inv H3.
  simpl in *. inv H1; simpl in *.
  pfold. econstructor; try eapply star_plus.
  econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
  econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
  eauto.
  inv H1; inv H2; simpl in *.
  pfold. econstructor 2; try eapply star_refl; eauto. stuck.
  eapply H3. econstructor. 
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  stuck. eapply H4. econstructor.
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  pfold. inv H5. econstructor 2. 
  Focus 2. eapply star_refl.
  Focus 2. econstructor 2. 
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  eauto. simpl; eauto. stuck.
  eapply H3. econstructor.
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  eauto.
  pfold. inv H5. econstructor 2. 
  Focus 2. econstructor 2. 
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  eauto. 
  Focus 2. eapply star_refl.
  simpl; eauto. eauto. stuck.
  eapply H4. econstructor.
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  pfold. inv H5. inv H7. econstructor 2. 
  Focus 2. econstructor 2. 
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  eauto. 
  Focus 2. econstructor 2. 
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  eauto. eauto. eauto. eauto.
  inv H1. pfold. econstructor 3; try eapply star_refl; eauto.
  stuck. destruct H2. econstructor. econstructor.
  eapply drop_get. simpl. orewrite (labN l + 0 = labN l).
  eauto. eauto. eauto. reflexivity. 
  pfold. econstructor 3; eauto.
  inv H3; simpl in *.
  econstructor.
  econstructor. eapply get_drop in Ldef.
  orewrite (labN l + 0 = labN l) in Ldef. eauto. eauto. eauto. reflexivity.
  eauto.
  eapply psimapxd_mon.
Qed.




(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)

