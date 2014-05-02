Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL ParamsMatch Sim SimApx Alpha Coherence Fresh.

Require Import Liveness.

Set Implicit Arguments.
Unset Printing Records.

Opaque compute_prop.

Fixpoint compile (s:stmt) (a:ann (set var)) :=
  match s, a with
    | stmtExp x e s, annExp lv an => 
      if [x ∈ getAnn an] then stmtExp x e (compile s an)
                         else compile s an
    | stmtIf x s t, annIf _ ans ant => stmtIf x (compile s ans) (compile t ant)
    | stmtGoto f Y, annGoto lv => 
      stmtGoto f (List.filter (fun y => B[y ∈ lv]) Y) 
    | stmtReturn x, annReturn _ => stmtReturn x
    | stmtLet Z s t, annLet lv ans ant => 
      stmtLet (List.filter (fun x => B[x ∈ getAnn ans]) Z)
              (compile s ans) (compile t ant)
    | s, _ => s
  end.

Definition ArgRel (G:(set var * params)) (VL VL': list val) : Prop := 
  VL' = (filter_by (fun x => B[x ∈ (fst G)]) (snd G) VL) /\
  length (snd G) = length VL.

Definition ParamRel (G:(set var * params)) (Z Z' : list var) : Prop := 
  Z' = (List.filter (fun x => B[x ∈ (fst G)]) Z) /\ snd G = Z.

Lemma lookup_list_filter_by_commute A B C (V:A->B) (Z:list C) Y p
: length Z = length Y 
  -> lookup_list V (filter_by p Z Y) =
    filter_by p Z (lookup_list V Y).
Proof.
  intros. eapply length_length_eq in H. 
  general induction H; simpl; eauto.
  + destruct if; simpl; rewrite IHlength_eq; eauto.
Qed.

Lemma argsLive_filter_length lv blv Z Y
: argsLive lv blv Y Z
  -> length (List.filter (fun x : var => B[x ∈ blv]) Z) =
    length (List.filter (fun y : var => B[y ∈ lv]) Y).
Proof.
  intros. general induction H; simpl; eauto.
  destruct_prop (z ∈ blv); destruct_prop (y ∈ lv); try tauto; simpl.
  - rewrite IHargsLive; eauto.
Qed.

Lemma filter_incl lv Y
  : of_list (List.filter (fun y : var => B[y ∈ lv]) Y) ⊆ lv.
Proof.
  general induction Y; simpl. 
  - cset_tac; intuition.
  - destruct_prop (a ∈ lv); simpl. cset_tac; intuition. rewrite <- H0; eauto.
    rewrite <- IHY; eauto.
    eauto.
Qed.

Tactic Notation "destruct-if" "in" hyp(H) :=
  match goal with 
    | H : context [if sumbool_bool ?P then _ else _] |- _ => destruct P
    | H : context [if ?P then _ else _] |- _ => destruct P
  end.

Tactic Notation "destruct-if" :=
  match goal with
    | |- context [if (if ?P then true else false) then _ else _] => destruct P
    | |- context [if ?P then _ else _] => destruct P
  end.

Lemma argsLive_filter_filter_by lv blv Y Z
: argsLive lv blv Y Z
  -> List.filter (fun y : var => B[y ∈ lv]) Y
    = filter_by (fun x : var => B[x ∈ blv]) Z Y.
Proof.
  intros. general induction H; simpl; eauto.
  repeat destruct-if; try tauto.
  rewrite IHargsLive; eauto.
Qed.

Lemma agree_on_update_filter lv (V:var -> val) Z VL 
: length Z = length VL
  -> agree_on lv 
             (V [Z <-- VL])
             (V [List.filter (fun x => B[x ∈ lv]) Z <--
                             filter_by (fun x => B[x ∈ lv]) Z VL]).
Proof.
  intros. eapply length_length_eq in H.
  general induction H.
  - eapply agree_on_refl.
  - simpl. repeat destruct-if. simpl. eapply agree_on_update_same.
    eapply agree_on_incl. eapply IHlength_eq. cset_tac; intuition.
    eapply agree_on_update_dead; eauto.
Qed.

Lemma agree_on_update_filter' (lv:set var) (V V':var -> val) Z VL 
: length Z = length VL
  -> agree_on (lv \ of_list Z) V V'
  -> agree_on lv 
             (V [Z <-- VL])
             (V' [List.filter (fun x => B[x ∈ lv]) Z <--
                             filter_by (fun x => B[x ∈ lv]) Z VL]).
Proof.
  intros.
  pose proof (update_with_list_agree _ VL H0 H).
  eapply agree_on_trans. eapply H1.
  eapply agree_on_update_filter. eauto.
Qed.

Lemma filter_filter_by_length {X} {Y} (Z:list X) (VL:list Y) 
: length Z = length VL
  -> forall p, length (List.filter p Z) =
    length (filter_by p Z VL).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl; eauto.
  destruct if; simpl. rewrite IHlength_eq; eauto. eauto.
Qed.

Definition blockRel (AL:list (set var*params)) L (L':F.labenv) := (forall n blk lvZ, get AL n lvZ -> get L n blk -> block_Z blk = snd lvZ).

Lemma plus_is_step_star (X : Type) (R : rel X) x y
: plus R x y -> exists z, R x z /\ star R z y.
Proof.
  intros. general induction H; eauto using star_refl.
  - destruct IHplus; eauto using plus_star.
Qed.

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
  eapply plus_is_step_star in H0.
  eapply plus_is_step_star in H1.
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
  Focus 2. eapply drop_get. simpl. orewrite (labN l + 0 = labN l).
  eauto. eauto. reflexivity. 
  pfold. econstructor 3; eauto.
  inv H3; simpl in *.
  econstructor.
  econstructor. Focus 2. eapply get_drop in Ldef.
  orewrite (labN l + 0 = labN l) in Ldef. eauto. eauto. reflexivity.
  eauto.
  eapply psimapxd_mon.
Qed.

Lemma sim_DVE' r L L' V V' s LV lv
: agree_on (getAnn lv) V V'
-> true_live_sound LV s lv
-> simL' r ArgRel ParamRel LV L L'
-> paco2 (@psimapx F.state _ F.state _) r (L,V, s) (L',V', compile s lv).
Proof.
  general induction s; simpl; inv H0; simpl in * |- *.
  + case_eq (exp_eval V e); intros. destruct if. 
    - pfold. econstructor; try eapply plusO.
      econstructor; eauto.
      econstructor; eauto. instantiate (1:=v).
      erewrite exp_eval_live; eauto using agree_on_sym.
      left. eapply IHs; eauto. eapply agree_on_update_same. 
      eapply agree_on_incl; eauto.
    - eapply simapx_expansion_closed; 
      [ | eapply S_star; [ econstructor; eauto | eapply star_refl ]
        | eapply star_refl]. 
      eapply IHs; eauto. eapply agree_on_update_dead; eauto.
      eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition.
    - pfold. econstructor 3; [| eapply star_refl|]; eauto. stuck.
  + case_eq (val2bool (V x)); intros.
    pfold; econstructor; try eapply plusO.
    econstructor; eauto. econstructor; eauto. 
    rewrite <- H; eauto. left. eapply IHs1; eauto using agree_on_incl.
    pfold; econstructor; try eapply plusO.
    econstructor 3; eauto. econstructor 3; eauto.
    rewrite <- H; eauto. left; eapply IHs2; eauto using agree_on_incl. 
  + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    (* hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
(*    destruct_prop (length Z = length Y). *)
    unfold simL in H1.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr. 
    simpl in *. repeat get_functional; subst.
    inv H16. hnf in H20. dcr; simpl in *. subst bZ.
    eapply sim_drop_shift. eapply H21.
    hnf; intros; simpl. subst. split.
    rewrite <- lookup_list_filter_by_commute.
    exploit argsLive_filter_filter_by; eauto.
    rewrite <- X. eapply lookup_list_agree.
    eapply agree_on_incl; eauto using agree_on_sym.
    eapply filter_incl; eauto. congruence.
    rewrite lookup_list_length; eauto.
    pfold; eapply psimE; try eapply star_refl; eauto; stuck. eauto.
    hnf in H1.
    edestruct AIR5_nth2 as [? [? [? []]]]; eauto; dcr.
    eauto.
  + pfold. econstructor 2; try eapply star_refl.
    simpl. rewrite H; eauto. simpl. 
    stuck. stuck.
  + pfold. econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    simpl. left. eapply IHs2; eauto. 
    - simpl in *; eapply agree_on_incl; eauto.
    - eapply simL_mon; eauto. eapply simL_extension'; eauto.
      hnf; intros. hnf in H3. hnf in H2. dcr; subst.
      split; eauto. eapply filter_filter_by_length; eauto.
      hnf; intros.
      eapply IHs1; eauto.
      * hnf in H2. dcr; subst. simpl.
        eapply agree_on_update_filter'. eauto.
        eapply agree_on_incl; eauto.
      * split; reflexivity.
Qed.

Print Assumptions sim_DVE.

(*           
Lemma sim_DVE L L' V V' s LV lv
: agree_on (getAnn lv) V V'
-> true_live_sound LV s lv
-> simL' r ArgRel ParamRel LV L L'
-> @simapx F.state _ F.state _ (L,V, s) (L',V', compile s lv).
Proof.
  general induction s; simpl; inv H0; simpl in * |- *.
  + case_eq (exp_eval V e); intros. destruct if. 
    - eapply simS; try eapply plusO.
      econstructor; eauto.
      econstructor; eauto. instantiate (1:=v).
      erewrite exp_eval_live; eauto using agree_on_sym.
      eapply IHs; eauto. eapply agree_on_update_same. 
      eapply agree_on_incl; eauto. 
    - eapply simapx_expansion_closed; 
      [ | eapply S_star; [ econstructor; eauto | eapply star_refl ]
        | eapply star_refl].
      eapply IHs; eauto. eapply agree_on_update_dead; eauto.
      eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition.
    - eapply simErr; [| eapply star_refl|]; eauto. stuck.
  + case_eq (val2bool (V x)); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto. econstructor; eauto. 
    rewrite <- H; eauto. eapply IHs1; eauto using agree_on_incl.
    eapply simS; try eapply plusO.
    econstructor 3; eauto. econstructor 3; eauto.
    rewrite <- H; eauto. eapply IHs2; eauto using agree_on_incl.
  + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
(*    hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
    destruct_prop (length Z = length Y). 
    unfold simL in H1.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr. 
    simpl in *. repeat get_functional; subst.
    inv H16. hnf in H20. dcr; simpl in *. subst bZ.
    eapply simS; try eapply plusO.
    econstructor; eauto. simpl. congruence.
    econstructor; eauto. simpl. hnf in H21. dcr. simpl in *. subst.
    simpl.  
    eapply argsLive_filter_length; eauto.
    simpl in * |- *.
    unfold updE. eapply H21.
    hnf. simpl. 
    rewrite <- lookup_list_filter_by_commute.
    exploit argsLive_filter_filter_by; eauto.
    rewrite <- X. eapply lookup_list_agree.
    eapply agree_on_incl; eauto using agree_on_sym.
    eapply filter_incl; eauto.
    congruence.
    rewrite lookup_list_length; congruence.
    subst. rewrite lookup_list_length.
    eapply argsLive_filter_length; eauto.
    eapply simE; try eapply star_refl; eauto; stuck.
    eapply simE; try eapply star_refl; eauto; stuck; eauto.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    simpl in *. repeat get_functional; subst.

  + eapply simE; try eapply star_refl.
    simpl. rewrite H; eauto. simpl. 
    stuck. stuck.
  + econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    simpl. eapply IHs2; eauto. 
    - simpl in *; eapply agree_on_incl; eauto.
    - eapply simL_extension; eauto. hnf; intros.
      eapply IHs1; eauto.
      * hnf in H2. subst. simpl.
        eapply agree_on_update_filter'. eauto.
        eapply agree_on_incl; eauto.
      * split; reflexivity.
Qed.
*)

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
