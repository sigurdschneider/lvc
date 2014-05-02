Require Import AllInRel List Map Env IL AutoIndTac Sim Exp.
Require Export ParamsMatch DecSolve.

Set Implicit Arguments.

Inductive argsLive (Caller Callee:set var) : args -> params -> Prop :=
| AL_nil : argsLive Caller Callee nil nil
| AL_cons y z Y Z : argsLive Caller Callee Y Z -> (z ∈ Callee <-> y ∈ Caller) -> 
  argsLive Caller Callee (y::Y) (z::Z).

Lemma argsLive_length lv bv Y Z
  : argsLive lv bv Y Z
  -> length Y = length Z.
Proof.
  intros. general induction H; simpl; eauto.
Qed.


Instance argsLive_dec Caller Callee Y Z
      : Computable (argsLive Caller Callee Y Z).
Proof.
  constructor. destruct_prop(length Y = length Z).
  eapply length_length_eq in e. general induction e.
  left; econstructor. 
  destruct_prop(y ∈ Callee <-> x ∈ Caller);
  edestruct (IHe Caller Callee); try dec_solve; try eassumption; try inv an; eauto; try tauto.
  right; intro. eapply argsLive_length in H. congruence.
Qed.

Lemma argsLive_Z_incl lv blv Y Z
  : argsLive lv blv Y Z 
  -> of_list Z ⊆ blv
  -> of_list Y ⊆ lv.
Proof.  
  intros. general induction H; simpl. eapply incl_empty.
  simpl in H. 
  apply subset_add_3; eauto. eapply H0. eapply H1. eapply add_1; eauto.
  eapply IHargsLive. rewrite <- H1. eapply subset_add_2. reflexivity.
Qed.

 
Lemma params_live_args_live Y Z bv lv
  : argsLive lv bv Y Z
  -> of_list Z ⊆ bv
  -> of_list Y ⊆ lv. 
Proof.
  induction 1; simpl; intros; hnf; intros. cset_tac; intuition.
  eapply add_iff in H2; destruct H2. 
  rewrite <- H2; intuition. 
  eapply IHargsLive; eauto. cset_tac; intuition.
Qed.

Lemma argsLive_get_live (bv lv:set var) Z Y x y n
  : getT Z n x -> getT Y n y
  -> argsLive lv bv Y Z
  -> x ∈ bv 
  -> y ∈ lv.
Proof.
  intros X. revert Y y.
  induction X; intros. 
  inv X.
  inv H; intuition.
  inv X0; inv H; eauto.
Qed.

(*
Lemma argsLive_arg (bv lv:live) Z Y x n
  : getT Z n x 
  -> argsLive lv bv Y Z
  -> x ∈ bv 
  -> { y:var & (get Y n y * (y ∈ lv))%type }.
Proof.
  intros X. revert Y.
  induction X; intros. 
  inv H. eexists; eauto using get.
  inv X0. edestruct IHX as [y' [A B]]; eauto.
  eexists; eauto using get.
Qed.
*)

Lemma argsLive_agree_on (E1:env val) E1' E E' lv blv Y Z
:  agree_on (blv \ of_list Z) E1 E1'
 -> agree_on lv E E'
 -> argsLive lv blv Y Z
 -> length Z = length Y
 -> agree_on blv (E1 [Z <-- lookup_list E Y])
           (E1' [Z <-- lookup_list E' Y]).
Proof.
  intros. 
  hnf; intros; simpl.
  eapply length_length_eq in H2.
  destruct_prop (x ∈ of_list Z).
  clear H.
  general induction H2. unfold of_list in i; simpl in i; exfalso; cset_tac; eauto.
  simpl. lud. eapply H0. inv H1. eapply H9. rewrite e. eauto.
  inv H1. eapply IHlength_eq; eauto. simpl in *; cset_tac; intuition.
  repeat rewrite update_with_list_no_update; eauto. eapply H.
  cset_tac; eauto.
Qed.

Inductive live_sound : list (set var*params) -> stmt -> ann (set var) -> Prop :=
| LOpr x Lv b lv e (al:ann (set var))
  :  live_sound Lv b al
  -> live_exp_sound e lv
  -> (getAnn al\{{x}}) ⊆ lv
  -> live_sound Lv (stmtExp x e b) (annExp lv al)
| LIf Lv x b1 b2 lv al1 al2
  :  live_sound Lv b1 al1
  -> live_sound Lv b2 al2
  -> x ∈ lv
  -> getAnn al1 ⊆ lv
  -> getAnn al2 ⊆ lv
  -> live_sound Lv (stmtIf x b1 b2) (annIf lv al1 al2)
| LGoto l Y Lv lv blv Z
  : get Lv (counted l) (blv,Z)
  -> (blv \ of_list Z) ⊆ lv
  -> length Y = length Z
  -> of_list Y ⊆ lv 
  -> live_sound Lv (stmtGoto l Y) (annGoto lv)
| LReturn Lv x lv
  : x ∈ lv
  -> live_sound Lv (stmtReturn x) (annReturn lv)
| LLet Lv s Z b lv als alb
  : live_sound ((getAnn als,Z)::Lv) s als
  -> live_sound ((getAnn als,Z)::Lv) b alb
  -> (of_list Z) ⊆ getAnn als
  -> (getAnn als \ of_list Z) ⊆ lv
  -> getAnn alb ⊆ lv
  -> live_sound Lv (stmtLet Z s b)(annLet lv als alb).

Lemma live_sound_annotation Lv s slv
: live_sound Lv s slv -> annotation s slv.
Proof.
  intros. general induction H; econstructor; eauto.
Qed.

Lemma freeVars_live s lv Lv
  : live_sound Lv s lv -> IL.freeVars s ⊆ getAnn lv.
Proof.
  intros. general induction H; simpl; eauto. 
  + cset_tac; intuition. eapply H1. cset_tac; eauto. 
    eapply freeVars_live; eauto.
  + cset_tac; intuition. rewrite H5; eauto. 
  + cset_tac; eauto.
  + eapply union_subset_3.
    rewrite IHlive_sound1; eauto.
    rewrite IHlive_sound2; eauto.
Qed.

Definition live_rename_L_entry (ϱ:env var) (x:set var * params)
 := (lookup_set ϱ (fst x), lookup_list ϱ (snd x)).

Definition live_rename_L (ϱ:env var) DL
 := List.map (live_rename_L_entry ϱ) DL.

Lemma live_rename_sound DL s an (ϱ:env var)
: live_sound DL s an 
  -> live_sound (live_rename_L ϱ DL) (rename ϱ s) (mapAnn (lookup_set ϱ) an).
Proof.
  intros. general induction H; simpl.
  + econstructor; eauto.
    eapply live_exp_sound_incl. Focus 2.
    eapply Exp.live_freeVars. 
    eapply Subset_trans.
    eapply rename_exp_freeVars; eauto. intuition.
    eapply lookup_set_incl; eauto. intuition. 
    eapply Exp.freeVars_live; eauto.
    rewrite getAnn_mapAnn. 
    cset_tac; eqs; simpl; eauto. eapply lookup_set_incl; eauto. intuition.
    eapply lookup_set_spec; eauto. intuition. 
    eapply lookup_set_spec in H3; eauto. destruct H3; dcr; eauto.
    eexists x0; intuition. cset_tac; eauto. intro. eapply H2. 
    rewrite <- H3; eauto. intuition.
  + econstructor; eauto. eapply lookup_set_spec; eauto. intuition.
    rewrite getAnn_mapAnn. eapply lookup_set_incl; eauto. intuition.
    rewrite getAnn_mapAnn. eapply lookup_set_incl; eauto. intuition.
  + pose proof (map_get_1 (live_rename_L_entry ϱ) H). 
    econstructor; eauto. rewrite of_list_lookup_list. 
    simpl. eapply Subset_trans. eapply lookup_set_minus_incl. intuition.
    eapply lookup_set_incl; eauto. intuition. intuition. simpl.
    repeat rewrite lookup_list_length; eauto.
    rewrite of_list_lookup_list; try eapply lookup_set_incl; intuition.
  + econstructor. eapply lookup_set_spec. intuition. eexists; intuition; eauto.
  + econstructor; eauto; try rewrite getAnn_mapAnn.
    eapply IHlive_sound1. eapply IHlive_sound2.
    rewrite of_list_lookup_list. eapply lookup_set_incl; eauto. intuition.
    intuition.
    rewrite of_list_lookup_list. 
    eapply Subset_trans. eapply lookup_set_minus_incl. intuition.
    eapply lookup_set_incl; eauto. intuition. intuition.
    eapply lookup_set_incl; eauto. intuition. 
Qed.

Inductive true_live_sound : list (set var *params) -> stmt -> ann (set var) -> Prop :=
| TLOpr x Lv b lv e al
  :  true_live_sound Lv b al
  -> (x ∈ getAnn al -> live_exp_sound e lv)
  -> (getAnn al\{{x}}) ⊆ lv
(*  -> (x ∉ getAnn al -> lv ⊆ getAnn al \ {{x}}) *)
  -> true_live_sound Lv (stmtExp x e b) (annExp lv al)
| TLIf Lv x b1 b2 lv al1 al2
  :  true_live_sound Lv b1 al1
  -> true_live_sound Lv b2 al2
  -> x ∈ lv
  -> getAnn al1 ⊆ lv
  -> getAnn al2 ⊆ lv
  -> true_live_sound Lv (stmtIf x b1 b2) (annIf lv al1 al2)
| TLGoto l Y Lv lv blv Z
  : get Lv (counted l) (blv,Z)
  -> (blv \ of_list Z) ⊆ lv
  -> argsLive lv blv Y Z
  -> length Y = length Z
  -> true_live_sound Lv (stmtGoto l Y) (annGoto lv)
| TLReturn Lv x lv
  : x ∈ lv
  -> true_live_sound Lv (stmtReturn x) (annReturn lv)
| TLLet Lv s Z b lv als alb
  : true_live_sound ((getAnn als,Z)::Lv) s als
  -> true_live_sound ((getAnn als,Z)::Lv) b alb
  -> (getAnn als \ of_list Z) ⊆ lv
  -> getAnn alb ⊆ lv
  -> true_live_sound Lv (stmtLet Z s b)(annLet lv als alb).

Lemma true_live_sound_annotation Lv s slv
: true_live_sound Lv s slv -> annotation s slv.
Proof.
  intros. general induction H; econstructor; eauto.
Qed.

Lemma live_relation Lv s lv
: (forall n lvZ, get Lv n lvZ -> of_list (snd lvZ) ⊆ fst lvZ)
  -> live_sound Lv s lv 
  -> true_live_sound Lv s lv.
Proof.
  intros. general induction H0; eauto using true_live_sound.
  - econstructor; eauto. 
    exploit H3; eauto.
    clear H H0 H3. simpl in *.
    eapply length_length_eq in H1.
    general induction H1; simpl in * |- *; eauto using argsLive.
    econstructor. 
    + eapply IHlength_eq; eauto. cset_tac; intuition.
      cset_tac; intuition.
    + cset_tac; intuition.
  - econstructor; eauto. 
    eapply IHlive_sound1; eauto; intros.
    inv H3; eauto using get.
    eapply IHlive_sound2; eauto; intros.
    inv H3; eauto using get.
Qed.


Inductive approxF :  F.block -> F.block -> Prop :=
 | approxFI E E' Z s
    : agree_on (IL.freeVars s \ of_list Z) E E'
    ->  approxF (F.blockI E Z s) (F.blockI E' Z s).

Unset Printing Records.

Inductive freeVarSimF : F.state -> F.state -> Prop :=
  freeVarSimFI (E E':env val) L L' s 
  (LA: PIR2 approxF L L')
  (AG:agree_on (IL.freeVars s) E E')
  : freeVarSimF (L, E, s) (L', E', s).

Lemma freeVarSimF_sim σ1 σ2
  : freeVarSimF σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros. 
  destruct H; destruct s; simpl; simpl in *.
  + case_eq (exp_eval E e); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto. econstructor; eauto.
    instantiate (1:=v). erewrite <- exp_eval_live; eauto. 
    eapply live_exp_sound_incl; try eapply live_freeVars. cset_tac; eauto.
    eapply freeVarSimF_sim. econstructor; eauto.
    eapply agree_on_update_same; eauto using agree_on_incl.
    eapply agree_on_incl; eauto. cset_tac; eauto.
    eapply simE; try eapply star_refl; eauto; stuck.
    erewrite <- exp_eval_live in def; eauto. congruence.
    eapply live_exp_sound_incl;try eapply live_freeVars; eauto.
    cset_tac; intuition.
  + case_eq (val2bool (E x)); intros.
    eapply simS; try eapply plusO. 
    econstructor; eauto. 
    econstructor. rewrite <- AG; eauto. cset_tac; intuition.
    eapply freeVarSimF_sim; econstructor; eauto using agree_on_incl.
    eapply agree_on_incl; eauto. cset_tac; intuition.
    eapply simS; try eapply plusO.
    eapply F.stepIfF; eauto. 
    rewrite AG in H; eauto.
    eapply F.stepIfF; eauto. cset_tac; intuition.
    eapply freeVarSimF_sim; econstructor; eauto using agree_on_incl.
    eapply agree_on_incl; eauto. cset_tac; intuition.
  + destruct (get_dec L (counted l)) as [[[Eb Zb sb]]|].
    provide_invariants_P2.
    destruct_prop (length Zb = length Y).
    one_step.
    simpl. eapply freeVarSimF_sim. econstructor; eauto.
    unfold updE. 
    erewrite lookup_list_agree; eauto using agree_on_incl.
    eapply update_with_list_agree. eapply agree_on_incl; eauto.
    cset_tac; eauto. rewrite lookup_list_length; simpl in *; congruence.
    no_step; get_functional; subst. simpl in *; congruence.
    simpl in *; congruence.
    no_step. provide_invariants_P2.
    edestruct PIR2_nth_2; eauto; dcr; eauto.
  + eapply simE; try eapply star_refl; simpl; eauto; try stuck.
    rewrite AG; eauto; cset_tac; intuition.
  + eapply simS; try (eapply plusO; econstructor).
    eapply freeVarSimF_sim; econstructor; eauto.
    econstructor; eauto using agree_on_incl. 
    econstructor; eauto using agree_on_incl. 
    eapply agree_on_incl; eauto. cset_tac; intuition.
    eapply agree_on_incl; eauto. cset_tac; intuition.
Qed.

Inductive approxF' : list (set var * params) -> F.block -> F.block -> Prop :=
  approxFI' DL E E' Z s lv
  : live_sound ((getAnn lv, Z)::DL) s lv
    -> agree_on (getAnn lv \ of_list Z) E E'
    ->  approxF' ((getAnn lv,Z)::DL) (F.blockI E Z s) (F.blockI E' Z s).

Inductive liveSimF : F.state -> F.state -> Prop :=
  liveSimFI (E E':env val) L L' s Lv lv 
            (LS:live_sound Lv s lv)
            (LA:AIR3 approxF' Lv L L')
            (AG:agree_on (getAnn lv) E E')
  : liveSimF (L, E, s) (L', E', s).

Lemma liveSim_freeVarSim σ1 σ2
  : liveSimF σ1 σ2 -> freeVarSimF σ1 σ2.
Proof.
  intros. general induction H; econstructor; eauto.
  clear LS. 
  general induction LA; eauto using PIR2.
  econstructor. inv pf. econstructor.
  eapply agree_on_incl; eauto. eapply incl_minus_lr; try reflexivity.
  eapply freeVars_live; eauto.
  eapply IHLA; eauto.
  eapply agree_on_incl; eauto. eapply freeVars_live; eauto.
Qed.
(*
We are going to prove a simapx result about dve instead.
Inductive approxI 
  : list (live*params) -> I.block -> I.block -> Prop :=
  approxII DL Z s lv
  : true_live_sound ((getAnn lv, Z)::DL) s lv
    ->  approxI ((getAnn lv,Z)::DL) (I.blockI Z s) (I.blockI Z s).

Inductive liveSimI : I.state -> I.state -> Prop :=
  liveSimII (E E':env val) L s Lv lv 
  (LS:true_live_sound Lv s lv)
  (LA:AIR3 approxI Lv L L)
  (AG:agree_on (getAnn lv) E E')
  : liveSimI (L, E, s) (L, E', s).

Lemma liveSimI_sim σ1 σ2
  : liveSimI σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros. 
  destruct H; inv LS; simpl; simpl in *.
  + case_eq (exp_eval E e); intros.
    destruct_prop(x ∈ getAnn al).
    eapply simS; try eapply plusO. 
    econstructor; eauto.     econstructor; eauto.
    instantiate (1:=v). erewrite <- exp_eval_live; eauto.
    eapply liveSimI_sim. econstructor; eauto.
    eapply agree_on_update_same; eauto using agree_on_incl.
    case_eq (exp_eval E' e); intros.
    eapply simS; try eapply plusO. 
    econstructor; eauto.     econstructor; eauto.
    eapply liveSimI_sim. econstructor; eauto.
    assert (getAnn al [=] getAnn al \ {{x}}). 
    split; cset_tac; intuition. rewrite H5.
    eapply agree_on_update_dead_both. cset_tac; intuition. 
    eapply agree_on_incl; eauto.
    eapply simE; try eapply star_refl; eauto; stuck.
    erewrite <- exp_eval_live in def; eauto. congruence.
    eapply live_exp_sound_incl;try eapply live_freeVars; eauto.
  + case_eq (val2bool (E x)); intros.
    eapply simS; try eapply plusO. 
    econstructor; eauto. 
    econstructor. rewrite <- AG; eauto.
    eapply liveSimI_sim; econstructor; eauto using agree_on_incl.
    eapply simS; try eapply plusO.
    eapply I.stepIfF; eauto. 
    rewrite AG in H6; eauto.
    eapply I.stepIfF; eauto. 
    eapply liveSimI_sim; econstructor; eauto using agree_on_incl.
  + provide_invariants_3.
    eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; try eapply H7; eauto.
    simpl. eapply liveSimI_sim. econstructor; eauto.
    unfold updE.
    eapply argsLive_agree_on; eauto using agree_on_incl.

  + eapply simE; try eapply star_refl; simpl; eauto; try stuck.

  + eapply simS; try (eapply plusO; econstructor).
    eapply liveSimI_sim; econstructor; eauto.
    econstructor; eauto using agree_on_incl. 
    econstructor; eauto using agree_on_incl. 
    eapply agree_on_incl; eauto.
Qed.

Inductive approxFT 
  : list (live*params) -> I.block -> I.block -> Prop :=
  approxIFT DL Z s lv
  : true_live_sound ((getAnn lv, Z)::DL) s lv
    ->  approxFT ((getAnn lv,Z)::DL) (I.blockI Z s) (I.blockI Z s).

Inductive liveSimFT : I.state -> I.state -> Prop :=
  liveSimIFT (E E':env val) L s Lv lv 
  (LS:true_live_sound Lv s lv)
  (LA:AIR3 approxFT Lv L L)
  (AG:agree_on (getAnn lv) E E')
  : liveSimFT (L, E, s) (L, E', s).

Lemma liveSimFT_sim σ1 σ2
  : liveSimFT σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros. 
  destruct H; inv LS; simpl; simpl in *.
  + case_eq (exp_eval E e); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto. econstructor; eauto.
    instantiate (1:=v). erewrite <- exp_eval_live; eauto. 
    eapply live_exp_sound_incl; try eapply live_freeVars. cset_tac; eauto.
    eapply liveSimFT_sim. econstructor; eauto.
    eapply agree_on_update_same; eauto using agree_on_incl.
    eapply simE; try eapply star_refl; eauto; stuck.
    erewrite <- exp_eval_live in def; eauto. congruence.
    eapply live_exp_sound_incl;try eapply live_freeVars; eauto.
  + case_eq (val2bool (E x)); intros.
    eapply simS; try eapply plusO. 
    econstructor; eauto. 
    econstructor. rewrite <- AG; eauto.
    eapply liveSimFT_sim; econstructor; eauto using agree_on_incl.
    eapply simS; try eapply plusO.
    eapply I.stepIfF; eauto. 
    rewrite AG in H6; eauto.
    eapply I.stepIfF; eauto. 
    eapply liveSimFT_sim; econstructor; eauto using agree_on_incl.
  + provide_invariants_3.
    eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; try eapply H7; eauto.
    simpl. eapply liveSimFT_sim. econstructor; eauto.
    unfold updE.
    eapply argsLive_agree_on; eauto using agree_on_incl.

  + eapply simE; try eapply star_refl; simpl; eauto; try stuck.

  + eapply simS; try (eapply plusO; econstructor).
    eapply liveSimFT_sim; econstructor; eauto.
    econstructor; eauto using agree_on_incl. 
    econstructor; eauto using agree_on_incl. 
    eapply agree_on_incl; eauto.
Qed.
*)
(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
