Require Import AllInRel List Map Env ParamsMatch DecSolve.
Require Import IL Annotation AutoIndTac Sim Exp MoreExp Filter.

Set Implicit Arguments.

Local Hint Resolve incl_empty minus_incl incl_right incl_left.


Inductive argsLive (Caller Callee:set var) : args -> params -> Prop :=
| AL_nil : argsLive Caller Callee nil nil
| AL_cons y z Y Z 
  : argsLive Caller Callee Y Z 
    -> (z ∈ Callee <-> live_exp_sound y Caller)
    -> argsLive Caller Callee (y::Y) (z::Z).

Lemma argsLive_length lv bv Y Z
  : argsLive lv bv Y Z
  -> length Y = length Z.
Proof.
  intros. general induction H; simpl; eauto.
Qed.

Lemma argsLive_liveSound lv blv Y Z
: argsLive lv blv Y Z
  -> forall (n : nat) (y : exp),
      get (filter_by (fun y : var => B[y ∈ blv]) Z Y) n y ->
      live_exp_sound y lv.
Proof.
      intros. general induction H; simpl in * |- *.
      - isabsurd.
      - decide (z ∈ blv); eauto. 
        inv H1; eauto. eapply H0; eauto.
Qed.

Lemma argsLive_live_exp_sound lv blv Y Z y z n
: argsLive lv blv Y Z
  -> get Y n y
  -> get Z n z
  -> z ∈ blv
  -> live_exp_sound y lv.
Proof.
  intros. general induction n; inv H0; inv H1; inv H; intuition; eauto.
Qed.

Lemma argsLive_agree_on' (V E E':onv val) lv blv Y Z v v'
:  argsLive lv blv Y Z
 -> agree_on lv E E'
 -> omap (exp_eval E) Y = Some v
 -> omap (exp_eval E') Y = Some v'
 -> agree_on blv (V [Z <-- List.map Some v]) (V [Z <-- List.map Some v']).
Proof.
  intros. general induction H; simpl in * |- *; eauto using agree_on_refl.
  monad_inv H2. monad_inv H3.
  decide (z ∈ blv).
  - erewrite <- exp_eval_live in EQ0; eauto. 
    + assert (x1 = x) by congruence.
      subst. simpl. 
      eauto using agree_on_update_same, agree_on_incl.
    + eapply H0; eauto.
  - eapply agree_on_update_dead_both; eauto.
Qed.

(* TODO: replace lemma in lib with this *)
Lemma update_with_list_agree X Y `{OrderedType X} `{Equivalence Y} lv (E E':X -> Y) XL YL
: agree_on (lv\of_list XL) E E'
  -> length XL = length YL
  -> agree_on lv (E [ XL <-- YL]) (E' [ XL <-- YL ]).
Proof.
  intros. eapply length_length_eq in H2.
  general induction XL; simpl in * |- *.
  - rewrite (@minus_empty _ _ lv) in H1; eauto.
  - inv H2. eapply agree_on_update_same.
    eapply IHXL; eauto. rewrite minus_union; eauto.
    rewrite add_union_singleton. rewrite (empty_union_2 (s:=∅)); eauto.
    rewrite <- add_union_singleton; eauto.
    eapply SetInterface.empty_1.
Qed.

Lemma argsLive_agree_on (V V' E E':onv val) lv blv Y Z v v'
: agree_on (blv \ of_list Z) V V'
  -> argsLive lv blv Y Z
  -> agree_on lv E E'
  -> omap (exp_eval E) Y = Some v
  -> omap (exp_eval E') Y = Some v'
  -> agree_on blv (V [Z <-- List.map Some v]) (V' [Z <-- List.map Some v']).
Proof.
  intros. etransitivity; eauto using argsLive_agree_on'. 
  eapply update_with_list_agree; eauto.
  exploit omap_length; eauto. exploit argsLive_length; eauto. 
  rewrite map_length; congruence.
Qed.

Inductive live_sound : list (set var*params) -> stmt -> ann (set var) -> Prop :=
| LOpr x Lv b lv e (al:ann (set var))
  :  live_sound Lv b al
  -> live_exp_sound e lv
  -> (getAnn al\{{x}}) ⊆ lv
  -> live_sound Lv (stmtExp x e b) (ann1 lv al)
| LIf Lv e b1 b2 lv al1 al2
  :  live_sound Lv b1 al1
  -> live_sound Lv b2 al2
  -> live_exp_sound e lv
  -> getAnn al1 ⊆ lv
  -> getAnn al2 ⊆ lv
  -> live_sound Lv (stmtIf e b1 b2) (ann2 lv al1 al2)
| LGoto l Y Lv lv blv Z
  : get Lv (counted l) (blv,Z)
  -> (blv \ of_list Z) ⊆ lv
  -> length Y = length Z
  -> (forall n y, get Y n y -> live_exp_sound y lv)
  -> live_sound Lv (stmtGoto l Y) (ann0 lv)
| LReturn Lv e lv
  : live_exp_sound e lv
  -> live_sound Lv (stmtReturn e) (ann0 lv)
| LLet Lv s Z b lv als alb
  : live_sound ((getAnn als,Z)::Lv) s als
  -> live_sound ((getAnn als,Z)::Lv) b alb
  -> (of_list Z) ⊆ getAnn als
  -> (getAnn als \ of_list Z) ⊆ lv
  -> getAnn alb ⊆ lv
  -> live_sound Lv (stmtLet Z s b)(ann2 lv als alb).

Lemma live_sound_annotation Lv s slv
: live_sound Lv s slv -> annotation s slv.
Proof.
  intros. general induction H; econstructor; eauto.
Qed.

Lemma live_sound_monotone LV LV' s lv
: live_sound LV s lv
  -> PIR2 (fun lvZ lvZ' => fst lvZ' ⊆ fst lvZ /\ snd lvZ = snd lvZ') LV LV'
  -> live_sound LV' s lv.
Proof.
  intros. general induction H; simpl; eauto using live_sound.
  - edestruct PIR2_nth; eauto; dcr; simpl in *. 
    destruct x; subst; simpl in *.
    econstructor; eauto. cset_tac; intuition.
  - econstructor; eauto 20 using PIR2.
    eapply IHlive_sound1. econstructor; intuition. 
    eapply IHlive_sound2. econstructor; intuition.
Qed.

Lemma live_sound_monotone2 LV s lv a
: live_sound LV s lv
  -> getAnn lv ⊆ a
  -> live_sound LV s (setTopAnn lv a).
Proof.
  intros. general induction H; simpl in * |- *; eauto using live_sound, live_exp_sound, Subset_trans.
  - econstructor; eauto using live_exp_sound_incl.
    etransitivity; eauto.
  - econstructor; eauto using live_exp_sound_incl; etransitivity; eauto.
  - econstructor; eauto. cset_tac; intuition. 
    intros; eauto using live_exp_sound_incl.
  - econstructor; eauto using live_exp_sound_incl; etransitivity; eauto.
  - econstructor; eauto. cset_tac; intuition. cset_tac; intuition.
Qed.

Lemma freeVars_live s lv Lv
  : live_sound Lv s lv -> IL.freeVars s ⊆ getAnn lv.
Proof.
  intros. general induction H; simpl; eauto using Exp.freeVars_live.
  + exploit Exp.freeVars_live; eauto.
    cset_tac; intuition. eapply H1.
    cset_tac; intuition. 
  + cset_tac; intuition. exploit Exp.freeVars_live; eauto.
  + eapply list_union_incl; eauto.
    intros. 
    edestruct map_get_4; eauto; dcr; subst.
    exploit Exp.freeVars_live; eauto. 
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
  + econstructor; eauto using live_exp_rename_sound.
    rewrite getAnn_mapAnn. 
    cset_tac; eqs; simpl; eauto. eapply lookup_set_incl; eauto.
    eapply lookup_set_spec; eauto.
    eapply lookup_set_spec in H3; eauto. destruct H3; dcr; eauto.
    eexists x0; intuition. cset_tac; eauto. intro. eapply H2. 
    rewrite <- H3; eauto.
  + econstructor; eauto using live_exp_rename_sound.
    rewrite getAnn_mapAnn. eapply lookup_set_incl; eauto.
    rewrite getAnn_mapAnn. eapply lookup_set_incl; eauto.
  + pose proof (map_get_1 (live_rename_L_entry ϱ) H). 
    econstructor; eauto. rewrite of_list_lookup_list; eauto.
    simpl. eapply Subset_trans. eapply lookup_set_minus_incl; eauto. 
    eapply lookup_set_incl; eauto. simpl.
    repeat rewrite lookup_list_length; eauto. rewrite map_length; eauto.
    intros. edestruct map_get_4; eauto; dcr; subst.
    eapply live_exp_rename_sound; eauto.
  + econstructor; eauto using live_exp_rename_sound.
  + econstructor; eauto; try rewrite getAnn_mapAnn; eauto.
    eapply IHlive_sound1. eapply IHlive_sound2.
    rewrite of_list_lookup_list; eauto. eapply lookup_set_incl; eauto. 
    rewrite of_list_lookup_list; eauto.
    eapply Subset_trans. eapply lookup_set_minus_incl; eauto.
    eapply lookup_set_incl; eauto. 
    eapply lookup_set_incl; eauto.
Qed.

Inductive true_live_sound : list (set var *params) -> stmt -> ann (set var) -> Prop :=
| TLOpr x Lv b lv e al
  :  true_live_sound Lv b al
  -> (x ∈ getAnn al -> live_exp_sound e lv)
  -> (getAnn al\{{x}}) ⊆ lv
(*  -> (x ∉ getAnn al -> lv ⊆ getAnn al \ {{x}}) *)
  -> true_live_sound Lv (stmtExp x e b) (ann1 lv al)
| TLIf Lv e b1 b2 lv al1 al2
  :  true_live_sound Lv b1 al1
  -> true_live_sound Lv b2 al2
  -> live_exp_sound e lv
  -> getAnn al1 ⊆ lv
  -> getAnn al2 ⊆ lv
  -> true_live_sound Lv (stmtIf e b1 b2) (ann2 lv al1 al2)
| TLGoto l Y Lv lv blv Z
  : get Lv (counted l) (blv,Z)
  -> (blv \ of_list Z) ⊆ lv
  -> argsLive lv blv Y Z
  -> length Y = length Z
  -> true_live_sound Lv (stmtGoto l Y) (ann0 lv)
| TLReturn Lv e lv
  : live_exp_sound e lv
  -> true_live_sound Lv (stmtReturn e) (ann0 lv)
| TLLet Lv s Z b lv als alb
  : true_live_sound ((getAnn als,Z)::Lv) s als
  -> true_live_sound ((getAnn als,Z)::Lv) b alb
  -> (getAnn als \ of_list Z) ⊆ lv
  -> getAnn alb ⊆ lv
  -> true_live_sound Lv (stmtLet Z s b)(ann2 lv als alb).

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
    + eapply IHlength_eq; eauto using get. cset_tac; intuition.
    + cset_tac; intuition. eauto using get.
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
  freeVarSimFI (E E':onv val) L L' s 
  (LA: PIR2 approxF L L')
  (AG:agree_on (IL.freeVars s) E E')
  : freeVarSimF (L, E, s) (L', E', s).



Lemma freeVarSimF_sim σ1 σ2
  : freeVarSimF σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros. 
  destruct H; destruct s; simpl; simpl in *.
  - case_eq (exp_eval E e); intros.
    + exploit exp_eval_agree; eauto. eauto using agree_on_incl.
      one_step. 
      eapply freeVarSimF_sim. econstructor; eauto.
      eapply agree_on_update_same; eauto using agree_on_incl.
    + exploit exp_eval_agree; eauto using agree_on_incl.
      no_step.
  - case_eq (exp_eval E e); intros.
    exploit exp_eval_agree; eauto using agree_on_incl.
    case_eq (val2bool v); intros.
    + one_step; eauto using agree_on_incl, freeVarSimF.
    + one_step; eauto using agree_on_incl, freeVarSimF.
    + exploit exp_eval_agree; eauto using agree_on_incl.
      no_step.
  - destruct (get_dec L (counted l)) as [[[Eb Zb sb]]|].
    provide_invariants_P2.
    decide (length Zb = length Y).
    case_eq (omap (exp_eval E) Y); intros.
    + exploit omap_exp_eval_agree; eauto.
      one_step.
      simpl. eapply freeVarSimF_sim. econstructor; eauto. 
      eapply update_with_list_agree; eauto. 
      exploit omap_length; eauto. rewrite map_length; congruence.
    + exploit omap_exp_eval_agree; eauto.
      no_step; get_functional; subst. 
    + no_step; get_functional; subst; simpl in *; congruence.
    + no_step; eauto. 
      edestruct PIR2_nth_2; eauto; dcr; eauto.
  - no_step. simpl. erewrite exp_eval_agree; eauto using agree_on_sym.
  - one_step.
    eapply freeVarSimF_sim; econstructor; eauto.
    econstructor; eauto using agree_on_incl. 
    econstructor; eauto using agree_on_incl. 
    eapply agree_on_incl; eauto. 
Qed.

Inductive approxF' : list (set var * params) -> F.block -> F.block -> Prop :=
  approxFI' DL E E' Z s lv
  : live_sound ((getAnn lv, Z)::DL) s lv
    -> agree_on (getAnn lv \ of_list Z) E E'
    ->  approxF' ((getAnn lv,Z)::DL) (F.blockI E Z s) (F.blockI E' Z s).

Inductive liveSimF : F.state -> F.state -> Prop :=
  liveSimFI (E E':onv val) L L' s Lv lv 
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

Inductive approxI 
  : list (set var * params) -> I.block -> I.block -> Prop :=
  approxII DL Z s lv
  : live_sound ((getAnn lv, Z)::DL) s lv
    ->  approxI ((getAnn lv,Z)::DL) (I.blockI Z s) (I.blockI Z s).

Inductive liveSimI : I.state -> I.state -> Prop :=
  liveSimII (E E':onv val) L s Lv lv 
  (LS:live_sound Lv s lv)
  (LA:AIR3 approxI Lv L L)
  (AG:agree_on (getAnn lv) E E')
  : liveSimI (L, E, s) (L, E', s).

Lemma liveSimI_sim σ1 σ2
  : liveSimI σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros. 
  destruct H; inv LS; simpl; simpl in *.
  - case_eq (exp_eval E e); intros.
    + exploit exp_eval_live_agree; eauto.
      one_step.
      eapply liveSimI_sim. econstructor; eauto.
      eapply agree_on_update_same; eauto using agree_on_incl.
    + exploit exp_eval_live_agree; eauto.
      no_step.
  - case_eq (exp_eval E e); intros.
    exploit exp_eval_live_agree; eauto.
    case_eq (val2bool v); intros.
    one_step.
    eapply liveSimI_sim; econstructor; eauto using agree_on_incl.
    one_step.
    eapply liveSimI_sim; econstructor; eauto using agree_on_incl.
    exploit exp_eval_live_agree; eauto.
    no_step.
  - provide_invariants_3.
    case_eq (omap (exp_eval E) Y); intros.
    + exploit omap_exp_eval_live_agree; eauto.
      one_step; simpl; try congruence.
      simpl. eapply liveSimI_sim. econstructor; eauto.
      eapply update_with_list_agree; eauto using agree_on_incl.
      exploit omap_length; eauto. rewrite map_length. congruence.
    + exploit omap_exp_eval_live_agree; eauto.
      no_step.
  - no_step. simpl. eapply exp_eval_live; eauto.
  - one_step.
    eapply liveSimI_sim; econstructor; eauto.
    econstructor; eauto using agree_on_incl. 
    econstructor; eauto using agree_on_incl. 
    eapply agree_on_incl; eauto.
Qed.

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
