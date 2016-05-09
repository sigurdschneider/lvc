Require Import AllInRel List Map Env DecSolve InRel.
Require Import IL Annotation AutoIndTac BisimI BisimF Exp MoreExp Rename.

Set Implicit Arguments.

Notation "DL \\ ZL" := (zip (@lminus _ _) DL ZL) (at level 50).

Local Hint Resolve incl_empty minus_incl incl_right incl_left.

(** * Liveness *)

(** We have two flavors of liveness: functional and imperative. See comments in inductive definition [live_sound]. *)

Inductive overapproximation : Set
  := Functional | Imperative | FunctionalAndImperative.

Definition isFunctional (o:overapproximation) :=
  match o with
    | Functional => true
    | FunctionalAndImperative => true
    | _ => false
  end.

Definition isImperative (o:overapproximation) :=
  match o with
    | Imperative => true
    | FunctionalAndImperative => true
    | _ => false
  end.

(** ** Inductive Definition of Liveness *)

Inductive live_sound (i:overapproximation) : list (set var*params) -> stmt -> ann (set var) -> Prop :=
| LOpr x Lv b lv e (al:ann (set var))
  :  live_sound i Lv b al
  -> live_exp_sound e lv
  -> (getAnn al\ singleton x) ⊆ lv
  -> x ∈ getAnn al
  -> live_sound i Lv (stmtLet x e b) (ann1 lv al)
| LIf Lv e b1 b2 lv al1 al2
  :  live_sound i Lv b1 al1
  -> live_sound i Lv b2 al2
  -> live_exp_sound e lv
  -> getAnn al1 ⊆ lv
  -> getAnn al2 ⊆ lv
  -> live_sound i Lv (stmtIf e b1 b2) (ann2 lv al1 al2)
| LGoto l Y Lv lv blv Z
  : get Lv (counted l) (blv,Z) (** Imperative Liveness requires the globals of a function to be live at the call site *)
  -> (if isImperative i then ((blv \ of_list Z) ⊆ lv) else True)
  -> length Y = length Z
  -> (forall n y, get Y n y -> live_exp_sound y lv)
  -> live_sound i Lv (stmtApp l Y) (ann0 lv)
| LReturn Lv e lv
  : live_exp_sound e lv
  -> live_sound i Lv (stmtReturn e) (ann0 lv)
| LExtern x Lv b lv Y al f
  :  live_sound i Lv b al
  -> (forall n y, get Y n y -> live_exp_sound y lv)
  -> (getAnn al\ singleton x) ⊆ lv
  -> x ∈ getAnn al
  -> live_sound i Lv (stmtExtern x f Y b) (ann1 lv al)
| LLet Lv F b lv als alb
  : live_sound i (zip pair (getAnn ⊝ als) (fst ⊝ F) ++ Lv) b alb
    -> length F = length als
  -> (forall n Zs a, get F n Zs ->
               get als n a ->
               live_sound i (zip pair (getAnn ⊝ als) (fst ⊝ F) ++ Lv) (snd Zs) a)
  -> (forall n Zs a, get F n Zs ->
               get als n a ->
               (of_list (fst Zs)) ⊆ getAnn a
               /\ (if isFunctional i then (getAnn a \ of_list (fst Zs)) ⊆ lv else True))
  -> getAnn alb ⊆ lv
  -> live_sound i Lv (stmtFun F b)(annF lv als alb).


(** ** Relation between different overapproximations *)

Lemma live_sound_overapproximation_I Lv s slv
: live_sound FunctionalAndImperative Lv s slv -> live_sound Imperative Lv s slv.
Proof.
  intros. general induction H; simpl in * |- *; econstructor; simpl; eauto.
  - intros. edestruct H3; eauto.
Qed.

Lemma live_sound_overapproximation_F Lv s slv
: live_sound FunctionalAndImperative Lv s slv -> live_sound Functional Lv s slv.
Proof.
  intros. general induction H; simpl in * |- *; econstructor; simpl; eauto.
Qed.

(** ** [live_sound] ensures that the annotation matches the program *)
Lemma live_sound_annotation i Lv s slv
: live_sound i Lv s slv -> annotation s slv.
Proof.
  intros. general induction H; econstructor; eauto.
Qed.

(** ** Some monotonicity properties *)

Definition live_ann_subset (lvZ lvZ' : set var * list var) :=
  match lvZ, lvZ' with
    | (lv,Z), (lv',Z') => lv' ⊆ lv /\ Z = Z'
  end.

Instance live_ann_subset_refl : Reflexive live_ann_subset.
hnf; intros. destruct x; firstorder.
Qed.

Lemma live_sound_monotone i LV LV' s lv
: live_sound i LV s lv
  -> PIR2 live_ann_subset LV LV'
  -> live_sound i LV' s lv.
Proof.
  intros. general induction H; simpl; eauto using live_sound.
  - edestruct PIR2_nth; eauto; dcr; simpl in *.
    destruct x; subst; simpl in *.
    econstructor; eauto.
    cases; simpl in *; eauto; dcr; subst.
    rewrite <- H0. rewrite <- H4. reflexivity.
    cset_tac; eauto.
  - econstructor; eauto 20 using PIR2_app.
Qed.

Lemma live_sound_monotone2 i LV s lv a
: live_sound i LV s lv
  -> getAnn lv ⊆ a
  -> live_sound i LV s (setTopAnn lv a).
Proof.
  intros. general induction H; simpl in * |- *; eauto using live_sound, live_exp_sound, Subset_trans.
  - econstructor; eauto using live_exp_sound_incl.
    etransitivity; eauto.
  - econstructor; eauto using live_exp_sound_incl; etransitivity; eauto.
  - econstructor; eauto using live_exp_sound_incl.
    destruct i; simpl; eauto; rewrite <- H3; eauto.
  - econstructor; eauto using live_exp_sound_incl; etransitivity; eauto.
  - econstructor; eauto using live_exp_sound_incl.
    etransitivity; eauto.
  - econstructor; eauto. intros. edestruct H3; eauto.
    destruct i; simpl; eauto; cset_tac.
    cset_tac.
Qed.

(** ** Live variables always contain the free variables *)

Lemma incl_incl_minus X `{OrderedType X} s t u v
  : t \ u ⊆ v -> s ⊆ t -> s \ u ⊆ v.
Proof.
  intros A B. rewrite B; eauto.
Qed.

Lemma incl_minus_exp_live_union s t e v
  : s \ t ⊆ v -> live_exp_sound e v -> s \ t ∪ Exp.freeVars e ⊆ v.
Proof.
  intros. eauto using Exp.freeVars_live with cset.
Qed.

Hint Resolve incl_incl_minus incl_minus_exp_live_union : cset.

Lemma freeVars_live s lv Lv
  : live_sound Functional Lv s lv -> IL.freeVars s ⊆ getAnn lv.
Proof.
  intros.
  induction H; simpl.
  - eauto using Exp.freeVars_live with cset.
  - eauto using Exp.freeVars_live with cset.
  - eapply list_union_incl; eauto.
    intros. inv_map H3.
    eauto using Exp.freeVars_live with cset.
  - eauto using Exp.freeVars_live with cset.
  - rewrite (list_union_incl (s':=lv)); eauto with cset.
    intros ? ? GET. inv_map GET.
    eauto using Exp.freeVars_live with cset.
  - eapply union_subset_3.
    + eapply list_union_incl; intros; eauto.
      inv_map H5. edestruct (get_length_eq _ H6 H0); eauto.
      edestruct H3; eauto. simpl in *. exploit H2; eauto.
      eauto with cset.
    + rewrite IHlive_sound; eauto.
Qed.

(** ** Liveness is stable under renaming *)

Definition live_rename_L_entry (ϱ:env var) (x:set var * params)
 := (lookup_set ϱ (fst x), lookup_list ϱ (snd x)).

Definition live_rename_L (ϱ:env var) DL
  := List.map (live_rename_L_entry ϱ) DL.

Lemma live_rename_L_globals ϱ als F
: length F = length als
  -> live_rename_L ϱ (zip pair (getAnn ⊝ als) (fst ⊝ F)) =
    zip pair
        (getAnn ⊝ (List.map (mapAnn (lookup_set ϱ)) als))
        (fst ⊝ (List.map (fun Zs0 => (lookup_list ϱ (fst Zs0), rename ϱ (snd Zs0))) F)).
Proof.
  intros. length_equify. general induction H; simpl; eauto.
  - f_equal; eauto. rewrite getAnn_mapAnn; reflexivity.
Qed.

Lemma live_rename_L_app ϱ L L'
: live_rename_L ϱ (L ++ L') = live_rename_L ϱ L ++ live_rename_L ϱ L'.
Proof.
  unfold live_rename_L. rewrite map_app; reflexivity.
Qed.

Lemma live_rename_sound i DL s an (ϱ:env var)
: live_sound i DL s an
  -> live_sound i (live_rename_L ϱ DL) (rename ϱ s) (mapAnn (lookup_set ϱ) an).
Proof.
  intros. general induction H; simpl.
  - econstructor; eauto using live_exp_rename_sound.
    + rewrite getAnn_mapAnn.
      rewrite <- lookup_set_singleton'; eauto.
      rewrite lookup_set_minus_incl; eauto.
      eapply lookup_set_incl; eauto.
    + rewrite getAnn_mapAnn.
      eapply lookup_set_spec; eauto.
  - econstructor; eauto using live_exp_rename_sound.
    + rewrite getAnn_mapAnn. eapply lookup_set_incl; eauto.
    + rewrite getAnn_mapAnn. eapply lookup_set_incl; eauto.
  - pose proof (map_get_1 (live_rename_L_entry ϱ) H).
    econstructor; eauto.
    + destruct i; simpl in * |- *; eauto.
      rewrite of_list_lookup_list; eauto.
      eapply Subset_trans. eapply lookup_set_minus_incl; eauto.
      eapply lookup_set_incl; eauto. simpl.
      rewrite of_list_lookup_list; eauto.
      eapply Subset_trans. eapply lookup_set_minus_incl; eauto.
      eapply lookup_set_incl; eauto.
    + simpl.
      repeat rewrite lookup_list_length; eauto. rewrite map_length; eauto.
    + intros. edestruct map_get_4; eauto; dcr; subst.
      eapply live_exp_rename_sound; eauto.
  - econstructor; eauto using live_exp_rename_sound.
  - econstructor; intros; eauto using live_exp_rename_sound.
    + edestruct map_get_4; eauto; dcr; subst.
      eapply live_exp_rename_sound; eauto.
    + rewrite getAnn_mapAnn.
      rewrite lookup_set_minus_single_incl; eauto.
      eapply lookup_set_incl; eauto.
    + rewrite getAnn_mapAnn; eauto. eapply lookup_set_spec; eauto.
  - econstructor; eauto; try rewrite getAnn_mapAnn; eauto.
    + rewrite <- live_rename_L_globals, <- live_rename_L_app; eauto.
    + repeat rewrite map_length; eauto.
    + intros. inv_map H5. inv_map H6.
      rewrite <- live_rename_L_globals, <- live_rename_L_app; eauto.
      eapply H2; eauto.
    + intros. inv_map H6; inv_map H5.
      exploit H3; eauto; dcr. simpl.
      assert (Proper (_eq ==> _eq) ϱ) by eapply Proper_eq_fun.
      split.
      * rewrite of_list_lookup_list; eauto.
        rewrite getAnn_mapAnn.
        eapply lookup_set_incl; eauto.
      * cases; eauto.
        rewrite getAnn_mapAnn.
        rewrite of_list_lookup_list; eauto.
        rewrite lookup_set_minus_incl; eauto.
        eapply lookup_set_incl; eauto.
    + eapply lookup_set_incl; eauto.
Qed.

(** ** For functional programs, only free variables are significant *)

Inductive approxF :  F.block -> F.block -> Prop :=
 | approxFI E E' Z s n
    : agree_on eq (IL.freeVars s \ of_list Z) E E'
    ->  approxF (F.blockI E Z s n) (F.blockI E' Z s n).

Unset Printing Records.

Require Import SetOperations.

Lemma mkBlocks_approxF s0 E E' s i
: agree_on eq (list_union
                 (List.map
                    (fun f : params * stmt =>
                       IL.freeVars (snd f) \ of_list (fst f)) s) ∪ IL.freeVars s0) E E'
  -> PIR2 approxF (mapi_impl (F.mkBlock E) i s) (mapi_impl (F.mkBlock E') i s).
Proof.
  intros.
  general induction s; eauto using PIR2. simpl.
  - econstructor. econstructor.
    eapply agree_on_incl; eauto.
    rewrite <- get_list_union_map; eauto using get.
    eapply IHs.
    eapply agree_on_incl; eauto. simpl.
    norm_lunion. clear_all; cset_tac.
Qed.


Inductive freeVarSimF : F.state -> F.state -> Prop :=
  freeVarSimFI (E E':onv val) L L' s
  (LA: PIR2 approxF L L')
  (AG:agree_on eq (IL.freeVars s) E E')
  : freeVarSimF (L, E, s) (L', E', s).

Lemma freeVarSimF_sim σ1 σ2
  : freeVarSimF σ1 σ2 -> bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; destruct s; simpl; simpl in *.
  - case_eq (exp_eval E e); intros.
    + exploit exp_eval_agree; eauto. eauto using agree_on_incl.
      one_step.
      eapply freeVarSimF_sim. econstructor; eauto.
      eapply agree_on_update_same; eauto using agree_on_incl with cset.
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
      eapply PIR2_drop; eauto.
      eapply update_with_list_agree; eauto.
      exploit omap_length; eauto. rewrite map_length; congruence.
    + exploit omap_exp_eval_agree; eauto.
      no_step; get_functional; subst.
    + no_step; get_functional; subst; simpl in *; congruence.
    + no_step; eauto.
      edestruct PIR2_nth_2; eauto; dcr; eauto.
  - no_step. simpl. erewrite exp_eval_agree; eauto. symmetry; eauto.
  - case_eq (omap (exp_eval E) Y); intros.
    exploit omap_exp_eval_agree; eauto using agree_on_incl.
    extern_step.
    + exploit omap_exp_eval_agree; eauto using agree_on_incl.
    + exploit omap_exp_eval_agree.
      * symmetry. eauto using agree_on_incl.
      * eauto.
      * eapply freeVarSimF_sim. econstructor; eauto.
        eapply agree_on_update_same; eauto using agree_on_incl with cset.
    + exploit omap_exp_eval_agree; eauto. symmetry; eauto using agree_on_incl with cset.
    + exploit omap_exp_eval_agree.
      * symmetry. eauto using agree_on_incl.
      * eauto.
      * eapply freeVarSimF_sim. econstructor; eauto.
        eapply agree_on_update_same; eauto using agree_on_incl with cset.
    + no_step.
      symmetry in AG.
      exploit omap_exp_eval_agree; eauto using agree_on_incl.
      congruence.
  - one_step.
    eapply freeVarSimF_sim; econstructor; eauto using agree_on_incl.
    eapply PIR2_app; eauto. eapply mkBlocks_approxF; eauto.
Qed.

(** ** Since live variables contain free variables, liveness contains all variables significant to an IL/F program *)

Inductive approxF' : list (set var * params) -> F.block -> F.block -> Prop :=
  approxFI' DL E E' Z s lv n
  : live_sound Functional ((getAnn lv, Z)::DL) s lv
    -> agree_on eq (getAnn lv \ of_list Z) E E'
    ->  approxF' ((getAnn lv,Z)::DL) (F.blockI E Z s n) (F.blockI E' Z s n).

Inductive liveSimF : F.state -> F.state -> Prop :=
  liveSimFI (E E':onv val) L L' s Lv lv
            (LS:live_sound Functional Lv s lv)
            (LA:AIR3 approxF' Lv L L')
            (AG:agree_on eq (getAnn lv) E E')
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

(** ** Live variables contain all variables significant to an IL/I program *)

Inductive approxI
  : list (set var * params) -> list I.block -> list I.block -> set var * params -> I.block -> I.block -> Prop :=
  approxII DL Z s lv n L L'
  : live_sound Imperative DL s lv
    ->  approxI DL L L' (getAnn lv,Z) (I.blockI Z s n) (I.blockI Z s n).

Inductive liveSimI : I.state -> I.state -> Prop :=
  liveSimII (E E':onv val) L s Lv lv
  (LS:live_sound Imperative Lv s lv)
  (LA:inRel approxI Lv L L)
  (AG:agree_on eq (getAnn lv) E E')
  : liveSimI (L, E, s) (L, E', s).

Lemma approx_mutual_block alF F Lv i L L'
:
  length alF = length F
  ->  (forall (n : nat) Zs (als : ann (set var)),
        get F n Zs ->
        get alF n als -> live_sound Imperative Lv (snd Zs) als)
  -> mutual_block (approxI Lv L L') i (zip pair (getAnn ⊝ alF) (fst ⊝ F))
                 (mapi_impl I.mkBlock i F) (mapi_impl I.mkBlock i F).
Proof.
  unfold mapi.
  intros. length_equify.
  general induction H; simpl.
  - econstructor.
  - econstructor; eauto.
    + eapply IHlength_eq; intros; eauto using get.
    + destruct y. eauto using approxI, get.
Qed.

Lemma liveSimI_sim σ1 σ2
  : liveSimI σ1 σ2 -> bisim σ1 σ2.
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
  - inRel_invs.
    case_eq (omap (exp_eval E) Y); intros.
    + exploit omap_exp_eval_live_agree; eauto.
      one_step; simpl; try congruence.
      simpl. eapply liveSimI_sim. econstructor; eauto.
      eapply (inRel_drop LA G).
      eapply update_with_list_agree; eauto using agree_on_incl with len.
      exploit omap_length; eauto. rewrite map_length. congruence.
    + exploit omap_exp_eval_live_agree; eauto.
      no_step.
  - no_step. simpl. eapply exp_eval_live; eauto.
  - case_eq (omap (exp_eval E) Y); intros;
    exploit omap_exp_eval_live_agree; eauto.
    extern_step.
    + exploit omap_exp_eval_live_agree; eauto.
    + eapply liveSimI_sim; econstructor; eauto.
      eapply agree_on_update_same; eauto using agree_on_incl.
    + symmetry in AG. exploit omap_exp_eval_live_agree; eauto.
    + eapply liveSimI_sim; econstructor; eauto.
      eapply agree_on_update_same; eauto using agree_on_incl.
    + no_step.
  - one_step.
    eapply liveSimI_sim; econstructor; eauto using agree_on_incl.
    + econstructor; eauto using agree_on_incl.
      eapply approx_mutual_block; eauto.
Qed.
