Require Import List Map Env AllInRel Exp MoreExp Rename.
Require Import IL Annotation InRel AutoIndTac .

Set Implicit Arguments.

Notation "DL \\ ZL" := (zip (fun s L => s \ of_list L) DL ZL) (at level 50).

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

Inductive live_sound (i:overapproximation)
  : list params -> list (set var) -> stmt -> ann (set var) -> Prop :=
| LOpr ZL Lv x e s lv (al:ann (set var))
  :  live_sound i ZL Lv s al
     -> live_exp_sound e lv
     -> (getAnn al \ singleton x) ⊆ lv
     -> x ∈ getAnn al
     -> live_sound i ZL Lv (stmtLet x e s) (ann1 lv al)
| LIf Lv ZL e s1 s2 lv al1 al2
  :  live_sound i ZL Lv s1 al1
     -> live_sound i ZL Lv s2 al2
     -> live_exp_sound e lv
     -> getAnn al1 ⊆ lv
     -> getAnn al2 ⊆ lv
     -> live_sound i ZL Lv (stmtIf e s1 s2) (ann2 lv al1 al2)
| LGoto ZL Lv l Y lv blv Z
  : get ZL (counted l) Z
    -> get Lv (counted l) blv
    (** Imperative Liveness requires the globals of a function to be live at the call site *)
    -> (if isImperative i then ((blv \ of_list Z) ⊆ lv) else True)
    -> length Y = length Z
    -> (forall n y, get Y n y -> live_exp_sound y lv)
    -> live_sound i ZL Lv (stmtApp l Y) (ann0 lv)
| LReturn ZL Lv e lv
  : live_exp_sound e lv
    -> live_sound i ZL Lv (stmtReturn e) (ann0 lv)
| LExternZL ZL Lv x f Y s lv al
  :  live_sound i ZL Lv s al
     -> (forall n y, get Y n y -> live_exp_sound y lv)
     -> (getAnn al \ singleton x) ⊆ lv
     -> x ∈ getAnn al
     -> live_sound i ZL Lv (stmtExtern x f Y s) (ann1 lv al)
| LLet ZL Lv F t lv als alb
  : live_sound i (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) t alb
    -> length F = length als
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 live_sound i (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 (of_list (fst Zs)) ⊆ getAnn a
                 /\ (if isFunctional i then (getAnn a \ of_list (fst Zs)) ⊆ lv else True))
    -> getAnn alb ⊆ lv
    -> live_sound i ZL Lv (stmtFun F t)(annF lv als alb).


(** ** Relation between different overapproximations *)

Lemma live_sound_overapproximation_I ZL Lv s slv
: live_sound FunctionalAndImperative ZL Lv s slv -> live_sound Imperative ZL Lv s slv.
Proof.
  intros. general induction H; simpl in * |- *; econstructor; simpl; eauto.
  - intros. edestruct H3; eauto.
Qed.

Lemma live_sound_overapproximation_F ZL Lv s slv
: live_sound FunctionalAndImperative ZL Lv s slv -> live_sound Functional ZL Lv s slv.
Proof.
  intros. general induction H; simpl in * |- *; econstructor; simpl; eauto.
Qed.

(** ** [live_sound] ensures that the annotation matches the program *)
Lemma live_sound_annotation i ZL Lv s slv
: live_sound i ZL Lv s slv -> annotation s slv.
Proof.
  intros. general induction H; econstructor; eauto.
Qed.

(** ** Some monotonicity properties *)


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

Hint Resolve incl_minus_lr : cset.

Lemma live_sound_monotone i ZL LV LV' s lv
: live_sound i ZL LV s lv
  -> PIR2 Subset LV' LV
  -> live_sound i ZL LV' s lv.
Proof.
  intros. general induction H; simpl; eauto using live_sound.
  - PIR2_inv.
    econstructor; eauto.
    cases; eauto with cset.
  - econstructor; eauto using PIR2_app.
Qed.

Lemma live_sound_monotone2 i ZL LV s lv a
: live_sound i ZL LV s lv
  -> getAnn lv ⊆ a
  -> live_sound i ZL LV s (setTopAnn lv a).
Proof.
  intros. general induction H; simpl in * |- *;
            eauto using live_sound, live_exp_sound_incl, Subset_trans with cset.
  - econstructor; eauto using live_exp_sound_incl.
    cases; eauto with cset.
  - econstructor; eauto with cset.
    + intros. edestruct H3; eauto.
      cases; eauto with cset.
Qed.

(** ** Live variables always contain the free variables *)

Lemma freeVars_live_list Y lv
  : (forall (n : nat) (y : exp), get Y n y -> live_exp_sound y lv)
    -> list_union (Exp.freeVars ⊝ Y) ⊆ lv.
Proof.
  intros H. eapply list_union_incl; intros; inv_get; eauto using Exp.freeVars_live.
Qed.

Lemma freeVars_live s lv ZL Lv
  : live_sound Functional ZL Lv s lv -> IL.freeVars s ⊆ getAnn lv.
Proof.
  intros.
  induction H; simpl; eauto using Exp.freeVars_live, freeVars_live_list with cset.
  - eapply union_subset_3; eauto with cset.
    + eapply list_union_incl; intros; inv_get; eauto.


      edestruct H3; eauto; simpl in *. exploit H2; eauto.
      eauto with cset.
Qed.

(** ** Liveness is stable under renaming *)

Lemma live_rename_sound i ZL Lv s an (ϱ:env var)
: live_sound i ZL Lv s an
  -> live_sound i (lookup_list ϱ ⊝ ZL) (lookup_set ϱ ⊝ Lv) (rename ϱ s) (mapAnn (lookup_set ϱ) an).
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
  - econstructor; eauto with len.
    + cases; eauto.
      rewrite of_list_lookup_list; eauto.
      etransitivity. eapply lookup_set_minus_incl; eauto.
      eapply lookup_set_incl; eauto.
    + rewrite lookup_list_length; eauto with len.
    + intros; inv_get; eauto using live_exp_rename_sound.
  - econstructor; eauto using live_exp_rename_sound.
  - econstructor; eauto using live_exp_rename_sound.
    + intros; inv_get; eauto using live_exp_rename_sound.
    + rewrite getAnn_mapAnn.
      rewrite lookup_set_minus_single_incl; eauto.
      eapply lookup_set_incl; eauto.
    + rewrite getAnn_mapAnn; eauto. eapply lookup_set_spec; eauto.
  - econstructor; eauto; try rewrite getAnn_mapAnn; eauto with len.
    + repeat rewrite map_map; simpl. rewrite <- map_map.
      rewrite <- map_app.
      setoid_rewrite getAnn_mapAnn.
      setoid_rewrite <- map_map at 3. rewrite <- map_app. eauto.
    + intros; inv_get. simpl.
      repeat rewrite map_map; simpl. rewrite <- map_map.
      rewrite <- map_app.
      setoid_rewrite getAnn_mapAnn.
      setoid_rewrite <- map_map at 3. rewrite <- map_app. eauto.
    + intros; inv_get; simpl.
      exploit H3; eauto; dcr. simpl.
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