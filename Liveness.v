Require Import List Map Env AllInRel Exp MoreExp Rename.
Require Import IL Annotation InRel AutoIndTac .

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
