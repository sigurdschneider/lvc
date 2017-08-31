Require Import List Map Env AllInRel Exp Rename.
Require Import IL Annotation AutoIndTac MoreListSet.

Export MoreListSet.

Set Implicit Arguments.

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
     -> live_op_sound e lv
     -> getAnn al1 ⊆ lv
     -> getAnn al2 ⊆ lv
     -> live_sound i ZL Lv (stmtIf e s1 s2) (ann2 lv al1 al2)
| LGoto ZL Lv l Y lv blv Z
  : get ZL (counted l) Z
    -> get Lv (counted l) blv
    (** Imperative Liveness requires the globals of a function to be live at the call site *)
    -> (if isImperative i then ((blv \ of_list Z) ⊆ lv) else True)
    -> length Y = length Z
    -> (forall n y, get Y n y -> live_op_sound y lv)
    -> live_sound i ZL Lv (stmtApp l Y) (ann0 lv)
| LReturn ZL Lv e lv
  : live_op_sound e lv
    -> live_sound i ZL Lv (stmtReturn e) (ann0 lv)
| LLet ZL Lv F t lv als alb
  : live_sound i (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) t alb
    -> length F = length als
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 live_sound i (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 (of_list (fst Zs)) ⊆ getAnn a
                 /\ NoDupA eq (fst Zs)
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
            eauto using live_sound, live_op_sound_incl,
            live_exp_sound_incl, Subset_trans with cset.
  - econstructor; eauto using live_op_sound_incl.
    cases; eauto with cset.
  - econstructor; eauto with cset.
    + intros. edestruct H3; dcr; eauto.
      cases; eauto with cset.
Qed.

(** ** Live variables always contain the free variables *)

Lemma freeVars_live s lv ZL Lv
  : live_sound Functional ZL Lv s lv -> IL.freeVars s ⊆ getAnn lv.
Proof.
  intros.
  induction H; simpl; eauto using Exp.freeVars_live, Op.freeVars_live,
                      Op.freeVars_live_list with cset.
  - eapply union_subset_3; eauto with cset.
    + eapply list_union_incl; intros; inv_get; eauto.
      edestruct H3; dcr; eauto; simpl in *. exploit H2; eauto.
      eauto with cset.
Qed.

Lemma adapt_premise F als lv
: (forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
   get F n Zs ->
   get als n a ->
   of_list (fst Zs) ⊆ getAnn a /\ NoDupA eq (fst Zs) /\ getAnn a \ of_list (fst Zs) ⊆ lv)
  -> forall (n0 : nat) (Zs0 : params * stmt) (a : ann ⦃var⦄),
    get F n0 Zs0 -> get als n0 a -> of_list (fst Zs0) ⊆ getAnn a /\ getAnn a \ of_list (fst Zs0) ⊆ lv.
Proof.
  intros A; intros; edestruct A; dcr; eauto.
Qed.

Hint Resolve adapt_premise.

Lemma live_globals_zip (F:〔params*stmt〕) (als:〔ann ⦃var⦄〕) DL ZL (LEN1:length F = length als)
  : zip pair (getAnn ⊝ als) (fst ⊝ F) ++ zip pair DL ZL =
    zip pair (List.map getAnn als ++ DL) (List.map fst F ++ ZL).
Proof with eauto with len.
  rewrite zip_app...
Qed.

Lemma PIR2_Subset_tab_extend AP DL ZL (F:list (params*stmt)) als
  : PIR2 Subset AP (DL \\ ZL)
    -> ❬F❭ = ❬als❭
    -> PIR2 Subset (tab {} ‖F‖ ++ AP) ((getAnn ⊝ als ++ DL) \\ (fst ⊝ F ++ ZL)).
Proof.
  intros P LEN.
  rewrite zip_app; eauto using PIR2_length with len.
  eapply PIR2_app; eauto.
  eapply PIR2_get; try (intros ? ? ? GET; inv_map GET); eauto with cset len.
Qed.

Lemma live_sound_ann_ext ZL Lv s lv lv'
  : ann_R Equal lv lv'
    -> live_sound Imperative ZL Lv s lv
    -> live_sound Imperative ZL Lv s lv'.
Proof.
  intros annR lvSnd.
  general induction lvSnd; inversion_clear annR.
  - econstructor; eauto; apply ann_R_get in H3.
    + apply live_exp_sound_incl with (lv':=lv); eauto.
      rewrite H2. reflexivity.
    + rewrite <- H3. rewrite <- H2. eauto.
    + rewrite <- H3. eauto.
  - econstructor; eauto;
      apply ann_R_get in H3;
      apply ann_R_get in H4;
      try rewrite <- H2;
      try rewrite <- H3;
      try rewrite <- H4;
      eauto.
  - econstructor; simpl; intros; eauto;
      try rewrite <- H4; eauto.
  - econstructor; simpl; intros; eauto;
      try rewrite <- H0; eauto.
  - apply ann_R_get in H7 as H7'.
    assert (PIR2 Subset (getAnn ⊝ bns ++ Lv) (getAnn ⊝ als ++ Lv))
      as pir2_als_bns.
    { apply PIR2_app.
      - apply PIR2_get; eauto with len.
        intros; inv_get.
        exploit H6 as EQ; eauto.
        eapply ann_R_get in EQ. rewrite EQ. reflexivity.
      - apply PIR2_refl; eauto.
    }
    econstructor; simpl; eauto;
      try rewrite <- H0; eauto.
    + apply live_sound_monotone with (LV:=getAnn ⊝ als ++ Lv); eauto.
    + rewrite <- H5. eauto.
    + intros. inv_get.
      apply live_sound_monotone with (LV:=getAnn ⊝ als ++ Lv); eauto.
    + intros. simpl in H2. inv_get.
      exploit H6 as EQ; eauto.
      apply ann_R_get in EQ.
      rewrite <- EQ.
      apply H2 with (n:=n); eauto.
    + rewrite <- H4. rewrite <- H7'. eauto.
Qed.
