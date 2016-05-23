Require Import AllInRel List Map Env DecSolve.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp SetOperations.
Require Export Liveness Filter LabelsDefined OUnion.

Set Implicit Arguments.

Local Hint Resolve incl_empty minus_incl incl_right incl_left.

Inductive argsLive (Caller Callee:set var) : args -> params -> Prop :=
| AL_nil : argsLive Caller Callee nil nil
| AL_cons y z Y Z
  : argsLive Caller Callee Y Z
    -> (z ∈ Callee -> live_exp_sound y Caller)
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
    inv H1; eauto.
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
     -> agree_on eq lv E E'
     -> omap (exp_eval E) Y = Some v
     -> omap (exp_eval E') Y = Some v'
     -> agree_on eq blv (V [Z <-- List.map Some v]) (V [Z <-- List.map Some v']).
Proof.
  intros. general induction H; simpl in * |- *; eauto.
  - monad_inv H2. monad_inv H3.
    decide (z ∈ blv).
    +erewrite <- exp_eval_live in EQ0; eauto.
     *  assert (x1 = x) by congruence.
        subst. simpl.
        eauto using agree_on_update_same, agree_on_incl.
    + eapply agree_on_update_dead_both; eauto.
Qed.

Lemma argsLive_agree_on (V V' E E':onv val) lv blv Y Z v v'
  : agree_on eq (blv \ of_list Z) V V'
    -> argsLive lv blv Y Z
    -> agree_on eq lv E E'
    -> omap (exp_eval E) Y = Some v
    -> omap (exp_eval E') Y = Some v'
    -> agree_on eq blv (V [Z <-- List.map Some v]) (V' [Z <-- List.map Some v']).
Proof.
  intros. etransitivity; eauto using argsLive_agree_on'.
  eapply update_with_list_agree; eauto.
  exploit omap_length; eauto. exploit argsLive_length; eauto.
  rewrite map_length; congruence.
Qed.

Lemma filter_by_incl_argsLive lv blv Y Z
  : ❬Y❭ = ❬Z❭
    -> list_union (Exp.freeVars ⊝ filter_by (fun x => if [x \In blv] then true else false) Z Y) ⊆ lv
    -> argsLive lv blv Y Z.
Proof.
  intros LEN INCL. length_equify.
  general induction LEN; simpl in *; eauto using argsLive.
  - econstructor.
    + cases in INCL; try congruence; eauto.
      * eapply IHLEN. rewrite <- INCL.
        simpl List.map. rewrite list_union_cons. eauto with cset.
    + intros. cases in INCL.
      simpl List.map in INCL.
      rewrite list_union_cons in INCL.
      eapply live_exp_sound_incl;[| eapply live_freeVars].
      rewrite <- INCL. eauto with cset.
Qed.

Inductive true_live_sound (i:overapproximation)
  : list params -> list (set var) -> stmt -> ann (set var) -> Prop :=
| TLOpr ZL Lv x b lv e al
  :  true_live_sound i ZL Lv b al
     -> (x ∈ getAnn al -> live_exp_sound e lv)
     -> (getAnn al\{{x}}) ⊆ lv
     -> true_live_sound i ZL Lv (stmtLet x e b) (ann1 lv al)
| TLIf ZL Lv e b1 b2 lv al1 al2
  :  (exp2bool e <> Some false -> true_live_sound i ZL Lv b1 al1)
     -> (exp2bool e <> Some true -> true_live_sound i ZL Lv b2 al2)
     -> (exp2bool e = None -> live_exp_sound e lv)
     -> (exp2bool e <> Some false -> getAnn al1 ⊆ lv)
     -> (exp2bool e <> Some true -> getAnn al2 ⊆ lv)
     -> true_live_sound i ZL Lv (stmtIf e b1 b2) (ann2 lv al1 al2)
| TLGoto ZL Lv l Y lv blv Z
  : get ZL (counted l) Z
    -> get Lv (counted l) blv
    -> (if isImperative i then  (blv \ of_list Z ⊆ lv) else True)
    -> argsLive lv blv Y Z
    -> length Y = length Z
    -> true_live_sound i ZL Lv (stmtApp l Y) (ann0 lv)
| TLReturn ZL Lv e lv
  : live_exp_sound e lv
    -> true_live_sound i ZL Lv (stmtReturn e) (ann0 lv)
| TLExtern ZL Lv x b lv Y al f
  : true_live_sound i ZL Lv b al
    -> (forall n y, get Y n y -> live_exp_sound y lv)
    -> (getAnn al\{{x}}) ⊆ lv
    -> true_live_sound i ZL Lv (stmtExtern x f Y b) (ann1 lv al)
| TLLet ZL Lv F t lv als alt
  : true_live_sound i (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) t alt
    -> length F = length als
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 true_live_sound i (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 if isFunctional i then (getAnn a \ of_list (fst Zs)) ⊆ lv
                 else True)
    -> getAnn alt ⊆ lv
    -> true_live_sound i ZL Lv (stmtFun F t)(annF lv als alt).


Lemma true_live_sound_overapproximation_I ZL Lv s slv
  : true_live_sound FunctionalAndImperative ZL Lv s slv
    -> true_live_sound Imperative ZL Lv s slv.
Proof.
  intros. general induction H; simpl in * |- *; econstructor; simpl; eauto.
Qed.

Lemma true_live_sound_overapproximation_F ZL Lv s slv
  : true_live_sound FunctionalAndImperative ZL Lv s slv
    -> true_live_sound Functional ZL Lv s slv.
Proof.
  intros. general induction H; simpl in * |- *; econstructor; simpl; eauto.
Qed.

(*
Lemma true_live_sound_trueIsCalled i Lv s slv l
  : true_live_sound i Lv s slv
    -> trueIsCalled s l
    -> exists lv Z, get Lv (counted l) (lv, Z).
Proof.
  intros Live IC. destruct l; simpl in *.
  general induction IC; invt true_live_sound; eauto.
  - edestruct IHIC2 as [lv' [Z' ?]]; eauto; simpl in *.
    rewrite get_app_lt in H1; eauto with len. inv_get.
    edestruct IHIC1 as [lv'' [Z'' ?]]; eauto.
    rewrite get_app_ge in H1; eauto with len.
    rewrite zip_length2 in H1; eauto with len.
    rewrite map_length in H1.
    orewrite (❬F❭ + n - ❬als❭ = n) in H1. eauto.
  - edestruct IHIC as [lv' [Z' ?]]; eauto; try reflexivity.
    rewrite get_app_ge in H; eauto with len.
    rewrite zip_length2 in H; eauto with len.
    rewrite map_length in H.
    orewrite (❬F❭ + n - ❬als❭ = n) in H. eauto.
Qed.*)