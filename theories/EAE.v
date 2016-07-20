Require Import CSet Le.
Require Import Plus Util AllInRel Map SetOperations.

Require Import Val EqDec Computable Var Env IL Annotation.
Require Import paco2 SimF Fresh MoreExp.

Set Implicit Arguments.
Unset Printing Records.

Function list_to_stmt (xl: list var) (Y : list exp) (s : stmt) : stmt :=
  match xl, Y with
    | x::xl, e :: Y => stmtLet x e (list_to_stmt xl Y s)
    | _, _ => s
  end.

Section MapUpdate.
  Open Scope fmap_scope.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.

  Fixpoint update_with_list' XL YL (m:X -> Y) :=
    match XL, YL with
      | x::XL, y::YL => update_with_list' XL YL (m[x <- y])
      | _, _ => m
    end.

  Lemma update_unique_commute (XL:list X) (VL:list Y) E D x y
  : length XL = length VL
    -> unique (x::XL)
    -> agree_on eq D (E [x <- y] [XL <-- VL]) (E [XL <-- VL] [x <- y]).
  Proof.
    intros LEN UNIQ. length_equify.
    general induction LEN; simpl in * |- *; dcr; simpl in *; eauto.
    hnf; intros. lud.
    - exfalso; eauto.
    - etransitivity; [eapply IHLEN|]; eauto; lud.
    - etransitivity; [eapply IHLEN|]; eauto; lud.
  Qed.

  Lemma update_with_list_agree' (XL:list X) (VL:list Y) E D
  : length XL = length VL
    -> unique XL
    -> agree_on eq D (E [XL <-- VL]) (update_with_list' XL VL E).
  Proof.
    intros LEN UNIQ. length_equify.
    general induction LEN; simpl in *; eauto.
    - etransitivity. symmetry. eapply update_unique_commute; eauto using length_eq_length.
      eapply IHLEN; eauto.
  Qed.
End MapUpdate.


Lemma list_to_stmt_correct L E s xl Y vl
: length xl = length Y
  -> omap (exp_eval E) Y = Some vl
  -> unique xl
  -> disj (of_list xl) (list_union (List.map Exp.freeVars Y))
  -> star2 F.step (L, E, list_to_stmt xl Y s) nil (L, update_with_list' xl (List.map Some vl) E, s).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl in * |- *.
  - eapply star2_refl.
  - monad_inv H0.
    econstructor 2 with (y:=EvtTau).
    econstructor; eauto.
    simpl. eapply IHlength_eq; eauto.
    + eapply omap_exp_eval_agree; [|eauto].
      symmetry. eapply agree_on_update_dead; [|reflexivity].
      rewrite list_union_start_swap in H2.
      intro. eapply (H2 x); eauto; cset_tac.
    + rewrite list_union_start_swap in H2.
      eapply disj_1_incl; [ eapply disj_2_incl |]; eauto with cset.
Qed.

Lemma list_to_stmt_crash L E s xl Y
: length xl = length Y
  -> omap (exp_eval E) Y = None
  -> unique xl
  -> disj (of_list xl) (list_union (List.map Exp.freeVars Y))
  -> exists σ, star2 F.step (L, E, list_to_stmt xl Y s) nil σ /\ state_result σ = None /\ normal2 F.step σ.
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl in * |- *.
  - monad_inv H0.
    + eexists; repeat split; eauto using star2_refl. stuck2.
    + rewrite list_union_start_swap in H2.
      edestruct (IHlength_eq L (E [x <- Some x0])); eauto.
      * eapply omap_exp_eval_agree; eauto. symmetry.
        eapply agree_on_update_dead; [|reflexivity].
        intro. eapply (H2 x); cset_tac.
      * eapply disj_1_incl; [ eapply disj_2_incl |]; eauto with cset.
      * dcr. eexists. split; eauto.
        econstructor 2 with (y:=EvtTau); eauto.
        econstructor; eauto.
Qed.

Fixpoint compile s {struct s}
  : stmt  :=
  match s with
    | stmtLet x e s => stmtLet x e (compile s)
    | stmtIf x s t => stmtIf x (compile s) (compile t)
    | stmtApp l Y  =>
      if [ forall n e, get Y n e -> isVar e] then
        stmtApp l Y
      else
        let xl := fresh_list fresh (list_union (List.map Exp.freeVars Y)) (length Y) in
        list_to_stmt xl Y (stmtApp l (List.map Var xl))
    | stmtReturn x => stmtReturn x
    | stmtExtern x f Y s => stmtExtern x f Y (compile s)
    | stmtFun F t => stmtFun (List.map (fun Zs => (fst Zs, compile (snd Zs))) F) (compile t)
  end.

Definition ParamRel (G:params) (Z Z' : list var) : Prop :=
  Z = Z' /\ length Z = length G.

Instance SR : ProofRelation params := {
   ParamRel G VL VL' :=   VL = VL' /\ length VL = length G;
   ArgRel G Z Z' := Z = Z' /\ length Z = length G;
   IndexRel AL n n' := n = n';
   Image AL := length AL
}.
- intros; dcr; subst; eauto with len.
- intros; subst; eauto.
Defined.


Lemma omap_lookup_vars V xl vl
  : length xl = length vl
    -> unique xl
    -> omap (exp_eval (V[xl <-- List.map Some vl])) (List.map Var xl) = Some vl.
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl; eauto.
  lud; isabsurd; simpl.
  erewrite omap_exp_eval_agree; try eapply IHlength_eq; eauto; simpl in *; intuition.
  instantiate (1:= V [x <- Some y]).
  eapply update_unique_commute; eauto; simpl; intuition.
Qed.


Lemma sim_EAE' r L L' V s
  : simLabenv Bisim r SR (block_Z ⊝ L) L L'
    -> ❬L❭ = ❬L'❭
    -> sim'r r Bisim (L, V, s) (L',V, compile s).
Proof.
  revert_except s. unfold sim'r.
  sind s; destruct s; simpl; intros; simpl in * |- *.
  - case_eq (exp_eval V e); intros.
    + pone_step; eauto.
    + pno_step.
  - case_eq (exp_eval V e); intros.
    + case_eq (val2bool v); intros;
        pone_step; eauto.
    + pno_step.
  - case_eq (omap (exp_eval V) Y); intros.
    exploit (list_to_stmt_correct L' V (stmtApp l (Var ⊝ fresh_list fresh (list_union (Exp.freeVars ⊝ Y)) ❬Y❭)) (fresh_list fresh (list_union (Exp.freeVars ⊝ Y)) ❬Y❭) Y) as LTSC; eauto using fresh_spec, fresh_list_unique, fresh_list_spec.
    + destruct (get_dec L (counted l)) as [[[bE bZ bs n]]|].
      * hnf in H; dcr. inv_get. destruct x as [bE' bZ' bs' n'].
        decide (length Y = length bZ). {
          cases.
          - eapply H3; eauto. hnf; eauto.
            hnf; eauto with len.
          - eapply sim'_expansion_closed;
              [
              | eapply star2_refl
              | eapply list_to_stmt_correct;
                eauto using fresh_spec, fresh_list_unique, fresh_list_spec
              ]; eauto.
            simpl. eapply H3; eauto.
            hnf; eauto.
            Focus 2.
            eapply omap_exp_eval_agree.
            eapply update_with_list_agree';
              eauto using fresh_list_unique, fresh_spec with len.
            eapply omap_lookup_vars;
              eauto using fresh_list_unique, fresh_spec with len.
            hnf; simpl; eauto with len.
        }
        cases.
        pno_step; simpl in *. exploit H3; eauto; dcr; subst. congruence.
        eapply sim'_expansion_closed; [| eapply star2_refl | eapply LTSC].
        exploit H3; eauto; dcr. hnf; eauto. simpl in *; dcr; subst.
        pno_step. simpl in *.
        eapply n0; rewrite len. rewrite map_length.
        rewrite fresh_list_length. eauto.
      * cases. pno_step; eauto. inv_get; eauto.
        eapply sim'_expansion_closed; [| eapply star2_refl | eapply LTSC].
        pno_step; repeat get_functional; simpl in *.
        exploit H; eauto; dcr. inv_get; eauto.
    + cases. pno_step.
      edestruct (list_to_stmt_crash L' V (stmtApp l (Var ⊝ fresh_list fresh (list_union (Exp.freeVars ⊝ Y)) ❬Y❭)) (fresh_list fresh (list_union (Exp.freeVars ⊝ Y)) ❬Y❭) Y); eauto using fresh_spec, fresh_list_unique, fresh_list_spec; dcr.
      pfold. econstructor 4; [ | eapply star2_refl | eapply H3 | | ]; eauto.
      stuck2.
  - pno_step.
  - case_eq (omap (exp_eval V) Y); intros.
    + pextern_step; eauto.
    + pno_step.
  - pone_step.
    left. eapply IH; eauto 20 with len.
    + rewrite List.map_app.
      eapply simLabenv_extension_len; eauto with len.
      * intros; hnf; intros; inv_get; simpl in *; dcr; subst.
        get_functional. eapply IH; eauto 20 with len.
        rewrite List.map_app. eauto.
      * hnf; intros; simpl in *; subst; inv_get; simpl; eauto.
      * simpl. eauto with len.
Qed.

Lemma sim_EAE V s
: @sim _ statetype_F _ statetype_F Bisim (nil, V, s) (nil,V, compile s).
Proof.
  eapply sim'_sim. eapply sim_EAE'; eauto.
  hnf; intros; split; eauto using @sawtooth with len.
  isabsurd.
Qed.
