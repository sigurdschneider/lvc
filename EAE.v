Require Import CSet Le.
Require Import Plus Util AllInRel Map SetOperations.

Require Import Val EqDec Computable Var Env EnvTy IL Annotation.
Require Import Bisim Fresh MoreExp.

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
    intros. eapply length_length_eq in H0.
    general induction H0; simpl. reflexivity.
    hnf; intros. lud. hnf in H1; simpl in *.
    dcr. exfalso. eapply H7. econstructor. eapply H4.
    exploit (IHlength_eq H E {x1} x0 y0). simpl in *; intuition.
    hnf; intros. eapply H8. econstructor 2; eauto.
    rewrite H8. lud. cset_tac; intuition.
    exploit (IHlength_eq H E {x1} x0 y0). simpl in *; intuition.
    hnf; intros. eapply H7. econstructor 2; eauto.
    rewrite H7. lud. cset_tac; intuition.
  Qed.

  Lemma update_with_list_agree' (XL:list X) (VL:list Y) E D
  : length XL = length VL
    -> unique XL
    -> agree_on eq D (E [XL <-- VL]) (update_with_list' XL VL E).
  Proof.
    intros. eapply length_length_eq in H0.
    general induction H0; simpl in *.
    - reflexivity.
    - etransitivity. symmetry. eapply update_unique_commute; eauto using length_eq_length.
      eapply IHlength_eq; intuition.
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
      eauto with cset.
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
  - monad_inv H0; isabsurd.
    + eexists; repeat split; eauto using star2_refl. stuck2.
    + rewrite list_union_start_swap in H2.
      edestruct (IHlength_eq L (E [x <- Some x0])); eauto.
      * eapply omap_exp_eval_agree; eauto. symmetry.
        eapply agree_on_update_dead; [|reflexivity].
        intro. eapply (H2 x); cset_tac.
      * eauto with cset.
      * dcr. eexists. split; eauto.
        econstructor 2 with (y:=EvtTau).
        econstructor; eauto.
        eauto.
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

Definition ArgRel (V V:onv val) (G:params) (VL VL': list val) : Prop :=
  VL = VL' /\ length VL = length G.

Definition ParamRel (G:params) (Z Z' : list var) : Prop :=
  Z = Z' /\ length Z = length G.

Instance SR : ProofRelation params := {
   ParamRel := ParamRel;
   ArgRel := ArgRel;
   BlockRel := fun lvZ b b' => lvZ = F.block_Z b
}.
intros. hnf in H. hnf in H0. dcr; split; congruence.
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


Lemma sim_EAE' r L L' V s PL
: simL' bisim_progeq r SR PL L L'
-> bisim'r r (L, V, s) (L',V, compile s).
Proof.
  revert_except s. unfold bisim'r.
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
    + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
      * hnf in H. inRel_invs. simpl in H2, InR, H13.
        hnf in H11, H12; dcr; subst; simpl in *.
        exploit omap_length as Hlen; eauto.
        decide (length Y = length Z'). {
          cases.
          - eapply bisim_drop_shift; eauto. eapply (inRel_sawtooth H).
            eapply (inRel_sawtooth H). eapply H13; eauto. hnf.
            split; congruence.
          - eapply bisim'_expansion_closed;
              [ eapply bisim_drop_shift
              | eapply star2_refl
              | eapply (list_to_stmt_correct);
                eauto using fresh_spec, fresh_list_unique, fresh_list_spec
              ]; try eapply (inRel_sawtooth H); eauto.
            simpl. eapply H13; eauto.
            instantiate (1:=l0).
            eapply omap_exp_eval_agree. Focus 2.
            eapply omap_lookup_vars.
            rewrite fresh_list_length; eauto.
            eapply fresh_list_unique. eapply fresh_spec.
            eapply update_with_list_agree'. rewrite fresh_list_length, map_length; eauto.
            eapply fresh_list_unique. eapply fresh_spec.
            hnf; split; congruence.
        }
        cases.
        pno_step; get_functional; simpl in *; congruence.
        eapply bisim'_expansion_closed; [| eapply star2_refl | eapply LTSC].
        pno_step; repeat get_functional; simpl in *. congruence.
        eapply n; rewrite len. rewrite map_length. rewrite fresh_list_length. eauto.
      * cases. pno_step; eauto. hnf in H. inRel_invs; eauto.
        eapply bisim'_expansion_closed; [| eapply star2_refl | eapply LTSC].
        pno_step; repeat get_functional; simpl in *. eauto.
        hnf in H. inRel_invs; eauto.
    + cases. pno_step.
      edestruct (list_to_stmt_crash L' V (stmtApp l (Var ⊝ fresh_list fresh (list_union (Exp.freeVars ⊝ Y)) ❬Y❭)) (fresh_list fresh (list_union (Exp.freeVars ⊝ Y)) ❬Y❭) Y); eauto using fresh_spec, fresh_list_unique, fresh_list_spec; dcr.
      pfold. econstructor 3; try eapply H2; try eapply star2_refl; eauto. stuck2.
  - pno_step.
  - case_eq (omap (exp_eval V) Y); intros.
    + pextern_step.
      * eexists; split; [ econstructor; eauto | eauto ].
      * eexists; split; [ econstructor; eauto | eauto ].
    + pno_step.
  - pone_step.
    left. eapply IH with (PL:=fst ⊝ s ++ PL); eauto.
    + eapply simL_mon; eauto. eapply simL_extension'; eauto with len.
      * intros; inv_get; simpl. unfold fexteq', ParamRel; split; eauto.
        split; hnf; eauto; intros. hnf in H1. dcr; subst.
        eapply IH; eauto.
Qed.

Lemma sim_EAE V s
: @bisim _ statetype_F _ statetype_F (nil, V, s) (nil,V, compile s).
Proof.
  eapply bisim'_bisim. hnf. eapply sim_EAE'. constructor.
Qed.
