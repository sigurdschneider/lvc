Require Import CSet Le.
Require Import Plus Util AllInRel Map SetOperations.

Require Import Val EqDec Computable Var Env EnvTy IL Annotation.
Require Import Bisim Fresh Filter Filter MoreExp.

Set Implicit Arguments.
Unset Printing Records.

Function list_to_stmt (xl: list var) (Y : list exp) (s : stmt) : stmt :=
  match xl, Y with
    | x::xl, e :: Y => stmtExp x e (list_to_stmt xl Y s)
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
    rewrite X0. lud. cset_tac; intuition.
    exploit (IHlength_eq H E {x1} x0 y0). simpl in *; intuition.
    hnf; intros. eapply H7. econstructor 2; eauto.
    rewrite X0. lud. cset_tac; intuition.
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
  -> of_list xl ∩ list_union (List.map Exp.freeVars Y) [=] ∅
  -> star2 F.step (L, E, list_to_stmt xl Y s) nil (L, update_with_list' xl (List.map Some vl) E, s).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl in * |- *.
  - eapply star2_refl.
  - monad_inv H0.
    econstructor 2 with (y:=EvtTau).
    econstructor; eauto.
    simpl. eapply IHlength_eq.
    eapply omap_exp_eval_agree.
    symmetry. eapply agree_on_update_dead.
    cset_tac. intro. eapply (H2 x).
    split; cset_tac; intuition.
    unfold list_union. simpl.
    eapply list_union_start_swap. cset_tac; intuition.
    reflexivity. eauto. intuition.
    cset_tac; intuition.
    eapply (H2 a); split; cset_tac; intuition.
    unfold list_union. simpl.
    eapply list_union_start_swap. cset_tac; intuition.
Qed.

Lemma list_to_stmt_crash L E s xl Y
: length xl = length Y
  -> omap (exp_eval E) Y = None
  -> unique xl
  -> of_list xl ∩ list_union (List.map Exp.freeVars Y) [=] ∅
  -> exists σ, star2 F.step (L, E, list_to_stmt xl Y s) nil σ /\ state_result σ = None /\ normal2 F.step σ.
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl in * |- *.
  - monad_inv H0; isabsurd.
    + eexists; repeat split; eauto using star2_refl. stuck2.
    + edestruct (IHlength_eq L (E [x <- Some x0])); eauto; intuition.
      eapply omap_exp_eval_agree; eauto.
      symmetry. eapply agree_on_update_dead; try reflexivity.
      intro. cset_tac. eapply (H2 x). cset_tac; intuition.
      unfold list_union; simpl.
      eapply list_union_start_swap. cset_tac; intuition.
      cset_tac; intuition. eapply (H2 a); cset_tac; intuition.
      unfold list_union; simpl.
      eapply list_union_start_swap. cset_tac; intuition.
      eexists. split; eauto.
      econstructor 2 with (y:=EvtTau).
      econstructor; eauto.
      eauto.
Qed.

Fixpoint compile s
  : stmt :=
  match s with
    | stmtExp x e s => stmtExp x e (compile s)
    | stmtIf x s t => stmtIf x (compile s) (compile t)
    | stmtGoto l Y  =>
      let xl := fresh_list fresh (list_union (List.map Exp.freeVars Y)) (length Y) in
      list_to_stmt xl Y (stmtGoto l (List.map Var xl))
    | stmtReturn x => stmtReturn x
    | stmtExtern x f Y s => stmtExtern x f Y (compile s)
    | stmtLet Z s t => stmtLet Z (compile s) (compile t)
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
  rewrite map_length.
  eapply length_eq_length; eauto.
Qed.


Lemma sim_EAE' r L L' V s PL
: simL' bisim_progeq r SR PL L L'
-> bisim'r r (L, V, s) (L',V, compile s).
Proof.
  general induction s; simpl; simpl in * |- *.
  - case_eq (exp_eval V e); intros.
    + pfold. econstructor; try eapply plus2O.
      econstructor; eauto. reflexivity.
      econstructor; eauto. reflexivity.
      left. eapply IHs; eauto.
    + pfold. econstructor 3; [| eapply star2_refl|eapply star2_refl| |]; eauto; stuck.
  - case_eq (exp_eval V e); intros.
    case_eq (val2bool v); intros.
    pfold; econstructor; try eapply plus2O.
    econstructor; eauto. reflexivity.
    econstructor; eauto. reflexivity.
    left; eapply IHs1; eauto.
    pfold; econstructor; try eapply plus2O.
    econstructor 3; eauto. reflexivity.
    econstructor 3; eauto. reflexivity.
    left; eapply IHs2; eauto.
    pfold. econstructor 3; try eapply star2_refl; eauto; stuck.
  - case_eq (omap (exp_eval V) Y); intros.
    + exploit (list_to_stmt_correct L' V (stmtGoto l (List.map Var
            (fresh_list fresh (list_union (List.map Exp.freeVars Y)) (length Y))))).
      rewrite fresh_list_length; eauto. eauto.
      eapply fresh_list_unique. eapply fresh_spec. eapply fresh_list_spec. eapply fresh_spec.
      destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
      * edestruct AIR5_length; try eassumption; dcr.
        edestruct get_length_eq; try eassumption.
        edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr.
        simpl in *. repeat get_functional; subst.
        inv H11.
        decide (length Y = length bZ).
        eapply bisim'_expansion_closed; [eapply bisim_drop_shift; eapply H18| eapply star2_refl |].
        eauto.
        Focus 2. hnf; split. reflexivity. simpl. hnf in H15. hnf in H17.
        dcr; subst. simpl in *.
        erewrite <- omap_length; try eapply H0; eauto.
        eapply omap_exp_eval_agree. Focus 2.
        eapply omap_lookup_vars.
        rewrite fresh_list_length. eapply omap_length; eauto.
        eapply fresh_list_unique. eapply fresh_spec.
        eapply update_with_list_agree'. rewrite fresh_list_length, map_length.
        eapply omap_length; eauto. eapply fresh_list_unique. eapply fresh_spec.
        eapply X.
        hnf in H15. hnf in H17. dcr; simpl in *. pfold.
        econstructor 3; try eapply X; try eapply star2_refl. subst.
        simpl in *. congruence. stuck2. get_functional; subst; simpl in *; congruence.
        edestruct AIR5_nth2 as [? [?[? [?]]]]; try eassumption; dcr.
        stuck2. repeat get_functional; subst. simpl in *.
        rewrite map_length in len. rewrite fresh_list_length in len. congruence.
      * pfold. econstructor 3; try eapply X; try eapply star2_refl.
        simpl in *. congruence. stuck2; eauto.
        stuck2; eauto.
        edestruct AIR5_nth2 as [? [?[? [?]]]]; try eassumption; dcr. eauto.
    + edestruct list_to_stmt_crash; eauto.
      eapply fresh_list_length. eapply fresh_list_unique. eapply fresh_spec.
      eapply fresh_list_spec. eapply fresh_spec. dcr.
      pfold. econstructor 3; try eapply H2; try eapply star2_refl.
      simpl in *. congruence. stuck2. eapply H5.
  - pfold. econstructor 3; try eapply star2_refl.
    simpl; eauto.
    stuck2. stuck2.
  - pfold.
    case_eq (omap (exp_eval V) Y); intros.
    econstructor 2; try eapply star2_refl.
    + eexists (ExternI f l 0); eexists; try (now (econstructor; eauto)).
    + eexists (ExternI f l 0); eexists; try (now (econstructor; eauto)).
    + intros. inv H1. eexists. split.
      * econstructor; eauto.
      * left. eapply IHs; eauto.
    + intros. inv H1. eexists. split.
      * econstructor; eauto.
      * left. eapply IHs; eauto.
    + econstructor 3; try eapply star2_refl; simpl; eauto.
      stuck2. stuck2.
  - pfold. econstructor; try eapply plus2O.
    econstructor; eauto. reflexivity.
    econstructor; eauto. reflexivity.
    simpl. left. eapply IHs2; eauto.
    + eapply simL_mon; eauto. eapply simL_extension'; eauto.
      * hnf; intros. split. hnf; split. reflexivity. reflexivity.
        intros. inv H0. eapply IHs1; eauto.
      * split; reflexivity.
Qed.

Lemma sim_EAE V s
: @bisim _ statetype_F _ statetype_F (nil, V, s) (nil,V, compile s).
Proof.
  eapply bisim'_bisim. hnf. eapply sim_EAE'. constructor.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
