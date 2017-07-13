Require Import Util MoreList Get Option OptionMap.
Require Import Var IL AppExpFree.

Fixpoint list_to_stmt (xl: list var) (Y : list op) (s : stmt) : stmt :=
  match xl, Y with
  | x::xl, e :: Y => stmtLet x  (Operation e) (list_to_stmt xl Y s)
  | _, _ => s
  end.

Lemma list_to_stmt_correct L E s xl Y vl
: length xl = length Y
  -> omap (op_eval E) Y = Some vl
  -> NoDupA _eq xl
  -> disj (of_list xl) (list_union (List.map Op.freeVars Y))
  -> star2 F.step (L, E, list_to_stmt xl Y s) nil
          (L, update_with_list' xl (List.map Some vl) E, s).
Proof.
  intros Len Eq Uni Disj.
  length_equify.
  general induction Len; simpl in * |- *; eauto using star2_refl.
  - simpl in *. monad_inv Eq.
    eapply star2_silent.
    econstructor; eauto.
    rewrite list_union_start_swap in Disj.
    eapply IHLen; eauto.
    eapply omap_op_eval_agree; eauto.
    symmetry. eapply agree_on_update_dead; [|reflexivity].
    eauto with cset.
    eapply disj_incl; eauto with cset.
Qed.

Lemma list_to_stmt_crash L E xl Y s
: length xl = length Y
  -> omap (op_eval E) Y = None
  -> NoDupA _eq xl
  -> disj (of_list xl) (list_union (List.map Op.freeVars Y))
  -> exists σ, star2 F.step (L, E, list_to_stmt xl Y s) nil σ
         /\ state_result σ = None
         /\ normal2 F.step σ.
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl in * |- *.
  - monad_inv H0.
    + eexists. split. eapply star2_refl.
      split; eauto. stuck2.
    + rewrite list_union_start_swap in H2.
      edestruct (IHlength_eq L (E [x <- Some x0])); eauto.
      * eapply omap_op_eval_agree; eauto. symmetry.
        eapply agree_on_update_dead; [|reflexivity].
        intro. eapply (H2 x); eauto with cset.
      * eapply disj_incl; eauto with cset.
      * dcr. eexists. split; eauto.
        eapply star2_silent.
        econstructor; eauto. eauto.
Qed.

Lemma list_to_stmt_app_expfree  ZL Y Y' l
  : (forall n e, get Y' n e -> isVar e)
    -> app_expfree (list_to_stmt ZL Y (stmtApp l Y')).
Proof.
  general induction Y; destruct ZL; destruct Y'; simpl;
    econstructor; intros; inv_get; isabsurd; eauto using isVar.
Qed.


Lemma list_to_stmt_freeVars xl Y s (Len:❬xl❭ = ❬Y❭)
      (Disj:disj (of_list xl) (list_union (Op.freeVars ⊝ Y)))
  : freeVars (list_to_stmt xl Y s) [=] list_union (Op.freeVars ⊝ Y) ∪ (freeVars s \ of_list xl).
Proof.
  general induction Len; simpl in *.
  - cset_tac.
  - setoid_rewrite list_union_start_swap.
    setoid_rewrite list_union_start_swap in Disj.
    rewrite IHLen.
    clear IHLen. cset_tac.
    eapply disj_incl; eauto with cset.
Qed.
