Require Import IL Annotation RenamedApart.

Set Implicit Arguments.


Hint Extern 5 =>
match goal with
  [ H : notApp (stmtApp _ _ ) |- _ ] => exfalso; inv H
end.

Hint Constructors notApp.

Inductive star (X : Type) (R : X -> X -> Prop) : X -> X -> Prop :=
    star_refl : forall x : X, star R x x
  | star_step : forall x x' z, R x x' -> star R x' z -> star R x z.

Definition nc_step (σ: F.state) (σ': F.state) :=
  step σ EvtTau σ' /\ notApp (snd σ).

Lemma nc_step_step σ σ'
  : nc_step σ σ' -> F.step σ EvtTau σ'.
Proof.
  firstorder.
Qed.

Lemma nc_star_step σ σ'
  : star nc_step σ σ' -> star2 F.step σ nil σ'.
Proof.
  intros. general induction H; eauto using star2.
  eapply star2_silent; eauto using nc_step_step.
Qed.

Lemma nc_step_L L1 E s L1' E' s' L2
  : nc_step (L1, E, s) (L1', E', s')
    -> exists L2', nc_step (L2, E, s) (L2', E', s').
Proof.
  intros [A B]; inv A; eexists; simpl; split; now (eauto; single_step).
Qed.

Lemma noFun_nc_step L E s σ
  : noFun s
    -> nc_step (L, E, s) σ
    -> noFun (snd σ).
Proof.
  intros NF [Step NA]; inv NF; inv Step; inv NA; simpl; eauto.
Qed.

Lemma noFun_nc_step' L E s L' E' s'
  : noFun s
    -> nc_step (L, E, s) (L', E', s')
    -> noFun s'.
Proof.
  intros NF [Step NA]; inv NF; inv Step; inv NA; simpl; eauto.
Qed.

Hint Resolve noFun_nc_step noFun_nc_step'.

Lemma nc_step_agree L L' s D s' (E:onv val) (E':onv val)
 : renamedApart s D
   -> noFun s
   -> star nc_step (L, E, s) (L', E', s')
   -> agree_on eq (fst(getAnn D)) E E'.
Proof.
  intros RA NF Trm.
  general induction Trm; eauto using agree_on_refl.
  destruct x' as [[L'' E''] s'']. destruct H; simpl in *.
  invt renamedApart; try invt F.step;try invt noFun; simpl; eauto.
  - exploit IHTrm; [ | | reflexivity | reflexivity |]; eauto.
    pe_rewrite.
    eapply agree_on_update_inv in H6.
    eapply agree_on_incl; eauto. cset_tac.
  - exploit IHTrm; [ | | reflexivity | reflexivity |]; eauto.
    pe_rewrite. eauto.
  - exploit IHTrm; [ | | reflexivity | reflexivity |]; eauto.
    pe_rewrite. eauto.
Qed.

Lemma nc_step_agree' σ σ' D
  : star nc_step σ σ'
    -> renamedApart (snd σ) D
    -> noFun (snd σ)
    -> agree_on eq (fst(getAnn D)) (snd (fst σ)) (snd (fst σ')).
Proof.
  destruct σ as [[L E] s], σ' as [[L' E'] s']; eauto using nc_step_agree.
Qed.

Lemma nc_step_agree_all L L' s D G s' (E:onv val) (E':onv val)
 : renamedApart s D
   -> noFun s
   -> star nc_step (L, E, s) (L', E', s')
   -> agree_on eq (G \ snd (getAnn D)) E E'.
Proof.
  intros RA NF Trm.
  general induction Trm; eauto using agree_on_refl.
  destruct x' as [[L'' E''] s'']. destruct H; simpl in *.
  invt renamedApart; try invt F.step;try invt noFun; simpl; eauto.
  - exploit IHTrm; [ | | reflexivity | reflexivity |]; eauto.
    pe_rewrite.
    eapply agree_on_update_inv in H6. rewrite H4.
    eapply agree_on_incl; eauto. cset_tac.
  - exploit IHTrm; [ | | reflexivity | reflexivity |]; eauto.
    pe_rewrite. rewrite <- H3.
    eapply agree_on_incl; eauto. cset_tac.
  - exploit IHTrm; [ | | reflexivity | reflexivity |]; eauto.
    pe_rewrite. rewrite <- H3.
    eapply agree_on_incl; eauto. cset_tac.
Qed.

Inductive nc_terminal : F.state -> Prop :=
| NcTerminalReturn L E e v
  : op_eval E e = Some v -> nc_terminal (L, E, stmtReturn e)
| NcTerminalApp L E f Y vl
  : omap (op_eval E) Y = Some vl -> nc_terminal (L, E, stmtApp f Y).

Inductive nc_stuck : F.state -> Prop :=
| NcStuckApp L E f Y
  : omap (op_eval E) Y = None -> nc_stuck (L, E, stmtApp f Y)
| NcStuck L E s
  : notApp s -> result (L,E,s) = None -> normal2 F.step (L,E,s) -> nc_stuck (L, E, s).

Lemma nc_stuck_terminal σ
  : nc_stuck σ -> normal2 F.step σ.
Proof.
  intros H. invc H; subst; eauto. stuck2.
Qed.

Lemma nc_stuck_result_none σ
  : nc_stuck σ -> result σ = None.
Proof.
  intros H. invc H; subst; eauto.
Qed.

Definition nc_final σ := nc_terminal σ \/ nc_stuck σ.

Definition Terminates σ σ' :=
  star nc_step σ σ' /\ nc_terminal σ'.

Definition Crash σ σ' :=
  star nc_step σ σ' /\ nc_stuck σ'.

Lemma noFun_impl_term_crash' E s
  : noFun s
    ->  exists E' s', forall L, star nc_step (L, E, s) (L, E', s') /\ nc_final (L, E', s').
Proof.
  intros. general induction s; invt noFun.
  - case_eq (op_eval E e0); intros.
    + edestruct IHs; eauto; dcr.
      do 2 eexists; split; [| eapply H3]; eauto using star.
      eapply star_step. split; simpl; eauto. single_step.
      eapply H3; eauto.
    + do 2 eexists; split; [ eapply star_refl|].
      right; eauto using nc_stuck. econstructor; eauto. stuck.
  - case_eq (op_eval E e); intros.
    + case_eq (val2bool v); intros.
      * edestruct IHs1; eauto; dcr.
        do 2 eexists; split; [| eapply H5].
        eapply star_step. split; simpl; eauto. single_step.
        eapply H5; eauto.
      * edestruct IHs2; eauto; dcr.
        do 2 eexists; split; [| eapply H5].
        eapply star_step. split; simpl; eauto. single_step.
        eapply H5; eauto.
    + do 2 eexists; split; [ eapply star_refl|].
      right. econstructor; eauto. stuck.
  - case_eq (omap (op_eval E) Y); intros.
    + do 2 eexists; split; [ eapply star_refl|].
      left. econstructor; eauto.
    + do 2 eexists; split; [ eapply star_refl|].
      right. econstructor ; eauto.
  - case_eq (op_eval E e); intros.
    + do 2 eexists; split; [ eapply star_refl|].
      left; econstructor; eauto.
    + do 2 eexists; split; [ eapply star_refl|].
      right; econstructor; eauto. stuck.
Qed.

Lemma noFun_impl_term_crash E s
: noFun s
  ->  exists E' s', forall L, Terminates (L, E, s)(L, E', s') \/ Crash (L, E, s) (L, E', s').
Proof.
  intros.
  edestruct noFun_impl_term_crash'; eauto; dcr.
  eexists x, x0; intros L. destruct (H1 L) as [A [B|B]].
  - left; split; eauto.
  - right; split; eauto.
Qed.

Lemma nc_step_renamedApart D (L:F.labenv) E s E' s'
  : noFun s
    -> renamedApart s D
    -> star nc_step (L, E, s) (L, E', s')
    -> exists D', renamedApart s' D'
                  /\ fst (getAnn D) ⊆ fst (getAnn D')
                  /\ snd (getAnn D') ⊆ snd (getAnn D).
Proof.
  intros NF RA STAR. general induction STAR; eauto.
  destruct x' as [[L'' E''] s'']. destruct H; simpl in *.
  invt renamedApart; invt noFun; invt notApp; try invt F.step; simpl.
  - edestruct (IHSTAR an L'' (E[x<-Some v]) s'' ); eauto; dcr.
    pe_rewrite. simpl. eexists; split; eauto.
    rewrite <- H10, H11, H4. eauto with cset.
  - edestruct (IHSTAR ans); try reflexivity; eauto; dcr.
    eexists; split; eauto.
    pe_rewrite.
    rewrite H13, H14, <- H3. eauto with cset.
  - edestruct IHSTAR; eauto; dcr.
    pe_rewrite.
    eexists; split; eauto.
    rewrite <- H13, H14, <- H3. eauto with cset.
Qed.


Lemma terminates_impl_eval L L' E s E' e
  : noFun s
    -> Terminates (L, E, s) (L', E',stmtReturn  e)
    -> exists v, op_eval E' e = Some v.
Proof.
  intros NF [? Trm].
  inv Trm. eauto.
Qed.

Lemma terminates_impl_evalList L  L' E s E' f el
  : noFun s
    -> Terminates (L, E, s) (L', E', stmtApp f el)
    -> exists v, omap (op_eval E') el = Some v.
Proof.
  intros NF [? Trm].
  inv Trm; eauto.
Qed.

Lemma nostep_let:
  forall L E x e s,
    normal2 F.step (L, E, stmtLet x (Operation e) s)
    -> op_eval E e = None.

Proof.
  intros. case_eq (op_eval E e); intros; eauto.
  exfalso; apply H. unfold reducible2.
  exists EvtTau. exists (L, E[x<-Some v],s). econstructor; eauto.
Qed.

Lemma nostep_if:
  forall L E e t f,
    normal2 F.step (L, E, stmtIf e t f)
    -> op_eval E e = None.
Proof.
  intros. case_eq (op_eval E e); intros; eauto.
  exfalso; eapply H; unfold reducible2.
  exists (EvtTau).
  case_eq (val2bool v); intros.
  - exists (L, E, t); econstructor; eauto.
  - exists (L, E, f); econstructor; eauto.
Qed.
