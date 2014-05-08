Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL ParamsMatch Sim Alpha Coherence Fresh.

Require Import Liveness Substitution.

Set Implicit Arguments.
Unset Printing Records.

Fixpoint copyPropagate (ϱ:var -> var) (s:stmt) : stmt :=
  match s with
   | stmtExp x (Var y) s => copyPropagate (ϱ[x <- ϱ y]) s
   | stmtExp x e s => let x' := fresh_stable (lookup_set ϱ (freeVars s \ {{x}})) x in
                        stmtExp x' (rename_exp ϱ e) (copyPropagate (ϱ[x <- x']) s)
   | stmtIf e s1 s2 => stmtIf (rename_exp ϱ e)
                             (copyPropagate ϱ s1)
                             (copyPropagate ϱ s2)
   | stmtGoto l Y => stmtGoto l (List.map (rename_exp ϱ) Y)
   | stmtReturn e => stmtReturn (rename_exp ϱ e)
   | stmtLet Z s1 s2 => 
     let Z' := fresh_stable_list (lookup_set ϱ (freeVars s1 \ of_list Z)) Z in
     stmtLet Z' (copyPropagate (ϱ[Z <-- Z']) s1) (copyPropagate ϱ s2)
   end.

Lemma sim_CP s ϱ 
: simeq (copyPropagate ϱ s) (subst ϱ s).
Proof. 
  general induction s; simpl in * |- *.
  + destruct e; hnf; intros.
    - one_step. reflexivity. reflexivity. 
      unfold simeq in IHs. eapply IHs; eauto.
    - case_eq (E (ϱ v)); intros.
      eapply sim_expansion_closed.
      Focus 2. eapply star_refl.
      Focus 2. eapply S_star. econstructor. simpl. eauto.
      eapply star_refl.
      simpl in * |- *.
      refine (sim_trans (IHs _ _ _) _ ); eauto.
      eapply subst_fresh. eapply simL_refl. (* eapply agree_on_comp_fresh.
      eapply fresh_stable_spec. *) admit.
      no_step.
    - case_eq (exp_eval E (rename_exp ϱ (BinOp b e1 e2))); intros.
      one_step. eapply IHs; eauto.
      no_step; simpl in *; congruence.
  + etransitivity.
    eapply (simeq_contextual (ctxIfT _  _ ctxHole)); eauto.
    eapply (simeq_contextual (ctxIfS _ ctxHole _)); eauto.
  + eapply simeq_refl.
  + eapply simeq_refl.
  + etransitivity.
    eapply (simeq_contextual (ctxLetT _ _ ctxHole)); eauto.
    eapply (simeq_contextual (ctxLetS _ ctxHole _)). eapply IHs1; eauto.
Qed.

Lemma CP_tv s s' C C' D D'
  : ssa C s C' -> ssa D s' D'
  -> copyPropagate id s = copyPropagate id s'
  -> simeq s s'.
Proof.
  intros. 
  pose proof (simeq_trans (subst_id _) (simeq_sym (sim_CP s _ ))); eauto.
  pose proof (simeq_trans (subst_id _) (simeq_sym (sim_CP s' _ ))); eauto.
  eapply simeq_sym in H3. rewrite <- H1 in H3.
  eapply simeq_trans; eauto.  
Qed.

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
