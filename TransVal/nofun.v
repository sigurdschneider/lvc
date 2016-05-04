Require Import IL Compute.

Inductive noFun : stmt->Prop :=
|noFunLet x e s :
 noFun s
 -> noFun (stmtLet x e s)
|noFunIf e s t :
 noFun s
 -> noFun t
 -> noFun (stmtIf e s t)
|noFunCall l Y :
 noFun (stmtApp l Y)
|noFunExp e :
 noFun (stmtReturn e).

(** Lemma 2 of the thesis
It is decidable wether program leaf crashes or leaf terminates **)
Lemma noFun_impl_term_crash :
forall E s,
noFun s
->  exists E' s',
      forall L,
        Terminates (L, E, s)(L, E', s') \/ Crash (L, E, s) (L, E', s').

Proof.
intros E s noFun_s; general induction noFun_s.
-  case_eq (exp_eval E e); intros.
   + destruct (IHnoFun_s (E[x<- Some v])) as [E' [s' termcrash]].
     exists E'; exists s'; intros.
     destruct (termcrash L) as [ term | crash].
     * left. econstructor; eauto.
              { econstructor; eauto. }
              { intros. hnf; isabsurd. }
     * right. econstructor; eauto; try  econstructor; eauto; intros; isabsurd.
   + exists E; exists (stmtLet x e s); intros.
       right. econstructor; eauto; intros; try hnf; try isabsurd.
       intros. unfold reducible2 in H0. destruct H0 as [y [σ' H0]].
       isabsurd.
- case_eq (exp_eval E e); intros.
  + case_eq (val2bool v); intros.
    * destruct (IHnoFun_s1 E) as [E' [s' termcrash]].
      exists E'; exists s'; intros.
      destruct (termcrash L) as [term | crash].
      { left. econstructor; eauto.
       - econstructor; eauto.
       - hnf; intros; isabsurd. }
      { right. econstructor; eauto. econstructor; eauto.
      intros; isabsurd. }
    * destruct (IHnoFun_s2 E) as [E' [s' termcrash]];
      exists E'; exists s'; intros.
      destruct (termcrash L) as [ term | crash ].
      { left. econstructor; eauto.
       - econstructor; eauto.
       - hnf; intros; isabsurd. }
      { right. econstructor; eauto. econstructor; eauto.
      intros; isabsurd. }
  +  exists E; exists (stmtIf e s t).
            right. econstructor; eauto; intros; try hnf; try isabsurd.
            intros. unfold reducible2 in H0. destruct H0 as [y [σ' H0]].
            isabsurd.
- case_eq (omap (exp_eval E) Y); intros.
  + exists E; exists (stmtApp l Y); left; econstructor; eauto.
  + exists E; exists (stmtApp l Y); right.
           econstructor; eauto; intros; try hnf; try isabsurd.
- case_eq (exp_eval E e).
  + exists E; exists (stmtReturn e).
           left; econstructor; eauto.
  + exists E; exists (stmtReturn e). right.
           econstructor; eauto; intros; try hnf; try isabsurd.
           intros. unfold reducible2 in H0. destruct H0.
           destruct H0. inversion H0.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)