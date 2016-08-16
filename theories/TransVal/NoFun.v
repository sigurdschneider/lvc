Require Import IL.

Inductive Terminates :F.state -> F.state -> Prop :=
|TerminatesReturn L E e v:
   op_eval E e = ⎣v⎦
   -> Terminates (L, E, stmtReturn e)   (L  , E , stmtReturn e)
|TerminatesApp L E f x vl:
   omap (op_eval E) x = ⎣vl⎦
   -> Terminates (L, E, stmtApp f x) (L, E, stmtApp f x)
|TerminatesStep L E s L'  E' s'  L'' E'' s''  a:
   F.step (L, E, s) a (L', E', s')
   -> Terminates (L', E', s') (L'', E'', s'')
   -> notApp s
   -> Terminates (L,E,s) (L'', E'', s'') .

Hint Extern 5 =>
match goal with
  [ H : notApp (stmtApp _ _ ) |- _ ] => exfalso; inv H
end.

Hint Constructors notApp.

Lemma terminates_impl_star2:
  forall L E s L' Es s',
    noFun s
    -> Terminates (L, E ,s ) (L', Es, s')
    -> (star2 F.step (L, E, s) nil (L', Es, s'))
       /\ ((exists e, s' = stmtReturn e) \/ (exists f X, s' = stmtApp f X)).

Proof.
  intros L E s L' Es s' noFun_s Terminates_s.
  general induction Terminates_s; try invt F.step; invt noFun; eauto using star2_refl.
  - edestruct IHTerminates_s as [step ?]; try reflexivity; eauto; dcr; split; eauto using star2_silent.
  - edestruct IHTerminates_s as [step ?]; try reflexivity; eauto; dcr; split; eauto using star2_silent.
  - edestruct IHTerminates_s as [step ?]; try reflexivity; eauto; dcr; split; eauto using star2_silent.
Qed.

(** Lemma 2 in Thesis
Proves that Terminates ignores the label environment **)

Lemma term_swap_fun L1 L2 L1'  V V' s s':
Terminates (L1,V,s) (L1',V',s')
-> exists L2', Terminates (L2, V, s) (L2', V', s').

Proof.
  intros term. general induction term; eauto using Terminates.
  assert (exists L2', F.step (L2, V, s0) a (L2', E', s')). {
    inv H; eexists; econstructor; eauto.
  }
  destruct H1; eauto. edestruct IHterm; eauto.
  eexists; eauto using Terminates.
Qed.

Inductive Crash : F.state -> F.state -> Prop :=
|CrashApp L E f Y:
   omap (op_eval E) Y = None
   -> Crash (L, E, stmtApp f Y) (L, E, stmtApp f Y)
|CrashBase L E s :
   ( forall f el, s <> stmtApp f el)
   ->  normal2 F.step (L, E, s)
   -> state_result (L,E,s) = None
   -> Crash (L, E,s) (L,E,s)
|CrashStep L E s sigma' sigma'' a:
   F.step (L, E, s) a sigma'
   ->  (forall f xl, s <> stmtApp f xl)
   -> Crash sigma' sigma''
   -> Crash (L,E,s) sigma''.

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
  - case_eq (op_eval E e); intros.
     + destruct (IHnoFun_s (E[x<- Some v])) as [E' [s' termcrash]].
       exists E'; exists s'; intros.
       destruct (termcrash L) as [ term | crash].
       * left. econstructor; eauto.
         { econstructor; eauto. }
       * right. econstructor; eauto; try  econstructor; eauto; intros; isabsurd.
     + exists E; exists (stmtLet x (Operation e) s); intros.
       right. econstructor; eauto; intros; try hnf; try isabsurd.
       intros. unfold reducible2 in H0. destruct H0 as [y [σ' H0]].
       isabsurd.
  - case_eq (op_eval E e); intros.
    + case_eq (val2bool v); intros.
      * destruct (IHnoFun_s1 E) as [E' [s' termcrash]].
        exists E'; exists s'; intros.
        destruct (termcrash L) as [term | crash].
        { left. econstructor; eauto.
          - econstructor; eauto. }
        { right. econstructor; eauto. econstructor; eauto.
          intros; isabsurd. }
      * destruct (IHnoFun_s2 E) as [E' [s' termcrash]];
          exists E'; exists s'; intros.
        destruct (termcrash L) as [ term | crash ].
        { left. econstructor; eauto.
          - econstructor; eauto.
           }
        { right. econstructor; eauto. econstructor; eauto.
          intros; isabsurd. }
    +  exists E; exists (stmtIf e s t).
       right. econstructor; eauto; intros; try hnf; try isabsurd.
       intros. unfold reducible2 in H0. destruct H0 as [y [σ' H0]].
       isabsurd.
  - case_eq (omap (op_eval E) Y); intros.
    + exists E; exists (stmtApp l Y); left; econstructor; eauto.
    + exists E; exists (stmtApp l Y); right.
      econstructor; eauto; intros; try hnf; try isabsurd.
  - case_eq (op_eval E e).
    + exists E; exists (stmtReturn e).
      left; econstructor; eauto.
    + exists E; exists (stmtReturn e). right.
      econstructor; eauto; intros; try hnf; try isabsurd.
      intros. unfold reducible2 in H0. destruct H0.
      destruct H0. inversion H0.
Qed.
