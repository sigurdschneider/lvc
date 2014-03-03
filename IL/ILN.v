Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL Sim.

Set Implicit Arguments.

Open Scope map_scope.

Inductive nstmt : Type :=
| nstmtExp    (x : var) (e: exp) (s : nstmt)
| nstmtIf     (x : var) (s : nstmt) (t : nstmt)
| nstmtGoto   (l : lab) (Y:args) 
| nstmtReturn (x : var) 
(* block f Z : rt = s in b *)    
| nstmtLet    (l : lab) (Z:params) (s : nstmt) (t : nstmt).


Fixpoint pos X `{OrderedType X} (l:list X) (x:X) (n:nat) : option nat :=
  match l with 
    | nil => None
    | y::l => if [ x == y ] then Some n else pos l x (S n)
  end.


(** *** Functional Semantics *)
Module F.

  Inductive block : Type :=
    blockI {
        block_L : env (option block);
        block_E : env val;
        block_F : lab * params * nstmt
      }.
  
  Definition labenv := env (option block).
  Definition state : Type := (labenv * env val * nstmt)%type.

  Inductive step : state -> state -> Prop :=
  | nstepExp L E x e b v
    (def:exp_eval E e = Some v)
    : step (L, E, nstmtExp x e b) (L, E[x<-v], b)

  | nstepIfT L E
    (x:var) b1 b2
    (condTrue: val2bool (E x) = true)
    : step (L, E, nstmtIf x b1 b2) (L, E, b1)
    
  | nstepIfF L E
    (x:var) b1 b2
    (condFalse:val2bool (E x) = false)
    : step (L, E, nstmtIf x b1 b2) (L, E, b2)

    
  | nstepGoto (L:labenv) (E:env val) (l:lab) Y Z (s:nstmt) L' E'
    (len:length Z = length Y)
    (Ldef:L (counted l) = Some (blockI L' E' (l,Z,s))) E''
    (updOk:updE E' E Z Y  = E'')
    : step (L, E, nstmtGoto l Y)
           (L'[(counted l) <- Some (blockI L' E' (l,Z,s))], E'', s)

  | stepLet L E f s Z t 
    : step (L, E, nstmtLet f Z s t) (L[counted f <- Some (blockI L E (f,Z,s))], E, t).

  Lemma step_functional :
    functional step.
  Proof.
    induction 1; inversion 1; intros; subst; repeat get_functional; try congruence. 
  Qed.

  Lemma step_dec 
  : reddec step.
  Proof.
    hnf; intros. destruct x as [[L V] []].
    - case_eq (exp_eval V e); intros. 
      + left; eauto 20 using step.
      + right. stuck.
    - left; case_eq (val2bool (V x)); eexists; intros; eauto using step.
    - case_eq (L (counted l)); intros. 
      + destruct b as [? ? [[? ?] ?]].
        destruct_prop (l = l0); subst; try now (right; stuck).
        destruct_prop (length p = length Y); try now (right; stuck).
        left. eexists. econstructor; eauto.
      + right; stuck.
    - right; stuck.
    - left; eexists; eauto using step.
  Qed.

End F.


(** *** Imperative Semantics *)
Module I.

  Inductive block : Type :=
    blockI {
        block_L : env (option block);
        block_F : lab * params * nstmt
      }.
  
  Definition labenv := env (option block).
  Definition state : Type := (labenv * env val * nstmt)%type.

  Inductive step : state -> state -> Prop :=
  | nstepExp L E x e b v
    (def:exp_eval E e = Some v)
    : step (L, E, nstmtExp x e b) (L, E[x<-v], b)

  | nstepIfT L E
    (x:var) b1 b2
    (condTrue: val2bool (E x) = true)
    : step (L, E, nstmtIf x b1 b2) (L, E, b1)
    
  | nstepIfF L E
    (x:var) b1 b2
    (condFalse:val2bool (E x) = false)
    : step (L, E, nstmtIf x b1 b2) (L, E, b2)

  | nstepGoto (L:labenv) (E:env val) (l:lab) Y Z (s:nstmt) L'
    (len:length Z = length Y)
    (Ldef:L (counted l) = Some (blockI L' (l,Z,s))) E''
    (updOk:updE E E Z Y  = E'')
    : step (L, E, nstmtGoto l Y)
           (L'[(counted l) <- Some (blockI L' (l,Z,s))], E'', s)

  | stepLet L E f s Z t 
    : step (L, E, nstmtLet f Z s t) (L[counted f <- Some (blockI L (f,Z,s))], E, t).

  Lemma step_functional :
    functional step.
  Proof.
    induction 1; inversion 1; intros; subst; repeat get_functional; try congruence. 
  Qed.

  Lemma step_dec 
  : reddec step.
  Proof.
    hnf; intros. destruct x as [[L V] []].
    - case_eq (exp_eval V e); intros. 
      + left; eauto 20 using step.
      + right. stuck.
    - left; case_eq (val2bool (V x)); eexists; intros; eauto using step.
    - case_eq (L (counted l)); intros. 
      + destruct b as [? [[? ?] ?]].
        destruct_prop (l = l0); subst; try now (right; stuck).
        destruct_prop (length p = length Y); try now (right; stuck).
        left. eexists. econstructor; eauto.
      + right; stuck.
    - right; stuck.
    - left; eexists; eauto using step.
  Qed.

End I.

Fixpoint labIndices (s:nstmt) (symb: list lab) : option stmt :=
  match s with
    | nstmtExp x e s => mdo s' <- (labIndices s symb); Some (stmtExp x e s')
    | nstmtIf x s1 s2 => 
      mdo s1' <- (labIndices s1 symb);
      mdo s2' <- (labIndices s2 symb);
      Some (stmtIf x s1' s2')
    | nstmtGoto l Y => mdo f <- pos symb l 0; Some (stmtGoto (LabI f) Y)
    | nstmtReturn x => Some (stmtReturn x)
    | nstmtLet l Z s1 s2 => 
      mdo s1' <- labIndices s1 (l::symb);
      mdo s2' <- labIndices s2 (l::symb);
      Some (stmtLet Z s1' s2')
  end.

Definition state_result X (s:X*env val*nstmt) : option val :=
  match s with
    | (_, E, nstmtReturn x) => Some (E x)
    | _ => None
  end.

Instance statetype_I : StateType I.state := {
  step := I.step;
  result := (@state_result I.labenv);
  step_dec := I.step_dec; 
  step_functional := I.step_functional
}. 


Ltac single_step :=
  match goal with
    | [ H : agree_on _ ?E ?E', I : val2bool (?E ?x) = true |- step (_, ?E', stmtIf ?x _ _) _ _ ] =>
      econstructor; eauto; rewrite <- H; eauto; cset_tac; intuition
    | [ H : agree_on _ ?E ?E', I : val2bool (?E ?x) = false |- step (_, ?E', stmtIf ?x _ _) _ _ ] =>
      econstructor 3; eauto; rewrite <- H; eauto; cset_tac; intuition
    | [ H : val2bool _ = false |- _ ] => econstructor 3 ; try eassumption; try reflexivity
    | [ H : step (?L, _ , stmtGoto ?l _) None _, H': get ?L (counted ?l) _ |- _] =>
      econstructor; try eapply H'; eauto
    | [ H': get ?L (counted ?l) _ |- step (?L, _ , stmtGoto ?l _) None _] =>
      econstructor; try eapply H'; eauto
    | [ H : agree_on _ ?E ?E'  |- step (_, ?E', _) (Some (?E ?x)) _ ] =>
      rewrite H; [econstructor; eauto| cset_tac; intuition]
    | [ H : agree_on _ ?E' ?E  |- step (_, ?E', _) (Some (?E ?x)) _ ] =>
      rewrite <- H; [econstructor; eauto| cset_tac; intuition]
    | _ => econstructor ; eauto
  end.


Ltac one_step := eapply simS; [ eapply plusO; single_step
                              | eapply plusO; single_step
                              | ].

Ltac no_step := eapply simE; try eapply star_refl; try get_functional; try subst;
                [ try reflexivity
                | stuck
                | stuck  ].


Tactic Notation "goto_invs" tactic(tac) :=
  match goal with
    | [ |- sim (?L, _, nstmtGoto ?l ?Y) (_, _, _) ] =>
      let b := fresh "blk" in
      destruct (get_dec L (counted l)) as [[b ?]|];
        [ first [ destruct_prop (length (F.block_Z b) = length Y);
                  [ tac | no_step ]
                | destruct_prop (length (I.block_Z b) = length Y);
                  [ tac | no_step ] ]
        | no_step; tac; simpl in *; eauto ]
  end.

Inductive labIndicesSim : I.state -> IL.I.state -> Prop :=
  | labIndicesSimI (L:env (option I.block)) L' E s s' symb
    (EQ:labIndices s symb = Some s')
    (LEQ: forall f Lb Z s, L (counted f) = Some (I.blockI Lb (f,Z,s))
                 -> exists i s', pos symb f 0 = Some i /\ get L' i (IL.I.blockI Z s'))
  : labIndicesSim (L, E, s) (L', E, s').

Lemma labIndicesSim_sim σ1 σ2
  : labIndicesSim σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; destruct s; simpl in *; try monad_inv EQ.
  - case_eq (exp_eval E e); intros. 
    + one_step. eapply labIndicesSim_sim; econstructor; eauto.
    + no_step.
  - case_eq (val2bool (E x)); intros; one_step; eapply labIndicesSim_sim; econstructor; eauto.
  - case_eq (L (counted l)); intros.
    + destruct b as [? [[? ?] ?]].
      destruct_prop (l = l0); subst.
      edestruct LEQ as [? [? []]]; eauto.
      assert (x = x0) by congruence; subst.
      eapply simS. eapply plusO. econstructor; try eapply H; try reflexivity.
      admit. 
      eapply plusO. constructor; eauto. simpl. admit.
      admit.
      admit.
    + no_step. admit.
  - no_step.
  - one_step. eapply labIndicesSim_sim. econstructor; eauto.
    admit.
Admitted.


(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lyn")) ***
*** End: ***
*)

