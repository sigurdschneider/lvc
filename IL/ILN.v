Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL Sim Infra.Status.

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
    | y::l => if [ x === y ] then Some n else pos l x (S n)
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

    
  | nstepGoto (L:labenv) (E:env val) (l l':lab) Y Z (s:nstmt) L' E'
    (len:length Z = length Y)
    (lEQ:l = l') (* hack: otherwise inversions confuse guardedness checker in 
                  simulation proofs*)
    (Ldef:L (counted l) = Some (blockI L' E' (l',Z,s))) E''
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
  Definition labenv_empty : labenv := fun _ => None.

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

  | nstepGoto (L:labenv) (E:env val) (l l':lab) Y Z (s:nstmt) L'
    (len:length Z = length Y)
    (lEQ: l = l')
    (Ldef:L (counted l) = Some (blockI L' (l',Z,s))) E''
    (updOk:updE E E Z Y  = E'')
    : step (L, E, nstmtGoto l Y)
           (L'[(counted l) <- Some (blockI L' (l',Z,s))], E'', s)

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

Fixpoint labIndices (s:nstmt) (symb: list lab) : status stmt :=
  match s with
    | nstmtExp x e s => sdo s' <- (labIndices s symb); Success (stmtExp x e s')
    | nstmtIf x s1 s2 => 
      sdo s1' <- (labIndices s1 symb);
      sdo s2' <- (labIndices s2 symb);
      Success (stmtIf x s1' s2')
    | nstmtGoto l Y => 
      sdo f <- option2status (pos symb l 0) "labIndices: Undeclared function" ; Success (stmtGoto (LabI f) Y)
    | nstmtReturn x => Success (stmtReturn x)
    | nstmtLet l Z s1 s2 => 
      sdo s1' <- labIndices s1 (l::symb);
      sdo s2' <- labIndices s2 (l::symb);
      Success (stmtLet Z s1' s2')
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

Inductive lab_approx : list lab -> env (option I.block) -> list IL.I.block -> Prop :=
  Lai symb L L'
    (LEQ: forall f f' s Z Lb, 
             L (counted f) = Some (I.blockI Lb (f',Z,s)) 
             -> exists i s',   
                 get L' i (IL.I.blockI Z s')
                 /\ labIndices s (drop i symb) = Success s'
                 /\ pos symb f 0 = Some i                                                             /\ lab_approx (drop (S i) symb) (Lb (* [counted f <- Some (I.blockI Lb (f, Z, s))] *)) (drop (S i) L')
                 /\ (forall l b, Lb (counted l) = Some b -> fst (fst (I.block_F b)) = l)
                 /\ (forall f i' k, pos (drop (S i) symb) f k = Some i' -> Lb (counted f) <> None) 
                 /\ f = f') 
  : lab_approx symb L L'.

Inductive labIndicesSim : I.state -> IL.I.state -> Prop :=
  | labIndicesSimI (L:env (option I.block)) L' E s s' symb
    (EQ:labIndices s symb = Success s')
    (LA:lab_approx symb L L')
    (LL:forall l b, L (counted l) = Some b -> fst (fst (I.block_F b)) = l)
    (EX:forall f i k, pos symb f k = Some i -> L (counted f) <> None)
  : labIndicesSim (L, E, s) (L', E, s').


Lemma modus_ponens P Q
: P -> (P -> Q) -> Q.
tauto.
Qed.

Tactic Notation "exploiT" tactic(tac) :=
  eapply modus_ponens;[ tac | intros].

Ltac exploit H :=
  eapply modus_ponens;[ eapply H | intros].

      
Lemma pos_add k' symb (f:lab) k i
: pos symb f k = Some i -> pos symb f (k' + k) = Some (k' + i).
Proof.
  general induction symb; eauto.
  unfold pos in *; fold pos in *.
  destruct if. congruence.
  eapply IHsymb in H. orewrite (S (k' + k) = k' + S k). eauto.
Qed.

Lemma pos_sub k' symb (f:lab) k i
: pos symb f (k' + k) = Some (k' + i) -> pos symb f k = Some i.
Proof.
  general induction symb; eauto.
  unfold pos in *; fold pos in *.
  destruct if. f_equal. inv H. omega.
  orewrite (S (k' + k) = k' + S k) in H. 
  eauto.
Qed.

Lemma pos_ge symb (l:lab) i k
: pos symb l k = Some i
  -> k <= i.
Proof.
  general induction symb. unfold pos in H; fold pos in H.
  destruct if in H. inv H. cbv in e. omega.
  exploit IHsymb; eauto. omega.
Qed.

Lemma pos_drop_eq symb (l:lab) x
: pos symb l 0 = Some x
          -> drop x symb = l::tl (drop x symb).
Proof.
  general induction symb. 
  unfold pos in H; fold pos in H. destruct if in H.
  inv H; inv e; eauto.
  destruct x. exfalso. exploit pos_ge; eauto. omega.
  simpl. erewrite IHsymb; eauto. 
  eapply (pos_sub 1); eauto.
Qed.

Lemma pos_plus symb (f:lab) n i
: pos symb f 0 = Some (n + i)
  -> pos (drop n symb) f 0 = Some i.
Proof.
  general induction n; simpl; eauto.
  destruct symb; simpl.
  + inv H.
  + eapply IHn; eauto. simpl in H; destruct if in H. 
    * inv H. 
    * eapply (pos_sub 1); eauto.
Qed.

Lemma labIndicesSim_sim σ1 σ2
  : labIndicesSim σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; destruct s; simpl in *; try monadS_inv EQ.
  - case_eq (exp_eval E e); intros. 
    + one_step. eapply labIndicesSim_sim; econstructor; eauto.
    + no_step.
  - case_eq (val2bool (E x)); intros; one_step; eapply labIndicesSim_sim; econstructor; eauto. 
  - case_eq (L (counted l)); intros.
    + destruct b as [? [[l0 Z'] s']].
      eapply option2status_inv in EQ0.
      inv LA.
      edestruct LEQ as [? [? ?]]; dcr; eauto.
      assert (x0 = x) by congruence; subst x0.
      destruct_prop (length Z' = length Y).
      eapply simS; try eapply plusO.
      econstructor. try eapply H1; eauto; try reflexivity.
      symmetry. eapply LL; eauto. eapply H. reflexivity.
      econstructor; eauto. simpl. eauto.
      eapply labIndicesSim_sim.
      econstructor; eauto. subst l0.
      * simpl.
        econstructor. simpl; intros; dcr.
        lud. inv H0.         
        assert (f = f') by (destruct f, f'; simpl in *; congruence); subst.
        do 2 eexists. split.
        eapply drop_get with (n:=0). orewrite (x + 0 = x). eauto.
        intuition. 
        eapply pos_plus. orewrite (x + 0 = x); eauto.
        simpl in *. repeat rewrite drop_tl. auto.
        eapply H6. simpl in H8. rewrite drop_tl in H8. eapply H8. eauto.
        inv H4.
        edestruct (LEQ0); eauto. destruct H9; dcr.
        eexists (S x0), x2. split; eauto using get. 
        eapply drop_get. orewrite (x + S x0 = S x + x0). eapply get_drop. eauto.
        repeat rewrite drop_tl in *. repeat rewrite drop_drop in *.
        orewrite (S x0 + x = x0 + S x); eauto.
        repeat (split; eauto). 
        exploit pos_drop_eq; [eapply H2|].
        rewrite X. unfold pos; fold pos. destruct if. congruence.
        rewrite drop_tl. eapply (pos_add 1); eauto.       
      * subst l0. intros. lud. inv H0.
        assert (l = l0) by (destruct l, l0; simpl in *; congruence); subst.                 simpl; eauto.
        eapply H5; eauto.
      * subst l. intros. lud. congruence. eapply H6; eauto. 
        exploit pos_drop_eq; [eapply H2|].
        rewrite X in H0. unfold pos in H0; fold pos in H0.
        destruct if in H0. congruence.
        simpl. rewrite <- drop_tl. eauto.
      * subst l. no_step. simpl in *. (*rewrite H in Ldef. inv Ldef. congruence. *)
        simpl in *. get_functional; subst. simpl in *. congruence.
    + eapply option2status_inv in EQ0. exfalso. eapply EX; eauto.
  - no_step.
  - one_step. eapply labIndicesSim_sim. econstructor; eauto.
    econstructor. intros. 
    + lud. 
      * inv H. do 2 eexists.
        split. econstructor. intuition. unfold pos; fold pos.
        destruct if; eauto. cbv in n; destruct f, f'; simpl in *; congruence.
        destruct f, f'; simpl in *; congruence.
      * inv LA. edestruct LEQ; eauto. destruct H2.
        eexists (S x1),x2. dcr. split; eauto using get.
        split; eauto. split; eauto.
        unfold pos; fold pos. destruct if; eauto.
                                         congruence.
        intros. eapply (pos_add 1); eauto. 
    + intros. lud; eauto. 
      inv H; eauto. destruct l, l0; simpl in *; congruence; eauto.
    + intros. lud. congruence. 
      unfold pos in H; fold pos in H. 
      destruct if in H. congruence. eapply EX; eauto.
Qed.

(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)

