Require Export Util Var Val Exp Env Map CSet AutoIndTac.
Require Import List.

Set Implicit Arguments.

Open Scope map_scope.

(** * Intermediate Language IL *)

(** ** Syntax *)

(** [args] is the type of the list of variables passed at a goto ... *)
Definition args := list var.
(** ... while [params] is the type of the list of formal parameters *)
Definition params := list var.

Inductive stmt : Type :=
| stmtExp    (x : var) (e: exp) (b : stmt) : stmt
| stmtIf     (x : var) (b1 : stmt) (b2 : stmt) : stmt
| stmtGoto   (l : lab) (Y:args) : stmt
| stmtReturn (x : var) : stmt
(* block f Z : rt = s in b *)
| stmtLet    (s : stmt) (Z:params) (b : stmt) : stmt.

Inductive notOccur G : stmt -> Type :=
  | ncExp x e s : x ∉ G -> notOccur G s -> notOccur G (stmtExp x e s)
  | ncIf x s t : x ∉ G -> notOccur G s -> notOccur G t -> notOccur G (stmtIf x s t)
  | ncRet x : notOccur G (stmtReturn x)
  | ncGoto l Y : fromList Y ∩ G = empty -> notOccur G (stmtGoto l Y)
  | ncLet s Z t : fromList Z ∩ G = empty -> notOccur G s -> notOccur G t 
    -> notOccur G (stmtLet s Z t).

Fixpoint freeVars (s:stmt) : cset var :=
  match s with
    | stmtExp x e s0 => freeVars s0 \ {{x}}
    | stmtIf x s1 s2 => freeVars s1 ∪ freeVars s2 ∪ {{x}}
    | stmtGoto l Y => fromList Y
    | stmtReturn x => {{x}}
    | stmtLet s1 Z s2 => (freeVars s1 \ fromList Z) ∪ freeVars s2
  end.

Lemma notOccur_incl G G' s
  : G' ⊆ G -> notOccur G s -> notOccur G' s.
Proof.
  intros A B. general induction B; eauto using notOccur, incl_not_member, incl_meet_empty.
Qed.

Inductive ann (A:Type) : stmt -> A -> Type :=
| annExp x e b a ab : ann b ab -> ann (stmtExp x e b) a
| annIf x b1 b2 a1 a2 a : ann b1 a1 -> ann b2 a2 -> ann (stmtIf x b1 b2) a
| annGoto l Y a : ann (stmtGoto l Y) a
| annReturn x a : ann (stmtReturn x) a
| annLet s Z b a1 a2 a : ann s a1 -> ann b a2 -> ann (stmtLet s Z b) a.

Fixpoint ann_map A B (f:A->B) s a (ans:ann s a) : ann s (f a) :=
 match ans in (ann s0 y) return (ann s0 (f y)) with
   | annExp x e b a0 ab ans0 => @annExp B x e b _ _ (ann_map f ans0)
   | annIf x b1 b2 a1 a2 a0 ans1 ans2 => @annIf _ _ _ _ _ _ _ (ann_map f ans1) (ann_map f ans2)
   | annGoto l Y a0 => annGoto l Y (f a0)
   | annReturn x a0 => annReturn x (f a0)
   | annLet s0 Z b a1 a2 a0 ans1 ans2 => @annLet _ _ _ _ _ _ _ (ann_map f ans1) (ann_map f ans2)
 end.

(** ** Semantics *)

Inductive block : Type :=
  blockI {
    block_E : env val;
    block_s : stmt;
    block_Z : params
  }.

Definition labenv := list block.
Definition state : Type := (env val * labenv * stmt)%type.

Definition updE X `{Defaulted X} (Ecallee : env X) (Ecaller : env X) (Z : params) (Y:args)
  : env X := 
  update_with_list Z (lookup_list Ecaller Y) Ecallee.

(** *** Functional Semantics *)

Section FunctionalSemantics.

  Inductive fstep : state -> state -> Prop :=
  | fstepExp E L x e b v
    (def:exp_eval E e = Some v)
    : fstep (E, L, stmtExp x e b) (E[x<-v], L, b)

  | fstepIfT E L
    (x:var) (b1 b2 : stmt)
    (condTrue: val2bool (E[x]) = true)
    : fstep (E, L, stmtIf x b1 b2) (E, L, b1)
    
  | fstepIfF E L
    (x:var) (b1 b2:stmt)
    (condFalse:val2bool (E[x]) = false)
    : fstep (E, L, stmtIf x b1 b2) (E, L, b2)
    
  | fstepGoto E L l Y
    blk (Ldef:get L (counted l) blk) E'
    (updOk:updE (block_E blk) E (block_Z blk) Y  = E')
    : fstep  (E,   L, stmtGoto l Y)
            (E', drop (counted l) L, block_s blk)

  | fstepLet E L 
    s Z (b:stmt) 
    : fstep (E, L, stmtLet s Z b) (E, blockI E s Z::L, b).
  
  Lemma fstep_functional s s' s'' :
    fstep s s' -> fstep s s'' -> s' = s''.
  Proof.
    induction 1; inversion 1; intros; subst; repeat get_functional; try congruence.
  Qed.

  Inductive fevalsTo : state -> val -> Prop :=
  | fevalsToRet E L x v :
      E[x] = v  -> fevalsTo (E, L, stmtReturn x) v
  | fevalsToFstep s s' v :
      fstep s s' -> fevalsTo s' v -> fevalsTo s v.

  Lemma evalsTo_functional s v v' :
    fevalsTo s v -> fevalsTo s v' -> v = v'.
  Proof.
    intros H. revert v'. induction H; intros v' H'; inv H'.
    eauto with get. inv H0. inv H.
    generalize (fstep_functional H H1). intros. subst. auto.
  Qed.
End FunctionalSemantics.

(** *** Imperative Semantics *)

Section ImperativeSemantics.

  Inductive istep : state -> state -> Prop :=
  | istepExp E L x e b v
    (def:exp_eval E e = Some v)
    : istep (E, L, stmtExp x e b) (E[x<-v], L, b)

  | istepIfT E L
    (x:var) (b1 b2 : stmt)
    (condTrue: val2bool (E[x]) = true)
    : istep (E, L, stmtIf x b1 b2) (E, L, b1)
    
  | istepIfF E L
    (x:var) (b1 b2:stmt)
    (condFalse:val2bool (E[x]) = false)
    : istep (E, L, stmtIf x b1 b2) (E, L, b2)
    
  | istepGoto E L l Y
    blk (Ldef:get L (counted l) blk) E'
    (updOk:updE E E (block_Z blk) Y = E')
    : istep (E,   L, stmtGoto l Y)
            (E', drop (counted l) L, block_s blk)

  | istepLet E L
    s Z (b:stmt)
    : istep (E, L, stmtLet s Z b) (E, blockI E s Z::L, b).
  
  Lemma istep_functional s s' s'' :
    istep s s' -> istep s s'' -> s' = s''.
  Proof.
    induction 1; inversion 1; intros; subst; repeat get_functional; try congruence.
  Qed.

  Inductive ievalsTo : state -> val -> Prop :=
  | evalsToRet E L x v :
      E[x] = v  -> ievalsTo (E, L, stmtReturn x) v
  | evalsToIstep s s' v :
      istep s s' -> ievalsTo s' v -> ievalsTo s v.

  Theorem ievalsTo_star E L s E' L' x
    : star istep (E, L, s) (E', L', stmtReturn x)
    -> ievalsTo (E, L, s) (E'[x]). 
  Proof.
    intros A. remember (E, L, s). remember (E', L', stmtReturn x).
    revert E L s E' L' x Heqp Heqp0.
    induction A; intros; subst. inv Heqp0. econstructor; reflexivity.
    destruct y as [[a b] c].
    econstructor. eassumption. eapply IHA; eauto. 
  Qed.

  Lemma ievalsTo_star_extend s s' v
    : star istep s s' -> ievalsTo s' v -> ievalsTo s v.
  Proof.
    induction 1; intros; eauto.
    econstructor; eauto.
  Qed.
  

  Lemma ievalsTo_functional s v v' :
    ievalsTo s v -> ievalsTo s v' -> v = v'.
  Proof.
    intros H. revert v'. induction H; intros v' H'; inv H'.
    eauto with get. inv H0. inv H.
    generalize (istep_functional H H1). intros. subst. auto.
  Qed.

End ImperativeSemantics.


(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr" "../il" "../isa" "../") ***
*** End: ***
*)

