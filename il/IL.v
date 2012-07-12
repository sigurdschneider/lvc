Require Export Util Var Val Exp Env CSet Map AutoIndTac.
Require Import List.

Set Implicit Arguments.

Open Scope map_scope.

(** * Intermediate Language IL *)

(** ** Syntax *)

(** [args] is the type of the list of variables passed at a goto ... *)
Definition args := list var.
(** ... while [params] is the type of the list of formal parameters *)
Definition params := list var.
Definition param_decls := list (var*ty).

Definition paramNames (Z:param_decls) := List.map fst Z.
Lemma paramNames_length Z 
  : length Z = length (paramNames Z).
Proof.
  induction Z; simpl; eauto.
Qed.



Inductive stmt : Type :=
| stmtExp    (x : var) (e: exp) (b : stmt) : stmt
| stmtIf     (x : var) (b1 : stmt) (b2 : stmt) : stmt
| stmtGoto   (l : lab) (Y:args) : stmt
| stmtReturn (x : var) : stmt
(* block f Z : rt = s in b *)
| stmtLet    (s : stmt) (Z:params) (b : stmt) : stmt.

Inductive ann (A:Type) : stmt -> A -> Type :=
| annExp x e b a ab : ann b ab -> ann (stmtExp x e b) a
| annIf x b1 b2 a1 a2 a : ann b1 a1 -> ann b2 a2 -> ann (stmtIf x b1 b2) a
| annGoto l Y a : ann (stmtGoto l Y) a
| annReturn x a : ann (stmtReturn x) a
| annLet s Z b a1 a2 a : ann s a1 -> ann b a2 -> ann (stmtLet s Z b) a.


(** ** Semantics *)

Inductive block : Type :=
  blockI {
    block_E : env val;
    block_s : stmt;
    block_Z : params
  }.

Definition labenv := list block.
Definition state : Type := (env val * labenv * stmt)%type.

Fixpoint updE X `{Defaulted X} (Ecallee : env X) (Ecaller : env X) (Z : params) (Y : args)
  : env X := 
  match Z, Y with
  | nil, nil  => Ecallee
  | y::Z', a :: Y' => 
      (updE Ecallee Ecaller Z' Y')[y <- Ecaller[a]]
  | _, _ => Ecallee
  end.

Fixpoint updE' X `{Defaulted X} (Ecallee : env X) (Ecaller : env X) (Z : params) (Y : args)
  : env X := 
  match Z, Y with
  | nil, nil  => Ecallee
  | y::Z', a :: Y' => 
      (updE' (Ecallee[y <- Ecaller[a]]) Ecaller Z' Y')
  | _, _ => Ecallee
  end.

Definition args_for_params (Y:args) (Z:params) :=
  ((length Y = length Z) * unique Z)%type.

Definition arg_for_param (x y:var) Y Z :=
  { n : nat & (get Y n y * get Z n x)%type }.

Lemma args_for_params_each Y Z (AFP: args_for_params Y Z) x
  : x ∈ fromList Z -> { y : var & ((y ∈ fromList Y) * arg_for_param x y Y Z)%type}.
Proof.
Admitted.

Lemma updE_param' E E' Z Y x y n
  : get Z n x 
  -> get Y n y
  -> unique Z
  -> updE E E' Z Y [x] = (E'[y]).
Proof.
  intros X. revert Y. induction X; intros. inv X; simpl; simplify lookup; eauto.
  inv X0. assert (x<>x'). simpl in X1; destruct X1. 
  intro. eapply f. subst. eapply get_in; eauto. eapply inst_eq_dec_var.
  simpl. simplify lookup. eapply IHX; eauto. firstorder.
Qed.

Lemma updE_param E E' Z Y x y 
  : args_for_params Y Z
  -> arg_for_param x y Y Z
  -> updE E E' Z Y [x] = (E'[y]).
Proof.
Admitted.

Lemma updE_no_param E E' Y Z x
  : x ∉ fromList Z
  -> updE E E' Z Y [x] = E [x].
Proof.
  intros. general induction Z; simpl; destruct Y; eauto.
  destruct_prop (a=x); subst; simplify lookup.
  exfalso. eapply H. simpl; cset_tac; firstorder.
  assert (~x ∈ fromList Z) by (simpl in H; cset_tac; firstorder).
  eauto.
Qed.


Lemma updE_fresh E E' Z Y x v
  : fresh x Z 
  -> updE (E [x <- v]) E' Z Y = (updE E E' Z Y [x <- v]).
Proof.
  intros. 
  revert x v E E' Z X.
  induction Y; intros; destruct Z; simpl; eauto.
  rewrite IHY.
  destruct_prop (x=v0).
  exfalso; subst; firstorder.
  eapply map_extensionality; intros.
  eapply update_commute; eauto.
  firstorder.
Qed.

Lemma updE_updE' E Z Y E'
  : unique Z -> updE' E E' Z Y = updE E E' Z Y.
Proof.
  intros.
  revert E E' Z X.
  induction Y; intros; destruct Z; simpl; eauto.
  rewrite IHY; try eapply updE_fresh; firstorder.
Qed.

Lemma updE_Y_nil E E' Z
  : updE E E' Z nil = E.
Proof.
  revert E E'; induction Z; intros; simpl; try destruct a; eauto.
Qed.  

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
    (updOk:updE (block_E blk) E (block_Z blk) Y = E')
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
