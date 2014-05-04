Require Import List.
Require Export Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList OptionMap.

Set Implicit Arguments.

Open Scope map_scope.

(** * Intermediate Language IL *)

(** ** Syntax *)

(** [args] is the type of the list of variables passed at a goto ... *)
Notation "'args'" := (list exp) (at level 0).
(** ... while [params] is the type of the list of formal parameters *)
Notation "'params'" := (list var) (at level 0).

Inductive stmt : Type :=
| stmtExp    (x : var) (e: exp) (s : stmt) : stmt
| stmtIf     (e : exp) (s : stmt) (t : stmt) : stmt
| stmtGoto   (l : lab) (Y:args) : stmt
| stmtReturn (e : exp) : stmt 
(* block f Z : rt = s in b *)    
| stmtLet    (Z:params) (s : stmt) (t : stmt) : stmt.

Inductive notOccur (G:set var) : stmt -> Prop :=
  | ncExp x e s 
    : x ∉ G 
      -> notOccur G s 
      -> Exp.notOccur G e 
      -> notOccur G (stmtExp x e s)
  | ncIf e s t 
    : Exp.notOccur G e 
      -> notOccur G s 
      -> notOccur G t 
      -> notOccur G (stmtIf e s t)
  | ncRet e : Exp.notOccur G e -> notOccur G (stmtReturn e)
  | ncGoto l (Y:list exp) 
    : (forall n e, get Y n e -> Exp.notOccur G e) 
      -> notOccur G (stmtGoto l Y)
  | ncLet s Z t 
    : of_list Z ∩ G [=] ∅ 
      -> notOccur G s 
      -> notOccur G t 
      -> notOccur G (stmtLet Z s t).

Fixpoint freeVars (s:stmt) : set var :=
  match s with
    | stmtExp x e s0 => (freeVars s0 \ {{x}}) ∪ Exp.freeVars e
    | stmtIf e s1 s2 => freeVars s1 ∪ freeVars s2 ∪ Exp.freeVars e
    | stmtGoto l Y => list_union (List.map Exp.freeVars Y)
    | stmtReturn e => Exp.freeVars e
    | stmtLet Z s1 s2 => (freeVars s1 \ of_list Z) ∪ freeVars s2
  end.

Fixpoint occurVars (s:stmt) : set var :=
  match s with
    | stmtExp x e s0 => occurVars s0 ∪ {{x}}
    | stmtIf e s1 s2 => occurVars s1 ∪ occurVars s2 ∪ Exp.freeVars e
    | stmtGoto l Y => list_union (List.map Exp.freeVars Y)
    | stmtReturn e => Exp.freeVars e
    | stmtLet Z s1 s2 => freeVars s1 ∪ freeVars s2 ∪ of_list Z
  end.

Fixpoint rename (ϱ:env var) (s:stmt) : stmt :=
  match s with
    | stmtExp x e s => stmtExp (ϱ x) (rename_exp ϱ e) (rename ϱ s)
    | stmtIf e s t => stmtIf (rename_exp ϱ e) (rename ϱ s) (rename ϱ t)
    | stmtGoto l Y => stmtGoto l (List.map (rename_exp ϱ) Y)
    | stmtReturn e => stmtReturn (rename_exp ϱ e)
    | stmtLet Z s t => stmtLet (lookup_list ϱ Z) (rename ϱ s) (rename ϱ t)
  end.  

Fixpoint label_closed (n:nat) (s:stmt) : Prop :=
  match s with
    | stmtExp _ e s => label_closed n s
    | stmtIf _ s t => label_closed n s /\ label_closed n t
    | stmtGoto l _ => counted l < n
    | stmtReturn _ => True
    | stmtLet _ s t => label_closed (S n) s /\ label_closed (S n) t
  end.

Lemma notOccur_incl G G' s
  : G' ⊆ G -> notOccur G s -> notOccur G' s.
Proof.
  intros A B. general induction B; 
              eauto using notOccur, incl_not_member, incl_meet_empty,
              Exp.notOccur_antitone.
Qed.

Add Parametric Morphism : notOccur with
  signature Subset ==> eq ==> flip impl as incl_notOccur_morphism.
Proof.
  intros; hnf; intros. general induction H0; eauto 20 using notOccur, Exp.notOccur_antitone.
  - econstructor; eauto.
    eapply incl_eq; eauto using incl_empty. rewrite <- H.
    eapply incl_meet_lr; intuition.
Qed.

Add Parametric Morphism : notOccur with
  signature Equal ==> eq ==> iff as eq_cset_notOccur_morphism.
Proof.
  intros. split; intros. 
  assert (Subset y x); intuition. 
  rewrite H1; eauto.
  assert (Subset x y); intuition. 
  rewrite H1; eauto.
Qed.

(** ** Semantics *)

(** *** Functional Semantics *)
Module F.

  Inductive block : Type :=
    blockI {
      block_E : env val;
      block_Z : params;
      block_s : stmt
    }.

  Definition labenv := list block.
  Definition state : Type := (labenv * env val * stmt)%type.

  Inductive step : state -> state -> Prop :=
  | stepExp L E x e b v
    (def:exp_eval E e = Some v)
    : step (L, E, stmtExp x e b) (L, E[x<-v], b)

  | stepIfT L E 
    e (b1 b2 : stmt) v
    (def:exp_eval E e = Some v)
    (condTrue: val2bool v = true)
    : step (L, E, stmtIf e b1 b2) (L, E, b1)
    
  | stepIfF L E
    e (b1 b2:stmt) v
    (def:exp_eval E e = Some v)
    (condFalse: val2bool v = false)
    : step (L, E, stmtIf e b1 b2) (L, E, b2)
    
  | stepGoto L E l Y blk vl
    (Ldef:get L (counted l) blk)
    (len:length (block_Z blk) = length Y)
    (def:omap (exp_eval E) Y = Some vl) E'
    (updOk:(block_E blk) [block_Z blk  <-- vl] = E')
    : step  (L, E, stmtGoto l Y)
            (drop (counted l) L, E', block_s blk)

  | stepLet L E 
    s Z (t:stmt) 
    : step (L, E, stmtLet Z s t) (blockI E Z s::L, E, t).
  
  Lemma step_functional :
    functional step.
  Proof.
    induction 1; inversion 1; intros; subst; repeat get_functional; try congruence.
  Qed.

  Lemma step_dec 
  : reddec step.
  Proof.
    hnf; intros. destruct x as [[L V] []].
    - case_eq (exp_eval V e); intros. left. eauto using step.
      right. stuck.
    - case_eq (exp_eval V e); intros. 
      left. case_eq (val2bool v); intros; eauto using step.
      right. stuck.
    - destruct (get_dec L (counted l)) as [[blk A]|?].
      decide (length (block_Z blk) = length Y).
      case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      + left. econstructor. econstructor; eauto.
      + right. stuck. get_functional; subst; eauto.
      + right. stuck. eauto.
    - right. stuck.
    - left. eauto using step.
  Qed.

End F.

(** *** Imperative Semantics *)

Module I.
  Inductive block : Type :=
    blockI {
      block_Z : params;
      block_s : stmt
    }.

  Definition labenv := list block.
  Definition state : Type := (labenv * env val * stmt)%type.

  Inductive step : state -> state -> Prop :=
  | stepExp L E x e b v
    (def:exp_eval E e = Some v)
    : step (L, E, stmtExp x e b) (L, E[x<-v], b)

  | stepIfT L E 
    e (b1 b2 : stmt) v
    (def:exp_eval E e = Some v)
    (condTrue: val2bool v = true)
    : step (L, E, stmtIf e b1 b2) (L, E, b1)
    
  | stepIfF L E
    e (b1 b2:stmt) v
    (def:exp_eval E e = Some v)
    (condFalse: val2bool v = false)
    : step (L, E, stmtIf e b1 b2) (L, E, b2)
    
  | stepGoto L E l Y blk vl
    (Ldef:get L (counted l) blk)
    (len:length (block_Z blk) = length Y)
    (def:omap (exp_eval E) Y = Some vl) E'
    (updOk:E[block_Z blk  <-- vl] = E')
    : step  (L, E, stmtGoto l Y)
            (drop (counted l) L, E', block_s blk)

  | stepLet L E
    s Z (b:stmt)
    : step (L, E, stmtLet Z s b) (blockI Z s::L, E, b).
  
  Lemma step_functional : functional step.
  Proof.
    hnf.
    induction 1; inversion 1; intros; subst; repeat get_functional; try congruence.
  Qed.

  Lemma step_dec 
  : reddec step.
  Proof.
    hnf; intros. destruct x as [[L V] []].
    - case_eq (exp_eval V e); intros. left. eauto using step.
      right. stuck.
    - case_eq (exp_eval V e); intros. 
      left. case_eq (val2bool v); intros; eauto using step.
      right. stuck.
    - destruct (get_dec L (counted l)) as [[blk A]|?].
      decide (length (block_Z blk) = length Y).
      case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      + left. econstructor. econstructor; eauto.
      + right. stuck. get_functional; subst; eauto.
      + right. stuck. eauto.
    - right. stuck.
    - left. eauto using step.
  Qed.

End I.

Class StateType S := {
  step : S -> S -> Prop;
  result : S -> option val;
  step_dec : reddec step;
  step_functional : functional step
}.

Definition state_result X (s:X*env val*stmt) : option val :=
  match s with
    | (_, stmtExp _ _ _) => None
    | (_, stmtIf _ _ _) => None
    | (_, stmtGoto _ _) => None
    | (_, E, stmtReturn e) => exp_eval E e
    | (_, stmtLet _ _ _) => None
  end.

Instance statetype_F : StateType F.state := {
  step := F.step;
  result := (@state_result F.labenv);
  step_dec := F.step_dec;
  step_functional := F.step_functional
}.


Instance statetype_I : StateType I.state := {
  step := I.step;
  result := (@state_result I.labenv);
  step_dec := I.step_dec;
  step_functional := I.step_functional
}. 

Fixpoint labenvRmE (L:F.labenv) : I.labenv
  :=
  match L with
    | nil => nil
    | F.blockI E Z s::L => I.blockI Z s :: labenvRmE L
  end.

(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)

