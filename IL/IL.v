Require Import List.
Require Export Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList.

Set Implicit Arguments.

Open Scope map_scope.

(** * Intermediate Language IL *)

(** ** Syntax *)

(** [args] is the type of the list of variables passed at a goto ... *)
Definition args := list var.
(** ... while [params] is the type of the list of formal parameters *)
Definition params := list var.

Inductive stmt : Type :=
| stmtExp    (x : var) (e: exp) (s : stmt) : stmt
| stmtIf     (x : var) (s : stmt) (t : stmt) : stmt
| stmtGoto   (l : lab) (Y:args) : stmt
| stmtReturn (x : var) : stmt 
(* block f Z : rt = s in b *)    
| stmtLet    (Z:params) (s : stmt) (t : stmt) : stmt.

Inductive notOccur (G:set var) : stmt -> Prop :=
  | ncExp x e s : x ∉ G -> notOccur G s -> Exp.notOccur G e -> notOccur G (stmtExp x e s)
  | ncIf x s t : x ∉ G -> notOccur G s -> notOccur G t -> notOccur G (stmtIf x s t)
  | ncRet x : x ∉ G -> notOccur G (stmtReturn x)
  | ncGoto l (Y:list var) : of_list Y ∩ G [=] ∅ -> notOccur G (stmtGoto l Y)
  | ncLet s Z t : of_list Z ∩ G [=] ∅ -> notOccur G s -> notOccur G t 
    -> notOccur G (stmtLet Z s t).

Fixpoint freeVars (s:stmt) : set var :=
  match s with
    | stmtExp x e s0 => (freeVars s0 \ {{x}}) ∪ Exp.freeVars e
    | stmtIf x s1 s2 => freeVars s1 ∪ freeVars s2 ∪ {{x}}
    | stmtGoto l Y => of_list Y
    | stmtReturn x => {{x}}
    | stmtLet Z s1 s2 => (freeVars s1 \ of_list Z) ∪ freeVars s2
  end.

Fixpoint occurVars (s:stmt) : set var :=
  match s with
    | stmtExp x e s0 => occurVars s0 ∪ {{x}}
    | stmtIf x s1 s2 => occurVars s1 ∪ occurVars s2 ∪ {{x}}
    | stmtGoto l Y => of_list Y
    | stmtReturn x => {{x}}
    | stmtLet Z s1 s2 => freeVars s1 ∪ freeVars s2 ∪ of_list Z
  end.

Fixpoint rename (ϱ:env var) (s:stmt) : stmt :=
  match s with
    | stmtExp x e s => stmtExp (ϱ x) (rename_exp ϱ e) (rename ϱ s)
    | stmtIf x s t => stmtIf (ϱ x) (rename ϱ s) (rename ϱ t)
    | stmtGoto l Y => stmtGoto l (lookup_list ϱ Y)
    | stmtReturn x => stmtReturn (ϱ x)
    | stmtLet Z s t => stmtLet (lookup_list ϱ Z) (rename ϱ s) (rename ϱ t)
  end.  

Fixpoint label_closed (n:nat) (s:stmt) : Prop :=
  match s with
    | stmtExp x e s => label_closed n s
    | stmtIf x s t => label_closed n s /\ label_closed n t
    | stmtGoto l Y => counted l < n
    | stmtReturn x => True
    | stmtLet Z s t => label_closed (S n) s /\ label_closed (S n) t
  end.

Lemma notOccur_incl G G' s
  : G' ⊆ G -> notOccur G s -> notOccur G' s.
Proof.
  intros A B. general induction B; eauto using notOccur, incl_not_member, incl_meet_empty.
  econstructor; auto. eapply Exp.notOccur_antitone; eauto.
Qed.

Add Parametric Morphism : notOccur with
  signature Subset ==> eq ==> flip impl as incl_notOccur_morphism.
Proof.
  intros; hnf; intros. general induction H0; eauto 20 using notOccur.
  econstructor; eauto using Exp.notOccur_antitone. 
  econstructor; eauto.
  eapply incl_eq; eauto using incl_empty. rewrite <- H.
  eapply incl_meet_lr; intuition.
  econstructor; eauto.
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

Inductive ann (A:Type) : Type :=
| annExp     (a:A) (sa:ann A) : ann A
| annIf      (a:A) (sa:ann A) (ta:ann A) : ann A
| annGoto    (a:A) : ann A
| annReturn  (a:A) : ann A
| annLet     (a:A) (sa:ann A) (ta:ann A) : ann A.
 
Definition getAnn {A} (a:ann A) : A :=
match a with
| annExp a _ => a
| annIf a _ _ => a
| annGoto a => a
| annReturn a => a
| annLet a _ _ => a
end.

Fixpoint setAnn A (s:stmt) (a:A) : ann A :=
  match s with
   | stmtExp x e s' => annExp a (setAnn s' a)
   | stmtIf x s1 s2 => annIf a (setAnn s1 a) (setAnn s2 a)
   | stmtGoto l Y => annGoto a
   | stmtReturn x => annReturn a
   | stmtLet Z s1 s2 => annLet a (setAnn s1 a) (setAnn s2 a)
   end.

Fixpoint mapAnn X Y (f:X->Y) (a:ann X) : ann Y := 
  match a with
    | annExp a an => annExp (f a) (mapAnn f an)
    | annIf a an1 an2 => annIf (f a) (mapAnn f an1) (mapAnn f an2) 
    | annGoto a => annGoto (f a)
    | annReturn a => annReturn (f a)
    | annLet a an1 an2 => annLet (f a) (mapAnn f an1) (mapAnn f an2)
  end.

Lemma getAnn_mapAnn A A' (a:ann A) (f:A->A')
  : getAnn (mapAnn f a) = f (getAnn a).
Proof.
  general induction a; simpl; eauto.
Qed.

Inductive annotation {A:Type} : stmt -> ann A -> Prop :=
| antExp x e s a sa 
  : annotation s sa 
    -> annotation (stmtExp x e s) (annExp a sa)
| antIf x s t a sa ta 
  : annotation s sa 
    -> annotation t ta 
    -> annotation (stmtIf x s t) (annIf a sa ta)
| antGoto l Y a 
  : annotation (stmtGoto l Y) (annGoto a)
| antReturn x a 
  : annotation (stmtReturn x) (annReturn a)
| antLet Z s t a sa ta 
  : annotation s sa 
    -> annotation t ta 
    -> annotation (stmtLet Z s t) (annLet a sa ta).

Instance annotation_dec_inst {A} {s} {a} : Computable (@annotation A s a).
Proof. 
  constructor.
  revert a. induction s; destruct a; try destruct IHs;
  try (now left; econstructor; eauto);
  try (now right; inversion 1; eauto).
  destruct (IHs a0); 
    try (now left; econstructor; eauto);
    try (now right; inversion 1; eauto).
  destruct (IHs1 a2), (IHs2 a3);
    try (now left; econstructor; eauto);
    try (now right; inversion 1; eauto).
  destruct (IHs1 a2), (IHs2 a3);
    try (now left; econstructor; eauto);
    try (now right; inversion 1; eauto).
Defined.



(*
Fixpoint ann_map A B (f:A->B) s a (ans:ann s a) : ann s (f a) :=
 match ans in (ann s0 y) return (ann s0 (f y)) with
   | annExp x e b a0 ab ans0 => @annExp B x e b _ _ (ann_map f ans0)
   | annIf x b1 b2 a1 a2 a0 ans1 ans2 => @annIf _ _ _ _ _ _ _ (ann_map f ans1) (ann_map f ans2)
   | annGoto l Y a0 => annGoto l Y (f a0)
   | annReturn x a0 => annReturn x (f a0)
   | annLet s0 Z b a1 a2 a0 ans1 ans2 => @annLet _ _ _ _ _ _ _ (ann_map f ans1) (ann_map f ans2)
 end.
*)

(** ** Semantics *)
Definition updE X `{OrderedType X} (Ecallee : env X) (Ecaller : env X) (Z : params) (Y:args)
  : env X := 
  update_with_list Z (lookup_list Ecaller Y) Ecallee.

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
    (x:var) (b1 b2 : stmt)
    (condTrue: val2bool (E x) = true)
    : step (L, E, stmtIf x b1 b2) (L, E, b1)
    
  | stepIfF L E
    (x:var) (b1 b2:stmt)
    (condFalse:val2bool (E x) = false)
    : step (L, E, stmtIf x b1 b2) (L, E, b2)
    
  | stepGoto L E l Y
    blk 
    (len:length (block_Z blk) = length Y)
    (Ldef:get L (counted l) blk) E'
    (updOk:updE (block_E blk) E (block_Z blk) Y  = E')
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
    case_eq (exp_eval V e); intros. left. eauto using step.
    right. intros [A B]; inv B; congruence.
    left. case_eq (val2bool (V x)); intros; eauto using step.
    destruct (get_dec L (counted l)) as [[blk A]|?].
    destruct_prop (length (block_Z blk) = length Y).
    left. econstructor. econstructor; eauto.
    right; intros [? B]; inv B; eauto; get_functional; subst; eauto.
    right; intros [? B]; inv B; eauto; get_functional; subst; eauto.
    right; intros [? B]; inv B; eauto.
    left. eexists. econstructor.
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
    (x:var) (b1 b2 : stmt)
    (condTrue: val2bool (E x) = true)
    : step (L, E, stmtIf x b1 b2) (L, E, b1)
    
  | stepIfF L E
    (x:var) (b1 b2:stmt)
    (condFalse:val2bool (E x) = false)
    : step (L, E, stmtIf x b1 b2) (L, E, b2)
    
  | stepGoto L E l Y
    blk 
    (len:length (block_Z blk) = length Y)
    (Ldef:get L (counted l) blk) E'
    (updOk:updE E E (block_Z blk) Y = E')
    : step (L, E, stmtGoto l Y)
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
    case_eq (exp_eval V e); intros. left. eauto using step.
    right. intros [A B]; inv B; congruence.
    left. case_eq (val2bool (V x)); intros; eauto using step.
    destruct (get_dec L (counted l)) as [[blk A]|?].
    destruct_prop (length (block_Z blk) = length Y).
    left. econstructor. econstructor; eauto.
    right; intros [? B]; inv B; eauto; get_functional; subst; eauto.
    right; intros [? B]; inv B; eauto; get_functional; subst; eauto.
    right; intros [? B]; inv B; eauto.
    left. eexists. econstructor.
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
    | (_, E, stmtReturn x) => Some (E x)
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
*** coq-load-path: (("../" "Lyn")) ***
*** End: ***
*)

