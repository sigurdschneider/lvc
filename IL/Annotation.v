Require Import List.
Require Export Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList IL.

Set Implicit Arguments.

Inductive ann (A:Type) : Type :=
| ann0 (a:A) : ann A
| ann1 (a:A) (sa:ann A) : ann A
| ann2 (a:A) (sa:ann A) (ta:ann A) : ann A.
 
Definition getAnn {A} (a:ann A) : A :=
match a with
| ann0 a => a
| ann1 a _ => a
| ann2 a _ _ => a
end.

Fixpoint setAnn A (s:stmt) (a:A) : ann A :=
  match s with
   | stmtExp x e s' => ann1 a (setAnn s' a)
   | stmtIf x s1 s2 => ann2 a (setAnn s1 a) (setAnn s2 a)
   | stmtGoto l Y => ann0 a
   | stmtReturn x => ann0 a
   | stmtLet Z s1 s2 => ann2 a (setAnn s1 a) (setAnn s2 a)
   end.

Fixpoint setTopAnn A (s:ann A) (a:A) : ann A :=
  match s with
   | ann0 _ => ann0 a
   | ann1 _ s' => ann1 a s'
   | ann2 _ s1 s2 => ann2 a s1 s2
   end.

Fixpoint mapAnn X Y (f:X->Y) (a:ann X) : ann Y := 
  match a with
    | ann1 a an => ann1 (f a) (mapAnn f an)
    | ann2 a an1 an2 => ann2 (f a) (mapAnn f an1) (mapAnn f an2) 
    | ann0 a => ann0 (f a)
  end.

Lemma getAnn_mapAnn A A' (a:ann A) (f:A->A')
  : getAnn (mapAnn f a) = f (getAnn a).
Proof.
  general induction a; simpl; eauto.
Qed.

Inductive annotation {A:Type} : stmt -> ann A -> Prop :=
| antExp x e s a sa 
  : annotation s sa 
    -> annotation (stmtExp x e s) (ann1 a sa)
| antIf x s t a sa ta 
  : annotation s sa 
    -> annotation t ta 
    -> annotation (stmtIf x s t) (ann2 a sa ta)
| antGoto l Y a 
  : annotation (stmtGoto l Y) (ann0 a)
| antReturn x a 
  : annotation (stmtReturn x) (ann0 a)
| antLet Z s t a sa ta 
  : annotation s sa 
    -> annotation t ta 
    -> annotation (stmtLet Z s t) (ann2 a sa ta).

Instance annotation_dec_inst {A} {s} {a} : Computable (@annotation A s a).
Proof. 
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
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)

