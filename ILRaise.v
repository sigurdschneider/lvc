Require Import List.
Require Import Var IL Arith.

Global Instance nat_le_comp (a b:nat) : Computable (a < b).
eapply lt_dec; eauto.
Defined.

Fixpoint raiseL (d:nat) (k:nat) (b:stmt) :=
  match b with
    | stmtExp x e s => stmtExp x e (raiseL d k s)
    | stmtIf x s t => stmtIf x (raiseL d k s) (raiseL d k t)
    | stmtGoto l Y => 
      if [(counted l) < d]
        then stmtGoto l Y
        else stmtGoto (incc l k) Y
    | stmtReturn x => stmtReturn x
    | stmtLet Z s t => stmtLet Z (raiseL (S d) k s) (raiseL (S d) k t) 
  end.

(** raising is cummulative *)
Lemma raiseL_cumm d k k' s
  : raiseL d k (raiseL d k' s) = raiseL d (k+k') s.
revert d k k'. induction s; intros; simpl; try rewrite IHs; try rewrite IHs1; try rewrite IHs2; eauto.
repeat (destruct if; simpl in *); try now intuition.
destruct l; simpl; simpl in *. exfalso; omega.
destruct l; simpl in *.
do 2 f_equal; try omega.
Qed.

(** another form of cummulativity *)
Lemma raiseL_cumm' d k s
  : raiseL (S d) k (raiseL d 1 s) = raiseL d (S k) s.
revert d. induction s; intros; simpl; try rewrite IHs; try rewrite IHs1; try rewrite IHs2; eauto.
destruct l.
repeat (destruct if; simpl in *); intuition.
do 2 f_equal. omega.
Qed.

(** raising with 0 is identity *)
Lemma raiseL_null d s
  : raiseL d 0 s = s.
revert d. induction s; simpl; intros; f_equal; eauto. 
destruct l; simpl. destruct if; eauto.
Qed.

(** raises can be swapped *)
Lemma raiseL_swap a k d cont
  : raiseL (a + 1 + d) k (raiseL d 1 cont) = raiseL d 1 (raiseL (a+d) k cont).
revert a k d. 
induction cont; intros; simpl; try (f_equal; now trivial).
- destruct l; simpl. 
  repeat (destruct if; simpl); intuition.
  do 2 f_equal; omega.
- pose proof (IHcont1 a k (S d)). orewrite (S (a + 1 + d) = a + 1 + S d). 
  rewrite H. f_equal. f_equal. f_equal. omega.
  pose proof (IHcont2 a k (S d)). rewrite H0. 
  do 2 f_equal. omega.
Qed.



(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
