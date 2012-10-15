Require Import List Arith.
Require Import IL.

Fixpoint raiseL (d:nat) (k:nat) (b:stmt) :=
  match b with
    | stmtExp x e s => stmtExp x e (raiseL d k s)
    | stmtIf x b1 b2 => stmtIf x (raiseL d k b1) (raiseL d k b2)
    | stmtGoto l Y => 
      if lt_dec (counted l) d
        then stmtGoto l Y
        else stmtGoto (incc l k) Y
    | stmtReturn x => stmtReturn x
    | stmtLet s Z b => stmtLet (raiseL (S d) k s) Z (raiseL (S d) k b) 
  end.

(** raising is cummulative *)
Lemma raiseL_cumm d k k' s
  : raiseL d k (raiseL d k' s) = raiseL d (k+k') s.
revert d k k'. induction s; intros; simpl; try rewrite IHs; try rewrite IHs1; try rewrite IHs2; eauto.
destruct (lt_dec (labN l) d); simpl. destruct (lt_dec (labN l) d); try (exfalso; omega); eauto.
destruct l; simpl. simpl in *.
destruct (lt_dec (k' + n0) d). exfalso. omega. f_equal. f_equal. omega.
Qed.

(** another form of cummulativity *)
Lemma raiseL_cumm' d k s
  : raiseL (S d) k (raiseL d 1 s) = raiseL d (S k) s.
revert d. induction s; intros; simpl; try rewrite IHs; try rewrite IHs1; try rewrite IHs2; eauto.
destruct (lt_dec (labN l) d); simpl. destruct (lt_dec (labN l) (S d)); try (exfalso; omega); eauto.
destruct l; simpl in * |- *.
destruct (lt_dec (S n0) (S d)); eauto. exfalso. omega. f_equal; f_equal; omega.
Qed.

(** raising with 0 is identity *)
Lemma raiseL_null d s
  : raiseL d 0 s = s.
revert d. induction s; simpl; intros; f_equal; eauto. 
destruct l; simpl. destruct (lt_dec n d); eauto.
Qed.

(** raises can be swapped *)
Lemma raiseL_swap a k d cont
  : raiseL (a + 1 + d) k (raiseL d 1 cont) = raiseL d 1 (raiseL (a+d) k cont).
revert a k d. 
induction cont; intros; simpl; try (f_equal; now trivial). 
destruct l; simpl. 
destruct (lt_dec n d), (lt_dec n (a+d)); try (exfalso; omega); simpl.
destruct (lt_dec n (a + 1 + d)), (lt_dec n d); try (exfalso; omega); trivial.
destruct (lt_dec (S n) (a + 1 + d)), (lt_dec n d); try (exfalso; omega); trivial.
destruct (lt_dec (S n) (a + 1 + d)), (lt_dec n d); try (exfalso; omega); trivial.
destruct (lt_dec (k+n) d); try (exfalso; omega). 
simpl. f_equal; f_equal; omega.
f_equal. pose proof (IHcont1 a k (S d)). assert (S (a + 1 + d) = a + 1 + S d). omega. rewrite H0. 
rewrite H. f_equal. f_equal. omega.
pose proof (IHcont2 a k (S d)). assert (S (a + 1 + d) = a + 1 + S d). omega. rewrite H0. 
rewrite H. f_equal. f_equal. omega.
Qed.