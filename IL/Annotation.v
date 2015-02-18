Require Import List.
Require Import Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList IL DecSolve.
Require Import Libs.PartialOrder.

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
   | stmtApp l Y => ann0 a
   | stmtReturn x => ann0 a
   | stmtExtern x f Y s => ann1 a (setAnn s a)
   | stmtFun Z s1 s2 => ann2 a (setAnn s1 a) (setAnn s2 a)
   end.

Fixpoint setTopAnn A (s:ann A) (a:A) : ann A :=
  match s with
   | ann0 _ => ann0 a
   | ann1 _ s' => ann1 a s'
   | ann2 _ s1 s2 => ann2 a s1 s2
   end.

Lemma getAnn_setTopAnn A (an:ann A) a
 : getAnn (setTopAnn an a) = a.
Proof.
  destruct an; eauto.
Qed.

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
  : annotation (stmtApp l Y) (ann0 a)
| antReturn x a
  : annotation (stmtReturn x) (ann0 a)
| antExtern x f Y s a sa
  : annotation s sa
    -> annotation (stmtExtern x f Y s) (ann1 a sa)
| antLet Z s t a sa ta
  : annotation s sa
    -> annotation t ta
    -> annotation (stmtFun Z s t) (ann2 a sa ta).

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
  destruct (IHs a0);
    try (now left; econstructor; eauto);
    try (now right; inversion 1; eauto).
  destruct (IHs1 a2), (IHs2 a3);
    try (now left; econstructor; eauto);
    try (now right; inversion 1; eauto).
Defined.

Inductive ann_R {A B} (R:A->B->Prop) : ann A -> ann B -> Prop :=
  | annLt1 a b an bn
    : R a b
      -> ann_R R an bn
      -> ann_R R (ann1 a an) (ann1 b bn)
  | annLt2 a ans ant b bns bnt
    : R a b
      -> ann_R R ans bns
      -> ann_R R ant bnt
      -> ann_R R (ann2 a ans ant) (ann2 b bns bnt)
  | annLt0 a b
      : R a b
      -> ann_R R (ann0 a) (ann0 b).

Lemma ann_R_get A B (R: A-> B-> Prop) a b
: ann_R R a b
  -> R (getAnn a) (getAnn b).
Proof.
  intros. inv H; eauto.
Qed.

Instance ann_R_refl {A} {R} `{Reflexive A R} : Reflexive (ann_R R).
Proof.
  hnf in H.
  hnf; intros. general induction x; eauto using ann_R.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Instance ann_R_sym {A} {R} `{Symmetric A R} : Symmetric (ann_R R).
Proof.
  hnf in H.
  hnf; intros. general induction H0; eauto using ann_R.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Instance ann_R_trans A R `{Transitive A R} : Transitive (ann_R R).
Proof.
  hnf; intros ? ? ? B C.
  general induction B; inv C; econstructor; eauto.
Qed.

Instance ann_R_ann1_pe_morphism X `{OrderedType X}
: Proper (@pe X _ ==> ann_R (@pe X _) ==> ann_R (@pe X _)) (@ann1 _).
Proof.
  unfold Proper, respectful; intros.
  econstructor; eauto.
Qed.

Instance ordered_type_lt_dec A `{OrderedType A} (a b: A)
: Computable (_lt a b).
pose proof (_compare_spec a b).
destruct (_cmp a b).
right; inv H0. hnf; intros. eapply (lt_not_eq H2 H1).
left. inv H0; eauto.
right; inv H0. intro. eapply (lt_not_gt H1 H2).
Defined.

Instance ann_R_dec A B (R:A->B->Prop)
         `{forall a b, Computable (R a b)} (a:ann A) (b:ann B) :
  Computable (ann_R R a b).
Proof.
  revert a b.
  fix 1.
  destruct a; destruct b; try dec_solve.
  + decide (R a a0); dec_solve.
  + decide (R a a1); try dec_solve;
    edestruct ann_R_dec with (a:=a0) (b:=b); hnf in *;
    try eassumption; try dec_solve.
  + decide (R a1 a); try dec_solve.
    destruct (ann_R_dec a2 b1); try dec_solve.
    destruct (ann_R_dec a3 b2); try dec_solve.
Defined.

Instance PartialOrder_ann Dom `{PartialOrder Dom}
: PartialOrder (ann Dom) := {
  poLe := ann_R poLe;
  poLe_dec := @ann_R_dec _ _ poLe poLe_dec;
  poEq := ann_R poEq;
  poEq_dec := @ann_R_dec _ _ poEq poEq_dec
}.

Instance getAnn_ann_R_morphism A (R:A->A->Prop)
: Proper (ann_R R ==> R) (getAnn).
Proof.
  unfold Proper, respectful; intros.
  inv H; simpl; eauto.
Qed.

Hint Extern 20 (ann_R _ ?a ?a') => (is_evar a ; fail 1)
                                    || (has_evar a ; fail 1)
                                    || (is_evar a' ; fail 1)
                                    || (has_evar a'; fail 1)
                                    || reflexivity.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
