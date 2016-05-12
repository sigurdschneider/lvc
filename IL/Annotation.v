Require Import List.
Require Import Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList IL DecSolve.
Require Import Libs.PartialOrder.

Set Implicit Arguments.

Inductive ann (A:Type) : Type :=
| ann0 (a:A) : ann A
| ann1 (a:A) (sa:ann A) : ann A
| ann2 (a:A) (sa:ann A) (ta:ann A) : ann A
| annF (a:A) (sa:list (ann A)) (ta:ann A).

Instance Ann_size A : Size (ann A). gen_Size. Defined.


Definition getAnn {A} (a:ann A) : A :=
  match a with
    | ann0 a => a
    | ann1 a _ => a
    | ann2 a _ _ => a
    | annF a _ _ => a
  end.

Fixpoint setTopAnn A (s:ann A) (a:A) : ann A :=
  match s with
   | ann0 _ => ann0 a
   | ann1 _ s' => ann1 a s'
   | ann2 _ s1 s2 => ann2 a s1 s2
   | annF _ s1 s2 => annF a s1 s2
   end.

Fixpoint setAnn A (a:A) (s:stmt) : ann A :=
  match s with
    | stmtLet x e s0 => ann1 a (setAnn a s0)
    | stmtIf e s1 s2 => ann2 a (setAnn a s1) (setAnn a s2)
    | stmtApp l Y => ann0 a
    | stmtReturn e => ann0 a
    | stmtExtern x f Y s0 => ann1 a (setAnn a s0)
    | stmtFun s0 s1 => annF a (List.map (snd ∘ (setAnn a)) s0) (setAnn a s1)
  end.

Lemma getAnn_setTopAnn A (an:ann A) a
 : getAnn (setTopAnn an a) = a.
Proof.
  destruct an; eauto.
Qed.

Fixpoint mapAnn X Y (f:X->Y) (a:ann X) : ann Y :=
  match a with
    | ann0 a => ann0 (f a)
    | ann1 a an => ann1 (f a) (mapAnn f an)
    | ann2 a an1 an2 => ann2 (f a) (mapAnn f an1) (mapAnn f an2)
    | annF a an1 an2 => annF (f a) (List.map (mapAnn f) an1) (mapAnn f an2)
  end.

Lemma getAnn_mapAnn A A' (a:ann A) (f:A->A')
  : getAnn (mapAnn f a) = f (getAnn a).
Proof.
  general induction a; simpl; eauto.
Qed.

Inductive annotation {A:Type} : stmt -> ann A -> Prop :=
| antExp x e s a sa
  : annotation s sa
    -> annotation (stmtLet x e s) (ann1 a sa)
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
| antLet s t a sa ta
  : length s = length sa
    -> (forall n s' sa', get sa n sa' -> get s n s' -> annotation (snd s') sa')
    -> annotation t ta
    -> annotation (stmtFun s t) (annF a sa ta).

Definition indexwise_R_dec' {A} {B} {R:A->B->Prop} LA LB (Rdec:(forall n a b, get LA n a -> get LB n b -> Computable (R a b)))
: Computable (forall n a b, get LA n a -> get LB n b -> R a b).
Proof.
unfold Computable. revert LA LB Rdec. fix 2. intros LA LB Rdec.
destruct LA, LB; try now left; isabsurd.
intros. destruct (Rdec 0 a b).
- eauto using get.
- eauto using get.
- destruct (indexwise_R_dec' LA LB).
  + intros. eauto using get.
  + left. hnf; intros. destruct n; inv H; inv H0; eauto.
  + right; intro HH. eapply n; hnf; intros; eapply HH; eauto using get.
- right; intro. eapply n; hnf; intros. eapply H; eauto using get.
Defined.

Instance annotation_dec_inst {A} {s} {a} : Computable (@annotation A s a).
Proof.
  revert a. sind s; destruct s; destruct a;
  try (now left; econstructor; eauto);
  try (now right; inversion 1; eauto).
  edestruct (IH); eauto;
    try (now left; econstructor; eauto);
    try (now right; inversion 1; eauto); eauto.
  edestruct (IH s1); edestruct (IH s2);
    try (now left; econstructor; eauto);
    try (now right; inversion 1; eauto); eauto.
  edestruct (IH); eauto;
    try (now left; econstructor; eauto);
    try (now right; inversion 1; eauto); eauto.
  decide (length s = length sa); try dec_solve.
  edestruct (IH s0); try dec_solve; eauto.
  destruct (@indexwise_R_dec' _ _ (fun a b => @annotation A (snd a) b) s sa);
    try dec_solve.
  intros. eapply IH; eauto.
  Grab Existential Variables. eauto. eauto.
Defined.

Inductive ann_R {A B} (R:A->B->Prop) : ann A -> ann B -> Prop :=
| annLt0 a b
  : R a b
    -> ann_R R (ann0 a) (ann0 b)
| annLt1 a b an bn
  : R a b
    -> ann_R R an bn
    -> ann_R R (ann1 a an) (ann1 b bn)
| annLt2 a ans ant b bns bnt
  : R a b
    -> ann_R R ans bns
    -> ann_R R ant bnt
    -> ann_R R (ann2 a ans ant) (ann2 b bns bnt)
| annLtF a ans b bns ant bnt
  : R a b
    -> length ans = length bns
    -> (forall n a b, get ans n a -> get bns n b -> ann_R R a b)
    -> ann_R R ant bnt
    -> ann_R R (annF a ans ant) (annF b bns bnt).

Lemma ann_R_get A B (R: A-> B-> Prop) a b
: ann_R R a b
  -> R (getAnn a) (getAnn b).
Proof.
  intros. inv H; eauto.
Qed.

Instance ann_R_refl {A} {R} `{Reflexive A R} : Reflexive (ann_R R).
Proof.
  hnf in H.
  hnf; intros. sinduction x; eauto using ann_R; try econstructor; eauto.
  - intros. get_functional; subst. eapply H; eauto.
Qed.

Instance ann_R_sym {A} {R} `{Symmetric A R} : Symmetric (ann_R R).
Proof.
  hnf in H.
  hnf; intros. general induction H0; eauto using ann_R; econstructor; eauto.
Qed.

Instance ann_R_trans A R `{Transitive A R} : Transitive (ann_R R).
Proof.
  hnf; intros ? ? ? B C.
  general induction B; inv C; econstructor; eauto.
  - congruence.
  - intros. edestruct get_length_eq; try eapply H0; eauto.
Qed.

Instance ann_R_Equivalence A R `{Equivalence A R} : Equivalence (ann_R R).
Proof.
  econstructor.
  - hnf; intros; reflexivity.
  - hnf; intros; symmetry; eauto.
  - hnf; intros; etransitivity; eauto.
Qed.

Instance ann_R_anti A R EqA `{Antisymmetric A R EqA} : Antisymmetric _ _ (ann_R R).
Proof.
  intros ? ? B C. general induction B; inv C; eauto using @ann_R.
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
  revert b.
  sinduction a; destruct b; try dec_solve.
  + decide (R a a0); dec_solve.
  + decide (R a a0); try dec_solve.
    edestruct (X x); hnf in *;
    try eassumption; try dec_solve.
  + decide (R a a0); try dec_solve.
    edestruct (X x1); try dec_solve; eauto.
    edestruct (X x2); try dec_solve; eauto.
  + decide (R a a0); try dec_solve.
    decide (length sa = length sa0); try dec_solve.
    edestruct (X x); try dec_solve; eauto.
    destruct (@indexwise_R_dec' _ _ (ann_R R) sa sa0); try dec_solve.
    intros. eapply X; eauto.
Defined.

Instance PartialOrder_ann Dom `{PartialOrder Dom}
: PartialOrder (ann Dom) := {
  poLe := ann_R poLe;
  poLe_dec := @ann_R_dec _ _ poLe poLe_dec;
  poEq := ann_R poEq;
  poEq_dec := @ann_R_dec _ _ poEq poEq_dec
}.
Proof.
  - intros. general induction H0; eauto using @ann_R, poEq_refl.
  - intros ? ? A B. general induction A; inv B; eauto using @ann_R, po_antisymmetric.
    + econstructor; eauto using po_antisymmetric.
Defined.

Instance getAnn_ann_R_morphism A (R:A->A->Prop)
: Proper (ann_R R ==> R) (getAnn).
Proof.
  unfold Proper, respectful; intros.
  inv H; simpl; eauto.
Qed.

Hint Extern 20 (ann_R _ ?a ?a') => progress (first [ has_evar a | has_evar a' | reflexivity ]).

Create HintDb ann discriminated.

Hint Extern 10 =>
match goal with
| [ |- context [ getAnn (mapAnn _ _) ] ] => setoid_rewrite getAnn_mapAnn
end : ann.
