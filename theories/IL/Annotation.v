Require Import Util LengthEq Get Drop Map CSet MoreList DecSolve AllInRel.
Require Import Var Val Exp Env IL.
Require Import PartialOrder Terminating .

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

Definition setTopAnn A (s:ann A) (a:A) : ann A :=
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
    | stmtFun s0 s1 => annF a (List.map (snd ∘ (setAnn a)) s0) (setAnn a s1)
  end.

Lemma getAnn_setTopAnn A (an:ann A) a
 : getAnn (setTopAnn an a) = a.
Proof.
  destruct an; eauto.
Qed.

Lemma setTopAnn_eta A (an:ann A) a
  : getAnn an = a
    -> setTopAnn an a = an.
Proof.
  intros; destruct an; simpl in *; subst; eauto.
Qed.

Fixpoint mapAnn X Y (f:X->Y) (a:ann X) : ann Y :=
  match a with
    | ann0 a => ann0 (f a)
    | ann1 a an => ann1 (f a) (mapAnn f an)
    | ann2 a an1 an2 => ann2 (f a) (mapAnn f an1) (mapAnn f an2)
    | annF a an1 an2 => annF (f a) (List.map (mapAnn f) an1) (mapAnn f an2)
  end.

Lemma getAnn_mapAnn A A' (f:A->A') (a:ann A)
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
  decide (length F = length sa); try dec_solve.
  edestruct (IH s); try dec_solve; eauto.
  destruct (@indexwise_R_dec' _ _ (fun a b => @annotation A (snd a) b) F sa);
    try dec_solve.
  intros. eapply IH; eauto.
  Grab Existential Variables. eauto. eauto.
Defined.

Lemma setAnn_annotation A (a:A) s
  : annotation s (setAnn a s).
Proof.
  sind s; destruct s; simpl; eauto using @annotation.
  - econstructor; eauto with len.
    intros; inv_get; unfold comp; simpl; eauto.
Qed.

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

Instance ann_R_anti A R Eq `{EqA:Equivalence _ Eq} `{@Antisymmetric A Eq EqA R}
  : @Antisymmetric _ (ann_R Eq) _ (ann_R R).
Proof.
  intros ? ? B C. general induction B; inv C; eauto 20 using @ann_R.
Qed.

Instance ann_R_ann0_pe_morphism X `{OrderedType X}
: Proper (@pe X _ ==> ann_R (@pe X _)) (@ann0 _).
Proof.
  unfold Proper, respectful; intros.
  econstructor; eauto.
Qed.


Instance ann_R_ann1_pe_morphism X `{OrderedType X}
: Proper (@pe X _ ==> ann_R (@pe X _) ==> ann_R (@pe X _)) (@ann1 _).
Proof.
  unfold Proper, respectful; intros.
  econstructor; eauto.
Qed.


Instance ann_R_ann2_pe_morphism X `{OrderedType X}
: Proper (@pe X _ ==> ann_R (@pe X _) ==> ann_R (@pe X _) ==> ann_R (@pe X _)) (@ann2 _).
Proof.
  unfold Proper, respectful; intros.
  econstructor; eauto.
Qed.

Instance ann_R_annF_pe_morphism X `{OrderedType X}
: Proper (@pe X _ ==> list_eq (ann_R (@pe X _)) ==> ann_R (@pe X _) ==> ann_R (@pe X _)) (@annF _).
Proof.
  unfold Proper, respectful; intros.
  econstructor; eauto using list_eq_length.
  intros.
  edestruct @list_eq_get; eauto; dcr. get_functional. eauto.
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
  - intros. general induction H0; eauto using @ann_R, poLe_refl.
Defined.

Instance getAnn_ann_R_morphism A (R:A->A->Prop)
: Proper (ann_R R ==> R) (getAnn).
Proof.
  unfold Proper, respectful; intros.
  inv H; simpl; eauto.
Qed.

Hint Extern 20 (ann_R _ ?a ?a') => progress (first [ has_evar a | has_evar a' | reflexivity ]).

Create HintDb ann discriminated.

Hint Extern 1 =>
match goal with
| [ |- context [ getAnn (mapAnn _ _) ] ] => setoid_rewrite getAnn_mapAnn
end : ann.


Hint Extern 10 =>
match goal with
| [ H : ann_R poLe ?a ?b, H': ann_R poLe ?b ?c |- ann_R poLe ?a ?c ] =>
  etransitivity; [ eapply H | eapply H' ]
| [ H : poLe ?a ?b, H': ann_R poLe ?b ?c, H'' : poLe ?c ?d |- poLe ?a ?d ] =>
  etransitivity; [ eapply H | etransitivity; [ eapply H' | eapply H''] ]
| [ H : ann_R poLe ?a ?b, H': ann_R poLe ?b ?c, H'' : ann_R poLe ?c ?d |- ann_R poLe ?a ?d ] =>
  etransitivity; [ eapply H | etransitivity; [ eapply H' | eapply H''] ]
| [ H : poLe ?a ?b, H': ann_R poLe ?b ?c |- poLe ?a ?c ] =>
  etransitivity; [ eapply H | eapply H' ]
| [ H : poLe ?a ?b, H' : ann_R poLe ?b ?c, H'' : ~ poEq ?b ?c |- poLt ?a ?c ] =>
  rewrite H; eapply poLt_intro; [ eapply H' | eapply H'']
end.

Lemma ann_R_annotation s A B (R : A -> B -> Prop) (a:ann A) (b:ann B)
  : annotation s a
    -> ann_R R a b
    -> annotation s b.
Proof.
  intros Ann AnnR.
  general induction Ann; inv AnnR; eauto using @annotation.
  - econstructor; eauto with len.
    intros. edestruct (get_length_eq _ H2 (eq_sym H6)); eauto.
Qed.

Lemma setTopAnn_annotation s A (an:ann A) a
  : annotation s an
    -> annotation s (setTopAnn an a).
Proof.
  intros. inv H; simpl; eauto using @annotation.
Qed.

Lemma ann_R_setTopAnn A B (R: A -> B -> Prop) (a:A) (b:B) an bn
  : R a b
    -> ann_R R an bn
    -> ann_R R (setTopAnn an a) (setTopAnn bn b).
Proof.
  intros. inv H0; simpl; econstructor; eauto.
Qed.

Lemma poLe_setTopAnn A `{PartialOrder A} (a b:A) an bn
  : poLe a b
    -> poLe an bn
    -> poLe (setTopAnn an a) (setTopAnn bn b).
Proof.
  intros. eapply ann_R_setTopAnn; eauto.
Qed.

Instance getAnn_poLe Dom `{PartialOrder Dom}
  : Proper (poLe ==> poLe) getAnn.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl; eauto.
Qed.

Instance getAnn_poEq Dom `{PartialOrder Dom}
  : Proper (poEq ==> poEq) getAnn.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl; eauto.
Qed.

Lemma getAnn_mapAnn_map (A B:Type) (f:A->B) L
  : getAnn ⊝ mapAnn f ⊝ L = f ⊝ getAnn ⊝ L.
Proof.
  rewrite map_map. setoid_rewrite getAnn_mapAnn.
  rewrite <- map_map. reflexivity.
Qed.

Lemma terminating_ann Dom `{PO:PartialOrder Dom}
  : Terminating Dom poLt
    -> Terminating (ann Dom) poLt.
Proof.
  intros Trm a.
  econstructor. intros ? [A _].
  induction A.
  - specialize (Trm b).
    general induction Trm.
    econstructor. intros ? [A B].
    inv A.
    eapply H0; eauto. split; eauto.
    intro. eapply B. econstructor. eauto.
  - pose proof (Trm b) as FST. clear A H.
    rename IHA into SND.
    assert (poLe bn bn) by reflexivity.
    revert H. generalize bn at 2 3.
    induction FST as [? ? FST].
    assert (poLe x x) by reflexivity.
    revert H0. generalize x at 2 3.
    induction SND as [? ? SND].
    intros.
    econstructor; intros ? [A B].
    inv A.
    decide (poEq bn bn0).
    + decide (poEq x1 b).
      exfalso; eapply B; econstructor; eauto.
      eapply FST; eauto.
    + eapply (SND bn0); eauto.
  - clear H A1 A2 ans ant a.
    assert (poLe bns bns) by reflexivity.
    revert H. generalize bns at 2 3.
    assert (poLe bnt bnt) by reflexivity.
    revert H. generalize bnt at 2 3.
    assert (poLe b b) by reflexivity.
    revert H. generalize b at 2 3.
    specialize (Trm b).
    induction Trm.
    induction IHA1.
    induction IHA2.
    intros.
    econstructor; intros ? [A B].
    inv A.
    decide (poEq b b0).
    + decide (poEq bns bns0).
      * decide (poEq bnt bnt0).
        exfalso; apply B; econstructor; eauto.
        eapply (H4 bnt0); eauto.
      * eapply (H2 bns0); eauto.
    + eapply (H0 b0); eauto.
  - clear H A.
    pose proof (Trm b) as FST.
    rename IHA into SND.
    assert (TRD:terminates poLt bns). {
      eapply terminates_list_get.
      intros. symmetry in H0; edestruct get_length_eq; eauto.
    }
    clear H0 H1 H2.
    assert (poLe bns bns) by reflexivity.
    revert H. generalize bns at 2 3.
    assert (poLe bnt bnt) by reflexivity.
    revert H. generalize bnt at 2 3.
    assert (poLe b b) by reflexivity.
    revert H. generalize b at 2 3.
    induction FST.
    induction SND.
    induction TRD.
    intros.
    econstructor; intros ? [A B].
    inv A.
    decide (poEq b b0).
    + decide (poEq bns bns0).
      * decide (poEq bnt bnt0).
        exfalso; apply B; eauto. econstructor; eauto.
        intros. eapply PIR2_nth in p0; eauto.
        dcr. get_functional. eauto.
        eapply (H2 bnt0); eauto.
      * eapply PIR2_get in H14; eauto.
        eapply (H4 bns0); eauto.
    + eapply PIR2_get in H14; eauto.
      eapply (H0 b0); eauto.
Qed.

Lemma list_get_eq A (L L':list A)
  : length L = length L'
    -> (forall n a b, get L n a -> get L' n b -> a = b)
    -> L = L'.
Proof.
  intros. length_equify. general induction H; f_equal; eauto using get.
Qed.

Lemma ann_R_eq A (a b:ann A)
  : ann_R eq a b <-> a = b.
Proof.
  split; intros; subst; eauto.
  induction H; subst; eauto.
  f_equal. eapply list_get_eq; eauto.
Qed.

Lemma setTopAnn_inv A R (an an':ann A) a
  : ann_R R (setTopAnn an a) an'
    -> R a (getAnn an').
Proof.
  intros; destruct an; inv H; simpl; eauto.
Qed.

Lemma getAnn_setAnn A s (a:A)
 : getAnn (setAnn a s) = a.
Proof.
  destruct s; eauto.
Qed.

Lemma ann_R_setTopAnn_left (A B : Type) (R : A -> B -> Prop) (a : A)
      (an : ann A) (bn : ann B)
  : R a (getAnn bn) -> ann_R R an bn -> ann_R R (setTopAnn an a) bn.
Proof.
  intros. inv H0; simpl; eauto using @ann_R.
Qed.

Smpl Add
     match goal with
     | [ H : @equiv (@ann _) _ _ ?A ?B |- _ ] => inv_if_one_ctor H A B
     end : inv_trivial.

Lemma ann_R_setTopAnn_right (A B : Type) (R : A -> B -> Prop) (b : B)
      (an : ann A) (bn : ann B)
  : R (getAnn an) b -> ann_R R an bn -> ann_R R an (setTopAnn bn b).
Proof.
  intros. inv H0; simpl; eauto using @ann_R.
Qed.


Lemma PIR2_ann_R_get X Y (R:X->Y->Prop) A B
  : PIR2 (ann_R R) A B
    -> PIR2 R (getAnn ⊝ A) (getAnn ⊝ B).
Proof.
  intros. general induction H; simpl; eauto using PIR2.
  econstructor; eauto.
  eapply ann_R_get in pf; eauto.
Qed.


Lemma getAnn_setTopAnn_zip X A (B:list X)
  : getAnn ⊝ (@setTopAnn _ ⊜ A B) = Take.take (min ❬A❭ ❬B❭) B.
Proof.
  general induction A; destruct B; isabsurd; simpl in *; eauto.
  rewrite getAnn_setTopAnn; f_equal; eauto.
Qed.
