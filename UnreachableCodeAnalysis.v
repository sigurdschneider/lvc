Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet ListUpdateAt.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve Filter.
Require Import Analysis AnalysisForward Terminating.

Remove Hints trans_eq_bool.

Set Implicit Arguments.


Lemma tab_false_impb Dom `{PartialOrder Dom} AL AL'
  : poLe AL AL'
    -> PIR2 impb (tab false ‖AL‖) (tab false ‖AL'‖).
Proof.
  intros. hnf in H0.
  general induction H0; simpl; unfold impb; eauto using @PIR2.
Qed.

Lemma zip_orb_impb Dom `{PartialOrder Dom} AL AL' BL BL'
  : poLe AL AL'
    -> poLe BL BL'
    -> PIR2 impb (orb ⊜ AL BL) (orb ⊜ AL' BL').
Proof.
  unfold poLe; simpl.
  intros A B.
  general induction A; inv B; simpl; eauto using PIR2.
  - econstructor; eauto.
    unfold impb. destruct x, x0, y, y0; simpl in *; eauto.
Qed.

Lemma update_at_impb Dom `{PartialOrder Dom} AL AL' n
  : poLe AL AL'
    ->  PIR2 impb (list_update_at (tab false ‖AL‖) n true)
            (list_update_at (tab false ‖AL'‖) n true).
Proof.
  unfold poLe; simpl.
  intros A. general induction A; simpl; eauto using PIR2.
  - unfold impb. destruct n; simpl; eauto using @PIR2, tab_false_impb.
Qed.


Lemma PIR2_impb_orb A A' B B'
  : PIR2 impb A A'
    -> PIR2 impb B B'
    -> PIR2 impb (orb ⊜ A B) (orb ⊜ A' B').
Proof.
  intros AA BB. general induction AA; inv BB; simpl; eauto using @PIR2.
  econstructor; eauto.
  destruct x, x0, y, y0; inv pf0; simpl; eauto.
Qed.

Lemma PIR2_impb_orb_right A A' B
  : length A <= length B
    -> PIR2 impb A A'
    -> PIR2 impb A (orb ⊜ A' B).
Proof.
  intros LEN AA.
  general induction AA; destruct B; simpl in *; isabsurd; eauto using @PIR2.
  econstructor; eauto.
  destruct x, y, b; inv pf; simpl; eauto.
  eapply IHAA; eauto. omega.
Qed.

Lemma PIR2_impb_fold (A A':list (list bool * bool)) (B B':list bool)
  : poLe A A'
    -> poLe B B'
    -> (forall n a, get A n a -> length B <= length (fst a))
    -> poLe (fold_left (fun a (b:list bool * bool) => if snd b then orb ⊜ a (fst b) else a) A B)
           (fold_left (fun a (b:list bool * bool) => if snd b then orb ⊜ a (fst b) else a) A' B').
Proof.
  intros. simpl in *.
  general induction H; simpl; eauto.
  eapply IHPIR2; eauto using PIR2_impb_orb.
  dcr. hnf in H2.
  repeat cases; try congruence; isabsurd; eauto using PIR2_impb_orb, PIR2_impb_orb_right.
  eapply PIR2_impb_orb_right; eauto using get.
  rewrite <- (PIR2_length H2); eauto. eauto using get.
  intros. cases; eauto using get.
  rewrite zip_length3; eauto using get.
Qed.


Definition unreachable_code_transform
           (ZL:list params)
           (st:stmt)
           (d:bool)
  : anni bool :=
  match st with
  | stmtLet x e s => anni1 d
  | stmtIf e s t =>
    if d then
    anni2 (if [exp2bool e = Some false] then false else true)
          (if [exp2bool e = Some true] then false else true)
    else anni2 false false
  | stmtApp f Y => anni1 d
  | stmtReturn e => anni1 d
  | stmtExtern x f Y s => anni1 d
  | _ => anni1 false
  end.

Lemma unreachable_code_transform_monotone sT s
  : Subterm.subTerm s sT ->
    Subterm.subTerm s sT ->
    forall (ZL : 〔params〕) (a b : bool),
      a ⊑ b -> unreachable_code_transform ZL s a ⊑ unreachable_code_transform ZL s b.
Proof.
  intros; destruct s; simpl; try econstructor; simpl; eauto.
  - repeat cases; simpl in *; econstructor; simpl; eauto.
Qed.

Print Instances Terminating.

Definition unreachable_code_analysis :=
  makeForwardAnalysis (fun s => bool ) _
                      (fun sT ZL s ST => unreachable_code_transform ZL s)
                      unreachable_code_transform_monotone
                      (fun s => terminating_bool).
