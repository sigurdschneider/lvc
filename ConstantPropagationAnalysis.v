Require Import CSet Le.

Require Import Plus Util AllInRel CSet.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve Analysis Filter.

Require Import CMap.

Definition Dom := option (Map [var, val]).

Set Implicit Arguments.

Open Scope map_scope.

Definition join (v v' : option val) : option val :=
  match v, v' with
    | Some v, Some v' => if [v = v'] then Some v else None
    | _, _ => None
  end.

Definition joinDom (d d':Dom) : Dom :=
  match d, d' with
    | Some E, Some E' => Some (map2 join E E')
    | Some E, _ => Some E
    | _, Some E' => Some E'
    | _, _ => None
  end.


Definition domain {X} `{OrderedType X} {Y} (d:Map [X, Y])
: set X := fold (fun (k:X) _ (a:set X) => {k; a}) d ∅.

Inductive ge : option val -> option val -> Prop :=
  | geTop v : ge None (Some v)
  | geEq v : ge (Some v) (Some v).

Instance ge_dec x y : Computable (ge x y).
destruct x, y; try dec_solve.
decide (v = v0); subst; try dec_solve.
Defined.


Instance lt_find_dec d d' x : Computable ((fun x0 : var => ge (find x0 d) (find x0 d')) x).
Proof.
  hnf; intros. eapply ge_dec.
Defined.


Inductive geDom : Dom -> Dom -> Prop :=
  | geDomNone d' : geDom (Some d') None
  | geDomLt (d d':Map [var, val])
    : (forall x, x ∈ domain d ∪ domain d' -> ge (find x d) (find x d'))
      -> geDom (Some d) (Some d').

Definition set_quant_dec X `{OrderedType X} s P `{Proper _ (_eq ==> iff) P}  `{forall x, Computable (P x) } : bool :=
  SetInterface.fold (fun x b => if [P x] then b else false) s true.

Arguments set_quant_dec [X] {H} s P {H0} {H1}.

Instance set_quant_computable X `{OrderedType X} s P `{Proper _ (_eq ==> iff) P}
         `{forall x, Computable (P x) } :
  Computable (forall x, x ∈ s -> P x).
Proof.
  hnf. case_eq (set_quant_dec s P); intros.
  - left.
    revert H2. pattern s. eapply set_induction.
    + intros. eapply empty_is_empty_1 in H2. rewrite H2 in H4.
      cset_tac; intuition.
    + unfold set_quant_dec. intros.
      rewrite fold_2 in H5; eauto.
      * decide (P x); try congruence.
        eapply Add_Equal in H4.
        eapply H4 in H6. cset_tac. destruct H6.
        rewrite <- H6; eauto.
        eapply H2; eauto.
      * unfold Proper, respectful, flip; intros; subst.
        repeat destruct if; eauto.
        exfalso. rewrite H7 in n; eauto.
        exfalso. rewrite H7 in p; eauto.
      * unfold transpose, flip; intros.
        repeat destruct if; eauto.
  - right.
    revert H2. pattern s. eapply set_induction.
    + intros.
      unfold set_quant_dec in H3.
      rewrite SetProperties.fold_1 in H3; eauto; try congruence.
    + unfold set_quant_dec.
      intros. intro.
      rewrite fold_2 in H5; eauto.
      * decide (P x).
        eapply H2; eauto. intros. eapply H6.
        eapply Add_Equal in H4. rewrite H4.
        cset_tac; intuition.
        eapply Add_Equal in H4. eapply n, H6.
        rewrite H4. cset_tac; intuition.
      * unfold Proper, respectful, flip; intros; subst.
        repeat destruct if; eauto.
        exfalso. rewrite H7 in n; eauto.
        exfalso. rewrite H7 in p; eauto.
      * unfold transpose, flip; intros.
        repeat destruct if; eauto.
Defined.

Arguments set_quant_computable [X] {H} s P {H0} {H1}.

Instance geDom_dec
  :  forall d d' : Dom, Computable (geDom d d').
Proof.
  intros; hnf; intros.
  destruct d, d'; try dec_solve.
  edestruct (@set_quant_computable _ _ (domain d ∪ domain d0) (fun x => ge (find x d) (find x d0))); try dec_solve.
  - unfold Proper, respectful; intros.
    hnf in H; subst; intuition.
  - intros; eapply ge_dec.
Defined.

Instance Equal_computable (s t:Map [var, val])
: Computable (Equal s t).
pose (R:=inst_eq_dec_val).
case_eq (equal R s t); intros.
eapply MF.equal_iff in H. subst R.
eapply MF.Equal_Equivb in H. left; eauto.
intros. destruct (inst_eq_dec_val e e'); intuition.
right; intro.
eapply MF.Equal_Equivb in H0.
eapply MF.equal_iff in H0. instantiate (1:=fun x y => R x y) in H0.
congruence.
intros; simpl. subst R.
destruct (inst_eq_dec_val e e'); intuition.
Defined.

Definition ltDom d d' := ~ geDom d' d.

Lemma ltDom_dec
  :  forall d d' : Dom, Computable (ltDom d d').
Proof.
  unfold ltDom. intros.
  decide (geDom d' d).
  + right. intro. eauto.
  + left; eauto.
Defined.


Instance Dom_semilattice : PartialOrder Dom := {
  poLt := ltDom;
  poLt_dec := ltDom_dec;
  poEq := option_eq Equal;
  poEq_dec := _
}.
hnf; intros. destruct d,d'; try dec_solve.
edestruct (Equal_computable d d0); try dec_solve.
Defined.

Instance set_var_semilattice : BoundedSemiLattice Dom := {
  bottom := None;
  join := joinDom
}.
- intros. hnf. unfold joinDom.
  destruct a; eauto using @option_eq.
  econstructor. hnf; intros.
  rewrite MapFacts.map2_1bis; unfold join.
  destruct (find y d); try destruct if; eauto; congruence.
  congruence.
- hnf; intros. unfold joinDom.
  destruct a, b; simpl; eauto using @option_eq; try reflexivity.
  econstructor.
  hnf; intros.
  repeat rewrite MapFacts.map2_1bis; try reflexivity.
  destruct (find y d), (find y d0); simpl; repeat destruct if; congruence.
- intros; hnf; intros.
  destruct a,b,c; simpl; try econstructor; eauto; try reflexivity.
  hnf; intro.
  repeat rewrite MapFacts.map2_1bis; try reflexivity.
  destruct (find y d), (find y d0), (find y d1); simpl; repeat destruct if; subst; simpl; try congruence.
  destruct if; congruence.
  destruct if; congruence.
- unfold Proper, respectful; intros.
  simpl in *.
  destruct x, y, x0, y0; simpl; eauto using @option_eq; try reflexivity; try eassumption; isabsurd.
  inv H; inv H0.
  econstructor.
  intro. repeat rewrite MapFacts.map2_1bis; try reflexivity.
  unfold join. rewrite H3. rewrite H4.
  reflexivity.
- unfold Proper, respectful; intros.
  simpl in *.
  intro.
  hnf in H, H0.
  unfold joinDom in H1.
  admit.
Qed.


  Fixpoint list_update_at {X} (L:list X) (n:nat) (v:X)  :=
    match L, n with
      | x::L, 0 => v::L
      | x::L, S n => x::list_update_at L n v
      | _, _ => nil
    end.

  Lemma list_update_at_length X (l:list X) off v
  : length (list_update_at l off v) = length l.
  Proof.
    general induction l; simpl; eauto.
    - destruct off; simpl; eauto.
  Qed.

  Lemma list_update_at_get_1 X (l:list X) off v v' n
  : get (list_update_at l off v') n v
    -> n <> off
    -> get l n v.
  Proof.
    intros. general induction l; simpl in * |- *; isabsurd.
    - destruct off; simpl in *.
      * inv H; intuition.
      * inv H; intuition (eauto using get).
  Qed.

  Lemma list_update_at_get_2 X (l:list X) off v v' n
  : get (list_update_at l off v') n v
    -> n = off
    -> v = v'.
  Proof.
    intros.
    general induction H; simpl in * |- *; isabsurd.
    - destruct l; simpl in *; isabsurd; congruence.
    - destruct l; simpl in *; isabsurd.
      inv Heql0; eauto.
  Qed.

  Fixpoint update_with_list X `{OrderedType X} Y XL YL (m:Map [X, Y]) :=
    match XL, YL with
      | x::XL, Some y::YL => (update_with_list XL YL m)[x <- y]
      | x::XL, None::YL => remove x (update_with_list XL YL m)
      | _, _ => m
    end.

  Local Notation "f [ w <-- x ]" := (update_with_list w x f) (at level 29, left associativity).

Definition defdom (d:Dom) : Map [var, val] :=
  match d with
    | Some d => d
    | None => empty _
  end.

Definition domupd (d:Map [var, val]) x (o:option val) : Map [var, val] :=
  match o with
    | Some xv => (d [x <- xv])
    | None => (remove x d)
  end.

Definition constant_propagation_transform st (a:list (Dom * params)*Dom) :=
  match st, a with
    | stmtExp x e s as st, (AL, d) =>
      let d' := (defdom d) in
      let d'' := domupd d' x (exp_eval (fun x => find x d') e) in
      (AL, anni1 (Some d''))
    | stmtIf e s t as st, (AL, d) =>
      let d := defdom d in
      let ai :=
          if [exp_eval (fun x => find x d) e = Some val_true] then
              match e with
                | BinOp 3 (Var x) (Con c) => anni2opt (Some (Some (d[x <- c]))) None
                | _ => anni2opt (Some (Some d)) None
              end
          else if [exp_eval (fun x => find x d) e = Some val_false] then
            match e with
              | Var x => anni2opt None (Some (Some (d[x <- 0])))
(*            | BinOp 4 (Var x) (Con c) => anni2opt None (Some (Some (d[x <- c]))) *)
              | _ => anni2opt None (Some (Some d))
            end
          else
            anni2opt (Some (Some d)) (Some (Some d))
      in
      (AL, ai)
    | stmtGoto f Y as st, (AL, d) =>
      let d := defdom d in
      let df := nth (counted f) AL (bottom, nil) in
      let Yc := List.map (fun e => exp_eval (fun x => find x d) e) Y in
      (* we assume renamed apart here, so it's ok to leave definitions
       in d[X <-- Yc] that are /not/ defined at the point where f is defined *)
      let d' := (Some (d [snd df <-- Yc])) in
      (list_update_at AL (counted f) (joinDom (fst df) d', snd df), anni1 d')
    | stmtReturn e as st, (AL, d) =>
      let d := defdom d in
      (AL, anni1 (Some d))
    | stmtExtern x f Y s as st, (AL, d) =>
      let d := defdom d in
      (* we assume renamed apart here, and dont zero x *)
      (AL, anni1 (Some d))
    | stmtLet Z s t as st, (AL, d) =>
      let d' := defdom d in
      (* we assume renamed apart here, and dont zero Z *)
      (AL, anni2 d (Some d'))
  end.

Instance list_equal_computable X `{@EqDec X eq _}
: forall (L L':list X), Computable (eq L L').
Proof.
  intros. decide (length L = length L').
  - general induction L; destruct L'; isabsurd; try dec_solve.
    decide (a = x); try dec_solve.
    edestruct IHL with (L':=L'); eauto; subst; try dec_solve.
  - right; intro; subst. eauto.
Qed.


Instance Dom_params_semilattice : PartialOrder (Dom * params) := {
  poLt p p' := poLt (fst p) (fst p') /\ snd p = snd p';
  poLt_dec := _;
  poEq p p' := poEq (fst p) (fst p') /\ snd p = snd p';
  poEq_dec := _
}.
- intros. decide (poLt (fst d) (fst d')); decide (snd d = snd d'); try dec_solve.
- intros. decide (poEq (fst d) (fst d')); decide (snd d = snd d'); try dec_solve.
Defined.



Definition constant_propagation_analysis :=
  SSA.makeForwardAnalysis _ Dom_params_semilattice constant_propagation_transform (fun Z an => (an, Z)) fst.


(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
