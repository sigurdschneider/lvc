Require Import CSet Le.

Require Import Plus Util AllInRel CSet.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve Analysis Filter Lattice.

Require Import CMap.

Set Implicit Arguments.

Open Scope map_scope.

Definition Dom := Map [var, withTop val].

Definition join (v v' : option (withTop val)) : option (withTop val) :=
  match v, v' with
    | Some (wTA v), Some (wTA v') => if [v = v'] then Some (wTA v) else Some Top
    | Some (Top), _ => Some Top
    | _, Some Top => Some Top
    | Some (wTA v), _ => Some (wTA v)
    | _, Some (wTA v) => Some (wTA v)
    | None, None => None
  end.

Definition joinDom (d d':Dom) : Dom := map2 join d d'.

Definition domain {X} `{OrderedType X} {Y} (d:Map [X, Y])
: set X := of_list (List.map fst (elements d)).

Lemma domain_join (d d':Dom)
: domain (map2 join d d') [=] domain d ∪ domain d'.
Proof.
  unfold domain. split; intros.
  - eapply of_list_1 in H.
Admitted.


Inductive lt : option (withTop val) -> option (withTop val) -> Prop :=
  | ltTop v : lt (Some v) (Some Top)
  | ltBot w : lt None (Some w).

Instance lt_dec x y : Computable (lt x y).
destruct x, y; try dec_solve.
destruct w, w0; dec_solve.
Defined.

Instance lt_find_dec d d' x : Computable ((fun x0 : var => lt (find x0 d) (find x0 d')) x).
Proof.
  hnf; intros. eapply lt_dec.
Defined.

Definition ltDom (d d': Dom) : Prop :=
 (forall x, x ∈ domain d ∪ domain d' -> lt (find x d) (find x d')).

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

Instance ltDom_dec
  :  forall d d' : Dom, Computable (ltDom d d').
Proof.
  intros; hnf; intros.
  edestruct (@set_quant_computable _ _ (domain d ∪ domain d') (fun x => lt (find x d) (find x d'))).
  - unfold Proper, respectful; intros.
    hnf in H; subst; intuition.
  - intros; eapply lt_dec.
  - eauto.
  - right; eauto.
Defined.

Instance Equal_computable (s t:Map [var, withTop val])
: Computable (Equal s t).
pose (R:=@withTop_eq_dec _ _ inst_eq_dec_val).
case_eq (equal R s t); intros.
eapply MF.equal_iff in H. subst R.
eapply MF.Equal_Equivb in H. left; eauto.
intros. destruct (withTop_eq_dec val e e'); intuition.
right; intro.
eapply MF.Equal_Equivb in H0.
eapply MF.equal_iff in H0. instantiate (1:=fun x y => R x y) in H0.
congruence.
intros; simpl. subst R.
destruct (withTop_eq_dec val e e'); intuition.
Defined.

Lemma not_domain_find {X} `{OrderedType X} {Y} (d:Map [X, Y]) x
: x ∉ domain d -> find x d = None.
Proof.
  unfold domain. intros.
  case_eq (find x d); intros; eauto.
  exfalso. eapply H0.
  rewrite MapFacts.elements_o in H1.
  Lemma findA_get A B (L:list (A * B)) f v
  : findA f L = Some v
    -> exists x n, get L n x /\ snd x = v /\ f (fst x).
  Proof.
    general induction L; simpl; eauto.
    - simpl in H. destruct a. destruct if in H.
    + inv H.
      eexists (a,v). eexists 0. repeat split; eauto using get. simpl.
      rewrite <- Heq. eapply I.
    + edestruct IHL as [? [? ]]; dcr; eauto.
      do 2 eexists; eauto using get.
  Qed.
  eapply findA_get in H1. destruct H1 as [? [? ]]; dcr; subst.
  unfold MapFacts.eqb in H5.
  cbv in H5. destruct x0.
  pose proof (_compare_spec x x0).
  Transparent compare. unfold compare in H5.
  inv H1; rewrite  <- H3 in H5; intuition.
  rewrite H4.
  eapply get_in_of_list. change x0 with (fst (x0, y)). eapply map_get_1; eauto.
Qed.

Lemma domain_find {X} `{OrderedType X} {Y} (d:Map [X, Y]) x
: x ∈ domain d -> exists v, find x d = Some v.
Proof.
  unfold domain.
  case_eq (find x d); intros; eauto.
  exfalso.
  admit.
Qed.


Lemma lt_join x y x' y'
: lt y x
  -> lt y' x'
  -> lt (join y y') (join x x').
Proof.
  intros.
  inv H; inv H0; simpl; eauto using lt;
  try destruct v; try destruct v0; try destruct w; eauto using lt.
  - destruct if; eauto using lt.
  - destruct w0; eauto. destruct if; eauto using lt.
Qed.

Lemma join_bot_right (y:Dom) x0
  : join (find x0 y) ⎣⎦ = find x0 y.
Proof.
  destruct (find x0 y); simpl; eauto.
  destruct w; eauto.
Qed.

Lemma join_bot_left (y:Dom) x0
  : join ⎣⎦ (find x0 y) = find x0 y.
Proof.
  destruct (find x0 y); simpl; eauto.
  destruct w; eauto.
Qed.

Lemma ltDom_join x y x' y'
: ltDom y x
  -> ltDom y' x'
  -> ltDom (joinDom y y') (joinDom x x').
Proof.
  unfold ltDom, joinDom.
  intros.
  repeat rewrite MapFacts.map2_1bis; eauto.
  repeat rewrite domain_join in H1.
  cset_tac.
  decide (x0 ∈ domain y);
  decide (x0 ∈ domain y');
  decide (x0 ∈ domain x);
  decide (x0 ∈ domain x'); (try now intuition);
  repeat match goal with
    | [H' : ?x ∈ domain y |- _ ] => exploit (H x); eauto;
                                 eapply domain_find in H'; destruct H'
    | [H' : ?x ∈ domain x |- _ ] => exploit (H x); eauto;
                                 eapply domain_find in H'; destruct H'
    | [H' : ?x ∈ domain y' |- _ ] => exploit (H0 x); eauto;
                                 eapply domain_find in H'; destruct H'
    | [H' : ?x ∈ domain x' |- _ ] => exploit (H0 x); eauto;
                                 eapply domain_find in H'; destruct H'
  end; (try now eapply lt_join; eauto);
  repeat match goal with
      | [H' : ?x ∉ domain ?y |- _ ] => eapply not_domain_find in H'; rewrite H'
         end;
  repeat rewrite join_bot_right;
  repeat rewrite join_bot_left; eauto; simpl;
  repeat match goal with
    | [H : lt ?x ?y, H' : ?y = None |- _ ] => rewrite H' in H; inv H
  end.
  rewrite H2. econstructor.
  rewrite H2. econstructor.
Qed.

Set Implicit Arguments.

Instance Dom_semilattice_ltDom : PartialOrder Dom := {
  poLt := ltDom;
  poLt_dec := ltDom_dec;
  poEq := Equal;
  poEq_dec := _
}.

Instance set_var_semilattice : BoundedSemiLattice Dom := {
  bottom := (@empty var _ _ (withTop val));
  join := joinDom
}.
- intros. hnf. unfold joinDom.
  intros.
  rewrite MapFacts.map2_1bis; unfold join; eauto.
  destruct (find y a); try destruct if; eauto; try congruence.
  destruct w; eauto. destruct if; eauto. congruence.
- hnf; intros. unfold joinDom.
  hnf; intros.
  repeat rewrite MapFacts.map2_1bis; try reflexivity.
  destruct (find y a), (find y b); simpl; repeat destruct if; try destruct w; try destruct w0; try congruence.
  repeat destruct if; try subst a0; eauto; try congruence.
- intros; hnf; intros.
  unfold joinDom.
  repeat rewrite MapFacts.map2_1bis; try reflexivity.
  destruct (find y a), (find y b), (find y c); simpl; repeat destruct if; subst; simpl;
    try destruct w; try destruct w0; try destruct w1; simpl; repeat destruct if; try subst;
    simpl; try congruence.
  destruct if; congruence.
  destruct if; congruence.
- unfold Proper, respectful; intros.
  simpl in *.
  intro. unfold joinDom. repeat rewrite MapFacts.map2_1bis; try reflexivity.
  unfold join. rewrite H. rewrite H0.
  reflexivity.
- unfold Proper, respectful; intros.
  eapply ltDom_join; eauto.
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
      | x::XL, y::YL => (update_with_list XL YL m)[x <- y]
      | _, _ => m
    end.

Local Notation "f [ w <-- x ]" := (update_with_list w x f) (at level 29, left associativity).

Definition domupd (d:Dom) x (o:option val) : Dom :=
  match o with
    | Some xv => (d [x <- wTA xv])
    | None => (d [x <- Top])
  end.

Definition domenv (d:Dom) (x:var) : option val :=
  match find x d with
    | Some (wTA v) => Some v
    | _ => None
  end.

Definition constant_propagation_transform st (a:list (Dom * params)*Dom) :=
  match st, a with
    | stmtExp x e s as st, (AL, d) =>
      let d' := d in
      let d'' := domupd d' x (exp_eval (domenv d') e) in
      (AL, anni1 d'')
    | stmtIf e s t as st, (AL, d) =>
      let ai :=
          if [exp_eval (domenv d) e = Some val_true] then
              match e with
                | BinOp 3 (Var x) (Con c) => anni2opt (Some (d[x <- wTA c])) None
                | _ => anni2opt (Some d) None
              end
          else if [exp_eval (domenv d) e = Some val_false] then
            match e with
              | Var x => anni2opt None (Some (d[x <- wTA 0]))
(*            | BinOp 4 (Var x) (Con c) => anni2opt None (Some (Some (d[x <- c]))) *)
              | _ => anni2opt None (Some d)
            end
          else
            anni2opt (Some d) (Some d)
      in
      (AL, ai)
    | stmtGoto f Y as st, (AL, d) =>
      let df := nth (counted f) AL (bottom, nil) in
      let Yc := List.map (fun e => match exp_eval (domenv d) e with
                        | Some v => wTA v
                        | None => Top
                        end ) Y in
      (* we assume renamed apart here, so it's ok to leave definitions
       in d[X <-- Yc] that are /not/ defined at the point where f is defined *)
      let d' := (d [snd df <-- Yc]) in
      (list_update_at AL (counted f) (joinDom (fst df) d', snd df), anni1 d')
    | stmtReturn e as st, (AL, d) =>
      (AL, anni1 d)
    | stmtExtern x f Y s as st, (AL, d) =>
      (* we assume renamed apart here, and dont zero x *)
      (AL, anni1 d)
    | stmtLet Z s t as st, (AL, d) =>
      (* we assume renamed apart here, and dont zero Z *)
      (AL, anni2 d d)
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
