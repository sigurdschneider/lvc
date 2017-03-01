Require Import CSet Le.

Require Import Plus Util AllInRel CSet.
Require Import Val Var Env IL Annotation Infra.Lattice DecSolve.
Require Import Analysis.Analysis AnalysisForwardSSA ConstantPropagation.

Require Import CMap.

Set Implicit Arguments.

Open Scope map_scope.


Definition Dom := Map [var, withTop val].

Definition join (v v' : option (withTop val)) : option (withTop val) :=
  match v, v' with
    | Some (wTA v), Some (wTA v') => if [v = v'] then Some (wTA v) else Some Top
    | Some (Top), _ => Some Top
    | _, Some Top => Some Top
    | Some (wTA v), None => Some (wTA v)
    | None, Some (wTA v) => Some (wTA v)
    | None, None => None
  end.

Definition joinDom (d d':Dom) : Dom := map2 join d d'.

Definition domain {X} `{OrderedType X} {Y} (d:Map [X, Y])
: set X := of_list (List.map fst (elements d)).

Lemma InA_eq_key_elt X `{OrderedType X} Y (x:X) (y:Y) L
  : InA eq_key_elt (x, y) L
    -> InA _eq x (fst ⊝ L).
Proof.
  intros IN.
  general induction IN; simpl.
  - inv H0; simpl in *; subst.
    econstructor; eauto.
  - econstructor 2; eauto.
Qed.

Lemma domain_join (d d':Dom)
: domain (map2 join d d') [=] domain d ∪ domain d'.
Proof.
  unfold domain. split; intros.
  - eapply of_list_1 in H.
    eapply InA_map_inv with (R':=eq_key_elt) in H; eauto.
    destruct H; dcr. destruct x. simpl in *; subst.
    assert (IN:In n (map2 join d d')). {
      rewrite MapFacts.elements_in_iff; eauto.
    }
    eapply map2_2 in IN.
    destruct IN; eauto.
    + eapply MapFacts.elements_in_iff in H; dcr.
      eapply InA_eq_key_elt in H1. cset_tac.
    + eapply MapFacts.elements_in_iff in H; dcr.
      eapply InA_eq_key_elt in H1. cset_tac.
  - eapply of_list_1.
    cset_tac'.
    + eapply of_list_1 in H0.
      eapply InA_map_inv with (R':=eq_key_elt) in H0; eauto.
      destruct H0; dcr. destruct x. simpl in *; subst.
      assert (IN:In n d). {
        rewrite MapFacts.elements_in_iff; eauto.
      }
      eapply of_list_1.
      enough (exists y, InA eq_key_elt (n,y) (elements (map2 join d d'))). {
        dcr. eapply InA_eq_key_elt; eauto.
      }
      eapply MapFacts.elements_in_iff.
      rewrite MapFacts.in_find_iff.
      rewrite map2_1; eauto.
      eapply MapFacts.in_find_iff in IN.
      destruct (find n d); simpl in *; isabsurd.
      repeat cases; eauto; discriminate.
    + eapply of_list_1 in H0.
      eapply InA_map_inv with (R':=eq_key_elt) in H0; eauto.
      destruct H0; dcr. destruct x. simpl in *; subst.
      assert (IN:In n d'). {
        rewrite MapFacts.elements_in_iff; eauto.
      }
      eapply of_list_1.
      enough (exists y, InA eq_key_elt (n,y) (elements (map2 join d d'))). {
        dcr. eapply InA_eq_key_elt; eauto.
      }
      eapply MapFacts.elements_in_iff.
      rewrite MapFacts.in_find_iff.
      rewrite map2_1; eauto.
      eapply MapFacts.in_find_iff in IN.
      destruct (find n d'); simpl in *; isabsurd.
      destruct (find n d); simpl; repeat cases; eauto; subst;
        discriminate.
Qed.

Inductive le : option (withTop val) -> option (withTop val) -> Prop :=
  | leTop v : le (Some (wTA v)) (Some Top)
  | leBot' w : le None (Some w)
  | leRefl v : le v v.

Instance le_dec x y : Computable (le x y).
destruct x, y; try dec_solve.
destruct w, w0; try dec_solve.
decide (a = a0); subst; try dec_solve.
Defined.

Instance le_ref : Reflexive le.
Proof.
  hnf; intros.
  destruct x; eauto using le.
Qed.

Instance le_tran : Transitive le.
Proof.
  hnf; intros.
  inv H; inv H0; eauto using le.
Qed.

Instance le_anti : Antisymmetric _ eq le.
Proof.
  hnf; intros.
  inv H; inv H0; eauto.
Qed.

Lemma le_bot a
  : le None a.
Proof.
  destruct a; eauto using le.
Qed.

Lemma not_le_irreflexive x y
: ~le x y -> x <> y.
Proof.
  intros. intro. eapply H. subst. eapply leRefl.
Qed.

Instance le_find_dec d d' x : Computable ((fun x0 : var => le (find x0 d) (find x0 d')) x).
Proof.
  hnf; intros. eapply le_dec.
Defined.

Definition leDom (d d': Dom) : Prop :=
 (forall x, le (find x d) (find x d')).

Lemma leDom_irreflexive x y
: ~leDom x y -> ~Equal x y.
Proof.
  intros. intro. eapply H.
  hnf; intros. rewrite H0. eapply leRefl; eauto.
Qed.

Lemma le_antisymmetric x y
  : le x y -> le y x -> x = y.
Proof.
  intros A B; inv A; inv B; eauto.
Qed.

Instance leDom_ref : Reflexive leDom.
Proof.
  hnf; intros. hnf; intros. reflexivity.
Qed.

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
        eapply H4 in H6. cset_tac'.
        rewrite <- H9; eauto.
      * unfold Proper, respectful, flip; intros; subst.
        repeat cases; eauto.
        exfalso. rewrite H7 in NOTCOND; eauto.
        exfalso. rewrite H7 in COND; eauto.
      * unfold transpose, flip; intros.
        repeat cases; eauto.
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
        decide (P y); decide (P x0); intros; eauto.
        -- exfalso. rewrite H7 in n; eauto.
        -- exfalso. rewrite H7 in p. eauto.
      * unfold transpose, flip; intros.
        decide (P y); decide (P x0); intros; eauto.
Defined.

Arguments set_quant_computable [X] {H} s P {H0} {H1}.



Lemma findA_get A B (L:list (A * B)) f v
  : findA f L = Some v
    -> exists x n, get L n x /\ snd x = v /\ f (fst x).
Proof.
  general induction L; simpl; eauto.
  - simpl in H. destruct a. cases in H.
    + inv H.
      eexists (a,v). eexists 0. repeat split; eauto using get.
    + edestruct IHL as [? [? ]]; dcr; eauto.
      do 2 eexists; eauto using get.
Qed.

Lemma not_domain_find {X} `{OrderedType X} {Y} (d:Map [X, Y]) x
: x ∉ domain d -> find x d = None.
Proof.
  unfold domain. intros.
  case_eq (find x d); intros; eauto.
  exfalso. eapply H0.
  rewrite MapFacts.elements_o in H1.
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
  intros IN.
  eapply of_list_get_first in IN; dcr. inv_get.
  destruct x2.
  eapply get_InA_R with (R:=eq_key_elt) in H0; eauto.
  rewrite <- MapFacts.elements_mapsto_iff in H0.
  eapply MapFacts.find_mapsto_iff in H0. simpl in *. rewrite <- H1 in H0.
  eauto.
Qed.

Lemma find_domain (X : Type) (H : OrderedType X) (Y : Type) (d : Map [X, Y]) (x : X)
  : find x d <> None -> x \In domain d.
Proof.
  intros.
  decide (x ∈ domain d); eauto.
  exfalso. eapply not_domain_find in n. congruence.
Qed.

Lemma find_domain' (X : Type) (H : OrderedType X) (Y : Type) (d : Map [X, Y]) x v
  : find x d = Some v -> x \In domain d.
Proof.
  intros.
  decide (x ∈ domain d); eauto.
  exfalso. eapply not_domain_find in n. congruence.
Qed.

Lemma le_domain_find x y' x'
  : (forall x : nat, x \In domain y' ∪ domain x' -> le (find x y') (find x x'))
    -> le (find x y') (find x x').
Proof.
  intros. specialize (H x). revert H.
  case_eq (find x y'); intros; eauto using le_bot.
  - eapply find_domain' in H; eauto.
    eapply H0. cset_tac.
Qed.

Instance leDom_dec
  :  forall d d' : Dom, Computable (leDom d d').
Proof.
  intros; hnf; intros.
  edestruct (@set_quant_computable _ _ (domain d ∪ domain d') (fun x => le (find x d) (find x d'))).
  - unfold Proper, respectful; intros.
    hnf in H; subst; intuition.
  - intros; eapply le_dec.
  - left; eauto.
    hnf; intros. eapply le_domain_find; eauto.
  - right; eauto.
Defined.

Instance Equal_computable (s t:Map [var, withTop val])
  : Computable (Equal s t).
Proof.
  pose (R:=@withTop_eq_dec _ _ inst_eq_dec_val).
  case_eq (equal R s t); intros.
  rewrite <- MapFacts.equal_iff in H. subst R.
  eapply MapFacts.Equal_Equivb in H. left; eauto.
  intros. destruct (withTop_eq_dec val e e'); intuition.
  right; intro.
  eapply MapFacts.Equal_Equivb in H0.
  eapply MapFacts.equal_iff in H0. instantiate (1:=fun x y => R x y) in H0.
  congruence.
  intros; simpl. subst R.
  destruct (withTop_eq_dec val e e'); intuition.
Defined.

Lemma lt_join x y x' y'
: le y x
  -> le y' x'
  -> le (join y y') (join x x').
Proof.
  intros.
  inv H; inv H0; simpl; eauto using le;
  try destruct x'; try destruct x; simpl; try destruct w; try cases; try destruct w0;
    try cases; subst; eauto using le.
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

Lemma join_some_inv (y y':Dom) x z
  : join (find x y) (find x y') = ⎣ z ⎦
    -> exists z',
      (find x y = Some z' \/ find x y' = Some z')
      /\ le (Some z') (Some z).
Proof.
  destruct (find x y); destruct (find x y'); simpl; repeat cases; subst;
    intros; clear_trivial_eqs; eexists; eauto using le.
Qed.

Lemma leDom_join x y x' y'
  : leDom y x
    -> leDom y' x'
    -> leDom (joinDom y y') (joinDom x x').
Proof.
  unfold leDom, joinDom.
  intros.
  repeat rewrite MapFacts.map2_1bis; eauto.
  eapply lt_join; eauto.
Qed.

Instance leDom_tran : Transitive leDom.
Proof.
  hnf. unfold leDom; intros.
  etransitivity; eauto.
Qed.

Instance leDom_anti : Antisymmetric Dom Equal leDom.
Proof.
  hnf. unfold leDom, Equal.
  intros.
  eapply le_anti; eauto.
Qed.

Set Implicit Arguments.

Instance Dom_semilattice_ltDom : PartialOrder Dom := {
  poLe := leDom;
  poLe_dec := leDom_dec;
  poEq := Equal;
  poEq_dec := _
}.
Proof.
  intros. hnf in H. hnf.
  intros. rewrite H. reflexivity.
Defined.

Lemma empty_bottom
  :  forall a : Dom, empty (withTop val) ⊑ a.
Proof.
  intros. hnf; intros.
  rewrite MapFacts.empty_o.
  eapply le_bot.
Qed.

Lemma join_idem
  : forall a, join a a = a.
Proof.
  unfold join; intros; repeat cases; eauto.
Qed.

Lemma joinDom_idem
  : forall a : Dom, joinDom a a ≣ a.
Proof.
  unfold joinDom. intros.
  hnf; intros.
  rewrite MapFacts.map2_1bis; eauto.
  rewrite join_idem; eauto.
Qed.

Lemma join_sym
  : forall a b, join a b = join b a.
Proof.
  unfold join; intros; repeat cases; eauto.
  congruence.
Qed.

Lemma joinDom_sym
  : forall a b : Dom, joinDom a b ≣ joinDom b a.
Proof.
  unfold joinDom; intros. hnf; intros.
  rewrite !MapFacts.map2_1bis; eauto.
  rewrite join_sym; auto.
Qed.

Lemma join_assoc
  : forall a b c, join (join a b) c = join a (join b c).
Proof.
  intros. rewrite join_sym.
  unfold join; repeat (cases; subst); eauto;
    destruct b; try destruct w; try destruct w0;
      try destruct w1; subst; eauto; isabsurd;
        repeat cases in Heq; repeat cases in Heq0;
          eauto; try congruence.
Qed.

Lemma joinDom_assoc
  : forall a b c : Dom, joinDom (joinDom a b) c ≣ joinDom a (joinDom b c).
Proof.
  unfold joinDom; intros. hnf; intros.
  rewrite !MapFacts.map2_1bis; eauto.
  rewrite join_assoc. reflexivity.
Qed.

Lemma join_exp
  : forall a b, le a (join a b).
Proof.
  unfold join; intros;
    repeat cases; eauto using le.
Qed.

Lemma joinDom_exp
  : forall a b : Dom, a ⊑ joinDom a b.
Proof.
  intros. unfold joinDom. hnf; intros.
  rewrite !MapFacts.map2_1bis; eauto.
  eapply join_exp.
Qed.

Instance joinDom_eq
  : Proper (poEq ==> poEq ==> poEq) joinDom.
Proof.
  unfold Proper, respectful; intros.
  hnf in H, H0.
  unfold joinDom.
  hnf; intros.
  rewrite !MapFacts.map2_1bis; eauto.
  rewrite H, H0. reflexivity.
Qed.

Instance joinDom_poLe
  : Proper (poLe ==> poLe ==> poLe) joinDom.
Proof.
  unfold Proper, respectful; intros.
  eapply leDom_join; eauto.
Qed.

Instance map_semilattice : BoundedSemiLattice Dom := {
  bottom := (@empty var _ _ (withTop val));
  join := joinDom
}.
- eapply empty_bottom.
- eapply joinDom_idem.
- eapply joinDom_sym.
- eapply joinDom_assoc.
- eapply joinDom_exp.
Defined.


Require Import MapNotations ListUpdateAt Subterm.

Definition domupd (d:Dom) x (o:option aval) : Dom :=
  match o with
    | Some xv => (d [- x <- xv -])
    | None => remove x d
  end.

Fixpoint domupd_list (m:Dom) (A:list var) (B:list (option aval)) :=
  match A, B with
  | x::A, y::B => domupd (domupd_list m A B) x y
  | _, _ => m
  end.

Definition domenv (d:Dom) (x:var) : option aval :=
  find x d.

Definition constant_propagation_transform sT ZL st (ST:subTerm st sT)
           (a:Dom)
  : anni Dom st :=
  match st as st', a return anni Dom st'  with
  | stmtLet x (Operation e) s as st, d =>
    let d' := domupd d x (op_eval (domenv d) e) in
    d'
  | stmtLet x (Call f Y) s as st, d =>
    (* we assume renamed apart here, and dont zero x *)
    d
  | stmtIf e s t as st, d =>
    if [op_eval (domenv d) e = Some (wTA val_true)] then
      (Some d, None)
    else if [op_eval (domenv d) e = Some (wTA val_false)] then
           (None, Some d)
         else if [op_eval (domenv d) e = None] then
                (None, None)
              else
                (Some d, Some d)
  | stmtApp f Y as st, d =>
    let Z := nth (counted f) ZL (nil:list var) in
    let Yc := List.map (op_eval (domenv d)) Y in
    (* we assume renamed apart here, so it's ok to leave definitions
       in d[X <-- Yc] that are /not/ defined at the point where f is defined *)
    domupd_list d Z Yc
  | stmtReturn e as st, d =>
    d
  | stmtFun F t as st, d =>
    (* we assume renamed apart here, and dont zero Z *)
    d
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


Instance eq_Refl
  : Reflexive (fun p p' : Dom * params => fst p ≣ fst p' /\ snd p = snd p').
Proof.
  intuition.
Qed.

Instance eq_Symm
  : Symmetric (fun p p' : Dom * params => fst p ≣ fst p' /\ snd p = snd p').
Proof.
  firstorder.
Qed.

Instance eq_Trans
  : Transitive (fun p p' : Dom * params => fst p ≣ fst p' /\ snd p = snd p').
Proof.
  hnf; intros; dcr; destruct y; simpl in *; subst; split; eauto.
  rewrite <- H1. eauto.
Qed.


Instance Dom_params_semilattice : PartialOrder (Dom * params) := {
  poLe p p' := poLe (fst p) (fst p') /\ snd p = snd p';
  poLe_dec := _;
  poEq p p' := poEq (fst p) (fst p') /\ snd p = snd p';
  poEq_dec := _
}.
Proof.
  - econstructor; eauto with typeclass_instances.
  - intros; dcr; split; eauto.
    rewrite H0. eauto.
  - hnf; intros; dcr; split; eauto.
    etransitivity; eauto.
  - hnf; intros; dcr; split; eauto.
    hnf; intros.
    specialize (H1 y0).
    specialize (H0 y0).
    eapply le_antisymmetric; eauto.
Qed.

Require Import Terminating OptionR.


Lemma leDom_op_eval e a b
  : leDom a b
    -> le (op_eval (domenv a) e) (op_eval (domenv b) e).
Proof.
  general induction e; simpl; eauto using le.
  - specialize (IHe _ _ H).
    inv IHe; repeat cases; eauto using le.
  - specialize (IHe1 _ _ H).
    specialize (IHe2 _ _ H).
    inv IHe1; inv IHe2; repeat cases; eauto using le.
Qed.


Ltac mlookup_eq_tac :=
  match goal with
  | [H : ?x === ?x' |- context[@find ?key ?OT ?FM ?elt ?x' (add ?x _ ?m) ] ]
    => rewrite (@MapFacts.add_eq_o key OT FM _ elt m x x' _ H)
  | [H : ?x === ?x', H' : context[@find ?key ?OT ?FM ?elt ?x' (add ?x _ ?m) ] |- _ ]
    => rewrite (@MapFacts.add_eq_o key OT FM _ elt m x x' _ H) in H'
  | [H : ?x === ?x' |- context[@find ?key ?OT ?FM ?elt ?x' (remove ?x ?m) ] ]
    => rewrite (@MapFacts.remove_eq_o key OT FM _ elt m x x' H)
  | [H : ?x === ?x', H' : context[@find ?key ?OT ?FM ?elt ?x' (remove ?x ?m) ]  |- _ ]
    => rewrite (@MapFacts.remove_eq_o key OT FM _ elt m x x' H) in H'
  end.

Ltac mlookup_neq_tac :=
   match goal with
    | [ H : ~ ?x === ?x' |- context[@find ?key ?OT ?FM ?elt ?x' (add ?x _ ?m)] ]
      => rewrite (@MapFacts.add_neq_o key OT FM _ elt m x x' _ H)
    | [ H : ~ ?x === ?x', H' : context[@find ?key ?OT ?FM ?elt ?x' (add ?x _ ?m)] |- _ ]
      => rewrite (@MapFacts.add_neq_o key OT FM _ elt m x x' _ H) in H'
    | [ H : ~ ?x === ?x' |- context[@find ?key ?OT ?FM ?elt ?x' (remove ?x ?m)] ]
      => rewrite (@MapFacts.remove_neq_o key OT FM _ elt m x x' H)
    | [ H : ~ ?x === ?x', H' : context[@find ?key ?OT ?FM ?elt ?x' (remove ?x ?m)] |- _ ]
      => rewrite (@MapFacts.remove_neq_o key OT FM _ elt m x x' H) in H'
   end.


Tactic Notation "smplmap" :=
  repeat (repeat (subst || mlookup_eq_tac || mlookup_neq_tac)).


Ltac lud :=
  repeat (smplmap ||
          match goal with
          | [ x: _, x': _ |- context [@find ?key ?OT ?FM ?elt ?x' (add ?x _ ?m) ] ]
      =>  match goal with
          | [H' : x === x' |- _ ] => fail 1
          | [H' : ~x === x' |- _ ] => fail 1
          | [H' : x === x' -> False |- _ ] => fail 1
          | [H' : x =/= x' |- _ ] => fail 1
          | [ |- _ ] => decide(x === x')
          end
    | [ x: _, x': _, H : context[find ?x (add ?x' _ _)] |- _ ]
      => match goal with
          | [H' : x === x' |- _ ] => fail 1
          | [H' : ~x === x' |- _ ] => fail 1
          | [H' : x === x' -> False |- _ ] => fail 1
          | [H' : x =/= x' |- _ ] => fail 1
          | [ |- _ ] => decide(x === x')
        end
    | [ x: _, x': _ |- context [find ?x' (remove ?x _)] ]
      => match goal with
        | [H' : x === x' |- _ ] => fail 1
        | [H' : ~x === x' |- _ ] => fail 1
        | [H' : x === x' -> False |- _ ] => fail 1
        | [H' : x =/= x' |- _ ] => fail 1
        | [ |- _ ] => decide(x === x')
        end
          end).

Lemma domupd_le a b v v' x
  : leDom a b
    -> le v v'
    -> leDom (domupd a x v) (domupd b x v').
Proof.
  unfold leDom, domupd; intros.
  invt le; repeat cases; lud; eauto using le.
Qed.

Lemma domupd_list_le a b Z Y
  : leDom a b
    -> leDom (domupd_list a Z (op_eval (domenv a) ⊝ Y))
            (domupd_list b Z (op_eval (domenv b) ⊝ Y)).
Proof.
  unfold leDom, domupd; intros.
  general induction Z; destruct Y; simpl; eauto.
  eapply domupd_le; eauto.
  hnf. eapply IHZ; eauto.
  eapply (leDom_op_eval o); eauto.
Qed.

Lemma transf_mon
  : (forall (sT s : stmt) (ST ST' : subTerm s sT) (ZL : 〔params〕) (a b : Dom),
        a ⊑ b ->
        constant_propagation_transform ZL ST a
                                       ⊑ constant_propagation_transform ZL ST' b).
Proof.
  intros.
  general induction s; simpl in *; eauto.
  - destruct e; eauto.
    eapply domupd_le; eauto.
    eapply (leDom_op_eval e); eauto.
  - exploit (leDom_op_eval e); eauto.
    repeat cases; simpl; split; eauto using @OptionR.fstNoneOrR;
      try congruence;
      invt le; try congruence.
    exfalso; eauto. exfalso; eauto.
  - destruct (get_dec ZL l); dcr.
    + erewrite get_nth; eauto; simpl.
      hnf; intros.
      eapply domupd_list_le; eauto.
    + rewrite not_get_nth_default; eauto.
Qed.

Lemma terminating_Dom
  : Terminating.Terminating Dom poLt.
Proof.
  unfold Dom.
Admitted.

Definition constant_propagation_analysis :=
  makeForwardAnalysis _ _ constant_propagation_transform transf_mon
                      (fun _ => terminating_Dom).
