Require Import CSet Le.

Require Import Plus Util AllInRel CSet OptionR.
Require Import Val Var Env IL Annotation Infra.Lattice DecSolve.
Require Import Analysis.Analysis AnalysisForwardSSA ValueOpts.ConstantPropagation.

Require Import CMap WithTop.

Set Implicit Arguments.

Open Scope map_scope.


Definition Dom := Map [var, withTop val].


Lemma wua_poLe_inv (x y : withUnknown val)
  : poLe x y -> x = y.
Proof.
  intros A; inv A.
  - f_equal. eauto.
  - eauto.
Qed.

Smpl Add 100 match goal with
             | [ H : @poLe (withUnknown val) _ ?x ?y  |- _ ] =>
               eapply wua_poLe_inv in H; subst
             | [ H : ~ ?a === ?a |- _ ] => exfalso; eapply H; reflexivity
             | [ H : @poLe (withTop _) _ (wTA _) (wTA _) |- _ ] =>
               eapply withTop_poLe_inv in H
             | [ H : @poLe _ _ (wTA _) (wTA _) |- _ ] => invc H
             | [ H : Known _ === Known _ |- _ ] => invc H
             | [ H : withUnknown_eq _ _ |- _ ] =>
               invc H
             | [ H : withTop_le _ _ |- _ ] => invc H
             | [ H : ?A === ?B |- _ ] => inv_if_ctor H A B
             | [ H : poEq ?A ?B |- _ ] => inv_if_ctor H A B
             end : inv_trivial.



Require Import MapNotations ListUpdateAt Subterm.

Definition domupd (d:Dom) x (o:aval) : Dom :=
  match o with
  | Some xv => (d [- x <- xv -])
  | None => remove x d
  end.

Fixpoint domupd_list (m:Dom) (A:list var) (B:list aval) :=
  match A, B with
  | x::A, y::B => domupd (domupd_list m A B) x y
  | _, _ => m
  end.

Definition domenv (d:Dom) (x:var) : aval :=
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
    domupd d x (Some Top)
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

Instance eq_Refl
  : Reflexive (fun p p' : Dom * params => fst p ≣ fst p' /\ snd p = snd p').
Proof.
  intuition.
Qed.

Instance eq_Symm
  : Symmetric (fun p p' : Dom * params => fst p ≣ fst p' /\ snd p = snd p').
Proof.
  hnf; intros; dcr; split; symmetry; eauto.
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
  - hnf; intros; dcr; split; eauto.
    etransitivity; eauto.
  - hnf; intros; dcr; split; eauto.
    hnf; intros.
    specialize (H1 x0).
    specialize (H0 x0).
    eapply poLe_antisymmetric; eauto.
Qed.

Require Import Terminating OptionR.


Lemma leMap_op_eval e a b
  : leMap a b
    -> poLe (op_eval (domenv a) e) (op_eval (domenv b) e).
Proof.
  general induction e; simpl; eauto using @fstNoneOrR, @withTop_le.
  - reflexivity.
  - unfold domenv.
    specialize (H n).
    destruct (find n a); eauto using fstNoneOrR.
  - specialize (IHe _ _ H).
    inv IHe; repeat cases;
      simpl in *; clear_trivial_eqs; eauto using fstNoneOrR, @withTop_le.
    econstructor. econstructor. congruence.
    congruence.
  - specialize (IHe1 _ _ H).
    specialize (IHe2 _ _ H).
    inv IHe1; inv IHe2; repeat cases;
      simpl in *; clear_trivial_eqs;
        eauto using fstNoneOrR, withTop_le.
    + econstructor; econstructor. congruence.
    + congruence.
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
  : leMap a b
    -> poLe v v'
    -> leMap (domupd a x v) (domupd b x v').
Proof.
  unfold leMap, domupd; intros.
  inv H0.
  - repeat cases; simpl; clear_trivial_eqs.
    lud; eauto using fstNoneOrR.
    eapply H.
    lud; eauto using fstNoneOrR.
    eapply H.
  - lud. econstructor; eauto.
    eapply H.
Qed.

Lemma domupd_list_le a b Z Y
  : leMap a b
    -> leMap (domupd_list a Z (op_eval (domenv a) ⊝ Y))
            (domupd_list b Z (op_eval (domenv b) ⊝ Y)).
Proof.
  unfold leMap, domupd; intros.
  general induction Z; destruct Y; simpl; eauto.
  eapply H. eapply H. eapply H.
  eapply domupd_le; eauto.
  hnf. eapply IHZ; eauto.
  eapply (leMap_op_eval o); eauto.
Qed.

Smpl Add match goal with
         | [ H : int_eq val_true val_false |- _ ] =>
           exfalso; eapply int_eq_true_false_absurd in H; eauto
         | [ H : val_true = val_false |- _ ] => inv H
         | [ H : val_false = val_true |- _ ] => inv H
         end : inv_trivial.

Lemma transf_mon
  : (forall (sT s : stmt) (ST ST' : subTerm s sT) (ZL : 〔params〕) (a b : Dom),
        a ⊑ b ->
        constant_propagation_transform ZL ST a
                                       ⊑ constant_propagation_transform ZL ST' b).
Proof.
  intros.
  general induction s; simpl in *; eauto.
  - destruct e; eauto.
    + eapply domupd_le; eauto.
      eapply (leMap_op_eval e); eauto.
    + hnf; intros. lud; eauto.
  - exploit (leMap_op_eval e); eauto.
    repeat cases; split; eauto using @fstNoneOrR;
      try congruence; rewrite COND in *; try rewrite COND0 in *;
        simpl in *;
        clear_trivial_eqs.
    inv H0; try congruence. inv H3. clear_trivial_eqs.
    rewrite <- H1 in *. isabsurd.
    inv H0; try congruence. inv H3. clear_trivial_eqs.
    rewrite <- H1 in *. isabsurd.
    inv H0; try congruence. inv H0; congruence.
  - destruct (get_dec ZL l); dcr.
    + erewrite get_nth; eauto; simpl.
      hnf; intros.
      eapply domupd_list_le; eauto.
    + rewrite not_get_nth_default; eauto.
Qed.


Definition constant_propagation_analysis :=
  makeForwardAnalysis _ _ _ constant_propagation_transform transf_mon
                      (fun _ => terminating_Dom).
