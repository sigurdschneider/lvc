Require Import CSet Le CMap CMapDomain CMapPartialOrder CMapJoinSemiLattice CMapTerminating.

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

Smpl Add 100
     match goal with
     | [ H : @Equivalence.equiv val int_eq Equivalence_eq_int' _ _ |- _ ] =>
       eapply int_eq_eq in H
     end : inv_trivial.

Lemma leMap_op_eval e a b
  : leMap a b
    -> poLe (op_eval (domenv a) e) (op_eval (domenv b) e).
Proof.
  general induction e; simpl; eauto using @fstNoneOrR, @withTop_le.
  - reflexivity.
  - unfold domenv.
    specialize (H n).
    destruct (find n a); eauto using fstNoneOrR.
  - specialize (IHe _ _ H); repeat cases; eauto using fstNoneOrR, @withTop_le.
    reflexivity.
  - specialize (IHe1 _ _ H).
    specialize (IHe2 _ _ H).
    inv IHe1; inv IHe2; repeat cases;
      simpl in *; clear_trivial_eqs;
        eauto using fstNoneOrR, withTop_le.
    + econstructor; econstructor. congruence.
Qed.


Lemma poLe_option_None X `{PartialOrder X} (x:option X)
  :  ⎣⎦ ⊑ x.
Proof.
  econstructor.
Qed.

Hint Resolve poLe_option_None.

Lemma domupd_le a b v v' x
  : leMap a b
    -> poLe v v'
    -> leMap (domupd a x v) (domupd b x v').
Proof.
  unfold leMap, domupd; intros.
  inv H0.
  - repeat cases; clear_trivial_eqs; mlud; eauto.
  - mlud; eauto.
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
    + hnf; intros. mlud; eauto.
  - exploit (leMap_op_eval e); eauto.
    repeat cases; split; eauto using @fstNoneOrR;
      try congruence; rewrite COND in *; try rewrite COND0 in *;
        simpl in *;
        clear_trivial_eqs.
    inv H0; try congruence. clear_trivial_eqs.
    rewrite <- H1 in *. isabsurd.
    inv H0; try congruence. clear_trivial_eqs.
    rewrite <- H1 in *. isabsurd.
    inv H0; try congruence. inv H0; congruence.
  - destruct (get_dec ZL l); dcr.
    + erewrite get_nth; eauto; simpl.
      hnf; intros.
      eapply domupd_list_le; eauto.
    + rewrite not_get_nth_default; eauto.
Qed.

Definition DDom (sT:stmt) := { m : Map [var, withTop val] | domain m ⊆ occurVars sT}.

Smpl Add 100
     match goal with
     | [ H : (_, _) = (_,_) |- _ ] => invc H
     end : inv_trivial.

Lemma domain_domupd_incl m x v
  : domain (domupd m x v) ⊆ {x; domain m}.
Proof.
  unfold domupd; cases.
  - rewrite domain_add. reflexivity.
  - rewrite domain_remove. cset_tac.
Qed.

Lemma domain_domupd_list_incl m x v
  : domain (domupd_list m x v) ⊆ of_list x ∪ domain m.
Proof.
  general induction x; destruct v; simpl.
  - cset_tac.
  - cset_tac.
  - cset_tac.
  - rewrite domain_domupd_incl.
    rewrite IHx; eauto. cset_tac.
Qed.

Definition cp_trans_dep sT (ZL:list params) st (ST:subTerm st sT)
           (ZLIncl: list_union (of_list ⊝ ZL) ⊆ occurVars sT) (a:DDom sT)
  : anni (DDom sT) st.
Proof.
  set (res:=(@constant_propagation_transform sT ZL st ST (proj1_sig a))).
  pose proof (subTerm_occurVars ST) as Incl. destruct a; simpl in *.
  destruct st; simpl in *.
  - destruct e.
    + refine (exist _ res _); subst res.
      rewrite domain_domupd_incl.
      revert s Incl; cset_tac.
    + refine (exist _ res _); subst res.
      rewrite domain_add.
      revert s Incl; cset_tac.
  - refine (match res return
                  (res = if [op_eval (domenv x) e = ⎣ wTA val_true ⎦] then (⎣ x ⎦, ⎣⎦) else if [op_eval (domenv x) e = ⎣ wTA val_false ⎦] then (⎣⎦, ⎣ x ⎦) else if [op_eval (domenv x) e = ⎣⎦] then (⎣⎦, ⎣⎦) else (⎣ x ⎦, ⎣ x ⎦)) -> ؟ (DDom sT) * ؟ (DDom sT)
            with
            | (Some x, Some y) => fun EQ => (Some (exist _ x _) , Some (exist _ y _))
            | (Some x, None) => fun EQ => (Some (exist _ x _) ,None)
            | (None, Some y) => fun EQ => (None, Some (exist _ y _))
            | (None, None) => fun EQ => (None,None)
            end eq_refl);
      repeat cases in EQ; clear_trivial_eqs; eauto.
  - refine (exist _ res _); subst res.
    destruct (get_dec ZL l); dcr.
    + erewrite get_nth; eauto.
      rewrite domain_domupd_list_incl.
      eapply union_incl_split; eauto.
      rewrite <- ZLIncl.
      eapply incl_list_union; eauto using map_get_1.
    + rewrite not_get_nth_default; eauto.
  - refine (exist _ res _); subst res. eauto.
  - refine (exist _ res _); subst res. eauto.
Defined.


Lemma transf_mon_dep
  : (forall (sT s : stmt) (ST ST' : subTerm s sT) (ZL : 〔params〕)
       (ZLIncl ZLIncl': list_union (of_list ⊝ ZL) ⊆ occurVars sT) (a b : DDom sT),
        a ⊑ b ->
        cp_trans_dep ZL ST ZLIncl a ⊑ cp_trans_dep ZL ST' ZLIncl' b).
Proof.
  intros. destruct a as [a aBound], b as [b bBound]; simpl in H.
  pose proof (@transf_mon sT s ST ST' ZL a b H) as LE.
  destruct s; clear_trivial_eqs; simpl in *; eauto.
  - destruct e; simpl; eauto.
  - repeat (cases in LE; simpl in *); dcr;
            clear_trivial_eqs; eauto using fstNoneOrR.
Qed.

Instance map_sig_semilattice_bound X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  : JoinSemiLattice ({ m : Map [X, Y] | domain m ⊆ U}) := {
  join x y := exist _ (join (proj1_sig x) (proj1_sig y)) _
}.
Proof.
  - destruct x,y; simpl.
    unfold joinMap. rewrite domain_join. cset_tac.
  - hnf; intros [a ?]. simpl. eapply joinDom_idem.
  - hnf; intros [a ?] [b ?]. eapply joinDom_sym.
  - hnf; intros [a ?] [b ?] [c ?]. eapply joinDom_assoc.
  - hnf; intros [a ?] [b ?]; simpl. eapply joinDom_exp.
  - simpl. unfold Proper, respectful; intros. destruct x,y,x0,y0; simpl in * |- *.
    rewrite H2, H3. reflexivity.
  - simpl. unfold Proper, respectful; intros. destruct x,y,x0,y0; simpl in * |- *.
    rewrite H3, H2. reflexivity.
Defined.

Instance map_sig_lower_bounded X `{OrderedType X} Y `{JoinSemiLattice Y} U
  : LowerBounded { m : Map [X, Y] | domain m ⊆ U} :=
  {
    bottom := exist _ (empty _) (incl_empty _ _)
  }.
Proof.
  intros [a b]; simpl.
  eapply empty_bottom; eauto.
Defined.

Instance
  : Terminating (withTop val) poLt.
Proof.
  hnf; intros.
  destruct x.
  - econstructor; intros. inv H. inv H0. inv H. exfalso; eauto.
  - econstructor; intros. inv H. inv H0.
    + eapply int_eq_eq in H3. subst.
      exfalso. eapply H1. eauto.
    + econstructor; intros.
      inv H2. inv H3. inv H2. exfalso; eauto.
Qed.

Definition constant_propagation_analysis :=
  makeForwardAnalysis DDom _ _ cp_trans_dep transf_mon_dep
                      (fun s => (@terminating_Dom var _ _ _ (occurVars s) _)).
