Require Import CSet Le CMap CMapDomain CMapPartialOrder CMapJoinSemiLattice CMapTerminating.

Require Import Plus Util AllInRel CSet OptionR.
Require Import Val Var Env IL Annotation Infra.Lattice DecSolve.
Require Import Analysis.Analysis AnalysisForwardSSA ValueOpts.ConstantPropagation.

Require Import CMap WithTop DomainSSA.

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
(*
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
  general induction Z; destruct Y; simpl domupd_list; eauto.
  simple eapply domupd_le.
  - hnf. eapply IHZ; eauto.
  - exploit (@join_struct (option (withTop val)) _).
    Focus 3. eapply H0.
    eauto.
    eapply (leMap_op_eval o); eauto.
Qed.

Lemma domupd_eq a b v v' x
  : eqMap a b
    -> poEq v v'
    -> eqMap (domupd a x v) (domupd b x v').
Proof.
  unfold eqMap, domupd; intros.
  inv H0.
  - repeat cases; clear_trivial_eqs; mlud; eauto.
  - mlud; eauto.
Qed.

Lemma domupd_list_eq a b Z Y
  : eqMap a b
    -> eqMap (domupd_list a Z (op_eval (domenv a) ⊝ Y))
            (domupd_list b Z (op_eval (domenv b) ⊝ Y)).
Proof.
  unfold eqMap, domupd; intros.
  general induction Z; destruct Y; simpl domupd_list; eauto.
  simple eapply domupd_eq.
  - hnf. eapply IHZ; eauto.
  - exploit (@join_struct (option (withTop val)) _).
    Focus 3. eapply H0.
    eauto.
    eapply (eqMap_op_eval o); eauto.
Qed.

Lemma domupd_list_exp m Z Y
  : leMap m (domupd_list m Z Y).
Proof.
  general induction Z; destruct Y; simpl domupd_list; eauto;
    try reflexivity.
  unfold ojoin; repeat cases; simpl domupd; eauto.
  - hnf; intros. mlud.
    + rewrite <- e, <- Heq.
      econstructor.
      unfold withTop_generic_join; repeat cases; try econstructor; eauto.
      reflexivity.
    + eapply IHZ.
  - hnf; intros; mlud.
    rewrite Heq, e; eauto.
    eapply IHZ.
  - hnf; intros; mlud.
    rewrite <- e, <- Heq; eauto.
    eapply IHZ.
  - hnf; intros; mlud.
    rewrite <- e, <- Heq; eauto.
    eapply IHZ.
Qed.

 *)

Lemma leMap_op_eval e a b
  : poLe a b
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

Hint Resolve leMap_op_eval.

Lemma eqMap_op_eval e a b
  : poEq a b
    -> poEq (op_eval (domenv a) e) (op_eval (domenv b) e).
Proof.
  general induction e; simpl; eauto using @fstNoneOrR, @withTop_eq, @option_R.
  - reflexivity.
  - unfold domenv.
    specialize (H n).
    destruct (find n a); eauto using fstNoneOrR.
  - specialize (IHe _ _ H); repeat cases; eauto using fstNoneOrR, @withTop_eq, @option_R.
    reflexivity.
  - specialize (IHe1 _ _ H).
    specialize (IHe2 _ _ H).
    inv IHe1; inv IHe2; repeat cases;
      simpl in *; clear_trivial_eqs;
        eauto using fstNoneOrR, withTop_eq, option_R.
    + econstructor; econstructor. congruence.
Qed.

Hint Resolve leMap_op_eval eqMap_op_eval.

Definition constant_propagation_transform sT ZL st (ST:subTerm st sT)
           (a:Dom) (b:bool)
  : Dom :=
  match st as st', a return Dom with
  | stmtLet x (Operation e) s as st, d =>
    let d' := domupd d x (op_eval (domenv d) e) in
    d'
  | stmtLet x (Call f Y) s as st, d =>
    (* we assume renamed apart here, and dont zero x *)
    domupd d x (Some Top)
  | stmtIf e s t as st, d => d
  | stmtApp f Y as st, d =>
    let Z := nth (counted f) ZL (nil:list var) in
    let Yc := List.map (op_eval (domenv d)) Y in
    (* we assume renamed apart here, so it's ok to leave definitions
       in d[X <-- Yc] that are /not/ defined at the point where f is defined *)
    if b then
      domjoin_list d Z Yc
    else
      d
  | stmtReturn e as st, d =>
    d
  | stmtFun F t as st, d =>
    (* we assume renamed apart here, and dont zero Z *)
    d
  end.

Arguments poLe : simpl never.
Arguments poEq : simpl never.

Lemma poLe_map D `{PartialOrder D} D' `{PartialOrder D'} (f g:D -> D') (L L':list D)
      (LEf:forall a b, poLe a b -> poLe (f a) (g b))
      (LE: poLe L L')
  : poLe (f ⊝ L) (g ⊝ L').
Proof.
  general induction LE; simpl; eauto.
Qed.

Lemma poLe_map_nd D D' `{PartialOrder D'} (f g:D -> D') (L L':list D)
      (LEf:forall a, poLe (f a) (g a))
  : poLe (f ⊝ L) (g ⊝ L).
Proof.
  general induction L; simpl; eauto.
Qed.

Lemma poEq_map D `{PartialOrder D} D' `{PartialOrder D'} (f g:D -> D') (L L':list D)
      (LEf:forall a b, poEq a b -> poEq (f a) (g b))
      (LE: poEq L L')
  : poLe (f ⊝ L) (g ⊝ L').
Proof.
  general induction LE; simpl; eauto.
Qed.

Lemma poEq_map_nd D D' `{PartialOrder D'} (f g:D -> D') (L L':list D)
      (LEf:forall a, poEq (f a) (g a))
  : poEq (f ⊝ L) (g ⊝ L).
Proof.
  general induction L; simpl; eauto.
Qed.

Lemma transf_mon
  : (forall (sT s : stmt) (ST : subTerm s sT) (ZL : 〔params〕) (a b : Dom),
        a ⊑ b -> forall (c d:bool), c ⊑ d ->
        constant_propagation_transform ZL ST a c
                                       ⊑ constant_propagation_transform ZL ST b d).
Proof.
  intros.
  general induction s; simpl in *; eauto.
  - destruct e; eauto.
    + eapply domupd_le; eauto.
    + hnf; intros. mlud; eauto.
  - destruct (get_dec ZL l); dcr.
    + erewrite get_nth; eauto; simpl.
      repeat cases; isabsurd; eauto;
        try (eapply domjoin_list_le; eauto).
      * eapply poLe_map_nd; eauto.
      * rewrite H. eapply domjoin_list_exp.
    + rewrite not_get_nth_default; eauto.
      simpl; repeat cases; eauto.
Qed.


Definition DDom (sT:stmt) := { m : Map [var, withTop val] | domain m ⊆ occurVars sT}.

Lemma cp_trans_domain  sT (ZL:list params) st (ST:subTerm st sT)
       (ZLIncl: list_union (of_list ⊝ ZL) ⊆ occurVars sT) (a:DDom sT) b
  : domain (constant_propagation_transform ZL ST (proj1_sig a) b) ⊆ occurVars sT.
Proof.
  pose proof (subTerm_occurVars ST) as Incl. destruct a; simpl in *.
  destruct st; simpl in *; eauto.
  - destruct e; eauto.
    rewrite domain_domupd_incl. cset_tac.
    rewrite domain_add. cset_tac.
  - destruct (get_dec ZL l); dcr.
    + erewrite get_nth; eauto; cases; eauto.
      rewrite domain_domjoin_list_incl.
      eapply union_incl_split; eauto.
      rewrite <- ZLIncl.
      eapply incl_list_union; eauto using map_get_1.
    + rewrite not_get_nth_default; eauto; simpl; cases; eauto.
Qed.


Definition cp_trans_dep sT (ZL:list params) st (ST:subTerm st sT)
           (ZLIncl: list_union (of_list ⊝ ZL) ⊆ occurVars sT) (a:DDom sT) (b:bool)
  : DDom sT.
Proof.
  set (res:=(@constant_propagation_transform sT ZL st ST (proj1_sig a) b)).
  set (pf:=cp_trans_domain ZL ST ZLIncl a b).
  destruct st; try eapply (exist _ res pf).
Defined.


Lemma transf_mon_dep
  : (forall (sT s : stmt) (ST : subTerm s sT) (ZL : 〔params〕)
       (ZLIncl : list_union (of_list ⊝ ZL) ⊆ occurVars sT) (a b : DDom sT),
        a ⊑ b -> forall (c d:bool), c ⊑ d ->
        cp_trans_dep ZL ST ZLIncl a c ⊑ cp_trans_dep ZL ST ZLIncl b d).
Proof.
  intros. destruct a as [a aBound], b as [b bBound]; simpl in H.
  pose proof (@transf_mon sT s ST ZL a b H) as LE.
  destruct s; clear_trivial_eqs; simpl in *; eauto.
  eapply LE; eauto.
Qed.


Lemma transf_ext sT (s : stmt) (ST : subTerm s sT) (ZL : 〔params〕)
    (ZLIncl : list_union (of_list ⊝ ZL) [<=] occurVars sT)
  : forall (a0 a' : DDom sT),
    a0 ≣ a' ->
    forall b b' : bool, b ≣ b' -> cp_trans_dep ZL ST ZLIncl a0 b ≣ cp_trans_dep ZL ST ZLIncl a' b'.
Proof.
  intros. unfold cp_trans_dep; cases; simpl; eauto.
  - cases; eauto.
    + eapply domupd_eq; eauto.
    + hnf; intros. simpl. mlud; eauto.
  - repeat cases; eauto.
    eapply poEq_vdom_struct.
    destruct (get_dec ZL l); dcr.
    + erewrite get_nth; eauto.
      eapply domjoin_list_eq; eauto.
      eapply poEq_map_nd; eauto.
    + rewrite not_get_nth_default; eauto; simpl; cases; eauto.
Qed.

Definition cp_trans_reach (sT : stmt) (e : op)
           (Incl:Op.freeVars e [<=] occurVars sT) (d:DDom sT) (b:bool) : bool * bool :=
  (if [op_eval (domenv (proj1_sig d)) e = None] then false
     else if [op_eval (domenv (proj1_sig d)) e = Some (wTA val_false)] then
            false else b,
     if [op_eval (domenv (proj1_sig d)) e = None] then false
     else if [op_eval (domenv (proj1_sig d)) e = Some (wTA val_true)] then
            false else b).

Smpl Add match goal with
         | [ H : poLe _ None |- _ ] => invc H
         | [ H : ⎣ ?x ⎦ <> ⎣ ?x ⎦ |- _ ] => exfalso; apply H; reflexivity
         end : inv_trivial.

Lemma cp_trans_reach_mon
  : forall (sT : stmt) (e : op) (s : stmt),
    subTerm s sT ->
    forall (FVIncl : Op.freeVars e [<=] occurVars sT) (a a' : DDom sT),
      a ⊑ a' ->
      forall b b' : bool,
        b ⊑ b' -> cp_trans_reach e FVIncl a b ⊑ cp_trans_reach e FVIncl a' b'.
Proof.
  intros. pose proof (leMap_op_eval e H0); eauto.
  unfold cp_trans_reach.
  set (X:=op_eval (domenv (proj1_sig a)) e) in *.
  set (Y:=op_eval (domenv (proj1_sig a')) e) in *. clearbody X Y.
  unfold val in *.
  repeat cases; split; simpl fst; simpl snd; eauto; clear_trivial_eqs.
  inv H2; clear_trivial_eqs.
  inv H2; clear_trivial_eqs.
Qed.

Lemma cp_trans_reach_ext
  : forall sT (e : op) (s : stmt),
    subTerm s sT ->
    forall (FVIncl : Op.freeVars e [<=] occurVars sT) (a0 a' : DDom sT),
      a0 ≣ a' ->
      forall b b' : bool,
        b ≣ b' -> cp_trans_reach e FVIncl a0 b ≣ cp_trans_reach e FVIncl a' b'.
Proof.
  intros. exploit (eqMap_op_eval e); eauto. eapply H0.
  unfold cp_trans_reach.
  set (X:=op_eval (domenv (proj1_sig a0)) e) in *.
  set (Y:=op_eval (domenv (proj1_sig a')) e) in *. clearbody X Y.
  repeat cases; split; simpl fst; simpl snd; eauto; clear_trivial_eqs;
  inv H2; clear_trivial_eqs; exfalso; eauto.
Qed.


Definition cp_reach (U : ⦃nat⦄) (b:bool) (d: VDom U (withTop val)) (e:op) : bool * bool :=
  (true, true).

Lemma cp_reach_mon (U : ⦃nat⦄) (e : op) (a a' : VDom U (withTop val))
  : a ⊑ a' -> forall b b' : bool, b ⊑ b' -> cp_reach b a e ⊑ cp_reach b' a' e.
Proof.
  intros. reflexivity.
Qed.

Definition cp_trans (U : ⦃nat⦄) (b:bool) (d: VDom U (withTop val)) (e:exp) : ؟ (withTop val) :=
  match e with
  | Operation e => op_eval (domenv (proj1_sig d)) e
  | _ => Some Top
  end.

Lemma cp_trans_mon (U : ⦃nat⦄) (e : exp) (a a' : VDom U (withTop val))
  : a ⊑ a' -> forall b b' : bool, b ⊑ b' -> @cp_trans U b a e ⊑ @cp_trans U b' a' e.
Proof.
  intros. destruct e; simpl; eauto.
Qed.

Definition constant_propagation_analysis :=
  makeForwardAnalysis _ _ _ cp_trans cp_reach cp_trans_mon cp_reach_mon.
