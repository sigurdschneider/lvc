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
  | x::A, y::B =>
    domupd (domupd_list m A B) x (join (find x m) y)
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

Lemma eqMap_op_eval e a b
  : eqMap a b
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

Lemma join_struct T `{JoinSemiLattice T} (a b a' b':T)
  : a ≣ a'
    -> b ≣ b'
    -> a ⊔ b ≣ (a' ⊔ b').
Proof.
  intros A B. rewrite A, B. reflexivity.
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

Lemma domupd_ne m x y a
  : x =/= y
    -> find x (domupd m y a) = find x m.
Proof.
  unfold domupd; cases; intros; mlud; eauto.
Qed.

Lemma domupd_list_ne m x Z Y
  : ~ InA eq x Z
    -> find x (domupd_list m Z Y) === find x m.
Proof.
  intros NI.
  general induction Z; destruct Y; simpl; eauto.
  rewrite domupd_ne; eauto.
  intro; eapply NI; econstructor. eapply H.
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


Definition constant_propagation_transform sT ZL st (ST:subTerm st sT)
           (a:Dom) (b:bool)
  : anni Dom st :=
  match st as st', a return anni Dom st'  with
  | stmtLet x (Operation e) s as st, d =>
    let d' := domupd d x (op_eval (domenv d) e) in
    d'
  | stmtLet x (Call f Y) s as st, d =>
    (* we assume renamed apart here, and dont zero x *)
    domupd d x (Some Top)
  | stmtIf e s t as st, d =>
    (if [op_eval (domenv d) e = None] then false
     else if [op_eval (domenv d) e = Some (wTA val_false)] then
            false else b,
     if [op_eval (domenv d) e = None] then false
     else if [op_eval (domenv d) e = Some (wTA val_true)] then
            false else b,
     d)
  | stmtApp f Y as st, d =>
    let Z := nth (counted f) ZL (nil:list var) in
    let Yc := List.map (op_eval (domenv d)) Y in
    (* we assume renamed apart here, so it's ok to leave definitions
       in d[X <-- Yc] that are /not/ defined at the point where f is defined *)
    if b then
      domupd_list d Z Yc
    else
      d
  | stmtReturn e as st, d =>
    d
  | stmtFun F t as st, d =>
    (* we assume renamed apart here, and dont zero Z *)
    d
  end.

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
      eapply (leMap_op_eval e); eauto.
    + hnf; intros. mlud; eauto.
  - exploit (leMap_op_eval e); eauto.
    repeat (cases; try split; eauto using @fstNoneOrR); simpl;
      try congruence;
    repeat (match goal with
           | [ H : _ = None |- _ ] => rewrite H in *
           | [ H : _ = Some _ |- _ ] => rewrite H in *
            end; clear_trivial_eqs; try inv H1; try congruence).
    + clear_trivial_eqs. rewrite <- H2 in *.
      exfalso; eapply NOTCOND0. reflexivity.
    + clear_trivial_eqs. rewrite <- H2 in *.
      exfalso. eapply NOTCOND1. reflexivity.
  - destruct (get_dec ZL l); dcr.
    + erewrite get_nth; eauto; simpl.
      repeat cases; isabsurd; eauto;
        try (eapply domupd_list_le; eauto).
      etransitivity; eauto.
      eapply domupd_list_exp.
    + rewrite not_get_nth_default; eauto.
      simpl; repeat cases; eauto.
Qed.


Definition DDom (sT:stmt) := { m : Map [var, withTop val] | domain m ⊆ occurVars sT}.

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


Definition anni_dom sT (a:anni Dom sT) : set var.
  destruct sT; simpl in *;
    try eapply (domain a).
  - eapply (domain (snd a)).
Defined.

Lemma cp_trans_domain  sT (ZL:list params) st (ST:subTerm st sT)
       (ZLIncl: list_union (of_list ⊝ ZL) ⊆ occurVars sT) (a:DDom sT) b
  : anni_dom _ (constant_propagation_transform ZL ST (proj1_sig a) b) ⊆ occurVars sT.
Proof.
  pose proof (subTerm_occurVars ST) as Incl. destruct a; simpl in *.
  destruct st; simpl in *; eauto.
  - destruct e; eauto.
    rewrite domain_domupd_incl. cset_tac.
    rewrite domain_add. cset_tac.
  - destruct (get_dec ZL l); dcr.
    + erewrite get_nth; eauto; cases; eauto.
      rewrite domain_domupd_list_incl.
      eapply union_incl_split; eauto.
      rewrite <- ZLIncl.
      eapply incl_list_union; eauto using map_get_1.
    + rewrite not_get_nth_default; eauto; simpl; cases; eauto.
Qed.


Definition cp_trans_dep sT (ZL:list params) st (ST:subTerm st sT)
           (ZLIncl: list_union (of_list ⊝ ZL) ⊆ occurVars sT) (a:DDom sT) (b:bool)
  : anni (DDom sT) st.
Proof.
  set (res:=(@constant_propagation_transform sT ZL st ST (proj1_sig a) b)).
  set (pf:=cp_trans_domain ZL ST ZLIncl a b).
  destruct st; try eapply (exist _ res pf).
  simpl.
  eapply (fst (fst res), snd (fst res), exist _ (snd res) pf).
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
      eapply eqMap_op_eval; eauto.
    + hnf; intros. mlud; eauto.
  - pose proof(eqMap_op_eval e H).  hnf in H1.
    cases; inv H1; simpl.
    repeat split; eauto.
    repeat cases; try congruence.
    exfalso; eauto.
    repeat cases; repeat split; eauto.
    exfalso; eauto.
  - repeat cases; eauto.
    destruct (get_dec ZL l); dcr.
    + erewrite get_nth; eauto.
      eapply domupd_list_eq; eauto.
    + rewrite not_get_nth_default; eauto; simpl; cases; eauto.
Qed.

Lemma domain_join_sig X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  (x y : {m : Map [X, Y] | domain m [<=] U})
  : domain (proj1_sig x ⊔ proj1_sig y) [<=] U.
Proof.
  destruct x,y; simpl.
  unfold joinMap. rewrite domain_join. cset_tac.
Qed.

Definition joinsig X `{OrderedType X} Y `{JoinSemiLattice Y}  U
           (x y : {m : Map [X, Y] | domain m ⊆ U}) :=
  exist (fun m => domain m ⊆ U) (join (proj1_sig x) (proj1_sig y)) (domain_join_sig x y).

Definition joinsig_idem X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  : forall a : {m : Map [X, Y] | domain m [<=] U}, joinsig a a ≣ a.
Proof.
  - hnf; intros [a ?]. simpl. eapply joinDom_idem.
Qed.

Definition joinsig_sym X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  : forall a b : {m : Map [X, Y] | domain m [<=] U}, joinsig a b ≣ joinsig b a.
Proof.
  - hnf; intros [a ?] [b ?]. eapply joinDom_sym.
Qed.

Definition joinsig_assoc X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  : forall a b c : {m : Map [X, Y] | domain m [<=] U}, joinsig (joinsig a b) c ≣ joinsig a (joinsig b c).
Proof.
  hnf; intros [a ?] [b ?] [c ?]. eapply joinDom_assoc.
Qed.

Definition joinsig_exp X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  : forall a b : {m : Map [X, Y] | domain m [<=] U}, a ⊑ joinsig a b.
Proof.
  hnf; intros [a ?] [b ?]; simpl. eapply joinDom_exp.
Qed.


Instance map_sig_semilattice_bound X `{OrderedType X} Y `{JoinSemiLattice Y}  U
  : JoinSemiLattice ({ m : Map [X, Y] | domain m ⊆ U}) := {
  join x y := joinsig x y
}.
Proof.
  - eapply joinsig_idem.
  - eapply joinsig_sym.
  - eapply joinsig_assoc.
  - eapply joinsig_exp.
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
