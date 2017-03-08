Require Import CSet Le.

Require Import Plus Util AllInRel CSet OptionR.
Require Import Val Var Env IL Annotation Infra.Lattice DecSolve.
Require Import Analysis.Analysis AnalysisForwardSSA ValueOpts.ConstantPropagation.

Require Import CMap WithTop.

Set Implicit Arguments.

Open Scope map_scope.


Definition Dom := Map [var, withTop val].

(*
Definition join (v v' : aval) : aval :=
  match v with
  | Top => Top
  | wTA (Known v0) =>
    match v' with
    | Top => Top
    | wTA (Known v'0) => if [v0 = v'0] then wTA (Known v0) else Top
    | wTA Unknown => v
    end
  | wTA Unknown => v'
  end.
*)
Definition join' (a b : option aval) :=
  match a, b with
  | None, None => None
  | Some a, None => Some a
  | None, Some b => Some b
  | Some a, Some b => Some (join a b)
  end.


Definition joinMap X `{OrderedType X} Y `{JoinSemiLattice Y}
           (d d':Map [X, Y]) := @map2 _ H _ Y Y Y join d d'.

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

(*
Lemma domain_join (d d':Dom)
: domain (map2 join' d d') [=] domain d ∪ domain d'.
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
 *)

(*
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
 *)

Definition leMap X `{OrderedType X} Y `{PartialOrder Y} (d d': Map [X, Y]) : Prop :=
 (forall x, poLe (find x d) (find x d')).

Lemma leMap_irreflexive X `{OrderedType X} Y `{PartialOrder Y} (x y:Map [X,Y])
: ~leMap x y -> ~Equal x y.
Proof.
  intros. intro. eapply H1.
  hnf; intros. rewrite H2.
  reflexivity.
Qed.

Instance leMap_ref X `{OrderedType X} Y `{PartialOrder Y} : Reflexive (@leMap X _ Y _).
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

Lemma not_find_domain (X : Type) (H : OrderedType X) (Y : Type) (d : Map [X, Y]) (x : X)
  : find x d = None -> x ∉ domain d.
Proof.
  intros.
  decide (x ∈ domain d); eauto.
  exfalso. eapply domain_find in i. dcr; congruence.
Qed.

Lemma find_domain' (X : Type) (H : OrderedType X) (Y : Type) (d : Map [X, Y]) x v
  : find x d = Some v -> x \In domain d.
Proof.
  intros.
  decide (x ∈ domain d); eauto.
  exfalso. eapply not_domain_find in n. congruence.
Qed.


Lemma le_domain_find X `{OrderedType X} Y `{PartialOrder Y} x (d d':Map [X, Y])
  : (forall x, x \In domain d ∪ domain d' ->
              poLe ((find x d)) ((find x d')))
    -> poLe (find x d) (find x d').
Proof.
  intros DEQ. specialize (DEQ x). revert DEQ.
  case_eq (find x d'); intros; eauto.
  - eapply find_domain' in H1; eauto.
    eapply DEQ. cset_tac.
  - simpl. case_eq (find x d); intros; eauto; simpl.
    + pose proof H2. eapply find_domain' in H2.
    exploit DEQ; eauto. cset_tac. simpl in *.
    rewrite H3 in H4. eauto.
    + econstructor.
Qed.

Instance leMap_proper X `{OrderedType X} Y `{PartialOrder Y} (d d':Map [X, Y])
  : Proper (_eq ==> iff) (fun x => find x d ⊑ find x d').
Proof.
  unfold Proper, respectful; intros.
  split; intros.
  - rewrite <- H1; eauto.
  - rewrite H1; eauto.
Qed.

Instance leMap_dec X `{OrderedType X} Y `{PartialOrder Y}
  :  forall d d' : Map [X, Y], Computable (leMap d d').
Proof.
  intros; hnf; intros.
  edestruct (@set_quant_computable _ _ (domain d ∪ domain d')
                                   (fun x => poLe ((find x d))
                                               (find x d'))).
  - eapply leMap_proper.
  - hnf; intros.
    eauto with typeclass_instances.
  - left; eauto.
    hnf; intros.
    eapply le_domain_find; eauto.
  - right; eauto.
Defined.


(*
Instance Equal_computable X `{OrderedType X} Y `{OrderedType Y}
         (s t:Map [X, Y])
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
 *)


Lemma wua_poLe_inv (x y : withUnknown val)
  : poLe x y -> x = y.
Proof.
  intros A; inv A.
  - f_equal. eauto.
  - eauto.
Qed.

Lemma withTop_poLe_inv A R `{EqDec A R} (a b:A)
  : poLe (wTA a) (wTA b)
    -> a === b.
Proof.
  intros. inv H0. eapply H3.
Qed.

Ltac inv_if_ctor H A B :=
  let A' := eval hnf in A in
      let B' := eval hnf in B in
          is_constructor_app A'; is_constructor_app B'; inv H.



(*
Lemma lt_join (x y x' y':aval)
: poLe y x
  -> poLe y' x'
  -> poLe (join y y') (join x x').
Proof.
  intros.
  inv H; inv H0; simpl; repeat cases; eauto using withTop_le;
    clear_trivial_eqs; eauto using withTop_le.
  reflexivity.
Qed.


Lemma join_bot_right (y:Dom) x0
  : join' (find x0 y) ⎣⎦ = find x0 y.
Proof.
  destruct (find x0 y); simpl; eauto.
  destruct a; eauto. destruct a; reflexivity.
  reflexivity.
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
 *)


Smpl Add 100 match goal with
             | [ H : @poLe (withUnknown val) _ ?x ?y  |- _ ] =>
               eapply wua_poLe_inv in H; subst
             | [ H : ?a <> ?a |- _ ] => exfalso; eapply H; reflexivity
             | [ H : ~ ?a === ?a |- _ ] => exfalso; eapply H; reflexivity
             | [ H : @poLe (withTop _) _ (wTA _) (wTA _) |- _ ] =>
               eapply withTop_poLe_inv in H
             | [ H : @poLe _ _ (wTA _) (wTA _) |- _ ] => invc H
             | [ H : Known _ === Known _ |- _ ] => invc H
             | [ H : withUnknown_eq _ _ |- _ ] =>
               invc H
             | [ H : fstNoneOrR _ ?A ?B |- _ ] =>
               inv_if_ctor H A B; clear H
             | [ H : fstNoneOrR _ ?A ?B |- _ ] =>
               inv_if_ctor H A B; clear H
             | [ H : withTop_le _ _ |- _ ] => invc H
             | [ H : int_eq _ _ |- _ ] => eapply int_eq_eq in H
             | [ H : ?A === ?B |- _ ] => inv_if_ctor H A B
             | [ H : poEq ?A ?B |- _ ] => inv_if_ctor H A B
             end : inv_trivial.

Lemma leMap_join X `{OrderedType X} Y `{JoinSemiLattice Y} (x y x' y':Map[X, Y])
  : leMap y x
    -> leMap y' x'
    -> leMap (joinMap y y') (joinMap x x').
Proof.
  unfold leMap, joinMap.
  intros LE1 LE2 z.
  repeat rewrite MapFacts.map2_1bis; eauto.
  specialize (LE1 z). specialize (LE2 z).
  revert LE1 LE2.
  case_eq (find z y); case_eq (find z x);
    case_eq (find z y'); case_eq (find z x'); intros; simpl in *;
      clear_trivial_eqs; simpl; repeat cases; try reflexivity;
        eauto using fstNoneOrR, join_struct, join_poLe.
  - econstructor. rewrite H8. eapply join_poLe.
  - econstructor. rewrite H8. rewrite join_commutative. eapply join_poLe.
Qed.

Instance leMap_tran X `{OrderedType X} Y `{PartialOrder Y}
  : Transitive (@leMap X _ Y _).
Proof.
  hnf. unfold leMap; intros.
  etransitivity; eauto.
Qed.

Definition eqMap X `{OrderedType X} Y `{PartialOrder Y}
           (d d' : Map [X, Y]) : Prop :=
 (forall x, poEq (find x d) (find x d')).

Instance eqMap_Equiv  X `{OrderedType X} Y `{PartialOrder Y}
  : Equivalence (@eqMap X _ Y _).
Proof.
  constructor; unfold eqMap; hnf; intros.
  - reflexivity.
  - symmetry; eauto.
  - etransitivity; eauto.
Qed.


Lemma eq_domain_find X `{OrderedType X} Y `{PartialOrder Y} x (d d':Map [X, Y])
  : (forall x, x \In domain d ∪ domain d' -> poEq (find x d)
                                               (find x d'))
    -> poEq (find x d) (find x d').
Proof.
  intros DEQ. specialize (DEQ x). revert DEQ.
  case_eq (find x d'); intros; eauto.
  - eapply find_domain' in H1; eauto.
    eapply DEQ. cset_tac.
  - simpl. case_eq (find x d); intros; eauto; simpl.
    + pose proof H2. eapply find_domain' in H2.
    exploit DEQ; eauto. cset_tac. simpl in *.
    rewrite H3 in H4. eauto.
    + econstructor.
Qed.

Instance eqDom_dec X `{OrderedType X} Y `{PartialOrder Y}
  :  forall d d' : Map [X, Y], Computable (eqMap d d').
Proof.
  intros; hnf; intros.
  edestruct (@set_quant_computable _ _ (domain d ∪ domain d')
                                   (fun x => poEq ((find x d))
                                               ((find x d')))).
  - unfold Proper, respectful; intros.
    split; intros.
    rewrite <- H1; eauto.
    rewrite H1; eauto.
  - hnf; intros.
    eauto with typeclass_instances.
  - left; eauto.
    hnf; intros. eapply eq_domain_find; eauto.
  - right; eauto.
Defined.

Instance leMap_anti X `{OrderedType X} Y `{PartialOrder Y}
  : Antisymmetric (Map [X, Y]) (@eqMap X _ Y _) (@leMap X _ Y _).
Proof.
  hnf. unfold leMap, Equal.
  intros. hnf; intros.
  eapply poLe_antisymmetric in H1; eauto.
Qed.

Set Implicit Arguments.

Instance find_eqMap_proper  X `{OrderedType X} Y `{PartialOrder Y}
  : Proper (_eq ==> @eqMap X _ Y _  ==> poEq) find.
Proof.
  unfold Proper, respectful, eqMap.
  intros. rewrite H2, H1. reflexivity.
Qed.

Instance Dom_semilattice_ltDom  X `{OrderedType X} Y `{PartialOrder Y}
  : PartialOrder (Map [X, Y]) := {
  poLe := @leMap X _ Y _;
  poLe_dec := (@leMap_dec X _ Y _);
  poEq := @eqMap X _ Y _;
  poEq_dec := _
}.
Proof.
  intros. hnf; intros.
  rewrite H1. reflexivity.
Defined.


Lemma empty_bottom X `{OrderedType X} Y `{JoinSemiLattice Y}
  :  forall a : Map [X, Y], @empty _ _ _ _ ⊑ a.
Proof.
  intros. econstructor.
Qed.

Lemma joinDom_idem X `{OrderedType X} Y `{JoinSemiLattice Y}
  : forall a : Map [X, Y], joinMap a a ≣ a.
Proof.
  unfold joinMap. intros.
  hnf; intros.
  rewrite MapFacts.map2_1bis; eauto.
  rewrite join_idempotent; eauto.
Qed.

Lemma joinDom_sym X `{OrderedType X} Y `{JoinSemiLattice Y}
  : forall a b : Map [X, Y], joinMap a b ≣ joinMap b a.
Proof.
  unfold joinMap; intros. hnf; intros.
  rewrite !MapFacts.map2_1bis; eauto.
  rewrite join_commutative. reflexivity.
Qed.

Lemma joinDom_assoc X `{OrderedType X} Y `{JoinSemiLattice Y}
  : forall a b c : Map [X, Y], joinMap (joinMap a b) c ≣ joinMap a (joinMap b c).
Proof.
  unfold joinMap; intros. hnf; intros.
  rewrite !MapFacts.map2_1bis; eauto.
  rewrite join_associative. reflexivity.
Qed.

Hint Resolve withTop_le_refl WithTopLe_refl.

Lemma joinDom_exp X `{OrderedType X} Y `{JoinSemiLattice Y}
  : forall a b : Map [X, Y], a ⊑ joinMap a b.
Proof.
  intros. unfold joinMap. hnf; intros.
  rewrite !MapFacts.map2_1bis; eauto.
  eapply join_poLe.
Qed.

Instance joinDom_eq X `{OrderedType X} Y `{JoinSemiLattice Y}
  : Proper (poEq ==> poEq ==> poEq) (@joinMap X _ Y _ _).
Proof.
  unfold Proper, respectful; intros.
  hnf in H, H0.
  unfold joinMap.
  hnf; intros.
  rewrite !MapFacts.map2_1bis; eauto.
  rewrite H2, H3. reflexivity.
Qed.

Instance joinDom_poLe X `{OrderedType X} Y `{JoinSemiLattice Y}
  : Proper (poLe ==> poLe ==> poLe) (@joinMap X _ Y _ _).
Proof.
  unfold Proper, respectful; intros.
  eapply leMap_join; eauto.
Qed.

Instance map_semilattice X `{OrderedType X} Y `{JoinSemiLattice Y}
  : JoinSemiLattice (Map [X, Y]) := {
  join := @joinMap X _ Y _ _
                                                    }.

- eapply joinDom_idem.
- eapply joinDom_sym.
- eapply joinDom_assoc.
- eapply joinDom_exp.
Defined.


Instance map_lower_bounded X `{OrderedType X} Y `{JoinSemiLattice Y}
  : LowerBounded (Map [X, Y]) :=
  {
    bottom := (@empty X _ _ Y)
  }.
Proof.
  - eapply empty_bottom; eauto.
Qed.


Import Terminating.

(*
Lemma Terminating_subtype_incl X `{OrderedType X} Y `{PartialOrder Y} U U' x p p'
      (T:terminates (@poLt {x : Map [X, Y] | domain x ⊆ U} _) (exist _ x p))
      (Incl: domain x [<=] U)
  : terminates (@poLt {x : Map [X, Y] | domain x ⊆ U' } _) (exist _ x p').
Proof.
  general induction T.
  econstructor; intros [] LE.
  eapply H2;[|reflexivity]. eauto.
  Unshelve.
Qed.


Lemma Terminating_subtype_incl X `{OrderedType X} Y `{PartialOrder Y} U U'
      (T:Terminating ({ x : Map [X, Y] | domain x ⊆ U }) poLt)
 : Terminating ({ x  : Map [X, Y] | domain x ⊆ U' }) poLt.
Proof.
  hnf; intros. destruct x.
  specialize (T (exist _ x (INCL x p))).
  general induction T.
  econstructor; intros.
  destruct y. eapply H1;[|reflexivity].
  instantiate (1:=INCL).
  destruct H2.
  econstructor; eauto.
Qed.
*)

Lemma leMap_domain X `{OrderedType X} Y `{PartialOrder Y} x y
  : leMap x y -> domain x ⊆ domain y.
Proof.
  unfold leMap. intros.
  hnf; intros.
  specialize (H1 a).
  eapply domain_find in H2. dcr.
  rewrite H3 in H1. inv H1.
  eapply find_domain. congruence.
Qed.

Instance poLt_poLe_impl Dom `{PartialOrder Dom}
  : Proper (poEq ==> poEq ==> iff) poLt.
Proof.
  unfold Proper, respectful, flip, impl; intros.
  unfold poLt. rewrite H0, H1. reflexivity.
Qed.

Instance ltMap_proper X `{OrderedType X} Y `{PartialOrder Y} (d d':Map [X, Y])
  : Proper (_eq ==> iff) (fun x => find x d ⊏ find x d').
Proof.
  unfold Proper, respectful; intros.
  split; intros.
  - rewrite <- H1; eauto.
  - rewrite H1; eauto.
Qed.



Tactic Notation "decide_goal" :=
  match goal with
    [ |- ?s ] => decide s
  end.

Lemma not_poLt_poLe_poEq X `{PartialOrder X} x y
  : ~ x ⊏ y -> poLe x y -> x === y.
Proof.
  intros.
  eapply poLe_antisymmetric; eauto.
  decide_goal; eauto.
  exfalso. eapply H0. split; eauto.
  intro. eapply n. rewrite H2. eauto.
Qed.

Lemma leMap_remove X `{OrderedType X} Y `{PartialOrder Y} (m m':Map [X, Y]) x
  : leMap m m'
    -> leMap (remove x m) (remove x m').
Proof.
  unfold leMap; intros LE y.
  specialize (LE y).
  decide (x === y).
  - rewrite !MapFacts.remove_eq_o; eauto.
  - rewrite !MapFacts.remove_neq_o; eauto.
Qed.

Lemma domain_remove X `{OrderedType X} Y `{PartialOrder Y} (m:Map [X,Y]) x
  : domain (remove x m) [=] domain m \ singleton x.
Proof.
  eapply incl_eq.
  - hnf; intros.
    cset_tac'.
    eapply find_domain.
    rewrite !MapFacts.remove_neq_o; eauto.
    eapply domain_find in H2; dcr; congruence.
  - hnf; intros.
    eapply domain_find in H1; dcr.
    decide (x === a).
    + rewrite !MapFacts.remove_eq_o in H2; eauto. congruence.
    + rewrite !MapFacts.remove_neq_o in H2; eauto.
      eapply find_domain' in H2. cset_tac.
Qed.

Lemma terminating_Dom_eq_add_some X `{OrderedType X} Y `{PartialOrder Y} U x (NIN:x ∉ U)
      (TRM:Terminating Y poLt)
      (T:Terminating ({ X : Map [X, Y] | domain X ⊆ U }) poLt)
  : forall (y : Y) m p,
    find x m === ⎣ y ⎦ ->
    terminates poLt (exist (fun X0 : Map [X, Y] => domain X0 [<=] {x; U}) m p).
Proof.
  intros y m pr FEQ.
  pose proof (TRM y).
  revert dependent m.
  induction H1; intros.

  assert (RD:domain (remove x m) ⊆ U). {
    rewrite domain_remove; eauto. cset_tac.
  }
  specialize (T (exist _ (remove x m) RD)).
  remember_arguments T. revert dependent m.
  induction T; intros; clear_trivial_eqs.

  econstructor; intros [m' d'] [LE1 LE2]. simpl in *.

  decide (poLt (find x m) (find x m')).
  - rewrite FEQ in p. destruct p as [p1 p2]. inv p1.
    eapply H2; eauto.
    split; eauto. rewrite <- H6 in *. clear_trivial_eqs.
    intro; eapply p2; eauto. econstructor; eauto.
    rewrite H6; eauto.
  - assert (RD':domain (remove x m') ⊆ U). {
      rewrite domain_remove; eauto. cset_tac.
    }
    eapply H4; try reflexivity. instantiate (1:=RD').
    split; simpl.
    + eapply leMap_remove; eauto.
    + intro.
      specialize (LE1 x).
      eapply not_poLt_poLe_poEq in n; eauto.
      eapply LE2.
      hnf; intros.
      decide (x1 === x). rewrite e. eauto.
      specialize (H5 x1). lud.
      rewrite !MapFacts.remove_neq_o in H5; eauto.
    + specialize (LE1 x).
      rewrite FEQ in *.
      inv LE1.  econstructor.
      eapply poLe_antisymmetric; eauto.
      decide (y ⊑ x0); eauto.
      exfalso. eapply n.
      rewrite <- H6. split; try econstructor. eauto.
      intro. eapply n0. inv H5. rewrite H10. eauto.
Qed.

Lemma terminating_Dom_eq_add_none X `{OrderedType X} Y `{PartialOrder Y} U x (NIN:x ∉ U)
      (TRM:Terminating Y poLt)
      (TA:Terminating ({ X : Map [X, Y] | domain X ⊆ U }) poLt)
  : forall m p,
    find x m = None ->
    terminates poLt (exist (fun X0 : Map [X, Y] => domain X0 [<=] {x; U}) m p).
Proof.
  intros m pr FEQ.
  assert (RD:domain m ⊆ U). {
    eapply not_find_domain in FEQ. cset_tac.
  }
  pose proof (TA (exist _ m RD)) as T.
  remember_arguments T. revert dependent m.
  induction T; intros; clear_trivial_eqs.

  econstructor; intros [m' d'] [LE1 LE2]. simpl in *.

  decide (poLt (find x m) (find x m')).
  - rewrite FEQ in p. destruct p as [p1 p2].
    case_eq (find x m').
    + intros.
      eapply terminating_Dom_eq_add_some; eauto.
      rewrite H3; eauto.
    + intros.
      assert (RD':domain m' ⊆ U). {
        eapply not_find_domain in H3. cset_tac.
      }
      eapply H2; eauto. instantiate (1:=RD').
      split; eauto.
  - pose proof (LE1 x) as LE1x.
    eapply not_poLt_poLe_poEq in n; eauto.
    rewrite FEQ in n. inv n.
    symmetry in H3.
    assert (RD':domain m' ⊆ U). {
      eapply not_find_domain in H3. cset_tac.
    }
    eapply H2; eauto.
    + instantiate (1:=RD'). split; simpl; eauto.
Qed.

Lemma terminating_Dom_eq_add X `{OrderedType X} Y `{PartialOrder Y} U x (NIN:x ∉ U)
      (TRM:Terminating Y poLt)
      (T:Terminating ({ X : Map [X, Y] | domain X ⊆ U }) poLt)
  : Terminating ({ X : Map [X, Y] | domain X ⊆ {x; U} }) poLt.
Proof.
  hnf; intros [m d].
  case_eq (find x m).
  - intros.
    eapply terminating_Dom_eq_add_some; eauto.
    rewrite H1; eauto.
  - intros.
    eapply terminating_Dom_eq_add_none; eauto.
Qed.

Lemma terminates_bound_inv X `{OrderedType X} Y `{PartialOrder Y} (P P':Map [X, Y] -> Prop)
      (IMPL: forall x, P' x -> P x )
      (x: Map [X, Y]) (px:P x) (py:P' x)
  : terminates (@poLt { x : Map [X, Y] | P x } _ ) (exist _ x px)
    -> terminates (@poLt { x : Map [X, Y] | P' x } _ ) (exist _ x py).
Proof.
  intros T.
  general induction T.
  econstructor; intros [] [LE1 LE2]; simpl in *.
  eapply H2; eauto. instantiate (1:=IMPL x p).
  split; eauto.
Qed.

Lemma terminating_bound_inv X `{OrderedType X} Y `{PartialOrder Y} (P P':Map [X, Y] -> Prop)
      (IMPL: forall x, P' x -> P x )
  : Terminating ({ x : Map [X, Y] | P x }) poLt
    -> Terminating ({ x : Map [X, Y] | P' x }) poLt.
Proof.
  intros T. hnf; intros [x p].
  eapply terminates_bound_inv; eauto.
  Unshelve. eauto.
Qed.


Lemma terminating_Dom X `{OrderedType X} Y `{PartialOrder Y} U
      (TRM:Terminating Y poLt)
  : Terminating ({ X : Map [X, Y] | domain X ⊆ U }) poLt.
Proof.
  pattern U.
  eapply set_induction; intros.
  - eapply empty_is_empty_1 in H1.
    hnf; intros [m d].
    econstructor; intros [m' d'] [LE1 LE2].
    simpl in *.
    exfalso. eapply LE2. hnf; intros.
    eapply eq_domain_find; intros.
    cset_tac.
  - eapply terminating_bound_inv.
    instantiate (1:=fun x0 => domain x0 ⊆ {x; s}); simpl.
    cset_tac.
    eapply terminating_Dom_eq_add; eauto.
Qed.

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
  : leDom a b
    -> poLe v v'
    -> leDom (domupd a x v) (domupd b x v').
Proof.
  unfold leDom, domupd; intros.
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
  : leDom a b
    -> leDom (domupd_list a Z (op_eval (domenv a) ⊝ Y))
            (domupd_list b Z (op_eval (domenv b) ⊝ Y)).
Proof.
  unfold leDom, domupd; intros.
  general induction Z; destruct Y; simpl; eauto.
  eapply H. eapply H. eapply H.
  eapply domupd_le; eauto.
  hnf. eapply IHZ; eauto.
  eapply (leDom_op_eval o); eauto.
Qed.

Lemma int_eq_true_false_absurd
  : int_eq val_true val_false -> False.
Proof.
  intros. eapply int_eq_eq in H. inv H.
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
      eapply (leDom_op_eval e); eauto.
    + hnf; intros. lud; eauto.
  - exploit (leDom_op_eval e); eauto.
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
