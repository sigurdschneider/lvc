Require Export Setoid Coq.Classes.Morphisms.  
Require Import EqDec DecidableTactics Util AutoIndTac.
Require Export CSet Containers.SetDecide.
Require Export MapBasics MapLookup MapUpdate MapUpdateList.

Set Implicit Arguments.

Section InjectiveMapping.

  Inductive inj_mapping {X} `{OrderedType X} {Y} `{OrderedType Y} (LV:set Y) : list X -> list Y -> Prop :=
  | im_nil : inj_mapping LV nil nil
  | im_cons x y XL YL : inj_mapping LV XL YL 
    -> fresh x XL -> fresh y YL -> (~ y ∈ LV) 
    -> inj_mapping LV (x::XL) (y::YL).

  Lemma inj_mapping_length W `{OrderedType W} X `{OrderedType X} (LV:set X) Y Z
    : @inj_mapping W _ X _ LV Y Z -> length Y = length Z.
  Proof.
    intros. general induction H1; simpl; eauto. 
  Qed.

  Lemma inj_mapping_incl W `{OrderedType W} X `{OrderedType X} (L L':set X) Y Z
    : L' ⊆ L -> @inj_mapping W _ X _ L Y Z -> inj_mapping L' Y Z.
  Proof.
    intros. general induction H2; constructor; eauto.  
  Qed.

  Lemma ra_insert_allocs_correct' X `{OrderedType X} Y `{OrderedType Y}
    (m:X -> Y) 
    (lv:set X) XL YL x
    : InA _eq x XL
    -> inj_mapping (lookup_set m lv) XL YL
    -> InA _eq ((update_with_list XL YL m) x) YL.
  Proof.
    intros.
    general induction H1; simpl in *; intros; eauto. inv H2.
    lud. econstructor; eauto. exfalso. eapply H4. eauto.
    inv H2. lud. constructor; eauto.
    right. eapply IHInA; eauto. 
  Qed.

  Lemma ra_insert_allocs_no_param X `{OrderedType X} Y `{OrderedType Y}
    XL YL (m:X -> Y) x
    : ~x ∈ of_list XL
    -> (update_with_list XL YL m) x = m x.
  Proof.
    general induction XL; simpl; intros; eauto.
    destruct YL; eauto.
    assert (x=/=a). intro; subst; cset_tac. eapply H1. simpl. 
    eapply add_1; eauto.
    lud. eapply IHXL; cset_tac; eauto. simpl in H1; cset_tac. intro.
    eapply H1; eauto.
  Qed.

(*
  Lemma ra_insert_allocs_cases W `{OrderedType W} X `{OrderedType X} `{Defaulted X} XL YL 
    (m:Map[W, X]) bv y 
    : inj_mapping (lookup_set m bv) XL YL
    -> y ∈ lookup_set (update_with_list XL YL m) ((fromList XL ∪ bv))
    -> y ∈ lookup_set m bv \/ y ∈ fromList YL.
  Proof.
    intros.
    eapply lookup_set_spec in H2; eauto.
    destruct H2 as [x [A B]].
    destruct_prop (x ∈ fromList XL).
    right. eapply in_fromList. rewrite <- B. eapply ra_insert_allocs_correct'; eauto.
    eapply in_fromList. assumption. 
    left. rewrite <- B. rewrite ra_insert_allocs_no_param; eauto. 
    eapply lookup_set_spec; eauto.
    destruct (union_cases _ _ _ _ A); firstorder.
  Qed.


  Lemma injective_on_mapping  X {ED':EqDec X eq} (lv:cset W) (m:Map[W, X]) (Z:list W) YL
    (rk:injective_on lv m)
    (IM:inj_mapping (lookup_set m lv) Z YL)
    : injective_on (fromList Z ∪ lv) (update_with_list Z YL m).
  Proof.
    general induction IM; simpl.
    rewrite empty_neutral_union; eauto.
    rewrite union_assoc.
    eapply injective_on_fresh.
    eapply injective_on_forget; eauto.
    intro. eapply lookup_set_incl in H; eauto using incl_minus.
    edestruct (@ra_insert_allocs_cases _ _ _ _ _ _ _ _ y IM); eauto. 
    eapply f0; eapply in_fromList; eauto. 
  Qed.
*)
End InjectiveMapping.

Global Instance inj_mapping_morphism {X} `{OrderedType X} {Y} `{OrderedType Y}
  : Proper (Equal ==> eq ==> eq ==> iff) (@inj_mapping X _ Y _).
Proof.
  unfold Proper, respectful; intros.
  split; intros; subst.
  general induction H4; eauto using inj_mapping. constructor.
  econstructor; eauto. rewrite <- H5; eauto.
  general induction H4; eauto using inj_mapping. constructor.
  econstructor; eauto. rewrite H5; eauto.
Qed.

Global Instance fresh_computable {X} `{OrderedType X} (x:X) L
  : Computable (fresh x L).
Proof.
  constructor.
  general induction L. left; intro A; inv A.
  destruct (IHL _ x); eauto. destruct_prop(x===a); eauto; eqs.
  left; intro A; inv A; eauto.
  right. intro A. eapply n. intro. eapply A. eauto.
Defined.

Global Instance inj_mapping_computable {X Y : Type} `{OrderedType X} `{OrderedType Y} (LV:set Y) (L: list X)  L'
   : Computable (inj_mapping LV L L').
Proof.
  constructor.
  general induction L.
  + destruct L'. 
    - left; econstructor.
    - right. intro A; inv A.
  + destruct L'. 
    - right; intro A; inv A.
    - destruct (IHL _ _ _ LV L'); eauto.
      destruct_prop (fresh a L). 
      destruct_prop (fresh y L'). 
      destruct_prop (y ∈ LV).
      right; intro A; inv A; eauto.
      left; econstructor; eauto. 
      right; intro A; inv A; eauto.
      right; intro A; inv A; eauto.
      right; intro A; inv A; eauto.
Defined.

  
  
  

(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr" "../il"  "..") ***
*** End: ***
*)
