Require Export Setoid Coq.Classes.Morphisms.  
Require Import EqDec DecidableTactics Util LengthEq AutoIndTac.
Require Export CSet Containers.SetDecide.
Require Export MapBasics MapLookup MapAgreement.

Set Implicit Arguments.

Section MapUpdate.
  Open Scope map_scope.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.
  Context `{OrderedType Y}.

  Fixpoint update_list (m:X -> Y) (f:X -> Y) (L:list X) := 
    match L with
      | nil => m
      | x::L => (update_list m f L) [x <- f x]
    end.

  Lemma update_list_agree_minus lv (E E' f:X -> Y) XL
    :  agree_on lv E' E 
    -> agree_on (lv\of_list XL) (update_list E' f XL) E.
  Proof.
    intros. general induction XL; simpl. rewrite minus_empty. eassumption.
    rewrite add_union_singleton. rewrite union_comm. rewrite <- minus_union. 
    eapply agree_on_update_dead.
    cset_tac. intro; decompose records; eauto. 
    eauto using agree_on_incl, incl_minus.
  Qed.

  Corollary update_list_agree_self lv (E:X -> Y) L f
    : agree_on (lv\of_list L) (update_list E f L) E.
  Proof. 
    eapply update_list_agree_minus. reflexivity.
  Qed.

  Lemma update_list_no_upd  (m:X -> Y) f L x
    : x ∉ of_list L
    -> (update_list m f L) x === m x.
  Proof.
    intros. general induction L; simpl; eauto. lud.
    + exfalso. eapply H1. simpl in * |- *. rewrite e. eapply add_1; eauto.
    + assert (~x ∈ of_list L). 
      - intro. eapply H1. simpl. eapply add_2; eauto.
      - eauto. 
  Qed.

  Lemma update_list_upd  (m:X -> Y) f L x
    : x ∈ of_list L
    -> Proper (_eq ==> _eq) f
    -> (update_list m f L) x === f x.
  Proof.
    intros. general induction L; simpl; eauto.
    + simpl in *; cset_tac; firstorder.
    + lud. 
      - rewrite e; eauto.
      - eapply IHL; eauto. eapply zadd_3; eauto.
  Qed.

End MapUpdate.


Section MapUpdateList.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.

  Open Scope map_scope.

  Fixpoint update_with_list XL YL (m:X -> Y) :=
    match XL, YL with
      | x::XL, y::YL => (update_with_list XL YL m)[x <- y]
      | _, _ => m
    end.

  Notation "f [ w <-- x ]" := (update_with_list w x f) (at level 29, left associativity).


  Lemma update_with_list_agree lv (E E':X -> Y) XL YL
    : agree_on (lv\of_list XL) E E'
    -> length XL = length YL
    -> agree_on lv (E [ XL <-- YL]) (E' [ XL <-- YL ]).
  Proof.
    intros. eapply length_length_eq in H1.
    general induction XL; simpl in * |- *. rewrite (@minus_empty _ _ lv) in H0; eauto.
    inv H1. eapply agree_on_update_same.
    eapply IHXL; eauto. rewrite minus_union; eauto.
    rewrite add_union_singleton. rewrite (empty_union_2 (s:=∅)); eauto.
    rewrite <- add_union_singleton; eauto.
    eapply SetInterface.empty_1.
  Qed.

  Lemma update_with_list_no_update (E:X -> Y) Y' Z x
    : x ∉ of_list Z
    -> (E [ Z <-- Y' ]) x = E x.
  Proof.
    intros. general induction Z; simpl; destruct Y'; eauto.
    lud.
    + exfalso. eapply H0. simpl; cset_tac; intuition. 
    + simpl in H0. assert (x ∉ of_list Z).
      - cset_tac; intuition. 
      - eapply IHZ; eauto.
  Qed.

  Lemma update_with_list_agree_minus lv (E E':X -> Y) XL YL 
    : length XL = length YL
    -> agree_on lv E' E 
    -> agree_on (lv\of_list XL) (E' [ XL <-- YL ]) E.
  Proof.
    intros. eapply length_length_eq in H0. 
    general induction H0; simpl. rewrite minus_empty. eassumption.
    rewrite add_union_singleton. rewrite union_comm. rewrite <- minus_union. 
    eapply agree_on_update_dead.
    cset_tac. intro; decompose records; eauto. 
    eauto using agree_on_incl, incl_minus.
  Qed.



  Lemma update_with_list_agree_self  `{Defaulted X} lv (E:X -> Y) XL YL
    : agree_on (lv\of_list XL) (E [ XL <-- YL]) E.
  Proof.
    general induction XL; simpl. rewrite minus_empty. eapply agree_on_refl.
    destruct YL. apply agree_on_refl.
    rewrite add_union_singleton. 
    rewrite union_comm. rewrite <- minus_union. eapply agree_on_update_dead.
    cset_tac. intro; decompose records; eauto. 
    eapply agree_on_incl. eapply IHXL; eauto.
    instantiate (1:=lv). eapply incl_minus.
  Qed.

  Lemma update_id `{OrderedType Y} (m:X -> Y) x `{Proper _ (_eq ==> _eq) m}
    : feq (m [x <- m x])  m.
  Proof.
    intros y. lud. rewrite e; eauto.
  Qed. 

End MapUpdateList.

Notation "f [ w <-- x ]" := (update_with_list w x f) (at level 29, left associativity). 

Instance update_inst X `{OrderedType X} Y `{OrderedType Y} :
  Proper ((@feq X Y _ _) ==> _eq ==> _eq ==> feq) (@update X Y _).
Proof.
  unfold respectful, Proper, update, feq; intros. 
  repeat destruct if; eqs; eauto. 
  exfalso. eapply H7. eapply H2.
  exfalso. eapply H8. eapply H2.
Qed.

Lemma update_with_list_id X `{OrderedType X} (l:list X) 
  : feq (update_with_list l l id) id.
Proof.
  general induction l; simpl. reflexivity.
  rewrite IHl. change a with (id a) at 2. 
  pose proof update_id. specialize (H0 X _ X _ id a).
  eapply H0. firstorder.
Qed.

Lemma update_with_list_lookup_in {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y) Z Z' x
  : length Z = length Z'
  -> x ∈ of_list Z
  -> f [ Z <-- Z' ] x ∈ of_list Z'.
Proof.
  intros L. eapply length_length_eq in L. 
  general induction L; simpl in * |- *. exfalso; cset_tac; firstorder.
  eapply add_iff in H1. destruct H1.
  lud; try eapply add_1; eauto.
  lud. eapply add_1; eauto.
  eapply add_iff. right. eapply IHL; eauto.
Qed.

Lemma update_with_list_lookup_not_in {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y) (Z:list X) (Z':list Y) x y
  : x ∉ of_list Z
    -> f [ Z <-- Z' ] x = y
    -> f x = y.
Proof.
  general induction Z; simpl in * |- *; eauto. 
  destruct Z'; eauto. lud. rewrite add_iff in H1.
  exfalso; firstorder.
  eapply IHZ; eauto. intro. eapply H1. eapply add_2; eauto.
Qed.

Instance proper_update_with_list {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y) Z Z' 
: length Z = length Z'
  -> Proper (_eq ==> _eq) f
  -> Proper (_eq ==> _eq) (f [Z <-- Z']).
Proof.
  intros. eapply length_length_eq in H1.
  general induction H1; intuition.
  simpl. hnf; intros. unfold update. 
  repeat destruct if; try (now exfalso; eqs; intuition).
  reflexivity.
  eapply IHlength_eq; intuition.
Qed.
                   

Lemma update_with_list_lookup_set_incl {X} `{OrderedType X} {Y} `{OrderedType Y} 
(f:X->Y) Z Z' `{Proper _ (_eq ==> _eq) f} D
  : length Z = length Z'
  -> D ⊆ of_list Z
  -> lookup_set (f [ Z <-- Z' ]) D ⊆ of_list Z'.
Proof.
  intros. hnf; intros. 
  eapply lookup_set_spec in H4; try eapply proper_update_with_list; eauto.
  destruct H4; dcr. rewrite H6. eapply update_with_list_lookup_in; eauto.
Qed.

Instance update_list_morphism {X} `{OrderedType X} {Y} `{OrderedType Y}
  : Proper (@feq X _ _ _ ==> @feq X _ _ _ ==> eq ==> feq) (@update_list X _ Y).
Proof.
  unfold Proper, respectful; intros. subst.
  general induction y1. simpl. eauto. simpl.
  rewrite IHy1; eauto. hnf; intros; lud. eapply H2.
Qed.

(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
