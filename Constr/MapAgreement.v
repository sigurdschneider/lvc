Require Export Setoid Coq.Classes.Morphisms.  
Require Import EqDec Computable Util AutoIndTac.
Require Export CSet Containers.SetDecide.
Require Export MapBasics MapLookup.

Set Implicit Arguments.

Section MapAgreement.
  Open Scope map_scope.

  Variable X : Type.
  Context `{OrderedType X}.

  Variable Y : Type.

  Definition agree_on `{Equivalence Y} (D:set X) (E E':X -> Y) := 
    forall x, x ∈ D -> R (E x) (E' x).

  Lemma agree_on_refl `{Equivalence Y} L (E:X -> Y) 
    : agree_on L E E.
  Proof.
    firstorder.
  Qed.

  Lemma agree_on_sym `{Equivalence Y} L (E E':X -> Y) 
    : agree_on L E E' -> agree_on L E' E.
  Proof.
    intros; hnf; firstorder.
  Qed.

  Lemma agree_on_trans `{Equivalence Y} L (E E' E'':X -> Y) 
    : agree_on L E E' -> agree_on L E' E'' -> agree_on L E E''.
  Proof.
    intros; hnf; intros. transitivity (E' x); eauto.
  Qed.

  Lemma agree_on_update `{Equivalence Y} L (E E':X->Y) (x:X) (v:Y)
    : agree_on L E E' -> agree_on L (E[x<-v]) (E'[x<-v]).
  Proof.
    intros. hnf; intros; lud; eauto.
  Qed.

  Lemma agree_on_incl `{Equivalence Y} (bv lv:set X) (E E': X -> Y)
    : agree_on lv E E'
    -> bv ⊆ lv
    -> agree_on bv E E'.
  Proof.
    firstorder.
  Qed.

  Lemma agree_on_update_same `{Equivalence Y} (lv:set X) (E E':X -> Y) x v
    : agree_on (lv\{{x}}) E E'
    -> agree_on lv (E [x <- v]) (E' [x <- v]).
  Proof.
    intros A. hnf; intros; lud;
    eapply A. eapply in_in_minus; eauto. eapply neq_not_in_single. eqs.
  Qed.

  Lemma agree_on_update_any_same `{Equivalence Y} (lv:set X) (E E':X -> Y) x v
    : agree_on lv E E'
    -> agree_on (lv ∪ {{x}}) (E [x <- v]) (E' [x <- v]).
  Proof.
    intros A. hnf; intros; lud; eapply A.
    eapply union_cases in H1; destruct H1; eauto.
    eapply single_spec_neq in H1. exfalso; eauto.
  Qed.

  Lemma agree_on_update_dead `{Equivalence Y} (lv:set X) (E E':X -> Y) x v
    : ~x ∈ lv
    -> agree_on lv E E'
    -> agree_on lv (E [x <- v]) E'.
  Proof.
    intros A B.
    hnf; intros; lud. cset_tac.
    eapply B; eauto.
  Qed.

  Lemma agree_on_update_dead_both `{Equivalence Y} (lv:set X) (E E':X -> Y) x v v'
    : ~x ∈ lv
    -> agree_on lv E E'
    -> agree_on lv (E [x <- v]) (E'[x <- v']).
  Proof.
    intros A B. eauto using agree_on_trans, agree_on_update_dead, agree_on_sym.
  Qed.


(*
  Global Instance lookup_fun_inst `{OrderedType Y} {m:X -> Y}
    : Proper (_eq ==> _eq) m.
  Proof.
    hnf; intros; simpl. rewrite H2. eauto.
  Qed.
*)

End MapAgreement.

Arguments agree_on {X} {H} {Y} {R} {_} D E E'.

Global Instance agree_on_reflexive X `{OrderedType X} Y `{OrderedType Y} {s:set X}
 : Reflexive (@agree_on X _ Y _ _ s).
firstorder using agree_on_refl.
Qed.

Global Instance agree_on_symmetric X `{OrderedType X} Y `{OrderedType Y} {s:set X}
 : Symmetric (@agree_on X _ Y _ _ s).
firstorder using agree_on_sym.
Qed.

Global Instance agree_on_transitive X `{OrderedType X} Y `{OrderedType Y} {s:set X}
 : Transitive (@agree_on X _ Y _ _ s).
hnf; intros. eauto using agree_on_trans.
Qed.

Global Instance agree_on_equivalence X `{OrderedType X} Y `{OrderedType Y} {s:set X}
 : Equivalence (@agree_on X _ Y _ _ s).
econstructor; eauto using agree_on_reflexive, agree_on_symmetric, agree_on_transitive.
Qed.

Lemma lookup_set_agree X `{OrderedType X} Y `{OrderedType Y} s (m m':X -> Y)
`{Proper _ (respectful _eq _eq) m} `{Proper _ (respectful _eq  _eq) m'}
: agree_on s m m' -> lookup_set m s [=] lookup_set m' s.
Proof.
  intros; split; intros. 
  - eapply lookup_set_spec; eauto. eapply lookup_set_spec in H4; dcr; eauto.
    eexists x; split; eauto. rewrite H7; eauto. eapply H3; eauto.
  - eapply lookup_set_spec; eauto. eapply lookup_set_spec in H4; dcr; eauto.
    eexists x; split; eauto. rewrite H7; symmetry; eapply H3; eauto. 
Qed.



(*Global Instance test X `{OrderedType X} Y `{Equivalence Y}
: Proper ((@feq X _ _ Y _ _) ==> (@feq X _ _ Y _ _) ==> iff) R.
*)
Global Instance eq_cset_agree_on_morphism X `{OrderedType X} Y `{Equivalence Y}
: Proper (SetInterface.Equal ==> (@feq X Y _ _) ==> feq ==> iff) agree_on.
Proof.
  intros. split; intros; hnf; intros. 
  + rewrite <- (H2 x2); try reflexivity. erewrite <- (H3 x2); try reflexivity. 
    eapply H4. eapply H1; eauto.
  + erewrite (H2 _ ); try reflexivity. erewrite (H3 _); try reflexivity.
    eapply H4. eapply H1; eauto.
Qed.

Global Instance incl_agree_on_morphism X `{OrderedType X} Y `{OrderedType Y}
: Proper (SetInterface.Equal ==> (@feq X Y _ _) ==> feq ==> flip impl) agree_on.
Proof.
  unfold respectful, impl; hnf; intros; hnf; intros.
  hnf in H2. unfold equiv in H2.
  hnf; intros. erewrite (H2 _ ); try reflexivity. erewrite (H3 _); try reflexivity.
  apply H4. eapply H1; eauto.
Qed.

Lemma agree_on_union {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y) g D D'
  : agree_on D f g
  -> agree_on D' f g
  -> agree_on (D ∪ D') f g.
Proof.
  intros. hnf; intros. cset_tac. destruct H3; eauto.
Qed.

Global Instance agree_on_computable {X} `{OrderedType X} {Y} `{OrderedType Y}
 (f g:X->Y) D `{Proper _ (_eq ==> _eq) f} `{Proper _ (_eq ==> _eq) g}
  : Computable (agree_on D f g).
Proof.
  case_eq (for_all (fun x => @decision_procedure (f x === g x) _) D); intros.
  eapply for_all_iff in H3. left. hnf; intros.
  specialize (H3 _ H4). simpl in H3.
  unfold decision_procedure in H3; simpl in H3.
  unfold inst_equiv_cm in H3.
  destruct (inst_eq_dec_ordered_type Y H0 (f x) (g x)); eauto; isabsurd.
  hnf; intros. simpl.
  unfold decision_procedure, inst_equiv_cm.
  destruct (inst_eq_dec_ordered_type Y H0 (f x) (g x));
  destruct (inst_eq_dec_ordered_type Y H0 (f y) (g y)); try constructor.
  exfalso. eapply c. rewrite <- H4. eauto.
  exfalso. eapply c. rewrite H4. eauto.
  right. intro.
  change False with (Is_true false). rewrite <- H3.
  eapply Is_true_eq_left. rewrite <- for_all_iff.
  hnf; intros. simpl. specialize (H4 _ H5).
  unfold decision_procedure, inst_equiv_cm.
  destruct (inst_eq_dec_ordered_type Y H0 (f x) (g x)); simpl; eauto.
  hnf; intros. simpl.
  unfold decision_procedure, inst_equiv_cm.
  destruct (inst_eq_dec_ordered_type Y H0 (f x) (g x));
  destruct (inst_eq_dec_ordered_type Y H0 (f y) (g y)); try constructor.
  exfalso. eapply c. rewrite <- H5. eauto.
  exfalso. eapply c. rewrite H5. eauto.
Defined.

Extraction Inline agree_on_computable.

(* 
 *** Local Variables: ***
 *** coq-load-path: (("../" "Lvc")) ***
 *** End: ***
 *)
