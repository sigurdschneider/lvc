Require Import EqDec DecidableTactics Util AutoIndTac.
Require Export CSet Containers.SetDecide.
Require Export MapBasics MapLookup OrderedTypeEx.
 
Set Implicit Arguments.

Section MapInjectivity.
  Open Scope map_scope.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.
  Context `{OrderedType Y}.

  Definition injective_on D (f:X->Y) :=
    forall x y, x ∈ D -> y ∈ D -> f x === f y -> x === y.

  Lemma injective_on_incl (D D':set X) (f:X -> Y) (SM:D' ⊆ D)
    : injective_on D f -> injective_on D' f.
  Proof.
    firstorder.
  Qed.

  Lemma injective_on_dead lv (f:X -> Y) x v `{Proper _ (respectful _eq _eq) f}
  : injective_on (lv\{{x}}) f
    -> injective_on (lv\{{x}}) (f[x<-v]).
   Proof.
    intros; hnf; intros. lud; eauto.
    + exfalso; cset_tac; eauto.
    + exfalso; cset_tac; eauto.
  Qed.

  Lemma injective_on_fresh lv (f:X -> Y) x xr `{Proper _ (_eq ==> _eq) f}
    :    injective_on (lv\{{x}}) f
      -> ~xr ∈ lookup_set f (lv\{{x}})
      -> injective_on ({{x}} ∪ lv) (f[x <- xr]).
  Proof.
    intros. hnf; intros. lud.
    + exfalso. eapply H3. eapply lookup_set_spec; eauto.
      exists x0. split. 
      - cset_tac. intuition. 
      - eqs.
    + exfalso. eapply H3. eapply lookup_set_spec; eauto.
      eexists y. split; cset_tac; intuition; eauto. 
    + eapply H2; eauto. cset_tac; intuition.
      cset_tac; intuition.
  Qed.

  Lemma injective_on_forget s (f:X -> Y) y `{Proper _ (_eq ==> _eq) f}
  : injective_on s f
    -> injective_on (s\{{y}}) f.
  Proof.
    intros. hnf; intros.
    assert (y =/= y0). intro; cset_tac; firstorder.
    assert (x =/= y). intro; cset_tac; firstorder.
    eapply H. cset_tac; firstorder.
  Qed.

  Lemma lookup_set_minus_incl_inj s t (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
  : injective_on (s ∪ t) m
    -> lookup_set m (s \ t) ⊆ lookup_set m s \ (lookup_set m t).
  Proof.
    intros; hnf; intros.
    eapply lookup_set_spec in H3; decompose records.
    edestruct (minus_in_in _ _ _ _ H5); eauto.
    eapply in_in_minus; eauto. eapply lookup_set_spec; eauto.
    intro. eapply lookup_set_spec in H7; decompose records. 
    subst. eapply H4. rewrite H2; eauto. eapply union_left; eauto.
    eapply union_right; eauto. rewrite <- H6. rewrite <- H10. reflexivity.
    intuition. intuition.
  Qed.

    
End MapInjectivity.
    
Global Instance injective_on_morphism {X} `{OrderedType X} {Y} {HY:OrderedType Y}
  : Proper (Equal ==> (@feq X Y (@_eq Y HY) (@OT_Equivalence Y HY)) ==> iff) (@injective_on X H Y HY).
Proof.
  unfold Proper, respectful; intros.
  split; intros; hnf; intros. 
  + eapply H2; try rewrite H0 ; eauto. 
    hnf in H1. repeat rewrite H1. eauto.
  + eapply H2; cset_tac; eauto; firstorder.
    hnf in H1. repeat rewrite <- H1. eauto.
Qed.


Lemma injective_on_update_not_in {X} `{OrderedType X} {Y} `{OrderedType Y}
  D x (f:X -> Y) `{Proper _ (_eq ==> _eq) f} 
: injective_on (D \ {{x}}) f
  -> f x ∉ lookup_set f (D \ {{x}})
  -> injective_on D f.
Proof.
  intros; hnf; intros. 
  destruct_prop(x0 === x); destruct_prop (x0 === y); eauto.
  exfalso. eapply H3. eapply lookup_set_spec. intuition.
  eexists y. cset_tac; eqs; eauto. rewrite e in H6; eauto.
  eapply H2; cset_tac; eauto. intro. 
  eapply H3. do 2 set_tac; intuition.  eexists x0. cset_tac; intuition.
  rewrite <- H7. eqs.
Qed.

Lemma injective_on_update_fresh {X} `{OrderedType X} {Y} `{OrderedType Y}
  D x y f `{Proper _ (_eq ==> _eq) f}
: injective_on (D \ {{x}}) f
  -> y ∉ lookup_set f (D \ {{x}})
  -> injective_on D (update f x y).
Proof.
  intros; hnf; intros. lud. 
  exfalso. eapply H3. eapply lookup_set_spec. intuition.
  eexists x0. cset_tac; eauto.
  exfalso. eapply H3. eapply lookup_set_spec. intuition.
  eexists y0. cset_tac; eauto.
  eapply H2; cset_tac; eauto.
Qed.

Lemma injective_on_not_in_lookup_set {X} `{OrderedType X} {Y} `{OrderedType Y} f D D' x
    `{Proper _ (_eq ==> _eq) f}
    : injective_on D f
      -> D' ⊆ D\{{x}} -> x ∈ D
      -> f x ∉ lookup_set f D'.
Proof.
  intros. intro. eapply lookup_set_spec in H5; eauto. destruct H5; dcr.
  specialize (H3 _ H6). cset_tac; eauto.
Qed. 

Lemma lookup_set_not_in  {X} `{OrderedType X} {Y} `{OrderedType Y} f D x
    `{Proper _ (_eq ==> _eq) f}
  : f x ∉ lookup_set f D
    -> lookup_set f D \ {{f x}} [=] lookup_set f (D\{{x}}).
Proof.
  intros. cset_tac; split; intros; dcr. eapply lookup_set_spec; eauto.
  + eapply lookup_set_spec in H4. destruct H4; dcr; eauto. eexists x0; cset_tac; eauto.
    intro. eapply H2. eapply lookup_set_spec; eauto. eexists x.  rewrite H3 in H4; eauto.
    intuition. 
  + eapply lookup_set_spec in H3; eauto. destruct H3; dcr. cset_tac.
    eapply lookup_set_spec; eauto.
    intro. eapply H2. eapply lookup_set_spec; eauto. eexists x0; split; eqs; eauto.
Qed.


Definition injective_on_step {X} {Y} `{OrderedType Y}
f (x : X) (p : set Y * bool) :=
      ({f x; fst p}, if snd p then 
        negb (sumbool_bool (@compute_prop (f x ∈ fst p) _))
       else false).

Lemma injective_on_step_transpose {X} {Y} `{OrderedType Y}
f 
  : transpose _eq (@injective_on_step X Y _ f).
Proof.
  hnf; intros. 
  unfold injective_on_step. econstructor.
  destruct z; simpl. econstructor; cset_tac; intuition.
  destruct z. unfold snd. destruct b. 
  unfold fst, snd;
  destruct_prop (f y ∈ s); destruct_prop (f x ∈ {f y; s});
  destruct_prop (f x ∈ s); destruct_prop (f y ∈ {f x; s}); simpl; 
  eauto; cset_tac; intuition.
  econstructor.
Qed.

Lemma injective_on_step_spec {X} `{OrderedType X} {Y} `{OrderedType Y}
f (x : X) (p : set Y * bool) (s:set Y) b
:  snd (injective_on_step f x (s,b))
   -> {f x; s} [=] fst (injective_on_step f x (s,b)).
Proof.
  intros. unfold injective_on_step in *.
  destruct b. unfold snd in *. unfold fst; reflexivity.
  reflexivity.
Qed.


Global Instance injective_on_step_proper 
  {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y) 
  `{Proper _ (_eq ==> _eq) f}
 : Proper (_eq ==> _eq ==> _eq) (injective_on_step f).
Proof.
  unfold Proper, respectful; intros.
  destruct x0, y0. unfold injective_on_step. unfold snd.
  destruct b, b0. unfold fst. econstructor.
  inv H3. rewrite H7. rewrite H2. reflexivity.
  destruct_prop (f x ∈ s); destruct_prop (f y ∈ s0).
  econstructor. exfalso. eapply n. rewrite <- H2.
  inv H3. rewrite <- H7. eauto.
  exfalso. eapply n. rewrite H2.
  inv H3. rewrite H7. eauto. econstructor.
  inv H3. inv H9. inv H3. inv H9.
  econstructor. simpl. rewrite H2.
  inv H3. rewrite H7. econstructor; eauto. econstructor.
Qed.

Global Instance injective_on_step_proper'
  {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y) 
  `{Proper _ (_eq ==> eq) f}
 : Proper (_eq ==> eq ==> eq) (injective_on_step f).
Proof.
  unfold Proper, respectful; intros.
  destruct x0, y0. unfold injective_on_step. unfold snd.
  destruct b, b0. unfold fst. f_equal.
  inv H3. rewrite H2. reflexivity.
  destruct_prop (f x ∈ s); destruct_prop (f y ∈ s0).
  econstructor. exfalso. eapply n. rewrite <- H2.
  inv H3. eauto.
  exfalso. eapply n. rewrite H2.
  inv H3. eauto.
  inv H3. econstructor. inv H3. inv H3.
  inv H3. f_equal. simpl. rewrite H2. reflexivity.
Qed.


Definition injective_on_compute {X} `{OrderedType X} {Y} `{OrderedType Y} 
  (D:set X) (f: X-> Y) `{Proper _ (_eq ==> _eq) f} : bool 
  := snd (fold (injective_on_step f) D (∅, true)).

Lemma injective_on_compute_lookup_set {X} `{OrderedType X} {Y} `{OrderedType Y} 
   (f: X-> Y) `{Proper _ (_eq ==> _eq) f}
: 
  forall D LD',
    lookup_set f D ∪ LD' [=] fst (fold (injective_on_step f) D (LD', true)).
Proof.
  intros.
  eapply (@fold_rec _ _ _ _ _ (fun (D:set X) (fld:set Y * bool) => 
          lookup_set f D ∪ LD' [=] fst fld
         ) _ (LD', true)); intros; simpl.

  + eapply empty_is_empty_1 in H2.
    set_tac; intuition. destruct H4; cset_tac.
    eapply H2 in H4. cset_tac; intuition.
  
  + cset_tac.
    split; intros. destruct H6. set_tac. destruct H6; dcr.
    eapply H4 in H7. destruct H7. rewrite <- H6 in H8; eauto.
    right. eapply H5. cset_tac. left. set_tac. eexists x0; intuition.
    eauto. eauto. right. eapply H5. cset_tac. right; eauto.
    destruct H6. left. set_tac. eexists x; intuition.
    eapply H4. eauto. intuition.
    eapply H5 in H6. cset_tac; intuition.
    left. set_tac; intuition. set_tac; intuition.
    eexists x0; eauto. split; eauto. eapply H4. right; eauto.
Qed.

 
Definition injective_on_iff {X} `{OrderedType X} {Y} `{OrderedType Y} 
   (f: X-> Y) `{Proper _ (_eq ==> _eq) f} D
: forall D' LD', 
    D' ∩ D [=] ∅
    -> lookup_set f D' [=] LD' 
    -> injective_on D' f 
    -> (snd (fold (injective_on_step f) D (LD', true)) <-> (injective_on (D ∪ D') f)).
Proof.
  pattern D. eapply set_induction; intros.
  eapply empty_is_empty_1 in H2. intuition. eapply injective_on_incl; eauto.
  rewrite H2. cset_tac; intuition.
  
  pose proof (@fold_equal X _ _ _ _ _ _ (injective_on_step f) _ (injective_on_step_transpose f) (LD', true) _ _ H2). 
  rewrite fold_empty in H7.
  destruct (fold (injective_on_step f) s (LD', true)). inv H7. inv H13.
  eapply I.

   
  pose proof H4 as FOO. eapply Add_Equal in H4.
  pose proof (@fold_equal X _ _ _ _ _ _ (injective_on_step f) _ (injective_on_step_transpose f) (LD', true) _ _ H4). 
  destruct (fold (injective_on_step f) s' (LD', true)). 
  rewrite (@fold_add X _ _ _ _ _ _ (injective_on_step f) (injective_on_step_proper f) (injective_on_step_transpose f) (LD', true) _ _ H3) in H8.

  destruct_prop (x ∈ D'). exfalso. destruct (FOO x).
  cset_tac; intuition. eapply (H5 x). intuition cset_tac. 
  eapply H11; reflexivity.
  assert (D' ∩ s [=] ∅). cset_tac; intuition. destruct (FOO a).
  eapply H5; split; eauto.

(*  erewrite <- H9. cset_tac; intuition. eapply H4. eapply add_iff. right; eauto. *)
  
  specialize (H2 D' _ H9 H6 H7).
  case_eq (fold (injective_on_step f) s (LD', true)); intros; rewrite H10 in *.
  unfold injective_on_step in H8. unfold fst in H8.
  destruct_prop (f x ∈ s1).
  destruct b. try now (destruct b0; simpl in *; inv H8; isabsurd). 
  simpl; split; intros; isabsurd.

  simpl_pair_eqs.
  pose proof (injective_on_compute_lookup_set s LD'). 
  rewrite H12 in H10. clear H8.
  rewrite <- H10 in i. rewrite <- H6 in i. rewrite <- lookup_set_union in i.
  eapply lookup_set_spec in i. destruct i; dcr.
  eapply H11 in H15. cset_tac. rewrite H15 in n,H3. destruct H14; eauto.
  rewrite H4; cset_tac; intuition.
  rewrite H4; cset_tac; intuition. intuition. intuition.
  
  destruct b, b0; try now (simpl in *; inv H8; isabsurd). 
  simpl; split; intros; eauto.
  destruct H2. specialize (H2 I).
  simpl_pair_eqs.
  pose proof (injective_on_compute_lookup_set s LD'). simpl.
  rewrite H13 in H10.
  clear H8.
  rewrite <- H10 in n0. 
  rewrite <- H6 in n0. rewrite <- lookup_set_union in n0.
  assert (s ∪ D' [=] (s' ∪ D') \ {{x}}). 
  rewrite H4. cset_tac; intuition. 
  intro A; rewrite A in H13; eauto.
  intro A; rewrite A in H13; eauto.
  rewrite H8 in n0. rewrite H8 in H2.
  pose proof (injective_on_update_not_in H2 n0); eauto. intuition.

  simpl. split; intros; isabsurd.
  simpl in H2. eapply H2. eapply injective_on_incl; eauto.
  rewrite H4. cset_tac; intuition.
Qed.

Global Instance injective_on_computable {X} `{OrderedType X} {Y} `{OrderedType Y} 
  (D:set X) (f: X-> Y) `{Proper _ (_eq ==> _eq) f} `{Proper _ (_eq ==> eq) f}
: Computable (injective_on D f).
Proof.
  econstructor.    
  case_eq (@injective_on_compute X _ Y _ D f _); eauto; intros.
  left. pose proof (@injective_on_iff X _ Y _ f _ D ∅ ∅).
  destruct H4; eauto. cset_tac; intuition. set_tac; intuition.
  edestruct H4; cset_tac; intuition. isabsurd.
  unfold injective_on_compute in H3.
  rewrite H3 in H4. specialize (H4 I). eapply injective_on_incl ;eauto.
  cset_tac; eauto.
  right. intro. 
  pose proof (@injective_on_iff X _ Y _ f _ D ∅ ∅).
  edestruct H5. cset_tac; intuition. cset_tac; intuition.
  assert (a ∈ lookup_set f D).
  set_tac; eauto. set_tac; eauto. eexists x. intuition.
  set_tac; eauto. set_tac. destruct H6; cset_tac. eauto.
  intuition. isabsurd. 
  change False with (Is_true false). rewrite <- H3.
  unfold injective_on_compute in H3. rewrite H3 in H7. 
  unfold injective_on_compute. rewrite H3. eapply H7.
  eapply injective_on_incl; eauto. cset_tac; intuition.
Defined.

Lemma lookup_set_minus_eq X `{OrderedType X} Y `{OrderedType Y} s t (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
: injective_on (s ∪ t) m
  -> lookup_set m (s \ t) [=] lookup_set m s \ (lookup_set m t).
Proof.
  split; intros. eapply lookup_set_minus_incl_inj; eauto.
  apply lookup_set_minus_incl; eauto.
Qed.


(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lyn")) ***
*** End: ***
*)
