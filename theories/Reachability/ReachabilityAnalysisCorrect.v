Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet OptionR MoreList.
Require Import Val Var Env IL Annotation AnnotationLattice Infra.Lattice.
Require Import DecSolve Analysis Filter Terminating ContextMap.
Require Import Analysis AnalysisForward FiniteFixpointIteration.
Require Import Reachability ReachabilityAnalysis Subterm.

Set Implicit Arguments.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {Dom} {H} {H0} {H1} ftransform ZL st ST AL a.

(*
(* Coq can't figure out the instantiation (fun _ => bool) via unification,
   so we have to add this specialized lemma *)
Lemma forward_length_ass_UC
      (sT : stmt)
      (f : forall sT0 : stmt,
          〔params〕 ->
          forall s : stmt, subTerm s sT0 -> bool -> anni bool)
      (s : stmt) (ST : subTerm s sT) (ZL : 〔params〕)
      k (a : ann bool)
  : ❬ZL❭ = k -> ❬snd (forward f ZL s ST a)❭ = k.
  eapply (@forward_length_ass _ (fun _ => bool)).
Qed.


Hint Resolve forward_length_ass_UC.
 *)

Lemma forward_getAnn (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, ctxmap params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT)) s (ST:subTerm s sT) ZL a an
      AL
  : poEq (fst (@forward sT Dom _ _ _ f ZL s ST AL (setTopAnn an a))) an
    -> getAnn an ≣ a.
Proof.
  intros. eapply ann_R_get in H2.
  rewrite forward_getAnn' in H2. rewrite getAnn_setTopAnn in H2.
  symmetry; eauto.
Qed.

Lemma forward_setTopAnn_inv (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, ctxmap params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
      (fExt:forall (s0 : stmt) (ST0 : subTerm s0 sT) ZL0 (a0 b : Dom sT),
          a0 ≣ b -> f sT ZL0 s0 ST0 a0 ≣ f sT ZL0 s0 ST0 b)
      s (ST:subTerm s sT) ZL AL a an
  : poEq (fst (@forward sT Dom _ _ _ f ZL s ST AL (setTopAnn an a))) an
    -> poEq (fst (@forward sT Dom _ _ _ f ZL s ST AL an)) an /\ getAnn an ≣ a.
Proof.
  intros. split; eauto using forward_getAnn.
  rewrite <- H2 at 2.
  eapply ann_R_get in H2.
  rewrite forward_getAnn' in H2. rewrite getAnn_setTopAnn in H2.
  eapply forward_ext; eauto.
  rewrite setTopAnn_eta_poEq; eauto.
Qed.

Lemma forward_setTopAnn_inv_poLe (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, ctxmap params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
      s (ST:subTerm s sT) ZL a an AL
  : poLe an (fst (@forward sT Dom _ _ _ f ZL s ST AL (setTopAnn an a)))
    -> getAnn an ⊑ a.
Proof.
  intros.
  eapply ann_R_get in H2.
  rewrite (@forward_getAnn' sT Dom) in H2.
  rewrite getAnn_setTopAnn in H2. eauto.
Qed.

Ltac forward_setTopAnn_inv :=
  match goal with
  | [ H: poEq (fst (@forward ?sT ?Dom _ _ _ ?f ?ZL ?AL ?s ?ST (setTopAnn ?an ?a))) ?an |- _ ]
    => eapply (@forward_setTopAnn_inv sT Dom _ _ _ f ltac:(eauto)) in H;
      destruct H
(*  | [ H: poLe (fst (@forward ?sT ?Dom _ _ _ ?f ?ZL ?s ?ST (setTopAnn ?an ?a))) |- _ ]
    => eapply (@forward_setTopAnn_inv sT Dom _ _ _ f) in H;
      destruct H*)
  end.

Smpl Add forward_setTopAnn_inv : inv_trivial.

Lemma forward_setTopAnn_inv_snd (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, ctxmap params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
      (fExt:forall (s0 : stmt) (ST0 : subTerm s0 sT) ZL0 (a0 b : Dom sT),
          a0 ≣ b -> f sT ZL0 s0 ST0 a0 ≣ f sT ZL0 s0 ST0 b)
      a an (EQ:getAnn an ≣ a)
      s (ST:subTerm s sT) ZL AL
  : poEq (@forward sT Dom _ _ _ f ZL s ST AL (setTopAnn an a))
         (@forward sT Dom _ _ _ f ZL s ST AL an).
Proof.
  intros.
  eapply forward_ext; eauto.
  rewrite setTopAnn_eta_poEq; eauto.
Qed.

Lemma forward_setTopAnn_inv_snd' (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, ctxmap params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
      (fExt:forall (s0 : stmt) (ST0 : subTerm s0 sT) ZL0 (a0 b : Dom sT),
          a0 ≣ b -> f sT ZL0 s0 ST0 a0 ≣ f sT ZL0 s0 ST0 b)
      a an (EQ:getAnn an ≣ a)
      s (ST:subTerm s sT) ZL AL
  : poLe (@forward sT Dom _ _ _ f ZL s ST AL (setTopAnn an a))
         (@forward sT Dom _ _ _ f ZL s ST AL an).
Proof.
  intros.
  rewrite forward_ext; eauto. reflexivity. reflexivity.
  rewrite setTopAnn_eta_poEq; eauto.
Qed.

Ltac forward_setTopAnn_inv_snd :=
  match goal with
  | [ H : context [ @forward ?sT ?Dom ?PO ?JSL ?LB ?f ?ZL ?s ?ST ?AL
                             (setTopAnn ?an ?a) ],
      I : getAnn ?an ≣ ?a |- _ ]
    => setoid_rewrite (@forward_setTopAnn_inv_snd sT Dom PO JSL LB f
                                          ltac:(eauto) _ _ I s ST ZL AL) in H
  | [ H : context [ @forward ?sT ?Dom ?PO ?JSL ?LB ?f ?ZL ?s ?ST ?AL
                             (setTopAnn ?an ?a) ],
      I : getAnn ?an ≣ ?a |- _ ]
    => setoid_rewrite (@forward_setTopAnn_inv_snd' sT Dom PO JSL LB f
                                          ltac:(eauto) _ _ I s ST ZL AL) in H
  end.

(* Smpl Add forward_setTopAnn_inv_snd : inv_trivial. *)

Instance zip_join_proper_poEq X `{JoinSemiLattice X}
  : Proper (poEq ==> poEq ==> poEq) (zip join).
Proof.
  unfold Proper, respectful; intros.
  eapply poEq_join_zip; eauto.
Qed.

Instance zip_join_proper_poLe' X `{JoinSemiLattice X}
  : Proper (poLe ==> poLe ==> poLe) (zip join).
Proof.
  unfold Proper, respectful; intros.
  eauto.
Qed.

Instance drop_proper_poEq X `{PartialOrder X} n
  : Proper (poEq ==> poEq) (drop n).
Proof.
  unfold Proper, respectful; intros.
  eapply poEq_drop; eauto.
Qed.

Instance drop_proper_poLe X `{PartialOrder X} n
  : Proper (poLe ==> poLe) (drop n).
Proof.
  unfold Proper, respectful; intros.
  eapply poLe_drop; eauto.
Qed.

Instance fold_left_zip_join_proper_poEq X `{JoinSemiLattice X}
  : Proper (poEq ==> poEq ==> poEq) (fold_left (zip join)).
Proof.
  unfold Proper, respectful; intros.
  eauto.
Qed.

Instance fold_left_zip_join_proper_poLe X `{JoinSemiLattice X}
  : Proper (poLe ==> poLe ==> poLe) (fold_left (zip join)).
Proof.
  unfold Proper, respectful; intros.
  eauto.
Qed.

Instance setTopAnn_proper_poEq X `{PartialOrder X}
  : Proper (poEq ==> poEq ==> poEq) (@setTopAnn X).
Proof.
  unfold Proper, respectful; intros. eauto.
Qed.

Instance setTopAnn_proper_poLe X `{PartialOrder X}
  : Proper (poLe ==> poLe ==> poLe) (@setTopAnn X).
Proof.
  unfold Proper, respectful; intros. eauto.
Qed.

Instance zip_setTopAnn_proper_poEq X `{PartialOrder X}
  : Proper (poEq ==> poEq ==> poEq) (zip (@setTopAnn X)).
Proof.
  unfold Proper, respectful; intros. eauto.
Qed.

Instance zip_setTopAnn_proper_poLe X `{PartialOrder X}
  : Proper (poLe ==> poLe ==> poLe) (zip (@setTopAnn X)).
Proof.
  unfold Proper, respectful; intros. eauto.
Qed.

Instance map_getAnn_proper_poEq X `{PartialOrder X}
  : Proper (poEq ==> poEq) (List.map getAnn).
Proof.
  unfold Proper, respectful; intros.
  eapply poEq_map; eauto.
  intros. rewrite H1; eauto.
Qed.

Instance map_getAnn_proper_poLe X `{PartialOrder X}
  : Proper (poLe ==> poLe) (List.map getAnn).
Proof.
  unfold Proper, respectful; intros.
  eapply poLe_map; eauto.
  intros. rewrite H1; eauto.
Qed.


Lemma setTopAnn_map_inv_poEq X `{PartialOrder X} A B
  : setTopAnn (A:=X) ⊜ A B ≣ A
    -> Take.take ❬A❭ B ≣ getAnn ⊝ A.
Proof.
  intros. general induction A; destruct B; simpl; eauto.
  - exfalso. inv H0.
  - simpl in *. inv H0; inv_cleanup.
    eapply poEq_list_struct; eauto.
    rewrite <- pf. rewrite getAnn_setTopAnn. reflexivity.
Qed.

Inductive sndR X Y (R:X -> Y -> Prop) : X -> option Y -> Prop :=
| SndR_R x y : R x y -> sndR R x (Some y).

Instance sndR_poEq_proper_impl X `{PartialOrder X}
  : Proper (poEq ==> poEq ==> impl) (@sndR X X poLe).
Proof.
  unfold Proper, respectful, impl; intros.
  inv H2; clear_trivial_eqs. econstructor.
  rewrite <- H0, H1; eauto.
Qed.

Instance sndR_poEq_proper_flip_impl X `{PartialOrder X}
  : Proper (poEq ==> poEq ==> flip impl) (@sndR X X poLe).
Proof.
  unfold Proper, respectful, impl, flip; intros.
  inv H2; clear_trivial_eqs. econstructor.
  rewrite H0, H1; eauto.
Qed.

Instance sndR_poEq_proper_flip_impl' X `{PartialOrder X}
  : Proper (poEq ==> poEq ==> flip impl) (@sndR X X (flip poLe)).
Proof.
  unfold Proper, respectful, impl, flip; intros.
  inv H2; clear_trivial_eqs. econstructor.
  rewrite H0, H1; eauto.
Qed.

Instance sndR_poEq_proper_impl' X `{PartialOrder X}
  : Proper (poLe ==> poEq ==> impl) (@sndR X X (flip poLe)).
Proof.
  unfold Proper, respectful, impl, flip; intros.
  inv H2; clear_trivial_eqs. econstructor.
  rewrite H1, <- H0. eauto.
Qed.

Instance sndR_poEq_proper_impl'' X `{PartialOrder X}
  : Proper (flip poLe ==> poEq ==> flip impl) (@sndR X X (flip poLe)).
Proof.
  unfold Proper, respectful, impl, flip; intros.
  inv H2; clear_trivial_eqs. econstructor.
  rewrite H1, <- H0. eauto.
Qed.

Instance sndR_poEq_proper X `{PartialOrder X}
  : Proper (poEq ==> poEq ==> iff) (@sndR X X poLe).
Proof.
  unfold Proper, respectful, impl; intros.
  split; rewrite H0, H1; eauto.
Qed.


Definition ctxRel A B (R:A -> B -> Prop) (AL:list A) (m:ctxmap B) :=
  length AL = ctxmap_len m
  /\ forall n a, get AL n a -> sndR R a (ctxmap_at m n).


Smpl Add
     match goal with
     | [ H : ?x ≣ ?y, Get : get ?y ?n ?a |- _ ] =>
       match goal with
       | [ Get' : get x n _ |- _ ] => fail 1
       | _ => edestruct (PIR2_nth_2 H Get) as [? [? ?]]
       end
     | [ H : ?y ≣ ?x, Get : get ?y ?n ?a |- _ ] =>
       match goal with
       | [ Get' : get x n _ |- _ ] => fail 1
       | _ => edestruct (PIR2_nth H Get) as [? [? ?]]
       end
     | [ H : ?x ⊑ ?y, Get : get ?y ?n ?a |- _ ] =>
       match goal with
       | [ Get' : get x n _ |- _ ] => fail 1
       | _ => edestruct (PIR2_nth_2 H Get) as [? [? ?]]
       end
     | [ H : ?y ⊑ ?x, Get : get ?y ?n ?a |- _ ] =>
       match goal with
       | [ Get' : get x n _ |- _ ] => fail 1
       | _ => edestruct (PIR2_nth H Get) as [? [? ?]]
       end
     end : inv_get.


Instance ctxRel_proper A `{PartialOrder A}
  : Proper (poEq ==> poEq ==> impl) (@ctxRel A A poLe).
Proof.
  unfold Proper, respectful, impl; intros.
  destruct H2. split; eauto.
  rewrite <- H0, <- H1. eauto.
  intros. rewrite ctxmap_at_poEq; eauto.
  inv_get. rewrite <- H6. eauto.
Qed.

Instance ctxRel_proper_flip A `{PartialOrder A}
  : Proper (poEq ==> poEq ==> flip impl) (@ctxRel A A poLe).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  eapply ctxRel_proper; eauto.
Qed.

Instance ctxRel_proper_iff A `{PartialOrder A}
  : Proper (poEq ==> poEq ==> iff) (@ctxRel A A poLe).
Proof.
  unfold Proper, respectful, impl; intros.
  split; intros.
  rewrite <- H1. rewrite <- H0. eauto.
  rewrite H1, H0. eauto.
Qed.

Instance ctxRel_proper' A `{PartialOrder A}
  : Proper (poEq ==> poEq ==> impl) (@ctxRel A A (flip poLe)).
Proof.
  unfold Proper, respectful, impl; intros.
  destruct H2. split; eauto.
  rewrite <- H0, <- H1. eauto.
  intros. rewrite ctxmap_at_poEq; eauto.
  inv_get. rewrite <- H6. eauto.
Qed.


Lemma poLe_app X `{PartialOrder X} (L1 L2 : 〔X〕) (L1' L2' : 〔X〕)
  : poLe L1 L1' -> poLe L2 L2' -> poLe (L1 ++ L2) (L1' ++ L2').
Proof.
  intros. eapply PIR2_app; eauto.
Qed.

Lemma poEq_app X `{PartialOrder X} (L1 L2 : 〔X〕) (L1' L2' : 〔X〕)
  : poEq L1 L1' -> poEq L2 L2' -> poEq (L1 ++ L2) (L1' ++ L2').
Proof.
  intros. eapply PIR2_app; eauto.
Qed.

Hint Resolve poLe_app poEq_app.

Lemma poLe_app_proper X `{PartialOrder X}
  : Proper (poLe ==> poLe ==> poLe) (@List.app X).
Proof.
  unfold Proper, respectful; intros; eauto.
Qed.

Lemma poLe_app_proper_funny X `{PartialOrder X} L
  : Proper (flip poLe ==> flip poLe) (@List.app X L).
Proof.
  unfold Proper, respectful, flip; intros; eauto.
Qed.

Lemma poLe_app_proper' X `{PartialOrder X}
  : Proper (flip poLe ==> flip poLe ==> flip poLe) (@List.app X).
Proof.
  unfold Proper, respectful, flip; intros; eauto.
Qed.

Lemma poLe_app_proper_poEq X `{PartialOrder X}
  : Proper (poEq ==> poEq ==> poEq) (@List.app X).
Proof.
  unfold Proper, respectful; intros; eauto.
Qed.

Lemma reachability_monotone (ceval : op -> ؟ (withTop bool))
      (BL BL' : 〔bool〕) (s : stmt) (a : ann bool) p
  : poLe BL BL' ->
    reachability ceval p BL s a ->
    reachability ceval p BL' s a.
Proof.
  intros. general induction H0; eauto 10 using reachability.
  - inv_get. econstructor; eauto.
    cases; eauto.
Qed.

Instance reachability_mon_proper ceval p
  : Proper (poLe ==> eq ==> eq ==> impl) (reachability ceval p).
Proof.
  unfold Proper, respectful, impl; intros; subst.
  eapply reachability_monotone; eauto.
Qed.

Instance reachability_mon_proper' ceval p
  : Proper (flip poLe ==> eq ==> eq ==> flip impl) (reachability ceval p).
Proof.
  unfold Proper, respectful, impl, flip; intros; subst.
  eapply reachability_monotone; eauto.
Qed.


(*
Instance ctxRel_proper'' A `{PartialOrder A}
  : Proper (poEq ==> poLe ==> flip impl) (@ctxRel A A (flip poLe)).
Proof.
  unfold Proper, respectful, impl; intros. hnf; intros.
  destruct H2. split; eauto.
  rewrite H0, H1. eauto.
  intros. inv_get. eapply H3 in H5.
  rewrite H6.
  eapply sndR_poEq_proper_impl''; eauto. rewrite H6. reflexivity.
  rewrite H6.
Qed.
 *)

Instance forwardF_proper (sT:stmt) ZL F ST
  : Proper (poEq ==> poEq ==> poEq)
           (forwardF (@forward sT _ _ _ _ reachability_transform ZL) F ST).
Proof.
  unfold Proper, respectful.
  intros. eapply (@forwardF_ext sT (fun _ => bool)); eauto.
Qed.

Lemma labelsDefined_app' (A : Type)
      (L : 〔A〕) (L':ctxmap A) (k : nat) (t : stmt)
  : labelsDefined t (k + ctxmap_len L') -> ❬L❭ = k -> labelsDefined t (ctxmap_len (L +|+ L')).
Proof.
  intros. len_simpl. subst. eauto.
Qed.

Hint Resolve labelsDefined_app'.

Lemma ctxmap_drop_zero X (m:ctxmap X)
  : ctxmap_drop 0 m = m.
Proof.
  destruct m; unfold ctxmap_drop; simpl.
  orewrite (ctxmap_len - 0 = ctxmap_len). reflexivity.
Qed.

Instance tl_poEq_proper X `{PartialOrder X}
  : Proper (poEq ==> poEq) (@tl X).
Proof.
  unfold Proper, respectful; intros.
  inv H0; eauto.
Qed.

Instance tl_poLe_proper X `{PartialOrder X}
  : Proper (poLe ==> poLe) (@tl X).
Proof.
  unfold Proper, respectful; intros.
  inv H0; eauto.
Qed.


Unset Printing Records.
Lemma ctxmap_to_list_drop X `{LowerBounded X} (m:ctxmap X) k
  : ctxmap_to_list (ctxmap_drop k m) ≣ drop k (ctxmap_to_list m).
Proof.
  destruct m as [M l]; simpl.
  general induction l; simpl.
  - unfold ctxmap_to_list; simpl. rewrite drop_nil. reflexivity.
  -unfold ctxmap_drop. simpl ctxmap_len. simpl ctxmap_M.
   destruct k.
   + reflexivity.
   + simpl. pose proof (IHl X _ _ M k).
     unfold ctxmap_drop in H1. simpl in *. rewrite H1.
     unfold ctxmap_to_list. simpl.
     eapply poEq_drop.
     clear_all.
     generalize 0.
     intros. eapply PIR2_get; eauto with len.
     intros. inv_get.
     unfold ctxmap_at_def.
     unfold ctxmap_to_idx; simpl.
     repeat cases; eauto; try omega.
Qed.

Lemma getAnn_mapi_setTopAnn X f (L:list (ann X)) k
  :(getAnn ⊝ mapi_impl (fun i a  => setTopAnn a (f i)) k L)
   = (f ⊝ range k (length L)).
Proof.
  general induction L; simpl; eauto.
  f_equal.
  - rewrite getAnn_setTopAnn; eauto.
  - rewrite IHL. reflexivity.
Qed.

Definition ctxmap_at_def' X `{LowerBounded X} m n :=
  match
    MapInterface.find
      (ctxmap_to_idx m n)
      (ctxmap_M m)
  with
  | ⎣ x ⎦ => x
  | ⎣⎦ => ⊥
  end.

Lemma ctxmap_at_def_in_range X `{LowerBounded X} (m:ctxmap X) n
  : n <= ctxmap_len m -> ctxmap_at_def m ⊝ range 0 n = ctxmap_at_def' m ⊝ range 0 n.
Proof.
  intros.
  assert (0 + n <= ctxmap_len m). omega. revert H2; clear H1.
  generalize 0 as i; intros.
  general induction n; simpl; eauto.
  rewrite <- IHn; try omega. f_equal.
  unfold ctxmap_at_def, ctxmap_at_def'. cases; try omega. reflexivity.
Qed.

Lemma ctxmap_at_def_drop X `{LowerBounded X} (m:ctxmap X) n
  : n <= ctxmap_len m
    -> ctxmap_at_def (ctxmap_drop n m) ⊝ range 0 (ctxmap_len (ctxmap_drop n m))
      = ctxmap_at_def m ⊝ range n (ctxmap_len m - n).
Proof.
  intros.
  eapply map_ext_get_eq; eauto with len.
  intros. inv_get.
  unfold ctxmap_drop, ctxmap_at_def, ctxmap_to_idx; simpl.
  orewrite (ctxmap_len m - n - S n0 = ctxmap_len m - S (n + n0)).
  repeat cases; eauto; try omega.
Qed.

Lemma range_app i n k
  : range i n ++ range (i + n ) k = range i (n + k).
Proof.
  general induction n; simpl.
  - repeat f_equal; omega.
  - rewrite <- (IHn (S i) k); eauto. simpl. repeat f_equal. omega.
Qed.

Lemma ctxmap_to_list_app X `{LowerBounded X} (m:ctxmap X) n (Len:n <= ctxmap_len m)
  : ctxmap_at_def m ⊝ range 0 n ++
                  ctxmap_to_list (ctxmap_drop n m) =
    ctxmap_to_list m.
Proof.
  unfold ctxmap_to_list.
  rewrite ctxmap_at_def_drop; eauto.
  rewrite <- List.map_app.
  rewrite (range_app 0). repeat f_equal. omega.
Qed.

Definition reachability_sound sT ZL BL s a (ST:subTerm s sT) AL
  : poEq (fst (forward reachability_transform ZL s ST AL a)) a
    -> annotation s a
    -> labelsDefined s (ctxmap_len ZL)
    -> labelsDefined s (length BL)
    -> poLe (ctxmap_to_list (snd (@forward sT _ _ _ _ reachability_transform ZL s ST AL a))) BL
    -> ctxmap_len ZL = length BL
    -> reachability cop2bool Sound BL s a.
Proof.
  intros EQ Ann DefZL DefBL LE LEN.
  general induction Ann; simpl in *; inv DefZL; inv DefBL;
    repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *;
      repeat clear_trivial_eqs.
  - forward_setTopAnn_inv_snd.
    econstructor; eauto.
  - forward_setTopAnn_inv_snd.
    rewrite forward_ext in H;
      [| | eapply (@forward_setTopAnn_inv_snd sT (fun _ => bool) _ _ _); eauto|];
      try reflexivity; eauto.
    rewrite forward_ext in LE;
      [| | eapply (@forward_setTopAnn_inv_snd sT (fun _ => bool) _ _ _); eauto|];
      try reflexivity; eauto.
    econstructor; eauto with len.
    + rewrite H2. unfold cop2bool, op2bool. simpl.
      cases; eauto.
      monad_inv COND. rewrite EQ. intros. exfalso; eauto.
    + rewrite H0. unfold cop2bool, op2bool. simpl.
      cases; eauto.
      monad_inv COND. rewrite EQ. intros. exfalso; eauto.
    + rewrite <- (@forward_exp sT (fun _ => bool)) in LE; eauto.
  - Transparent poLe. hnf in LE.
    edestruct PIR2_nth; eauto using ListUpdateAt.list_update_at_get_3; dcr.
    eapply map_get_1. instantiate (2:=l).
    eapply get_range. reflexivity.
    len_simpl. eapply PIR2_length in LE. len_simpl. omega.
    econstructor; simpl; eauto. rewrite <- H1.
    eapply ctxmap_at_def_join. eapply PIR2_length in LE. len_simpl. omega.
  - econstructor.
  - eapply PIR2_get in H14; eauto; clear H13.
    change (PIR2 poEq) with (@poEq (list (ann bool)) _) in H14.
    set (FWt:=(forward reachability_transform (fst ⊝ s +|+ ZL)%ctxmap
                       t (subTerm_EQ_Fun1 eq_refl ST)
                       (ctxmap_extend AL ❬s❭) (setTopAnn ta a))) in *.
    set (FWF:=forwardF (forward reachability_transform (fst ⊝ s +|+ ZL)%ctxmap) s
                       (subTerm_EQ_Fun2 eq_refl ST) (snd FWt) sa) in *.
    assert (FWtEQ:FWt ≣ FWt) by reflexivity.
    unfold FWt in FWtEQ at 2. clearbody FWt.
    assert (FWFEQ:FWF ≣ FWF) by reflexivity.
    unfold FWF in FWFEQ at 2. clearbody FWF.
    forward_setTopAnn_inv_snd.
    econstructor; eauto.
    + eapply IHAnn; eauto.
      eapply labelsDefined_app'; eauto with len.
      erewrite (take_eta ❬s❭) at 1.
      eapply poLe_app; eauto.
      * rewrite <- H14.
        unfold mapi.
        rewrite getAnn_mapi_setTopAnn.
        unfold ctxmap_to_list. len_simpl.
        set (AA:=(snd
                    (forward reachability_transform (fst ⊝ s +|+ ZL) t
                             (subTerm_EQ_Fun1 eq_refl ST)
                             (ctxmap_extend AL ❬s❭) ta))).
        assert (poEq AA (snd FWt)). rewrite FWtEQ. reflexivity.
        rewrite take_range.
        assert (Len1:❬fst FWF❭ = ❬s❭). rewrite FWFEQ. len_simpl. reflexivity.
        rewrite Len1.
        rewrite min_l; try omega.
        eapply poLe_map_nd; intros.
        rewrite H7. rewrite FWFEQ.
        rewrite <- (@snd_forwardF_exp sT (fun _ => bool)). reflexivity.
      * rewrite <- LE.
        rewrite ctxmap_to_list_drop.
        eapply poLe_drop.
        rewrite FWFEQ.
        rewrite (@snd_forwardF_exp' sT (fun _ => bool)). reflexivity.
        intros. eapply (@forward_exp sT (fun _ => bool)); eauto.
        rewrite FWtEQ. reflexivity.
      * eauto with len.
    + intros.
      assert (n < ctxmap_len (snd FWt)). {
        rewrite FWtEQ. len_simpl.
        eapply Get.get_range in H7. omega.
      }
      eapply reachability_monotone. eapply poLe_app.
      rewrite <- H14. unfold mapi. rewrite getAnn_mapi_setTopAnn. reflexivity.
      eauto. eapply PIR2_nth_2 in H14; eauto; dcr; inv_get.
      pose proof (poEq_fst _ _ _ _ FWFEQ) as FWFEQ2.
      eapply PIR2_nth in FWFEQ2; eauto; dcr; inv_get.
      eapply (@forwardF_get sT (fun _ => bool)) in H14; eauto.
      destruct H14 as [? [? [? [? [? [? ]]]]]]; dcr.
      inv_get.
      eapply H1 with (ZL:=(fst ⊝ s +|+ ZL)%ctxmap); eauto.
      * rewrite <- H13 at 2. rewrite H15.
        eapply ann_R_setTopAnn_right; [|reflexivity].
        rewrite (@forward_getAnn' sT (fun _ => bool)).
        rewrite <- H13. rewrite getAnn_setTopAnn. reflexivity.
      * eauto with len.
      * len_simpl. rewrite <- LE in LEN. len_simpl.
        rewrite <- LEN.
        rewrite FWFEQ, FWtEQ. len_simpl. eauto.
      * assert (Len1: ❬fst FWF❭ = ❬s❭) by (rewrite FWFEQ; eauto with len).
        rewrite Len1. rewrite ctxmap_to_list_app.
        rewrite H14. rewrite FWFEQ. reflexivity.
        rewrite FWFEQ. len_simpl. rewrite FWtEQ; len_simpl. omega.
      * len_simpl. rewrite <- LE in LEN. len_simpl.
        rewrite <- LEN.
        rewrite FWFEQ, FWtEQ. len_simpl. eauto.
Qed.

Lemma impl_poLe (a b:bool)
  : (a -> b) <-> (poLe a b).
Proof.
  destruct a, b; simpl; firstorder.
Qed.

Lemma orb_poLe_struct a b c
  : a ⊑ c -> b ⊑ c -> a || b ⊑ c.
Proof.
  destruct a, b; simpl; eauto.
Qed.

Arguments join : simpl never.

Lemma forwardF_snd_poLe' sT ZL F ST n AL anF
      (IH:forall n Zs ST a AL k, get F n Zs -> get anF n a ->
                    ctxmap_at_def
                      (snd (forward reachability_transform ZL (snd Zs) ST AL a)) k
                      ⊑ (getAnn a ⊔ ctxmap_at_def AL k))
  : ctxmap_at_def
        (snd (forwardF (@forward sT (fun _ => bool) _ _ _ reachability_transform ZL) F ST AL anF)) n ⊑
        (fold_left join (getAnn ⊝ anF) (ctxmap_at_def AL n)).
Proof.
  intros.
  general induction F; destruct anF; simpl; eauto.
  - rewrite join_commutative.
    rewrite fold_left_join_start_swap. eauto.
  - rewrite IHF; eauto using get.
    eapply fold_left_join_struct; eauto.
    rewrite IH; eauto using get.
    rewrite join_commutative. eauto.
Qed.

Lemma fold_left_join_poLe X `{JoinSemiLattice X} A b c
  : (forall n a, get A n a -> a ⊑ c)
    -> b ⊑ c
    -> fold_left join A b ⊑ c.
Proof.
  intros. general induction A; simpl; eauto using get.
  exploit H1; eauto using get.
  eapply IHA; eauto using get.
  rewrite H2, H3; eauto. rewrite join_idempotent; eauto.
Qed.

Lemma forward_snd_poLe sT BL ZL s (ST:subTerm s sT) n a c AL b
  : reachability cop2bool Complete BL s a
    -> poLe (getAnn a) c
    -> poEq b (setTopAnn a c)
    -> ctxmap_at_def (snd (forward reachability_transform ZL s ST AL b)) n ⊑ join c (ctxmap_at_def AL n).
Proof.
  revert ZL AL BL ST n a b c.
  induction s using stmt_ind'; intros ZL AL BL ST n a b c RCH LE EQ;
    destruct a; invt reachability; invc EQ;
    simpl in *; repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; simpl in *;
      inv_get; clear_trivial_eqs;
      try solve [ destruct a; simpl; eauto | destruct b; simpl; eauto ].
  - rewrite IHs2; only 2: eapply H9; only 3: (rewrite H5; reflexivity).
    + rewrite IHs1;
        try eapply ann_R_setTopAnn_poEq; try eassumption; only 3: reflexivity.
      * rewrite <- H3. clear. repeat cases; eauto.
        destruct a; eauto.
      * cases; eauto.
        -- rewrite <- H10; eauto.
           eapply op2bool_cop2bool in COND. rewrite COND; eauto.
        -- rewrite H3, <- LE. eapply H6; eauto.
    + cases; eauto.
      * rewrite H11; eauto.
        rewrite op2bool_cop2bool in COND; eauto. rewrite COND; eauto.
      * rewrite H3. rewrite <- LE. eapply H7.
        eauto using op2bool_cop2bool_not_some.
  - decide (n < ctxmap_len AL).
    + destruct l. decide (n0 = n); subst.
      * rewrite ctxmap_at_def_join_at; eauto.
      * rewrite ctxmap_at_def_join_at_ne; eauto.
    + unfold ctxmap_at_def. len_simpl. cases; eauto; try omega.
  - rewrite ctxmap_at_def_drop_shift.
    rewrite forwardF_snd_poLe'.
    + eapply fold_left_join_poLe.
      * intros; inv_get. exploit H12; eauto. rewrite H4.
        exploit H11; eauto.
      * rewrite IHs; only 2: eauto; only 3: (rewrite H13; reflexivity).
        rewrite H3. rewrite ctxmap_at_def_extend_shift. reflexivity.
        rewrite H8. rewrite LE. eauto.
    + intros. inv_get.
      rewrite H. reflexivity. eauto. eapply H9; eauto.
      eapply H12 in H2; eauto. rewrite H2; eauto.
      eapply H12 in H2; eauto. rewrite H2; eauto.
      rewrite setTopAnn_eta. reflexivity. reflexivity.
Qed.

Lemma forwardF_snd_poLe sT ZL F ST n AL anF BL
      (IH:forall n Zs a, get F n Zs -> get anF n a ->
                            reachability cop2bool Complete BL (snd Zs) a)
  : ctxmap_at_def
      (snd (forwardF (@forward sT (fun _ => bool) _ _ _ reachability_transform ZL)
                     F ST AL anF)) n ⊑
        (fold_left join (getAnn ⊝ anF) (ctxmap_at_def AL n)).
Proof.
  intros.
  general induction F; destruct anF; simpl; eauto.
  - rewrite join_commutative.
    rewrite fold_left_join_start_swap. eauto.
  - rewrite IHF; eauto using get.
    eapply fold_left_join_struct; eauto.
    exploit IH; eauto using get.
    rewrite forward_snd_poLe;
      try (symmetry; eapply setTopAnn_eta_poEq); try reflexivity.
    rewrite join_commutative. eauto. eauto.
Qed.

Local Hint Extern 0 => first [ erewrite (@forward_getAnn' _ (fun _ => bool))
                            | erewrite getAnn_setTopAnn
                            | rewrite getAnn_setAnn ].

Transparent poLe.

(*
Lemma fold_left_forward_mono sT F t ZL als als' alt alt'
      (STF:forall n s, get F n s -> subTerm (snd s) sT)
      (ST:subTerm t sT)
  : length F = length als
    -> annotation t alt
    -> (forall n Zs a, get F n Zs -> get als n a -> annotation (snd Zs) a)
    -> poLe als als'
    -> poLe alt alt'
    -> poLe (fold_left
            (zip orb)
            (snd ⊝ forwardF (forward reachability_transform (fst ⊝ F ++ ZL)) F als STF)
            (snd (forward reachability_transform (fst ⊝ F ++ ZL)
                          t ST alt)))
         (fold_left
            (zip orb)
            (snd ⊝ forwardF (forward reachability_transform (fst ⊝ F ++ ZL)) F als' STF)
            (snd (forward reachability_transform (fst ⊝ F ++ ZL)
                          t ST alt'))).
Proof.
  intros LEN Ant AnF LE1 LE2.
  eapply fold_left_mono.
  - eapply poLe_map; eauto.
    eapply (@forwardF_monotone sT (fun _ => bool)); eauto.
  - eapply (@forward_monotone sT (fun _ => bool)); eauto.
Qed.
 *)

Lemma impl_impb (a b: bool)
  : (a -> b) -> impb a b.
Proof.
  destruct a, b; firstorder.
Qed.

Local Hint Extern 0 =>
match goal with
| [ H : op2bool ?e <> Some ?t , H' : op2bool ?e <> Some ?t -> _ |- _ ] =>
  specialize (H' H); subst
| [ H : op2bool ?e = Some true , H' : op2bool ?e <> Some false -> _ |- _ ] =>
  let H'' := fresh "H" in
  assert (H'':op2bool e <> Some false) by congruence;
    specialize (H' H''); subst
end.

Lemma reachability_analysis_complete_isCalledF' BL
      sT ZL F ST AL ans n
      (IH: forall k a Zs ST, get F k Zs ->
                      get ans k a ->
                      forall AL,
                        ctxmap_at_def (snd (forward (sT:=sT) reachability_transform ZL (snd Zs) ST AL a)) n
                        -> isCalled true (snd Zs) (LabI n) \/ ctxmap_at_def AL n)
      (RCH: forall k Zs a, get F k Zs -> get ans k a ->
                         reachability cop2bool Complete BL (snd Zs) a)
  : ctxmap_at_def (snd (forwardF (forward (sT:=sT) reachability_transform ZL) F ST AL ans)) n
    -> (exists k Zs a, get F k Zs /\ isCalled true (snd Zs) (LabI n) /\ get ans k a /\ getAnn a) \/ ctxmap_at_def AL n.
Proof.
  intros. general induction F; destruct ans; simpl in *; eauto.
  edestruct IHF as [[? [? [? [? [? [? ?]]]]]]|]; try eapply H; eauto 20 using get.
  - exploit IH; eauto using get.
    rewrite forward_snd_poLe in H0; only 4: (rewrite setTopAnn_eta; reflexivity);
      try reflexivity.
    decide (ctxmap_at_def AL n).
    destruct H1; eauto 20 using get. destruct (ctxmap_at_def AL n); isabsurd.
    destruct H1; isabsurd. rewrite join_false_right in *.
    eauto 20 using get. eauto 20 using get.
Qed.

Lemma callChain_step_right (isCalled: stmt -> lab -> Prop) F k Zs f g
  : get F k Zs
    -> isCalled (snd Zs) g
    -> callChain isCalled F f (LabI k)
    -> callChain isCalled F f g.
Proof.
  intros. destruct g.
  general induction H1; eauto using callChain.
Qed.

Lemma reachability_analysis_complete_isCalled
      sT BL ZL s (ST:subTerm s sT) n a c AL b
  : reachability cop2bool Complete BL s a
    -> poEq b (setTopAnn a c)
    -> poLe (getAnn a) c
    -> ctxmap_at_def (snd (forward reachability_transform ZL s ST AL b)) n
    -> isCalled true s (LabI n) \/ ctxmap_at_def AL n.
Proof.
  intros RCH EQ LE DEF.
  general induction RCH; simpl in *; invc EQ; eauto;
    repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *.
  - edestruct IHRCH; eauto using isCalled.
  - cases in DEF.
    + exploit H1; eauto.
      eapply op2bool_cop2bool in COND; rewrite COND; eauto.
      eapply IHRCH2 in DEF; only 2: (rewrite H9; reflexivity).
      * destruct DEF; eauto using isCalled.
        rewrite forward_snd_poLe in H4; eauto.
        instantiate (1:=false) in H4. rewrite H3 in *. right; eauto.
        rewrite H3, H8; reflexivity.
      * cases; try congruence.
        rewrite op2bool_cop2bool in COND. rewrite COND in *.
        rewrite H0; eauto. rewrite H7; eauto. intro. clear_trivial_eqs.
    + cases in DEF.
      * exploit H2; eauto.
        eapply op2bool_cop2bool in COND; rewrite COND; eauto.
        rewrite forward_snd_poLe in DEF; eauto.
        instantiate (1:=false) in DEF. rewrite H3 in *.
        eapply IHRCH1 in DEF; eauto using isCalled.
        destruct DEF; eauto. left. econstructor; eauto.
        rewrite H; eauto. rewrite H3, H9; eauto.
      * eapply IHRCH2 in DEF; only 2: (rewrite H9; reflexivity).
        -- destruct DEF; eauto using isCalled.
           eapply IHRCH1 in H3; eauto using isCalled.
           destruct H3; eauto. left. econstructor; eauto.
           rewrite H; eauto.
        -- rewrite H0; eauto. rewrite H7; eauto.
  - decide (labN l = n); subst; eauto using isCalled.
    + destruct l. left. econstructor.
    + right. rewrite ctxmap_at_def_join_at_ne in *; eauto.
  - rewrite ctxmap_at_def_drop_shift in DEF.
    eapply reachability_analysis_complete_isCalledF' in DEF.
    + destruct DEF as [[? [? [? [? [? [? ?]]]]]]|]; inv_get.
      * exploit H4; eauto.
        exploit H3; eauto. rewrite <- H11; eauto.
        left. destruct H15 as [? [? ?]].
        econstructor; eauto. simpl.
        eapply callChain_step_right; eauto.
        rewrite plus_comm; eauto.
      * eapply IHRCH in H5; try rewrite H12; eauto.
        rewrite ctxmap_at_def_extend_shift in H5; eauto.
        destruct H5; eauto.
        left. econstructor; eauto. simpl.
        rewrite plus_comm.
        econstructor 1.
    + intros. inv_get. eapply H2; try eapply H7; eauto.
      instantiate (1:=false). rewrite setTopAnn_eta; eauto.
      rewrite join_false_right; eauto.
    + intros; inv_get; eauto using get.
      assert (a0 = x). {
        rewrite <- ann_R_eq. change eq with (@poEq bool _).
        eapply H11; eauto.
      }
      subst.
      eapply H1; eauto.
Qed.

Lemma reachability_analysis_complete_isCalledF BL
      sT ZL F ST AL ans n
      (RCH: forall k Zs a, get F k Zs -> get ans k a ->
                         reachability cop2bool Complete BL (snd Zs) a)
  : ctxmap_at_def (snd (forwardF (forward (sT:=sT) reachability_transform ZL) F ST AL ans)) n
    -> (exists k Zs a, get F k Zs /\ isCalled true (snd Zs) (LabI n) /\ get ans k a /\ getAnn a) \/ ctxmap_at_def AL n.
Proof.
  intros.
  eapply reachability_analysis_complete_isCalledF'; eauto.
  intros.
  eapply reachability_analysis_complete_isCalled; try eapply H2; eauto.
  instantiate (1:=false). rewrite setTopAnn_eta; eauto.
  rewrite join_false_right; eauto.
Qed.


(*
Lemma reachability_analysis_complete_isCalled sT ZL BL s a b
      (ST:subTerm s sT)
  : reachability cop2bool Complete BL s a
    -> forall n, get (snd (forward reachability_transform ZL s ST (setTopAnn a b))) n true
           -> poLe (getAnn a) b
           -> isCalled true s (LabI n).
Proof.
  intros.
  general induction H; simpl in *;
    repeat let_case_eq; repeat simpl_pair_eqs; subst;
      simpl in *; eauto using isCalled.
  - inv_get. cases in H7; try congruence.
    + eapply forward_snd_poLe in H7; eauto; clear_trivial_eqs.
      * eapply IsCalledIf2; eauto.
        eapply IHreachability2; eauto.
        cases in H5; eauto.
        rewrite H0; eauto.
      * rewrite H3; eauto.
        rewrite op2bool_cop2bool in COND. rewrite COND. reflexivity.
    + cases in H5; try congruence.
      eapply forward_snd_poLe in H5; eauto; clear_trivial_eqs.
      * eapply IsCalledIf1; eauto.
        eapply IHreachability1; eauto.
        rewrite H; eauto.
      * rewrite H4; eauto.
        rewrite op2bool_cop2bool in COND. rewrite COND. reflexivity.
      * eapply orb_prop in EQ. destruct EQ; subst; isabsurd.
        -- eapply IsCalledIf1; eauto.
           eapply IHreachability1; eauto.
           rewrite H; eauto.
        -- eapply IsCalledIf2; eauto.
           eapply IHreachability2; eauto.
           rewrite H0; eauto.
  - decide (labN l = n); subst.
    + eapply ListUpdateAt.list_update_at_get_2 in H1; eauto; subst.
      destruct l; simpl. econstructor.
    + eapply ListUpdateAt.list_update_at_get_1 in H1; eauto; subst.
      inv_get.
  - exfalso. inv_get.
  - inv_get. rename H6 into Get.
    eapply fold_left_zip_orb_inv in Get.
    destruct Get as [Get|[? [? [GetFwd Get]]]]; dcr.
    + exploit forward_snd_poLe; try eapply Get; eauto.
      exploit IHreachability; eauto.
      eapply IsCalledLet; eauto.
      econstructor 1.
    + inv_get.
      exploit H2; eauto.
      rewrite <- (setTopAnn_eta x3 eq_refl) in Get.
      exploit forward_snd_poLe; try eapply Get; eauto.
      exploit H3; eauto; dcr.
      edestruct isCalledFrom_extend; eauto; dcr.
      econstructor; eauto.
Qed.
 *)

Lemma poLe_nth X `{PartialOrder X} (L : 〔X〕) (L' : 〔X〕) (n : nat) (x : X)
  : poLe L L'
    -> get L n x
    -> exists x', get L' n x' /\ poLe x x'.
Proof.
  intros. eapply PIR2_nth; eauto.
Qed.


Smpl Add match goal with
         | [ H : poLe ?L ?L', Get : get ?L ?n ?x |- _ ] =>
           match goal with
           | [ Get' : get L' n _ |- _ ] => fail 1
           | _ => edestruct (@poLe_nth _ _ L L' n x H Get) as [? [? ?]]
           end
         end : inv_trivial.

Lemma reachability_analysis_complete sT ZL BL BL' (Len:❬BL❭ = ❬BL'❭) s a (ST:subTerm s sT) b b' c AL
      (LDEF:labelsDefined s (ctxmap_len ZL))
      (EQ:(fst (forward reachability_transform ZL s ST AL (setTopAnn a b))) = c)
      (LE:poLe a (setTopAnn c b'))
      (LEb: poLe b b')
  : reachability cop2bool Complete BL s a
    -> reachability cop2bool Complete BL' s (setTopAnn c b').
Proof.
  subst c.
  intros RCH.
  general induction RCH; simpl in *; repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *; invt labelsDefined; try inv LE;
    clear_trivial_eqs;
    eauto using reachability, subTerm, reachability_sTA_inv,
    ann_R_setTopAnn_left.
  - econstructor. eapply reachability_sTA_inv.
    eapply IHRCH; eauto.
    rewrite setTopAnn_eta; eauto.
    repeat rewrite (@forward_getAnn' _ (fun _ => bool)). eauto.
  - econstructor; intros; simpl;
      repeat rewrite (@forward_getAnn' _ (fun _ => bool));
      repeat rewrite getAnn_setTopAnn; eauto.
    + cases; eauto.
    + cases; eauto.
    + eapply reachability_sTA_inv. eapply IHRCH1; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply reachability_sTA_inv. eapply IHRCH2; eauto.
      rewrite setTopAnn_eta; eauto.
    + intros. cases; eauto.
      exfalso.
      eapply op2bool_cop2bool_not_some in NOTCOND; eauto.
    + intros. cases; eauto.
      exfalso.
      eapply op2bool_cop2bool_not_some in NOTCOND; eauto.
  - inv_get. econstructor; eauto. simpl; eauto.
  - econstructor; eauto.
  - eapply PIR2_get in H15; eauto; clear H14.
    change (PIR2 poEq) with (@poEq (list (ann bool)) _) in H15.
    set (FWt:=(forward reachability_transform (fst ⊝ F +|+ ZL)%ctxmap
                       t (subTerm_EQ_Fun1 eq_refl ST)
                       (ctxmap_extend AL ❬F❭) (setTopAnn alt b0))) in *.
    set (FWF:=forwardF (forward reachability_transform (fst ⊝ F +|+ ZL)%ctxmap) F
                       (subTerm_EQ_Fun2 eq_refl ST) (snd FWt) als) in *.
    econstructor; simpl; repeat rewrite (@forward_getAnn' _ (fun _ => bool)).
    + eapply reachability_sTA_inv. eapply IHRCH; eauto.
      * eauto with len.
      * len_simpl. eauto.
      * rewrite setTopAnn_eta; eauto.
      * subst FWt; eauto.
    + subst FWF FWt. eauto with len.
    + subst FWt. eauto.
    + intros. inv_get.
      unfold mapi. rewrite getAnn_mapi_setTopAnn.
      subst FWF.
      edestruct (@forwardF_get sT (fun _ => bool) _ _ _ _ _ _ _ _ _ _ _ H6) as [? [? [? [? [? [? ]]]]]]; dcr;
        subst. protect H15. inv_get.
      rewrite <- (setTopAnn_eta x0 eq_refl).
      eapply H2; eauto.  len_simpl. omega. len_simpl. eauto.
      * unprotect H15. eapply PIR2_nth in H15; eauto; dcr. inv_get.
        etransitivity. eapply H14.
        eapply poLe_setTopAnn. reflexivity.
        rewrite setTopAnn_eta. reflexivity. eauto.
      * unprotect H15. eapply PIR2_nth in H15; eauto; dcr. inv_get.
        rewrite H14. rewrite getAnn_setTopAnn. reflexivity.
    + intros. inv_get. rewrite getAnn_setTopAnn in *.
      subst FWF.
      edestruct (@forwardF_get sT (fun _ => bool) _ _ _ _ _ _ _ _ _ _ _ H5) as [? [? [? [? [? [? ]]]]]];
        eauto; dcr. subst.
      eapply reachability_analysis_complete_isCalledF in H6; eauto.
      destruct H6.
      * destruct H6 as [? [? [? [? [? [? ?]]]]]].
        exploit H4; eauto.
        eapply isCalledFrom_extend; eauto.
      * subst FWt.
        eapply reachability_analysis_complete_isCalled in H6; try reflexivity; eauto.
        -- destruct H6.
           ++ econstructor; eauto using callChain.
           ++ rewrite ctxmap_at_def_extend_at in H6; eauto using Get.get_range.
        -- rewrite H16. eauto.
    + intros. inv_get. rewrite getAnn_setTopAnn.
      eapply PIR2_nth_2 in H15; eauto using mapi_get_1; dcr; simpl in *.
      eapply ann_R_get in H10. rewrite getAnn_setTopAnn in H10.
      exploit H4; eauto.
      assert (snd FWt ⊑ snd FWF). {
        subst FWt FWF.
        eapply (@snd_forwardF_exp sT (fun _ => bool)).
      }
      subst FWF.
      rewrite forwardF_snd_poLe; eauto.
      eapply fold_left_join_poLe.
      * intros; inv_get. exploit H4; eauto.
      * subst FWt. rewrite forward_snd_poLe; only 4: reflexivity; eauto.
        rewrite LEb.
        rewrite ctxmap_at_def_extend_at. rewrite bottom_least.
        rewrite join_idempotent; eauto.
        inv_get. eapply Get.get_range in H13. eauto.
        rewrite H16.
        rewrite (@forward_getAnn' _ (fun _ => bool)). rewrite getAnn_setTopAnn. eauto.
Qed.

Lemma reachability_complete_bottom BL s
  : labelsDefined s ❬BL❭
    -> reachability cop2bool Complete BL s (setAnn bottom s).
Proof.
  revert BL.
  sind s; intros; destruct s; invt labelsDefined; simpl; eauto 10 using reachability.
  - edestruct get_in_range; eauto.
    econstructor; simpl; eauto.
  - econstructor; simpl; eauto with len.
    + intros; inv_get; eauto.
      eapply IH; eauto. rewrite app_length, !map_length. eauto.
    + intros; inv_get; eauto.
      unfold comp in H1. rewrite getAnn_setAnn in H1. intuition.
    + intros; inv_get; eauto.
      unfold comp. eauto.
Qed.

Lemma reachability_complete_initial BL s
  : labelsDefined s ❬BL❭
    -> reachability cop2bool Complete BL s (setTopAnn (setAnn bottom s) true).
Proof.
  revert BL. Opaque bottom.
  intros.
  destruct s; inv H; simpl setAnn; simpl setTopAnn;
    try now (econstructor; eauto using reachability_complete_bottom;
             try rewrite getAnn_setAnn; simpl; eauto).
  - edestruct get_in_range; eauto.
    econstructor; simpl; eauto.
  - econstructor; simpl; eauto using reachability_complete_bottom with len.
    + intros; inv_get; eauto.
      eapply reachability_complete_bottom; eauto.
      len_simpl; eauto.
    + intros; inv_get; eauto.
      unfold comp in H1. rewrite getAnn_setAnn in H1. intuition.
    + intros; inv_get; eauto.
      unfold comp. eauto.
Qed.

Lemma reachability_complete s
  : labelsDefined s ❬nil:list params❭
    -> reachability cop2bool Complete nil s (reachabilityAnalysis s).
Proof.
  unfold reachabilityAnalysis. destr_sig.
  destruct e as [n [Iter _]]. subst.
  intros. eapply safeFixpoint_induction.
  - unfold initial_value. simpl.
    eapply reachability_complete_initial; eauto.
  - intros. rewrite <- (setTopAnn_eta _ eq_refl).
    eapply (@reachability_analysis_complete s (ctxmap_emp _)); eauto.
    + rewrite setTopAnn_eta; reflexivity.
    + simpl. erewrite !(setTopAnn_eta _ eq_refl); eauto.
    + simpl. rewrite (@forward_getAnn' s (fun _ => bool)); eauto.
Qed.

Lemma correct s
  : labelsDefined s 0
    -> reachability cop2bool SoundAndComplete nil s (reachabilityAnalysis s).
Proof.
  intros.
  eapply reachability_sound_and_complete.
  - eapply reachability_complete; eauto.
  - unfold reachabilityAnalysis.
    destr_sig. destr_sig. dcr.
    eapply (@reachability_sound s (ctxmap_emp _)); simpl; eauto.
    + eapply H2.
    + assert (ctxmap_len (snd (forward reachability_transform (ctxmap_emp _) s (subTerm_refl s) (ctxmap_emp _) x)) = 0). {
        rewrite (@forward_length _ (fun _ => bool)); eauto.
      }
      destruct (snd (forward reachability_transform (ctxmap_emp _) s (subTerm_refl s) (ctxmap_emp _) x)); isabsurd.
      destruct ctxmap_len; isabsurd. reflexivity.
Qed.

Lemma reachabilityAnalysis_getAnn s
  : getAnn (ReachabilityAnalysis.reachabilityAnalysis s).
Proof.
  unfold reachabilityAnalysis. destr_sig.
  destruct e as [n [Iter _]]. subst.
  intros. eapply safeFixpoint_induction.
  - simpl. rewrite getAnn_setTopAnn; eauto.
  - intros. simpl.
    rewrite (@forward_getAnn' s (fun _ => bool)); eauto.
Qed.