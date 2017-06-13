Require Import CSet Le ListUpdateAt Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Terminating ContextMap.
Require Import Val Var Env IL Annotation AnnotationLattice.
Require Import Infra.Lattice DecSolve LengthEq MoreList Status AllInRel OptionR.
Require Import Keep Subterm Analysis.
Require Import FiniteFixpointIteration.

Set Implicit Arguments.

Definition forwardF (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)}
           (forward: ctxmap (Dom sT) -> forall s (ST:subTerm s sT)
                      (a:ann (Dom sT)), ann (Dom sT) * ctxmap (Dom sT))
           (AL:ctxmap (Dom sT))
           (F:list (params * stmt)) (anF:list (ann (Dom sT)))
           (ST:forall n s, get F n s -> subTerm (snd s) sT)
  : list (ann (Dom sT)) * ctxmap (Dom sT).
  revert AL F anF ST.
  fix g 2. intros.
  destruct F as [|Zs F'].
  - eapply (nil, AL).
  - destruct anF as [|a anF'].
    + eapply (nil, AL).
    + pose proof (forward AL (snd Zs) (ST 0 Zs ltac:(eauto using get)) a).
      pose proof (g (snd X) F' anF' ltac:(eauto using get)).
      eapply (fst X :: fst X0, snd X0).
Defined.

Arguments forwardF [sT] [Dom] {H} {H0} forward AL F anF ST.

Fixpoint forwardF_length (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)} forward AL
           (F:list (params * stmt)) (anF:list (ann (Dom sT)))
           (ST:forall n s, get F n s -> subTerm (snd s) sT) {struct F}
  : length (fst (forwardF forward AL F anF ST)) = min (length F) (length anF).
Proof.
  destruct F as [|Zs F'], anF; simpl; eauto.
Qed.

Smpl Add
     match goal with
     | [ |- context [ ❬fst (@forwardF ?sT ?Dom ?H ?BSL ?f ?AL ?F ?anF ?ST)❭ ] ] =>
       rewrite (@forwardF_length sT Dom H BSL f AL F anF ST)
     | [ H : context [ ❬fst (@forwardF ?sT ?Dom ?H ?BSL ?f ?AL ?F ?anF ?ST)❭ ] |- _ ] =>
       rewrite (@forwardF_length sT Dom H BSL f AL F anF ST) in H
     end : len.

Lemma forwardF_length_ass (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)}
      forward AL F anF ST k
  : length F = k
    -> length F = length anF
    -> length (fst (forwardF forward AL F anF ST)) = k.
Proof.
  intros. rewrite forwardF_length, <- H2.
  repeat rewrite Nat.min_idempotent; eauto.
Qed.

Hint Resolve @forwardF_length_ass : len.



Fixpoint forward (sT:stmt) (Dom: stmt -> Type)
         `{JoinSemiLattice (Dom sT)}
         `{@LowerBounded (Dom sT) H}
           (ftransform :
              forall sT, ctxmap params ->
                    forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
           (ZL:ctxmap params) (AL:ctxmap (Dom sT))
           (st:stmt) (ST:subTerm st sT) (a:ann (Dom sT)) {struct st}
  :  ann (Dom sT) * ctxmap (Dom sT)
  := match st as st', a return st = st' -> ann (Dom sT) * ctxmap (Dom sT) with
    | stmtLet x e s as st, ann1 d ans =>
      fun EQ =>
        let d' := getAnni d (ftransform sT ZL st ST d) in
        let (ans', AL) := forward Dom ftransform ZL AL (subTerm_EQ_Let EQ ST)
                                 (setTopAnn ans d') in
        (ann1 d ans', AL)

    | stmtIf x s t, ann2 d ans ant =>
      fun EQ =>
        let an := ftransform sT ZL st ST d in
        let d1 := (getAnniLeft d an) in
        let d2 := (getAnniRight d an) in
        let (ans', AL') := forward Dom ftransform ZL AL (subTerm_EQ_If1 EQ ST)
                                  (setTopAnn ans d1) in
        let (ant', AL'') := forward Dom ftransform ZL AL' (subTerm_EQ_If2 EQ ST)
                                  (setTopAnn ant d2) in
        (ann2 d ans' ant', AL'')

    | stmtApp f Y as st, ann0 d as an =>
      fun EQ =>
        let an := ftransform sT ZL st ST d in
        (ann0 d, ctxmap_join_at AL (counted f) (getAnni d an))

    | stmtReturn x as st, ann0 d as an =>
      fun EQ => (ann0 d, AL)

    | stmtFun F t as st, annF d anF ant =>
      fun EQ =>
        let ZL' := ctxmap_app ZL (List.map fst F) in
        let AL' := ctxmap_extend AL (length F) in
        let (ant', ALt) := forward Dom ftransform ZL' AL' (subTerm_EQ_Fun1 EQ ST)
                                  (setTopAnn ant d) in
        let (anF', AL'') := forwardF (forward Dom ftransform ZL') AL' F anF
                                   (subTerm_EQ_Fun2 EQ ST) in
        (annF d (MoreList.mapi (fun i a => setTopAnnO a (ctxmap_at AL'' i)) anF') ant',
         ctxmap_drop ❬F❭ AL'')
    | _, an => fun EQ => (an, AL)
  end eq_refl.

(*
Lemma forwardF_get  (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)}
      forward
           (F:list (params * stmt)) (anF:list (ann (Dom sT))) AL
           (ST:forall n s, get F n s -> subTerm (snd s) sT) aa n
           (GetBW:get (fst (forwardF forward AL F anF ST)) n aa)
      :
        { Zs : params * stmt & {GetF : get F n Zs &
        { a : ann (Dom sT) & { getAnF : get anF n a &
        { ST' : subTerm (snd Zs) sT | aa = fst (forward AL (snd Zs) ST' a)
        } } } } }.
Proof.
  eapply get_getT in GetBW.
  general induction anF; destruct F as [|[Z s] F']; inv GetBW.
  - exists (Z, s). simpl. do 4 (eexists; eauto 20 using get).
  - edestruct IHanF as [Zs [? [? [? ]]]]; eauto; dcr; subst.
    exists Zs. do 4 (eexists; eauto 20 using get).
Qed.

Lemma get_forwardF  (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)}
           (forward: forall s (ST:subTerm s sT) (a:ann (Dom sT)),
                       ann (Dom sT) * list (Dom sT))
           (F:list (params * stmt)) (anF:list (ann (Dom sT)))
           (ST:forall n s, get F n s -> subTerm (snd s) sT) n Zs a
  :get F n Zs
   -> get anF n a
   -> { ST' | get (forwardF forward F anF ST) n (forward (snd Zs) ST' a) }.
Proof.
  intros GetF GetAnF.
  eapply get_getT in GetF.
  eapply get_getT in GetAnF.
  general induction GetAnF; destruct Zs as [Z s]; inv GetF; simpl.
  - eexists; econstructor.
  - edestruct IHGetAnF; eauto using get.
Qed.


Ltac inv_get_step_analysis_forward :=
  match goal with
  | [ H: get (@forwardF ?sT ?Dom ?PO ?BSL ?f ?F ?anF ?ST) ?n ?x |- _ ]
    => eapply (@forwardF_get sT Dom PO BSL f F anF ST x n) in H;
      destruct H as [? [? [? [? [? ]]]]]
  end.

Smpl Add inv_get_step_analysis_forward : inv_get.
 *)


Lemma forwardF_monotone' (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)}
      (forward:ctxmap (Dom sT) -> forall s (ST:subTerm s sT) (a:ann (Dom sT)),
                 ann (Dom sT) * ctxmap (Dom sT))
      F
      (forward_mon: forall AL AL', poLe AL AL' -> forall n Zs, get F n Zs -> forall (ST:subTerm (snd Zs) sT),
          forall (a b : ann (Dom sT)), a ⊑ b ->
                                  forward AL _ ST a ⊑ forward AL' _ ST b)
  : forall AL AL', poLe AL AL' -> forall ST,
    forall anF bnF, anF ⊑ bnF ->
               forwardF forward AL F anF ST ⊑ forwardF forward AL' F bnF ST.
Proof.
  intros. general induction H2; destruct F; simpl; eauto 20 using get.
Qed.

Lemma snd_forwardF_exp' (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)}
      (forward:ctxmap (Dom sT) -> forall s (ST:subTerm s sT) (a:ann (Dom sT)),
                 ann (Dom sT) * ctxmap (Dom sT))
      F
      (forward_mon: forall AL AL' n Zs, get F n Zs -> forall (ST:subTerm (snd Zs) sT),
          forall (a : ann (Dom sT)), AL ⊑ AL' -> AL ⊑ snd (forward AL' _ ST a))
  : forall AL AL' ST anF, AL ⊑ AL' -> AL ⊑ snd (forwardF forward AL' F anF ST).
Proof.
  intros. general induction anF; destruct F; simpl; eauto using get.
Qed.

Lemma forwardF_ext' (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)}
      (forward:ctxmap (Dom sT) -> forall s (ST:subTerm s sT) (a:ann (Dom sT)),
           ann (Dom sT) * ctxmap (Dom sT))
      F
      (forward_mon: forall AL AL', AL ≣ AL' -> forall n Zs, get F n Zs -> forall (ST:subTerm (snd Zs) sT),
              forall (a b : ann (Dom sT)), a ≣ b ->
                                      forward AL _ ST a ≣ forward AL' _ ST b)
  : forall AL AL', AL ≣ AL' -> forall ST,
    forall anF bnF, anF ≣ bnF ->
               forwardF forward AL F anF ST ≣ forwardF forward AL' F bnF ST.
Proof.
  intros. general induction H2; destruct F; simpl; eauto 20 using get.
Qed.

(*
Lemma forward_length (sT:stmt) (Dom : stmt -> Type) `{JoinSemiLattice (Dom sT)}
      `{@LowerBounded (Dom sT) H}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params),
    forall (a : ann (Dom sT)), ❬snd (forward Dom f ZL ST a)❭ = ❬ZL❭.
Proof.
  sind s; destruct s; destruct a; simpl; eauto with len;
    repeat let_pair_case_eq; subst; simpl in *; eauto.
  - rewrite zip_length2; eauto. rewrite IH; eauto; symmetry; eauto.
  - rewrite list_update_at_length; eauto with len.
  - rewrite length_drop_minus.
    rewrite fold_list_length'.
    + rewrite IH; eauto. rewrite app_length, map_length. omega.
    + intros. inv_get. repeat rewrite IH; eauto.
    + intros. rewrite zip_length; eauto.
      eapply min_l; eauto.
Qed.



Smpl Add
     match goal with
     | [ |- context [ ❬snd (@forward ?sT ?Dom ?H ?BSL ?LB ?f ?ZL ?s ?ST ?a)❭ ] ] =>
       rewrite (@forward_length sT Dom H BSL LB f s ST ZL a)
     end : len.

Lemma forward_length_ass
      (sT:stmt) (Dom : stmt -> Type) `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) k,
    forall (a : ann (Dom sT)), ❬ZL❭ = k -> ❬snd (forward Dom f ZL ST a)❭ = k.
Proof.
  intros. rewrite forward_length; eauto.
Qed.

Lemma forward_length_le_ass
      (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) k,
    forall (a : ann (Dom sT)), ❬ZL❭ <= k -> ❬snd (forward Dom f ZL ST a)❭ <= k.
Proof.
  intros. rewrite forward_length; eauto.
Qed.

Lemma forward_length_le_ass_right
      (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) k,
    forall (a : ann (Dom sT)), k <= ❬ZL❭ -> k <= ❬snd (forward Dom f ZL ST a)❭.
Proof.
  intros. rewrite forward_length; eauto.
Qed.


Hint Resolve @forward_length_ass forward_length_le_ass forward_length_le_ass_right : len.
 *)

Lemma forwardF_ann  (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)}
      (forward:ctxmap (Dom sT) -> forall s (ST:subTerm s sT) (a:ann (Dom sT)),
           ann (Dom sT) * ctxmap (Dom sT))
           (F:list (params * stmt)) (anF:list (ann (Dom sT))) AL
           (ST:forall n s, get F n s -> subTerm (snd s) sT) aa n
           (GetBW:get (fst (forwardF forward AL F anF ST)) n aa) Zs
           (Get: get F n Zs)
           (IH: forall AL Zs ST  a, get F n Zs -> get anF n a ->
                             annotation (snd Zs) (fst (forward AL (snd Zs) ST a)))
      : annotation (snd Zs) aa.
Proof.
  eapply get_getT in GetBW.
  general induction anF; destruct F as [|[Z s] F']; inv GetBW.
  - inv_get. simpl. exploit IH; eauto using get.
  - eapply IHanF; eauto using get.
Qed.

Lemma forward_annotation sT (Dom:stmt->Type)
      `{JoinSemiLattice (Dom sT)} s `{@LowerBounded (Dom sT) H}
      (f: forall sT, ctxmap params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
  : forall AL ZL a (ST:subTerm s sT), annotation s a
               -> annotation s (fst (forward Dom f AL ZL ST a)).
Proof.
  induction s using stmt_ind'; intros AL ZL a ST Ann; inv Ann; simpl;
    repeat let_pair_case_eq; subst; eauto 20 using @annotation, setTopAnn_annotation.
  - econstructor; eauto using setTopAnn_annotation.
    + len_simpl; eauto.
    + intros. inv_get.
      eapply forwardF_ann in H3; eauto.
      * eauto using setTopAnnO_annotation, setAnn_annotation.
Qed.

Lemma forward_getAnn' (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, ctxmap params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT)) s (ST:subTerm s sT) ZL AL an
  : getAnn (fst (@forward sT Dom _ _ _ f AL ZL s ST an)) = getAnn an.
Proof.
  intros. destruct s, an; simpl in *; eauto;
  repeat let_pair_case_eq; simpl; eauto.
Qed.

(*
Lemma forward_getAnn (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT)) s (ST:subTerm s sT) ZL a an
  : ann_R eq (fst (@forward sT Dom _ _ _ f ZL s ST an)) an
    -> getAnn an = a.
Proof.
  intros. eapply ann_R_get in H2.
  rewrite forward_getAnn' in H2. eauto.
Qed.
 *)

(*
Ltac simpl_forward_setTopAnn :=
  repeat match goal with
         | [H : poEq (fst (forward ?reachability_transform ?ZL
                                       ?s ?ST ?a ?sa)) ?sa |- _ ] =>
           let X := fresh "H" in
           match goal with
           | [ H' : getAnn sa = a |- _ ] => fail 1
           | _ => exploit (forward_getAnn _ _ _ _ _ H) as X
           end
         end; subst; try eassumption.

Smpl Add 130
    match goal with
    | [H : poEq (fst (forward ?reachability_transform ?ZL
                              ?s ?ST ?a ?sa)) ?sa |- _ ] =>
      let X := fresh "H" in
      match goal with
      | [ H' : getAnn sa = a |- _ ] => fail 1
      | _ =>
        first [ unify a (getAnn sa); fail 1
              | exploit (forward_getAnn _ _ _ _ _ H) as X; subst ]
      end
    end : inv_trivial.
 *)


Ltac fold_po :=
  repeat match goal with
         | [ H : context [ @ann_R ?A ?A (@poLe ?A ?I) ] |- _ ] =>
           change (@ann_R A A (@poLe A I)) with (@poLe (@ann A) _) in H
         | [ H : context [ PIR2 poLe ?x ?y ] |- _ ] =>
           change (PIR2 poLe x y) with (poLe x y) in H
         | [ |- context [ ann_R poLe ?x ?y ] ] =>
           change (ann_R poLe x y) with (poLe x y)
  end.

Ltac PI_simpl :=
  match goal with
    [ H : subTerm ?s ?t, H' : subTerm ?s ?t |- _ ]
    => assert (H = H') by eapply subTerm_PI; try subst H'; try subst H
  end.


Lemma poLe_mapi D `{PartialOrder D} D' `{PartialOrder D'} (f g:nat -> D -> D') (L L':list D)
      (LEf:forall i a b, poLe a b -> poLe (f i a) (g i b))
      (LE: poLe L L') n
  : poLe (mapi_impl f n L) (mapi_impl g n L').
Proof.
  general induction LE; simpl; eauto.
Qed.

Lemma poEq_mapi D `{PartialOrder D} D' `{PartialOrder D'} (f g:nat -> D -> D') (L L':list D)
      (LEf:forall i a b, poEq a b -> poEq (f i a) (g i b))
      (LE: poEq L L') n
  : poEq (mapi_impl f n L) (mapi_impl g n L').
Proof.
  general induction LE; simpl; eauto.
Qed.

Lemma forward_monotone (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, ctxmap params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
      (fMon:forall s (ST:subTerm s sT) ZL,
          forall a b, a ⊑ b -> f sT ZL s ST a ⊑ f sT ZL s ST b)
  : forall (s : stmt) (ST:subTerm s sT) ZL,
    forall AL AL', poLe AL AL' ->
        forall (a b : ann (Dom sT)), a ⊑ b ->
                                forward Dom f ZL AL ST a ⊑ forward Dom f ZL AL' ST b.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  induction s using stmt_ind'; intros ST ZL AL AL' ALLE a b LE; simpl forward; inv LE;
    simpl forward; repeat let_pair_case_eq; subst; eauto.
  - eauto 100.
  - eauto 100.
  - clear_trivial_eqs. eapply PIR2_get in H5; eauto.
    eapply poLe_struct; eauto.
    + eapply annF_poLe; eauto.
      * eapply poLe_mapi; eauto using forwardF_monotone'.
        intros. eapply ann_R_setTopAnnO_poLe; eauto using forwardF_monotone'.
        eapply ctxmap_at_poLe.
        eapply forwardF_monotone'; eauto.
    + eapply ctxmap_drop_poLe.
      eapply forwardF_monotone'; eauto.
Qed.

Lemma forward_exp (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, ctxmap params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
      (fMon:forall s (ST:subTerm s sT) ZL,
          forall a b, a ⊑ b -> f sT ZL s ST a ⊑ f sT ZL s ST b)
  : forall (s : stmt) (ST:subTerm s sT) ZL,
    forall AL AL', poLe AL AL' ->
        forall a, AL ⊑ snd (forward Dom f ZL AL' ST a).
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  induction s using stmt_ind'; intros ST ZL AL AL' ALLE a; destruct a; simpl forward;
    simpl forward; repeat let_pair_case_eq; subst; eauto.
  - simpl. admit.
  - simpl. etransitivity; eauto.
    eapply poLe_struct; eauto.
    + eapply annF_poLe; eauto.
      * eapply poLe_mapi; eauto using forwardF_monotone'.
        intros. eapply ann_R_setTopAnnO_poLe; eauto using forwardF_monotone'.
        eapply ctxmap_at_poLe.
        eapply forwardF_monotone'; eauto.
    + eapply ctxmap_drop_poLe.
      eapply forwardF_monotone'; eauto.
Qed.

Hint Resolve ann_R_setTopAnn_poEq.

Lemma forwardF_monotone (sT:stmt) (Dom : stmt -> Type)
      `{PartialOrder (Dom sT)}
      `{@JoinSemiLattice (Dom sT) H} `{@LowerBounded (Dom sT) H}
      (f: forall sT, ctxmap params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
      (fMon:forall s (ST:subTerm s sT) ZL,
          forall a b, a ⊑ b -> f sT ZL s ST a ⊑ f sT ZL s ST b)
      F
  : forall AL AL', poLe AL AL' -> forall ST ZL,
    forall anF bnF, anF ⊑ bnF ->
               forwardF (@forward sT Dom _ _ _ f ZL) AL F anF ST
                        ⊑ forwardF (@forward sT Dom _ _ _ f ZL) AL' F bnF ST.
Proof.
  intros.
  general induction H3; destruct F; simpl; eauto 20 using get, forward_monotone.
Qed.

Lemma forward_ext (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, ctxmap params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
      (fMon:forall s (ST:subTerm s sT) ZL,
          forall a b, a ≣ b -> f sT ZL s ST a ≣ f sT ZL s ST b)
  : forall (s : stmt) (ST:subTerm s sT) ZL,
    forall AL AL', poEq AL AL' ->
    forall (a b : ann (Dom sT)), a ≣ b ->
                            forward Dom f ZL AL ST a ≣ forward Dom f ZL AL' ST b.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  induction s using stmt_ind'; intros ST ZL AL AL' ALLE a b LE; simpl forward; inv LE;
    simpl forward; repeat let_pair_case_eq; subst; eauto.
  - eauto 100.
  - eauto 100.
  - clear_trivial_eqs. eapply PIR2_get in H5; eauto.
    eapply poEq_struct; eauto.
    + eapply annF_poEq; eauto.
      * eapply poEq_mapi; eauto using forwardF_ext'.
        intros. eapply ann_R_setTopAnnO_poEq; eauto using forwardF_monotone'.
        eapply ctxmap_at_poEq.
        eapply forwardF_ext'; eauto.
    + eapply ctxmap_drop_poEq.
      eapply forwardF_ext'; eauto.
Qed.

Instance makeForwardAnalysis (Dom:stmt -> Type)
         (PO:forall s, PartialOrder (Dom s))
         (BSL:forall s, JoinSemiLattice (Dom s))
         (LB:forall s, @LowerBounded (Dom s) (PO s))
         (f: forall sT, ctxmap params ->
                   forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
         (fMon:forall sT s (ST:subTerm s sT) ZL,
             forall a b, a ⊑ b -> f sT ZL s ST a ⊑ f sT ZL s ST b)
         (Trm: forall s, Terminating (Dom s) poLt)

  : forall s (i:Dom s), Iteration { a : ann (Dom s) | annotation s a } :=
  {
    step := fun X : {a : ann (Dom s) | annotation s a} =>
                      exist (fun a0 : ann (Dom s) => annotation s a0)
                            (fst (forward Dom f (ctxmap_emp _) (ctxmap_emp _)
                                          (subTerm_refl _) (proj1_sig X)))
                                 (forward_annotation Dom f (ctxmap_emp _) (ctxmap_emp _) (subTerm_refl _) _);
    initial_value :=
      exist (fun a : ann (Dom s) => annotation s a)
            (setTopAnn (setAnn bottom s) i)
            (setTopAnn_annotation _ (setAnn_annotation bottom s))
  }.
Proof.
  - destruct X; eauto.
  - eapply ann_R_setTopAnn_left.
    + simpl. rewrite forward_getAnn'. rewrite getAnn_setTopAnn. reflexivity.
    + eapply ann_bottom.
      eapply forward_annotation; eauto.
      eapply setTopAnn_annotation.
      eapply setAnn_annotation.
  - intros [a Ann] [b Bnn] LE; simpl in *.
    eapply (forward_monotone Dom f (fMon s)); eauto.
Defined.
