Require Import CSet Le ListUpdateAt Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Terminating MoreInversion.
Require Import Val Var Env IL Annotation Infra.Lattice.
Require Import DecSolve LengthEq MoreList Status AllInRel OptionR.
Require Import Keep Subterm Analysis.

Set Implicit Arguments.


Definition anni A (s:stmt) : Type :=
  match s with
  | stmtIf _ _ _ => option A * option A
  | _ => A
  end.

Definition forwardF (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)}
           (forward: forall s (ST:subTerm s sT) (d:Dom sT),
                      Dom sT)
           (F:list (params * stmt)) (a:Dom sT)
           (ST:forall n s, get F n s -> subTerm (snd s) sT)
  : list (Dom sT).
  revert F ST.
  fix g 1. intros.
  destruct F as [|Zs F'].
  - eapply nil.
  - econstructor 2.
    + refine (forward (snd Zs) _ a).
      eapply (ST 0 Zs); eauto using get.
    + eapply (g F').
      eauto using get.
Defined.

Arguments forwardF [sT] [Dom] {H} {H0} forward F a ST.

Fixpoint forwardF_length (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)} forward
           (F:list (params * stmt)) a
           (ST:forall n s, get F n s -> subTerm (snd s) sT) {struct F}
  : length (forwardF forward F a ST) = length F.
Proof.
  destruct F as [|Zs F']; simpl; eauto.
Qed.

Smpl Add
     match goal with
     | [ |- context [ ❬@forwardF ?sT ?Dom ?H ?BSL ?f ?F ?a ?ST❭ ] ] =>
       rewrite (@forwardF_length sT Dom H BSL f F a ST)
     | [ H : context [ ❬@forwardF ?sT ?Dom ?H ?BSL ?f ?F ?a ?ST❭ ] |- _ ] =>
       rewrite (@forwardF_length sT Dom H BSL f F a ST) in H
     end : len.

Lemma forwardF_length_ass (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)}
      forward F a ST k
  : length F = k
    -> length (forwardF forward F a ST) = k.
Proof.
  intros. rewrite forwardF_length, <- H1.
  repeat rewrite Nat.min_idempotent; eauto.
Qed.

Hint Resolve @forwardF_length_ass : len.

Lemma anni_let A
      (st : stmt) (x : nat) (e : exp) (s : stmt)
      (EQ:st = stmtLet x e s) (d:anni A st) : A.
Proof.
  rewrite EQ in d. simpl in *. eauto.
Defined.

Lemma anni_if A
      (st : stmt) (e : op) (s t : stmt)
      (EQ:st = stmtIf e s t) (d:anni A st) : option A * option A.
Proof.
  rewrite EQ in d. simpl in *. eauto.
Defined.

Lemma anni_app A (st : stmt) f Y
      (EQ:st = stmtApp f Y) (d:anni A st) : A.
Proof.
  rewrite EQ in d. simpl in *. eauto.
Defined.

Arguments anni_if {A} {st} {e} {s} {t} EQ d.

Definition option_extr A (o:option A) (x:A) :=
  match o with
  | Some a => a
  | _ => x
  end.

Lemma ZLIncl_ext sT st F t (ZL:list params)
    (EQ:st = stmtFun F t) (ST:subTerm st sT)
    (ZLIncl:list_union (of_list ⊝ ZL) [<=] occurVars sT)
  : list_union (of_list ⊝ (fst ⊝ F ++ ZL)) [<=] occurVars sT.
Proof.
  subst.
  rewrite List.map_app.
  rewrite list_union_app. eapply union_incl_split; eauto.
  pose proof (subTerm_occurVars ST). simpl in *.
  rewrite <- H.
  eapply incl_union_left. eapply list_union_incl; intros; eauto with cset.
  inv_get. eapply incl_list_union. eapply map_get_1; eauto.
  cset_tac.
Qed.

Fixpoint forward (sT:stmt) (Dom: stmt -> Type) `{JoinSemiLattice (Dom sT)}
         `{@LowerBounded (Dom sT) H}
           (ftransform :
              forall sT (ZL:list params) s,
                subTerm s sT
                -> list_union (of_list ⊝ ZL) [<=] occurVars sT
                -> Dom sT -> anni (Dom sT) s)
           (ZL:list (params)) (ZLIncl:list_union (of_list ⊝ ZL) [<=] occurVars sT)
           (st:stmt) (ST:subTerm st sT) (d:Dom sT) {struct st}
  :  Dom sT.
  refine (
      match st as st' return st = st' -> Dom sT with
      | stmtLet x e s as st =>
        fun EQ =>
          let d:Dom sT := anni_let (Dom sT) EQ (ftransform sT ZL st ST ZLIncl d) in
        @forward sT Dom _ _ _ ftransform ZL ZLIncl s (subTerm_EQ_Let EQ ST) d
      | stmtIf x s t =>
        fun EQ =>
          let an := anni_if EQ (ftransform sT ZL st ST ZLIncl d) in
          match an with
          | (Some a, Some b) =>
            let a' := @forward sT Dom _ H0 _ ftransform ZL ZLIncl s
                               (subTerm_EQ_If1 EQ ST) a in
            let b' := @forward sT Dom _ H0 _ ftransform ZL ZLIncl t
                              (subTerm_EQ_If2 EQ ST) b in
            (join a' b')
            | (Some a, None) =>
              @forward sT Dom _ H0 _ ftransform ZL ZLIncl s
                       (subTerm_EQ_If1 EQ ST) a
            | (None, Some b) =>
              @forward sT Dom _ H0 _ ftransform ZL ZLIncl t
                       (subTerm_EQ_If2 EQ ST) b
            | (None, None) => bottom
          end
      | stmtApp f Y as st =>
        fun EQ =>
          let d := anni_app (Dom sT) EQ (ftransform sT ZL st ST ZLIncl d) in
          d

    | stmtReturn x as st =>
      fun EQ => d

    | stmtFun F t as st =>
      fun EQ =>
        let ZL' := List.map fst F ++ ZL in
        let ant' :=
            @forward sT Dom _ _ _ ftransform ZL'
                     (@ZLIncl_ext sT _ F t ZL EQ ST ZLIncl)
                     t (subTerm_EQ_Fun1 EQ ST)
                                  d in
        let anF' := forwardF (forward sT Dom _ _ _ ftransform ZL'
                                     (@ZLIncl_ext sT _ F t ZL EQ ST ZLIncl))
                            F d (subTerm_EQ_Fun2 EQ ST) in
        fold_left join anF' ant'
      end eq_refl).
Defined.

Lemma fold_list_length A B (f:list B -> (list A * bool) -> list B) (a:list (list A * bool)) (b: list B)
  : (forall n aa, get a n aa -> ❬b❭ <= ❬fst aa❭)
    -> (forall aa b, ❬b❭ <= ❬fst aa❭ -> ❬f b aa❭ = ❬b❭)
    -> length (fold_left f a b) = ❬b❭.
Proof.
  intros LEN.
  general induction a; simpl; eauto.
  erewrite IHa; eauto 10 using get with len.
  intros. rewrite H; eauto using get.
Qed.

Lemma forwardF_get  (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)}
      (forward: forall s (ST:subTerm s sT) (d:Dom sT),
          Dom sT)
      (F:list (params * stmt)) a
      (ST:forall n s, get F n s -> subTerm (snd s) sT) n aa
           (GetBW:get (forwardF forward F a ST) n aa)
  :
    { Zs : params * stmt & {GetF : get F n Zs &
                                   { ST' : subTerm (snd Zs) sT | aa = forward (snd Zs) ST' a
    } } }.
Proof.
  eapply get_getT in GetBW.
  general induction F; inv GetBW.
  - exists a. simpl. do 4 (eexists; eauto 20 using get).
  - edestruct IHF as [Zs [? [? ]]]; eauto; dcr; subst.
    exists Zs. do 4 (eexists; eauto 20 using get).
Qed.

Lemma get_forwardF  (sT:stmt) (Dom:stmt->Type) `{JoinSemiLattice (Dom sT)}
           (forward: forall s (ST:subTerm s sT) (d:Dom sT),
                       Dom sT)
           (ZL:list params)
           (F:list (params * stmt)) (a:Dom sT)
           (ST:forall n s, get F n s -> subTerm (snd s) sT) n Zs
  :get F n Zs
   -> { ST' | get (forwardF forward F a ST) n (forward (snd Zs) ST' a) }.
Proof.
  intros GetF.
  eapply get_getT in GetF.
  general induction GetF; try destruct Zs as [Z s]; simpl.
  - eexists; econstructor.
  - edestruct IHGetF; eauto using get.
Qed.


Ltac inv_get_step_analysis_forward :=
  match goal with
  | [ H: get (@forwardF ?sT ?Dom ?PO ?BSL ?f ?F ?a ?ST) ?n ?x |- _ ]
    => eapply (@forwardF_get sT Dom PO BSL f F a ST n x) in H;
      destruct H as [? [? [? ]]]
  end.

Smpl Add inv_get_step_analysis_forward : inv_get.


Lemma fold_list_length' A B (f:list B -> (list A) -> list B) (a:list (list A)) (b: list B)
  : (forall n aa, get a n aa -> ❬b❭ <= ❬aa❭)
    -> (forall aa b, ❬b❭ <= ❬aa❭ -> ❬f b aa❭ = ❬b❭)
    -> length (fold_left f a b) = ❬b❭.
Proof.
  intros LEN.
  general induction a; simpl; eauto.
  erewrite IHa; eauto 10 using get with len.
  intros. rewrite H; eauto using get.
Qed.

Ltac fold_po :=
  repeat match goal with
         | [ H : context [ @ann_R ?A ?A (@poLe ?A ?I) ] |- _ ] =>
           change (@ann_R A A (@poLe A I)) with (@poLe (@ann A) _) in H
         | [ H : context [ PIR2 poLe ?x ?y ] |- _ ] =>
           change (PIR2 poLe x y) with (poLe x y) in H
         | [ |- context [ ann_R poLe ?x ?y ] ] =>
           change (ann_R poLe x y) with (poLe x y)
  end.

Instance PO_anni A s `{PartialOrder A}
  : PartialOrder (anni A s).
Proof.
  destruct s; simpl; eauto with typeclass_instances.
Defined.



Lemma fold_left_join_struct T `{JoinSemiLattice T} (A A':list T) (b b':T)
  : PIR2 poLe A A'
    -> b ⊑ b'
    -> fold_left join A b ⊑ fold_left join A' b'.
Proof.
  intros pir.
  general induction pir; simpl; eauto.
  eapply IHpir.
  eapply join_struct; eauto.
Qed.

Require Import FiniteFixpointIteration.

Lemma option_extr_mon T `{PartialOrder T} (a a':option T) b b'
  : a ⊑ a'
    -> b ⊑ b'
    -> (forall x, a' = Some x -> b ⊑ x)
    -> option_extr a b ⊑ option_extr a' b'.
Proof.
  intros A B C; inv A; simpl; eauto.
  destruct a'; clear_trivial_eqs; simpl; eauto.
Qed.

Lemma ojoin_mon T `{PartialOrder T} (a a':option T) b b' f
  : a ⊑ a'
    -> b ⊑ b'
    -> ojoin _ f a b ⊑ ojoin _ f a' b'.
Proof.
  intros A B; inv A; inv B; simpl; try destruct a'; try destruct b';
    clear_trivial_eqs; simpl; eauto using fstNoneOrR.
  econstructor. admit.
  econstructor. admit.
  econstructor. admit.
Admitted.

Lemma option_map_mon T `{PartialOrder T}  U `{PartialOrder U} (a a':option T) (f f': T -> U)
  : a ⊑ a'
    -> (forall x y, x ⊑ y -> f x ⊑ f' y)
    -> option_map f a ⊑ option_map f' a'.
Proof.
  intros A; inv A; simpl;
    clear_trivial_eqs; simpl; eauto using fstNoneOrR.
Qed.

Lemma PIR2_bottom_least A B `{LowerBounded A} (ZL:list B) (l:list A)
  : ❬ZL❭ = ❬l❭
    -> PIR2 poLe (tab (⊥) ‖ZL‖) l.
Proof.
  intros. eapply PIR2_get; intros; inv_get; eauto with len.
  eapply bottom_least.
Qed.

Lemma forward_monotone (sT:stmt) (Dom : stmt -> Type) `{JoinSemiLattice (Dom sT)}
      `{@LowerBounded (Dom sT) H}
      (f: forall sT (ZL:list params),
          forall s, subTerm s sT -> list_union (of_list ⊝ ZL) [<=] occurVars sT
               -> Dom sT -> anni (Dom sT) s)
      (fMon:forall s (ST ST':subTerm s sT) ZL
          (ZLIncl ZLIncl':list_union (of_list ⊝ ZL) [<=] occurVars sT),
          forall a b, a ⊑ b -> f sT ZL s ST ZLIncl a ⊑ f sT ZL s ST' ZLIncl' b)
  : forall (s : stmt) (ST ST':subTerm s sT) (ZL:list params)
      (ZLIncl ZLIncl':list_union (of_list ⊝ ZL) [<=] occurVars sT),
    forall (d d' : Dom sT),
      d ⊑ d'
      -> forward Dom f ZL ZLIncl ST d ⊑ forward Dom f ZL ZLIncl' ST' d'.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  sind s; destruct s; intros ST ST' ZL ZLIncl ZLIncl' d d' LE_d; simpl forward;
    simpl forward; repeat let_pair_case_eq; subst; eauto 10 using @ann_R;
      try now (econstructor; simpl; eauto using @ann_R).
  - eapply IH; eauto.
    (* Coq can't find the instantiation *)
    eapply (fMon (stmtLet x e s)); eauto.
  - pose proof (fMon (stmtIf e s1 s2) ST ST' ZL ZLIncl ZLIncl' _ _ LE_d).
    pose proof (IH s1 ltac:(eauto) (subTerm_EQ_If1 eq_refl ST)
                                (subTerm_EQ_If1 eq_refl ST') ZL) as LE1; eauto.
    pose proof (IH s2 ltac:(eauto) (subTerm_EQ_If2 eq_refl ST)
                                (subTerm_EQ_If2 eq_refl ST') ZL) as LE2; eauto.
    destruct (f sT ZL (stmtIf e s1 s2) ST ZLIncl d);
      destruct (f sT ZL (stmtIf e s1 s2) ST' ZLIncl' d'); simpl; invc H2;
        simpl snd in *; simpl fst in *; clear_trivial_eqs.
    repeat cases; subst; clear_trivial_eqs; simpl;
      try (specialize (LE1 _ _ H3));
      try (specialize (LE2 _ _ H4));
      eauto using bottom_least, join_struct, PIR2_bottom_least with len.
    + rewrite LE1; eauto. eapply join_poLe; eauto.
    + rewrite LE2; eauto. rewrite join_commutative. eapply join_poLe.
  - eapply (fMon (stmtApp l Y)); eauto.
  - simpl; fold_po.
    + eapply fold_left_join_struct; eauto.
      * eapply PIR2_get; eauto with len.
        intros; inv_get.

        eapply IH; eauto.
Qed.

Require Import FiniteFixpointIteration.

Instance makeForwardAnalysis (Dom:stmt -> Type)
         {PO:forall s, PartialOrder (Dom s)}
         (BSL:forall s, JoinSemiLattice (Dom s))
         (LB: forall s, @LowerBounded (Dom s) (PO s))
         (f: forall (sT : stmt) (ZL : 〔params〕) (s : stmt),
             subTerm s sT ->
             list_union (of_list ⊝ ZL) [<=] occurVars sT -> Dom sT -> anni (Dom sT) s)
         (fMon:forall sT s (ST ST':subTerm s sT) ZL
                 (ZLIncl ZLIncl':list_union (of_list ⊝ ZL) [<=] occurVars sT),
             forall a b, a ⊑ b -> f sT ZL s ST ZLIncl a ⊑ f sT ZL s ST' ZLIncl' b)
         (Trm: forall s, Terminating (Dom s) poLt)

  : forall s, Iteration (Dom s) :=
  {
    step := fun X : Dom s => forward Dom f nil (incl_empty _ _) (subTerm_refl _) X;
    initial_value := bottom
  }.
Proof.
  - eapply bottom_least.
  - hnf; intros.
    eapply (forward_monotone Dom f (fMon s)); eauto.
Defined.
