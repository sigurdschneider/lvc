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

Definition forwardF (sT:stmt) (Dom:stmt->Type) `{BoundedSemiLattice (Dom sT)}
           (forward:〔params〕 ->
                    forall s (ST:subTerm s sT) (d:Dom sT),
                      Dom sT * 〔Dom sT〕)
           (ZL:list params)
           (F:list (params * stmt)) (a:Dom sT)
           (ST:forall n s, get F n s -> subTerm (snd s) sT)
  : list (Dom sT * 〔Dom sT〕).
  revert F ST.
  fix g 1. intros.
  destruct F as [|Zs F'].
  - eapply nil.
  - econstructor 2.
    + refine (forward ZL (snd Zs) _ a).
      eapply (ST 0 Zs); eauto using get.
    + eapply (g F').
      eauto using get.
Defined.

Arguments forwardF [sT] [Dom] {H} {H0} forward ZL F a ST.

Fixpoint forwardF_length (sT:stmt) (Dom:stmt->Type) `{BoundedSemiLattice (Dom sT)} forward
           (ZL:list params)
           (F:list (params * stmt)) a
           (ST:forall n s, get F n s -> subTerm (snd s) sT) {struct F}
  : length (forwardF forward ZL F a ST) = length F.
Proof.
  destruct F as [|Zs F']; simpl; eauto.
Qed.

Smpl Add
     match goal with
     | [ |- context [ ❬@forwardF ?sT ?Dom ?H ?BSL ?f ?ZL ?F ?a ?ST❭ ] ] =>
       rewrite (@forwardF_length sT Dom H BSL f ZL F a ST)
     | [ H : context [ ❬@forwardF ?sT ?Dom ?H ?BSL ?f ?ZL ?F ?a ?ST❭ ] |- _ ] =>
       rewrite (@forwardF_length sT Dom H BSL f ZL F a ST) in H
     end : len.

Lemma forwardF_length_ass (sT:stmt) (Dom:stmt->Type) `{BoundedSemiLattice (Dom sT)}
      forward ZL F a ST k
  : length F = k
    -> length (forwardF forward ZL F a ST) = k.
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

Fixpoint forward (sT:stmt) (Dom: stmt -> Type) `{BoundedSemiLattice (Dom sT)}
           (ftransform :
              forall sT, list params ->
                    forall s, subTerm s sT -> Dom sT -> anni (Dom sT) s)
           (ZL:list (params)) (st:stmt) (ST:subTerm st sT) (d:Dom sT) {struct st}
  :  Dom sT * list (Dom sT).
  refine (
      match st as st' return st = st' -> Dom sT * list (Dom sT) with
      | stmtLet x e s as st =>
        fun EQ =>
          let d:Dom sT := anni_let (Dom sT) EQ (ftransform sT ZL st ST d) in
        @forward sT Dom _ _ ftransform ZL s (subTerm_EQ_Let EQ ST) d
      | stmtIf x s t =>
        fun EQ =>
          let an := anni_if EQ (ftransform sT ZL st ST d) in
          let ans'ALs :=
              option_map (fun d => @forward sT Dom _ H0 ftransform ZL s
                                         (subTerm_EQ_If1 EQ ST) d)
                         (fst an)
          in
          let ant'ALt :=
              option_map (fun d => @forward sT Dom _ H0 ftransform ZL t
                                         (subTerm_EQ_If2 EQ ST) d)
                         (snd an)
          in
          option_extr (
          ojoin _ (fun x y => (join (fst x) (fst y), zip join (snd x) (snd y)))
                ans'ALs ant'ALt)
                      (d, (fun _ => bottom) ⊝ ZL)
      | stmtApp f Y as st =>
        fun EQ =>
          let d := anni_app (Dom sT) EQ (ftransform sT ZL st ST d) in
          (d, list_update_at ((fun _ => bottom) ⊝ ZL) (counted f) d)

    | stmtReturn x as st =>
      fun EQ => (d, (fun _ => bottom) ⊝ ZL)

    | stmtFun F t as st =>
      fun EQ =>
        let ZL' := List.map fst F ++ ZL in
        let (ant', ALt) :=
            @forward sT Dom _ _ ftransform ZL' t (subTerm_EQ_Fun1 EQ ST)
                                  d in
        let anF' := forwardF (forward sT Dom _ _ ftransform) ZL' F d
                            (subTerm_EQ_Fun2 EQ ST) in
        let AL' := fold_left (zip join) (snd ⊝ anF') ALt in
        (fold_left join (fst ⊝ anF') ant', drop ❬F❭ AL')
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

Lemma forwardF_get  (sT:stmt) (Dom:stmt->Type) `{BoundedSemiLattice (Dom sT)}
           (forward:〔params〕 ->
                     forall s (ST:subTerm s sT) (d:Dom sT),
                       Dom sT * list (Dom sT))
           (ZL:list params)
           (F:list (params * stmt)) a
           (ST:forall n s, get F n s -> subTerm (snd s) sT) aa n
           (GetBW:get (forwardF forward ZL F a ST) n aa)
      :
        { Zs : params * stmt & {GetF : get F n Zs &
        { ST' : subTerm (snd Zs) sT | aa = forward ZL (snd Zs) ST' a
        } } }.
Proof.
  eapply get_getT in GetBW.
  general induction F; inv GetBW.
  - exists a. simpl. do 4 (eexists; eauto 20 using get).
  - edestruct IHF as [Zs [? [? ]]]; eauto; dcr; subst.
    exists Zs. do 4 (eexists; eauto 20 using get).
Qed.

Lemma get_forwardF  (sT:stmt) (Dom:stmt->Type) `{BoundedSemiLattice (Dom sT)}
           (forward:〔params〕 ->
                     forall s (ST:subTerm s sT) (d:Dom sT),
                       Dom sT * list (Dom sT))
           (ZL:list params)
           (F:list (params * stmt)) (a:Dom sT)
           (ST:forall n s, get F n s -> subTerm (snd s) sT) n Zs
  :get F n Zs
   -> { ST' | get (forwardF forward ZL F a ST) n (forward ZL (snd Zs) ST' a) }.
Proof.
  intros GetF.
  eapply get_getT in GetF.
  general induction GetF; try destruct Zs as [Z s]; simpl.
  - eexists; econstructor.
  - edestruct IHGetF; eauto using get.
Qed.


Ltac inv_get_step_analysis_forward :=
  match goal with
  | [ H: get (@forwardF ?sT ?Dom ?PO ?BSL ?f ?ZL ?F ?a ?ST) ?n ?x |- _ ]
    => eapply (@forwardF_get sT Dom PO BSL f ZL F a ST x n) in H;
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

Lemma forward_length (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT) s)
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params),
    forall d, ❬snd (forward Dom f ZL ST d)❭ = ❬ZL❭.
Proof.
  sind s; destruct s; simpl; intros; eauto with len;
    repeat let_pair_case_eq; subst; simpl in *; eauto.
  - unfold option_extr.
    repeat cases; repeat simpl_pair_eqs; subst; simpl; eauto with len.
    unfold option_map in Heq.
    revert Heq. repeat cases; intros; simpl in *;
                  try clear_trivial_eqs; simpl.
    simpl. rewrite zip_length2; eauto.
    repeat rewrite IH; eauto.
    eauto with len. eauto with len.
  - intros. rewrite list_update_at_length. eauto with len.
  - intros.
    rewrite length_drop_minus.
    rewrite fold_list_length'.
    + rewrite IH; eauto. rewrite app_length, map_length. omega.
    + intros. inv_get. repeat rewrite IH; eauto.
    + intros. rewrite zip_length; eauto.
      eapply min_l; eauto.
Qed.


Smpl Add
     match goal with
     | [ |- context [ ❬snd (@forward ?sT ?Dom ?H ?BSL ?f ?ZL ?s ?ST ?d)❭ ] ] =>
       rewrite (@forward_length sT Dom H BSL f s ST ZL d)
     end : len.

Lemma forward_length_ass
      (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT) s)
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) k,
    forall d, ❬ZL❭ = k -> ❬snd (forward Dom f ZL ST d)❭ = k.
Proof.
  intros. rewrite forward_length; eauto.
Qed.

Lemma forward_length_le_ass
      (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT) s)
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) k,
    forall d, ❬ZL❭ <= k -> ❬snd (forward Dom f ZL ST d)❭ <= k.
Proof.
  intros. rewrite forward_length; eauto.
Qed.

Lemma forward_length_le_ass_right
      (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT) s)
  : forall (s : stmt) (ST:subTerm s sT) (ZL:list params) k,
    forall d, k <= ❬ZL❭ -> k <= ❬snd (forward Dom f ZL ST d)❭.
Proof.
  intros. rewrite forward_length; eauto.
Qed.


Hint Resolve @forward_length_ass forward_length_le_ass forward_length_le_ass_right : len.

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

Lemma poLe_opt_inv T H a b
  : @poLe (option T) (@PartialOrder_option_fstNoneOrR T H)
          (@Some T a) (@Some T b)
    -> poLe a b.
Proof.
  inversion 1; eauto.
Qed.


Smpl Add
     match goal with
     | [ H : @poLe (option ?T) (@PartialOrder_option_fstNoneOrR ?T ?H')
                   (@Some ?T ?a) (@Some ?T ?b) |- _ ] =>
       eapply (@poLe_opt_inv T H' a b) in H
     | [ H : @poLe (option ?T) (@PartialOrder_option_fstNoneOrR ?T ?H')
                   (@Some ?T ?a) None |- _ ] =>
       exfalso; inv H
     end : inv_trivial.


Lemma join_struct T `{BoundedSemiLattice T} (a b a' b':T)
  : a ⊑ a'
    -> b ⊑ b'
    -> a ⊔ b ⊑ (a' ⊔ b').
Proof.
  intros A B. rewrite A, B. reflexivity.
Qed.

Lemma fold_left_join_struct T `{BoundedSemiLattice T} (A A':list T) (b b':T)
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
    -> Some b ⊑ a'
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

Lemma forward_monotone (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT) s)
      (fMon:forall s (ST ST':subTerm s sT) ZL,
          forall a b, a ⊑ b -> f sT ZL s ST a ⊑ f sT ZL s ST' b)
  : forall (s : stmt) (ST ST':subTerm s sT) (ZL:list params),
    forall (d d' : Dom sT), d ⊑ d' ->
                           forward Dom f ZL ST d ⊑ forward Dom f ZL ST' d'.
Proof with eauto using poLe_setTopAnn, poLe_getAnni.
  intros s.
  sind s; destruct s; intros ST ST' ZL d d' LE_d; simpl forward;
    simpl forward; repeat let_pair_case_eq; subst; eauto 10 using @ann_R;
      try now (econstructor; simpl; eauto using @ann_R).
  - eapply IH; eauto.
    (* Coq can't find the instantiation *)
    eapply (fMon (stmtLet x e s)); eauto.
  - pose proof (fMon (stmtIf e s1 s2) ST ST' ZL _ _ LE_d).
    eapply option_extr_mon; eauto.
    + eapply ojoin_mon.
      eapply option_map_mon; eauto.
      eapply H1.
      eapply option_map_mon; eauto.
      eapply H1.
    + simpl; split; eauto.
    + admit.
  - econstructor; eauto. simpl.
    + eapply (fMon (stmtApp l Y)); eauto.
    + eapply update_at_poLe.
      eapply (fMon (stmtApp l Y)); eauto.
  - split; simpl; fold_po.
    + eapply fold_left_join_struct; eauto.
      * eapply PIR2_get; eauto with len.
        intros; inv_get.
        eapply IH; eauto.
      * eapply IH; eauto.
    + eapply PIR2_drop. eapply PIR2_fold_zip_join.
      * eapply PIR2_get; eauto with len.
        intros; inv_get.
        eapply IH; eauto.
      * eapply IH; eauto.
Admitted.

Require Import FiniteFixpointIteration.

Instance makeForwardAnalysis (Dom:stmt -> Type)
         `{forall s, PartialOrder (Dom s) }
         (BSL:forall s, BoundedSemiLattice (Dom s))
         (f: forall sT, list params ->
                   forall s, subTerm s sT -> Dom sT -> anni (Dom sT) s)
         (fMon:forall sT s (ST ST':subTerm s sT) ZL,
             forall a b, a ⊑ b -> f sT ZL s ST a ⊑ f sT ZL s ST' b)
         (Trm: forall s, Terminating (Dom s) poLt)

  : forall s, Iteration (Dom s) :=
  {
    step := fun X : Dom s => fst (forward Dom f nil (subTerm_refl _) X);
    initial_value := bottom
  }.
Proof.
  - eapply bottom_least.
  - hnf; intros.
    eapply (forward_monotone Dom f (fMon s)); eauto.
Defined.
