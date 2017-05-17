Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet OptionR MoreList.
Require Import Val Var Env IL Annotation Infra.Lattice RenamedApart.
Require Import DecSolve Analysis Filter Terminating.
Require Import Analysis AnalysisForwardSSA FiniteFixpointIteration.
Require Import Reachability Subterm AnnotationLattice DomainSSA.

Set Implicit Arguments.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {D} {H} {H0} exp_transf reach_transf ZL ZLIncl st ST d anr.

Opaque poLe.

(* Coq can't figure out the instantiation (fun _ => bool) via unification,
   so we have to add this specialized lemma *)

(*Lemma forward_length_ass_UC
      (sT : stmt)
      (f : forall sT0 : stmt,
          〔params〕 ->
          forall s : stmt, subTerm s sT0 -> bool -> anni bool)
      (s : stmt) (ST : subTerm s sT) (ZL : 〔params〕)
      k d (a : ann bool)
  : ❬ZL❭ = k -> ❬snd (forward f ZL s ST d a)❭ = k.
  eapply (@forward_length_ass _ (fun _ => bool)).
Qed.

Hint Resolve forward_length_ass_UC.
 *)

Lemma poEq_pair_inv A `{PartialOrder A} B `{PartialOrder B} (x y:A * B)
  : poEq x y <-> poEq (fst x) (fst y) /\ poEq (snd x) (snd y).
Proof.
  firstorder.
Qed.

Smpl Add 120
     match goal with
     | [ H : poEq (_,_) (_,_) |- _ ] =>
       rewrite poEq_pair_inv in H; simpl fst in H; simpl snd in H;
         let H' := fresh H in destruct H as [H H']
     | [H : poEq ?x ?x |- _ ] => clear H
     end : inv_trivial.


Ltac is_in_context X :=
  match goal with
  | [ H : ?Y  |- _ ] =>
    unify X Y
  end.

Smpl Add 120 match goal with
         | [ H : ?x = getAnn ?y, I : context [ setTopAnn ?y ?x ] |- _ ] =>
           rewrite (@setTopAnn_eta _ _ _ (eq_sym H)) in I
         | [ H : getAnn ?y = ?x, I : context [ setTopAnn ?y ?x ] |- _ ] =>
           rewrite (@setTopAnn_eta _ _ _ H) in I
         end : inv_trivial.

Ltac simpl_forward_setTopAnn :=
  match goal with
  | [H : ann_R _ (snd (fst (@forward ?sT ?D ?PO ?JSL ?f ?fr ?ZL ?ZLIncl
                                     ?s ?ST ?d ?r))) ?r' |- _ ] =>
    let X := fresh "HEQ" in
    match goal with
    | [ H' : getAnn r = getAnn r' |- _ ] => fail 1
    | _ => first
            [ unify r r'; fail 1
            | exploit (@forward_getAnn sT D PO JSL f fr ZL ZLIncl s ST d r r' H) as X;
              subst]
    end
  end; subst; try eassumption;
  try rewrite getAnn_setTopAnn in *;
  repeat rewrite setTopAnn_eta' in *.

Smpl Add 130 simpl_forward_setTopAnn : inv_trivial.



Lemma domupdd_eq (D : Type) `{PartialOrder D} (U : ⦃nat⦄) (d:VDom U D) x v pf
  : domenv (proj1_sig d) x === v
    -> d ≣ @domupdd _ _ d x v pf.
Proof.
  eapply poEq_domupd; eauto.
Qed.

Opaque poEq.

(*
Lemma vdom_upd_inv sT (D : Type) `{JoinSemiLattice D} (d d':VDom (occurVars sT) D) f fr ZL ZLIncl s (ST:subTerm s sT) r (AN:annotation s r)
      (EQ: fst (forward f fr ZL ZLIncl s ST d' r) ≣ (d,r))
      (fExt: forall U e (a a':VDom U D), a ≣ a' -> forall b b', b ≣ b' -> f _ b a e ≣ f _ b' a' e)
      (frExt:forall U e (a a':VDom U D),
          a ≣ a' -> forall b b', b ≣ b' -> fr _ b a e ≣ fr _ b' a' e)
  :  d === d'.
Proof.
  general induction AN; subst; simpl in *; dcr;
    repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *;
      simpl in *; clear_trivial_eqs.
  - eapply IHAN; eauto.
    split; simpl.
    + etransitivity; eauto.
      eapply forward_ext; eauto.
      admit.
    + Transparent poEq.
      etransitivity; eauto.
      eapply forward_ext; eauto.
      eapply domupdd_eq.
      exploit (@forward_agree sT _ _ _ f fr ZL (domupdd d' (f (occurVars sT) (getAnn sa) d' e) (subTerm_EQ_Let_x eq_refl ST)) (singleton x) s (subTerm_EQ_Let eq_refl ST) ZLIncl); eauto; dcr.
      etransitivity. symmetry. eapply
      eapply H2. admit.

Qed.
*)
Opaque poEq.
Opaque poLe.


Ltac PIR2_eq_simpl :=
  match goal with
  | [ H : PIR2 (ann_R eq) _ _ |- _ ] =>
    eapply PIR2_R_impl with (R':=eq) in H;
    [|intros ? ?; rewrite <- ann_R_eq; let A := fresh "A" in intros A; apply A]
  | [ H : PIR2 eq _ _ |- _ ] =>
    eapply PIR2_eq in H
  | [ H : ann_R eq _ _ |- _ ] => rewrite ann_R_eq in H
  end.

(*
Definition reachability_sound_indep (sT:stmt) D `{JoinSemiLattice D}
           f fr pr ZL BL s (d:VDom (occurVars sT) D) r (ST:subTerm s sT) ZLIncl
           (EQ:snd (fst (forward f fr ZL ZLIncl s ST d r)) ≣ r)
           (Ann: annotation s r)
           (DefZL: labelsDefined s (length ZL))
           (DefBL: labelsDefined s (length BL))
           (BL_le: poLe (snd (forward f fr ZL ZLIncl s ST d r)) BL)
           (fExt:forall (U : ⦃nat⦄) (e : exp) (a0 a' : VDom U D),
               a0 ≣ a' -> forall b b' : bool, b ≣ b' -> f U b a0 e ≣ f U b' a' e)
           (frIndep:forall U e (a a':VDom U D),
               forall b b', b ≣ b' -> fr _ b a e ≣ fr _ b' a' e)
  : reachability pr Sound BL s r.
Proof.
  general induction Ann; simpl in *; inv DefZL; inv DefBL;
    repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *;
      simpl in *; clear_trivial_eqs.
  Transparent poEq.
  - econstructor; eauto.
  - econstructor; eauto.
    + rewrite <- HEQ0. admit.
    + rewrite <- HEQ. admit.
    + eapply IHAnn1; eauto.
      eapply @PIR2_zip_join_inv_left. eauto.
      eauto with len.
    + eapply IHAnn2; eauto.
      eapply @PIR2_zip_join_inv_right. eauto.
      eauto with len.
  - edestruct get_in_range; eauto.
    edestruct get_in_range; try eapply H4; eauto.
    Transparent poLe. hnf in BL_le.
    edestruct PIR2_nth; eauto using ListUpdateAt.list_update_at_get_3; dcr.
    econstructor; simpl; eauto.
  - econstructor; eauto.
  - set (FWt:=(forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) t
                       (subTerm_EQ_Fun1 eq_refl ST) d ta)) in *.
    set (FWF:=@forwardF sT (sTDom D) (snd FWt) (forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl)) s (joinTopAnn (A:=bool) ⊜ sa (snd FWt)) (fst (fst FWt)) (subTerm_EQ_Fun2 eq_refl ST)) in *.
    eapply PIR2_get in H16; eauto with len.
    assert (LenA:❬s❭ <= ❬snd FWt❭). {
      subst FWt. len_simpl. omega.
    }

    assert (LenB:❬fst ⊝ s ++ ZL❭ = ❬snd FWt❭). {
      subst FWt. len_simpl. omega.
    }
    econstructor; eauto.
    + eapply IHAnn; eauto.
      * erewrite (take_eta ❬s❭) at 1. eapply PIR2_app; eauto.
        -- change (PIR2 impb) with (@poLe (list bool) _).
           assert (PIR2 impb (Take.take ❬s❭ (snd FWt)) (getAnn ⊝ sa)). {
             change (PIR2 impb) with (PIR2 (@poLe bool _)).
             rewrite H.
             exploit (snd_forwardF_inv _ _ _ _ _ _ _ H16); eauto.
             eapply (@joinTopAnn_map_inv); eauto.
           }
           rewrite <- H4. subst FWF.
           subst FWt. reflexivity.
        -- rewrite <- BL_le.
           eapply PIR2_drop.
           etransitivity;[| eapply forwardF_mon; eauto].
           reflexivity.
           subst FWt.
           eauto with len.
    + intros.
      exploit (snd_forwardF_inv _ _ _ _ _ _ _ H16); eauto.
      exploit (snd_forwardF_inv' _ _ _ _ _ _ _ H16); eauto.
      exploit (@joinTopAnn_map_inv bool). eapply H9.
      eapply H1; eauto.
      * eapply (@snd_forwardF_inv_get); eauto.
        intros. admit.
      * erewrite (take_eta ❬s❭) at 1. eapply PIR2_app; eauto.
        -- rewrite H. etransitivity; eauto. unfold FWt.
           admit.
        -- etransitivity; eauto.
          eapply PIR2_drop.
          eapply forwardF_PIR2; eauto.
           ++ eapply @PIR2_length in H9. rewrite H9. eauto.
           ++ admit.
           ++ repeat PIR2_eq_simpl. rewrite H9. eauto.
Qed.
 *)


Transparent poEq.

Lemma forward_if_inv (sT:stmt) D `{JoinSemiLattice D}
      f fr ZL s t (d:VDom (occurVars sT) D) STt STs ZLIncl sa ta
      (ANs:annotation s sa) (ANt:annotation t ta)
      (EQ: fst (fst (forward f fr ZL ZLIncl t STt (fst (fst (forward f fr ZL ZLIncl s STs d sa))) ta)) ≣ d)
      (disj1:disj (definedVars s) (definedVars t))
      (disj2:disj (definedVars s ∪ definedVars t) (list_union (of_list ⊝ ZL)))
  : (fst (fst (forward f fr ZL ZLIncl s STs d sa))) ≣ d.
Proof.
  hnf; intro x.
  exploit (@forward_agree sT _ _ _ f fr ZL d (singleton x) s STs ZLIncl); eauto; dcr.
  decide (x ∈ (definedVars s ∪ list_union (of_list ⊝ ZL))).
  - specialize (EQ x).
    rewrite <- EQ.
    exploit (@forward_agree sT _ _ _ f fr ZL (fst (fst (forward f fr ZL ZLIncl s STs d sa))) (singleton x) t STt ZLIncl); eauto; dcr.
    decide (x ∈ list_union (of_list ⊝ ZL)).
    + assert (x ∉ definedVars t) by cset_tac.
      eapply poLe_antisymmetric.
      * specialize (H5 x). rewrite H5. reflexivity.
        cset_tac.
      * rewrite EQ. eapply H3. cset_tac.
    + specialize (H4 x).
      rewrite H4. reflexivity. cset_tac.
  - symmetry.
    eapply H2. cset_tac.
Qed.

Lemma forward_agree_ren sT D `{JoinSemiLattice D} f fr
      ZL AE G s (ST:subTerm s sT) ra ZLIncl anr
      (RA:renamedApart s ra) (AN:annotation s anr)
  : agree_on poEq (G \ (snd (getAnn ra) ∪ list_union (of_list ⊝ ZL)))
             (domenv (proj1_sig AE))
             (domenv (proj1_sig
                        (fst (fst (forward f fr ZL ZLIncl
                                            s ST AE anr))))) /\
    agree_on poLe (G \ (snd (getAnn ra)))
             (domenv (proj1_sig AE))
             (domenv (proj1_sig
                        (fst (fst (forward f fr ZL ZLIncl
                                            s ST AE anr))))).
Proof.
  rewrite <- renamedApart_occurVars; eauto.
  eapply forward_agree; eauto.
Qed.


Lemma forward_agree_def_ren sT D `{JoinSemiLattice D} ZL AE G s f fr
      (ST:subTerm s sT) ra ZLIncl anr pf
  (RA:renamedApart s ra) (AN:annotation s anr)
  : agree_on poEq (G \ (snd (getAnn ra) ∪ list_union (of_list ⊝ ZL)))
             (domenv AE)
             (domenv (proj1_sig
                        (fst (fst (forward f fr
                                            ZL ZLIncl
                                            s ST (exist _ AE pf) anr))))).
Proof.
  edestruct forward_agree_ren with (AE:=exist _ AE pf); dcr; eauto.
Qed.


Lemma forward_agree_def sT D `{JoinSemiLattice D} ZL AE G s f fr
      (ST:subTerm s sT) ra ZLIncl anr pf
  (RA:renamedApart s ra) (AN:annotation s anr)
  : agree_on poEq (G \ (definedVars s ∪ list_union (of_list ⊝ ZL)))
             (domenv AE)
             (domenv (proj1_sig
                        (fst (fst (forward f fr
                                            ZL ZLIncl
                                            s ST (exist _ AE pf) anr))))).
Proof.
  edestruct forward_agree with (AE:=exist _ AE pf); dcr; eauto.
Qed.

Lemma forwardF_agree_get (sT:stmt) D `{JoinSemiLattice D} f fr
      (F : 〔params * stmt〕)
      (t : stmt)
      (ZL : 〔params〕)
      (ra : 〔ann (⦃nat⦄ * ⦃nat⦄)〕)
      (AE AE': VDom (occurVars sT) D) BL
      STF
      (ZLIncl : list_union (of_list ⊝ ZL) [<=] occurVars sT)
      (LenZL:❬ZL❭ >= ❬F❭)
      (sa : 〔ann bool〕)
      (ta : ann bool)  tra
      (RAt:renamedApart t tra) (AN:annotation t ta)
      (EQM :   (fst (fst (@forwardF sT (sTDom D) BL
                                (forward f fr ZL ZLIncl) F
                                sa
                                AE'
                                STF))) ≣ AE)
      (STt:subTerm t sT)
      (EQ: (fst (fst (forward f fr ZL ZLIncl t STt AE ta))) ≣ AE')
      (Disj1:disj (snd (getAnn tra)) (list_union (of_list ⊝ ZL)))
      (Disj2:disj (snd (getAnn tra)) (list_union (snd ⊝ getAnn ⊝ ra)))
      (Disj3:disj (list_union (of_list ⊝ ZL)) (list_union (snd ⊝ getAnn ⊝ ra)))
      (Disj5:disj (list_union (of_list ⊝ fst ⊝ F)) (list_union (snd ⊝ getAnn ⊝ ra)))
      (Disj6:PairwiseDisjoint.pairwise_ne disj (defVars ⊜ F ra))
      (Len2 : ❬F❭ = ❬ra❭)
      (Len1 : ❬F❭ = ❬sa❭)
      (AnnF : forall (n : nat) (s' : params * stmt) (sa' : ann bool),
         get sa n sa' -> get F n s' -> annotation (snd s') sa')
      (RA : forall (n : nat) (Zs : params * stmt) (a : ann (⦃nat⦄ * ⦃nat⦄)),
          get F n Zs -> get ra n a -> renamedApart (snd Zs) a)
      (fExt:forall (U : ⦃nat⦄) (e : exp) (a0 a' : VDom U D),
          a0 ≣ a' -> forall b b' : bool, b ≣ b' -> f U b a0 e ≣ f U b' a' e)
      (frExt:forall (U : ⦃nat⦄) (e : op) (a0 a' : VDom U D),
          a0 ≣ a' -> forall b b' : bool, b ≣ b' -> fr U b a0 e ≣ fr U b' a' e)
  : (fst (fst (forward f fr ZL ZLIncl t STt AE ta)) ≣ AE)
    /\  forall n Zs r (ST : subTerm (snd Zs) sT),
      get F n Zs ->
      get sa n r ->
      fst (fst (forward f fr ZL ZLIncl (snd Zs) ST AE r)) ≣ AE.
Proof.
  Opaque poEq.
  general induction Len1; simpl in *; eauto.
  - split; isabsurd. etransitivity; eauto.
  - destruct ra; simpl in *; isabsurd.
    revert Disj2 Disj3 Disj5. norm_lunion. intros Disj2 Disj3 Disj5.
    edestruct (IHLen1 sT _ _ _ f fr t ZL); eauto using get.
    + Transparent poEq.
      hnf; intros z.
      exploit (@forward_agree_ren sT _ _ _ f fr ZL AE (singleton z) t STt tra ZLIncl); eauto; dcr.
      exploit (@forward_agree_ren sT _ _ _ f fr ZL AE' (singleton z) (snd x) (STF 0 x (getLB XL x)) a ZLIncl); eauto using get; dcr.
      exploit (@forwardF_agree sT _ _ _ BL (singleton z) XL f fr YL ZL ZLIncl);
      eauto using get; dcr.
      * eauto with len.
      * intros. inv_get. inv_get. exploit (RA (S n)); eauto using get.
        eapply renamedApart_occurVars in H9; eauto.
        rewrite H9.
        eapply forward_agree_ren; eauto using get.
      * (*
(*    instantiate (3:=(fst (fst (forward f fr ZL ZLIncl (STF 0 x (getLB _ _)) AE' y)))) in H6.
    instantiate (1:=(fun (n : nat) (s : params * stmt) (H : get XL n s) =>
                     STF (S n) s (getLS x H))) in H6.*)
    unfold domenv in *.
    decide (z ∈ snd (getAnn tra) ∪ list_union (of_list ⊝ ZL)).
    + eapply disj_union_inv in i. destruct i; dcr.
      * rewrite EQ.
        eapply H4.
        revert H8 H9 Disj2. clear.
        intros. cset_tac.
      * eapply poLe_antisymmetric.
        -- rewrite EQ.
           eapply H5.
           revert H8 Disj3; clear_all. intros. cset_tac.
        -- etransitivity; [| eapply H3].
           rewrite <- EQM.
           eapply H7.
           revert H8 Disj3. clear_all; intros.
           cset_tac.
           revert H9; clear_all; cset_tac.
      * eapply disj_2_incl; try eapply Disj1; eauto.
    + decide (z ∈ (list_union (defVars ⊜ XL ra))).
      * clear H7 H6.
        rewrite EQ. eapply H4.
        eapply (@defVars_drop_disj (x::XL) (a::ra) 0) in Disj6;
          eauto using get. simpl in *.
        unfold defVars in Disj6 at 1.
        rewrite list_union_defVars_decomp in *; eauto.
        revert n i Disj5 Disj6. clear_all.
        intros. cset_tac.
      * exploit (H2 z). revert n; clear_all; cset_tac.
        rewrite <- H1.
        rewrite <- EQM. symmetry. eapply H6.
        revert n n0; clear_all; cset_tac.
    + eapply disj_2_incl; eauto.
    + eapply disj_2_incl. eapply Disj3. clear_all; cset_tac.
    + eapply disj_incl. eapply Disj5.
      clear_all; cset_tac.
      clear_all; cset_tac.
    + hnf; intros. eapply Disj6; [|eauto using get|eauto using get]. omega.
    + intros; split; eauto.
      intros. inv H3; inv H4; eauto using get.
      assert (AEQ:AE === AE').
      { hnf; intros.
        rewrite <- EQ. rewrite H1. reflexivity.
      }
      assert (EQF:@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) XL YL
                       (fst (fst (forward f fr ZL ZLIncl (STF 0 Zs (@getLB (params * stmt) XL Zs)) AE' r)))
                       (fun (n : nat) (s : params * stmt) (H : get XL n s) =>
                          STF (S n) s (getLS Zs H)) ===
                       forwardF BL (forward f fr ZL ZLIncl) XL YL
                       (fst (fst (forward f fr ZL ZLIncl ST AE r)))
                       (fun (n : nat) (s : params * stmt) (H : get XL n s) =>
                          STF (S n) s (getLS Zs H))
             ). {
        eapply forwardF_ext; eauto.
        intros. eapply forward_ext; eauto.
        assert ((STF 0 Zs (@getLB (params * stmt) XL Zs)) = ST) by eapply subTerm_PI.
        subst.
        eapply forward_ext; eauto.
        symmetry; eauto.
      }
       hnf; intros z.
    exploit (@forward_agree sT _ _ _ f fr ZL AE (singleton z) (snd Zs) ST a ZLIncl); eauto using get; dcr.
    exploit (@forwardF_agree sT _ _ _  BL (singleton z) XL f fr ra YL ZL ZLIncl);
      eauto using get; dcr.
    eauto with len.
    intros. inv_get.
    eapply forward_agree; eauto using get.
    unfold domenv in *.
    decide (z ∈ snd (getAnn tra) ∪ list_union (of_list ⊝ ZL)).
    * eapply disj_union_inv in i. destruct i; dcr.
      -- symmetry.
         eapply (H6 z).
         revert H10 H11 Disj2. clear.
         intros. cset_tac.
      -- eapply poLe_antisymmetric.
         ++ etransitivity.
           eapply H9.
           revert H10 Disj3; clear_all. intros. cset_tac.
           rewrite <- EQM.
           hnf in EQF. dcr.
           hnf in H5. dcr.
           specialize (H13 z).
           rewrite H13. reflexivity.
         ++ eapply H7.
           revert H10 H11 Disj3; clear_all. intros. cset_tac.
      -- eauto.
    * decide (z ∈ (list_union (defVars ⊜ XL ra))).
      -- symmetry.
         eapply H6.
         eapply (@defVars_drop_disj (Zs::XL) (a::ra) 0) in Disj6;
           eauto using get. simpl in *.
        unfold defVars in Disj6 at 1.
        rewrite list_union_defVars_decomp in Disj6; eauto.
        rewrite list_union_defVars_decomp in i; eauto.
        revert n i Disj5 Disj6. clear_all.
        intros. cset_tac.
      -- rewrite (H8 z).
         rewrite <- EQM.
         hnf in EQF. dcr.
         hnf in H5. dcr.
         specialize (H11 z).
         rewrite H11. reflexivity.
         revert n n0; clear_all; cset_tac.
Qed.
         *)
Admitted.
Opaque poEq.



Definition reachability_sound (sT:stmt) D `{JoinSemiLattice D}
           f fr pr ZL BL s (d:VDom (occurVars sT) D) r (ST:subTerm s sT) ZLIncl
           (EQ:(fst (forward f fr ZL ZLIncl s ST d r)) ≣ (d,r)) ra
    (Ann: annotation s r) (RA:renamedApart s ra)
    (DefZL: labelsDefined s (length ZL))
    (DefBL: labelsDefined s (length BL))
    (BL_le: poLe (snd (forward f fr ZL ZLIncl s ST d r)) BL)
    (Disj:disj (list_union (of_list ⊝ ZL)) (snd (getAnn ra)))
    (frIndep:forall U e (a a':VDom U D),
        forall b b', b ≣ b' -> fr _ b a e ≣ fr _ b' a' e)
  : reachability pr Sound BL s r.
Proof.
  general induction Ann; invt renamedApart; simpl in *; inv DefZL; inv DefBL;
    repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *;
      simpl in *; inv_cleanup.
  - clear_trivial_eqs.
    econstructor; eauto.
    eapply IHAnn; eauto. split; simpl; eauto.
    exploit (@forward_agree sT _ _ _ f fr ZL (domupdd d (f (occurVars sT) (getAnn sa) d e) (subTerm_EQ_Let_x eq_refl ST)) (singleton x) s (subTerm_EQ_Let eq_refl ST) ZLIncl); eauto; dcr.
    exploit (H2 x).
    rewrite renamedApart_occurVars; eauto. pe_rewrite. set_simpl.
    eapply renamedApart_disj in H6. pe_rewrite. revert H6 Disj.
    clear_all. cset_tac.
    rewrite EQ.
    eapply domupdd_eq.
    exploit (EQ x).
    rewrite H7 in H1.
    rewrite <- H1. symmetry.
    unfold domenv, domupdd; simpl.
    rewrite domupd_var_eq. reflexivity. reflexivity.
    pe_rewrite. eapply disj_2_incl; eauto. cset_tac.
  - clear_trivial_eqs.
    set_simpl.
    econstructor; eauto.
    + admit.
    + admit.
    + eapply IHAnn1;
        eauto using @PIR2_zip_join_inv_left, @PIR2_zip_join_inv_right with len.
      * split; simpl; eauto.
        eapply forward_if_inv; eauto;
          repeat rewrite renamedApart_occurVars; eauto;
            pe_rewrite; eauto with cset.
      * pe_rewrite. eapply disj_2_incl; eauto.
    + eapply IHAnn2;
        eauto using @PIR2_zip_join_inv_left, @PIR2_zip_join_inv_right with len.
      * split; simpl; eauto.
        rewrite EQ. symmetry.
        eapply forward_if_inv; eauto;
          repeat rewrite renamedApart_occurVars; eauto;
            pe_rewrite; eauto with cset.
      * pe_rewrite. eapply disj_2_incl; eauto.
  - edestruct get_in_range; eauto.
    edestruct get_in_range; try eapply H7; eauto.
    Transparent poLe. hnf in BL_le.
    edestruct PIR2_nth; eauto using ListUpdateAt.list_update_at_get_3; dcr.
    econstructor; simpl; eauto.
  - econstructor.
  - clear_trivial_eqs.
    set (FWt:=(forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) t
                       (subTerm_EQ_Fun1 eq_refl ST) d ta)) in *.
    set (FWF:=forwardF (snd FWt) (forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl)) s (joinTopAnn (A:=bool) ⊜ sa (snd FWt)) (fst (fst FWt)) (subTerm_EQ_Fun2 eq_refl ST)) in *.
    intros.
    eapply PIR2_get in H23; eauto with len.
    exploit (snd_forwardF_inv _ _ _ _ _ _ _ H23); eauto.
    subst FWt. len_simpl. omega.
    subst FWt. len_simpl. omega.
    exploit (snd_forwardF_inv' _ _ _ _ _ _ _ H23); eauto.
    subst FWt. len_simpl. omega.
    subst FWt. len_simpl. omega.
    assert (forall (n : nat) (r : ann bool) (Zs : params * stmt),
       get sa n r ->
       get s n Zs ->
       forall STZs : subTerm (snd Zs) sT,
       ann_R eq
         (snd
            (fst
               (forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl)
                        (snd Zs) STZs (fst (fst FWt)) r))) r).
    eapply (@snd_forwardF_inv_get); eauto.
    subst FWt. len_simpl.  omega.
    subst FWt. len_simpl. omega.
    intros. admit. admit.
    Transparent poEq.
    repeat PIR2_eq_simpl.
    subst FWF FWt.
    rewrite H23 in *.
    rewrite H4 in *.
    rewrite H5 in *.
    set (FWt:=(forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) t
                       (subTerm_EQ_Fun1 eq_refl ST) d ta)) in *.
    set (FWF:=forwardF (snd FWt) (forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl)) s sa (fst (fst FWt)) (subTerm_EQ_Fun2 eq_refl ST)) in *.
    Opaque poEq. inv_cleanup.

    econstructor; eauto.
    + eapply IHAnn; eauto.
      * split; eauto. simpl.
        admit.
      * erewrite (take_eta ❬s❭) at 1. eapply PIR2_app; eauto.
        --change (PIR2 poLe) with (@poLe (list bool) _).
           assert (poLe (Take.take ❬s❭ (snd FWt)) (getAnn ⊝ sa)). {
             rewrite H.
             eapply (@joinTopAnn_map_inv).
             rewrite <- H4 at 2. reflexivity.
           }
           rewrite <- H4. subst FWF.
           subst FWt.
           rewrite H4.
           rewrite <- H5.
           rewrite <- (@forwardF_mon' sT D _ _ f fr); eauto.
        -- rewrite <- BL_le.
           eapply PIR2_drop.
           etransitivity;[|
                          eapply forwardF_mon; eauto].
           reflexivity.
           subst FWt. eauto with len.
      * pe_rewrite.
        admit.
    + intros. inv_get. exploit H7; eauto.
      eapply H1; eauto.
      -- subst FWF FWt.

         exploit  forwardF_agree_get; eauto.
         len_simpl. omega.

        split; simpl; eauto. simpl. reflexivity.
      -- rewrite (take_eta ❬sa❭) at 1.
         eapply PIR2_app; eauto.
         ++ eapply setTopAnn_map_inv in H15.
           rewrite <- H15. eapply PIR2_take.
           change (PIR2 impb) with (@poLe (list bool) _).
           eapply forwardF_PIR2; eauto.
           subst FWt. clear_all. eauto with len.

         ++ etransitivity; eauto.
           rewrite H. eapply PIR2_drop.
           eapply forwardF_PIR2; eauto.
           subst FWt. eauto with len.
           admit.
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

Opaque poLe.


Lemma forward_snd_poLe sT BL ZL s (ST:subTerm s sT) n a b c
  : reachability cop2bool Complete BL s a
    -> poLe (getAnn a) c
    -> get (snd (forward reachability_transform ZL s ST c a)) n b
    -> poLe b c.
Proof.
  revert ZL BL ST n a b c.
  sind s; intros; destruct s; destruct a; invt reachability;
    simpl in *; repeat let_case_eq; repeat simpl_pair_eqs; simpl in *;
      inv_get;
      try solve [ destruct a; simpl; eauto | destruct a1; simpl; eauto ].
  - eapply IH in H1; eauto.
  - cases in H6; cases in H1; try congruence.
    + assert (cop2bool e = ⎣ wTA false ⎦). {
        rewrite op2bool_cop2bool in COND; eauto.
      }
      assert (~ cop2bool e ⊑ ⎣ wTA true ⎦). {
        rewrite H2. clear_all. intro. clear_trivial_eqs.
      }
      specialize (H10 ltac:(eauto)).
      eapply IH in H1; eauto.
      eapply orb_poLe_struct; eauto.
      rewrite <- H0. rewrite <- H10.
      eapply IH in H6; simpl in *; eauto.
      rewrite H6. eauto.
      rewrite H13; eauto. rewrite H2; eauto.
    + assert (cop2bool e = ⎣ wTA true ⎦). {
        rewrite op2bool_cop2bool in COND; eauto.
      }
      assert (~ cop2bool e ⊑ ⎣ wTA false ⎦). {
        rewrite H2. clear_all. intro. clear_trivial_eqs.
      }
      specialize (H9 ltac:(eauto)).
      eapply IH in H6; eauto.
      eapply orb_poLe_struct; eauto.
      eapply IH in H1; simpl in *; eauto.
      rewrite H1; eauto.
      rewrite H14; eauto. rewrite H2; eauto.
    + assert (~ cop2bool e ⊑ ⎣ wTA true ⎦). {
        eauto using op2bool_cop2bool_not_some.
      }
      assert (~ cop2bool e ⊑ ⎣ wTA false ⎦). {
        eauto using op2bool_cop2bool_not_some.
      }
      specialize (H9 ltac:(eauto)).
      specialize (H10 ltac:(eauto)).
      eapply IH in H1; eauto.
      eapply IH in H6; simpl in *; eauto.
      eapply orb_poLe_struct; eauto.
  - decide (labN l = n); subst.
    + eapply ListUpdateAt.list_update_at_get_2 in H1; eauto; subst.
    + eapply ListUpdateAt.list_update_at_get_1 in H1; eauto; subst.
      inv_get. eauto.
  - destruct b; [| destruct c; simpl; eauto].
    eapply fold_left_zip_orb_inv in H1. destruct H1.
    + eapply IH in H1; eauto.
    + dcr. inv_get.
      eapply IH in H4; eauto.
      exploit H13; eauto.
Qed.

Local Hint Extern 0 => first [ erewrite (@forward_getAnn' _ (fun _ => bool))
                            | erewrite getAnn_setTopAnn
                            | rewrite getAnn_setAnn ].

Transparent poLe.

Lemma fold_left_forward_mono sT F t ZL als als' alt alt' b b'
      (STF:forall n s, get F n s -> subTerm (snd s) sT)
      (ST:subTerm t sT)
  : length F = length als
    -> annotation t alt
    -> (forall n Zs a, get F n Zs -> get als n a -> annotation (snd Zs) a)
    -> poLe als als'
    -> poLe alt alt'
    -> poLe b b'
    -> poLe (fold_left
            (zip orb)
            (snd ⊝ forwardF (forward reachability_transform)
                 (fst ⊝ F ++ ZL) F als STF)
            (snd (forward reachability_transform (fst ⊝ F ++ ZL)
                          t ST
                          b alt)))
         (fold_left
            (zip orb)
            (snd ⊝ forwardF (forward reachability_transform)
                 (fst ⊝ F ++ ZL) F als' STF)
            (snd (forward reachability_transform (fst ⊝ F ++ ZL)
                          t ST
                          b' alt'))).
Proof.
  intros LEN Ant AnF LE1 LE2 LE3.
  eapply fold_left_mono.
  - eapply PIR2_get; intros; inv_get.
    + PI_simpl.
      eapply (@forward_monotone sT (fun _ => bool) _ _ _ reachability_transform ); eauto.
      eapply reachability_transform_monotone; eauto.
      eapply ann_R_get.
      eapply get_PIR2; eauto.
      eapply get_PIR2; eauto.
    + rewrite !map_length.
      rewrite !(@forwardF_length _ (fun _ => bool)).
      rewrite (PIR2_length LE1). reflexivity.
  - exploit (@forward_monotone sT (fun _ => bool) _ _ _ reachability_transform );
      try eapply H; eauto.
    eapply reachability_transform_monotone.
Qed.

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

Opaque poLe.

Lemma reachability_analysis_complete_isCalled sT ZL BL s a b
      (ST:subTerm s sT)
  : reachability cop2bool Complete BL s a
    -> forall n, get (snd (forward reachability_transform ZL s ST b a)) n true
           -> poLe (getAnn a) b
           -> isCalled true s (LabI n).
Proof.
  intros.
  general induction H; simpl in *;
    repeat let_case_eq; repeat simpl_pair_eqs; subst;
      simpl in *; eauto using isCalled.
  - inv_get. cases in H7; try congruence.
    + eapply forward_snd_poLe in H7; eauto; clear_trivial_eqs.
      * destruct x; isabsurd. simpl in *; subst.
        eapply IsCalledIf2; eauto.
        eapply IHreachability2; eauto.
        cases in H5; eauto.
        rewrite H0; eauto.
        eapply op2bool_cop2bool_not_some; eauto.
      * rewrite H3; eauto.
        rewrite op2bool_cop2bool in COND. rewrite COND. reflexivity.
    + cases in H5; try congruence.
      eapply forward_snd_poLe in H5; eauto; clear_trivial_eqs.
      * destruct x0; isabsurd.
        eapply orb_prop in EQ. destruct EQ; subst; isabsurd.
        eapply IsCalledIf1; eauto.
        eapply IHreachability1; eauto.
        rewrite H; eauto.
        eapply op2bool_cop2bool_not_some; eauto.
      * rewrite H4; eauto.
        rewrite op2bool_cop2bool in COND. rewrite COND. reflexivity.
      * eapply orb_prop in EQ. destruct EQ; subst; isabsurd.
        -- eapply IsCalledIf1; eauto.
           eapply IHreachability1; eauto.
           rewrite H; eauto.
           eapply op2bool_cop2bool_not_some; eauto.
        -- eapply IsCalledIf2; eauto.
           eapply IHreachability2; eauto.
           rewrite H0; eauto.
           eapply op2bool_cop2bool_not_some; eauto.
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
      exploit forward_snd_poLe; try eapply Get; eauto.
      exploit H3; eauto; dcr.
      edestruct isCalledFrom_extend; eauto; dcr.
      econstructor; eauto.
Qed.

Lemma reachability_analysis_complete sT ZL BL BL' (Len:❬BL❭ = ❬BL'❭) s a (ST:subTerm s sT) b b' c
      (LDEF:labelsDefined s (length ZL))
      (EQ:(fst (forward reachability_transform ZL s ST b a)) = c)
      (LE:poLe a (setTopAnn c b'))
      (LEb: poLe (getAnn c) b')
  : reachability cop2bool Complete BL s a
    -> reachability cop2bool Complete BL' s (setTopAnn c b').
Proof.
  subst c.
  intros RCH.
  general induction RCH; simpl in *; repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *; invt labelsDefined; try inv LE;
    eauto using reachability, subTerm, reachability_sTA_inv,
    ann_R_setTopAnn_left.
  - econstructor. eapply reachability_sTA_inv.
    eapply IHRCH; eauto.
    rewrite setTopAnn_eta; eauto.
    repeat rewrite (@forward_getAnn' _ (fun _ => bool)). eauto.
  - econstructor; intros; cases; simpl;
      eauto using reachability_sTA_inv, ann_R_setTopAnn_left.
    + eapply reachability_sTA_inv. eapply IHRCH1; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply reachability_sTA_inv. eapply IHRCH1; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply reachability_sTA_inv. eapply IHRCH2; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply reachability_sTA_inv. eapply IHRCH2; eauto.
      rewrite setTopAnn_eta; eauto.
    + intros. exfalso.
      eapply op2bool_cop2bool_not_some in NOTCOND; eauto.
    + intros. exfalso.
      eapply op2bool_cop2bool_not_some in NOTCOND; eauto.
  - inv_get. econstructor; eauto.
  - econstructor; eauto.
  - econstructor; simpl; eauto using reachability_sTA_inv, ann_R_setTopAnn_left.
    + eapply reachability_sTA_inv. eapply IHRCH; eauto.
      rewrite !app_length, !map_length.
      rewrite H14. eauto.
      rewrite setTopAnn_eta; eauto.
    + eauto with len.
    + intros. inv_get.
      rewrite <- (setTopAnn_eta x4 eq_refl).
      edestruct (@get_forwardF sT (fun _ => bool)); eauto.
      exploit H15. eauto.
      eapply zip_get_eq. eauto. eauto. reflexivity.
      eapply H2. eauto. rewrite setTopAnn_eta. eauto.
      eauto.
      eauto with len.
      eauto.
      eapply ann_R_get in H8. rewrite getAnn_setTopAnn in H8.
      eauto.
      etransitivity; eauto.
      rewrite (setTopAnn_eta _ eq_refl).
      Transparent poLe.
      eapply H8.
      pose proof (@poLe_setTopAnn bool _ x0 x0).
      eapply H10; eauto. assert (x = x6) by eapply subTerm_PI.
      subst. rewrite setTopAnn_eta. reflexivity. eauto.
    + intros. inv_get.
      rewrite getAnn_setTopAnn in H6.
      destruct x0; isabsurd.
      eapply fold_left_zip_orb_inv in H5. destruct H5.
      * eapply reachability_analysis_complete_isCalled in H5; eauto.
        econstructor; split; eauto. econstructor 1.
        eapply ann_R_get in H16.
        rewrite (@forward_getAnn' _ (fun _ => bool)) in H16. eauto.
      * dcr. inv_get.
        exploit forward_snd_poLe; try eapply H11; eauto.
        eapply reachability_analysis_complete_isCalled in H11; eauto.
        exploit H3; eauto.
        eapply isCalledFrom_extend; eauto.
    + intros. inv_get. rewrite getAnn_setTopAnn.
      exploit H4; eauto. destruct x0; simpl; eauto.
      destruct b0; eauto.
      destruct b'; invc LEb; eauto.
      destruct b; invc H12; eauto.
      eapply fold_left_zip_orb_inv in H5. destruct H5.
      * eapply forward_snd_poLe in H5; eauto.
      * dcr. inv_get.
        eapply forward_snd_poLe in H11; eauto.
        exploit H4; eauto. destruct (getAnn x8); isabsurd.
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

Lemma reachability_complete s
  : labelsDefined s ❬nil:list params❭
    -> reachability cop2bool Complete nil s (reachabilityAnalysis s).
Proof.
  unfold reachabilityAnalysis. destr_sig.
  destruct e as [n [Iter _]]. subst.
  intros. eapply safeFixpoint_induction.
  - eapply reachability_complete_bottom; eauto.
  - intros.
    eapply reachability_sTA_inv.
    eapply (@reachability_analysis_complete s nil); eauto.
    reflexivity.
    erewrite (setTopAnn_eta _ eq_refl); eauto.
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
    eapply (@reachability_sound s nil); simpl; eauto.
    + simpl in *. simpl_forward_setTopAnn.
    + assert (❬snd (forward reachability_transform nil s (subTerm_refl s) true x)❭ = 0).
      rewrite (@forward_length _ (fun _ => bool)); eauto.
      destruct (snd (forward reachability_transform nil s (subTerm_refl s) true x)); isabsurd.
      eauto using PIR2.
Qed.

Lemma reachabilityAnalysis_getAnn s
  : getAnn (ReachabilityAnalysis.reachabilityAnalysis s).
Proof.
  unfold reachabilityAnalysis.
  destr_sig. destruct e as [n [H1 H2]]. subst x.
  simpl in *; simpl_forward_setTopAnn; destr_sig; simpl in *.
  rewrite H. eauto.
Qed.