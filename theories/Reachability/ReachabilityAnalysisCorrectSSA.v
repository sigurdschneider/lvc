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



Lemma domupdd_eq (D : Type) `{PartialOrder D} (U : ⦃var⦄) (d:VDom U D) x v pf
  : domenv (proj1_sig d) x === v
    -> d ≣ @domupdd _ _ d x v pf.
Proof.
  eapply poEq_domupd; eauto.
Qed.

Opaque poEq.
Opaque poLe.


Ltac PIR2_eq_simpl :=
  match goal with
  | [ H : PIR2 (ann_R eq) _ _ |- _ ] =>
    eapply PIR2_R_impl with (R':=eq) in H;
    [|intros ? ?; rewrite <- ann_R_eq; let A := fresh "A" in intros A; apply A]
  | [ H : (@poEq (list (ann bool)) _) _ _ |- _ ] =>
    eapply PIR2_R_impl with (R':=eq) in H;
    [|intros ? ?; rewrite <- ann_R_eq; let A := fresh "A" in intros A; apply A]
  | [ H : PIR2 eq _ _ |- _ ] =>
    eapply PIR2_eq in H
  | [ H : PIR2 (@poEq bool _) _ _ |- _ ] =>
    eapply PIR2_eq in H
  | [ H : ann_R eq _ _ |- _ ] => rewrite ann_R_eq in H
  | [ H : _ = ?x |- _ ] => is_var x; rewrite H in *
  end.


Transparent poEq.

Lemma agree_comp_inv A `{OrderedType A} B (R:B->B->Prop) `{Transitive _ R} (f g : (A -> B) -> (A -> B)) Gf Gg
      (AGRf: forall d, agree_on R Gf d (f d))
      (AGRg: forall d, agree_on R Gg d (g d))
  : forall d, agree_on R (Gf ∩ Gg) d (f (g d)).
Proof.
  intros d. hnf; intros x IN.
  cset_tac'.
  rewrite <- (AGRf (g d) x); eauto.
  eapply AGRg; eauto.
Qed.

Lemma agree_comp_inv' A `{OrderedType A} B (R:B->B->Prop) `{Transitive _ R} (f g : (A -> B) -> (A -> B)) d D Gf Gg (disj: disj Gf Gg)
      (AGR:forall x, R (f (g d) x) (d x))
      (AGRf: forall d, agree_on R (D \ Gf) d (f d))
      (AGRg: forall d, agree_on R (D \ Gg) (g d) d)
  : agree_on R D (g d) d.
Proof.
  intros x IN.
  decide (x ∈ Gg).
  - assert (x ∉ Gf). cset_tac.
    specialize (AGRf (g d) x ).
    etransitivity. eapply AGRf. cset_tac.
    eapply AGR.
  - eapply AGRg. cset_tac.
Qed.

Lemma agree_comp_inv'' A `{OrderedType A} B (R:B->B->Prop) `{Transitive _ R}
      X (r : X -> (A -> B))
      (f g : X -> X) (d:X) D Gf Gg (disj: disj Gf Gg)
      (AGR:forall x, R (r (f (g d)) x) (r d x))
      (AGRf: forall d, agree_on R (D \ Gf) (r d) (r (f d)))
      (AGRg: forall d, agree_on R (D \ Gg) (r (g d)) (r d))
  : agree_on R D (r (g d)) (r d).
Proof.
  intros x IN.
  decide (x ∈ Gg).
  - assert (x ∉ Gf). cset_tac.
    specialize (AGRf (g d) x ).
    etransitivity. eapply AGRf. cset_tac.
    eapply AGR.
  - eapply AGRg. cset_tac.
Qed.

Lemma poEq_VDom D `{PartialOrder D} U (d d':VDom U D)
  : (forall G, agree_on poEq G (domenv (proj1_sig d)) (domenv (proj1_sig d')))
         <-> d ≣ d'.
Proof.
  intros. split; intros.
  - hnf; intros.
    eapply (H0 (singleton x)). cset_tac.
  - hnf; intros. eapply H0.
Qed.

(*
  eapply poEq_VDom; intros.
  decide (disj G (list_union (of_list ⊝ ZL))).
  - symmetry in disj1.
    eapply agree_comp_inv'' with
    (r:=fun d => domenv (proj1_sig d))
      (f:=fun d => fst (fst (forward f fr ZL ZLIncl t STt d ta)))
      (g:=fun d => fst (fst (forward f fr ZL ZLIncl s STs d sa))); try eapply disj1; eauto.
    hnf; intros. rewrite H1. eauto.
    + intros.
      eapply agree_on_incl.
      eapply forward_agree; eauto.
      instantiate (1:=G). revert d0. clear; cset_tac.
    + intros. symmetry.
      intros.
      eapply agree_on_incl.
      eapply forward_agree; eauto.
      instantiate (1:=G). revert d0. clear; cset_tac.
  -
 *)

Lemma forward_if_inv (sT:stmt) D `{JoinSemiLattice D}
      f fr ZL s t (d:VDom (occurVars sT) D) STt STs ZLIncl sa ta
      (EQ: fst (fst (forward f fr ZL ZLIncl t STt (fst (fst (forward f fr ZL ZLIncl s STs d sa))) ta)) ≣ d)
      (ANs:annotation s sa) (ANt:annotation t ta)
      (disj1:disj (definedVars s) (definedVars t))
      (disj2:disj (definedVars s ∪ definedVars t) (list_union (of_list ⊝ ZL)))
  : (fst (fst (forward f fr ZL ZLIncl s STs d sa))) ≣ d.
Proof.
  hnf; intros x.
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

Lemma list_union_definedVars_renamedApart (F:list (params * stmt)) ra
      (RA:forall n Zs a,
          get F n Zs -> get ra n a -> renamedApart (snd Zs) a)
      (Len:❬F❭ = ❬ra❭)
  : list_union (snd ⊝ getAnn ⊝ ra) [=] list_union (definedVars ⊝ snd ⊝ F).
Proof.
  general induction Len; simpl; eauto.
  norm_lunion. rewrite IHLen; eauto using get.
  rewrite renamedApart_occurVars; eauto using get.
  reflexivity.
Qed.

Lemma forwardF_agree_get (sT:stmt) D `{JoinSemiLattice D} f fr
      (F : 〔params * stmt〕)
      (t : stmt)
      (ZL : 〔params〕)
      (ra : 〔ann (⦃var⦄ * ⦃var⦄)〕)
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
      (RA : forall (n : nat) (Zs : params * stmt) (a : ann (⦃var⦄ * ⦃var⦄)),
          get F n Zs -> get ra n a -> renamedApart (snd Zs) a)
      (fExt:forall (U : ⦃var⦄) (e : exp) (a0 a' : VDom U D),
          a0 ≣ a' -> forall b b' : bool, b ≣ b' -> f U b a0 e ≣ f U b' a' e)
      (frExt:forall (U : ⦃var⦄) (e : op) (a0 a' : VDom U D),
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
      * specialize (EQ z). specialize (EQM z).
    instantiate (3:=(fst (fst (forward f fr ZL ZLIncl (snd x) (STF 0 x (getLB _ _)) AE' y)))) in H6.
    instantiate (1:=(fun (n : nat) (s : params * stmt) (H : get XL n s) =>
                       STF (S n) s (getLS x H))) in H6.
        {
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
                 rewrite <- EQM. specialize (H7 z).
                 eapply H7.
                 revert H8 Disj3.
                 rewrite list_union_definedVars_renamedApart; eauto using get.
                 clear_all; intros. cset_tac.
                 intros.
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
              revert n n0.
              rewrite list_union_definedVars'; eauto.
              rewrite list_union_defVars_decomp; eauto.
              rewrite list_union_definedVars_renamedApart; eauto using get.
              clear_all; cset_tac.
        }
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
        specialize (EQ x). specialize (H1 x).
        rewrite <- EQ. rewrite H1. reflexivity.
      }
      assert (EQF:@forwardF sT (sTDom D) BL (forward f fr ZL ZLIncl) XL YL
                            (fst (fst (forward f fr ZL ZLIncl _ (STF 0 Zs (@getLB (params * stmt) XL Zs)) AE' r)))
                            (fun (n : nat) (s : params * stmt) (H : get XL n s) =>
                               STF (S n) s (getLS Zs H)) ===
                            forwardF BL (forward f fr ZL ZLIncl) XL YL
                            (fst (fst (forward f fr ZL ZLIncl _ ST AE r)))
                            (fun (n : nat) (s : params * stmt) (H : get XL n s) =>
                               STF (S n) s (getLS Zs H))
             ). {
        eapply forwardF_ext'; eauto.
        assert ((STF 0 Zs (@getLB (params * stmt) XL Zs)) = ST) by eapply subTerm_PI.
        subst.
        eapply forward_ext; eauto.
      }
      hnf; intros z.
      exploit (@forward_agree sT _ _ _ f fr ZL AE (singleton z) (snd Zs) ST ZLIncl); eauto using get; dcr.
      exploit (@forwardF_agree sT _ _ _  BL (singleton z) XL f fr YL ZL ZLIncl);
        eauto using get; dcr.
      eauto with len.
      intros. inv_get.
      eapply forward_agree; eauto using get.
      unfold domenv in *.
      instantiate (2:=(fst (fst (forward f fr ZL ZLIncl (snd Zs) ST AE r)))) in H9.
      decide (z ∈ snd (getAnn tra) ∪ list_union (of_list ⊝ ZL)).
      * eapply disj_union_inv in i. destruct i; dcr.
        -- symmetry.
           eapply (H6 z).
           revert H10 H11 Disj2.
           rewrite list_union_definedVars_renamedApart; eauto using get.
           rewrite renamedApart_occurVars; eauto using get.
           clear. intros. cset_tac.
        -- eapply poLe_antisymmetric.
           ++ etransitivity. Transparent poLe.
             eapply (H9 z).
             revert H10 Disj3.
             rewrite list_union_definedVars_renamedApart; eauto using get.
             clear_all. intros; cset_tac.
             rewrite <- (EQM z).
             hnf in EQF. dcr.
             hnf in H5. dcr.
             specialize (H13 z).
             rewrite H13. reflexivity.
           ++ eapply H7.
             rewrite renamedApart_occurVars; eauto using get.
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
           revert n i Disj5 Disj6.
           rewrite renamedApart_occurVars; eauto using get.
           clear_all. intros. cset_tac.
        -- rewrite (H8 z).
           rewrite <- (EQM z).
           hnf in EQF. dcr.
           hnf in H5. dcr.
           specialize (H11 z).
           rewrite H11. reflexivity.
           revert n n0.
           rewrite list_union_defVars_decomp; eauto.
           rewrite list_union_definedVars_renamedApart; eauto using get.
           rewrite list_union_definedVars'; eauto.
           clear_all; cset_tac.
Qed.



Opaque poEq.



Lemma forward_domupdd_eq (sT:stmt) D `{JoinSemiLattice D} ZL ZLIncl s f fr sa v x IN
      (d:VDom (occurVars sT) D) STs (AN:annotation s sa)
      (NOTIN:x ∉ definedVars s ∪ list_union (of_list ⊝ ZL))
      (EQ : fst (fst (forward f fr ZL ZLIncl s STs (@domupdd _ _ d x v IN) sa)) ≣ d)

  : fst (fst (forward f fr ZL ZLIncl s STs (@domupdd _ _ d x v IN) sa))
        ≣ domupdd d v IN.
Proof.
  exploit (@forward_agree sT _ _ _ f fr ZL (domupdd d v IN) (singleton x) s STs ZLIncl); eauto; dcr.
  exploit (H2 x).
  - cset_tac.
  - rewrite EQ.
    eapply domupdd_eq.
    exploit (EQ x).
    rewrite H4 in H1.
    rewrite <- H1. symmetry.
    unfold domenv, domupdd; simpl.
    rewrite domupd_var_eq. reflexivity. reflexivity.
Qed.

Ltac ST_pat :=
  match goal with
  | [ H : context [ forward _ _ _ ?ZLIncl _ ?ST _ _ ] |- _  ] =>
    try (first [ is_var ZLIncl; fail 1
               | let X := fresh "ZLIncl" in set (X:=ZLIncl) in * ]);
    first [ is_var ST; fail 1
          | let X := fresh "ST" in set (X:=ST) in * ]
  | [ H : context [ forwardF _ _ _ _ _ ?STF ] |- _  ] =>
    first [ is_var STF; fail 1
          | let X := fresh "STF" in set (X:=STF) in * ]
  end.

Hint Resolve funConstr_disj_Dt' funConstr_disj_ZL_getAnn disj_Dt_getAnn : ren.

Lemma poEq_refl D `{PartialOrder D} x
  : poEq x x.
Proof.
  reflexivity.
Qed.

Lemma poEq_sym D `{PartialOrder D} x y
  : poEq x y -> poEq y x.
Proof.
  intros. symmetry. eauto.
Qed.

Hint Immediate poEq_refl poEq_sym : po.

Instance join_respects_le A  `{JoinSemiLattice A}
  : Proper (poEq ==> poEq ==> poLe) join.
Proof.
  unfold Proper, respectful; intros.
  rewrite H1, H2. reflexivity.
Qed.

Definition reachability_sound (sT:stmt) D `{JoinSemiLattice D}
           f fr pr ZL BL s (d:VDom (occurVars sT) D) r (ST:subTerm s sT) ZLIncl
           (EQ:(fst (forward f fr ZL ZLIncl s ST d r)) ≣ (d,r)) ra
    (Ann: annotation s r) (RA:renamedApart s ra)
    (DefZL: labelsDefined s (length ZL))
    (DefBL: labelsDefined s (length BL))
    (BL_le: poLe (snd (forward f fr ZL ZLIncl s ST d r)) BL)
    (Disj:disj (list_union (of_list ⊝ ZL)) (snd (getAnn ra)))
    (frExt:forall U e (a a':VDom U D), a ≣ a' ->
        forall b b', b ≣ b' -> fr _ b a e ≣ fr _ b' a' e)
    (fExt:forall (U : ⦃var⦄) (e : exp) (a a' : VDom U D),
        a ≣ a' -> forall b b' : bool, b ≣ b' -> f U b a e ≣ f U b' a' e)
    (frSound1: forall e d r,
        ~ pr d e ⊑ ⎣ wTA false ⎦ -> uceq Sound r (fst (fr (occurVars sT) r d e)))
    (frSound2: forall e d r,
        ~ pr d e ⊑ ⎣ wTA true ⎦ -> uceq Sound r (snd (fr (occurVars sT) r d e)))
  : reachability (pr d) Sound BL s r.
Proof.
  general induction Ann; invt renamedApart; simpl in *; inv DefZL; inv DefBL;
    repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *;
      simpl in *; inv_cleanup.
  - clear_trivial_eqs.
    econstructor; eauto.
    exploit forward_domupdd_eq; eauto.
    rewrite renamedApart_occurVars; eauto. pe_rewrite.
    set_simpl. eapply renamedApart_disj in H6; eauto.
    pe_rewrite. revert Disj H6; clear_all; cset_tac.
    rewrite EQ in H1. symmetry in H1.
    eapply forward_ext in H1; try reflexivity; eauto.
    rewrite H1 in *.
    eapply IHAnn; eauto.
    + split; simpl; eauto.
    + pe_rewrite. eapply disj_2_incl; eauto. cset_tac.
  - clear_trivial_eqs.
    set_simpl.
    exploit (forward_if_inv _ _ _ _ _ _ EQ); eauto.
    repeat rewrite renamedApart_occurVars; eauto;
      pe_rewrite; eauto with cset.
    repeat rewrite renamedApart_occurVars; eauto;
      pe_rewrite; eauto with cset.
    rewrite forward_ext in EQ; try eapply H1; try reflexivity; eauto.
    econstructor; eauto.
    + rewrite <- HEQ0. eapply frSound1.
    + rewrite <- HEQ. eapply frSound2.
    + eapply IHAnn1;
        eauto using @PIR2_zip_join_inv_left with len.
      * split; simpl; eauto.
      * pe_rewrite. eapply disj_2_incl; eauto.
    + eapply IHAnn2;
        eauto using @PIR2_zip_join_inv_left, @PIR2_zip_join_inv_right with len.
      * split; simpl; eauto.
        rewrite forward_ext; eauto.
      * eapply PIR2_zip_join_inv_right.
        rewrite <- BL_le. eapply PIR2_ojoin_zip. reflexivity.
        eapply poLe_refl. eapply forward_ext; eauto.
        symmetry; eauto with len.
      * pe_rewrite. eapply disj_2_incl; eauto.
  - edestruct get_in_range; eauto.
    edestruct get_in_range; try eapply H7; eauto.
    Transparent poLe. hnf in BL_le.
    edestruct PIR2_nth; eauto using ListUpdateAt.list_update_at_get_3; dcr.
    econstructor; simpl; eauto.
  - econstructor.
  - clear_trivial_eqs.
    eapply PIR2_get in H23; try eassumption. clear H22.
    exploit (snd_forwardF_inv _ _ _ _ _ _ _ H23); eauto with len.
    exploit (snd_forwardF_inv' _ _ _ _ _ _ _ H23); eauto with len.
    Transparent poEq. simpl poEq in H23.
    repeat PIR2_eq_simpl. repeat ST_pat.
    Opaque poEq.
    set (FWt:=(forward f fr (fst ⊝ s ++ ZL) ZLIncl0 t ST0 d ta)) in *.
    set (FWF:=forwardF (snd FWt) (forward f fr (fst ⊝ s ++ ZL) ZLIncl0)
                       s sa (fst (fst FWt)) STF) in *.

    assert (fst (fst (FWt)) ≣ d /\
            forall (n : nat) (Zs : params * stmt) (r : ann bool) (ST0 : subTerm (snd Zs) sT),
              get s n Zs ->
              get sa n r ->
              fst
                (fst
                   (forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) (snd Zs) ST0 d r))
                ≣ d). {
      pe_rewrite. set_simpl.
      eapply forwardF_agree_get; eauto. eauto with len.
      rewrite <- EQ. unfold FWF. reflexivity.
      unfold FWt. reflexivity.
      pe_rewrite. eauto with ren.
      pe_rewrite.
      eapply disj_Dt_getAnn; eauto.
      eapply funConstr_disj_ZL_getAnn; eauto.
      eapply disj_1_incl.
      eapply funConstr_disj_ZL_getAnn; eauto.
      rewrite List.map_app. rewrite list_union_app.
      clear_all. cset_tac.
    } dcr.

    assert (forall (n : nat) (r : ann bool) (Zs : params * stmt),
       get sa n r ->
       get s n Zs ->
       forall STZs : subTerm (snd Zs) sT,
         (snd
            (fst
               (forward f fr (fst ⊝ s ++ ZL) ZLIncl0 (snd Zs) STZs d r))) ≣ r). {
      eapply (@snd_forwardF_inv_get) with (BL:=(snd FWt)); eauto.
      subst FWt; eauto with len.
      subst FWt; eauto with len.
      rewrite <- H5 at 2. unfold FWF.
      rewrite forwardF_ext'; try reflexivity; eauto.
    }
    econstructor; eauto.
    + eapply IHAnn; eauto.
      * split; eauto.
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
        set_simpl.
        rewrite List.map_app. rewrite list_union_app.
        eapply disj_union_left.
        -- symmetry.
           eapply funConstr_disj_Dt; eauto.
        -- symmetry. eapply disj_incl; eauto.
    + intros. inv_get. exploit H7; eauto.
      eapply H1; eauto.
      -- split; simpl; eauto.
      -- rewrite (take_eta ❬sa❭) at 1.
         eapply PIR2_app; eauto.
         ++ Transparent poEq.
           unfold poEq in H23. simpl in H23.
           unfold poEq in H23. simpl in H23.
           repeat PIR2_eq_simpl.
           eapply setTopAnn_map_inv in H23.
           rewrite <- H23. eapply PIR2_take.
           change (PIR2 poLe) with (@poLe (list bool) _).
           unfold FWF.
           rewrite forwardF_ext'; eauto; try reflexivity.
           eapply forwardF_PIR2; eauto.
           subst FWt. clear_all. eauto with len.
         ++ etransitivity; eauto.
           rewrite H. eapply PIR2_drop.
           change (PIR2 poLe) with (@poLe (list bool) _).
           unfold FWF.
           rewrite forwardF_ext'; eauto; try reflexivity.
           unfold poEq in H23. simpl in H23.
           unfold poEq in H23. simpl in H23.
           repeat PIR2_eq_simpl.
           eapply forwardF_PIR2; eauto.
           subst FWt. clear_all. eauto with len.
      -- set_simpl.
         eapply disj_2_incl.
         eapply funConstr_disj_ZL_getAnn; eauto with ren.
         eapply incl_list_union; eauto using zip_get.
         Grab Existential Variables.
         eauto.
Qed.
