Require Import Util LengthEq Map Env Exp IL AllInRel Computable Annotation.
Require Import Rename RenamedApart Alpha ILDB SetOperations Status Position.
Import F.

Set Implicit Arguments.
Unset Printing Records.

(** * Properties of Alpha Equivalence and Renamed Apart Programs *)

(** ** Given an renamedApart program, every alpha-equivalent program
       can be obtained as a renaming according to some [rho] *)

Definition alpha_rho_F (alpha_rho:env var -> stmt -> stmt -> env var) :=
  fix f (rho: env var) (F F':list (params*stmt)) : env var :=
    match F, F' with
    | (Z,s)::F, (Z',s')::F' => f (alpha_rho (rho [Z <-- Z']) s s') F F'
    | _, _ => rho
    end.

Fixpoint alpha_rho (rho:env var) (s t:stmt) : env var :=
  match s, t with
  | stmtLet x _ s, stmtLet y _ t => alpha_rho (rho [x <- y]) s t
  | stmtIf _ s1 s2, stmtIf _ t1 t2 => alpha_rho (alpha_rho rho s1 t1) s2 t2
  | stmtApp _ _, stmtApp _ _ => rho
  | stmtReturn _, stmtReturn _ => rho
  | stmtFun F1 s, stmtFun F2 t => alpha_rho (alpha_rho_F alpha_rho rho F1 F2) s t
  | _, _ => rho
  end.

Lemma alpha_rho_agrees_snd_F F F' ans ϱ ϱ' D
  : ( forall (n : nat) (Zs : params * stmt) (a : ann (set var * set var)),
       get F n Zs ->
       get ans n a ->
       forall (u : stmt) (ϱ ϱ' : var -> var) (D0 : set var),
       agree_on eq D0 ϱ ϱ' ->
       agree_on eq D0 (alpha_rho ϱ (snd Zs) u) (alpha_rho ϱ' (snd Zs) u))
    -> (forall (n : nat) (Zs : params * stmt) (a : ann (set var * set var)),
          get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
    -> length F = length ans
    -> agree_on eq D ϱ ϱ'
    -> agree_on eq D (alpha_rho_F alpha_rho ϱ F F') (alpha_rho_F alpha_rho ϱ' F F').
Proof.
  intros AR RA LEN AGR. length_equify.
  general induction LEN; simpl; eauto.
  - destruct x as [Z u], F' as [|[Z' u'] F']; eauto.
    eapply IHLEN; eauto using get.
    + eapply AR with (Zs:=(Z,u)); eauto using get.
      eapply update_with_list_agree_preserve; eauto.
Qed.

Lemma alpha_rho_agrees_snd s u ang ϱ ϱ' D
  : renamedApart s ang
    -> agree_on eq D ϱ ϱ'
    -> agree_on eq D (alpha_rho ϱ s u) (alpha_rho ϱ' s u).
Proof.
  intros RA.
  general induction RA; destruct u; simpl in *; eauto.
  - eapply IHRA. eapply agree_on_update_same; eauto.
    eapply agree_on_incl; eauto.
  - eapply IHRA. eapply alpha_rho_agrees_snd_F; eauto.
Qed.

Lemma alpha_rho_agree_F F F' ans ϱ ϱ' D
  : (forall (n : nat) (Zs : params * stmt) (a : ann (set var * set var)),
       get F n Zs ->
       get ans n a ->
       forall (D0 : set var) (u : stmt) (ϱ ϱ' : var -> var),
       agree_on eq (D0 \ snd (getAnn a)) ϱ ϱ' ->
       agree_on eq (D0 \ snd (getAnn a)) ϱ (alpha_rho ϱ' (snd Zs) u))
    -> (forall (n : nat) (Zs : params * stmt) (a : ann (set var * set var)),
          get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
    -> length F = length ans
    -> agree_on eq (D \ list_union zip defVars F ans) ϱ ϱ'
    -> agree_on eq (D \ list_union zip defVars F ans)
               ϱ (alpha_rho_F alpha_rho ϱ' F F').

Proof.
  intros AR RA LEN AGR. length_equify.
  general induction LEN; simpl.
  + eauto.
  + destruct x as [Z s1], F' as [|[Z' s2] F']; simpl in *; eauto.
    eapply agree_on_incl. eapply IHLEN; eauto using get.
    instantiate (1:=D \ defVars (Z, s1) y).
    eapply agree_on_incl. eapply AR with (Zs:=(Z,s1)); eauto using get.
    symmetry. eapply agree_on_incl. eapply update_with_list_agree_minus; eauto.
    symmetry; eauto.
    instantiate (1:=D \ fold_left union (zip defVars XL YL) ({} ∪ defVars (Z, s1) y) \ of_list Z).
    cset_tac; intuition. unfold defVars at 1. simpl.
    setoid_rewrite list_union_start_swap at 2. unfold defVars at 2.
    simpl.
    * clear_all; cset_tac.
    * rewrite list_union_start_swap. clear_all; cset_tac.
Qed.

Lemma alpha_rho_agree D s u ang ϱ ϱ'
  : renamedApart s ang
    -> agree_on eq (D \ snd (getAnn ang)) ϱ ϱ'
    -> agree_on eq (D \ snd (getAnn ang)) ϱ (alpha_rho ϱ' s u).
Proof.
  intros RA.
  general induction RA; destruct u; simpl; eauto;
    set_simpl; pe_rewrite.
  - eapply agree_on_incl.
    + eapply IHRA.
      symmetry. instantiate (1:=D0 \ singleton x).
      eapply agree_on_update_dead; [ cset_tac | ].
      symmetry. eapply agree_on_incl; cset_tac.
    + cset_tac.
  - eapply agree_on_incl. eapply (IHRA2 (D0 \ Ds)).
    eapply agree_on_incl. eapply (IHRA1 (D0 \ Dt)).
    eapply agree_on_incl; eauto with cset.
    eauto with cset. eauto with cset.
  - pe_rewrite. simpl in *.
    eapply agree_on_incl. eapply IHRA.
    eapply agree_on_incl. eapply alpha_rho_agree_F; eauto.
    eapply agree_on_incl; eauto.
    + instantiate (1:=D0 \ Dt); eauto with cset.
    + instantiate (1:=D0 \ list_union zip defVars F ans).
      eauto with cset.
    + eauto with cset.
Qed.

Lemma alpha_rho_agrees_snd2_F F F' ans ϱ ϱ' D
  : (forall (n : nat) (Zs Zs': params * stmt)  (a : ann (set var * set var)),
       get F n Zs ->
       get ans n a ->
       get F' n Zs' ->
       forall (ϱ ϱ' : var -> var) (D0 : set var),
       agree_on eq (D0 \ definedVars (snd Zs)) ϱ ϱ' ->
       agree_on eq (D0) (alpha_rho ϱ (snd Zs) (snd Zs')) (alpha_rho ϱ' (snd Zs) (snd Zs')))
    ->  (forall (n : nat) (Zs Zs' : params * stmt),
           get F n Zs ->
           get F' n Zs' -> length (fst Zs) = length (fst Zs'))
    -> (forall (n : nat) (Zs : params * stmt) (a : ann (set var * set var)),
          get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
    -> length F = length ans
    -> length F = length F'
    -> agree_on eq (D \ list_union zip defVars F ans) ϱ ϱ'
    -> agree_on eq D (alpha_rho_F alpha_rho ϱ F F') (alpha_rho_F alpha_rho ϱ' F F').
Proof.
  intros AR LENF RA LEN1 LEN2 AGR. length_equify.
  general induction LEN1; inv LEN2; simpl in *; eauto using agree_on_incl with cset.
  - destruct x as [Z u], y0 as [Z' u']; eauto.
    eapply IHLEN1; eauto using get.
    + rewrite list_union_start_swap in AGR.
      exploit (AR 0); eauto using get.
      eapply update_with_list_agree with (XL:=Z) (YL:=Z'); eauto.
      eapply agree_on_incl. eapply AGR.
      unfold defVars at 2. simpl.
      exploit (RA 0); eauto using get.
      rewrite renamedApart_occurVars; eauto.
      cset_tac; intuition. exploit LENF; eauto using get.
Qed.


Lemma list_union_incl {X} `{OrderedType X} (L L':list (set X)) (s s':set X)
: length L = length L'
  -> (forall n s t, get L n s -> get L' n t -> s [<=] t)
  -> s [<=] s'
  -> fold_left union L s [<=] fold_left union L' s'.
Proof.
  intros. length_equify.
  general induction H0; simpl; eauto.
  exploit H1; eauto using get. rewrite H2, H3; eauto using get.
Qed.

Lemma alpha_rho_agrees_snd2 s u ang ϱ ϱ' D ρ ρ'
  : renamedApart s ang
    -> alpha ρ ρ' s u
    -> agree_on eq (D \ definedVars s) ϱ ϱ'
    -> agree_on eq D (alpha_rho ϱ s u) (alpha_rho ϱ' s u).
Proof.
  intros RA ALPHA.
  general induction RA; invt alpha; simpl in *;
  eauto using agree_on_incl, agree_on_update_same with cset.
  - eapply IHRA; eauto. eapply alpha_rho_agrees_snd2_F; eauto using agree_on_incl.
    + eapply agree_on_incl; eauto.
      unfold defVars.
      rewrite renamedApart_occurVars; eauto.
      pe_rewrite. rewrite union_comm. rewrite <- minus_union.
      eapply incl_minus_lr; eauto.
      eapply list_union_incl; eauto with len.
      * intros; inv_get.
        rewrite <- renamedApart_occurVars; eauto.
        eauto with cset.
Qed.

Lemma funConstr_disjoint_defVars F ans D Dt
  : length F = length ans
    -> Indexwise.indexwise_R (funConstr D Dt) F ans
    -> disj (list_union (defVars ⊜ F ans)) Dt.
Proof.
  intros.
  rewrite <- list_union_disjunct; intros; inv_get.
  edestruct H0; dcr; eauto.
Qed.

Require Import Take Drop.

Lemma alpha_rho_agree_F_get D F F' ans ϱ ϱ' n Z Z' u u'
  : (forall (n : nat) (Zs : params * stmt) (a : ann (set var * set var)),
        get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
    -> (forall (n : nat) (Zs Zs' : params * stmt),
                 get F n Zs -> get F' n Zs' -> ❬fst Zs❭ = ❬fst Zs'❭)
    -> length F = length ans
    -> length F = length F'
    -> agree_on eq (D \ list_union (take n (zip defVars F ans))) ϱ ϱ'
    -> get F n (Z, u)
    -> get F' n (Z', u')
    -> agree_on eq (D \ list_union (take n (zip defVars F ans))
                     \ list_union (drop (S n) (zip defVars F ans)))
               (alpha_rho (ϱ [Z <-- Z']) u u') (alpha_rho_F alpha_rho ϱ' F F').

Proof.
  intros RA ZLEN LEN1 LEN2 AGR GetF GetF'. length_equify.
  general induction LEN1; inv LEN2; simpl; [ isabsurd|]; inv GetF; inv GetF'.
  - simpl in *.
    + exploit RA; eauto using get; simpl in *.
      eapply alpha_rho_agree_F; eauto using get, alpha_rho_agree with len.
      eapply alpha_rho_agrees_snd; eauto.
      eapply update_with_list_agree; eauto.
      eapply agree_on_incl; eauto. clear; cset_tac.
      exploit ZLEN; eauto.
  - destruct x as [Z1 s1], y0 as [Z2 s2]; simpl.
    exploit RA; try econstructor. simpl in *.
    eapply agree_on_incl.
    eapply (IHLEN1 (D \ (of_list Z1 ∪ snd (getAnn y)))) ; eauto using get.
    + eapply agree_on_incl.
      eapply alpha_rho_agree; eauto.
      eapply agree_on_incl.
      symmetry. eapply update_with_list_agree_minus; eauto. symmetry; eauto.
      norm_lunion. unfold defVars at 1. simpl.
      instantiate (1:=D \ of_list Z1 \ list_union take n0 (defVars ⊜ XL YL)).
      clear; cset_tac.
      clear; cset_tac.
    + norm_lunion. unfold defVars at 1. simpl.
      clear; cset_tac.
Qed.

Lemma rename_renamedApart_all_alpha s t ang ϱ ϱ'
: renamedApart s ang
  -> alpha ϱ ϱ' s t
  -> rename (alpha_rho ϱ s t) s = t.
Proof.
  intros RA ALPHA.
  intros. general induction ALPHA; invt renamedApart; pe_rewrite; simpl.
  - erewrite op_rename_renamedApart_all_alpha; eauto.
  - f_equal. length_equify.
    revert H H0; clear_all; intros. general induction H; simpl; eauto.
    f_equal.
    + eapply op_rename_renamedApart_all_alpha; eauto using get.
    + eapply IHlength_eq; eauto using get, list_union_cons.
  - exploit IHALPHA; eauto; dcr; pe_rewrite.
    f_equal; eauto.
    + erewrite <- alpha_rho_agree; eauto. instantiate (1:=ra [x <- y]).
      lud; try congruence.
      reflexivity.
      pe_rewrite. eapply renamedApart_disj in H5. pe_rewrite.
      instantiate (1:={x}). specialize (H5 x).
      cset_tac; intuition.
    + eapply exp_rename_renamedApart_all_alpha.
      eapply alpha_exp_agree_on_morph; eauto.
      instantiate (1:=ira). eauto.
      etransitivity. symmetry. eapply agree_on_incl.
      eapply alpha_rho_agree; eauto. reflexivity.
      instantiate (1:=D). pe_rewrite.
      eapply renamedApart_disj in H5. pe_rewrite. eauto with cset.
      eapply agree_on_update_dead; eauto.
  - f_equal.
    + erewrite rename_op_agree. eapply op_rename_renamedApart_all_alpha; eauto.
      symmetry. etransitivity. Focus 2.
      eapply agree_on_incl. eapply alpha_rho_agree; eauto. reflexivity.
      instantiate (1:=D). eapply renamedApart_disj in H7; pe_rewrite.
      eauto with cset.
      eapply agree_on_incl. eapply alpha_rho_agree; eauto.
      instantiate (1:=D). eapply renamedApart_disj in H6; pe_rewrite.
      eauto with cset.
    + erewrite rename_agree; eauto.
      rewrite occurVars_freeVars_definedVars.
      rewrite renamedApart_freeVars; eauto.
      rewrite renamedApart_occurVars; eauto.
      pe_rewrite. symmetry.
      eapply agree_on_incl. eapply alpha_rho_agree; eauto.
      instantiate (1:=D ∪ Ds). pe_rewrite.
      eapply renamedApart_disj in H7. pe_rewrite.
      cset_tac; intuition.
    + erewrite rename_agree; eauto.
      rewrite occurVars_freeVars_definedVars.
      rewrite renamedApart_freeVars; eauto.
      rewrite renamedApart_occurVars; eauto.
      pe_rewrite. symmetry. eapply agree_on_union.
      * eapply agree_on_incl. eapply alpha_rho_agree. eauto.
        instantiate (1:=D \ Ds). pe_rewrite.
        etransitivity. symmetry.
        eapply agree_on_incl. eapply alpha_rho_agree. eauto. reflexivity.
        pe_rewrite. reflexivity.
        eapply agree_on_incl. eapply alpha_rho_agree. eauto. reflexivity.
        pe_rewrite. instantiate (1:=D\Dt). cset_tac; intuition. pe_rewrite.
        eapply renamedApart_disj in H7.
        eapply renamedApart_disj in H6.
        pe_rewrite. eauto with cset.
      * eapply agree_on_incl. eapply alpha_rho_agrees_snd. eauto.
        eapply alpha_rho_agree; eauto. pe_rewrite.
        instantiate (1:=Dt). cset_tac; intuition.
  - exploit IHALPHA; eauto; dcr; pe_rewrite.
    f_equal.
    + eapply map_ext_get_eq; eauto.
      intros. destruct x as [Z u]. inv_get.
      exploit H6; eauto.
      exploit H2; eauto. simpl in *.
      destruct y as [Z' u']; simpl in *. f_equal.
      * erewrite lookup_list_agree.
        instantiate (1:=ra[Z <-- Z']).
        eapply lookup_list_nodup; eauto.
        exploit H0; eauto. edestruct H7; eauto.
        symmetry.
        etransitivity.
        Focus 2.
        eapply agree_on_incl. eapply alpha_rho_agree; eauto.
        eapply agree_on_incl.
        eapply alpha_rho_agree_F_get; eauto. reflexivity.
        instantiate (1:=of_list Z).
        instantiate (1:=of_list Z).
        rewrite minus_union.
        repeat rewrite disj_minus_eq; eauto.
        eapply disj_app; split.
        symmetry. rewrite <- list_union_disjunct; intros; inv_get.
        exploit (H8 n0 n); eauto using zip_get. omega.
        eapply disj_2_incl; eauto. unfold defVars; simpl; eauto with cset.
        symmetry. rewrite <- list_union_disjunct; intros; inv_get.
        exploit (H8 (S n + n0) n); eauto using zip_get. omega.
        eapply disj_2_incl; eauto. unfold defVars; simpl; eauto with cset.

        pe_rewrite. edestruct H7; dcr; eauto with cset.

        pe_rewrite. rewrite disj_minus_eq; eauto.
        edestruct H7; dcr; eauto; simpl in *.
        eapply disj_1_incl; eauto with cset.

        eapply agree_on_incl.
        eapply alpha_rho_agree; eauto.
        instantiate (1:=of_list Z).
        edestruct H7; eauto; dcr; simpl in *.
        eapply renamedApart_disj in H14.
        rewrite H16 in H14.
        rewrite disj_minus_eq; eauto with cset.
      * erewrite rename_agree; eauto.
        symmetry.
        exploit renamedApart_occurVars as OC; eauto.
        exploit renamedApart_freeVars as FV; eauto.
        assert (DISJ:disj (occurVars u) Dt). {
          pe_rewrite. rewrite occurVars_freeVars_definedVars.
          edestruct H7; dcr; eauto; simpl in *.
          symmetry; eapply disj_app; split; symmetry.
          rewrite FV. rewrite H16.
          symmetry; eapply disj_app; split; symmetry. eauto with cset.
          eapply renamedApart_disj in RA. simpl in *.
          eapply disj_2_incl; eauto. rewrite <- H12. eauto with cset.
          rewrite OC. eauto with cset.
        }

        eapply agree_on_incl.
        eapply alpha_rho_agree; eauto.
        eapply agree_on_incl.
        eapply alpha_rho_agree_F_get; eauto.
        instantiate (2:=occurVars u).
        instantiate (1:=occurVars u).

        rewrite minus_union.
        repeat rewrite disj_minus_eq; eauto.
        rewrite occurVars_freeVars_definedVars.
        eapply disj_app; split.
        symmetry. rewrite <- list_union_disjunct; intros; inv_get.
        rewrite (@incl_minus_union2 _ _ (freeVars u) (of_list Z)).
        rewrite union_assoc.
        exploit (H8 n0 n); eauto using zip_get. omega.
        eapply disj_app; split.

        exploit renamedApart_freeVars; try eapply RA; eauto. simpl in *.
        exploit renamedApart_disj; try eapply RA; eauto. simpl in *.
        symmetry. eapply (disj_incl H22).
        rewrite <- H21. eapply incl_union_left, incl_list_union.
        eapply map_get_1; try eapply H4. simpl. reflexivity.
        rewrite <- H12. eapply incl_union_left, incl_list_union; eauto using zip_get.


        rewrite OC. unfold defVars in H20 at 2. simpl in *. eauto.

        symmetry. rewrite <- list_union_disjunct; intros; inv_get.
        rewrite (@incl_minus_union2 _ _ (freeVars u) (of_list Z)).
        rewrite union_assoc.
        eapply disj_app; split.

        exploit renamedApart_freeVars; try eapply RA; eauto. simpl in *.
        exploit renamedApart_disj; try eapply RA; eauto. simpl in *.
        symmetry. eapply (disj_incl H20).
        rewrite <- H19. eapply incl_union_left, incl_list_union.
        eapply map_get_1; try eapply H4. simpl. reflexivity.
        rewrite <- H12. eapply incl_union_left, incl_list_union; eauto using zip_get.

        exploit (H8 (S n + n0) n); eauto using zip_get. omega.
        eapply disj_2_incl; eauto.  unfold defVars. simpl.
        rewrite OC. eauto with cset.

        pe_rewrite; eauto.

        pe_rewrite. rewrite disj_minus_eq; eauto.

    + erewrite rename_agree; eauto.
      eapply alpha_rho_agrees_snd2; eauto.
      eapply agree_on_incl. symmetry.
      eapply alpha_rho_agree_F; eauto using alpha_rho_agree.
      setoid_rewrite disj_minus_eq at 2; [ reflexivity | ].
      eapply disj_incl.
      eapply (renamedApart_disj RA).
      simpl. rewrite occurVars_freeVars_definedVars.
      eapply renamedApart_freeVars in RA. simpl in *.
      rewrite <- RA. clear_all; cset_tac.
      simpl. rewrite <- H12. eauto with cset.
Qed.


(** ** Alpha Equivalent programs map to identical De-Bruijn terms *)

Lemma op_alpha_real ϱ ϱ' e e' symb symb'
: alpha_op ϱ ϱ' e e'
  -> (forall x y, ϱ x = y -> ϱ' y = x -> pos symb x 0 = pos symb' y 0)
  -> exp_idx symb e = exp_idx symb' e'.
Proof.
  intros. general induction H; simpl in * |- *; eauto.
  - erewrite H1; eauto.
  - erewrite IHalpha_op; intros; eauto.
  - erewrite IHalpha_op1; eauto with cset.
    erewrite IHalpha_op2; eauto with cset.
Qed.

Lemma alpha_real ϱ ϱ' s t symb symb'
: alpha ϱ ϱ' s t
  -> (forall x y, ϱ x = y -> ϱ' y = x -> pos symb x 0 = pos symb' y 0)
  -> stmt_idx symb s = stmt_idx symb' t.
Proof.
  intros. general induction H; simpl in * |- *.
  - erewrite op_alpha_real; eauto.
  - erewrite smap_agree_2; eauto.
    intros; erewrite op_alpha_real; eauto.
  - inv H.
    + erewrite op_alpha_real; eauto with cset.
      case_eq (exp_idx symb' e'0); intros; simpl; eauto.
      erewrite IHalpha; eauto with cset.
      simpl; intros.
      lud; repeat cases; try congruence.
      exploit H1; try eapply H5; eauto. eapply pos_inc with (k':=1); eauto.
    + erewrite smap_agree_2; eauto; [| intros; erewrite op_alpha_real; eauto].
      erewrite IHalpha; eauto.
      simpl; intros.
      lud; repeat cases; try congruence.
      exploit H1; try eapply H5; eauto. eapply pos_inc with (k':=1); eauto.
  - erewrite op_alpha_real; eauto with cset.
    erewrite IHalpha1; eauto with cset.
    erewrite IHalpha2; eauto with cset.
  - erewrite IHalpha; eauto with cset.
    erewrite smap_agree_2; eauto.
    intros m [Z u] [Z' u'] ? ?. erewrite H0; eauto.
    erewrite H2; eauto.
    intros.
    exploit H0; eauto. simpl in *.
    decide (x ∈ of_list Z).
    + edestruct (of_list_get_first _ i) as [n]; eauto; dcr.
      hnf in H11. subst x0.
      rewrite pos_app_in; eauto.
      exploit (update_with_list_lookup_in_list_first ra _ H9 H12 H14); eauto; dcr.
      assert (x0 = y) by congruence. subst x0. clear_dup.
      rewrite H7 in H13.
      edestruct (list_lookup_in_list_first _ _ Z (eq_sym H9) H8) as [n'];
        eauto using get_in_of_list; dcr.
      hnf in H11; subst x0.
      rewrite pos_app_in; eauto.
      decide (n < n'). now exfalso; exploit H17; eauto.
      decide (n' < n). now exfalso; exploit H14; eauto.
      assert (n = n') by omega. subst n'.
      repeat erewrite get_first_pos; eauto.
      eapply get_in_of_list; eauto.
    + exploit (update_with_list_lookup_not_in ra Z Z' y n); eauto.
      assert ((ira [Z' <-- Z]) y ∉ of_list Z). rewrite H8; eauto.
      eapply lookup_set_update_not_in_Z'_not_in_Z in H11; eauto.
      repeat rewrite pos_app_not_in; eauto.
      exploit (update_with_list_lookup_not_in ira Z' Z x H11); eauto.
      rewrite H9. eapply pos_inc; eauto.
Qed.
