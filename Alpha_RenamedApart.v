Require Import Util Map Env EnvTy Exp IL AllInRel Bisim Computable Annotation.
Require Import Rename RenamedApart Alpha ILDB SetOperations.
Import F.

Set Implicit Arguments.
Unset Printing Records.

(** * Properties of Alpha Equivalence and Renamed Apart Programs *)

(** ** Definition of [combine] *)

Definition combine X `{OrderedType X} Y (D:set X) (ϱ ϱ':X->Y) x :=
  if [x ∈ D] then ϱ x else ϱ' x.

Lemma combine_agree X `{OrderedType X} Y (D:set X) (ϱ ϱ':X->Y)
: agree_on eq D ϱ (combine D ϱ ϱ').
Proof.
  unfold combine; hnf; intros; simpl.
  cases; eauto.
Qed.

Lemma combine_agree' X `{OrderedType X} Y (D D':set X) (ϱ ϱ':X->Y)
: disj D D' -> agree_on eq D ϱ' (combine D' ϱ ϱ').
Proof.
  intros. unfold combine; hnf; intros; simpl.
  cases; eauto.
Qed.

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
  | stmtExtern x _ _ s, stmtExtern y _ _ t => alpha_rho (rho[x <- y]) s t
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
  general induction RA; destruct u; simpl; eauto.
  - pe_rewrite; simpl in *. rewrite H1 in *.
    eapply agree_on_incl.
    + eapply IHRA.
      symmetry. instantiate (1:=D0 \ singleton x).
      eapply agree_on_update_dead; [ cset_tac | ].
      symmetry. eapply agree_on_incl; cset_tac.
    + cset_tac.
  - simpl in *. rewrite <- H1 in *.
    pe_rewrite.
    eapply agree_on_incl. eapply (IHRA2 (D0 \ Ds)).
    eapply agree_on_incl. eapply (IHRA1 (D0 \ Dt)).
    eapply agree_on_incl; eauto with cset.
    cset_tac; intuition. cset_tac; intuition.
  - pe_rewrite. rewrite H1 in *. simpl in *.
    eapply agree_on_incl. eapply IHRA.
    symmetry. instantiate (1:=D0 \ singleton x).
    eapply agree_on_update_dead; [| symmetry; eauto].
    cset_tac; intuition. eapply agree_on_incl; eauto.
    clear_all; cset_tac; intuition.
    clear_all; cset_tac; intuition.
  - pe_rewrite. simpl in *.
    eapply agree_on_incl. eapply IHRA.
    eapply agree_on_incl. eapply alpha_rho_agree_F; eauto.
    eapply agree_on_incl; eauto. rewrite <- H5.
    instantiate (1:=D0 \ Dt). cset_tac; intuition.
    instantiate (1:=D0 \ list_union zip defVars F ans). cset_tac; intuition.
    rewrite <- H5. cset_tac; intuition.
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
      eapply list_union_incl; eauto.
      * rewrite map_length, zip_length2; eauto.
      * intros. inv_map H7. inv_zip H8. repeat get_functional; subst.
        rewrite <- renamedApart_occurVars; eauto. cset_tac; intuition.
Qed.

Lemma rename_renamedApart_all_alpha s t ang ϱ ϱ'
: renamedApart s ang
  -> alpha ϱ ϱ' s t
  -> rename (alpha_rho ϱ s t) s = t.
Proof.
  intros RA ALPHA.
  intros. general induction ALPHA; invt renamedApart; pe_rewrite; simpl.
  - erewrite exp_rename_renamedApart_all_alpha; eauto.
  - f_equal. length_equify.
    revert H H0; clear_all; intros. general induction H; simpl; eauto.
    f_equal.
    + eapply exp_rename_renamedApart_all_alpha; eauto using get.
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
    + erewrite rename_exp_agree. eapply exp_rename_renamedApart_all_alpha; eauto.
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
    f_equal; eauto.
    + erewrite <- alpha_rho_agree; eauto. instantiate (1:=ra [x <- y]). lud; try congruence.
      reflexivity.
      pe_rewrite. eapply renamedApart_disj in H8. pe_rewrite.
      instantiate (1:={x}). specialize (H8 x).
      cset_tac; intuition.
    + eapply map_ext_get_eq; eauto.
      intros.
      erewrite rename_exp_agree; eauto.
      eapply exp_rename_renamedApart_all_alpha; eauto using get.
      symmetry.
      pose proof (renamedApart_disj H8); eauto. pe_rewrite.
      eapply agree_on_incl. eapply alpha_rho_agree; eauto.
      symmetry. eapply agree_on_incl. eapply agree_on_update_dead; eauto.
      pe_rewrite. instantiate (1:=D). eauto with cset.
      rewrite <- H6. pe_rewrite.
      etransitivity. erewrite incl_list_union. reflexivity.
      eapply map_get_1. eapply H2. reflexivity. instantiate (1:={}).
      eapply not_incl_minus; eauto.
      rewrite H6. unfold disj in *. cset_tac; eauto.
  - exploit IHALPHA; eauto; dcr; pe_rewrite.
    f_equal.
    + eapply map_ext_get_eq; eauto.
      intros. destruct x as [Z u].
      edestruct (get_length_eq _ H4 H5); eauto.
      exploit H6; eauto.
      exploit H2; eauto. simpl in *.
      destruct y. f_equal.
      * simpl in *. admit.
      * simpl in *.
(*        erewrite rename_agree; eauto.
        eapply agree_on_incl.
        etransitivity.
        symmetry.
        eapply alpha_rho_agree. eauto.
        instantiate (2:=occurVars u).
        eapply agree_on_incl. eapply alpha_rho_agree_F; eauto.
        intros. edestruct H7; eauto; dcr.
        eapply alpha_rho_agree; eauto.
        Focus 3. eapply agree_on_incl. eapply alpha_rho_agree. eauto.
        eapply agree_on_incl. symmetry. eapply update_with_list_agree_minus. eauto.
        reflexivity.
        shelve. shelve. reflexivity.

        eapply alpha_rho_agrees_snd2_F; eauto.
        intros. eapply alpha_rho_agrees_snd2. eauto. eauto. eauto.*)
        admit.
    + erewrite rename_agree; eauto.
      eapply agree_on_incl.
      eapply alpha_rho_agrees_snd2; eauto with cset.
Admitted.


(** ** Alpha Equivalent programs map to identical De-Bruijn terms *)

Lemma exp_alpha_real ϱ ϱ' e e' symb symb'
: alpha_exp ϱ ϱ' e e'
  -> (forall x y, ϱ x = y -> ϱ' y = x -> pos symb x 0 = pos symb' y 0)
  -> exp_idx symb e = exp_idx symb' e'.
Proof.
  intros. general induction H; simpl in * |- *; eauto.
  - erewrite H1; eauto.
  - erewrite IHalpha_exp; intros; eauto.
  - erewrite IHalpha_exp1; eauto with cset.
    erewrite IHalpha_exp2; eauto with cset.
Qed.

Lemma alpha_real ϱ ϱ' s t symb symb'
: alpha ϱ ϱ' s t
  -> (forall x y, ϱ x = y -> ϱ' y = x -> pos symb x 0 = pos symb' y 0)
  -> stmt_idx symb s = stmt_idx symb' t.
Proof.
  intros. general induction H; simpl in * |- *.
  - erewrite exp_alpha_real; eauto.
  - erewrite smap_agree_2; eauto.
    intros; erewrite exp_alpha_real; eauto.
  - erewrite exp_alpha_real; eauto with cset.
    case_eq (exp_idx symb' e'); intros; simpl; eauto.
    erewrite IHalpha; eauto with cset.
    simpl; intros.
    lud; repeat cases; try congruence.
    exploit H1; eauto. eapply pos_inc with (k':=1); eauto.
  - erewrite exp_alpha_real; eauto with cset.
    erewrite IHalpha1; eauto with cset.
    erewrite IHalpha2; eauto with cset.
  - erewrite smap_agree_2; eauto; [| intros; erewrite exp_alpha_real; eauto].
    erewrite IHalpha; eauto.
    simpl; intros.
    lud; repeat cases; try congruence.
    exploit H1; eauto. eapply pos_inc with (k':=1); eauto.
  - erewrite IHalpha; eauto with cset.
    erewrite smap_agree_2; eauto.
    intros m [Z u] [Z' u'] ? ?. erewrite H0; eauto.
    erewrite H2; eauto.
    intros.
    exploit H0; eauto. simpl in *.
    decide (x ∈ of_list Z).
    + edestruct (of_list_get_first _ i) as [n]; eauto. dcr. hnf in H11. subst x0.
      rewrite pos_app_in; eauto.
      exploit (update_with_list_lookup_in_list_first ra _ H9 H12 H14); eauto; dcr.
      assert (x0 = y) by congruence. subst x0. clear_dup.
      edestruct (list_lookup_in_list_first _ _ _ (eq_sym H9) H8) as [n'];
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
