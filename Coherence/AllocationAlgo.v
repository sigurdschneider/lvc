Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map CMap Status Take.
Require Import Val Var Env EnvTy IL Annotation Liveness Fresh MoreList SetOperations PairwiseDisjoint.
Require Import Coherence Allocation RenamedApart.

Set Implicit Arguments.

(** * SSA-based register assignment formulated for IL *)


Definition regAssignF
           (regAssign : stmt -> ann (set var) -> Map [var, var] -> status (Map [var, var]))
  := fix regAssignF
           (ϱ:Map [var, var]) (F:list (list var * stmt)) (ans: list (ann (set var)))
: status (Map [var, var]) :=
  match F, ans with
    | Zs::F, a::ans =>
      let Z := fst Zs in let s := snd Zs in
      let Z' := fresh_list least_fresh (SetConstructs.map (findt ϱ 0) (getAnn a\of_list Z)) (length Z) in
      sdo ϱ' <- regAssign s a (ϱ[- Z <-- Z'-]);
        regAssignF ϱ' F ans

    | nil, nil => Success ϱ
    | _, _ => Error "regAssignF: function annotation mismatch"
  end.

Fixpoint regAssign (st:stmt) (an: ann (set var)) (ϱ:Map [var, var])
  : status (Map [var, var]) :=
 match st, an with
    | stmtLet x e s, ann1 lv ans =>
      let xv := least_fresh (SetConstructs.map (findt ϱ 0) (getAnn ans\ singleton x)) in
        regAssign s ans (ϱ[- x <- xv -])
    | stmtIf _ s t, ann2 lv ans ant =>
      sdo ϱ' <- regAssign s ans ϱ;
        regAssign t ant ϱ'
    | stmtApp _ _, ann0 _ => Success ϱ
    | stmtReturn _, ann0 _ => Success ϱ
    | stmtExtern x f Y s, ann1 lv ans =>
      let xv := least_fresh (SetConstructs.map (findt ϱ 0) (getAnn ans\ singleton x)) in
      regAssign s ans (ϱ[- x <- xv -])
    | stmtFun F t, annF _ ans ant =>
      sdo ϱ' <- regAssignF regAssign ϱ F ans;
        regAssign t ant ϱ'
    | _, _ => Error "regAssign: Annotation mismatch"
 end.

(** The algorithm only changes bound variables in the mapping [ϱ] *)

Lemma regAssign_renamedApart_agreeF G F ans als ϱ ϱ'
      (allocOK:regAssignF regAssign ϱ F als = Success ϱ')
      (REN:forall (n : nat) (Zs : params * stmt) (a : ann (set var * set var)),
             get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
      (LEN1:length F = length als)
      (LEN2:length F = length ans)
      (IH:(forall (n : nat) (Zs : params * stmt) (a : ann (set var)),
             get F n Zs ->
             get als n a ->
             forall (al : ann (set var * set var)) (ϱ0 ϱ'0 : Map  [var, var])
               (G0 : set var),
               renamedApart (snd Zs) al ->
               regAssign (snd Zs) a ϱ0 = Success ϱ'0 ->
               agree_on eq (G0 \ snd (getAnn al)) (findt ϱ0 0) (findt ϱ'0 0)))
: forall G' : set var,
    list_union zip defVars F ans[<=]G' ->
    agree_on eq (G \ G') (findt ϱ 0) (findt ϱ' 0).
Proof.
 intros G' INCL.
 length_equify. general induction LEN1; inv LEN2; simpl in * |- *; try monadS_inv allocOK; eauto.
 exploit IHLEN1; eauto using get.
 etransitivity; try eapply INCL.
 norm_lunion. eauto with cset.
 exploit IH; eauto using get.
 (rewrite <- map_update_list_update_agree in H0; eauto).
 etransitivity; try eapply H.
 eapply agree_on_incl.
 eapply update_with_list_agree_inv; try eapply X; eauto.
 instantiate (1:=G). rewrite minus_union.
 eapply incl_minus_lr; eauto.
 erewrite <- INCL. norm_lunion. unfold defVars. eauto with cset.
Qed.


Lemma regAssign_renamedApart_agree' i s al ϱ ϱ' LV alv G
      (allocOK:regAssign s alv ϱ = Success ϱ')
      (sd:renamedApart s al)
      (LS:live_sound i LV s alv)
: agree_on eq (G \ snd (getAnn al)) (findt ϱ 0) (findt ϱ' 0).
Proof.
  general induction LS; inv sd; simpl in * |- *; try monadS_inv allocOK; eauto.
  - exploit IHLS; eauto.
    rewrite <- map_update_update_agree in H2.
    eapply agree_on_incl.
    eapply agree_on_update_inv.
    eapply H2.
    instantiate (1:=G). rewrite H10, H9. simpl.
    revert H5; clear_all; cset_tac; intuition; eauto.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    rewrite H11 in H2. rewrite H12 in H3. simpl in *.
    etransitivity; eapply agree_on_incl; eauto.
    instantiate (1:=G). rewrite <- H7. clear_all; intro; cset_tac; intuition.
    instantiate (1:=G). rewrite <- H7. clear_all; intro; cset_tac; intuition.
  - exploit IHLS; eauto.
    rewrite <- map_update_update_agree in H2.
    eapply agree_on_incl.
    eapply agree_on_update_inv. eapply H2.
    rewrite H10, H11. instantiate (1:=G). simpl.
    revert H6; clear_all; cset_tac; intuition.
  - exploit IHLS; eauto. instantiate (1:=G) in H4.
    pe_rewrite.
    etransitivity; [| eapply agree_on_incl; try eapply H4].
    eapply agree_on_incl.
    eapply regAssign_renamedApart_agreeF with (G':=D'); try eassumption; eauto.
    rewrite <- H13. cset_tac; intuition. reflexivity.
    eapply incl_minus_lr; try reflexivity. rewrite <- H13. eauto with cset.
Qed.

Lemma regAssign_renamedApart_agree i s al ϱ ϱ' LV alv
      (sd:renamedApart s al)
      (LS:live_sound i LV s alv)
      (allocOK:regAssign s alv ϱ = Success ϱ')
: agree_on eq (fst (getAnn al)) (findt ϱ 0) (findt ϱ' 0).
Proof.
  eapply agree_on_incl.
  eapply regAssign_renamedApart_agree'; eauto.
  instantiate (1:=fst (getAnn al)).
  exploit renamedApart_disj; eauto.
  revert H. unfold disj.
  clear_all; cset_tac; intuition; eauto.
Qed.

Lemma regAssignF_get G F ans alv n Zs a ϱ ϱ' an Lv i D Dt lv
: regAssignF regAssign ϱ F alv = Success ϱ'
  -> (forall n Zs a, get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
  -> (forall n Zs a, get F n Zs ->
               get alv n a ->
               live_sound i Lv (snd Zs) a)
  -> (forall (n : nat) (Zs : params * stmt) (a : ann (set var)),
       get F n Zs ->
       get alv n a ->
       of_list (fst Zs)[<=]getAnn a /\ getAnn a \ of_list (fst Zs)[<=]lv)
  -> (forall n Zs a, get F n Zs -> get ans n a -> disj D (defVars Zs a))
  -> Indexwise.indexwise_R (funConstr D Dt) F ans
  -> pairwise_ne disj (zip defVars F ans)
  -> get F n Zs
  -> get alv n a
  -> get ans n an
  -> lv ⊆ D
  -> exists ϱ1 ϱ2, regAssign (snd Zs) a ϱ1 = Success ϱ2
             /\ regAssignF regAssign ϱ2 (drop (S n) F) (drop (S n) alv) = Success ϱ'
             /\ agree_on eq (G \ list_union (zip defVars (take n F) (take n ans)))
                        (findt (ϱ[-fst Zs <-- fresh_list least_fresh
                                      (SetConstructs.map (findt ϱ 0) (getAnn a \ of_list (fst Zs)))
                                      (length (fst Zs))-]) 0)
                        (findt ϱ1 0).
Proof.
  intros EQ REN LV LVINC DDISJ FUNC PWDISJ GET1 GET2 GET3 incl.
  general induction GET1; inv GET2; inv GET3; simpl in * |- *; monadS_inv EQ; eauto.
  - do 2 eexists; split; eauto. split. rewrite EQ0. reflexivity. reflexivity.
  - exploit (IHGET1 G); hnf; intros; eauto using get; dcr.
    do 2 eexists; split; eauto. split; eauto.
    rewrite EQ0. simpl. rewrite EQ1; eauto.
    etransitivity; eapply agree_on_incl; [ | reflexivity | eassumption | eauto ].
    + repeat rewrite <- map_update_list_update_agree; eauto.
      erewrite least_fresh_list_ext; eauto.
      * eapply update_with_list_agree; eauto.
        eapply regAssign_renamedApart_agree' in EQ0; eauto using get.
        rewrite <- map_update_list_update_agree in EQ0; eauto.
        eapply update_with_list_agree_inv in EQ0; eauto.
        eapply agree_on_incl. eauto.
        instantiate (1:=G \ list_union zip defVars (take n xl) (take n xl1)).
        norm_lunion. unfold defVars at 1. clear_all; cset_tac; intuition.
      * eapply lookup_set_agree; eauto.
        eapply regAssign_renamedApart_agree' in EQ0; eauto using get.
        rewrite <- map_update_list_update_agree in EQ0; eauto.
        eapply update_with_list_agree_inv in EQ0; eauto.
        eapply agree_on_incl; eauto.
        instantiate (1:=getAnn a \ of_list (fst x)).
        setoid_rewrite minus_union at 1.
        assert (disj (getAnn a \ of_list (fst x)) (snd (getAnn x'1)
                                                       ∪ of_list (fst x'))).
        {
          exploit PWDISJ;
          [| eauto using get| econstructor 2; eapply zip_get; eauto|].
          omega. unfold defVars in H.
          exploit (LVINC (S n)); eauto using get; dcr.
          rewrite H7. rewrite incl. rewrite union_comm.
          eapply DDISJ; eauto using get.
        }
        setoid_rewrite disj_minus_eq at 2; eauto.
    + norm_lunion. clear_all; cset_tac; intuition.
Qed.

Lemma defVars_take_disj F ans n Zs a
:  pairwise_ne disj (zip defVars F ans)
   -> get F n Zs
   -> get ans n a
   -> disj (defVars Zs a) (list_union zip defVars (take n F) (take n ans)).
Proof.
  intros.
  symmetry. rewrite <- list_union_disjunct; intros; inv_get.
  eapply (H n0 n); eauto using zip_get. omega.
Qed.

Lemma defVars_drop_disj F ans n Zs a
:  pairwise_ne disj (zip defVars F ans)
   -> get F n Zs
   -> get ans n a
   -> disj (defVars Zs a) (list_union zip defVars (drop (S n) F) (drop (S n) ans)).
Proof.
  intros.
  symmetry. rewrite <- list_union_disjunct; intros; inv_get.
  eapply (H (S n + n0) n); eauto using zip_get. omega.
Qed.

Lemma defVars_disj_D F ans D Dt D'
      (D'def:list_union zip defVars F ans ∪ Dt[=]D')
      (Ddisj: disj D D')
: forall n  DD' Zs, get F n Zs -> get ans n DD' ->
               disj D (defVars Zs DD').
Proof.
  intros.
  eapply disj_2_incl; eauto. rewrite <- D'def.
  eapply incl_union_left. eapply incl_list_union; eauto using zip_get.
Qed.
