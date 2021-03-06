Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map CMap Status Take Filter.
Require Import Val Var Envs IL Annotation Liveness.Liveness MoreList SetOperations PairwiseDisjoint.
Require Import Coherence Coherence.Allocation RenamedApart MapNotations InfinitePartition StableFresh.

Set Implicit Arguments.

(** * SSA-based register assignment formulated for IL *)

Lemma injective_on_update_cmap_fresh (p:inf_partition var) o lv x (ϱ:Map[var, var])
      (inj : injective_on (lv \ singleton x) (findt ϱ default_var))
  : injective_on lv
                 (findt (ϱ [-x <- least_fresh_part p o
                               (lookup_set (findt ϱ default_var) (lv \ singleton x)) x -]) default_var).
Proof.
  eapply injective_on_agree; [| eapply map_update_update_agree].
  eapply injective_on_incl.
  eapply injective_on_fresh; eauto using injective_on_incl.
  eapply least_fresh_part_fresh; eauto.
  eauto with cset.
Qed.

Definition regAssignF p (spill_oracle: var -> var)
           (regAssign : stmt -> ann (set var) -> Map [var, var] -> status (Map [var, var]))
  := fix regAssignF
           (ϱ:Map [var, var]) (F:list (list var * stmt)) (ans: list (ann (set var)))
: status (Map [var, var]) :=
  match F, ans with
    | Zs::F, a::ans =>
      let Z := fst Zs in let s := snd Zs in
      let Z' := fst (fresh_list_stable (stable_fresh_part p spill_oracle) (SetConstructs.map (findt ϱ default_var) (getAnn a\of_list Z)) Z) in
      sdo ϱ' <- regAssign s a (ϱ[- Z <-- Z'-]);
        regAssignF ϱ' F ans

    | _, _ => Success ϱ
  end.

Fixpoint regAssign p (spill_oracle: var -> var) (st:stmt) (an: ann (set var)) (ϱ:Map [var, var])
  : status (Map [var, var]) :=
 match st, an with
    | stmtLet x e s, ann1 lv ans =>
      let xv := least_fresh_part p spill_oracle (SetConstructs.map (findt ϱ default_var) (getAnn ans\ singleton x)) x
      in regAssign p spill_oracle s ans (ϱ[- x <- xv -])
    | stmtIf _ s t, ann2 lv ans ant =>
      sdo ϱ' <- regAssign p spill_oracle s ans ϱ;
        regAssign p spill_oracle t ant ϱ'
    | stmtApp _ _, ann0 _ => Success ϱ
    | stmtReturn _, ann0 _ => Success ϱ
    | stmtFun F t, annF _ ans ant =>
      sdo ϱ' <- regAssignF p spill_oracle (regAssign p spill_oracle) ϱ F ans;
        regAssign p spill_oracle t ant ϱ'
    | _, _ => Error "regAssign: Annotation mismatch"
 end.

(** The algorithm only changes bound variables in the mapping [ϱ] *)

Lemma regAssign_renamedApart_agreeF' c o G F ans als ϱ ϱ'
      (allocOK:regAssignF c o (regAssign c o) ϱ F als = Success ϱ')
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
               regAssign c o (snd Zs) a ϱ0 = Success ϱ'0 ->
               agree_on eq (G0 \ snd (getAnn al)) (findt ϱ0 default_var) (findt ϱ'0 default_var)))
: forall G' : set var,
    list_union zip defVars F ans[<=]G' ->
    agree_on eq (G \ G') (findt ϱ default_var) (findt ϱ' default_var).
Proof.
 intros G' INCL.
 length_equify. general induction LEN1; simpl in * |- *; try monadS_inv allocOK; eauto.
 exploit IHLEN1; eauto using get.
 - etransitivity; try eapply INCL.
   norm_lunion. eauto with cset.
 - exploit IH; eauto using get.
   (rewrite <- map_update_list_update_agree in H0; eauto with len).
   etransitivity; try eapply H.
   eapply agree_on_incl.
   eapply update_with_list_agree_inv; try eapply H0; eauto with len.
   instantiate (1:=G). rewrite minus_union.
   eapply incl_minus_lr; eauto.
   erewrite <- INCL. norm_lunion. unfold defVars. eauto with cset.
Qed.


Lemma regAssign_renamedApart_agree' c o i s al ϱ ϱ' ZL Lv alv G
      (allocOK:regAssign c o s alv ϱ = Success ϱ')
      (sd:renamedApart s al)
      (LS:live_sound i ZL Lv s alv)
: agree_on eq (G \ snd (getAnn al)) (findt ϱ default_var) (findt ϱ' default_var).
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
  - exploit IHLS; eauto. instantiate (1:=G) in H4.
    pe_rewrite.
    etransitivity; [| eapply agree_on_incl; try eapply H4].
    eapply agree_on_incl.
    eapply regAssign_renamedApart_agreeF' with (G':=D'); try eassumption; eauto.
    rewrite <- H13. cset_tac; intuition. reflexivity.
    eapply incl_minus_lr; try reflexivity. rewrite <- H13. eauto with cset.
Qed.

Lemma regAssign_renamedApart_agree c o i s al ϱ ϱ' ZL Lv alv
      (allocOK:regAssign c o s alv ϱ = Success ϱ')
      (sd:renamedApart s al)
      (LS:live_sound i ZL Lv s alv)
: agree_on eq (fst (getAnn al)) (findt ϱ default_var) (findt ϱ' default_var).
Proof.
  eapply agree_on_incl.
  eapply regAssign_renamedApart_agree'; eauto.
  instantiate (1:=fst (getAnn al)).
  exploit renamedApart_disj; eauto.
  revert H. unfold disj.
  clear_all; cset_tac; intuition; eauto.
Qed.

Lemma regAssignF_get p o G F ans alv n Zs a ϱ ϱ' an ZL Lv i D Dt lv
: regAssignF p o (regAssign p o) ϱ F alv = Success ϱ'
  -> (forall n Zs a, get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
  -> (forall n Zs a, get F n Zs ->
               get alv n a ->
               live_sound i ZL Lv (snd Zs) a)
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
  -> exists ϱ1 ϱ2, regAssign p o (snd Zs) a ϱ1 = Success ϱ2
             /\ regAssignF p o (regAssign p o) ϱ2 (drop (S n) F) (drop (S n) alv) = Success ϱ'
             /\ agree_on eq (G \ list_union (zip defVars (take n F) (take n ans)))
                        (findt (ϱ[-fst Zs <-- fst (fresh_list_stable (stable_fresh_part p o)
                                      (SetConstructs.map (findt ϱ default_var) (getAnn a \ of_list (fst Zs)))
                                      (fst Zs))-]) default_var)
                        (findt ϱ1 default_var).

Proof.
  intros EQ REN LV LVINC DDISJ FUNC PWDISJ GET1 GET2 GET3 incl.
  general induction GET1; try inv GET2; try inv GET3; simpl in * |- *; monadS_inv EQ; eauto.
  - exploit (IHGET1 p o G); hnf; intros; eauto using get; dcr.
    do 2 eexists; split; eauto. split; eauto.
    etransitivity; eapply agree_on_incl; [ | reflexivity | eassumption | eauto ].
    + repeat rewrite <- map_update_list_update_agree; eauto with len.
      erewrite least_fresh_list_part_ext; eauto.
      * eapply update_with_list_agree; eauto with len.
        eapply regAssign_renamedApart_agree' in EQ0; eauto using get.
        rewrite <- map_update_list_update_agree in EQ0; eauto with len.
        eapply update_with_list_agree_inv in EQ0; eauto with len.
        eapply agree_on_incl. eauto.
        instantiate (1:=G \ list_union zip defVars (take n xl) (take n xl1)).
        norm_lunion. unfold defVars at 1. clear_all; cset_tac; intuition.
      * eapply lookup_set_agree; eauto.
        eapply regAssign_renamedApart_agree' in EQ0; eauto using get.
        rewrite <- map_update_list_update_agree in EQ0; eauto with len.
        eapply update_with_list_agree_inv in EQ0; eauto with len.
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
