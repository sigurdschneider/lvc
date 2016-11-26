Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map CMap Status Take Filter.
Require Import Val Var Env IL Annotation Liveness Fresh MoreList SetOperations PairwiseDisjoint.
Require Import Coherence Allocation RenamedApart MapNotations.

Set Implicit Arguments.

(** * SSA-based register assignment formulated for IL *)


Definition least_fresh_P (c : var) (G:set var) x :=
  if [ x <= c ] then least_fresh G else x.

Lemma least_fresh_P_spec c G x
  : (~ x <= c -> x ∉ G)
    -> least_fresh_P c G x ∉ G.
Proof.
  unfold least_fresh_P; cases; eauto using least_fresh_spec.
Qed.

Lemma least_fresh_P_gt c G x
  : ~ x <= c
    -> least_fresh_P c G x = x.
Proof.
  intros; unfold least_fresh_P; cases; try omega; eauto.
Qed.

Lemma least_fresh_P_le c G x
  : x <= c
    -> least_fresh_P c G x = least_fresh G.
Proof.
  intros; unfold least_fresh_P; cases; try omega; eauto.
Qed.

Lemma lt_minus_lt x y z
  : x < y - z -> x < y.
  omega.
Qed.

Definition crd c (G:set var) (L:list var) :=
SetInterface.cardinal (filter (fun x0 : nat => if [x0 <= c] then true else false) G) <
c - SetInterface.cardinal (of_list (List.filter (fun x0 : nat => if [x0 <= c] then true else false) L)).


Lemma decons_noext c G x xl
  : crd c G (x::xl) -> crd c G xl.
Proof.
  unfold crd; intros Card. simpl in *. cases in Card; simpl in *.
  - decide (x ∈ of_list (List.filter (fun x0 : nat => if [x0 <= c] then true else false) xl)).
    + rewrite add_cardinal_1 in Card. unfold var in *. omega. eauto.
    + rewrite add_cardinal_2 in Card. unfold var in *. omega. eauto.
  - eauto.
Qed.

Lemma least_fresh_filter_small c G
      (Card:SetInterface.cardinal (filter (fun x : nat => if [x <= c] then true else false) G) < c)
: least_fresh G <= SetInterface.cardinal (filter (fun x : nat => if [x <= c] then true else false) G).
Proof.
  set (F:=(filter (fun x : nat => if [x <= c] then true else false) G)) in *.
  assert (SetInterface.cardinal F <= SetInterface.cardinal G). {
    subst F; rewrite filter_incl; eauto.
  }
  pose proof (least_fresh_smallest G).
  pose proof (least_fresh_small G).
  eapply (@all_in_lv_cardinal F (least_fresh G)).
  intros. eapply filter_iff; cset_tac.
  exfalso.
  exploit (@all_in_lv_cardinal F c); [| omega].
  intros. eapply filter_iff; cset_tac.
  eapply H0. omega.
  exfalso. omega.
Qed.

Section FreshListP.
  Variable c : var.

  Fixpoint fresh_list_P (G:set var) (xl:list var)
    : list var :=
    match xl with
      | nil => nil
      | x::xl =>
        if [x <= c] then
          let y := least_fresh G in
          y::fresh_list_P {y;G} xl
        else
          x::fresh_list_P G xl
    end.

  Lemma fresh_list_P_length (G:set var) L
  : length (fresh_list_P G L) = length L.
  Proof.
    general induction L; eauto.
    case_eq (@decision_procedure (a <= c) _); simpl; intros ? EQ;
    rewrite EQ at 1; simpl;
    f_equal; eauto.
  Qed.

  Lemma fresh_list_P_spec (G:set var) L
        (AL:forall x, x > c -> x ∈ of_list L -> x ∈ G -> False)
        (ND: NoDupA eq L)
        (Card: crd c G L)
    : disj (of_list (fresh_list_P G L)) G.
  Proof.
    general induction L.
    - simpl in *; intros; eauto.
    - unfold crd in *. simpl in *.
      cases; eauto; simpl.
      + hnf; intros. cset_tac.
        * eapply least_fresh_spec; eauto.
        * specialize (IHL {least_fresh G; G}).
          simpl in *. rewrite add_cardinal_2 in Card.
          -- eapply IHL; eauto with cset.
             ++ intros. simpl in *. cset_tac.
               exploit (@least_fresh_filter_small c G); eauto.
               rewrite Card. omega.
               rewrite <- H3 in Card. omega.
             ++ rewrite filter_add_incl, add_cardinal; [|clear; intuition].
               unfold var in *. simpl in *.
               omega.
          -- intro. inv ND. eapply H4.
             apply of_list_get_first in H; dcr; inv_get.
             cset_tac.
             eapply get_InA; eauto.
      + hnf; intros. simpl in *. cset_tac.
        * eapply (AL x); eauto. omega.
        * specialize (IHL G).
          eapply IHL; eauto with cset.
  Qed.

  Lemma fresh_list_get (G: set var) L x n
    : (forall x, x > c -> x ∈ of_list L -> x ∈ G -> False)
      -> NoDupA eq L
      -> crd c G L
      -> get (fresh_list_P G L) n x
      -> get L n x \/ (x <= c /\ exists y, get L n y /\ y <= c).
  Proof.
    intros. general induction H0; simpl in *.
    - isabsurd.
    - unfold crd in *; simpl in *.
      cases in H3; simpl in *; invt get; eauto using get.
      + right.
        rewrite (@least_fresh_filter_small c G); eauto.
        unfold var in *; simpl in *. split. omega. eauto using get.
        unfold var in *; simpl in *. omega.
      + rewrite add_cardinal_2 in H2; try omega.
        edestruct (IHNoDupA {least_fresh G; G}); eauto using get.
        * intros. eapply H1; cset_tac.
          exploit (@least_fresh_filter_small c G); eauto.
          unfold var in *; simpl in *.
          rewrite H2. omega.
          rewrite <- H6 in H2. omega.
        * rewrite filter_add_incl; [|intuition].
          rewrite add_cardinal.
          unfold var in *; simpl in *. omega.
        * dcr. right. split; eauto using get.
        * intro. eapply H.
          apply of_list_get_first in H4; dcr; inv_get.
          cset_tac.
          eapply get_InA; eauto.
      + edestruct (IHNoDupA G); eauto using get.
        * intros. eapply H1; cset_tac.
        * dcr; right; eauto using get.
  Qed.

  Lemma InA_get X `{EqDec X eq} (L:list X) x
    : InA eq x L
      -> { n:nat | get L n x }.
  Proof.
    general induction L; isabsurd.
    decide (x === a).
    + hnf in e; subst; eauto using get.
    + edestruct IHL; eauto. inv H0; eauto. exfalso. eauto.
      eauto using get.
  Qed.

  Lemma fresh_list_InA (G: set var) L x
    : (forall x, x > c -> x ∈ of_list L -> x ∈ G -> False)
      -> NoDupA eq L
      -> crd c G L
      -> InA eq x (fresh_list_P G L)
      -> InA eq x L \/ x <= c.
  Proof.
    intros. eapply InA_get in H2; dcr.
    edestruct fresh_list_get; eauto using get_InA.
    hnf; intros. decide (x0 === y); eauto.
  Qed.

  Lemma fresh_list_nodup (G: set var) L
    : (forall x, x > c -> x ∈ of_list L -> x ∈ G -> False)
      -> NoDupA eq L
      -> crd c G L
      -> NoDupA eq (fresh_list_P G L).
  Proof.
    intros Disj NoDup Card.
    general induction NoDup; simpl in *; eauto.
    unfold crd in Card; simpl in *.
    cases; simpl in *.
    - rewrite add_cardinal_2 in Card.
      + econstructor.
        * intro.
          eapply (@fresh_list_P_spec {least_fresh G; G}); eauto with cset.
          -- intros. cset_tac.
             exploit (@least_fresh_filter_small c G); eauto.
             unfold var in *; simpl in *.
             rewrite Card. omega.
             rewrite <- H3 in Card. omega.
          -- hnf.
             rewrite filter_add_incl; [|intuition].
             rewrite add_cardinal.
             unfold var in *; simpl in *. omega.
          -- eapply InA_in; eauto.
        * eapply IHNoDup; eauto.
          --  intros. cset_tac.
              exploit (@least_fresh_filter_small c G); eauto.
              unfold var in *; simpl in *.
              rewrite Card. omega.
              rewrite <- H2 in Card. omega.
          -- hnf; simpl.
             rewrite filter_add_incl; [|intuition].
             rewrite add_cardinal.
             unfold var in *; simpl in *. omega.
      + intro. eapply H.
        apply of_list_get_first in H0; dcr; inv_get.
        cset_tac.
        eapply get_InA; eauto.
    - econstructor.
      + intro. edestruct fresh_list_InA; eauto.
        cset_tac.
      + eapply IHNoDup; eauto.
        intros; cset_tac.
  Qed.
End FreshListP.

Lemma least_fresh_P_ext c (G G' : ⦃var⦄) Z
  : G [=] G' -> least_fresh_P c G Z = least_fresh_P c G' Z.
Proof.
  intros. unfold least_fresh_P; cases; eauto.
  eapply least_fresh_ext; eauto.
Qed.

Lemma fresh_list_P_ext c (G G' : ⦃var⦄) Z
  : G [=] G' -> fresh_list_P c G Z = fresh_list_P c G' Z.
Proof.
  intros. general induction Z; simpl; eauto.
  - cases; f_equal; eauto using least_fresh_ext.
    eapply IHZ. erewrite least_fresh_ext, H; eauto. eauto.
Qed.

Smpl Add match goal with
         | [ |- context [ length (fresh_list_P ?c ?G ?Z) ]] =>
           rewrite (@fresh_list_P_length c G Z)
         | [ H : context [ length (fresh_list_P ?c ?G ?Z) ] |- _ ] =>
           rewrite (@fresh_list_P_length c G Z) in H
         end : len.

Definition regAssignF (c : var)
           (regAssign : stmt -> ann (set var) -> Map [var, var] -> status (Map [var, var]))
  := fix regAssignF
           (ϱ:Map [var, var]) (F:list (list var * stmt)) (ans: list (ann (set var)))
: status (Map [var, var]) :=
  match F, ans with
    | Zs::F, a::ans =>
      let Z := fst Zs in let s := snd Zs in
      let Z' := fresh_list_P c (SetConstructs.map (findt ϱ 0) (getAnn a\of_list Z)) Z in
      sdo ϱ' <- regAssign s a (ϱ[- Z <-- Z'-]);
        regAssignF ϱ' F ans

    | _, _ => Success ϱ
  end.

Fixpoint regAssign (c : var) (st:stmt) (an: ann (set var)) (ϱ:Map [var, var])
  : status (Map [var, var]) :=
 match st, an with
    | stmtLet x e s, ann1 lv ans =>
      let xv := least_fresh_P c (SetConstructs.map (findt ϱ 0) (getAnn ans\ singleton x)) x
      in regAssign c s ans ( ϱ[- x <- xv -])
    | stmtIf _ s t, ann2 lv ans ant =>
      sdo ϱ' <- regAssign c s ans ϱ;
        regAssign c t ant ϱ'
    | stmtApp _ _, ann0 _ => Success ϱ
    | stmtReturn _, ann0 _ => Success ϱ
    | stmtFun F t, annF _ ans ant =>
      sdo ϱ' <- regAssignF c (regAssign c) ϱ F ans;
        regAssign c t ant ϱ'
    | _, _ => Error "regAssign: Annotation mismatch"
 end.

(** The algorithm only changes bound variables in the mapping [ϱ] *)

Lemma regAssign_renamedApart_agreeF c G F ans als ϱ ϱ'
      (allocOK:regAssignF c (regAssign c) ϱ F als = Success ϱ')
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
               regAssign c (snd Zs) a ϱ0 = Success ϱ'0 ->
               agree_on eq (G0 \ snd (getAnn al)) (findt ϱ0 0) (findt ϱ'0 0)))
: forall G' : set var,
    list_union zip defVars F ans[<=]G' ->
    agree_on eq (G \ G') (findt ϱ 0) (findt ϱ' 0).
Proof.
 intros G' INCL.
 length_equify. general induction LEN1; inv LEN2; simpl in * |- *; try monadS_inv allocOK; eauto.
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


Lemma regAssign_renamedApart_agree' c i s al ϱ ϱ' ZL Lv alv G
      (allocOK:regAssign c s alv ϱ = Success ϱ')
      (sd:renamedApart s al)
      (LS:live_sound i ZL Lv s alv)
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
  - exploit IHLS; eauto. instantiate (1:=G) in H4.
    pe_rewrite.
    etransitivity; [| eapply agree_on_incl; try eapply H4].
    eapply agree_on_incl.
    eapply regAssign_renamedApart_agreeF with (G':=D'); try eassumption; eauto.
    rewrite <- H13. cset_tac; intuition. reflexivity.
    eapply incl_minus_lr; try reflexivity. rewrite <- H13. eauto with cset.
Qed.

Lemma regAssign_renamedApart_agree c i s al ϱ ϱ' ZL Lv alv
      (sd:renamedApart s al)
      (LS:live_sound i ZL Lv s alv)
      (allocOK:regAssign c s alv ϱ = Success ϱ')
: agree_on eq (fst (getAnn al)) (findt ϱ 0) (findt ϱ' 0).
Proof.
  eapply agree_on_incl.
  eapply regAssign_renamedApart_agree'; eauto.
  instantiate (1:=fst (getAnn al)).
  exploit renamedApart_disj; eauto.
  revert H. unfold disj.
  clear_all; cset_tac; intuition; eauto.
Qed.

Lemma regAssignF_get c G F ans alv n Zs a ϱ ϱ' an ZL Lv i D Dt lv
: regAssignF c (regAssign c) ϱ F alv = Success ϱ'
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
  -> exists ϱ1 ϱ2, regAssign c (snd Zs) a ϱ1 = Success ϱ2
             /\ regAssignF c (regAssign c) ϱ2 (drop (S n) F) (drop (S n) alv) = Success ϱ'
             /\ agree_on eq (G \ list_union (zip defVars (take n F) (take n ans)))
                        (findt (ϱ[-fst Zs <-- fresh_list_P c
                                      (SetConstructs.map (findt ϱ 0) (getAnn a \ of_list (fst Zs)))
                                      (fst Zs)-]) 0)
                        (findt ϱ1 0).

Proof.
  intros EQ REN LV LVINC DDISJ FUNC PWDISJ GET1 GET2 GET3 incl.
  general induction GET1; inv GET2; inv GET3; simpl in * |- *; monadS_inv EQ; eauto.
  - do 2 eexists; split; eauto. split. rewrite EQ0. reflexivity. reflexivity.
  - exploit (IHGET1 c G); hnf; intros; eauto using get; dcr.
    do 2 eexists; split; eauto. split; eauto.
    rewrite EQ0. simpl. rewrite EQ1; eauto.
    etransitivity; eapply agree_on_incl; [ | reflexivity | eassumption | eauto ].
    + repeat rewrite <- map_update_list_update_agree; eauto with len.
      erewrite fresh_list_P_ext; eauto.
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
