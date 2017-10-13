Require Import Util CSet MapInjectivity FreshGen Even ARange VarsUpTo.

Set Implicit Arguments.

Definition FG_fast_pos : FreshGen positive positive :=
  @Build_FreshGen positive _ positive
                  (fun n _ => (n,  Pos.succ n))
                  (fun n Z => (range Pos.succ n ❬Z❭, (Util.iter ❬Z❭ n Pos.succ)))
                  (fun n => vars_up_to n)
                  (fun n s => Pos.max n (match SetInterface.max_elt s with
                                        | Some x => Pos.succ x
                                        | None => 1%positive
                                        end))
                  1%positive.

Smpl Add 90
     match goal with
     | [ LT : context [ (_ > _)%positive ] |- _ ] =>
       setoid_rewrite Pos2Nat.inj_gt in LT
     | [ |- context [ (_ > _)%positive ] ] =>
       setoid_rewrite Pos2Nat.inj_gt
     | [ LT : context [ (_ >= _)%positive ] |- _ ] =>
       setoid_rewrite Pos2Nat.inj_ge in LT
     | [ |- context [ (_ >= _)%positive ] ] =>
       setoid_rewrite Pos2Nat.inj_ge
     end : spos.

Smpl Add 90
     match goal with
     | [ LT : context [ (_ > _)%nat ] |- _ ] =>
       unfold Peano.gt in LT
     | [ |- context [ (_ > _)%nat ] ] =>
       unfold Peano.gt
     | [ LT : context [ (_ >= _)%nat ] |- _ ] =>
       unfold Peano.ge in LT
     | [ |- context [ (_ >= _)%nat ] ] =>
       unfold Peano.ge
     end : spos.

Smpl Add
     match goal with
     | [ LT : context [  Pos.to_nat (_ + _)%positive ] |- _ ] =>
       rewrite Pos2Nat.inj_add in LT
     | [ |- context [  Pos.to_nat (_ + _)%positive ] ] =>
       rewrite Pos2Nat.inj_add
     end : spos.

Smpl Add
     match goal with
     | [ H : context [ Pos.of_nat (Pos.to_nat _) ] |- _ ] =>
       rewrite Pos2Nat.id in H
     | [ |- context [ Pos.of_nat (Pos.to_nat _) ] ] =>
       rewrite Pos2Nat.id
     end : spos.

Lemma in_range_x_pos x k n
  : x ∈ of_list (range Pos.succ k n) -> (x >= k)%positive /\ (Pos.of_nat (Pos.to_nat k+n) > x)%positive.
Proof.
  general induction n; dcr.
  - simpl in *. cset_tac.
  - simpl in H. decide (x === k).
    + clear H. invc e; spos; split.
      * reflexivity.
      * rewrite Nat2Pos.id; omega.
    + exploit (IHn x); eauto.
      * cset_tac.
      * dcr. spos. split.
        -- omega.
        -- rewrite Nat2Pos.id;[| omega].
           rewrite Nat2Pos.id in H2;[| omega]. omega.
Qed.

Lemma iter_add_pos n i
  : iter n i Pos.succ = Pos.of_nat (n + Pos.to_nat i).
Proof.
  general induction n; simpl iter; simpl plus; spos; eauto.
  rewrite IHn. spos. f_equal. omega.
Qed.

Lemma range_nodup_pos i d
  : NoDupA _eq (@range positive Pos.succ i d).
Proof.
  general induction d; simpl range; eauto using NoDupA.
  econstructor; eauto.
  intro.
  rewrite InA_in in H.
  eapply in_range_x_pos in H. spos. omega.
Qed.

Lemma FGS_fast_pos : FreshGenSpec FG_fast_pos.
  econstructor.
  - intros. simpl. cset_tac'.
    rewrite <- vars_up_to_in in H. spos. omega.
  - simpl. intros. cset_tac'.
    + rewrite <- vars_up_to_in. spos. omega.
    + revert H0. setoid_rewrite <- vars_up_to_in. spos. omega.
  - intros; hnf; intros.
    eapply vars_up_to_in in H. spos.
    unfold fresh_list in H0; simpl in H0.
    eapply in_range_x_pos in H0 as [? ?]. spos.
    omega.
  - simpl. intros. cset_tac'.
    + eapply in_range_x_pos in H0 as [? ?].
      setoid_rewrite <- vars_up_to_in.
      rewrite iter_add_pos.
      spos. rewrite plus_comm. omega.
    + rewrite <- vars_up_to_in in *.
      rewrite iter_add_pos. spos.
      rewrite Nat2Pos.id; omega.
  - intros. eapply range_nodup_pos.
  - intros.
    unfold fresh_list. simpl.
    eauto with len.
  - intros; hnf; intros; simpl in *.
    eapply union_iff in H.
    rewrite <-  vars_up_to_in in *.
    spos.
    cases; symmetry in Heq.
    + destruct H.
      * eapply zmax_elt_2 in H; eauto.
        rewrite Pos2Nat.inj_max.
        unfold lt_StrictOrder in H. simpl in *. spos.
        rewrite <- Max.le_max_r. omega.
      * rewrite Pos2Nat.inj_max.
        rewrite <- Max.le_max_l. omega.
    + exploit (@max_elt_3 _ _ _ _ G); eauto. cset_tac'.
      rewrite Pos2Nat.inj_max.
      rewrite <- Max.le_max_l. eauto.
Qed.

Lemma NoDup_inj A `{OrderedType A} B `{OrderedType B} (L:list A) (f:A -> B)
      `{Proper _ (_eq ==> _eq) f}
  : NoDupA _eq L
    -> injective_on (of_list L) f
    -> NoDupA _eq (f ⊝ L).
Proof.
  intros ND INJ.
  general induction ND; simpl in *; eauto using NoDupA.
  econstructor; eauto using injective_on_incl with cset.
  intro. eapply InA_in in H3.
  eapply H1. eapply of_list_map in H3; eauto. cset_tac'.
  eapply INJ in H4; eauto with cset.
Qed.

Lemma iter_add2_pos n i
  : iter n i (fun x => Pos.succ (Pos.succ x)) = Pos.of_nat (2 * n + Pos.to_nat i).
Proof.
  general induction n; simpl iter; simpl plus; spos; eauto.
  rewrite IHn. spos. f_equal. omega.
Qed.

Lemma in_range2_x_pos x k n
  : x ∈ of_list (range (fun x => Pos.succ (Pos.succ x)) k n)
    -> (x >= k)%positive /\ (Pos.of_nat (Pos.to_nat k + 2 * n) > x)%positive.
Proof.
  general induction n; dcr.
  - simpl in *. cset_tac.
  - simpl in H. decide (x === k).
    + clear H. invc e; spos; split.
      * reflexivity.
      * rewrite Nat2Pos.id; omega.
    + exploit (IHn x); eauto.
      * cset_tac.
      * dcr. spos. split.
        -- omega.
        -- rewrite Nat2Pos.id;[| omega].
           rewrite Nat2Pos.id in H2;[| omega]. omega.
Qed.

(*
Lemma asNat_iter_plus_plus N `{NaturalRepresentationSucc N} n i
  : asNat (iter n i (fun x => succ (succ x))) = 2 * n + asNat i.
Proof.
  general induction n; simpl; eauto.
  rewrite IHn. spos. omega.
Qed.

Lemma in_range_x  V `{NaturalRepresentationSucc V} x k n
  : x ∈ of_list (range (fun x => succ (succ x)) k n) ->
                 asNat x >= asNat k /\ asNat k+2*n > asNat x.
Proof.
  general induction n; simpl in *; dcr.
  - cset_tac.
  - decide (x === k); subst; try omega;
      cset_tac'; spos; try omega.
    eapply IHn in H3; spos; omega.
    eapply IHn in H3; spos; omega.
Qed.

 *)

Lemma range_nodup i d
  : NoDupA _eq (range (fun x => Pos.succ (Pos.succ x)) i d).
Proof.
  general induction d; eauto using NoDupA.
  econstructor; eauto.
  intro.
  rewrite InA_in in H.
  eapply in_range2_x_pos in H. spos. omega.
Qed.


Definition FG_even_fast_pos : FreshGen positive {n : positive | even_pos_fast n}.
  refine
    (@Build_FreshGen positive _ {n :positive| even_pos_fast n}
                  (fun n _ => (proj1_sig n, exist _ (Pos.succ (Pos.succ (proj1_sig n))) _))
                  (fun n Z => let z := ❬Z❭ in
                             (range (fun x => Pos.succ (Pos.succ x)) (proj1_sig n)  ❬Z❭,
                              exist _ (iter z (proj1_sig n) (fun x => Pos.succ (Pos.succ x))) _))
                  (fun n => (vars_up_to (proj1_sig n)))
                  (fun n s =>
                     exist _ (Pos.max (proj1_sig n) (next_even_pos (match max_elt s with
                                                                    | Some x => Pos.succ x
                                                                    | None => 1%positive
                                                                    end))) _)
                  (exist _ 1%positive _)).
  - simpl. destruct n; simpl. rewrite <- even_pos_fast_correct in *. spos. eauto.
  - destruct n. subst z. simpl.
    rewrite <- even_pos_fast_correct in *. spos.
    rewrite iter_add2_pos.
    rewrite Nat2Pos.id.
    + intro. eapply i. eapply even_add_even; eauto.
      eapply even_mult2.
    + destruct (Pos.to_nat x); try omega.
      simpl in i. cset_tac.
  - destruct n. simpl.
    rewrite <- even_pos_fast_correct in *. spos.
    rewrite Pos2Nat.inj_max.
    eapply not_even_max; eauto.
    exploit next_even_pos_even. spos. eauto.
  - simpl. eauto.
Defined.

Lemma FGS_even_fast_pos : FreshGenSpec FG_even_fast_pos.
  econstructor; simpl.
  - intros. destruct i.
    cset_tac'. simpl in *. rewrite <- vars_up_to_in in H.
    spos; omega.
  - intros [] _; simpl. spos. cset_tac'.
    + rewrite <- vars_up_to_in. spos. omega.
    + rewrite <- vars_up_to_in in H0.
      rewrite <- vars_up_to_in. spos. omega.
  - intros; hnf; intros. cset_tac'.
    eapply vars_up_to_in in H. destruct i; simpl in *.
    eapply in_range2_x_pos in H0. dcr. spos. omega.
  - intros. destruct i; simpl in *. cset_tac'.
    + eapply in_range2_x_pos in H0. dcr.
      eapply vars_up_to_in. spos.
      rewrite iter_add2_pos.
      rewrite plus_comm. omega.
    + rewrite <- vars_up_to_in in *.
      rewrite iter_add2_pos.
      spos. rewrite Nat2Pos.id; try omega.
  - intros. change eq with (@_eq positive _).
    eapply range_nodup.
  - intros. eauto with len.
  - simpl. cset_tac'.
    + rewrite <- vars_up_to_in. spos.
      rewrite Pos2Nat.inj_max.
      rewrite <- Max.le_max_r. unfold next_even_pos.
      repeat cases; spos; eauto;
        rewrite <- even_pos_fast_correct in *; spos.
      * eapply zmax_elt_2 in H0; eauto.
        unfold lt_StrictOrder in H0. simpl in *. spos.
        omega.
      * exploit (@max_elt_3 _ _ _ _ G); eauto. cset_tac'.
      * eapply zmax_elt_2 in H0; eauto.
        unfold lt_StrictOrder in H0. simpl in *. spos.
        omega.
      * exploit (@max_elt_3 _ _ _ _ G); eauto. cset_tac'.
    + rewrite <- vars_up_to_in in *. destruct i; simpl in *.
      spos. rewrite Pos2Nat.inj_max.
      rewrite <- Max.le_max_l. eauto.
Qed.

Inductive FreshGenSingle (V:Type) `{OrderedType V} (Fi : Type) :=
  {
    fresh :> Fi -> V -> V * Fi;
    domain : Fi -> set V;
    domain_add : Fi -> set V -> Fi;
    empty_domain : Fi
  }.

Arguments FreshGenSingle V {H} Fi.

Inductive FreshGenSingleSpec V `{OrderedType V} Fi (FG:FreshGenSingle V Fi) : Prop :=
  {
    fresh_spec : forall i x, fst (fresh FG i x) ∉ domain FG i;
    fresh_domain_spec : forall i x, {fst (fresh FG i x); (domain FG i)}
                                 ⊆ domain FG (snd (fresh FG i x));
    domain_add_spec : forall i G, G ∪ domain FG i ⊆ domain FG (domain_add FG i G)
  }.


Section FreshList_FreshGenSingle.
  Variable V : Type.
  Context `{OrderedType V}.
  Variable Fi : Type.
  Context `{FG:@FreshGenSingle V H Fi}.
  Context `{FGS:@FreshGenSingleSpec V H Fi FG}.

  Fixpoint fresh_list_stable (G:Fi) (xl:list V) : list V * Fi :=
    match xl with
      | nil => (nil, G)
      | x::xl => let (y,G') := fresh FG G x in
                let (Y,G'') := fresh_list_stable G' xl in
                (y::Y,G'')
    end.

  Lemma fresh_list_stable_length G xl
  : length (fst (fresh_list_stable G xl)) = length xl.
  Proof.
    general induction xl; simpl; repeat let_pair_case_eq; subst; simpl; eauto.
  Qed.

  Lemma fresh_list_stable_spec
    : forall G L, disj (of_list (fst (fresh_list_stable G L))) (domain FG G).
  Proof.
    intros. revert G.
    induction L; simpl; intros;
      repeat let_pair_case_eq; subst; simpl; intros; eauto.
    - hnf; intros. eapply add_iff in H0 as [A|A].
      + rewrite <- A in H1. eapply fresh_spec in H1; eauto.
      + eapply IHL; eauto. rewrite <- fresh_domain_spec. cset_tac. eauto.
  Qed.

  Lemma fresh_list_stable_nodup G L
    : NoDupA _eq (fst (fresh_list_stable G L)).
  Proof.
    revert G.
    induction L; intros G; simpl; repeat let_pair_case_eq; subst; eauto.
    econstructor; eauto. intro.
    eapply (@fresh_list_stable_spec (snd (fresh FG G a)) L).
    eapply InA_in. eapply H0.
    rewrite <- fresh_domain_spec.
    cset_tac; eauto. eauto.
  Qed.

  Lemma fresh_list_stable_G G L
    : of_list (fst (fresh_list_stable G L)) ∪ domain FG G
              ⊆ domain FG (snd (fresh_list_stable G L)).
  Proof.
    revert G.
    induction L; intros G; simpl; repeat let_pair_case_eq; subst; simpl;
      eauto with cset.
    rewrite <- IHL. rewrite <- fresh_domain_spec. clear_all. cset_tac. eauto.
  Qed.

End FreshList_FreshGenSingle.


Definition mkFreshGenFromSingle V `{OrderedType V} Fi
           (FG:FreshGenSingle V Fi) : FreshGen V Fi :=
  @Build_FreshGen V _ Fi (@fresh _ _ _ FG)
                  (@fresh_list_stable _ _ _ FG)
                  (@domain _ _ _ FG)
                  (@domain_add _ _ _ FG)
                  (@empty_domain _ _ _ FG).

Lemma mkFreshGenFromSingleSpec V `{OrderedType V} Fi
      (FG:FreshGenSingle V Fi) (FGS:@FreshGenSingleSpec V _ Fi FG)
  : @FreshGenSpec V _ Fi (mkFreshGenFromSingle FG).
Proof.
  econstructor.
  - eapply fresh_spec; eauto.
  - eapply fresh_domain_spec; eauto.
  - symmetry. eapply (@fresh_list_stable_spec V _ Fi FG); eauto.
  - intros. pose proof (@fresh_list_stable_G V _ Fi FG FGS).
    unfold FreshGen.domain. simpl. eauto.
  - intros. eapply fresh_list_stable_nodup. eauto.
  - intros. simpl.
    rewrite fresh_list_stable_length; eauto.
  - eapply domain_add_spec; eauto.
Qed.

Definition FG_fast_pres' : FreshGenSingle positive positive :=
  @Build_FreshGenSingle positive _ positive
                  (fun n x => if [ even_pos_fast x = even_pos_fast n ] then
                               (n, Pos.succ n)
                             else (Pos.succ n, Pos.succ (Pos.succ n)))
                  (fun n => vars_up_to n)
                  (fun n s => Pos.max n (match max_elt s with
                                      | Some x => Pos.succ x
                                      | None => 1%positive
                                      end))
                  (1%positive).

Lemma FGS_fast_pres' : FreshGenSingleSpec FG_fast_pres'.
  econstructor.
  - intros. simpl. cases.
    + cset_tac'. simpl in *; subst. rewrite <- vars_up_to_in in H. spos. omega.
    + simpl. cset_tac'. rewrite <- vars_up_to_in in H.
      spos. omega.
  - simpl. intros. cset_tac'.
    + cases; simpl.
      * rewrite <- vars_up_to_in. spos. omega.
      * rewrite <- vars_up_to_in. spos. omega.
    + revert H0. setoid_rewrite <- vars_up_to_in. intros.
      cases; simpl; spos; eauto.
  - simpl. cset_tac'.
    + rewrite <- vars_up_to_in.
      spos. cases.
      * eapply zmax_elt_2 in H0; eauto.
        unfold lt_StrictOrder in H0. simpl in *. spos.
        rewrite Pos2Nat.inj_max.
        rewrite <- Max.le_max_r. spos. omega.
      * exploit (@max_elt_3 _ _ _ _ G); eauto. cset_tac'.
    + rewrite <- vars_up_to_in in *. spos.
      rewrite Pos2Nat.inj_max.
      rewrite <- Max.le_max_l. eauto.
Qed.

Definition FG_fast_pres := mkFreshGenFromSingle  FG_fast_pres'.
Definition FGS_fast_pres := mkFreshGenFromSingleSpec FGS_fast_pres'.