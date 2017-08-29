Require Import CSet Var.
Require Import Util Map Get Take LengthEq SafeFirst.
Require Export StableFresh VarsUpTo LeastFresh FreshList NaturalRep PidgeonHole.

Set Implicit Arguments.

Lemma all_in_lv_cardinal (lv:set var) n
  : (forall m, _lt m n -> m \In lv) -> cardinal lv >= pred (Pos.to_nat n).
Proof.
  revert lv.
  induction n using Pos.peano_ind; simpl; intros.
  - omega.
  - exploit (IHn (lv \ singleton n)).
    + intros. cset_tac'.
      * eapply H. etransitivity; eauto. nr.
        omega.
      * eapply OrderedType.StrictOrder_Irreflexive in H0. eauto.
    + assert (EQ:lv [=] {n; lv \ singleton n }). {
        exploit (H n); eauto. nr. omega.
        cset_tac.
      }
      rewrite EQ.
      assert (n ∉ lv \ singleton n) by cset_tac.
      erewrite cardinal_2; eauto. nr. omega.
Qed.

Definition fresh (s : set var) : var :=
  Pos.succ (fold Pos.max s 1%positive).

Lemma max_transpose
  : transpose _eq Pos.max.
Proof.
  hnf; intros. hnf.
  rewrite Pos.max_comm.
  rewrite <- Pos.max_assoc.
  setoid_rewrite Pos.max_comm at 2. reflexivity.
Qed.

Lemma fold_max_lt (G:set var)
  : forall (x:var), x ∈ G -> _lt x (Pos.succ (fold Pos.max G 1%positive)).
Proof.
  pattern G. pattern (fold Pos.max G 1%positive). eapply fold_rec.
  - cset_tac.
  - intros ? ? ? ? IN NOTIN ADD LT y yIn.
    eapply ADD in yIn. destruct yIn.
    + rewrite fold_2; eauto.
      * rewrite <- H.
        eapply inj_lt. nr.
        decide ((Pos.to_nat x) < (Pos.to_nat (fold Pos.max s' 1%positive))).
        -- rewrite Max.max_r; eauto. omega.
        -- rewrite Max.max_l; eauto. omega.
      * intuition.
      * eapply max_transpose.
    + rewrite fold_2; eauto using max_transpose.
      * exploit LT; eauto.
        eapply inj_lt. eapply inj_lt in H0. nr.
        decide ((Pos.to_nat x) <= (Pos.to_nat (fold Pos.max s' 1%positive))).
        rewrite Max.max_r; eauto.
        rewrite Max.max_l; omega.
      * intuition.
Qed.

Lemma fresh_spec G : fresh G ∉ G.
Proof.
  intro A. unfold fresh in A.
  pose proof (fold_max_lt A) as B.
  eapply lt_antirefl in B; eauto.
Qed.

Lemma fresh_variable_always_exists (lv:set var) n
  : safe (fun x => x ∉ lv) n.
Proof.
  - decide (_lt (fold Pos.max lv (Pos.of_succ_nat 0)) n).
    + econstructor; intro.
      exploit fold_max_lt. cset_tac.
      exfalso. simpl in *. nr.
      omega.
    + eapply safe_antitone with (n:=Pos.succ (fold Pos.max lv (Pos.of_succ_nat 0))).
      * unfold Proper, respectful. intros. rewrite H. reflexivity.
      * econstructor. intro. exploit fold_max_lt; eauto.
        cset_tac.
        exfalso. simpl in *. nr. omega.
      * simpl in *. nr. omega.
Qed.

Definition least_fresh_gen (lv:set var) : var.
  refine (@safe_first _ _ _ _ (fun x => x ∉ lv) _ (Pos.of_succ_nat 0) _).
  - eapply fresh_variable_always_exists.
Defined.

(*
  Lemma all_in_lv_cardinal (lv:set nat) n
    : (forall m : nat, m < n -> m \In lv) -> cardinal lv >= n.
  Proof.
    general induction n; simpl.
    - omega.
    - exploit (IHn _ _ _ _ _ (lv \ singleton n)).
      + intros. cset_tac'; omega.
      + assert (lv [=] {n; lv \ singleton n }). {
          exploit (H3 (n)); eauto.
          cset_tac.
        }
        rewrite H5.
        assert (n ∉ lv \ singleton n) by cset_tac.
        erewrite cardinal_2; eauto. omega.
  Qed.

  Lemma neg_pidgeon_hole (lv:set nat)
    : (forall m : nat, m <= cardinal lv -> m \In lv) -> False.
  Proof.
    intros. exploit (@all_in_lv_cardinal lv (S (cardinal lv))).
    intros; eapply H; eauto. omega. omega.
  Qed.
 *)

Lemma least_fresh_full_spec G
  : least_fresh_gen G ∉ G
    /\ pred (Pos.to_nat (least_fresh_gen G)) <= cardinal G
    /\ forall m, _lt m (least_fresh_gen G) -> m ∈ G.
Proof.
  unfold least_fresh_gen.
  eapply safe_first_spec
    with (I:= fun n => le (pred (Pos.to_nat n)) (cardinal G) /\ forall m, _lt m n -> m ∈ G).
  - intros ? [A B] NOTIN.
    assert (IN:n ∈ G) by cset_tac. clear NOTIN.
    split.
    + eapply all_in_lv_cardinal.
      intros. decide (Pos.to_nat m = Pos.to_nat n); try rewrite e in *; eauto.
      * eapply Pos2Nat.inj in e. subst; eauto.
      * unfold NaturalRep.succ in *. simpl in *.
        eapply B. nr. omega.
    + intros. decide (Pos.to_nat m = Pos.to_nat n); try rewrite e in *; eauto.
      * eapply Pos2Nat.inj in e. subst; eauto.
      * unfold NaturalRep.succ in *. simpl in *.
        eapply B. nr. omega.
  - intuition.
  - split; intros; simpl in *. omega.
    exfalso.
    eapply Pos.nlt_1_r in H; eauto.
Qed.

Lemma least_fresh_gen_ext (G G':set var)
  : G [=] G'
    -> least_fresh_gen G = least_fresh_gen G'.
Proof.
  intros. unfold least_fresh_gen.
  eapply safe_first_ext; eauto.
  split; intros.
  - rewrite <- H; eauto.
  - rewrite H; eauto.
Qed.

Instance LeastFreshNat : LeastFresh.LeastFresh var :=
  {
    least_fresh := @least_fresh_gen
  }.
Proof.
  - intros. eapply least_fresh_full_spec.
  - intros. eapply least_fresh_full_spec; eauto.
  - intros. eapply least_fresh_gen_ext; eauto.
Qed.


Lemma least_fresh_list_small (G:set var) n
  : forall i x, get (fresh_list least_fresh G n) i x -> pred (Pos.to_nat x) < cardinal G + n.
Proof.
  general induction n; simpl in *; isabsurd.
  - invc H.
    + clear IHn.
      pose proof (least_fresh_least G).
      eapply all_in_lv_cardinal in H.
      omega.
    + exploit IHn; eauto.
      erewrite cardinal_2 with (s:=G) in H. omega.
      eapply (least_fresh_spec). cset_tac.
Qed.

Lemma least_fresh_list_ext X `{LeastFresh X}  n (G:set X) G'
  : G [=] G'
    -> fresh_list least_fresh G n = fresh_list least_fresh G' n.
Proof.
  intros.
  eapply fresh_list_ext; eauto.
  eapply least_fresh_spec.
  eapply least_fresh_ext.
Qed.

Lemma least_fresh_list_small_vars_up_to (G:set var) (n:nat)
  : of_list (fresh_list least_fresh G n) ⊆ vars_up_to (Pos.of_succ_nat (cardinal G + n)).
Proof.
  eapply get_in_incl; intros.
  eapply in_vars_up_to.
  eapply least_fresh_list_small in H; eauto.
  rewrite <- Pos.succ_of_nat.
  - eapply inj_lt.
    rewrite Pos2Nat.inj_succ. rewrite Nat2Pos.id. omega. omega.
  - omega.
Qed.


(*
Lemma inverse_on_update_fresh_list (D:set nat) (Z:list nat) (ϱ ϱ' : nat -> nat)
 : inverse_on (D \ of_list Z) ϱ ϱ'
  -> inverse_on D (update_with_list Z (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) (length Z)) ϱ)
                 (update_with_list (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) ((length Z))) Z ϱ').
Proof.
  intros. eapply inverse_on_update_fresh; eauto. intros.
  eapply fresh_list_nodup, fresh_spec. eauto with len.
  eapply fresh_list_spec, fresh_spec.
Qed.
 *)
