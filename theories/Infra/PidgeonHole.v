Require Import CSet Le Arith.Compare_dec Plus Util.

Class NaturalRepresentation X `{OrderedType X} :=
  {
    asNat : X -> nat;
    ofNat : nat -> X;
    ofNat_asNat : forall x, ofNat (asNat x) === x;
    asNat_ofNat : forall n, asNat (ofNat n) === n;
    order_respecting : forall x y, x < y <-> _lt (ofNat x) (ofNat y);
    asNat_proper :> Proper (_eq ==> eq) asNat
  }.

Arguments asNat : simpl never.
Arguments ofNat : simpl never.

Arguments NaturalRepresentation X {H}.

Ltac revert_except E :=
  repeat match goal with
         | [H : _ |- _] =>
           match H with
           | E => fail 1
           | _ =>
             match type of H with
             | OrderedType _ => fail 1
             | NaturalRepresentation _ => fail 1
             | _ =>             revert H
             end
           end
         end.

Lemma order_respecting' X `{NaturalRepresentation X}
  :  forall x y, asNat x < asNat y <-> _lt x y.
Proof.
  intros.
  rewrite <- ofNat_asNat at 2.
  rewrite <- (ofNat_asNat y) at 2.
  eapply order_respecting.
Qed.


Class NaturalRepresentationSucc V `{NaturalRepresentation V} :=
  {
    succ : V -> V;
    succ_asNat : forall x, asNat (succ x) = S (asNat x);
    succ_ofNat : forall n:nat, succ (ofNat n) === ofNat (S n);
    respect_lt :> Proper (_lt ==> _lt) succ;
    respect_eq :> Proper (_eq ==> _eq) succ
  }.

Lemma all_in_lv_cardinal' X `{NaturalRepresentation X} (lv:set X) (n:nat)
  : (forall m : X, _lt m (ofNat n) -> m \In lv) -> cardinal lv >= n.
Proof.
  general induction n; simpl.
  - omega.
  - exploit (IHn _ _ _ (lv \ singleton (ofNat n))).
    + intros. cset_tac'.
      * eapply H1. etransitivity; eauto.
        eapply order_respecting. omega.
      * rewrite <- H3 in H2. exfalso.
        eapply OrderedType.StrictOrder_Irreflexive in H2. eauto.
    + assert (EQ:lv [=] {ofNat n; lv \ singleton (ofNat n) }). {
        exploit (H1 (ofNat n)); eauto.
        eapply order_respecting. omega.
        cset_tac.
      }
      rewrite EQ.
      assert (ofNat n ∉ lv \ singleton (ofNat n)) by cset_tac.
      erewrite cardinal_2; eauto. omega.
      Grab Existential Variables.
Qed.

Arguments all_in_lv_cardinal' {X} {H} {H0} lv n.

Lemma all_in_lv_cardinal X `{NaturalRepresentation X} (lv:set X) y
  : (forall x : X, _lt x y -> x \In lv) -> cardinal lv >= asNat y.
Proof.
  intros. eapply all_in_lv_cardinal'.
  intros m. rewrite ofNat_asNat. eauto.
Qed.

Arguments all_in_lv_cardinal {X} {H} {H0} lv y.

Lemma neg_pidgeon_hole X `{NaturalRepresentation X} (lv:set X)
  : (forall m : X, _lt m (ofNat (S (cardinal lv))) -> m \In lv) -> False.
Proof.
  intros. exploit (all_in_lv_cardinal' lv (S (cardinal lv))); eauto.
  - omega.
Qed.

Instance NaturalRepresentationNat : NaturalRepresentation nat :=
  {
    asNat := fun x => x;
    ofNat := fun x => x;
  }.
Proof.
  - reflexivity.
  - reflexivity.
  - simpl. intros. omega.
Defined.

Definition posToNat (x:positive) :=
  pred (Pos.iter_op Init.Nat.add x 1).

Fixpoint natToPos (n : nat) : positive :=
  match n with
  | 0 => 1%positive
  | 1 => 2%positive
  | S (S _ as x) => Pos.succ (natToPos x)
  end.

Lemma succ_natToPos n
  : Pos.succ (natToPos n) = natToPos (S n).
Proof.
  general induction n; simpl; eauto.
Qed.

Lemma natToPos_posToNat x
  : natToPos (posToNat x) = x.
Proof.
  unfold posToNat. pattern x.
  eapply Pos.peano_ind.
  - simpl. reflexivity.
  - intros. rewrite Pos.iter_op_succ.
    + simpl. rewrite <- H at 2.
      rewrite succ_natToPos.
      erewrite <- S_pred. reflexivity.
      eapply le_Pmult_nat.
    + intros. omega.
Qed.

Lemma posToNat_natToPos n
  : posToNat (natToPos n) = n.
Proof.
  unfold posToNat.
  general induction n; eauto.
  rewrite <- succ_natToPos.
  rewrite Pos.iter_op_succ; [|intros;omega].
  simpl. rewrite <- IHn at 2.
  erewrite <- S_pred. reflexivity.
  eapply le_Pmult_nat.
Qed.

Lemma lt_respect
  : forall x y : nat, x < y <-> _lt (natToPos x) (natToPos y).
Proof.
  simpl. intros.
  general induction x; simpl.
  + split; intros.
    * general induction y.
      -- omega.
      -- rewrite <- succ_natToPos.
         eapply Pos.lt_1_succ.
    * general induction y; simpl in *.
      inv H. destruct y. omega. omega.
  + split; intros.
    * destruct x.
      -- destruct y. omega.
         exploit (IHx y); dcr. simpl in *.
         destruct y. simpl in *. omega.
         exploit H1; eauto. omega.
         assert (2 = Pos.succ 1)%positive by reflexivity.
         rewrite H3.
         rewrite <- Pos.succ_lt_mono. eauto.
      -- destruct y. omega. destruct y. omega.
         edestruct (IHx (S y)). exploit H0. omega.
         setoid_rewrite <- succ_natToPos at 2.
         rewrite <- Pos.succ_lt_mono. eauto.
    * destruct x.
      -- destruct y; simpl in *. inv H.
         destruct y. inv H. simpl in *. destruct y. hnf. reflexivity.
         hnf. omega.
      -- destruct y.
         ++ setoid_rewrite <- succ_natToPos in H.
           simpl in H. destruct (natToPos x); isabsurd.
         ++ setoid_rewrite <- succ_natToPos in H at 2.
           rewrite <- Pos.succ_lt_mono in H.
           destruct y.
           setoid_rewrite <- succ_natToPos in H.
           simpl in H. destruct (natToPos x); isabsurd.
           eapply IHx in H. omega.
Qed.

Instance NaturalRepresentationPositive : NaturalRepresentation positive :=
  {
    asNat := posToNat;
    ofNat := natToPos;
  }.
Proof.
  - eapply natToPos_posToNat.
  - eapply posToNat_natToPos.
  - eapply lt_respect.
Defined.

Class NaturalRepresentationMax V `{NaturalRepresentation V} :=
  {
    max : V -> V -> V;
    max_asNat : forall x y, max x y === ofNat (Init.Nat.max (asNat x) (asNat y));
    max_proper :> Proper (_eq ==> _eq ==> _eq) max
  }.

Arguments NaturalRepresentationMax V {H} {H0}.

Smpl Create nr.

Smpl Add
     match goal with
     | [ LT : context [ @_lt ?V _ _ _ ], NR:NaturalRepresentation ?V |- _ ] =>
       setoid_rewrite <- (@order_respecting' V _ NR) in LT
     | [ NR:NaturalRepresentation ?V |-  context [ @_lt ?V _ _ _ ] ] =>
       setoid_rewrite <- (@order_respecting' V _ NR)
     end : nr.

Smpl Add
     match goal with
     | [ H: context [ @asNat ?V _ _ (@max ?V _ _ ?NRM _ _) ] |- _ ] =>
       setoid_rewrite (@max_asNat V _ _ NRM) in H
     | [ |- context [ @asNat ?V _ _ (@max ?V _ _ ?NRM _ _) ] ] =>
       setoid_rewrite (@max_asNat V _ _ NRM)
     end : nr.

Smpl Add
     match goal with
     | [ LT : context [ @asNat ?V _ _ (@succ ?V _ _ ?NRS _) ] |- _ ] =>
       setoid_rewrite (@succ_asNat V _ _ NRS) in LT
     | [ |- context [ @asNat ?V _ _ (@succ ?V _ _ ?NRS _) ] ] =>
       setoid_rewrite (@succ_asNat V _ _ NRS)
     end : nr.

Smpl Add
     match goal with
     | [ LT : context [ @asNat ?V _ ?NR (@ofNat ?V _ _ _) ] |- _ ] =>
       setoid_rewrite (@asNat_ofNat V _ NR) in LT
     | [ |- context [ @asNat ?V _ ?NR (@ofNat ?V _ _ _) ] ] =>
       setoid_rewrite (@asNat_ofNat V _ NR)
     end : nr.

Smpl Add
     match goal with
     | [ LT : context [ @ofNat ?V _ ?NR (@asNat ?V _ _ _) ] |- _ ] =>
       setoid_rewrite (@ofNat_asNat V _ NR) in LT
     | [ |- context [ @ofNat ?V _ ?NR (@asNat ?V _ _ _) ] ] =>
       setoid_rewrite (@ofNat_asNat V _ NR)
     end : nr.


Ltac nr := repeat smpl nr.

Instance NaturalRepresentationSuccNat : NaturalRepresentationSucc nat :=
  {
    succ := S
  }.
Proof.
  - reflexivity.
  - reflexivity.
  - unfold Proper, respectful; cbn. intros; omega.
Defined.

Instance NaturalRepresentationMaxNat : NaturalRepresentationMax nat :=
  {
    max := Max.max
  }.
Proof.
  - reflexivity.
Defined.


Instance NaturalRepresentationSuccPositive : NaturalRepresentationSucc positive :=
  {
    succ := Pos.succ
  }.
Proof.
  - unfold asNat; simpl.
    unfold posToNat; simpl.
    intros. rewrite Pos.iter_op_succ; simpl.
    erewrite <- S_pred. reflexivity.
    eapply le_Pmult_nat. intros; omega.
  - unfold ofNat. unfold NaturalRepresentationPositive.
    intros. rewrite succ_natToPos. reflexivity.
  - unfold Proper, respectful; cbn.
    intros. rewrite <- Pos.succ_lt_mono. eauto.
Defined.

Lemma Posmax_asNat x y
  : Pos.max x y === ofNat (Init.Nat.max (asNat x) (asNat y)).
Proof.
  pose proof (Pos.compare_spec x y).
  unfold Pos.max. inv H.
  - rewrite max_r; try omega. rewrite ofNat_asNat; eauto.
  - rewrite max_r; try omega. rewrite ofNat_asNat; eauto.
    edestruct (order_respecting' _ x y); eauto. simpl in *.
    exploit H3. hnf. eauto. omega.
  - rewrite Max.max_comm.
    rewrite max_r; try omega. rewrite ofNat_asNat; eauto.
    edestruct (order_respecting' _ y x); eauto. simpl in *.
    exploit H3. eauto. omega.
Defined.


Instance NaturalRepresentationMaxPositive : NaturalRepresentationMax positive :=
  {
    max := Pos.max
  }.
Proof.
  - intros. eapply Posmax_asNat.
Defined.


Lemma asNat_ofNat_swap N `{NaturalRepresentation N} k m
  : k = asNat m <-> ofNat k === m.
Proof.
  split; intros; subst.
  - rewrite ofNat_asNat. reflexivity.
  - rewrite <- H1. rewrite asNat_ofNat. reflexivity.
Qed.

Lemma asNat_inj N `{NaturalRepresentation N} m n
  : asNat m = asNat n -> m === n.
Proof.
  intros.
  decide (_lt m n); eauto.
  - nr. omega.
  - decide (_lt n m); eauto.
    + nr. omega.
    + eapply lt_trans_eq; eauto.
Qed.

Lemma asNat_iff N `{NaturalRepresentation N} m n
  : asNat m = asNat n <-> m === n.
Proof.
  split; eauto using asNat_inj, asNat_proper.
Qed.

(* Smpl Add match goal with
         | [ LT : context [ @asNat ?V ?H ?NR _ = asNat _ ] |- _ ] =>
           rewrite (@asNat_iff V H NR) in LT
         end : nr.*)

Smpl Add match goal with
         | [ EQ : context [ @equiv ?V (@_eq ?V ?H) _ _ _ ],
                  NR : @NaturalRepresentation ?V ?H |- _ ] =>
           rewrite <- (@asNat_iff V H NR) in EQ
         | [ NR : @NaturalRepresentation ?V ?H |- context [ @equiv ?V (@_eq ?V ?H) _ _ _ ] ] =>
           rewrite <- (@asNat_iff V H NR)
         end : nr.


Lemma asNat_iter_plus N `{NaturalRepresentationSucc N} n i
  : asNat (iter n i succ) = n + asNat i.
Proof.
  general induction n; simpl; eauto.
  rewrite IHn. nr. omega.
Qed.

Smpl Add
     match goal with
     | [ H : context [iter _ _ (@succ ?V ?H ?NR ?NRS)] |- _ ] =>
       setoid_rewrite (@asNat_iter_plus V H NR NRS) in H
     | [ |- context [iter _ _ (@succ ?V ?H ?NR ?NRS)] ] =>
       setoid_rewrite (@asNat_iter_plus V H NR NRS)
     end : nr.

Lemma succ_inj V `{NaturalRepresentationSucc V} (x y:V)
  : succ x === succ y
    -> x === y.
Proof.
  intros.
  nr. omega.
Qed.
