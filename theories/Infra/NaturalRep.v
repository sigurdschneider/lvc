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

Lemma order_respecting' X `{NaturalRepresentation X}
  :  forall x y, asNat x < asNat y <-> _lt x y.
Proof.
  intros.
  rewrite <- ofNat_asNat at 2.
  rewrite <- (ofNat_asNat y) at 2.
  eapply order_respecting.
Qed.

Lemma inj_lt x y
  : (x < y)%positive
    <-> Pos.to_nat x < Pos.to_nat y.
Proof.
  rewrite <- (Pos2Nat.id y) at 1.
  rewrite <- (Pos2Nat.id x) at 1.
  unfold Pos.lt.
  rewrite <- Nat2Pos.inj_compare; eauto.
  - rewrite Nat.compare_lt_iff. reflexivity.
  - exploit (Pos2Nat.is_pos x). simpl in *. omega.
  - exploit (Pos2Nat.is_pos y). simpl in *. omega.
Qed.

Lemma inj_le x y
  : (x <= y)%positive
    <-> Pos.to_nat x <= Pos.to_nat y.
Proof.
  rewrite <- (Pos2Nat.id y) at 1.
  rewrite <- (Pos2Nat.id x) at 1.
  unfold Pos.le.
  rewrite <- Nat2Pos.inj_compare; eauto.
  - rewrite Nat.compare_le_iff. reflexivity.
  - exploit (Pos2Nat.is_pos x). simpl in *. omega.
  - exploit (Pos2Nat.is_pos y). simpl in *. omega.
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


Instance NaturalRepresentationPositive : NaturalRepresentation positive :=
  {
    asNat := fun x => pred (Pos.to_nat x);
    ofNat := Pos.of_succ_nat;
  }.
Proof.
  - intros. eapply SuccNat2Pos.inv.
    erewrite Nat.lt_succ_pred. reflexivity.
    eapply Pos2Nat.is_pos.
  - intros. rewrite SuccNat2Pos.id_succ. reflexivity.
  - intros. rewrite inj_lt.
    rewrite !SuccNat2Pos.id_succ. omega.
Defined.


Class NaturalRepresentationSucc V `{NaturalRepresentation V} :=
  {
    succ : V -> V;
    succ_asNat : forall x, asNat (succ x) = S (asNat x);
    succ_ofNat : forall n:nat, succ (ofNat n) === ofNat (S n);
    respect_lt :> Proper (_lt ==> _lt) succ;
    respect_eq :> Proper (_eq ==> _eq) succ
  }.

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
     | [ LT : context [ (_ < _)%positive ] |- _ ] =>
       setoid_rewrite inj_lt in LT
     | [ |- context [ (_ < _)%positive ] ] =>
       setoid_rewrite inj_lt
     end : nr.

Smpl Add
     match goal with
     | [ H: context [ @asNat ?V _ _ (@max ?V _ _ ?NRM _ _) ] |- _ ] =>
       setoid_rewrite (@max_asNat V _ _ NRM) in H
     | [ |- context [ @asNat ?V _ _ (@max ?V _ _ ?NRM _ _) ] ] =>
       setoid_rewrite (@max_asNat V _ _ NRM)
     | [ H: context [ Pos.to_nat (Pos.max _ _) ] |- _ ] =>
       setoid_rewrite (Pos2Nat.inj_max) in H
     | [ |- context [ Pos.to_nat (Pos.max _ _) ] ] =>
       setoid_rewrite (Pos2Nat.inj_max)
     end : nr.

Smpl Add
     match goal with
     | [ LT : context [ @asNat ?V _ _ (@succ ?V _ _ ?NRS _) ] |- _ ] =>
       setoid_rewrite (@succ_asNat V _ _ NRS) in LT
     | [ |- context [ @asNat ?V _ _ (@succ ?V _ _ ?NRS _) ] ] =>
       setoid_rewrite (@succ_asNat V _ _ NRS)
     | [ LT : context [  Pos.to_nat (Pos.succ _) ] |- _ ] =>
       rewrite Pos2Nat.inj_succ in LT
     | [ |- context [  Pos.to_nat (Pos.succ _) ] ] =>
       rewrite Pos2Nat.inj_succ
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
    intros. rewrite Pos2Nat.inj_succ. simpl.
    erewrite <- S_pred. reflexivity.
    eapply Pos2Nat.is_pos.
  - unfold ofNat. unfold NaturalRepresentationPositive.
    intros. rewrite SuccNat2Pos.inj_succ. reflexivity.
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

Smpl Add
     match goal with
     | [ |- context [ Pos.to_nat (Pos.of_succ_nat _) ] ] =>
       setoid_rewrite SuccNat2Pos.id_succ
     end : nr.
