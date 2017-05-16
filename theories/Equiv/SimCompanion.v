Require Import Util Option AllInRel Get Setoid.
Require Export paco3 SmallStepRelations StateType Sim.
Require Import Coq.Logic.FunctionalExtensionality ClassicalFacts.

Axiom propositional_extensionality : prop_extensionality.

Notation "p =3= q" :=
  (forall x0 x1 x2, p x0 x1 x2 <-> (q x0 x1 x2:Prop))
    (at level 50, no associativity).


Lemma pred3_extensionality A B C (R R' : A -> B -> C -> Prop)
  : R =3= R' -> R = R'.
Proof.
  intros.
  do 3 (eapply functional_extensionality; intros).
  eapply propositional_extensionality. eauto.
Qed.

Set Implicit Arguments.

Section Tower.
  Variables A B C : Type.
  Variable f : (A -> B -> C -> Prop) -> (A -> B -> C -> Prop).

  Definition inf I (F: I -> A -> B -> C -> Prop) : A -> B -> C -> Prop :=
    fun a b c => forall i:I, F i a b c.

  Inductive T : (A -> B -> C -> Prop) -> Prop :=
  | T_step R : T R -> T (f R)
  | T_lim I (F : I -> A -> B -> C -> Prop)
    : (forall i, T (F i)) -> T (inf F).

  Definition companion (R : A -> B -> C -> Prop) : A -> B -> C -> Prop :=
    fun a b c => forall S, T S -> R <3= S -> S a b c.

  Notation "'㚘'" := companion (at level 0).

  Lemma T_companion x : T (companion x).
    repeat (eapply T_lim; intros).
    eauto.
  Qed.

  Lemma companion_monotone : monotone3 companion.
    hnf; intros. hnf; intros.
    eapply IN; eauto.
  Qed.

  Lemma companion_inc R : R <3= companion R.
    intros; hnf; eauto.
  Qed.

  Lemma companion_idem x : companion (companion x) = companion x.
    eapply pred3_extensionality; split.
    - intros H; eapply H; eauto using T_companion.
    - eapply companion_inc.
  Qed.


  Lemma companion_img x : T x -> companion x = x.
    intros. eapply pred3_extensionality.
    split; intros; eauto using companion_inc.
    - eapply H0; eauto.
  Qed.

  Definition inf_closed (P: (A -> B -> C -> Prop) -> Prop) :=
    forall I (F : I -> A -> B -> C -> Prop),
      (forall i, P (F i)) -> P (inf F).


  Theorem tower_ind P
    : inf_closed P ->
      (forall x, P (companion x) -> P (f (companion x))) ->
      forall x, P (companion x).
  Proof.
    intros.
    do 3 (eapply H; intros).
    clear x i1.
    induction i0; eauto.
    rewrite <- (companion_img i0).
    eapply H0. rewrite companion_img; eauto.
  Qed.

  Lemma companion_fold R
    : monotone3 f -> f (companion R) <3= companion R.
  Proof.
    intro.
    eapply tower_ind.
    - hnf; intros. hnf; intros. eauto.
    - intros. eapply H; eauto.
  Qed.

  Lemma companion_unfold
    : companion bot3 <3= f (companion bot3).
  Proof.
    intros. eapply PR; intros.
    - econstructor 1. eapply T_companion.
    - isabsurd.
  Qed.

  Section UptoLemma.
    Variable g : (A -> B -> C -> Prop) -> (A -> B -> C -> Prop).
    Hypothesis gP : monotone3 g.

    Lemma upto :
      (forall x, g (companion x) <3= companion x -> g (f (companion x)) <3= f (companion x)) ->
      (forall x, g (companion x) <3= companion x).
    Proof.
      intros H1 H2.
      eapply tower_ind.
      - intros; hnf; intros; eauto.
        hnf; eauto.
      - intros; eauto.
    Qed.

    Lemma upto_below :
      (forall x, g (companion x) <3= companion x) -> g <4= companion.
    Proof.
      intros H1 r; intros.
      eapply H1. eapply gP; eauto.
      eapply companion_inc.
    Qed.

    Lemma upto_char :
      monotone3 f ->
      g <4= companion ->
      forall x, g (companion x) <3= companion x -> g (f (companion x)) <3= f (companion x).
    Proof.
      intros gM H1 r H2; intros.
      eapply H1; eauto.
      econstructor 1. eapply T_companion.
    Qed.
  End UptoLemma.

    Lemma companion_unfold_r r
    : monotone3 f -> companion r <3= f (companion r \3/ r).
  Proof.
    intros. hnf in PR. eapply PR.
    - econstructor 1. admit.
    - intros.
      eapply H; try left; eauto.
      (* eapply PR. *)

  Admitted.

End Tower.



Definition simc {S} `{StateType S} {S'} `{StateType S'} r t (σ1:S) (σ2:S')
  := companion (@sim_gen S _ S' _) r t σ1 σ2.

Theorem simc_sim {S} `{StateType S} {S'} `{StateType S'} r t (σ1:S) (σ2:S')
  : simc bot3 t σ1 σ2 -> sim r t σ1 σ2.
Proof.
  intros. revert t σ1 σ2 H1.
  pcofix CIH; intros.
  pfold. eapply companion_unfold in H2.
  eapply sim_gen_mon; eauto.
Qed.


Theorem sim_simc {S} `{StateType S} {S'} `{StateType S'} r t (σ1:S) (σ2:S')
  : sim bot3 t σ1 σ2 -> simc r t σ1 σ2.
Proof.
  intros. revert t σ1 σ2 H1.
  unfold simc.
  eapply tower_ind; intros.
  - hnf; intros; hnf; intros. eauto.
  - punfold H2.
    eapply sim_gen_mon; eauto; intros.
    destruct PR; isabsurd.
    eapply H1. eauto.
Qed.

Lemma simc_trans t {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : simc bot3 t σ1 σ2 -> simc bot3 t σ2 σ3 -> simc bot3 t σ1 σ3.
Proof.
  intros.
  eapply sim_simc.
  eapply sim_trans with (S2:=S2).
  eapply simc_sim; eauto.
  eapply simc_sim; eauto.
Qed.

Definition expc {S} `{StateType S} {S'} `{StateType S'}
           (r:(simtype -> S -> S' -> Prop)) : simtype -> S -> S' -> Prop :=
  fun t σ σ' => exists σ1 σ2, star2 step σ nil σ1 /\ star2 step σ' nil σ2 /\ r t σ1 σ2.

Lemma expc_upto {S} `{StateType S} {S'} `{StateType S'}
  : (forall r, @expc S _ S' _ (simc r) <3= simc r).
Proof.
  intros H1 H2.
  eapply upto.
  - unfold expc; hnf; intros.
    destruct IN as [? [? [? [? ?]]]].
    do  2eexists; split; eauto.
  - unfold expc; intros.
    destruct PR as [? [? [? [? ?]]]].
    inv H6; zzsimpl; eauto 20.
Qed.


Lemma expc_simc {S} `{StateType S} {S'} `{StateType S'} (σ1 σ1':S) (σ2 σ2':S') t r
  : simc r t σ1'  σ2'
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> simc r t σ1 σ2.
Proof.
  intros.
  eapply expc_upto; hnf; eauto 20.
Qed.


Definition redc {S} `{StateType S} {S'} `{StateType S'}
           (r:(simtype -> S -> S' -> Prop)) : simtype -> S -> S' -> Prop :=
  fun t σ σ2 => exists σ1, star2 step σ1 nil σ (* /\ star2 step σ2 nil σ'*) /\ r t σ1 σ2.

Lemma star2n_reach' X (R:X -> event -> X -> Prop) σ1 σ2a σ2b n n'
: star2n R n σ1 nil σ2a
  -> star2n R n' σ1 nil σ2b
  -> internally_deterministic R
  -> ((star2n R (n'-n) σ2a nil σ2b /\ n' > n) \/
     (star2n R (n-n') σ2b nil σ2a /\ n > n')
     \/ ( n' = n /\ σ2a = σ2b)).
Proof.
  intros Star1 Star2 IDet.
  general induction Star1; eauto.
  - orewrite (n' - 0 = n').
    inv Star2; eauto.
    left. rewrite H. split; eauto. omega.
  - relsimpl. invc Star2; relsimpl; simpl; eauto.
    + right. left. split. eapply (S_star2n _ _ H Star1). omega.
    + edestruct IHStar1 as [?|[?|?]]; eauto; dcr.
      * left. split; try omega. eauto.
      * right. left. split; try omega. eauto.
Qed.

Lemma star2n_plus {S} `{StateType S} (σ σ':S) n
  : star2n step n σ nil σ'
    -> n > 0
    -> plus2 step σ nil σ'.
Proof.
  intros. general induction H0.
  - omega.
  - destruct y, yl; isabsurd; simpl in *.
    destruct n.
    + inv H1. econstructor 1; eauto.
    + econstructor 2; eauto. eapply IHstar2n; eauto.
      omega.
Qed.

(*
Lemma sim_reduction_closed_1 t {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2:S') r
  : simc r t σ1 σ2
    -> star2 step σ1 nil σ1'
    -> simc r t σ1' σ2.
Proof.
  intros Sim Star.
  eapply star2_star2n in Star. destruct Star as[n StarN].
  revert dependent r. revert σ1 σ2 σ1' StarN.
  size induction n.

  inv Sim; zzsimpl.
    + invc StarN; eauto. zzsimpl.
      eapply star2_star2n in H4. dcr.
      edestruct (star2n_reach' H11 H7) as [?|[?|?]]; eauto; subst; dcr. eapply H.
      * econstructor 1. eapply star2n_plus; eauto. omega. eauto. eauto.
      * eapply H3; eauto. admit.
      * subst.

Lemma redc_upto {S} `{StateType S} {S'} `{StateType S'}
  : (forall r, @redc S _ S' _ (simc r) <3= simc r).
Proof.
  intros H1 H2.
  eapply upto.
  - unfold redc; hnf; intros.
    dcr.
    do  2eexists;  eauto.
  - unfold redc. intros r UH t σ1 σ2 PR.
    destruct PR as [σ1' [StarN Sim]].
    eapply star2_star2n in StarN. destruct StarN as[n StarN].
    revert dependent r. revert σ1 σ2 σ1' StarN.
    size induction n.
    inv Sim; zzsimpl.
    + invc StarN; eauto. zzsimpl.
      eapply star2_star2n in H4. dcr.
      edestruct (star2n_reach' H11 H7) as [?|[?|?]]; eauto; subst; dcr. eapply H.
      * econstructor 1. eapply star2n_plus; eauto. omega. eauto. eauto.
      * eapply H3; eauto. admit.
      * subst.

        eapply H3. Focus 2. eauto. omega. eauto.



Qed.


Lemma redc_simc {S} `{StateType S} {S'} `{StateType S'} (σ1 σ1':S) (σ2 σ2':S') t r
  : simc r t σ1'  σ2'
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> simc r t σ1 σ2.
Proof.
  intros.
  eapply redc_upto; hnf; eauto 20.
Qed.

*)



Definition sconv {S} `{StateType S} (σ1 σ2:S) :=
  star2 step σ1 nil σ2 \/ star2 step σ2 nil σ1.

Instance sconv_refl {S} `{StateType S} : Reflexive sconv.
Proof.
  hnf; intros; hnf; left; eapply star2_refl.
Qed.

Instance sconv_sym {S} `{StateType S} : Symmetric sconv.
Proof.
  hnf; intros; hnf; firstorder.
Qed.

Lemma sconv_star2 {S} `{StateType S} (σ1 σ2:S)
  : star2 step σ1 nil σ2
    -> sconv σ1 σ2.
firstorder.
Qed.

Lemma sconv_plus2 {S} `{StateType S} (σ1 σ2:S)
  : plus2 step σ1 nil σ2
    -> sconv σ1 σ2.
  firstorder using plus2_star2.
Qed.

Lemma sconv_star2' {S} `{StateType S} (σ1 σ2:S)
  : star2 step σ1 nil σ2
    -> sconv σ2 σ1.
firstorder.
Qed.

Lemma sconv_plus2' {S} `{StateType S} (σ1 σ2:S)
  : plus2 step σ1 nil σ2
    -> sconv σ2 σ1.
Proof.
  unfold sconv; intros; eauto using plus2_star2.
Qed.

Hint Resolve sconv_star2 sconv_plus2 sconv_star2' sconv_plus2'.

Lemma sconv_closed {S} `{StateType S} (σ1 σ2 σ1' σ2':S)
  : sconv σ1 σ2
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> sconv σ1' σ2'.
Proof.
  unfold sconv; intros; destruct H0; zzsimpl; try zzcases; eauto.
  edestruct (star2_reach H1 H2); eauto. eapply H.
  edestruct (star2_reach H1 H2); eauto. eapply H.
Qed.

Hint Resolve sconv_closed.

Lemma sconv_activated_right  {S} `{StateType S} σ1 σ2
  : sconv σ1 σ2 -> activated σ2 ->
    exists σ1', star2 step σ1 nil σ1' /\ activated σ1'.
Proof.
  intros. destruct H0.
  - zzsimpl. eauto.
  - zzsimpl. eauto using star2.
Qed.

Ltac fold_conv :=
  match goal with
  | [ H : sconv ?σ1 ?σ2, I : star2 step ?σ2 nil ?σ3 |- _ ]
    => eapply sconv_closed in H; [ clear I | eapply star2_refl | eapply  I]
  | [ H : sconv ?σ1 ?σ2, I : star2 step ?σ1 nil ?σ3 |- _ ]
    => eapply sconv_closed in H; [ clear I | eapply  I | eapply star2_refl]
  end.




Definition g {S} `{StateType S} {S'} `{StateType S'}
           (r:(simtype -> S -> S' -> Prop)) : simtype -> S -> S' -> Prop :=
  fun t σ σ' => exists σ1 σ2, simc bot3 t σ σ1 /\
                      sconv σ1 σ2
                      /\ r t σ2 σ'.

Lemma g_upto {S} `{StateType S} {S'} `{StateType S'}
  : (forall r, @g S _ S' _ (simc r) <3= simc r).
    Proof.
      intros H1 H2.
      eapply upto.
      - unfold g; hnf; intros.
        destruct IN as [? [? ?]]. dcr.
        do 2 eexists; split; eauto.
      - unfold g; intros.
        destruct PR as [? [? [? [? ?]]]].
        eapply companion_unfold in H4.
        + { inv H6.
          - econstructor 1. eauto. eauto.
            eapply H3; eauto.
            do 2 eexists; split; eauto.
            split; [|eauto].
            eapply sconv_closed; eauto using plus2_star2.
          - (* plus step <-> activated *)
            admit.
          -
            zzsimpl. zzcases. zzsimpl.
        + econstructor 2; eauto using plus2_star2.
          * intros. unfold upaco3 in *; zzsimpl; eauto 10 using star2_refl.
          * intros. unfold upaco3 in *; zzsimpl; eauto 10 using star2_refl.
        + zzsimpl. assert (t = Sim).
          eapply (@sim_t_Sim_activated t _ _ _ H10 H9 _ _ _ H7); eauto.
          subst.
          econstructor 3; eauto using plus2_star2, star2_trans.
      - (* plus step <-> err *)
        zzsimpl. zzcases.
        + pfold. zzsimpl.
          econstructor 3; eauto; eauto.
        + eapply plus2_star2 in H4.
          exploit (star2_trans H4 H2); eauto.
      - (*  plus step <-> term *)
        zzsimpl. zzcases.
        + pfold. zzsimpl.
          econstructor 4; eauto; eauto.
        + zzsimpl.
          destruct (@sim_t_Sim_normal t _ _ _ _ _ _ H9 H8 H14 H7); eauto.
          * subst.
            pfold. econstructor 3; eauto using plus2_star2, star2_trans.
          * pfold. econstructor 4; eauto using plus2_star2, star2_trans.
            congruence.
      - (* activated <-> plus step *)
        pfold. zzsimpl.
        zzcases. zzsimpl.
        + unfold upaco3 in *.
          econstructor 2; eauto using plus2_star2.
          * intros. zzsimpl; eauto 10 using star2_refl.
          * intros. zzsimpl; eauto 10 using star2_refl.
      - (* activated <-> activated *)
        pfold. zzsimpl.
        unfold upaco3 in *.
        econstructor 2; eauto using plus2_star2.
        * intros. zzsimpl; eauto 10 using star2_refl.
        * intros. zzsimpl; eauto 10 using star2_refl.
      - (* activated <-> err *)
        zzsimpl.
      - (* activated <-> term *)
        zzsimpl.
      - (* term <-> plus step *)
        case_eq (result σ1'); intros.
        + pfold. zzsimpl. zzcases.
          zzsimpl.
          econstructor 4; eauto. eauto.
        + zzsimpl.
          rewrite H4 in H10.
          destruct (@sim_t_Sim_normal_step _ _ _ _ _ _ _ H10 H9 H15); eauto.
          * subst.
            pfold. econstructor 3; eauto. congruence.
          * destruct H2; dcr.
            zzsimpl.
            pfold. econstructor 4; eauto. congruence.
      - zzsimpl.
      - (* term <-> err *)
        zzsimpl.
        pfold. econstructor 3; eauto. congruence.
      - (* term <-> term *)
        zzsimpl.
        pfold. econstructor 4; eauto. congruence.


            + econstructor 1. eauto. eauto.
              eapply H3; eauto.
              do 2 eexists; split; eauto.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          }
        + {
            inv H4; inv H6.
            - zzsimpl. zzcases.
              + econstructor 1. eauto. eauto.
              eapply H3; eauto.
              do 2 eexists; split; eauto.
              + econstructor 1. eauto. eauto.
                eapply H3; eauto.
                do 2 eexists; split; eauto.

          }

    Qed.

Lemma simc_trans_r_right {S} `{StateType S} {S'} `{StateType S'} r t
       (σ1:S) (σ2a σ2b:S) (σ3:S')
  : simc bot3 t σ1 σ2a
    -> (star2 step σ2a nil σ2b \/ star2 step σ2b nil σ2a)
    -> simc r t σ2b σ3
    -> simc r t σ1 σ3.
Proof.

Lemma simc_trans_r_right {S} `{StateType S} {S'} `{StateType S'} r t
       (σ1:S) (σ2a σ2b:S) (σ3:S')
  : simc bot3 t σ1 σ2a
    -> (star2 step σ2a nil σ2b \/ star2 step σ2b nil σ2a)
    -> simc r t σ2b σ3
    -> simc r t σ1 σ3.
Proof.
  eapply upto.
  unfold simc.
  revert σ1 σ2a σ2b σ3. eapply tower_ind; intros.
  hnf; intros; eauto.
  intros.
  assert (sim r t σ2b σ3). admit.
  eapply simc_sim in H4.
  eapply companion_fold; eauto using sim_gen_mon.
  destruct H4.
