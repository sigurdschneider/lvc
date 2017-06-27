Require Import Util CSet LengthEq List Get Computable DecSolve AllInRel Omega.
Require Import Keep OptionR MoreList OUnion Annotation.


Lemma PIR2_ifSndR_keep X `{OrderedType X} n (AP:〔⦃X⦄〕)
  :  PIR2 (ifSndR Subset) AP (keep n AP).
Proof.
  unfold keep, mapi. generalize 0.
  general induction AP; simpl.
  - econstructor.
  - cases; eauto using PIR2, @ifSndR.
Qed.


Lemma zip_AP_mon X Y `{OrderedType Y}
      (AP:list (set Y)) (DL:list X) (f:X -> set Y  -> set Y)
      (LEN:length DL = length AP)
  : (forall x y, y ⊆ f x y)
    -> PIR2 Subset AP (zip f DL AP).
Proof.
  length_equify.
  general induction LEN; simpl; eauto using PIR2.
Qed.

Lemma drop_fold_zip_ounion X `{OrderedType X} A B k
  : (forall n a, get A n a -> length a = length B)
    -> (drop k (fold_left (zip ounion) A B)) =
      fold_left (zip ounion) (List.map (drop k) A) (drop k B).
Proof with eauto 20 using get with len.
  general induction A; simpl; eauto.
  - rewrite IHA...
    + rewrite drop_zip...
Qed.

Notation "'olist_union' A B" := (fold_left (zip ounion) A B) (at level 50, A at level 0, B at level 0).

Lemma PIR2_olist_union_bound X `{OrderedType X} A b c
  : ( forall n a, get A n a -> PIR2 (ifFstR Subset) a c)
    -> PIR2 (ifFstR Subset) b c
    -> PIR2 (ifFstR Subset) (olist_union A b) c.
Proof.
  intros. general induction A; simpl; eauto.
  - eapply IHA; eauto using get, ifFstR_zip_ounion.
Qed.

Lemma get_olist_union_b X `{OrderedType X} A b n x
  : get b n (Some x)
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> exists s, get (olist_union A b) n (Some s) /\ x ⊆ s.
Proof.
  intros GETb LEN. general induction A; simpl in *.
  - eexists x. eauto with cset.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETb (eq_sym H0)) as [y GETa]; eauto.
    exploit (zip_get ounion GETb GETa).
    destruct y; simpl in *.
    + exploit IHA; try eapply GET; eauto.
      rewrite zip_length2; eauto using get with len.
      edestruct H2; dcr; subst. eexists; split; eauto.
      rewrite <- H7; eauto.
    + exploit IHA; try eapply GET; eauto.
      rewrite zip_length2; eauto using get with len.
Qed.

Lemma get_olist_union_A X `{OrderedType X} A a b n k x
  : get A k a
    -> get a n (Some x)
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> exists s, get (olist_union A b) n (Some s) /\ x ⊆ s.
Proof.
  intros GETA GETa LEN.
  general induction A; simpl in * |- *; isabsurd.
  inv GETA; eauto.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETa H0) as [y GETb].
    exploit (zip_get ounion GETb GETa).
    destruct y; simpl in *.
    exploit (@get_olist_union_b _ _ A); eauto.
    rewrite zip_length2; eauto using get with len.
    destruct H2; dcr; subst. eexists; split; eauto.
    rewrite <- H4; eauto.
    eapply get_olist_union_b; try eapply GETunion; eauto.
    rewrite zip_length2; eauto using get with len.
  - eapply IHA; eauto.
    rewrite zip_length2; eauto using get with len.
Qed.

Lemma get_olist_union_A' X `{OrderedType X} A a b n k x p
  : get A k a
    -> get a n (Some x)
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> get (olist_union A b) n p
    -> exists s, p = (Some s) /\ x ⊆ s.
Proof.
  intros. edestruct get_olist_union_A; eauto; dcr.
  get_functional; eauto.
Qed.

Tactic Notation "Rexploit" uconstr(H) :=
  eapply modus_ponens; [refine H | intros].

Tactic Notation "Rexploit" uconstr(X) "as" ident(H)  :=
  eapply modus_ponens; [refine X | intros H].

Lemma get_fold_zip_join X (f: X-> X-> X) (A:list (list X)) (b:list X) n
  : n < ❬b❭
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> exists y, get (fold_left (zip f) A b) n y.
Proof.
  intros LE LEN. general induction A; simpl in *.
  - edestruct get_in_range; eauto.
  - exploit LEN; eauto using get.
    eapply IHA; eauto using get with len.
Qed.

Definition ominus' {X} `{OrderedType X} (s : set X) (t : option (set X))
  := mdo t' <- t; ⎣s \ t' ⎦.

Definition minuso {X} `{OrderedType X}
           (s : set X) (t : option (set X)) := ⎣s \ oget t ⎦.

Lemma zip_ominus_contra {X} `{OrderedType X} DL b b'
  : PIR2 (fstNoneOrR Subset) b b'
    -> zip ominus' DL b ≿ zip ominus' DL b'.
Proof.
  intros.
  general induction H0; destruct DL; simpl; eauto using PIR2.
  - econstructor; eauto.
    + inv pf; simpl; econstructor.
      unfold flip. rewrite H1. eauto.
Qed.


Lemma PIR2_combineParams {X} `{OrderedType X}
      (A:list (ann (list (list X)) * list (option (set X))))
      (B C:list (option (set X)))
  : (forall n a, get A n a -> length (snd a) = length B)
    -> PIR2 ≼ B C
    -> PIR2 ≼ B (olist_union (List.map snd A) C).
Proof.
  general induction B; invt PIR2.
  - clear H0. general induction A; eauto.
  - general induction A.
    + econstructor; eauto.
    + exploit H0; eauto using get.
      destruct a. destruct l; isabsurd. simpl in *.
      assert (length YL = length l). {
        eapply PIR2_length in H1. simpl in *. omega.
      }
      eapply IHA; eauto 10 using fstNoneOrR_ounion_left,
                  PIR2_ounion_left, get, @PIR2 with len.
Qed.

Lemma PIR2_combineParams_get {X} `{OrderedType X}
      (A:list (ann (list (list X)) * list (option (set X))))
      (B C:list (option (set X))) n a
  : (forall n a, get A n a -> length (snd a) = length B)
    -> length B = length C
    -> get A n a
    -> PIR2 ≼ B (snd a)
    -> PIR2 ≼ B (olist_union (List.map snd A) C).
Proof.
  intros LEN1 LEN2 GET P. length_equify.
  general induction LEN2; simpl.
  - clear LEN1 GET P. general induction A; eauto.
  - clear IHLEN2.
    general induction GET; simpl.
    + exploit (LEN1); eauto using get.
      destruct x. destruct l; isabsurd. simpl in *.
      eapply PIR2_combineParams; eauto using get.
      inv P.
      econstructor; eauto using fstNoneOrR_ounion_right, PIR2_ounion_right with len.
    + exploit (LEN1); eauto using get.
      destruct x'. destruct l; isabsurd. simpl in *.
      eapply IHGET; eauto using get with len.
      eapply length_length_eq. rewrite zip_length2; try omega. eauto with len.
      eapply length_eq_length in LEN2. omega.
Qed.

Lemma PIR2_ominus_minuso {X} `{OrderedType X} A B B'
  : PIR2 (fstNoneOrR Subset) B B'
    -> ominus' ⊜ A B ≿ minuso ⊜ A B'.
Proof.
  intros EQ.
  general induction EQ; destruct A; simpl; eauto.
  econstructor; eauto.
  inv pf; simpl; econstructor.
  simpl. unfold flip. rewrite H0. reflexivity.
Qed.

Notation "DL \\ ZL" := (zip (fun s L => s \ of_list L) DL ZL) (at level 50).

Lemma ominus'_Some_oto_list {X} `{OrderedType X} A B C1 C2
  : PIR2 ≼ C1 C2
    -> ominus' ⊜ (A \\ B) C1 ≿ Some ⊝ A \\ app (A:=X) ⊜ B (oto_list ⊝ C2).
Proof.
  intros.
  general induction H0; simpl; destruct A, B; try reflexivity.
  - simpl; econstructor; eauto.
    + inv pf; simpl ominus'. econstructor.
      econstructor. unfold flip, oto_list.
      rewrite of_list_app. rewrite of_list_3.
      unfold flip in H0. rewrite <- minus_union.
      rewrite H1. reflexivity.
Qed.
