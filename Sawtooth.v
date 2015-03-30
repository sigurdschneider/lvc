Require Import AllInRel Util Map Env EnvTy Exp IL DecSolve MoreList InRel Sublist.

Set Implicit Arguments.
Unset Printing Records.

Inductive tooth {B} `{BlockType B}
: nat -> list B -> Prop :=
  | Tooth_nil n : tooth n nil
  | Tooth_cons n b L :
      tooth (S n) L
      -> n = block_n b
      -> tooth n (b::L).

Lemma tooth_index {B} `{BlockType B} (L:list B) n b f
: tooth n L -> get L f b -> block_n b = (f+n).
Proof.
  intros. general induction H1.
  - inv H0; eauto.
  - inv H0; eauto. erewrite IHget; eauto. omega.
Qed.

Inductive sawtooth {B} `{BlockType B}
: list B -> Prop :=
  | Sawtooth_nil : sawtooth nil
  | Sawtooth_app L L' :
      sawtooth L'
      -> tooth 0 L
      -> sawtooth (L++L').

Definition smaller {B} `{BlockType B} (L:list B) :=
        forall f b, get L f b -> f >= block_n b.

Definition resetting {B} `{BlockType B} (L:list B) :=
  (forall f n b b', get L f b -> get L (f - block_n b + n) b' -> n >= block_n b').

Tactic Notation "get_cases" hyp (H) :=
  eapply get_app_cases in H; destruct H as [?|[? ?]]; dcr.

Lemma sawtooth_smaller {B} `{BlockType B} (L:list B)
: sawtooth L -> smaller L.
Proof.
  intros. general induction H0.
  - isabsurd.
  - hnf; intros. get_cases H2.
    + erewrite tooth_index; eauto; omega.
    + pose proof (IHsawtooth _ _ H2). omega.
Qed.

Lemma sawtooth_resetting {B} `{BlockType B} (L:list B)
: sawtooth L -> resetting L.
Proof.
  intros. general induction H0.
  - isabsurd.
  - hnf; intros. get_cases H2; get_cases H3.
    + erewrite tooth_index; eauto.
      erewrite tooth_index; eauto. omega.
    + exploit tooth_index; eauto.
      exploit (sawtooth_smaller H0 H3). omega.
    + exploit (sawtooth_smaller H0 H2).
      exploit (get_length H3). omega.
    + eapply (IHsawtooth _ _ _ _ H2); eauto.
      exploit (sawtooth_smaller H0 H2).
      orewrite (f - length L - block_n b + n = f - block_n b + n - length L); eauto.
Qed.

Lemma sawtooth_drop {B} `{BlockType B} L f b
: sawtooth L
  -> get L f b
  -> sawtooth (drop (f - block_n b) L).
Proof.
    intros. general induction H0; simpl; isabsurd.
    get_cases H2.
    - exploit tooth_index; eauto.
      rewrite X. orewrite (f - (f + 0) = 0).
      simpl; econstructor; eauto.
    - exploit (sawtooth_smaller H0 H2).
      specialize (IHsawtooth _ _ H2).
      orewrite (f - block_n b
                = length L + (f - length L - block_n b)).
      rewrite drop_app; eauto.
Qed.

Lemma tooth_I_mkBlocks n F
  : tooth n (mapi_impl I.mkBlock n F).
Proof.
  general induction F; simpl; econstructor; eauto.
Qed.

Lemma sawtooth_I_mkBlocks L F
  : sawtooth L
    -> sawtooth (I.mkBlocks F ++ L).
Proof.
  econstructor; eauto using tooth_I_mkBlocks.
Qed.
(*
Lemma nth_drop X (L:list X) n m x
: nth n (drop m L) x = nth (n+m) L x.
Proof.
  general induction m; simpl. orewrite (n + 0 = n); eauto.
  rewrite IHm; eauto. orewrite (n + S m = S (n + m)); eauto.
  destruct L; simpl; eauto. destruct (n + m); eauto.
Qed.

Lemma drop_length_ge (X : Type) (L L' : list X) (n : nat)
: n >= length L' -> drop n (L' ++ L) = drop (n - length L') L.
Proof.
  general induction L'; simpl. orewrite (n - 0 = n); eauto.
  destruct n; simpl. inv H.
  rewrite IHL'; eauto. simpl in *; omega.
Qed.

Lemma nth_mapi_impl X Y (L:list X) (f:nat->X->Y) n i y x
 : n < length L -> nth n (mapi_impl f i L) y = f (n+i) (nth n L x).
Proof.
  general induction L.
  - inv H.
  - destruct n; simpl in *; eauto.
    + orewrite (S (n + i) = n + (S i)). erewrite <- IHL; eauto. omega.
Qed.

Lemma nth_mapi X Y (L:list X) (f:nat->X->Y) n y x
 : n < length L -> nth n (mapi f L) y = f n (nth n L x).
Proof.
  intros. pose proof (nth_mapi_impl L f 0 y x H).
  orewrite (n + 0 = n) in H0. eauto.
Qed.

Lemma mapi_app X Y (f:nat -> X -> Y) n L L'
: mapi_impl f n (L++L') = mapi_impl f n L ++ mapi_impl f (n+length L) L'.
Proof.
  general induction L; simpl; eauto.
  - orewrite (n + 0 = n); eauto.
  - f_equal. rewrite IHL. f_equal; f_equal. omega.
Qed.

Lemma app_drop X (L L' L'':list X)
 : L = L' ++ L''
   -> drop (length L') L = L''.
Proof.
  general induction L'; simpl; eauto.
Qed.

Lemma drop_app_eq X (L L' : list X) n
: length L = n
  -> drop n (L ++ L') = L'.
Proof.
  intros; subst. orewrite (length L = length L + 0) . eapply drop_app.
Qed.
*)

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
