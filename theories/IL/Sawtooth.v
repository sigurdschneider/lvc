Require Import AllInRel Util Map Env Exp IL DecSolve MoreList Sublist.
Require Export BlockType.

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
      rewrite H3. orewrite (f - (f + 0) = 0).
      simpl; econstructor; eauto.
    - exploit (sawtooth_smaller H0 H2).
      specialize (IHsawtooth _ _ H2).
      orewrite (f - block_n b
                = length L + (f - length L - block_n b)).
      rewrite drop_app; eauto.
Qed.

Lemma sawtooth_get {B} `{BlockType B} L f b
  : sawtooth L
    -> get L f b
    -> get (drop (f - block_n b) L) (block_n b) b.
Proof.
  intros ST Get.
  general induction ST; isabsurd.
  get_cases Get.
  - exploit tooth_index as Idx; eauto.
    rewrite Idx. orewrite (f + 0 = f).
    orewrite (f - f = 0); simpl.
    eauto using get_app.
  - exploit (sawtooth_smaller ST H1).
    specialize (IHST _ _ H1).
    orewrite (f - block_n b
              = length L + (f - length L - block_n b)).
    rewrite drop_app; eauto.
Qed.

Lemma stepGotoI' L E l Y blk vl
      (Ldef:get L l blk)
      (len:length (I.block_Z blk) = length Y)
      (def:omap (op_eval E) Y = Some vl) E'
      (updOk:E [I.block_Z blk <-- List.map Some vl] = E')
      (ST:sawtooth L)
  : step (drop (l - block_n blk) L, E, stmtApp (LabI (block_n blk)) Y)
         EvtTau
         (drop (l - block_n blk) L, E', I.block_s blk).
Proof.
  pattern (l - block_n blk) at 2.
  orewrite (l - block_n blk = block_n blk - block_n blk + (l - block_n blk)).
  rewrite <- drop_drop.
  eapply sawtooth_get in Ldef; eauto.
  eapply (I.StepGoto E (LabI (block_n blk)) Y Ldef len def); eauto.
Qed.

Lemma stepGotoF' L E l Y blk vl
      (Ldef:get L l blk)
      (len:length (F.block_Z blk) = length Y)
      (def:omap (op_eval E) Y = Some vl) E'
      (updOk:(F.block_E blk) [F.block_Z blk <-- List.map Some vl] = E')
      (ST:sawtooth L)
  : step (drop (l - block_n blk) L, E, stmtApp (LabI (block_n blk)) Y)
         EvtTau
         (drop (l - block_n blk) L, E', F.block_s blk).
Proof.
  pattern (l - block_n blk) at 2.
  orewrite (l - block_n blk = block_n blk - block_n blk + (l - block_n blk)).
  rewrite <- drop_drop.
  eapply sawtooth_get in Ldef; eauto.
  eapply (F.StepGoto E (LabI (block_n blk)) Y Ldef len def); eauto.
Qed.


Lemma tooth_I_mkBlocks n F
  : tooth n (mapi_impl I.mkBlock n F).
Proof.
  general induction F; simpl; econstructor; eauto.
Qed.

Lemma sawtooth_I_mkBlocks L F
  : sawtooth L
    -> sawtooth (mapi I.mkBlock F ++ L).
Proof.
  econstructor; eauto using tooth_I_mkBlocks.
Qed.

Lemma tooth_F_mkBlocks E n F
  : tooth n (mapi_impl (F.mkBlock E) n F).
Proof.
  general induction F; simpl; econstructor; eauto.
Qed.

Lemma sawtooth_F_mkBlocks E L F
  : sawtooth L
    -> sawtooth (mapi (F.mkBlock E) F ++ L).
Proof.
  econstructor; eauto using tooth_F_mkBlocks.
Qed.

Lemma sawtooth_app B `{BlockType B} L L'
  : sawtooth L -> sawtooth L' -> sawtooth (L ++ L').
Proof.
  intros H1 H2. general induction H1; eauto.
  rewrite <- app_assoc. econstructor; eauto.
Qed.


(*

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


Hint Resolve sawtooth_drop sawtooth_I_mkBlocks sawtooth_F_mkBlocks.

Hint Extern 10 =>
match goal with
  [ GET : get ?L ?f ?b, ST: sawtooth ?L |- sawtooth (drop (?f - ?n) ?L) ] =>
  change (sawtooth (drop (f - (block_n b)) L));
    eapply (sawtooth_drop ST GET)
end.

Lemma sawtooth_drop_eq B `{BlockType B} (L:list B) g f b c
      (ST:sawtooth L)
      (GETf : get L (g - block_n c + f) b)
      (GETg : get L g c)
  : f - (block_n b) + (g - block_n c) =  g - block_n c + f - (block_n b).
Proof.
  exploit (sawtooth_smaller ST); eauto. simpl in *.
  exploit (sawtooth_smaller ST GETf); eauto. simpl in *.
  exploit (sawtooth_resetting ST); eauto. omega.
Qed.

Smpl Create sawtooth.

Smpl Add
  match goal with
  | [ |- context [ _ ⊝ drop _ _ ] ] => rewrite !drop_map
  | [ |- context [ drop _ (drop _ _) ] ] => rewrite drop_drop
  end : sawtooth.

Smpl Add
     match goal with
       [ ST: sawtooth ?L,
             GETf : get ?L (?g - ?m + ?f) ?b,
                    GETg : get ?L ?g ?c
         |- context [ ?f - ?n + (?g - ?m) ] ] =>
       let REQ := fresh "REQ" in
       change (n) with (BlockType.block_n b);
         change (m) with (BlockType.block_n c);
         rewrite (@sawtooth_drop_eq _ _ L g f b c ST GETf GETg);
         simpl BlockType.block_n
     end : sawtooth.

Ltac sawtooth := repeat smpl sawtooth.


Lemma sawtooth_drop_app B `{BlockType B} f n b (L:list B) C (L' L'':list C)
      (ST:sawtooth L)
      (GETf: get L (f - n) b)
      (Len2: n = ❬L'❭)
      (GE: f >= n)
  : drop (f - block_n b) (L' ++ L'') = drop (f - ❬L'❭ - block_n b) L''.
Proof.
  pose proof (sawtooth_smaller ST GETf) as SMALLER.
  rewrite !drop_app_gen; try len_simpl.
  f_equal. omega. omega.
Qed.


Smpl Add
     match goal with
       [ H : sawtooth ?L, GET : get (?L' ++ ?L) ?f ?b |- _ ] =>
       let GE := fresh "GE" in
       eapply get_app_cases in GET; destruct GET as [GET|[GET GE]];
         try len_simpl; inv_get;
           simpl BlockType.block_n in *;
           simpl I.block_n in *;
           simpl F.block_n in *;
           try rewrite ZL_mapi
     end : sawtooth.

Smpl Add
     match goal with
       [ |- context [drop (?f - ?f) _ ] ] => orewrite (f - f = 0); simpl drop
     end : sawtooth.

Smpl Add match goal with
           [ ST: sawtooth ?L, GETf: get ?L (?f - ?n') ?b, GE : ?f >= ?n'
             |- context [ drop (?f - ?n) (?A ++ ?B) ] ] =>
           let EQLen := fresh "EQLen" in
           assert (EQLen:❬A❭ = n') by eauto with len;
             let EQ := fresh "EQ" in
             pose proof (@sawtooth_drop_app _ _ _ _ _ _ _ A B ST GETf
                                            ltac:(eauto with len) GE) as EQ;
               simpl BlockType.block_n in *;
               simpl I.block_n in *;
               simpl F.block_n in *;
               rewrite !EQ; rewrite EQLen
         end : sawtooth.
