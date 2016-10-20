Require Import Util List OptionMap LengthEq Map Get Take MoreList.

Set Implicit Arguments.

Fixpoint filter_by {A B} (f:A -> bool) (L:list A) (L':list B) : list B :=
  match L, L' with
    | x :: L, y::L' => if f x then y :: filter_by f L L' else filter_by f L L'
    | _, _ => nil
  end.

Fixpoint countTrue (L:list bool) :=
  match L with
  | nil => 0
  | true :: xs => 1 + countTrue xs
  | false :: xs => countTrue xs
  end.

Lemma countTrue_exists (L:list bool) n
  : get L n true
    -> countTrue L <> 0.
Proof.
  intros. general induction H; simpl; eauto.
  - cases; eauto.
Qed.

Lemma countTrue_app (L L':list bool)
  : countTrue (L ++ L') = countTrue L + countTrue L'.
Proof.
  intros. induction L; simpl; eauto.
  destruct a; eauto. omega.
Qed.

Arguments filter_by [A B] f L L'.

Lemma filter_by_ext A B (f f':A -> bool) L1 L1' (L2:list B)
  : length L1 = length L1'
    -> (forall n a a', get L1 n a -> get L1' n a' -> f a = f' a')
    -> filter_by f L1 L2 = filter_by f' L1' L2.
Proof.
  intros. length_equify.
  general induction H; destruct L2; simpl; eauto.
  - erewrite H0; eauto using get.
    cases; eauto using get.
    f_equal. eauto using get.
Qed.

Lemma map_filter_by A B C (f:A -> bool) (g:B -> C) L L'
  : g ⊝ filter_by f L L' = filter_by f L (g ⊝ L').
Proof.
  general induction L; destruct L'; simpl; repeat cases; simpl; f_equal; eauto.
Qed.

Lemma filter_by_app A B (f:A -> bool) L1 (L1':list B) L2 L2' (LEN: ❬L1❭ = ❬L1'❭)
  : filter_by f (L1 ++ L2) (L1' ++ L2') = filter_by f L1 L1' ++ filter_by f L2 L2'.
Proof.
  length_equify.
  general induction LEN; simpl; repeat cases; simpl; f_equal; eauto.
Qed.

Lemma filter_by_nil A B (f:A -> bool) L (L':list B)
  : (forall n b, get L n b -> f b = false)
    -> filter_by f L L' = nil.
Proof.
  intros.
  general induction L; destruct L'; simpl; repeat cases; simpl; f_equal; eauto using get.
  - exfalso. exploit H; eauto using get. congruence.
Qed.

Lemma filter_by_not_nil A B (f:A -> bool) L (L':list B) n b
  : ❬L❭ = ❬L'❭
    -> get L n b
    -> f b = true
    -> filter_by f L L' <> nil.
Proof.
  intros LEN Get Tru. length_equify.
  general induction LEN; simpl; repeat cases; simpl; f_equal; eauto using get; isabsurd.
  - inv Get; isabsurd; eauto.
Qed.

Lemma get_filter_by A B (p:A->bool) (Z:list A) (Y:list B) y n z
  : get Z n z
    -> get Y n y
    -> p z
    -> get (filter_by p Z Y) (countTrue (p ⊝ (take n Z))) y.
Proof.
  intros GetZ GetY Pz.
  eapply get_getT in GetZ.
  eapply get_getT in GetY.
  general induction GetZ; inv GetY; simpl in * |- *; isabsurd.
  - cases. eauto using get.
  - exploit IHGetZ; eauto.
    cases; eauto using get.
Qed.


Lemma filter_by_length A B  (p: A -> bool) L (L':list B)
  : ❬L❭ = ❬L'❭
    -> ❬filter_by p L L'❭ = countTrue (p ⊝ L).
Proof.
  intros LEN; length_equify.
  general induction LEN; simpl; eauto.
  cases; simpl; f_equal; eauto.
Qed.

Lemma filter_by_length' A B  (p: A -> bool) L (L':list B)
  : ❬filter_by p L L'❭ = countTrue (p ⊝ (take ❬L'❭ L)).
Proof.
  general induction L; destruct L'; simpl; eauto.
  cases; simpl; f_equal; eauto.
Qed.

Smpl Add
     match goal with
     | [ |- context [ ❬@filter_by ?T ?T' ?f ?A ?B❭ ] ] =>
       rewrite (@filter_by_length' T T' f A B)
     end : len.

Fixpoint posOfTrue (n:nat) (L:list bool) :=
  match L, n with
  | nil, _ => 0
  | true :: xs, S n => S (posOfTrue n xs)
  | true :: xs, 0 => 0
  | false :: xs, n => S (posOfTrue n xs)
  end.

Lemma filter_by_get A B p (Z:list A) (Y:list B) y n
: get (filter_by p Z Y) n y
  -> { z : A | get Y (posOfTrue n (p ⊝ Z)) y /\ get Z (posOfTrue n (p ⊝ Z)) z /\ p z }.
Proof.
  intros.
  general induction Z; destruct Y; simpl in * |- *; isabsurd.
  cases in H.
  - eapply get_getT in H.
    inv H.
    + do 2 eexists; repeat split; eauto using get.
    + eapply getT_get in X.
      edestruct IHZ as [? [? []]]; eauto; dcr.
      do 2 eexists; eauto using get.
  - edestruct IHZ as [? [? []]]; eauto; dcr; eauto.
    do 2 eexists; eauto using get.
Qed.

Lemma posOfTrue_countTrue L (n:nat)
: get L n true
  -> posOfTrue (countTrue (take n L)) L = n.
Proof.
  intros. general induction L; [ isabsurd |].
  - invc H; simpl; eauto.
    cases; f_equal; eauto.
Qed.


Lemma filter_get A p (Y:list A) y n
: get (List.filter p Y) n y
  -> get Y (posOfTrue n (p ⊝ Y)) y /\ p y.
Proof.
  intros.
  general induction Y; simpl in * |- *; isabsurd.
  cases in H.
  - eapply get_getT in H.
    inv H; eauto using get.
    + eapply getT_get in X.
      edestruct IHY as [? ?]; dcr; eauto using get.
  - edestruct IHY; dcr; eauto using get.
Qed.

Ltac inv_get_step_filter dummy :=
  first [inv_get_step |
         repeat (match goal with
         | [ H : get (filter_by ?p ?L ?L') ?n ?x |- _ ] =>
           eapply filter_by_get in H; try rewrite map_id in H; destruct H as [? [? [? ?]]]
         | [ H : get (filter ?p ?L) ?n ?x |- _ ] =>
           eapply filter_get in H; try rewrite map_id in H; destruct H as [H ?]
         | [ H : get _ (posOfTrue (countTrue (?f ⊝ take ?n ?L)) (?f ⊝ ?L)) _,
                 H' : get ?L ?n ?x, H'' : ?f ?x = true |- _ ] =>
           rewrite (@map_take _ _ f L) in H;
           rewrite (@posOfTrue_countTrue (f ⊝ L) n) in H;[| eauto using map_get_eq]
         end)
        ].

Tactic Notation "inv_get_step" := inv_get_step_filter idtac.
Tactic Notation "inv_get" := inv_get' inv_get_step_filter.

Lemma lookup_list_filter_by_commute A B C (V:A->B) (Z:list C) Y p
: length Z = length Y
  -> lookup_list V (filter_by p Z Y) =
    filter_by p Z (lookup_list V Y).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl; eauto.
  + cases; simpl; rewrite IHlength_eq; eauto.
Qed.


Lemma of_list_filter X `{OrderedType X} lv Y
  : of_list (List.filter (fun y : X => B[y ∈ lv]) Y) [=] lv ∩ of_list Y.
Proof.
  general induction Y; simpl.
  - cset_tac; intuition.
  - decide (a ∈ lv); simpl.
    rewrite IHY; eauto. cset_tac; intuition.
    rewrite IHY; eauto. cset_tac; intuition.
Qed.


Lemma omap_filter_by A B C f p (Y:list A) (l:list B) (Z:list C)
: omap f Y = Some l
  -> length Y = length Z
  -> omap f (filter_by p Z Y) = Some (filter_by p Z l).
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; simpl in * |- *; eauto.
  monad_inv H. cases; simpl; eauto.
  - rewrite EQ. erewrite IHlength_eq; simpl; eauto.
Qed.

Lemma filter_filter_by_length {X} {Y} (Z:list X) (VL:list Y)
: length Z = length VL
  -> forall p, length (List.filter p Z) =
    length (filter_by p Z VL).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl; eauto.
  cases; simpl. rewrite IHlength_eq; eauto. eauto.
Qed.

Hint Resolve filter_filter_by_length : len.

Lemma filter_incl2 X `{OrderedType X} (p:X->bool) Z
: of_list (List.filter p Z) ⊆ of_list Z.
Proof.
  general induction Z; simpl.
  - reflexivity.
  - cases; simpl. rewrite IHZ; reflexivity.
    rewrite IHZ. cset_tac; intuition.
Qed.

Lemma filter_p X p (Z:list X)
: forall n x, get (List.filter p Z) n x -> p x.
Proof.
  intros.
  general induction Z; simpl.
  - isabsurd.
  - simpl in H. cases in H. inv H. rewrite <- Heq. eapply I.
    eapply IHZ; eauto.
    eapply IHZ; eauto.
Qed.

Lemma filter_in X `{OrderedType X} (p:X->bool) `{Proper _ (_eq ==> eq) p} a Z
 :  p a
    -> a \In of_list Z
    -> a \In of_list (List.filter p Z).
Proof.
  general induction Z; simpl in * |- *; eauto.
  - cset_tac. rewrite <- H3 in H1.
    cases; isabsurd. rewrite <- H3. simpl. cset_tac; intuition.
    cases; eauto. simpl. exploit IHZ; eauto. cset_tac; intuition.
Qed.


Lemma agree_on_update_filter X `{OrderedType X} Y `{Equivalence (option Y)}
      (lv:set X) (V: X -> option Y) Z VL
: length Z = length VL
  -> agree_on R lv
             (V [Z <-- List.map Some VL])
             (V [List.filter (fun x => B[x ∈ lv]) Z <--
                             List.map Some (filter_by (fun x => B[x ∈ lv]) Z VL)]).
Proof.
  intros. eapply length_length_eq in H1.
  general induction H1.
  - eapply agree_on_refl. eapply H0.
  - simpl. cases. simpl. eapply agree_on_update_same. reflexivity.
    eapply agree_on_incl. eapply IHlength_eq. eauto. cset_tac; intuition.
    eapply agree_on_update_dead; eauto.
Qed.

Lemma agree_on_update_filter' X `{OrderedType X} Y `{Equivalence (option Y)} (lv:set X) (V V':X -> option Y) Z VL
: length Z = length VL
  -> agree_on R (lv \ of_list Z) V V'
  -> agree_on R lv
             (V [Z <-- List.map Some VL])
             (V' [(List.filter (fun x => B[x ∈ lv]) Z) <-- (List.map Some
                             (filter_by (fun x => B[x ∈ lv]) Z VL))]).
Proof.
  intros.
  eapply agree_on_trans. eapply H0.
  eapply update_with_list_agree; eauto. rewrite map_length; eauto.
  eapply agree_on_update_filter; eauto.
Qed.
