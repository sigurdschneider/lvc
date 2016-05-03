Require Import Util Get CSet Relations AllInRel MoreList SetOperations.

Set Implicit Arguments.

Definition oget {X} `{OrderedType X} (s:option (set X)) :=
  match s with Some s => s | None => ∅ end.


Definition oto_list {X} `{OrderedType X} (s:option (set X)) :=
  match s with Some s => to_list s | None => nil end.

Definition ounion {X} `{OrderedType X} (s t: option (set X)) :=
  match s, t with
    | Some s, Some t => Some (s ∪ t)
    | Some s, None => Some s
    | None, Some t => Some t
    | _, _ => None
  end.


Lemma ounion_comm X `{OrderedType X} (s t:option (set X))
  : option_eq Equal (ounion s t) (ounion t s).
Proof.
  destruct s,t; simpl; try now econstructor.
  - econstructor. cset_tac; intuition.
Qed.

Lemma ounion_left_Some X `{OrderedType X} s t
  : ounion (Some s) t === Some (s ∪ oget t).
Proof.
  destruct t; simpl.
  - cset_tac.
  - econstructor. hnf. cset_tac.
Qed.

Lemma ounion_right_Some X `{OrderedType X} s t
  : ounion s (Some t) === Some (oget s ∪ t).
Proof.
  destruct s; simpl.
  - cset_tac.
  - econstructor. hnf. cset_tac.
Qed.

Lemma fold_zip_ounion_length X `{OrderedType X} a b
  : (forall n aa, get a n aa -> length aa = length b)
    -> length (fold_left (zip ounion) a b) = length b.
Proof.
  intros LEN.
  general induction a; simpl; eauto.
  rewrite IHa; eauto 10 using get with len.
Qed.


Notation "≽" := (fstNoneOrR (flip Subset)).
Notation "≼" := (fstNoneOrR (Subset)).
Notation "A ≿ B" := (PIR2 (fstNoneOrR (flip Subset)) A B) (at level 60).

Instance fstNoneOrR_flip_Subset_trans {X} `{OrderedType X} : Transitive ≽.
Proof.
hnf; intros. inv H1; inv H0; eauto using @fstNoneOrR.
- econstructor. transitivity x0; eauto.
Qed.

Instance fstNoneOrR_flip_Subset_trans2 {X} `{OrderedType X} : Transitive ≼.
Proof.
hnf; intros. inv H0; inv H1; eauto using @fstNoneOrR.
- econstructor. transitivity y0; eauto.
Qed.

Lemma PIR2_ounion {X} `{OrderedType X} (A B C:list (option (set X)))
: length A = length B
  -> length B = length C
  -> PIR2 ≽ A C
  -> PIR2 ≽ B C
  -> PIR2 ≽ (zip ounion A B) C.
Proof.
  intros. length_equify.
  general induction H0; inv H1; simpl.
  - econstructor.
  - simpl in *. inv H2; inv H3.
    exploit IHlength_eq; eauto.
    inv pf; inv pf0; simpl; try now (econstructor; [econstructor; eauto| eauto]).
    econstructor; eauto. econstructor. unfold flip in *.
    cset_tac; intuition.
Qed.

Lemma PIR2_ounion' {X} `{OrderedType X} (A B C:list (option (set X)))
: length A = length B
  -> length B = length C
  -> PIR2 ≼ C A
  -> PIR2 ≼ C B
  -> PIR2 ≼ C (zip ounion A B).
Proof.
  intros. length_equify.
  general induction H0; inv H1; simpl.
  - econstructor.
  - simpl in *. inv H2; inv H3.
    exploit IHlength_eq; eauto.
    inv pf; inv pf0; simpl;
    (econstructor; [econstructor; eauto with cset | eauto]).
Qed.

Lemma PIR2_ounion_AB {X} `{OrderedType X} (A A' B B':list (option (set X)))
: length A = length A'
  -> length B = length B'
  -> length A = length B
  -> PIR2 ≼ A A'
  -> PIR2 ≼ B B'
  -> PIR2 ≼ (zip ounion A B) (zip ounion A' B').
Proof.
  intros. length_equify.
  general induction H0; inv H1; inv H2; simpl; econstructor.
  - inv H3; inv H4.
    inv pf; inv pf0; simpl; try econstructor.
    destruct y; simpl; eauto. econstructor. cset_tac; intuition.
    destruct y0; simpl; eauto. econstructor. cset_tac; intuition.
    cset_tac; intuition.
  - inv H3; inv H4. eapply IHlength_eq; eauto.
Qed.

Lemma PIR2_option_eq_Subset_zip {X} `{OrderedType X} (A B C:list (option (set X)))
: length A = length B
  -> length B = length C
  -> PIR2 (option_eq Subset) C A
  -> PIR2 (option_eq Subset) C B
  -> PIR2 (option_eq Subset) C (zip ounion A B).
Proof.
  intros. length_equify.
  general induction H0; inv H1; simpl.
  - econstructor.
  - simpl in *. inv H2; inv H3.
    exploit IHlength_eq; eauto.
    inv pf; inv pf0; simpl;
    now (econstructor; [econstructor; eauto with cset | eauto]).
Qed.

Lemma ifFstR_zip_ounion X `{OrderedType X} A B C
: PIR2 (ifFstR Subset) A C
  -> PIR2 (ifFstR Subset) B C
  -> PIR2 (ifFstR Subset) (zip ounion A B) C.
Proof.
  intros.
  general induction H0.
  - inv H1; econstructor.
  - inv H1.
    inv pf; inv pf0; simpl; try now (econstructor; [econstructor; eauto| eauto]).
    econstructor; eauto. econstructor.
    cset_tac; intuition.
Qed.

Lemma PIR2_ifFstR_option_eq_left X `{OrderedType X} A B C
      : PIR2 (ifFstR Subset) B C
        -> PIR2 (option_eq Subset) A B
        -> PIR2 (ifFstR Subset) A C.
Proof.
  intros H1 H2. general induction H2; inv H1; eauto using @PIR2.
  econstructor; eauto.
  inv pf; try econstructor. inv pf0. intuition.
Qed.

Lemma PIR2_ifFstR_Subset_right X `{OrderedType X} A B C
: PIR2 (ifFstR Subset) A B
-> PIR2 Subset B C
-> PIR2 (ifFstR Subset) A C.
Proof.
  intros P S. general induction P; inv S; simpl in *; eauto using PIR2.
  - inv pf; eauto using PIR2, @ifFstR.
    econstructor; eauto.
    econstructor; cset_tac; intuition.
Qed.


Lemma ifFstR_fold_zip_ounion X `{OrderedType X} A B C
  : (forall n a, get A n a -> PIR2 (ifFstR Subset) a C)
    -> PIR2 (ifFstR Subset) B C
    -> PIR2 (ifFstR Subset) (fold_left (zip ounion) A B) C.
Proof.
  intros GET LE.
  general induction A; simpl; eauto.
  - eapply IHA; eauto using get, ifFstR_zip_ounion.
Qed.

Lemma PIR2_flip_Subset_ext_right X `{OrderedType X} A B B'
  : A ≿ B
    -> PIR2 (option_eq Equal) B B'
    -> A ≿ B'.
Proof.
  intros GE EQ. general induction GE; inv EQ; eauto.
  econstructor; eauto.
  inv pf; inv pf0; econstructor.
  rewrite <- H2. eauto.
Qed.

Lemma PIR2_map_some {X} R (AP AP':list X)
: length AP = length AP'
  -> PIR2 R AP AP'
  -> PIR2 (fstNoneOrR R) (List.map Some AP) (List.map Some AP').
Proof.
  intros. general induction H0.
  + econstructor.
  + simpl. econstructor.
    - econstructor; eauto.
    - eauto.
Qed.

Lemma PIR2_map_some_option {X} R (AP AP':list X)
: length AP = length AP'
  -> PIR2 R AP AP'
  -> PIR2 (option_eq R) (List.map Some AP) (List.map Some AP').
Proof.
  intros. general induction H0.
  + econstructor.
  + simpl. econstructor.
    - econstructor; eauto.
    - eauto.
Qed.


Lemma PIR2_ifSndR_Subset_left X `{OrderedType X} A B C
: PIR2 (ifSndR Subset) B C
-> PIR2 Subset A B
-> PIR2 (ifSndR Subset) A C.
Proof.
  intros. general induction H1; simpl in *.
  + inv H0. econstructor.
  + inv H0. inv pf0; eauto using @PIR2, @ifSndR with cset.
Qed.


Lemma ifSndR_zip_ounion X `{OrderedType X} A B C
: PIR2 (ifSndR Subset) C A
  -> PIR2 (ifSndR Subset) C B
  -> PIR2 (ifSndR Subset) C (zip ounion A B).
Proof.
  intros.
  general induction H0.
  - inv H1; econstructor.
  - inv H1.
    inv pf; inv pf0; eauto using @PIR2, @ifSndR with cset.
Qed.

Lemma ifSndR_fold_zip_ounion X `{OrderedType X} A B C
: (forall n a, get A n a -> PIR2 (ifSndR Subset) C a)
  -> PIR2 (ifSndR Subset) C B
  -> PIR2 (ifSndR Subset) C (fold_left (zip ounion) A B).
Proof.
  intros GET LE.
  general induction A; simpl; eauto.
  - eapply IHA; eauto using get, ifSndR_zip_ounion.
Qed.


Lemma PIR2_zip_ounion X `{OrderedType X} (b:list (option (set X))) b'
  : length b = length b'
    -> PIR2 (fstNoneOrR Subset) b (zip ounion b b').
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; simpl.
  - econstructor.
  - econstructor; eauto.
    + destruct x,y; simpl; econstructor; cset_tac; intuition.
Qed.

Lemma PIR2_zip_ounion' X `{OrderedType X} (b:list (option (set X))) b'
  : length b = length b'
    -> PIR2 (fstNoneOrR Subset) b (zip ounion b' b).
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; simpl.
  - econstructor.
  - econstructor; eauto.
    + destruct x,y; simpl; econstructor; cset_tac; intuition.
Qed.


Lemma fstNoneOrR_ounion_left X `{OrderedType X} a b c
  : ≼ a b -> ≼ a (ounion b c).
Proof.
  intros A; inv A; eauto using @fstNoneOrR.
  destruct c; simpl; eauto.
  econstructor. cset_tac.
Qed.


Lemma fstNoneOrR_ounion_right X `{OrderedType X} a b c
  : ≼ a c -> ≼ a (ounion b c).
Proof.
  intros A; inv A; eauto using @fstNoneOrR.
  destruct b; simpl; eauto.
  econstructor. cset_tac.
Qed.

Lemma PIR2_ounion_left X `{OrderedType X} (A B C:list (option (set X)))
: length A = length B
  -> PIR2 ≼ C A
  -> PIR2 ≼ C (zip ounion A B).
Proof.
  intros. length_equify.
  general induction H0; invt PIR2; simpl.
  - econstructor.
  - exploit IHlength_eq; eauto.
    econstructor; eauto using fstNoneOrR_ounion_left.
Qed.

Lemma PIR2_ounion_right X `{OrderedType X} (A B C:list (option (set X)))
: length A = length C
  -> PIR2 ≼ C B
  -> PIR2 ≼ C (zip ounion A B).
Proof.
  intros. length_equify.
  general induction H0; invt PIR2; simpl.
  - econstructor.
  - exploit IHlength_eq; eauto.
    econstructor; eauto using fstNoneOrR_ounion_left, fstNoneOrR_ounion_right.
Qed.


Lemma PIR2_ifFstR_Subset_oget X `{OrderedType X} A B
  : PIR2 (ifFstR Subset) A B
    -> PIR2 Subset (oget ⊝ A) B.
Proof.
  intros PIR. general induction PIR; simpl in *; eauto using PIR2.
  - inv pf; eauto using @PIR2, @ifSndR with cset.
Qed.

Instance PIR2_subset_impl X `{OrderedType X}
  : Proper (PIR2 (flip Subset) ==> PIR2 Subset ==> impl) (PIR2 Subset).
Proof.
  unfold Proper, respectful, impl, flip; intros.
  general induction H0; inv H1; inv H2; eauto using PIR2 with cset.
  econstructor; eauto. rewrite pf, pf1; eauto.
Qed.

Instance PIR2_Subset_Equal_Equal_impl X `{OrderedType X}
  : Proper (PIR2 Equal ==> PIR2 Equal ==> impl) (PIR2 Equal).
Proof.
  unfold Proper, respectful, impl; intros.
  general induction H0; inv H1; inv H2; eauto using PIR2 with cset.
  econstructor; eauto. rewrite <- pf, <- pf0. eauto.
Qed.

Instance PIR2_Subset_Equal_Equal_flip_impl X `{OrderedType X}
  : Proper (PIR2 Equal ==> PIR2 Equal ==> flip impl) (PIR2 Equal).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  general induction H0; inv H1; inv H2; eauto using PIR2 with cset.
  econstructor; eauto. rewrite pf, pf0. eauto.
Qed.

Instance PIR2_Equal_Subset_subrelation X `{OrderedType X}
  : subrelation (PIR2 Equal) (PIR2 Subset).
Proof.
  unfold subrelation; intros x y PIR.
  general induction PIR; eauto using PIR2.
  econstructor. rewrite pf; eauto. eauto.
Qed.

Instance map_Equal_impl X Y `{OrderedType Y}
  : Proper (@feq X (set Y) Equal ==> eq ==> PIR2 Equal) (@List.map _ _).
Proof.
  unfold Proper, respectful. intros; subst.
  general induction y0; simpl; eauto using PIR2.
Qed.

Instance app_Equal_Equal_Equal X `{OrderedType X}
  : Proper (PIR2 Equal ==> PIR2 Equal ==> PIR2 Equal) (@List.app _).
Proof.
  unfold Proper, respectful. intros; subst.
  eapply PIR2_app; eauto.
Qed.

Lemma of_list_oto_list_oget X `{OrderedType X}
  : @feq _ _ Equal (fun x => of_list (oto_list x)) oget.
Proof.
  hnf; intros L. destruct L; eauto. unfold oto_list. rewrite of_list_3; eauto.
Qed.
