Require Import CSet.

Set Implicit Arguments.

Instance prod_eq_refl X Y R R' `{Reflexive X R} `{Reflexive Y R'}
  : Reflexive (prod_eq R R').
Proof.
  hnf; intros. destruct x; econstructor; reflexivity.
Qed.

Instance pe_sym X Y R R' `{Symmetric X R} `{Symmetric Y R'}
  : Symmetric (prod_eq R R').
Proof.
  hnf; intros. inv H1; econstructor; eauto.
Qed.

Instance pe_trans  X Y R R' `{Transitive X R} `{Transitive Y R'}
  : Transitive (prod_eq R R').
Proof.
  hnf; intros ? ? ? B C.
  invc B; invc C; econstructor; eauto.
Qed.

Instance pe_morphism X Y (R:relation X) `{Transitive _ R}
         (R':relation Y) `{Transitive _ R'}
 : Proper ((flip (prod_eq R R')) ==> prod_eq R R' ==> impl) (prod_eq R R').
Proof.
  unfold Proper, respectful.
  intros. inv H1; inv H2; inversion 1; subst; econstructor; eauto.
Qed.

Instance pe_morphism' X `{OrderedType X}
 : Proper (prod_eq Equal Equal ==> prod_eq Equal Equal ==> iff) (prod_eq Equal Subset).
Proof.
  unfold Proper, respectful.
  intros. inv H0; inv H1; split; inversion 1; subst; econstructor; eauto;
  cset_tac; firstorder.
Qed.

Instance pe_morphism'' X `{OrderedType X}
 : Proper (prod_eq Equal Equal ==> prod_eq Equal Equal ==> impl) (prod_eq Equal Subset).
Proof.
  unfold Proper, respectful.
  intros. inv H0; inv H1; inversion 1; subst; econstructor; eauto;
  cset_tac; firstorder.
Qed.

Instance pe_morphism''' X `{OrderedType X}
 : Proper (prod_eq Equal Equal ==> prod_eq Equal Equal ==> flip impl) (prod_eq Equal Subset).
Proof.
  unfold Proper, respectful.
  intros. inv H0; inv H1; inversion 1; subst; econstructor; eauto;
  cset_tac; firstorder.
Qed.


Lemma prod_eq_proj1 X Y R R' (p p':X*Y)
  : prod_eq R R' p p'
    -> R (fst p) (fst p').
Proof.
  inversion 1; eauto.
Qed.

Lemma prod_eq_proj2 X Y R R' (p p':X*Y)
  : prod_eq R R' p p'
    -> R' (snd p) (snd p').
Proof.
  inversion 1; eauto.
Qed.

Hint Resolve prod_eq_intro.

Lemma pe_eta_split X Y R R' (x:X* Y) y z
  : prod_eq R R' (fst x, snd x) (y, z)
    -> prod_eq R R' x (y,z).
Proof.
  destruct x; eauto.
Qed.
