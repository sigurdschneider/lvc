Require Import Util Containers.OrderedTypeEx OrderedTypeComputable.
Require Import Setoid Coq.Classes.Morphisms Computable Coq.Classes.RelationClasses.

Definition _le X `{OrderedType X} (x y : X) := _lt x y \/ _eq x y.

Arguments _le {X H} x y : simpl never.

Lemma OT_le_refl X `{OrderedType X} x y : _eq x y -> _le x y.
Proof.
  firstorder.
Qed.

Instance OT_le_refl' X `{OrderedType X} : Reflexive _le.
Proof.
  hnf; intros.
  eapply OT_le_refl. reflexivity.
Qed.

Instance OT_le_trans X `{OrderedType X} : Transitive _le.
Proof.
  unfold _le; hnf; intros; destruct H0, H1; eauto.
  - left; etransitivity; eauto.
  - rewrite <- H1; eauto.
  - rewrite H0; eauto.
  - right; etransitivity; eauto.
Qed.

Instance OT_le_antisymmetric X `{OrderedType X} : Antisymmetric X _eq _le.
Proof.
  hnf; intros. destruct H0, H1; eauto.
  exfalso.
  assert (_lt x x) by (etransitivity; eauto).
  eapply (@OrderedType.StrictOrder_Irreflexive X _ _ _ (@OT_StrictOrder _ H)); eauto.
Qed.

Instance OT_le_morph X `{OrderedType X}
  : Proper (@_eq X _ ==> @_eq X _ ==> iff) (@_le X _).
Proof.
  unfold Proper, respectful; intros.
  split; eauto; intros; destruct H2; hnf;
    rewrite H0 in *; rewrite H1 in *; eauto.
Qed.

Instance OT_le_lt_morph X `{OrderedType X}
  : Proper (_eq ==> flip _lt ==> flip impl) (@_le X _).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  destruct H2; eauto.
  - rewrite H0. left. etransitivity; eauto.
  - rewrite H0. rewrite H2 in *. left; eauto.
Qed.

Instance OT_le_lt_morph_eq X `{OrderedType X}
  : Proper (@_lt X _ ==> _eq ==> flip impl) (@_le X _).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  destruct H2; eauto.
  - left. rewrite H1. rewrite H0. eauto.
  - rewrite H2 in *. rewrite H1 in *. left; eauto.
Qed.

Instance OT_le_lt_morph' X `{OrderedType X}
  : Proper (flip _lt ==> _eq ==> impl) (@_le X _).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  destruct H2; eauto.
  - left. rewrite <- H1. rewrite H0. eauto.
  - rewrite <- H1. rewrite <- H2. left; eauto.
Qed.

Instance OT_le_lt_morph'' X `{OrderedType X}
  : Proper (_eq ==> _lt ==> impl) (@_le X _).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  destruct H2; eauto.
  - left. rewrite H0 in *. etransitivity; eauto.
  - rewrite H0 in *. rewrite H2 in *. left. eauto.
Qed.

Lemma OT_lt_le X `{OrderedType X} x y
  : _lt x y -> _le x y.
Proof.
  left; eauto.
Qed.

Hint Resolve OT_lt_le | 100 .

Instance OT_le_impl_morph X `{OrderedType X}
  : Proper (@_le X _ ==> flip _le ==> flip impl) (@_le X _).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  destruct H0, H1, H2;
    try rewrite H0 in *; try rewrite H1 in *; try rewrite H2 in *; eauto using OT_lt_le;
      try solve [
            etransitivity; eauto using OT_lt_le
          | reflexivity
          ].
Qed.

Instance OT_le_impl_morph' X `{OrderedType X}
  : Proper (flip _le ==> _le ==> impl) (@_le X _).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  rewrite H0, <- H1, H2. reflexivity.
Qed.

Instance OT_lt_le_morph X `{OrderedType X}
  : Proper (flip _le ==> _le ==> impl) (@_lt X _).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  destruct H0, H1; eauto.
  - rewrite H0, H2; eauto.
  - rewrite H0, <- H1; eauto.
  - rewrite H0, <- H1; eauto.
  - rewrite H0, <- H1; eauto.
Qed.

Instance OT_lt_le_morph' X `{OrderedType X}
  : Proper (_le ==> flip _le ==> flip impl) (@_lt X _).
Proof.
  unfold Proper, respectful, flip, impl; intros.
  destruct H0, H1; eauto.
  - rewrite H0, H2; eauto.
  - rewrite H0, <- H1; eauto.
  - rewrite H0, <- H1; eauto.
  - rewrite H0, <- H1; eauto.
Qed.

Hint Extern 20 (_le ?a ?a') => progress (first [ has_evar a | has_evar a' | reflexivity ]).

Hint Extern 20 =>
  match goal with
  | [ H : _lt ?x ?y, H' : _lt ?y ?x |- _ ] =>
    exfalso;
      rewrite H' in H;
      eapply OrderedType.StrictOrder_Irreflexive in H; eauto
  | [ H : _lt ?x ?y, H' : _eq ?y ?x |- _ ] =>
    exfalso;
      rewrite H' in H;
      eapply OrderedType.StrictOrder_Irreflexive in H; eauto
  | [ H : _lt ?x ?y, H' : _eq ?x ?y |- _ ] =>
    exfalso;
      rewrite H' in H;
      eapply OrderedType.StrictOrder_Irreflexive in H; eauto
  end.


Lemma OT_le_lt_contra X `{OrderedType X} x y
  : _le y x
    -> _lt x y -> False.
Proof.
  destruct 1; intros; eauto.
Qed.

Hint Extern 20 =>
match goal with
| [ H : _le ?y ?x, H' : _lt ?x ?y |- _ ] => exfalso; eapply (@OT_le_lt_contra _ _ _ _ H H')
end.
