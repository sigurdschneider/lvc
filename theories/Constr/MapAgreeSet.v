Require Export Setoid Coq.Classes.Morphisms.
Require Import EqDec Computable Util AutoIndTac.
Require Export CSet Containers.SetDecide.
Require Export MapBasics MapLookup MapAgreement.

Set Implicit Arguments.


Section MapAgreeSet.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.
  Context `{OrderedType Y}.

  Definition agree_set (lv:set X) (m m':X -> Y) : set X
    := filter (fun x => if [m x === m' x] then true else false) lv.

  Lemma agree_set_spec (lv:set X) (m m': X -> Y) x
        `{Proper _ (respectful _eq _eq) m} `{Proper _ (respectful _eq _eq) m'}
  : x ∈ agree_set lv m m' <-> x ∈ lv /\ m x === m' x.
  Proof.
    intros.
    assert (Proper (_eq ==> eq) (fun x : X => if [m x === m' x] then true else false)). {
      hnf; intros. cbv beta. repeat cases; try reflexivity.
       - exfalso. eapply NOTCOND. rewrite <- H2; eauto. rewrite H1; eauto.
       - exfalso; eapply NOTCOND. rewrite H2; eauto. rewrite H1; eauto. }
    split; intros.
    + pose proof (filter_1 H4). pose proof (filter_2 H4).
      cbv beta in *. cases in H6; easy.
    + eapply filter_3.
      - eassumption.
      - eapply H4.
      - cases; eauto.
  Qed.

  Lemma agree_on_agree_set_eq
        (lv:set X) (D D':X -> Y)
        `{Proper _ (respectful _eq _eq) D} `{Proper _ (respectful _eq _eq) D'}
  : agree_on _eq lv D D' -> agree_set lv D D' [=] lv.
  Proof.
    intros. hnf; intros. split; intros.
    + eapply agree_set_spec in H4; dcr; eassumption.
    + eapply agree_set_spec; try eassumption. split; eauto.
      eapply H3; eauto.
  Qed.


  Lemma agree_set_agree_on  Z `{OrderedType Z}
        (lv:set X) (D D':X -> Y) (E E': X -> Z)
        `{Proper _ (respectful _eq _eq) D} `{Proper _ (respectful _eq _eq) D'}
  : agree_on _eq lv D D' -> agree_on _eq (agree_set lv D D') E E'
    -> agree_on _eq lv E E'.
  Proof.
    intros. hnf; intros.
    eapply H5. eapply agree_set_spec; try assumption. split; eauto.
    eapply H4; eauto.
  Qed.

  Lemma agree_on_agree_set (lv:set X) (D D' D'': X -> Y)
        `{Proper _ (respectful _eq _eq) D}
        `{Proper _ (respectful _eq _eq) D'}
        `{Proper _ (respectful _eq _eq) D''}
  : agree_on _eq lv D D' -> agree_set lv D D'' ⊆ agree_set lv D' D''.
  Proof.
    intros. hnf; intros. rewrite agree_set_spec in *; try assumption.
    intuition. transitivity (D a); eauto. symmetry. eapply H4; eauto.
  Qed.


  Lemma agree_set_incl (lv:set X) (D D': X -> Y)
        `{Proper _ (respectful _eq _eq) D}
        `{Proper _ (respectful _eq _eq) D'}
  : (agree_set lv D D') ⊆ lv.
  Proof.
    intros. hnf; intros. eapply agree_set_spec in H3; firstorder.
  Qed.


  Lemma agree_set_incl_both (lv' lv:set X) (D D':X->Y)
        `{Proper _ (respectful _eq _eq) D}
        `{Proper _ (respectful _eq _eq) D'}
  : lv' ⊆ lv -> agree_set lv' D D' ⊆ agree_set lv D D'.
  Proof.
    intros. hnf; intros. rewrite agree_set_spec in *; firstorder.
  Qed.

End MapAgreeSet.

Arguments agree_set {X} {H} {Y} {H0} lv m m' .
Arguments agree_set_spec {X} {H} {Y} {H0} lv m m' x {H1} {H2}.

Global Instance eq_cset_agree_set_morphism X `{OrderedType X} Y `{OrderedType Y}
  : Proper (SetInterface.Equal ==> (@fpeq X Y _eq H H0) ==> (@fpeq X Y _eq _ _) ==> SetInterface.Equal) (@agree_set X _ Y _ ).
Proof.
  unfold respectful; unfold fpeq.
  hnf;intros; dcr. hnf.
  intros.
  Unset Ltac Debug.
  split; intros.
  + eapply agree_set_spec in H2; eauto. dcr.
    eapply agree_set_spec; eauto. split.
    - rewrite <- H1; eauto.
    - rewrite <- (H4 _). rewrite <- (H3 _); eauto.
  + eapply agree_set_spec in H2; eauto. dcr.
    eapply agree_set_spec; eauto. split.
    - rewrite H1; eauto.
    - rewrite (H4 _). rewrite (H3 _); eauto.
Qed.

Add Parametric Morphism {X} `{OrderedType X} {Y} `{OrderedType Y} : (@lookup_set X _ Y _)
  with signature (@fpeq X Y _eq _ _) ==> SetInterface.Equal ==> SetInterface.Equal
    as eq_cset_lookup_set_morphism.
Proof.
  intros. intro. unfold fpeq in *; dcr.
  split; intros; eapply lookup_set_spec in H1; dcr; eauto.
  + eapply lookup_set_spec; eauto.
    eexists x1. split. rewrite <- H2; eauto. rewrite <- (H3 _); eauto.
  + eapply lookup_set_spec; eauto.
    eexists x1. split. rewrite H2; eauto. rewrite (H3 _); eauto.
Qed.

Add Parametric Morphism {X} `{OrderedType X} {Y} `{OrderedType Y}
  : (@lookup_set  X _ Y _)
  with signature (@fpeq X Y _eq _ _) ==> Subset ==> Subset
    as incl_lookup_set_morphism.
Proof.
  intros. hnf; intros.
  unfold fpeq in *; dcr.
  eapply lookup_set_spec in H3; dcr; eauto; eapply lookup_set_spec; eauto.
  eexists x1. split. rewrite <- H2. eauto. rewrite <- (H4 _); eauto.
Qed.


Lemma agree_set_minus X `{OrderedType X} Y `{OrderedType Y} lv lv' (D D': X -> Y)
      `{Proper _ (_eq ==> _eq) D} `{Proper _ (_eq ==> _eq) D'}
: agree_set lv D D' \ lv' [=] agree_set (lv \ lv') D D'.
Proof.
  intro. split; intros.
  + edestruct (@minus_in_in _ _ _ _ _ H3); eauto.
    rewrite agree_set_spec in H4 |- *; eauto.
    split.
  - eapply in_in_minus; eauto; eapply H4.
  - eapply H4.
    + rewrite agree_set_spec in H3; dcr; eauto.
      edestruct (minus_in_in _ _ _ _ H4); eauto.
      eapply in_in_minus; eauto. eapply agree_set_spec; eauto.
Qed.
