Require Import Util MoreList Get Option OptionMap Filter.

Set Implicit Arguments.

Fixpoint replace_if X (p:X -> bool) (L:list X) (L':list X) :=
  match L with
  | x::L => if p x then
              match L' with
              | y::L' => y::replace_if p L L'
              | _ => nil
              end
            else
              x::replace_if p L L'
  | _ => nil
  end.

Lemma replace_if_get_inv X (p:X -> bool) L L' n x
  : get (replace_if p L L') n x
    -> exists l , get L n l /\
            ((p l /\ exists l' n', get L' n' l' /\ x = l')
              \/ (~ p l /\ x = l)).
Proof.
  intros; general induction L; destruct L'; simpl in *; isabsurd.
  - cases in H; isabsurd. inv H.
    + exists x; split; eauto using get.
      right; split; eauto. rewrite <- Heq. eauto.
    + edestruct IHL; eauto; dcr.
      eexists; split; eauto using get.
  - cases in H; isabsurd.
    + inv H.
      * eexists; split; eauto using get.
        left. rewrite <- Heq; eauto using get.
      * edestruct IHL; eauto using get; dcr.
        eexists; split; eauto using get.
        destruct H2; dcr; isabsurd. left; eauto 20 using get.
        right; eauto using get.
    + inv H.
      * eexists; split; eauto using get.
        right. rewrite <- Heq; eauto using get.
      * edestruct IHL; eauto; dcr.
        eexists; split; eauto using get.
Qed.
