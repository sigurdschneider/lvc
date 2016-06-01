Require Import AllInRel List Map Env AutoIndTac MoreList IL.

Set Implicit Arguments.

Class BlockType X := {
                      block_n : X -> nat;
                      block_Z : X -> list var
                    }.

Instance block_type_I : BlockType (I.block) :=
  {
    block_n := I.block_n;
    block_Z := I.block_Z
  }.

Instance block_type_F : BlockType (F.block) :=
  {
    block_n := F.block_n;
    block_Z := F.block_Z
  }.


Lemma mkBlocks_I_less
  : forall (F : list (params * stmt)) (n k : nat) (b : I.block),
    get (mapi_impl I.mkBlock k F) n b -> I.block_n b <= k + length F - 1.
Proof.
  intros; inv_get. simpl. eapply get_range in H. omega.
Qed.

Lemma mkBlock_I_i F
  : forall i b, get (mapi I.mkBlock F) i b -> i = I.block_n b.
Proof.
  intros; inv_get; eauto.
Qed.


Lemma mkBlocks_F_less
  : forall E (F : list (params * stmt)) (n k : nat) (b : F.block),
    get (mapi_impl (F.mkBlock E) k F) n b -> F.block_n b <= k + length F - 1.
Proof.
  intros; inv_get. simpl. eapply get_range in H. omega.
Qed.

Lemma mkBlock_F_i E F
  : forall i b, get (mapi (F.mkBlock E) F) i b -> i = F.block_n b.
Proof.
  intros; inv_get; eauto.
Qed.
