Require Import CSet Le.

Require Import Plus Util Map.
Require Import Val Var Env EnvTy IL.

Set Implicit Arguments.

Inductive parameters_match : list nat -> stmt -> Prop :=
  | pmExp L x e s
    : parameters_match L s -> parameters_match L (stmtExp x e s)
  | pmIf L x s t
    :  parameters_match L s
    -> parameters_match L t
    -> parameters_match L (stmtIf x s t)
  | pmRet L x 
    : parameters_match L (stmtReturn x)
  | pmGoto L f Y n
    : get L (counted f) n
    -> n = length Y
    -> parameters_match L (stmtGoto f Y)
  | pmLet L s t Z
    : parameters_match (length Z::L) s 
    -> parameters_match (length Z::L) t 
    -> parameters_match L (stmtLet Z s t).

Class BlockType X := {
  block_s : X -> stmt;
  block_Z : X -> list var;
(*  rename_block : env var -> X -> X; *)
  block_ctor : forall s Z, { b : X | block_s b = s /\ block_Z b = Z }
(*  rename_block_s : forall ϱ b, block_s (rename_block ϱ b) = rename ϱ (block_s b);
  rename_block_Z : forall ϱ b, block_Z (rename_block ϱ b) = lookup_list ϱ (block_Z b) *)
}.

Definition rename_block_I (ϱ:env var) b :=
  match b with
    | I.blockI Z s => I.blockI (lookup_list ϱ Z) (rename ϱ s)
  end.

Definition rename_block_F (ϱ:env var) b :=
  match b with
    | F.blockI E Z s => F.blockI (ϱ ∘ E) (lookup_list ϱ Z) (rename ϱ s)
  end.

Global Instance block_type_I : BlockType (I.block) := {
  block_s := I.block_s;
  block_Z := I.block_Z }.
(*  rename_block := rename_block_I
}. *)
+ intros. eexists (I.blockI Z s); eauto. (*
+ intros; destruct b; eauto.
+ intros; destruct b; eauto. *)
Defined.

Global Instance block_type_F : BlockType (F.block) := {
  block_s := F.block_s;
  block_Z := F.block_Z }.
(*  rename_block := rename_block_F
}. *) 
+ intros. eexists (F.blockI id Z s); eauto. (*
+ intros; destruct b; eauto.
+ intros; destruct b; eauto. *)
Defined.
(*
Definition rename_labenv {B} `{BlockType B} (ϱ:env var) (L:list B) : list B
  := List.map (rename_block ϱ) L.
*)
Definition labenvZ {B} `{BlockType B} (L:list B) : list nat
  := List.map (block_Z ∘ (@length _)) L.
(*
Lemma labenvZ_rename_labenv {B} `{BlockType B} ϱ b L
    : labenvZ (rename_labenv ϱ (b::L)) 
    = lookup_list ϱ (block_Z b)::labenvZ (rename_labenv ϱ L).
Proof.
  simpl. f_equal. rewrite rename_block_Z. reflexivity.
Qed.
*)
Definition labenv_parameters_match {B} `{BlockType B} (L:list B) : Prop
  := forall n blk, get L n blk -> parameters_match (labenvZ (drop n L)) (block_s blk).

Definition params_match {B} `{BlockType B} (L:list B) s := 
  parameters_match (labenvZ L) s /\ labenv_parameters_match L.

Lemma params_match_exp {B} `{BlockType B} (L:list B) x e s
  : params_match L (stmtExp x e s)
  -> params_match L s.
Proof.
  intros. hnf in *. decompose records. inv H1. firstorder.
Qed.

Lemma params_match_if {B} `{BlockType B} (L:list B) x s t
  : params_match L (stmtIf x s t)
  -> params_match L s /\ params_match L t.
Proof.
  intros. hnf in *. decompose records. inv H1. firstorder.
Qed.

Lemma params_match_goto {B} `{BlockType B} (L:list B) f Y blk
  : params_match L (stmtGoto f Y)
  -> get L (counted f) blk
  -> params_match (drop (labN f) L) (block_s blk)
  /\ length (block_Z blk) = length Y.
Proof.
  intros. hnf in *. decompose records. inv H2. split.
  hnf. split. specialize (H3 _ _ H1). eapply H3.
  hnf; intros. rewrite drop_drop. eapply H3.
  rewrite plus_comm. eauto using get_drop.
  rewrite (map_get _ H1 H6); eauto.
Qed.

Lemma params_match_let_F L s Z t
  : params_match L (stmtLet s Z t)
  -> forall E, params_match (F.blockI E s Z :: L)%list t.
Proof.
  intros. hnf in *. decompose records. inv H0. simpl. split; eauto.
  hnf; intros. destruct n; inv H; simpl in *; eauto.
Qed.

Lemma params_match_let_I L s Z t
  : params_match L (stmtLet s Z t)
  -> params_match (I.blockI s Z :: L)%list t.
Proof.
  intros. hnf in *. decompose records. inv H0. simpl. split; eauto.
  hnf; intros. destruct n; inv H; simpl in *; eauto.
Qed.

Lemma params_match_get {B} `{BlockType B} (L:list B) l Y
 : params_match L (stmtGoto l Y)
   -> exists blk, get L (counted l) blk.
Proof.
  intros. inv H0. inv H1. unfold labenvZ in H6.
  eapply map_get_4 in H6. destruct H6; dcr. eauto.
Qed.

Ltac params_match_tac :=
  match goal with
    | [ H : params_match _ (stmtExp _ _ _) |- _ ] => pose proof (params_match_exp H)
    | [ H : params_match _ (stmtIf _ _ _) |- _ ] => destruct (params_match_if H)
    | [ H : params_match ?L (stmtGoto ?f _), H' : get ?L (counted ?f) _ |- _ ] 
      => destruct (params_match_goto H H')
    | [ H : params_match ?L (stmtGoto ?f _), H' : get ?L (labN ?f) _ |- _ ] 
      => destruct (params_match_goto H H')
    | [ H : params_match ?L (stmtGoto ?f _) |- _ ] 
      => destruct (params_match_get H); params_match_tac
    | [ H : params_match _ (stmtLet _ _ _) |- _ ] => pose proof (params_match_let_F H)
    | [ H : params_match _ (stmtLet _ _ _) |- _ ] => pose proof (params_match_let_I H)
  end.

Lemma params_match_F L E s L' E' s'
  : params_match L s 
  -> F.step (L,E,s) (L',E',s')
  -> params_match L' s'.
Proof.
  intros. inv H0; params_match_tac; eauto.
Qed.

Lemma params_match_I L E s L' E' s'
  : params_match L s 
  -> I.step (L,E,s) (L',E',s')
  -> params_match L' s'.
Proof.
  intros. inv H0; params_match_tac; eauto.
Qed.

Inductive labl X : list X  -> stmt -> Type :=
  | lablExp y e s (L:list X)
    : labl L s -> labl L (stmtExp y e s)
  | lablIf L y s t
    :  labl L s
    -> labl L t
    -> labl L (stmtIf y s t)
  | lablRet L y
    :  labl L (stmtReturn y) 
  | lablGoto L f Y y
    :  get L (counted f) y
    -> labl L (stmtGoto f Y)
  | lablLet L s t Z x
    :  labl (x::L) s
    -> labl (x::L) t
    -> labl L (stmtLet Z s t).

Lemma labl_other X (L L':list X) s
  : length L = length L' -> labl L s -> labl L' s.
Proof.
  intros A B; general induction B; eauto using labl.
  eapply get_range in g. rewrite A in g. eapply get_in_range in g.
  destruct g. econstructor; eauto.
  econstructor. instantiate (1:=x). eapply IHB1; simpl; eauto.
  eapply IHB2; simpl; eauto.
Qed.

(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
