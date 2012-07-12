Require Import List.
Require Export Monad.

(** Cast option in the framework of Monad. The code in this file is taken from CompCert. *)

Set Implicit Arguments.

Definition bind (A B : Type) (f : option A) (g : A -> option B) : option B :=
  match f with
    | Some a => g a
    | None   => None
  end.

Extraction Inline bind.

Global Instance inst_monad_option : Monad option := Build_Monad _ bind (fun A (x:A) => Some x).

Lemma bind_inversion (A B : Type) (f : option A) (g : A -> option B) (y : B) :
  bind f g = Some y -> exists x, f = Some x /\ g x = Some y.
Proof.
  destruct f. firstorder. discriminate.
Qed.

Lemma bind_inversion' (A B : Type) (f : option A) (g : A -> option B) (y : B) :
  bind f g = Some y -> { x : A | f = Some x /\ g x = Some y }.
Proof.
  destruct f. firstorder. discriminate.
Qed.


Lemma mmap_inversion:
  forall (A B : Type) (f : A -> option B) (l : list A) (l' : list B),
  mmap f l = Some l' ->
  Forall2 (fun x y => f x = Some y) l l'.
Proof.
  induction l; simpl; intros.
  inversion_clear H. constructor.
  destruct (bind_inversion _ _ H) as [hd' [P Q]].
  destruct (bind_inversion _ _ Q) as [tl' [R S]].
  inversion_clear S.
  constructor. auto. auto. 
Qed.

(** * Reasoning over monadic computations *)

(** The [monadInv H] tactic below simplifies hypotheses of the form
<<
        H: (do x <- a; b) = OK res
>>
    By definition of the bind operation, both computations [a] and
    [b] must succeed for their composition to succeed.  The tactic
    therefore generates the following hypotheses:

         x: ...
        H1: a = OK x
        H2: b x = OK res
*)

Ltac monad_inv1 H :=
  match type of H with
  | (Some _ = Some _) =>
      inversion H; clear H; try subst
  | (None   = Some _) =>
      discriminate
  | (bind ?F ?G = Some ?X) =>
      let x   := fresh "x"  in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
        destruct (bind_inversion' F G H) as [x [EQ1 EQ2]];
        clear H;
        try (monad_inv1 EQ2))))
  | (mmap ?F ?L = Some ?M) =>
      generalize (@mmap_inversion _ _ F L M H); intro
  end.

Ltac monad_inv H :=
  match type of H with
  | (Some _ = Some _) => monad_inv1 H
  | (None   = Some _) => monad_inv1 H
  | (bind ?F ?G = Some ?X) => monad_inv1 H
  | (@eq _ (@Monad.bind _ _ _ _ _ ?G) (?X)) => 
    let X := fresh in remember G as X; simpl in H; subst X; monad_inv1 H
  end.
