Require Import List.

(** Cast option in the framework of Monad. The code in this file is taken from CompCert. *)

Notation "⎣ x ⎦" := (Some x) (at level 0, x at level 200).
Notation "⎣⎦" := (None) (at level 0, x at level 200).

Set Implicit Arguments.

Definition bind (A B : Type) (f : option A) (g : A -> option B) : option B :=
  match f with
    | Some a => g a
    | None   => None
  end.

Extraction Inline bind.

Notation "'mdo' X <- A ; B" := (bind A (fun X => B))
 (at level 200, X ident, A at level 100, B at level 200).

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


Section ParametricOptionMapIndex.
  Variables X Y : Type.
  Hypothesis f : nat -> X -> option Y : Type.

  Fixpoint omapi_impl (n:nat) (L:list X) : option (list Y) :=
    match L with
      | x::L => 
        mdo v <- f n x; 
          mdo vl <- omapi_impl (S n) L;
          Some (v::vl)
      | _ => Some nil
    end.
  
  Definition omapi := omapi_impl 0.

End ParametricOptionMapIndex.

Arguments omapi [X] [Y] f L.


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


Lemma bind_inversion'' {A B : Type} (f : option A) (g : A -> option B) :
  bind f g = None -> f = None \/ exists x, f = Some x /\ g x = None.
Proof.
  destruct f; firstorder. 
Qed.

Ltac monad_simpl :=
  match goal with
    | [ H: ?F = _ |- appcontext [bind ?F ?G = _] ] => rewrite H; simpl
  end.

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
  | (bind ?F ?G = None) =>
    let x   := fresh "x"  in 
    let EQ1 := fresh "EQ" in 
    let EQ2 := fresh "EQ" in 
    destruct (bind_inversion'' F G H) as [|[x [EQ1 EQ2]]];
      clear H;
      try (monad_inv1 EQ2)
  end.

Ltac monad_inv H :=
  match type of H with
  | (Some _ = Some _) => monad_inv1 H
  | (None   = Some _) => monad_inv1 H
  | (Some _ = None) => monad_inv1 H
  | (bind ?F ?G = Some ?X) => monad_inv1 H
  | (bind ?F ?G = None) => monad_inv1 H
  | (@eq _ (@bind _ _ _ _ _ ?G) (?X)) => 
    let X := fresh in remember G as X; simpl in H; subst X; monad_inv1 H
  end.

(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
