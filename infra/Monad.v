Require Import List.

Set Implicit Arguments.

(** * Some support for programming with monads. *)

(** A monad must provide bind and return *)
Class Monad (M:Type->Type) := {
  bind     : forall {A B:Type}, forall (f:M A) (g: A -> M B), M B;
  ret      : forall {A:Type} (a:A), M A
}.

(** notation for all monadic computations *)
Notation "'mdo' X <- A ; B" := (bind A (fun X => B))
 (at level 200, X ident, A at level 100, B at level 200).

(** ** Operations for monads *)
Fixpoint mmap {X Y m} `{Monad m} (f : X -> m Y) (xs : list X) : m (list Y) :=
  match xs with
  | nil => ret nil
  | x :: xr =>
    mdo y  <- f x;
    mdo yr <- mmap f xr;
      ret (y :: yr)
  end.

Fixpoint mfoldr {X Y m} `{Monad m} (f : X -> Y -> m Y) (y : Y) (xs : list X) : m Y :=
  match xs with
  | nil => ret y
  | x :: xr => mdo y' <- mfoldr f y xr; f x y'
  end.

Fixpoint mfoldl {X Y m} `{Monad m} (f : X -> Y -> m Y) (y : Y) (xs : list X) : m Y :=
  match xs with
  | nil => ret y
  | x :: xr => mdo y' <- f x y; mfoldl f y' xr
  end.

Extraction Inline bind ret.