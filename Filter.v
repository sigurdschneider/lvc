Require Import Util List.

Notation "B[ x ]" := (if [ x ] then true else false).

Fixpoint filter_by {A B} (f:A -> bool) (L:list A) (L':list B) : list B :=
  match L, L' with
    | x :: L, y::L' => if f x then y :: filter_by f L L' else filter_by f L L' 
    | _, _ => nil
  end.

Arguments filter_by [A B] f L L'.

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
