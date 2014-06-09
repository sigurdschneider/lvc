Require Export Containers.OrderedType Setoid Coq.Classes.Morphisms Computable.
Require Import Containers.OrderedTypeEx DecSolve MoreList.

Class PartialOrder (Dom:Type) := {
  poLe : Dom -> Dom -> Prop;
  poLe_dec :> forall d d', Computable (poLe d d');
  poEq : Dom -> Dom -> Prop;
  poEq_dec :> forall d d', Computable (poEq d d')
}.


Instance PartialOrder_pair_instance X `{PartialOrder X} Y `{PartialOrder Y}
: PartialOrder (X * Y) := {
  poLe x y := poLe (fst x) (fst y) /\ poLe (snd x) (snd y);
  poLe_dec := _;
  poEq x y := poEq (fst x) (fst y) /\ poEq (snd x) (snd y);
  poEq_dec := _
}.
- intros.
  decide (poLe (fst d) (fst d')); decide (poLe (snd d) (snd d')); try dec_solve.
- intros.
  decide (poEq (fst d) (fst d')); decide (poEq (snd d) (snd d')); try dec_solve.
Defined.

Instance PartialOrder_list_instance X `{PartialOrder X}
: PartialOrder (list X) := {
  poLe := list_eq poLe;
  poLe_dec := _;
  poEq := list_eq poEq;
  poEq_dec := _
}.


(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
