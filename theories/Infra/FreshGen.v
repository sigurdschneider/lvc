Require Import CSet Le Arith.Compare_dec Var.
Require Import Plus Util Map Get Take LengthEq.

Set Implicit Arguments.

Inductive FreshGen (V:Type) `{OrderedType V} (Fi : Type) :=
  {
    fresh :> Fi -> V -> V * Fi;
    fresh_list : Fi -> list V -> list V * Fi;
    domain : Fi -> set V;
    domain_add : Fi -> set V -> Fi;
    empty_domain : Fi
  }.

Arguments FreshGen V {H} Fi.

Inductive FreshGenSpec V `{OrderedType V} Fi (FG:FreshGen V Fi) : Prop :=
  {
    fresh_spec : forall i x, fst (fresh FG i x) ∉ domain FG i;
    fresh_domain_spec : forall i x, {fst (fresh FG i x); (domain FG i)}
                                 ⊆ domain FG (snd (fresh FG i x));
    fresh_list_disj : forall i Z, disj (domain FG i) (of_list (fst (fresh_list FG i Z)));
    fresh_list_domain_spec : forall i Z, of_list (fst (fresh_list FG i Z)) ∪ domain FG i
                                            ⊆ domain FG (snd (fresh_list FG i Z));
    fresh_list_nodup : forall i Z, NoDupA _eq (fst (fresh_list FG i Z));
    fresh_list_len : forall i Z, ❬fst (fresh_list FG i Z)❭ = ❬Z❭;
    domain_add_spec : forall i G, G ∪ domain FG i ⊆ domain FG (domain_add FG i G)
  }.

Create HintDb fresh discriminated.
