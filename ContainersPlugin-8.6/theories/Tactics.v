(** This file contains some useful tactics for proving instances of
   [OrderedType]. For tactics dealing with ordered types ([order]) and
   sets ([fsetdec]), see respectively OrderedType.v and SetDecide.v.
   For more details about the following tactics, see "docs/GenerateOT.tex".

   The following tactics are useful to prove instances for your own datatypes.
   There is one tactic for each of these 5 properties : reflexivity, symmetry
   and transitivity of the equality relation, transitivity and irreflexivity
   of the strict order relation.

   They work for relations defined inductively ; for example, lets say you have
   the datatype [Inductive t := | t1 : A -> t | t2 : B -> C -> t] where [A],
   [B] and [C] are types that already have instances. There are two main ways
   of defining the equality and order on [t] in a 'canonical' way :
   using inductives
   [[
   Inductive t_eq : t -> t -> Prop :=
   | eq_t1 : forall a a',
     a === a' -> t_eq (t1 a) (t1 a')
   | eq_t2 : forall b b' c c',
     b === b' -> c === c' -> t_eq (t2 b c) (t2 b' c').
   ]]
   [[
   Inductive t_lt : t -> t -> Prop :=
   | lt_t1_t1 : forall a a',
     a <<< a' -> t_lt (t1 a) (t1 a')
   | lt_t1_t2 : forall a b c,
     t_lt (t1 a) (t2 b c)
   | lt_t2_t2_1 : forall b b' c c',
     b <<< b' -> t_lt (t2 b c) (t2 b' c')
   | lt_t2_t2_2 : forall b b' c c',
     b === b' -> c <<< c' -> t_lt (t2 b c) (t2 b' c').
   ]]
   or using functions
   [[
   Definition t_eq (x y : t) : Prop :=
     match x, y with
     | t1 a, t1 a' => a === a'
     | t2 b c, t2 b' c' => b === b' /\ c === c'
     | _, _ => False
     end.
   ]]
   [[
   Definition t_lt (x y : t) : Prop :=
     match x, y with
     | t1 a, t1 a' => a <<< a'
     | t1 _, t2 _ _ => True
     | t2 b c, t2 b' c' => b <<< b' \/ (b === b' /\ c <<< c')
     | _, _ => False
     end.
   ]]
   The tactics are only designed for the first version of these specifications.
   *)

Require Import OrderedType.

Ltac tconstructor t := once (constructor; t).

Tactic Notation "tconstructor" tactic(t) :=
  once (constructor; t).

(** * Tactics for inductives without recursion, nor parameters *)

(** ** Equivalence *)
Ltac inductive_refl := try unfold Reflexive;
  destruct 0; try tconstructor (reflexivity).

Ltac inductive_sym := try unfold Symmetric;
  do 3 intro; destruct 0;
    try tconstructor (symmetry; assumption).

Ltac inductive_trans := try unfold Transitive;
  do 4 intro; inversion_clear 0; intro; inversion_clear 0;
    try tconstructor (eapply transitivity; eassumption).

(** ** StrictOrder *)
Ltac solve_by_trans_modulo :=
  match goal with
    | H1 : ?R ?A ?B, H2 : ?R ?B ?C |- ?R ?A ?C =>
      transitivity B; eassumption
    | H1 : ?R ?A ?B, H2 : ?R' ?B ?C |- ?R ?A ?C =>
      apply eq_gt with B; assumption
    | H1 : ?R ?A ?B, H2 : ?R' ?B ?C |- ?R' ?A ?C =>
      apply eq_lt with B; [symmetry|]; assumption
 end.
Ltac inductive_lexico_trans :=
  do 4 intro; inversion_clear 0; intro; inversion_clear 0;
    try tconstructor (idtac; solve_by_trans_modulo).

Ltac solve_by_irrefl :=
  match goal with
    | H1 : ?R ?A ?A0, H0 : ?R' ?A ?A0 |- _ =>
      apply (lt_not_eq (x:=A) (y:=A0)); assumption
    | H1 : ?R ?A0 ?A, H0 : ?R' ?A ?A0 |- _ =>
      apply (gt_not_eq (x:=A) (y:=A0)); assumption
  end.
Ltac inductive_irrefl :=
  do 3 intro; inversion_clear 0; intro; inversion_clear 0;
    try solve_by_irrefl.

(** ** compare_spec *)
Ltac solve_compare_spec_match :=
  match goal with | |- context f [compare ?X1 ?X2] =>
    destruct (compare_dec X1 X2); solve_compare_spec_aux
  end
with solve_compare_spec_aux :=
  try solve [constructor; tconstructor (solve [auto])];
    solve_compare_spec_match.

Ltac solve_compare_spec :=
  let nx := fresh "x" in let ny := fresh "y" in
    intros nx ny; destruct nx; destruct ny; simpl;
      solve_compare_spec_aux.

(** * Tactics for inductives with recursion, but no parameters *)

(** ** Equivalence *)
Ltac rinductive_refl := try unfold Reflexive;
  induction 0; try tconstructor (try assumption; reflexivity).

Ltac rinductive_sym := try unfold Symmetric;
  do 3 intro; induction 0; try tconstructor (try symmetry; assumption).

Ltac rinductive_trans :=
  let nx := fresh "x" in let ny := fresh "y" in let nz := fresh "z" in
    let nHeq1 := fresh "Heq1" in
      intros nx ny nz nHeq1; revert nz; induction nHeq1;
        do 2 intro; inversion_clear 0;
          try (tconstructor (solve [auto | eapply transitivity; eassumption])).

(** ** StrictOrder *)
Ltac solve_eq_lt  t_eq_sym t_eq_trans :=
  solve [
    eapply transitivity; [symmetry|]; eassumption |
      eapply eq_lt; eassumption |
        eauto using t_eq_sym, t_eq_trans
  ].
Ltac rinductive_eq_lt t_eq_sym t_eq_trans :=
  let nx := fresh "x" in let nx' := fresh "x'" in let ny := fresh "y" in
    let nHlt := fresh "Heq" in
      intros nx nx' ny nHeq; revert ny; induction nHeq;
        do 2 intro; inversion_clear 0;
          try tconstructor (solve_eq_lt t_eq_sym t_eq_trans).

Ltac solve_eq_gt t_eq_trans :=
  solve [
    eapply t_eq_trans; eassumption |
      eapply transitivity; eassumption |
        eapply eq_gt; eassumption |
          auto
  ].
Ltac rinductive_eq_gt t_eq_trans :=
  let nx := fresh "x" in let nx' := fresh "x'" in let ny := fresh "y" in
    let nHeq := fresh "Heq" in
      intros nx nx' ny nHeq; revert ny; induction nHeq;
        do 2 intro; inversion_clear 0;
          try tconstructor (solve_eq_gt t_eq_trans).

Ltac rsolve_by_trans_modulo
  t_eq_sym t_eq_trans t_eq_gt t_eq_lt :=
  match goal with
    | H1 : ?R ?A ?B, H2 : ?R ?B ?C |- ?R ?A ?C =>
      first [apply t_eq_trans with B | transitivity B]; eassumption
    | H1 : ?R ?A ?B, H2 : ?R' ?B ?C |- ?R ?A ?C =>
      first [apply t_eq_gt with B | apply eq_gt with B]; assumption
    | H1 : ?R ?A ?B, H2 : ?R' ?B ?C |- ?R' ?A ?C =>
      first [apply t_eq_lt with B; [apply t_eq_sym |] |
        apply eq_lt with B; [symmetry |]]; assumption
    | IH : forall z, ?R _ _ -> ?R _ _ |- ?R _ _ =>
      apply IH; assumption
 end.
Ltac rinductive_lexico_trans t_eq_sym t_eq_trans t_eq_gt t_eq_lt :=
  let nx := fresh "x" in let ny := fresh "y" in let nz := fresh "z" in
    let nHlt1 := fresh "Hlt1" in
      intros nx ny nz nHlt1; revert nz; induction nHlt1;
        do 2 intro; inversion_clear 0;
          try tconstructor (idtac; rsolve_by_trans_modulo
            t_eq_sym t_eq_trans t_eq_gt t_eq_lt).

Ltac rinductive_irrefl :=
  do 3 intro; induction 0; intro; inversion_clear 0;
    auto; solve_by_irrefl.

(** ** compare_spec *)
Ltac rsolve_compare_spec_match t_eq_sym :=
  match goal with
    | IH : forall z, compare_spec _ _ _ _ (?R ?X1 _) |-
      context f [?R ?X1 ?X2] =>
      destruct (IH X2); rsolve_compare_spec_aux t_eq_sym
    | |- context f [compare ?X1 ?X2] =>
      destruct (compare_dec X1 X2); rsolve_compare_spec_aux t_eq_sym
  end
with rsolve_compare_spec_aux t_eq_sym :=
  try solve [constructor; tconstructor (solve [auto using t_eq_sym])];
    rsolve_compare_spec_match t_eq_sym.

Ltac rsolve_compare_spec t_eq_sym :=
  let nx := fresh "x" in let ny := fresh "y" in
    intros nx; induction nx; intros ny; destruct ny; simpl in *;
      rsolve_compare_spec_aux t_eq_sym.

(** * Tactics for mutual inductives, but no parameters *)

(** ** Equivalence *)
Ltac minductive_refl :=
  induction 0; constructor; auto; reflexivity.
Ltac minductive_sym :=
  do 3 intro; induction 0; tconstructor (try symmetry); auto.
Ltac minductive_trans :=
  let nx := fresh "x" in let ny := fresh "y" in
    let nz := fresh "z" in let nHeq1 := fresh "Heq1" in
      intros nx ny nz nHeq1; revert nz;
        induction nHeq1;
          do 2 intro; inversion_clear 0; constructor;
            solve [eauto | eapply transitivity; eassumption].

(** ** StrictOrder *)
Ltac minductive_irrefl :=
  do 3 intro; induction 0; intro;
    inversion_clear 0; eauto; solve_by_irrefl.
Ltac msolve_eq_lt s :=
  solve [
    eapply transitivity; [symmetry|]; eassumption |
      eapply eq_lt; eassumption |
        s
  ].
Ltac msolve_eq_gt s :=
  solve [
    s |
      eapply transitivity; eassumption |
        eapply eq_gt; eassumption |
          auto
  ].
Ltac minductive_eq_lt_gt s :=
  let nx := fresh "x" in let nx' := fresh "x'" in
    let ny := fresh "y" in let nHlt := fresh "Heq" in
      intros nx nx' ny nHeq; revert ny; induction nHeq;
        do 2 intro; inversion_clear 0;
          tconstructor s.
Ltac msolve_by_trans_modulo strans seqgt seqlt :=
  match goal with
  | H1:?R ?A ?B, H2:?R ?B ?C
    |- ?R ?A ?C =>
        (first [ strans B | transitivity B ]); eassumption
  | H1:?R ?A ?B, H2:?R' ?B ?C
    |- ?R ?A ?C =>
        (first [ seqgt B | apply eq_gt with B ]); assumption
  | H1:?R ?A ?B, H2:?R' ?B ?C
    |- ?R' ?A ?C =>
        (first
          [ seqlt B | apply eq_lt with B; [ symmetry  in |- * | idtac ] ]);
        assumption
    | IH:forall x y z, ?R _ _ -> ?R _ _ -> ?R _ _ |- ?R _ _ =>
      eapply IH; eassumption
  end.
Ltac minductive_lexico_trans sstrans seqgt seqlt :=
  let nx := fresh "x" in let ny := fresh "y" in
    let nz := fresh "z" in let nHlt1 := fresh "Hlt1" in
      intros nx ny nz nHlt1; revert nz; induction nHlt1;
        do 2 intro; inversion_clear 0;
          tconstructor (msolve_by_trans_modulo sstrans seqgt seqlt).

(** ** compare_spec *)
Ltac msolve_compare_spec_match s :=
  match goal with
    | IH : forall z z', compare_spec _ _ _ _ (?R _ _) |-
      context f [?R ?X1 ?X2] =>
      destruct (IH X1 X2); msolve_compare_spec_aux s
    | |- context f [compare ?X1 ?X2] =>
      destruct (compare_dec X1 X2); msolve_compare_spec_aux s
  end
with msolve_compare_spec_aux s :=
  try solve [constructor; tconstructor (solve [s])];
    msolve_compare_spec_match s.
Ltac msolve_compare_spec s :=
  let nx := fresh "x" in let ny := fresh "y" in
    intros nx; induction nx; intros ny; destruct ny; simpl in *;
      msolve_compare_spec_aux s.
(* ex : msolve_compare_spec (auto using term_eq_sym, terms_eq_sym). *)
