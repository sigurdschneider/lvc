(** Disclaimer: This file was taken from the Autosubst library.
    https://www.ps.uni-saarland.de/autosubst/
 *)

Require Import Coq.Program.Tactics Util Get.

Class Size (A : Type) := size : A -> nat.

Ltac gen_Size :=
hnf; match goal with [ |- ?A -> nat] =>
fix size' 1; intros s;
assert(size_inst : Size A);[exact size' | idtac];
destruct s eqn:E;
let term := type of s in
match goal with
    [E : s = ?s' |- _] =>
    let rec map s :=
        (match s with
             ?s1 ?s2 =>
             let size_s1 := map s1 in
             let s2_T := type of s2 in
             let size_s2 := match s2_T with
                         | A => constr:(size' s2)
                         | _ => constr:(size s2)
                       end in
             constr:(size_s1 + size_s2)
           | _ => constr:(O) end) in
    let t' := map s' in
    let t'' := eval simpl plus in t' in
    exact (S t'')
end
end.

Require Import Omega.

Lemma size_rec {A : Type} f (x : A) : forall P : A -> Type, (forall x, (forall y, f y < f x -> P y) -> P x) -> P x.
Proof.
  intros P IS. cut (forall n x, f x <= n -> P x). { eauto. }
  intros n. induction n; intros; apply IS; intros.
  - omega.
  - apply IHn. omega.
Defined.

Ltac autorevert x :=
  try (match goal with
    | [y : ?Y |- ?claim] =>
      try(match x with y => idtac end; fail 1);
        match goal with [z : _ |- _] =>
          match claim with appcontext[z] =>
            first[
                match Y with appcontext[z] => revert y; autorevert x end
              | match y with z => revert y; autorevert x end]
          end
        end
       end).

Tactic Notation "sinduction" ident(H) "using" open_constr(f) :=
let T := type of H in
autorevert H; induction H using (@size_rec _ f);
match goal with [H : T |- _] => destruct H end.

Tactic Notation "sinduction" ident(H) :=
let T := type of H in
autorevert H; induction H using (@size_rec _ size);
match goal with [H : T |- _] => destruct H end; intros.

Ltac sind H :=
let IH := fresh "IH" in
let x := fresh "x" in
induction H as [x IH] using (@size_rec _ size); try rename x into H.

Instance def_size (A : Type) : Size A | 100 := (fun x => O).

Instance size_nat : Size nat := id.

Instance size_prod {A B : Type} (size_A : Size A) (size_B : Size B)
: Size (prod A B).
intros [a b]. eapply (size a + size b).
Defined.



Instance size_list (A : Type) (size_A : Size A) : Size (list A). gen_Size. Defined.

Lemma size_list_get {A : Type} `{Size A} {L : list A} {n} {a}
: get L n a -> size a <= size L.
Proof.
  general induction L; inv H0; repeat(unfold size in *; unfold def_size in *; simpl in *).
  - omega.
  - rewrite IHL; eauto. omega.
Qed.

Lemma size_prod_split {A B : Type} `{Size A} `{Size B} {x:A*B} {n}
: size_prod _ _ x <= n -> size (fst x) <= n /\ size (snd x) <= n.
Proof.
  destruct x; simpl; intros. omega.
Qed.

(** Tactics *)

Ltac sizesimpl :=
     repeat (unfold size in * |- *; unfold def_size in * |- *; simpl in * |- *;
                        try match goal with
                          | [ H: get ?L ?n ?x |- context [size_list _ _ ?L] ]
                            => eapply size_list_get in H
                          | [ H: size_prod _ _ _ <= _ |- _ ]
                            => eapply size_prod_split in H
                            end; clear_trivial_eqs).

Tactic Notation "somega" := sizesimpl; omega.
Hint Extern 2 (size _ < size _) => somega.
Hint Extern 2 (size _ < S (size _)) => somega.

(** Tests *)

Inductive foo := Foo1 | Foo2 (_ : list foo) (_ : nat).

Instance size_foo : Size foo. gen_Size. Set Printing Implicit. Defined.
