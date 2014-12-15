Require Import List NPeano Decidable.
Require Import IL Val bitvec TUtil.

Set Implicit Arguments.

(* An smt environment must be defined on every variable that occurs in the formula.
Hence it is safe to not use options here *)

(** Define SMT expressions on bitvectors. **)
Inductive sexp :=
(** a + b **)
|splus: sexp -> sexp -> sexp
(** a - b **)
|ssub: sexp -> sexp -> sexp
(** a * b **)
|smult: sexp -> sexp -> sexp
(** a / b **)
|sdiv: sexp -> sexp -> sexp
(** a == b **)
|seq: sexp -> sexp -> sexp
(** ! a **)
|sneg: sexp->sexp
(** constants **)
|sconst: bitvec -> sexp
(** variables **)
|svar: var -> sexp.

(** Lemmas **)

Lemma zext_nil_eq_O:
forall k, zext k nil = zext k (O::nil).

Proof.
induction k.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Lemma not_zero_implies_uneq:
forall a b,
bvZero a = false
->b = zext k (O::nil)
->  ~ val2bool(bvEq a b).

Proof.
intros. hnf.  intros. hnf in H1.  unfold bvZero in H. unfold val2bool in H1.
rewrite H0 in H1. unfold zero in H. rewrite H in H1; eauto.
(*general induction a.
-  destruct a.
   + specialize (IHa (tl (zext k (O::nil))) (k-1)).   simpl in H. specialize (IHa H).
     hnf.  intros. eapply IHa.
     * destruct k; eauto.
       simpl. rewrite zext_nil_eq_O.   erewrite minus_n_0. reflexivity.
     * destruct k; eauto. simpl in H0.  exfalso. assumption.
   +  hnf. intros. simpl in H0. destruct k;  assumption. *)
Qed.

Lemma zero_implies_eq:
forall a b,
bvZero a = true
-> b = zext k (O::nil)
-> val2bool(bvEq a b).

Proof.
intros.  rewrite H0. unfold bvZero in H. unfold zero in H. unfold val2bool.
rewrite H; eauto. econstructor.
Qed.

Lemma exp_eval_if_list_eval:
  forall el E vl,
    omap (exp_eval E) el = Some vl
    -> forall e, List.In e el -> exists v, exp_eval E e = Some v.

Proof.
intros.
general induction el.
- simpl in H. exists (O::nil). intros. inversion H0.
- unfold omap in H. monad_inv H. decide (e=a).
  + exists x. intros. rewrite e0. assumption.
   + specialize (IHel E x0 EQ1). specialize (IHel e).
     simpl in H0.  destruct H0.
     * exfalso. apply n. rewrite H; reflexivity.
     * destruct (IHel H).  exists x1.
       rewrite H0. reflexivity.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
