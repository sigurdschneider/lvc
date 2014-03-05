Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map Status.
Require Import Val Var Env EnvTy IL Liveness Fresh Sim MoreList.

Set Implicit Arguments.

Section ParametricDualFold.
  Variables A X Y : Type.
  Hypothesis f : A -> X -> Y -> status A : Type.

  Fixpoint dfold (a:A) (L:list X) (L':list Y) : status A :=
    match L, L' with
      | x::L, y::L' => sdo a' <- f a x y;
                      dfold a' L L'
      | nil, nil => Success a
      | _, _ => Error "dfold: argument list size mismatch"
    end.
End ParametricDualFold.

Arguments dfold [A] [X] [Y] f a L L'.

(*
Variable oracle : var -> live -> env var -> option var.

Hypothesis oracle_sound' 
  : forall lv ra x xr, oracle x lv ra = Some xr -> ~xr ∈ lookup_set ra lv.
*)

Fixpoint oracle_list (L:list var) (lv:live) (ϱ:var -> var)
  : list var :=
  match L with
    | nil => nil
    | x::L => 
      let xr := least_fresh (lookup_set ϱ (lv\{{x}})) in
        let xl := oracle_list L ({{x}} ∪ lv) (ϱ[x<-xr]) in
          xr::xl
  end.
(*
-Lemma oracle_list_unique L lv ra L'
-  :  oracle_list L lv ra = Some L'
-  -> forall (a:var), a ∈ (lv\of_list L) -> Util.fresh (ra a) L'.
-Proof.
-  general induction L; isabsurd; simpl in *.
-  monad_inv H.
-  specialize (IHL _ _ _ EQ1); eauto. 
-  intro. simpl in H.  
-
-  pose proof (oracle_sound' EQ).
-  destruct H. subst. eapply H1. eapply lookup_set_spec.
-  intuition. 
-  eexists a0. cset_tac; intuition. 
-(*  eapply (IHL a0). eapply minus_in_in in H0. destruct H0.
-  eapply in_in_minus.
-  cset_tac. firstorder. intro. eapply H2. cset_tac; eauto.
-  assert (a0 <> a). intro; subst. eapply minus_in_in in H0.
-  destruct H0. eapply H2. cset_tac; firstorder.
-  simplify lookup. eauto. *)
-Qed.
-
-Lemma oracle_list_inj Z (bv:live) (ra:env var) YL
-  :  unique Z
-  -> oracle_list Z (bv\fromList Z) ra = Some YL
-  -> inj_mapping (lookup_set ra (bv\fromList Z)) Z YL.
-Proof.
-  general induction Z; simpl in *; eauto using inj_mapping.
-  monad_inv H. destruct X.  
-  erewrite set_fact_1 in EQ1; eauto using inst_eq_dec_var, fresh_fromList.
-  pose proof (IHZ _ _ _ u EQ1); eauto.
-  econstructor; eauto. 
-  eapply inj_mapping_incl; eauto.
-  erewrite lookup_set_agree. eapply lookup_set_incl.
-  hnf; cset_tac; firstorder.
-  apply agree_on_sym. rewrite union_comm, <- minus_union. eapply agree_on_update_dead.
-  cset_tac; firstorder. eapply agree_on_refl.
-  pose proof (oracle_list_unique _ _ _ EQ1 a).
-  simplify lookup. eapply X0.
-  cset_tac. left; left; firstorder.
-  eapply f. eapply in_fromList. eauto. 
-  eapply f. eapply in_fromList. eauto.
-  rewrite set_fact_2 in EQ.
-  eauto using oracle_sound'.
-Qed.
*)

Fixpoint linear_scan (st:stmt) (an: ann (live)) (ϱ:var -> var)
  : status (var -> var) :=
 match st, an with
    | stmtExp x e s, annExp lv ans =>
      let xv := least_fresh (lookup_set ϱ (getAnn ans\{{x}})) in
        linear_scan s ans (ϱ[x<- xv])
    | stmtIf _ s t, annIf lv ans ant =>
      sdo ϱ' <- linear_scan s ans ϱ;
        linear_scan t ant ϱ'
    | stmtGoto _ _, annGoto _ => Success ϱ
    | stmtReturn _, annReturn _ => Success ϱ
    | stmtLet Z s t, annLet _ ans ant =>
      let Z' := oracle_list Z (getAnn ans\of_list Z) ϱ in
      sdo ϱ' <- linear_scan s ans (ϱ[Z <-- Z']);
        linear_scan t ant ϱ'
    | _, _ => Error "linear_scan: Annotation mismatch"
  end.

(*
Lemma ralloc_ra_correct LT ET rt s Lv lv (alv:ann s lv) (LS:live_sound Lv alv) ra 
  (rk:injective_on lv ra)
  (sd:FunTS.stmtOfType LT ET s rt)
  alr (rallocOK:ralloc_ra LS ra = Some alr)
  : ra_sound alv alr.
Proof.
  intros.
  general induction LS; simpl in *; monad_inv rallocOK; inv sd;
    eauto 10 using ra_sound, injective_on_incl.
  econstructor; eauto using oracle_sound'. 
  eapply IHLS; eauto.
  destruct_prop (x ∈ bv). 
  rewrite (add_inane _ _ i0). 
  eauto using injective_on_fresh, injective_on_incl, oracle_sound'.
  rewrite (minus_inane _ _ n).
  eauto using injective_on_dead, injective_on_incl.
  econstructor; eauto.
  eapply IHLS1; eauto. 
  eapply injective_on_incl. eapply incl_union_minus.
  eapply injective_on_mapping. eauto using injective_on_incl.
  eapply oracle_list_inj; eauto.
  eapply IHLS2; eauto using injective_on_incl.
  eauto using oracle_list_inj.
Qed.
*)

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lyn")) ***
*** End: ***
*)

