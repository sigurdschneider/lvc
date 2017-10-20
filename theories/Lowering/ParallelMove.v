Require Import CSet Le.

Require Import Plus Util AllInRel InRel Map MapUpdate MapDefined.
Require Import Val Var Envs IL NoParams Annotation SimI Fresh.
Require Import Liveness.Liveness Status InfiniteSubset InfinitePartition AppExpFree.
Require compcert.lib.Parmov.

Set Implicit Arguments.
Unset Printing Records.

(** * Parallel Moves

   This code is based on the ril-cv-12 repo and the validator
   part its initial version was developed by Tobias Tebbi.
*)

Definition moves_source_set (p:Parmov.moves var) : set var
  := fold_right (fun p s => s \ singleton (snd p) ∪ singleton (fst p)) ∅ p.

Definition moves_dest_set (p:Parmov.moves var) : set var
  := of_list (snd ⊝ p).

Lemma moves_source_set_app mv1 mv2
  : moves_source_set (mv1 ++ mv2) [=]
                     moves_source_set mv1 ∪ moves_source_set mv2 \ moves_dest_set mv1.
Proof.
  unfold moves_dest_set.
  general induction mv1; simpl.
  - cset_tac.
  - rewrite IHmv1. clear. cset_tac.
Qed.

Lemma moves_source_set_incl p
  : moves_source_set p ⊆ of_list (fst ⊝ p).
Proof.
  general induction p; simpl.
  - eauto with cset.
  - rewrite IHp; clear. cset_tac.
Qed.

Lemma of_list_rev X `{OrderedType X} L
  : of_list (rev L) [=] of_list L.
Proof.
  general induction L; simpl; eauto.
  rewrite of_list_app; simpl; rewrite IHL.
  cset_tac.
Qed.

Instance eqdec_pospos
  :EqDec (positive * positive) eq.
hnf; intros.
decide (x === y). left. invc e. rewrite H, H0. reflexivity.
right; intro. invc H. eauto.
Defined.

Instance eqdec_pos
  :EqDec (positive) eq.
hnf; intros.
decide (x === y); eauto.
Defined.

Lemma fst_parmove x pm
  : of_list (fst ⊝ Parmov.parmove positive var_dec (fun _ : positive => x) pm) ⊆ {x; of_list (fst ⊝ pm)}.
Proof.
  hnf; intros.
  eapply of_list_get_first in H; dcr. invc H1.
  eapply get_in in H0; eauto.
  eapply Parmov.parmove_srcs_initial_reg_or_temp in H0.
  destruct H0. eapply in_get in H; dcr.
  unfold Parmov.srcs in p. eapply get_in_of_list in p. cset_tac.
  eapply eqdec_pos.
  destruct H; subst. cset_tac.
  eapply eqdec_pos.
Qed.

Lemma snd_parmove x pm
  : of_list (snd ⊝ Parmov.parmove positive var_dec (fun _ : positive => x) pm) ⊆ {x; of_list (snd ⊝ pm)}.
Proof.
  hnf; intros.
  eapply of_list_get_first in H; dcr. invc H1.
  eapply get_in in H0; eauto.
  eapply Parmov.parmove_dests_initial_reg_or_temp in H0.
  destruct H0. eapply in_get in H; dcr.
  unfold Parmov.dests in p. eapply get_in_of_list in p. cset_tac.
  eapply eqdec_pos.
  destruct H; subst. cset_tac.
  eapply eqdec_pos.
Qed.

Lemma combine_get A B (Z:list A) (Y:list B) n x y
  : get Z n x -> get Y n y -> get (combine Z Y) n (x,y).
Proof.
  intros GET1 GET2.
  general induction GET1; try inv GET2; clear_trivial_eqs; simpl;
    eauto using get.
Qed.

Lemma move_no_temp_notin m pmtmp
  : pmtmp ∉ of_list (fst ⊝ m) ∪ of_list (snd ⊝ m)
    <-> Parmov.move_no_temp positive (fun _ : positive => pmtmp) m.
Proof.
  split; hnf; intros; hnf; intros.
  - split; hnf; intros.
    + eapply in_get in H0 as [? ?]; eauto.
      hnf; intros; subst.
      cset_tac'. eapply H0.
      eapply get_in_of_list.
      eapply map_get_eq; eauto. eauto with typeclass_instances.
    + eapply in_get in H0 as [? ?]; eauto.
      hnf; intros; subst.
      cset_tac'. eapply H1.
      eapply get_in_of_list.
      eapply map_get_eq; eauto. eauto with typeclass_instances.
  - cset_tac'.
    + edestruct of_list_get_first; eauto; dcr. invc H2.
      inv_get.
      exploit (H (fst x1) (snd x1)).
      eapply get_in; eauto using combine_get; eauto.
      * eauto with typeclass_instances.
      * rewrite <- pair_eta; eauto.
      * dcr. eapply H2; eauto. eapply 1%positive.
    + edestruct of_list_get_first; eauto; dcr. invc H2.
      inv_get.
      exploit (H (fst x1) (snd x1)).
      eapply get_in; eauto using combine_get; eauto.
      * eauto with typeclass_instances.
      * rewrite <- pair_eta; eauto.
      * dcr. eapply H4; eauto. eapply 1%positive.
Qed.

Section ParmovSourceSet.
  Import Parmov.

  Definition st_source_set (st:state var) :=
    match st with
    | State mv1 mv2 mvs => of_list (fst ⊝ (mv1 ++ mv2)) \ moves_dest_set mvs ∪ moves_source_set (rev mvs)
    end.

  Tactic Notation "stsmpl" :=
    repeat (rewrite List.map_app || rewrite of_list_app
            || simpl || rewrite moves_source_set_app || unfold moves_dest_set || rewrite map_rev
            || rewrite of_list_rev).

  Lemma dtransition_source_set t st st'
    : dtransition var t st st' ->
      st_source_set st' ⊆ st_source_set st.
  Proof.
    intros TR.
    general induction TR; simpl in *; eauto; stsmpl.
    - cset_tac.
    - cset_tac.
    - cset_tac.
    - cset_tac.
    - cset_tac.
    - cset_tac.
  Qed.

  Lemma dtransitions_source_set t st st'
    : dtransitions var t st st' ->
      st_source_set st' ⊆ st_source_set st.
  Proof.
    intros TR.
    general induction TR; simpl in *; eauto using dtransition_source_set.
    - etransitivity; eauto.
  Qed.

  Lemma parmove_src_set t mu
    : moves_source_set (parmove var var_dec t mu) ⊆ of_list (fst ⊝ mu).
  Proof.
    pose proof (parmove_aux_transitions _ var_dec t (State _ mu nil nil)).
    eapply dtransitions_source_set in H.
    simpl in *. revert H; stsmpl.
    unfold parmove. cset_tac.
  Qed.

End ParmovSourceSet.

Section ParmovDestinationSet.
  Import Parmov.

  Definition st_dest_set x (st:state var) :=
    match st with
    | State mv1 mv2 mvs => of_list (snd ⊝ (mv1 ++ mv2 ++ mvs))
                                  \ (of_list (fst ⊝ (mv1 ++ mv2 ++ mvs))
                                             ∪ singleton x)
    end.

  Tactic Notation "stsmpl" :=
    repeat (rewrite List.map_app || rewrite of_list_app || simpl).

  Lemma dtransition_dest_set x st st'
    : dtransition var (fun _ => x) st st' ->
      st_dest_set x st ⊆ st_dest_set x st'.
  Proof.
    intros TR.
    general induction TR; simpl in *; eauto; stsmpl.
    - cset_tac.
    - cset_tac.
    - cset_tac.
    - cset_tac.
    - cset_tac.
   Qed.

  Lemma dtransitions_dest_set x st st'
    : dtransitions var (fun _ => x) st st' ->
      st_dest_set x st ⊆ st_dest_set x st'.
  Proof.
    intros TR.
    general induction TR; simpl in *; eauto.
    - eapply dtransition_dest_set; eauto.
    - etransitivity; eauto.
  Qed.

  Lemma parmove_dest_set (x:var) mu
        (NOTIN:x ∉ of_list (snd ⊝ mu))
    : of_list (snd ⊝ mu) \ of_list (fst ⊝ mu) ⊆ moves_dest_set (parmove var var_dec (fun _ => x) mu).
  Proof.
    pose proof (parmove_aux_transitions _ var_dec (fun _ => x) (State _ mu nil nil)).
    eapply dtransitions_dest_set in H.
    simpl in *. revert H; stsmpl.
    unfold parmove, moves_dest_set.
    rewrite map_rev. rewrite of_list_rev.
    intros.
    cset_tac.
  Qed.

End ParmovDestinationSet.


Lemma eq_dec_comm X (x y:X)
  : { x = y } + { ~ x = y }
    -> { y = x } + { ~ y = x } .
Proof.
  firstorder.
Qed.

Notation "f <||= p" := (@Parmov.exec_seq var var_dec _ p f) (at level 29, left associativity).

Lemma Parmov_update_eq M x y
  : Parmov.update var var_dec (؟ val) x y M = M [x <- y].
Proof.
  unfold Parmov.update, update.
  eapply FunctionalExtensionality.functional_extensionality.
  intros. repeat cases; eauto. eapply var_eq_eq in COND. exfalso; eauto.
Qed.

Section GlueCode.
  Fixpoint list_to_stmt (p : list (var * var)) (s : stmt) {struct p} : stmt :=
    match p with
      | nil => s
      | (x, y) :: p' => stmtLet y (Operation (var_to_op x)) (list_to_stmt p' s)
    end.

  Lemma list_to_stmt_correct (p:Parmov.moves var) s (M:onv val) K
        (Def:defined_on (moves_source_set p) M)
    : star2 I.step (K, M, list_to_stmt p s) nil
        (K, M <||= p, s).
  Proof.
    general induction p.
    - firstorder using star2.
    - destruct a as [x y]. simpl in *.
      edestruct (Def x); eauto with cset.
      exploit (var_to_op_correct M x).
      eapply star2_silent.
      + constructor; eauto.
      + rewrite H.
        rewrite Parmov_update_eq.
        eapply IHp; eauto using defined_on_update_some,
                    defined_on_incl with cset.
  Qed.

  Lemma exec_par_eq p (E:onv val)
    : Parmov.exec_par var var_dec _ p E =
      E [ snd ⊝ p <-- lookup_list E (fst ⊝ p) ].
  Proof.
    general induction p; simpl; eauto.
    cases; subst; simpl.
    rewrite IHp. simpl.
    intros. eapply Parmov_update_eq.
  Qed.

  Lemma NoDup_is_mill m
    : NoDupA eq (snd ⊝ m)
      -> Parmov.is_mill var m.
  Proof.
    intros ND. hnf. unfold Parmov.dests.
    general induction m; invt NoDupA; simpl;
      eauto using Coqlib.list_norepet.
    econstructor; eauto.
    intro; eapply H1.
    eapply In_InA; eauto.
  Qed.

  Lemma parmov_update_with_list D (m:Parmov.moves var) (M:onv val) x
        (ND:NoDupA eq (snd ⊝ m))
        (NOTIN : x ∉ of_list (fst ⊝ m) ∪ of_list (snd ⊝ m))
    : agree_on eq (D \ singleton x)
               (M <||= Parmov.parmove var var_dec (fun _ => x) m)
               (M [ snd ⊝ m <-- lookup_list M (fst ⊝ m) ]).
  Proof.
    intros.
    exploit (@Parmov.parmove_correctness var var_dec (fun _ => x) (option val) m).
    - rewrite <- move_no_temp_notin. eauto.
    - eapply NoDup_is_mill; eauto.
    - rewrite <- exec_par_eq.
      hnf; intros.
      rewrite <- H.
      + reflexivity.
      + hnf; cset_tac.
  Qed.

End GlueCode.

Section Implementation.
Fixpoint onlyVars (Y:args) : params :=
  match Y with
    | nil => nil
    | (Var x)::Y => x::onlyVars Y
    | _::Y => onlyVars Y
  end.

Lemma lookup_list_var_map (E:onv val) Y v
  : omap (op_eval E) (Var ⊝ Y) = Some v
    -> lookup_list E Y = Some ⊝ v.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  monad_inv H; simpl. f_equal; eauto.
Qed.

Lemma onlyVars_length Y
      (AEF:forall (n : nat) (y : op), get Y n y -> isVar y)
  : ❬onlyVars Y❭ = ❬Y❭.
Proof.
  general induction Y; simpl; eauto.
  exploit AEF; eauto using get. inv H; simpl.
  rewrite IHY; eauto using get.
Qed.

Lemma onlyVars_idem Y
  : onlyVars (Var ⊝ Y) = Y.
Proof.
  general induction Y; simpl; f_equal; eauto.
Qed.

Hint Resolve onlyVars_length : len.

Definition repl (Z:params) x y := (fun z => if [x === z] then y else z) ⊝ Z.

Instance pos_lt_computable x y : Computable ((x <= y)%positive).
Proof.
  hnf; intros. unfold Pos.le.
  destruct (x ?= y)%positive.
  - left; discriminate.
  - left; discriminate.
  - right; eauto.
Qed.

Fixpoint parmove_elim_mem2mem (p:inf_partition var) (r:var) (pm:〔var * var〕) :=
  match pm with
  | (x,y)::pm => if [part_2 p x /\ part_2 p y] then (x,r)::(r,y)::parmove_elim_mem2mem p r pm
                else (x,y)::parmove_elim_mem2mem p r pm
  | nil => nil
  end.

Lemma moves_source_set_elim_mem2mem p (r:var) pm
      (NOTIN: r ∉ of_list (fst ⊝ pm) ∪ of_list (snd ⊝ pm))
  : moves_source_set (parmove_elim_mem2mem p r pm) [=] moves_source_set pm.
Proof.
  general induction pm; simpl; eauto.
  pose proof (moves_source_set_incl pm) as INCL.
  destruct a; simpl; cases; simpl in *; rewrite IHpm.
  - clear - NOTIN INCL; cset_tac.
  - clear - NOTIN; cset_tac.
  - clear - NOTIN INCL; cset_tac.
  - clear - NOTIN; cset_tac.
Qed.

Lemma moves_dest_set_elim_mem2mem p (r:var) pm
  : moves_dest_set pm ⊆ moves_dest_set (parmove_elim_mem2mem p r pm).
Proof.
  unfold moves_dest_set.
  general induction pm; simpl; eauto.
  destruct a; simpl; cases; simpl in *; rewrite IHpm.
  - clear; cset_tac.
  - clear; cset_tac.
Qed.

Fixpoint lower (p:inf_partition var) (preg:var) (DL:〔⦃var⦄ * params〕) s (an:ann (set var))
  : stmt :=
  match s, an with
    | stmtLet x e s, ann1 lv ans => stmtLet x e (lower p preg DL s ans)
    | stmtIf x s t, ann2 lv ans ant => stmtIf x (lower p preg DL s ans) (lower p preg DL t ant)
    | stmtApp l Y, ann0 lv  =>
      let '(lv', Z) := nth_default (∅, nil) DL (counted l) in
      let x := least_fresh_P (part_2 p) (lv' ∪ lv) in
      let z := least_fresh_P (part_2 p) ({x; lv'} ∪ lv) in
      let r := least_fresh_P (part_1 p) (lv' ∪ lv) in
      if [ (r <= preg)%positive ] then
        let mvs := Parmov.parmove2 var var_dec (fun _ => x) (onlyVars Y) Z in
        let mvs' := parmove_elim_mem2mem p r mvs in
        list_to_stmt mvs' (stmtApp l nil)
      else
        let r := least_fresh_P (part_1 p) lv in
        if [ (r <= preg)%positive ] then
          let mvs := Parmov.parmove2 var var_dec (fun _ => x) (onlyVars Y) (repl Z r z) in
          let mvs' := parmove_elim_mem2mem p r mvs in
          list_to_stmt (mvs'++(z,r)::nil) (stmtApp l nil)
        else
          let r := proj1_sig (InfiniteSubset.inf_subset_least (part_1 p)) in
          let mvs := Parmov.parmove2 var var_dec (fun _ => x) (repl (onlyVars Y) r z) (repl Z r z) in
          let mvs' := parmove_elim_mem2mem p r mvs in
          list_to_stmt ((r,z)::mvs'++(z,r)::nil) (stmtApp l nil)
    | stmtReturn x, ann0 lv => stmtReturn x
    | stmtFun F t, annF lv ans ant =>
      let DL' := pair ⊜ (getAnn ⊝ ans) (fst ⊝ F) in
      let s' := zip (fun Zs a => lower p preg (DL' ++ DL) (snd Zs) a) F ans in
      let t' := lower p preg (DL' ++ DL) t ant in
      (stmtFun ((fun s => (nil, s)) ⊝ s') t')
    | _, _ => s
  end.

Inductive approx
  : inf_partition var -> var ->
    list (set var) -> list I.block -> list I.block -> ⦃var⦄ -> I.block -> I.block -> Prop :=
  approxI L L' DL Z s s' lv n p preg
  (al:ann (set var))
  (LS:live_sound Imperative (I.block_Z ⊝ L) DL s al)
  (AL:(of_list Z) ⊆ lv)
  (AEF:app_expfree s)
  (ND:NoDupA eq Z)
  (INCL:getAnn al \ of_list Z ⊆ lv)
  (spm:lower p preg (zip pair DL (I.block_Z ⊝ L)) s al = s')
  : approx p preg DL L L' lv (I.blockI Z s n) (I.blockI nil s' n).


Lemma omap_var_defined_on Za E vl
: omap (op_eval E) (List.map Var Za) = Some vl
  -> defined_on (of_list Za) E.
Proof.
  intros. general induction Za; simpl.
  - hnf; intros. cset_tac.
  - simpl in *.
    monad_inv H.
    exploit IHZa; eauto.
    hnf; intros. cset_tac.
Qed.

Lemma fst_combine A B (L:list A) (L':list B) (Len:❬L❭=❬L'❭)
  : fst ⊝ combine L L' = L.
Proof.
  general induction Len; simpl; f_equal; eauto.
Qed.

Lemma snd_combine A B (L:list A) (L':list B) (Len:❬L❭=❬L'❭)
  : snd ⊝ combine L L' = L'.
Proof.
  general induction Len; simpl; f_equal; eauto.
Qed.

Lemma repl_not_in Z x y
  : x ∉ of_list Z -> repl Z x y = Z.
Proof.
  general induction Z; simpl; repeat cases; simpl in *; eauto.
  - invc COND. cset_tac.
  - f_equal. eapply IHZ; cset_tac.
Qed.

Lemma repl_not_in' Z x y x'
  : x ∉ of_list Z -> x =/= y -> x ∉ of_list (repl Z x' y).
Proof.
  general induction Z; simpl; repeat cases; simpl in *; eauto.
  - invc COND. cset_tac.
  - exploit (IHZ x y); eauto. cset_tac. cset_tac.
Qed.

Lemma repl_nodup Z x y
  : y ∉ of_list Z -> NoDupA eq Z -> NoDupA eq (repl Z x y).
Proof.
  intros IN ND.
  general induction ND; simpl; repeat cases; simpl in *; eauto using NoDupA.
  - invc COND. econstructor; eauto.
    + rewrite repl_not_in; cset_tac.
    + eapply IHND. cset_tac.
  - econstructor; eauto.
    + exploit (@repl_not_in' l x y x0); eauto. cset_tac. cset_tac.
    + eapply IHND; eauto. cset_tac.
Qed.

Lemma of_list_repl_incl Z x y
  : of_list (repl Z x y) ⊆ {y; of_list Z}.
Proof.
  general induction Z; simpl; repeat cases; eauto.
  - cset_tac.
  - rewrite IHZ; cset_tac.
  - rewrite IHZ; cset_tac.
Qed.

Lemma of_list_repl Z x y
  : of_list (repl Z x y) ⊆ {y; of_list Z \ singleton x}.
Proof.
  general induction Z; simpl; repeat cases; eauto.
  - cset_tac.
  - rewrite IHZ; cset_tac.
  - rewrite IHZ; cset_tac.
Qed.

Lemma of_list_repl_eq (Z:params) x y
      (IN: x ∈ of_list Z)
  : of_list (repl Z x y) [=] {y; of_list Z \ singleton x}.
Proof.
  general induction Z; simpl; repeat cases; simpl in *; eauto.
  - invc COND. decide (a ∈ of_list Z).
    + rewrite IHZ; cset_tac.
    + rewrite repl_not_in; eauto. cset_tac.
  - rewrite IHZ; cset_tac.
Qed.

Lemma of_list_repl' Z x y
  : of_list Z \ singleton x ⊆ of_list (repl Z x y).
Proof.
  general induction Z; simpl; repeat cases; eauto.
  - rewrite <- IHZ; cset_tac.
  - rewrite <- IHZ; cset_tac.
Qed.

Lemma repl_get_ne (Z:params) n (x y z:var)
  : get Z n z -> z =/= x -> get (repl Z x y) n z.
Proof.
  intros GET. general induction GET; simpl; repeat cases; eauto using get.
Qed.

Lemma repl_get_eq (Z:params) n (x y z:var)
  : get Z n x -> get (repl Z x y) n y.
Proof.
  intros GET. general induction GET; simpl; repeat cases; eauto using get.
Qed.

Lemma repl_get_inv (Z:params) n (x y z:var)
  : get (repl Z x y) n z -> z =/= y -> get Z n z.
Proof.
  intros GET.
  general induction Z; simpl in *; repeat cases in GET; inv GET; eauto using get.
Qed.

Lemma exec_seq_agree G pm (E E':onv val)
      (AGR: agree_on eq (G ∪ moves_source_set pm) E E')
  : agree_on eq G (E <||= pm) (E' <||= pm).
Proof.
  general induction pm; simpl in *; eauto.
  - eapply agree_on_incl; eauto.
  - destruct a. rewrite !Parmov_update_eq.
    eapply IHpm. simpl in *.
    eapply agree_on_update_same.
    eapply AGR; eauto.
    cset_tac.
    eapply agree_on_incl; eauto.
    cset_tac.
Qed.


Lemma parmove_elim_mem2mem_agree G (p:inf_partition var) (reg:var) (E':onv val) pm
      (NOTIN:reg ∉ of_list (fst ⊝ pm))
  : agree_on eq (G \ singleton reg)
             (E' <||= parmove_elim_mem2mem p reg pm)
             (E' <||= pm).
Proof.
  general induction pm; simpl.
  - reflexivity.
  - destruct a; cases; simpl; rewrite !Parmov_update_eq.
    + etransitivity.
      eapply IHpm. simpl in *. cset_tac.
      lud; eauto.
      eapply exec_seq_agree.
      hnf; intros. lud.
      invc H3. exfalso.
      rewrite moves_source_set_incl in H. simpl in *.
      cset_tac.
    + eapply IHpm. simpl in *. cset_tac.
Qed.

Lemma parmov_repl_agree p lv (E:onv val) (pmtmp reg lstmp:var) (Y Z:params) (Len:❬Y❭=❬Z❭) (NEQ:reg =/= lstmp) (NEQ2:pmtmp =/= lstmp) (NEQ3:reg =/= pmtmp)
      (NDZ:NoDupA _eq Z) (NOTIN:lstmp ∉ of_list Y ∪ of_list Z) (NOTIN2: pmtmp ∉ of_list Y ∪ of_list Z)
  : agree_on eq (lv \ {lstmp; singleton pmtmp})
             (E <||= Parmov.parmove2 positive var_dec (fun _ : positive => pmtmp) Y Z)
             (E <||=
                ((reg, lstmp)
                   ::
                   parmove_elim_mem2mem p reg
                   (Parmov.parmove2 positive var_dec (fun _ : positive => pmtmp) (repl Y reg lstmp)
                                    (repl Z reg lstmp)) ++ (lstmp, reg) :: nil)).
Proof.
  simpl; rewrite Parmov.exec_seq_app; simpl.
  rewrite !Parmov_update_eq.
  set (ZR:=repl Z reg lstmp) in *.
  set (YR:=repl Y reg lstmp) in *.
  set (PM:=Parmov.parmove2 positive var_dec (fun _ : positive => pmtmp) (repl Y reg lstmp)
                           (repl Z reg lstmp)) in *.
  etransitivity. {
    eapply agree_on_incl.
    eapply parmov_update_with_list; eauto.
    + rewrite snd_combine; eauto with len.
    + rewrite fst_combine, snd_combine; eauto with len.
    + cset_tac.
  }
  symmetry. etransitivity. {
    eapply agree_on_update_same. reflexivity.
    eapply parmove_elim_mem2mem_agree.
    unfold Parmov.parmove2.
    rewrite fst_parmove. rewrite fst_combine; eauto with len.
    subst YR. rewrite of_list_repl. cset_tac.
  }
  etransitivity. {
    eapply agree_on_update_same. reflexivity.
    eapply agree_on_incl.
    eapply parmov_update_with_list; eauto.
    + rewrite snd_combine; eauto with len.
      eapply repl_nodup; eauto. cset_tac.
    + rewrite fst_combine, snd_combine; eauto with len.
      subst ZR YR. rewrite !of_list_repl_incl. cset_tac.
    + cset_tac.
  }
  symmetry.
  rewrite snd_combine, fst_combine; eauto with len.
  erewrite parmove_elim_mem2mem_agree with (G:=singleton lstmp);
    [|unfold Parmov.parmove2; rewrite fst_parmove; try rewrite fst_combine; eauto with len;
      subst YR; rewrite of_list_repl; cset_tac
     |cset_tac].
  hnf; intros. lud.
  - unfold Parmov.parmove2.
    erewrite parmov_update_with_list; eauto;
      try rewrite snd_combine; try rewrite fst_combine; eauto with len.
    + invc H3; clear e.
      decide (reg ∈ of_list Z).
      * eapply of_list_get_first in i; dcr. symmetry in H8; invc H8.
        exploit (@update_with_list_lookup_in_list_first _ _ _ E x Z (lookup_list E Y)); dcr;
          eauto with len.
        rewrite H12. rewrite lookup_list_map in H11. inv_get. rewrite <- EQ.
        exploit repl_get_eq; try eapply H3; eauto.
        exploit (@update_with_list_lookup_in_list_first _ _ _ (E [lstmp <- E reg]) x ZR (lookup_list (E [lstmp <- E reg]) YR)); dcr;
          eauto with len.
        -- intros. intro. invc H7.
           unfold ZR in H6. unfold repl in H6. inv_get. cases in EQ0.
           ++ eapply H10. eauto. eauto. eauto.
           ++ subst.
             eapply get_in_of_list in H6. cset_tac.
        -- rewrite H8.
           rewrite lookup_list_map in H7. subst YR. unfold repl in H7.
           inv_get. cases in H5.
           ++ invc COND.
             rewrite <- H5. lud. cset_tac.
           ++ unfold repl in H4. inv_get.
             cases in H4.
             rewrite <- H5. lud. invc H7.
             eapply get_in_of_list in H11. exfalso. cset_tac.
      * rewrite !lookup_set_update_not_in_Z; eauto.
        lud. cset_tac.
        subst ZR. rewrite repl_not_in; eauto. cset_tac.
    + eapply repl_nodup; eauto. cset_tac.
    + subst ZR YR. rewrite !of_list_repl_incl. cset_tac.
    + instantiate (1:=singleton lstmp). cset_tac.
  - rewrite fst_combine, snd_combine; eauto with len.
    decide (x ∈ of_list Z).
    + eapply of_list_get_first in i; dcr. symmetry in H6; invc H6.
      exploit (@update_with_list_lookup_in_list_first _ _ _ E x0 Z (lookup_list E Y)); dcr;
        eauto with len.
      rewrite H10.
      rewrite lookup_list_map in H9. inv_get. rewrite <- EQ.
      exploit repl_get_ne; try eapply H4; eauto.
      exploit (@update_with_list_lookup_in_list_first _ _ _ (E [lstmp <- E reg]) x0 ZR (lookup_list (E [lstmp <- E reg]) YR)); dcr;
        eauto with len.
      * subst ZR. intros. unfold repl in *. inv_get.
        repeat cases; eauto. invc COND.
        intro. invc H6.
        cset_tac.
      * subst YR. rewrite lookup_list_map in H11.
        unfold repl in H6, H11. inv_get.
        repeat cases; eauto.
        cases in H7.
        -- invc COND.
           rewrite <- H7. lud; eauto.
        -- rewrite <- H7. lud; eauto. invc H11. clear e.
           exfalso. clear - H9 NOTIN.
           eapply get_in_of_list in H9.
           cset_tac.
    + rewrite !lookup_set_update_not_in_Z; eauto.
      lud. cset_tac.
      eapply repl_not_in'; eauto. cset_tac.
Qed.

Local Arguments list_to_stmt : simpl never.
Local Arguments Parmov.exec_seq : simpl never.


Lemma correct (p:inf_partition var) (preg:var) Lv L L' s (E E':onv val) (al: ann (set var))
      (LS:live_sound Imperative (I.block_Z ⊝ L) Lv s al)
      (AEF:app_expfree s)
      (LA:inRel (approx p preg) Lv L L')
      (EEQ:agree_on eq (getAnn al) E E')
      (DEF:defined_on (getAnn al) E) (PREG1: part_1 p preg)
  : sim bot3 Sim (L,E,s) (L', E', lower p preg (zip pair Lv (I.block_Z ⊝ L))  s al).
Proof.
  revert_all. pcofix pmSim_sim; intros.
  inv LS; inv AEF; simpl in *.
  - invt live_exp_sound.
    + eapply (sim_let_op il_statetype_I);
        eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl,
        defined_on_update_some, defined_on_incl.
    + eapply (sim_let_call il_statetype_I);
        eauto 10 using agree_on_update_same, agree_on_incl,
        defined_on_update_some, defined_on_incl.
        erewrite <- omap_op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply (sim_cond il_statetype_I);
      eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl, defined_on_incl.
  - rewrite nth_default_eq. erewrite get_nth; eauto using zip_get; simpl.
    inRel_invs.
    inv_get. simpl in *.
    eapply op_eval_var in H5 as [Y' ?]; subst Y.
    rewrite onlyVars_idem in *. len_simpl.
    case_eq (omap (op_eval E) (Var ⊝ Y')); intros.
    + set (reg:=least_fresh_P (part_1 p) (blv ∪ lv)) in *.
      set (reg2:=least_fresh_P (part_1 p) lv) in *.
      set (lreg:=InfiniteSubset.inf_subset_least (part_1 p)) in *.
      set (pmtmp := least_fresh_P (part_2 p) (blv ∪ lv)) in *.
      set (lstmp := least_fresh_P (part_2 p) ({pmtmp; blv} ∪ lv)) in *.
      assert (NEQ1:reg =/= lstmp). {
        subst reg lstmp.
        intro.
        eapply (part_disj p (least_fresh_P (part_1 p) (blv ∪ lv))); eauto.
        eapply least_fresh_P_full_spec.
        rewrite H5.
        eapply least_fresh_P_full_spec.
      }
      assert (NEQ2: pmtmp =/= lstmp). {
        subst pmtmp lstmp. intro.
        eapply (least_fresh_P_full_spec (part_2 p) ({least_fresh_P (part_2 p) (blv ∪ lv); blv} ∪ lv)).
        rewrite <- H5. clear. cset_tac.
      }
      assert (NEQ3:proj1_sig lreg =/= lstmp). {
        subst lreg lstmp. destr_sig; dcr.
        intro. invc H7.
        eapply (part_disj p); eauto.
        eapply least_fresh_P_full_spec.
      }
      assert (NEQ4:proj1_sig lreg =/= pmtmp). {
        subst lreg pmtmp. destr_sig; dcr.
        intro. invc H5. simpl in *. dcr.
        eapply (part_disj p); eauto.
        eapply least_fresh_P_full_spec.
      }
      assert (pmtmp ∉ of_list Y' ∪ blv). {
        intro.
        eapply (least_fresh_P_full_spec (part_2 p) (blv ∪ lv)).
        eapply Ops.freeVars_live_list in H3.
        rewrite <- of_list_freeVars_vars in H3. rewrite <- H3 at 2.
        setoid_rewrite union_comm at 2. eauto.
      }
      assert (lstmp ∉ of_list Y' ∪ blv). {
        intro.
        eapply (least_fresh_P_full_spec (part_2 p) ({pmtmp; blv} ∪ lv)).
        eapply Ops.freeVars_live_list in H3.
        rewrite <- of_list_freeVars_vars in H3. rewrite <- H3 at 2.
        setoid_rewrite union_comm at 2.
        setoid_rewrite <- incl_add' at 2. eauto.
      }
      assert (reg ∉ getAnn al). {
        intro.
        eapply (least_fresh_P_full_spec (part_1 p) (blv ∪ lv)).
        change (reg ∈ blv ∪ lv). clear - H7 INCL AL. cset_tac.
      }
      unfold Parmov.srcs, Parmov.dests in *.
      exploit omap_op_eval_live_agree; try eassumption.
      {
        repeat cases.
        - exploit (@list_to_stmt_correct
                     (parmove_elim_mem2mem p reg
                                           (Parmov.parmove2 _ var_dec (fun _ => pmtmp) Y' Z0))
                     (stmtApp l nil) E' L'). {
            unfold Parmov.parmove2.
            simpl.
            rewrite moves_source_set_elim_mem2mem.
            rewrite !parmove_src_set. rewrite fst_combine; eauto with len.
            eapply omap_var_defined_on; eauto.
            admit.
          }
          pfold. eapply SimSilent.
          * eapply plus2O. econstructor; eauto with len. reflexivity.
          * eapply star2_plus2_plus2 with (A:=nil) (B:=nil); eauto.
            eapply plus2O. econstructor; eauto. reflexivity. reflexivity.
          * right; eapply (pmSim_sim p preg); try eapply LA1; eauto; simpl.
            -- eapply (inRel_drop LA H4).
            -- assert (getAnn al ⊆ blv) by eauto with cset.
               eapply agree_on_incl.
               symmetry. etransitivity. {
                 eapply parmove_elim_mem2mem_agree.
                 admit.
               }
               eapply agree_on_incl.
               etransitivity.
               eapply (@parmov_update_with_list (getAnn al));
                 try rewrite eauto.
               ++ rewrite snd_combine; eauto.
               ++ assert (of_list Y' ⊆ lv). {
                   eapply Ops.freeVars_live_list in H3.
                   rewrite <- H3.
                   rewrite of_list_freeVars_vars. reflexivity.
                 }
                 rewrite fst_combine, snd_combine; eauto.
                 rewrite AL; eauto.
               ++ rewrite fst_combine, snd_combine; eauto.
                 rewrite disj_minus_eq; eauto.
                 erewrite <- lookup_list_var_map; eauto.
                 eapply update_with_list_agree; eauto with len.
                 symmetry.
                 eapply agree_on_incl; eauto. eauto with cset.
                 rewrite H10. clear - H5. cset_tac.
               ++ instantiate (1:=getAnn al).
                 clear - H10 H5. cset_tac.
               ++ clear - H7. cset_tac.
            -- eapply defined_on_update_list; eauto with len.
               assert (getAnn al \ of_list Z0 ⊆ lv). {
                 rewrite <- H1. rewrite <- INCL. clear. cset_tac.
               }
               eauto using defined_on_incl.
        - exploit (@list_to_stmt_correct
                     (parmove_elim_mem2mem
                        p reg2
                        (Parmov.parmove2 positive var_dec (fun _ => pmtmp) Y' (repl Z0 reg2 lstmp)) ++
                        (lstmp, reg2) :: nil)
                     (stmtApp l nil) E' L'). {
            unfold Parmov.parmove2.
            simpl. rewrite moves_source_set_app; simpl.
            eapply Ops.freeVars_live_list in H3.
            rewrite <- of_list_freeVars_vars in H3.
            assert (IN:reg2 ∈ of_list Z0). {
              edestruct (least_fresh_P_full_spec (part_1 p) (lv)); dcr.
              edestruct (least_fresh_P_full_spec (part_1 p) (blv ∪ lv)); dcr.
              subst reg reg2.
              set (reg:=least_fresh_P (part_1 p) (blv ∪ lv)) in *.
              set (reg2:=least_fresh_P (part_1 p) lv) in *.
              exploit (H14 reg2); eauto.
              simpl.
              eapply Pos.le_lt_trans; eauto.
              eapply Pos.lt_nle. eauto. rewrite filter_incl in H13; eauto.
              clear - H13 H9 AL H1. clearbody reg2. cset_tac'.
              decide (reg2 ∈ of_list Z0); eauto. cset_tac.
            }
            assert (reg2 ∉ of_list Y'). {
              edestruct (least_fresh_P_full_spec (part_1 p) (lv)); dcr.
              rewrite H3. eauto.
            }
            rewrite !moves_source_set_elim_mem2mem.
            rewrite !parmove_src_set. simpl. rewrite fst_combine; eauto with len.
            eapply defined_on_incl.
            eapply defined_on_agree_eq; eauto.
            rewrite H3.
            rewrite <- moves_dest_set_elim_mem2mem.
            rewrite <- parmove_dest_set;
              try rewrite fst_combine; try rewrite snd_combine; eauto with len.
            rewrite of_list_repl_eq; eauto. clear - H3. cset_tac'.
            rewrite of_list_repl_eq; eauto. clear - NEQ2 H5 AL; cset_tac.
            - rewrite fst_parmove, snd_parmove, fst_combine, snd_combine; eauto with len.
              rewrite !of_list_repl.
              admit.
          }
           pfold. eapply SimSilent.
          * eapply plus2O. econstructor; eauto with len. reflexivity.
          * eapply star2_plus2_plus2 with (A:=nil) (B:=nil); eauto.
            eapply plus2O. econstructor; eauto. reflexivity. reflexivity.
          * right; eapply pmSim_sim; try eapply LA1; eauto; simpl.
            -- eapply (inRel_drop LA H4).
            -- assert (getAnn al ⊆ blv) by eauto with cset.
               symmetry. etransitivity. {
                 eapply agree_on_incl.
                 symmetry.
                 eapply parmov_repl_agree; eauto.
                 rewrite AL. eauto. rewrite AL; eauto.
                 instantiate (1:=blv).
                 rewrite H10. clear - H5 H6. cset_tac.
               }
               eapply agree_on_incl.
               etransitivity.
               eapply (@parmov_update_with_list (getAnn al));
                 try rewrite eauto.
               ++ rewrite snd_combine; eauto.
               ++ assert (of_list Y' ⊆ lv). {
                   eapply Ops.freeVars_live_list in H3.
                   rewrite <- H3.
                   rewrite of_list_freeVars_vars. reflexivity.
                 }
                 rewrite fst_combine, snd_combine; eauto.
                 rewrite AL; eauto.
               ++ rewrite fst_combine, snd_combine; eauto.
                 rewrite disj_minus_eq; eauto.
                 erewrite <- lookup_list_var_map; eauto.
                 eapply update_with_list_agree; eauto with len.
                 symmetry.
                 eapply agree_on_incl; eauto. eauto with cset.
                 rewrite H10. clear - H5. cset_tac.
               ++ clear - H10 H5. cset_tac.
            -- eapply defined_on_update_list; eauto with len.
               assert (getAnn al \ of_list Z0 ⊆ lv). {
                 rewrite <- H1. rewrite <- INCL. clear. cset_tac.
               }
               eauto using defined_on_incl.

        - exploit (@list_to_stmt_correct
                     ((proj1_sig lreg, lstmp)
                        :: parmove_elim_mem2mem p (proj1_sig lreg)
                        (Parmov.parmove2 positive var_dec (fun _ : positive => pmtmp)
                        (repl Y' (proj1_sig lreg) lstmp)
                        (repl Z0 (proj1_sig lreg) lstmp)) ++ (lstmp, proj1_sig lreg) :: nil)
                     (stmtApp l nil) E' L'). {
            unfold Parmov.parmove2.
            simpl. rewrite moves_source_set_app; simpl.
            rewrite !moves_source_set_elim_mem2mem.
            rewrite !parmove_src_set. simpl. rewrite fst_combine; eauto with len.
            edestruct (least_fresh_P_full_spec (part_1 p) (lv)); dcr.
            exploit (H11 (proj1_sig lreg)).
            - subst lreg. destr_sig. eauto.
            - subst lreg. destr_sig; dcr. simpl in *; dcr.
              exploit (H13 (least_fresh_P (part_1 p) (lv))); eauto.
              + destruct H14; eauto. invc H14. subst reg.
                set (reg:=least_fresh_P (part_1 p) (lv)) in *.
                exfalso. eapply NOTCOND0.
                eapply Pos.lt_eq_cases. eapply H13. eauto.
            - rewrite of_list_repl_incl.
              eapply defined_on_incl.
              eapply defined_on_agree_eq; eauto.
              eapply Ops.freeVars_live_list in H3.
              rewrite <- of_list_freeVars_vars in H3. rewrite H3.
              subst reg.
              assert (IN:proj1_sig lreg ∈ lv). {
                rewrite filter_incl in H10; eauto.
              }
              clear - IN. cset_tac.
            - rewrite fst_parmove, snd_parmove, fst_combine, snd_combine; eauto with len.
              rewrite !of_list_repl.
              clear - NEQ3 NEQ4. cset_tac.
          }
          pfold. eapply SimSilent.
          * eapply plus2O. econstructor; eauto with len. reflexivity.
          * eapply star2_plus2_plus2 with (A:=nil) (B:=nil); eauto.
            eapply plus2O. econstructor; eauto. reflexivity. reflexivity.
          * right; eapply pmSim_sim; try eapply LA1; eauto; simpl.
            -- eapply (inRel_drop LA H4).
            -- assert (getAnn al ⊆ blv) by eauto with cset.
               symmetry. etransitivity. {
                 eapply agree_on_incl.
                 symmetry.
                 eapply parmov_repl_agree; eauto.
                 rewrite AL. eauto. rewrite AL; eauto.
                 instantiate (1:=blv).
                 rewrite H10. clear - H5 H6. cset_tac.
               }
               eapply agree_on_incl.
               etransitivity.
               eapply (@parmov_update_with_list (getAnn al));
                 try rewrite eauto.
               ++ rewrite snd_combine; eauto.
               ++ assert (of_list Y' ⊆ lv). {
                   eapply Ops.freeVars_live_list in H3.
                   rewrite <- H3.
                   rewrite of_list_freeVars_vars. reflexivity.
                 }
                 rewrite fst_combine, snd_combine; eauto.
                 rewrite AL; eauto.
               ++ rewrite fst_combine, snd_combine; eauto.
                 rewrite disj_minus_eq; eauto.
                 erewrite <- lookup_list_var_map; eauto.
                 eapply update_with_list_agree; eauto with len.
                 symmetry.
                 eapply agree_on_incl; eauto. eauto with cset.
                 rewrite H10. clear - H5. cset_tac.
               ++ clear - H10 H5. cset_tac.
            -- eapply defined_on_update_list; eauto with len.
               assert (getAnn al \ of_list Z0 ⊆ lv). {
                 rewrite <- H1. rewrite <- INCL. clear. cset_tac.
               }
               eauto using defined_on_incl.
      }
    + perr.
  - pno_step. simpl. eauto using op_eval_live.
  - pone_step. right.
    rewrite <- zip_app in *; eauto with len.
    assert (EQ:fst ⊝ F ++ I.block_Z ⊝ L = I.block_Z ⊝ (mapi I.mkBlock F ++ L)). {
      unfold mapi. generalize 0.
      clear. general induction F; simpl; f_equal; eauto.
    }
    rewrite EQ in *.
    eapply pmSim_sim; try eapply H; eauto using agree_on_incl.
    econstructor; eauto.
    eapply mutual_approx; eauto 20 using mkBlock_I_i with len.
    intros; inv_get.
    econstructor; eauto.
    + exploit H2; eauto.
    + eapply H2; eauto.
    + eauto using defined_on_incl; eauto.
Qed.

End Implementation.

Lemma list_to_stmt_noParams pm s
      (NP:noParams s)
  : noParams (list_to_stmt pm s).
Proof.
  general induction pm; simpl;
    repeat let_pair_case_eq; eauto using noParams.
Qed.

Lemma pm_lower_noParams p ZL Lv s al preg
      (LS:live_sound Imperative ZL Lv s al)
  : noParams (lower p preg (zip pair Lv ZL) s al).
Proof.
  general induction LS; simpl;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; eauto using noParams.
  - cases; eauto using list_to_stmt_noParams, noParams.
  - econstructor; intros; inv_get; simpl;
      try rewrite <- zip_app; eauto using noParams with len.
Qed.
