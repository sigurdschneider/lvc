Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL Bisim Infra.Status Pos.

Set Implicit Arguments.
Unset Printing Records.

Inductive nstmt : Type :=
| nstmtLet    (x : var) (e: exp) (s : nstmt)
| nstmtIf     (e : exp) (s : nstmt) (t : nstmt)
| nstmtApp   (l : var) (Y:args)
| nstmtReturn (e : exp)
| nstmtExtern (x : var) (f:external) (Y:args) (s:nstmt)
(* block f Z : rt = s in b *)
| nstmtFun    (F : list (var * params * nstmt)) (t : nstmt).

Fixpoint freeVars (s:nstmt) : set var :=
  match s with
    | nstmtLet x e s0 => (freeVars s0 \ {{x}}) ∪ Exp.freeVars e
    | nstmtIf e s1 s2 => freeVars s1 ∪ freeVars s2 ∪ Exp.freeVars e
    | nstmtApp l Y => list_union (List.map Exp.freeVars Y)
    | nstmtReturn e => Exp.freeVars e
    | nstmtExtern x f Y s => (freeVars s \ {{x}}) ∪ list_union (List.map Exp.freeVars Y)
    | nstmtFun F s2 =>
      list_union (List.map (fun f => (freeVars (snd f) \ of_list (snd (fst f)))) F)
                 ∪ freeVars s2
  end.

(** *** Functional Semantics *)
Module F.

  Inductive block : Type :=
    blockI {
        block_L : onv block;
        block_E : onv val;
        block_F : list (var * params * nstmt);
        block_f : nat
      }.

  Definition labenv := onv block.
  Definition state : Type := (labenv * onv val * nstmt)%type.

  Definition mkBlock L E F f (_:var * params * nstmt) :=
    blockI L E F f.

  Definition mkBlocks L E F :=
    mapi (mkBlock L E F) F.


  Inductive step : state -> event -> state -> Prop :=
  | nstepExp L E x e b v
    (def:exp_eval E e = Some v)
    : step (L, E, nstmtLet x e b) EvtTau (L, E[x<-Some v], b)

  | nstepIfT L E
    (e:exp) b1 b2 v
    (def:exp_eval E e = Some v)
    (condTrue: val2bool v = true)
    : step (L, E, nstmtIf e b1 b2) EvtTau (L, E, b1)

  | nstepIfF L E
    (e:exp) b1 b2 v
    (def:exp_eval E e = Some v)
    (condFalse:val2bool v = false)
    : step (L, E, nstmtIf e b1 b2) EvtTau (L, E, b2)


  | nstepGoto L E l l' Y Z s L' E' F f
    (len:length Z = length Y)
    (lEQ:l = l') (* hack: otherwise inversions confuse guardedness checker in
                  simulation proofs*)

    (Ldef:L l = Some (blockI L' E' F f)) E'' vl
    (def:omap (exp_eval E) Y = Some vl)
    (sdef : get F f (l', Z, s))
    (updOk:E'[Z <-- List.map Some vl]  = E'')
    : step (L, E, nstmtApp l Y)
           EvtTau
           (L'[List.map (fst ∘ fst) F <-- List.map Some (mkBlocks L' E' F)], E'', s)

  | stepLet (L:onv block) E F t
    : step (L, E, nstmtFun F t) EvtTau (L[List.map (fst ∘ fst) F <-- List.map Some (mkBlocks L E F)], E, t)

  | stepExtern L E x f Y s vl v
    (def:omap (exp_eval E) Y = Some vl)
    : step  (L, E, nstmtExtern x f Y s)
            (EvtExtern (ExternI f vl v))
            (L, E[x <- Some v], s).


  Lemma step_internally_deterministic :
    internally_deterministic step.
  Proof.
    hnf; intros. inv H; inv H0; split; eauto; try congruence.
    rewrite Ldef0 in Ldef. inv Ldef. repeat (get_functional; subst); congruence.
  Qed.

  Lemma step_dec
  : reddec step.
  Proof.
    hnf; intros. destruct x as [[L V] []].
    - case_eq (exp_eval V e); intros. left. eexists EvtTau; eauto using step.
      right. stuck.
    - case_eq (exp_eval V e); intros.
      left. case_eq (val2bool v); intros; eexists EvtTau; eauto using step.
      right. stuck.
    - case_eq (L l); intros.
      + destruct b as [L' E' F' f'].
        destruct (get_dec F' f') as [[[[l' Z] s] ?]|].
        * decide (l = l'); subst; try now (right; stuck2).
          decide (length Z = length Y); try now (right; stuck2).
          case_eq (omap (exp_eval V) Y); intros; try now (right; stuck2).
          left. eexists EvtTau. econstructor. econstructor; eauto.
          orewrite (l' + 0=l'). eauto.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
        * right; stuck2. rewrite Ldef in H. inv H. eauto.
      + right. stuck.
    - right. stuck.
    - case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      left. eexists (EvtExtern (ExternI f l 0)). eauto using step.
    - left. exists EvtTau. eauto using step.
  Qed.

End F.


(** *** Imperative Semantics *)
Module I.

  Inductive block : Type :=
    blockI {
        block_L : onv block;
        block_F : list (var * params * nstmt);
        block_f : nat
      }.

  Definition labenv := onv block.
  Definition state : Type := (labenv * onv val * nstmt)%type.
  Definition labenv_empty : labenv := fun _ => None.

  Definition mkBlock L F f (_:var *params*nstmt):=
    blockI L F f.

  Definition mkBlocks L F :=
    mapi (mkBlock L F) F.


  Inductive step : state -> event -> state -> Prop :=
  | nstepExp L E x e b v
    (def:exp_eval E e = Some v)
    : step (L, E, nstmtLet x e b) EvtTau (L, E[x<-Some v], b)

  | nstepIfT L E
    (e:exp) b1 b2 v
    (def:exp_eval E e = Some v)
    (condTrue: val2bool v = true)
    : step (L, E, nstmtIf e b1 b2) EvtTau (L, E, b1)

  | nstepIfF L E
    (e:exp) b1 b2 v
    (def:exp_eval E e = Some v)
    (condFalse:val2bool v = false)
    : step (L, E, nstmtIf e b1 b2) EvtTau (L, E, b2)

  | nstepGoto L E l l' Y Z s L' F f
    (len:length Z = length Y)
    (lEQ:l = l') (* hack: otherwise inversions confuse guardedness checker in
                  simulation proofs*)

    (Ldef:L l = Some (blockI L' F f)) E'' vl
    (def:omap (exp_eval E) Y = Some vl)
    (sdef : get F f (l', Z, s))
    (updOk:E[Z <-- List.map Some vl]  = E'')
    : step (L, E, nstmtApp l Y)
           EvtTau
           (L'[List.map (fst ∘ fst) F <-- List.map Some (mkBlocks L' F)], E'', s)

  | stepLet L E F t
    : step (L, E, nstmtFun F t)
           EvtTau
           (L[List.map (fst ∘ fst) F <-- List.map Some (mkBlocks L F)], E, t)

  | stepExtern L E x f Y s vl v
    (def:omap (exp_eval E) Y = Some vl)
    : step  (L, E, nstmtExtern x f Y s)
            (EvtExtern (ExternI f vl v))
            (L, E[x <- Some v], s).


  Lemma step_internally_deterministic :
    internally_deterministic step.
  Proof.
    hnf; intros. inv H; inv H0; split; eauto; try congruence.
    rewrite Ldef0 in Ldef. inv Ldef. get_functional; subst. congruence.
  Qed.

  Lemma step_externally_determined
  : externally_determined step.
  Proof.
    hnf; intros.
    inv H; inv H0; eauto; try get_functional; try congruence.
    rewrite Ldef0 in Ldef. inv Ldef. get_functional; subst. congruence.
  Qed.


  Lemma step_dec
  : reddec step.
  Proof.
      hnf; intros. destruct x as [[L V] []].
    - case_eq (exp_eval V e); intros. left. eexists EvtTau; eauto using step.
      right. stuck.
    - case_eq (exp_eval V e); intros.
      left. case_eq (val2bool v); intros; eexists EvtTau; eauto using step.
      right. stuck.
    - case_eq (L l); intros.
      + destruct b as [L' F' f'].
        destruct (get_dec F' f') as [[[[l' Z] s] ?]|].
        * decide (l = l'); subst; try now (right; stuck2).
          decide (length Z = length Y); try now (right; stuck2).
          case_eq (omap (exp_eval V) Y); intros; try now (right; stuck2).
          left. eexists EvtTau. econstructor. econstructor; eauto.
          orewrite (l' + 0=l'). eauto.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
        * right; stuck2. rewrite Ldef in H. inv H. eauto.
      + right. stuck.
    - right. stuck.
    - case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      left. eexists (EvtExtern (ExternI f l 0)). eauto using step.
    - left. exists EvtTau. eauto using step.
  Qed.

End I.

Definition foo := 3.

Fixpoint labIndices (symb: list var) (s:nstmt) : status stmt :=
  match s with
    | nstmtLet x e s => sdo s' <- (labIndices symb s); Success (stmtLet x e s')
    | nstmtIf x s1 s2 =>
      sdo s1' <- (labIndices symb s1);
      sdo s2' <- (labIndices symb s2);
      Success (stmtIf x s1' s2')
    | nstmtApp l Y =>
      sdo f <- option2status (pos symb l 0) "labIndices: Undeclared function" ; Success (stmtApp (LabI f) Y)
    | nstmtReturn x => Success (stmtReturn x)
    | nstmtExtern x f Y s =>
      sdo s' <- (labIndices symb s); Success (stmtExtern x f Y s')
    | nstmtFun F s2 =>
      let fl := List.map (fst ∘ fst) F in
      sdo F' <- smap (fun (fZs:var*params*nstmt) => sdo s <- labIndices (fl ++ symb) (snd fZs);
                    Success (snd (fst fZs), s)) F;
      sdo s2' <- labIndices (fl++symb) s2;
      Success (stmtFun F' s2')
  end.

Definition state_result X (s:X*onv val*nstmt) : option val :=
  match s with
    | (_, E, nstmtReturn e) => exp_eval E e
    | _ => None
  end.

Instance statetype_I : StateType I.state := {
  step := I.step;
  result := (@state_result I.labenv);
  step_dec := I.step_dec;
  step_internally_deterministic := I.step_internally_deterministic;
  step_externally_determined := I.step_externally_determined
}.

(*Tactic Notation "goto_invs" tactic(tac) :=
  match goal with
    | [ |- sim (?L, _, nstmtApp ?l ?Y) (_, _, _) ] =>
      let b := fresh "blk" in
      destruct (get_dec L (counted l)) as [[b ?]|];
        [ first [ decide (length (F.block_Z b) = length Y);
                  [ tac | no_step ]
                | decide (length (I.block_Z b) = length Y);
                  [ tac | no_step ] ]
        | no_step; tac; simpl in *; eauto ]
  end.
 *)

Inductive lab_approx : list var -> env (option I.block) -> list IL.I.block -> Prop :=
  Lai symb L L'
    (LEQ: forall f f' Lb F x,
            L f = Some (I.blockI Lb F f')
            -> pos symb f 0 = Some x
            -> (* (exists symb', symb = (List.map (fst ∘ fst) F ++ symb')%list) /\*)
            exists i, lab_approx (drop (length F + i) symb) Lb (drop (length F + i) L')
                   /\ (forall f i' k, pos (drop i symb) f k = Some i' -> Lb f <> None)
                   /\ (exists Z s, get F f' (f, Z, s))
                   /\ (forall f' fb Z s, get F f' (fb,Z,s) ->
                                   exists s', get (drop i L') f' (IL.I.blockI Z s' f')
                                         /\ labIndices (drop i symb) s = Success s'
                                         /\ pos (drop i symb) fb 0 = Some f')
                   /\ x = i + f'
                   /\ exists symb', drop i symb = (List.map (fst ∘ fst) F ++ symb')%list
                     )
  : lab_approx symb L L'.


Definition invRunSeq (r:(env -> stream nat -> Prop) -> stmt -> env -> stream nat -> Prop) :=
  forall f c1 c2 E s, r f (Seq c1 c2) E s -> run r (r f c2) c1 E s.




Inductive labIndicesSim : I.state -> IL.I.state -> Prop :=
  | labIndicesSimI (L:env (option I.block)) L' E s s' symb
    (EQ:labIndices symb s = Success s')
    (LA:lab_approx symb L L')
(*    (LL:forall l b, L (counted l) = Some b -> fst (fst (I.block_F b)) = l) *)
    (EX:forall f i k, pos symb f k = Some i -> L f <> None)
(*    (SM:forall l blk, L l = Some blk -> I.block_f blk < length (I.block_F blk)) *)
  : labIndicesSim (L, E, s) (L', E, s').


Lemma pos_drop_eq symb (l:lab) x
: pos symb l 0 = Some x
  -> drop x symb = l::tl (drop x symb).
Proof.
  general induction symb.
  unfold pos in H; fold pos in H. destruct if in H.
  inv H; inv e; eauto.
  destruct x. exfalso. exploit (pos_ge _ _ _ H); eauto. omega.
  simpl. erewrite IHsymb; eauto.
  eapply (pos_sub 1); eauto.
Qed.

Lemma pos_plus symb (f:lab) n i
: pos symb f 0 = Some (n + i)
  -> pos (drop n symb) f 0 = Some i.
Proof.
  general induction n; simpl; eauto.
  destruct symb; simpl.
  + inv H.
  + eapply IHn; eauto. simpl in H; destruct if in H.
    * inv H.
    * eapply (pos_sub 1); eauto.
Qed.

Lemma labIndicesSim_sim σ1 σ2
  : labIndicesSim σ1 σ2 -> bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; destruct s; simpl in *; try monadS_inv EQ.
  - case_eq (exp_eval E e); intros.
    + one_step. eapply labIndicesSim_sim; econstructor; eauto.
    + no_step.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros; one_step; eapply labIndicesSim_sim; econstructor; eauto.
    no_step.
  - case_eq (L l); intros.
    + destruct b as [Lb Fb fb].
      eapply option2status_inv in EQ0.
      inv LA.
      edestruct LEQ as [i [A [B [[Z [s C]] D]]]]; dcr; eauto.
      edestruct H0; eauto; dcr. subst x.
      decide (length Z = length Y).
      case_eq (omap (exp_eval E) Y); intros.
      one_step. orewrite (l + 0 = l). eauto. simpl. eapply get_drop; eauto.
      simpl. congruence.
      eapply labIndicesSim_sim.
      econstructor; eauto. simpl. orewrite (i + fb - fb = i); eauto.
      * econstructor. simpl; intros; dcr. {
        decide (f ∈ of_list (List.map (fst ∘ fst) Fb)).
        - eapply update_with_list_lookup_in_list in i0. dcr.
          erewrite H10 in H3. clear H10. subst. invc H12. inv_map H9.
          unfold I.mkBlocks, I.mkBlock in H8.
          inv_map H8. inv_mapi H11. get_functional; subst.
          destruct x4 as [[? ?] ?]. unfold comp in *; simpl in *.
          eexists 0. simpl.
          split; eauto. repeat rewrite drop_drop.
          orewrite (length F + 0 + i = length F + i). eauto.
          split; eauto.
          split; eauto.
          split; eauto.
          split.
          intros. exploit H0; eauto. dcr. congruence.
          eauto.
          repeat rewrite map_length.
          unfold I.mkBlocks, I.mkBlock, mapi. rewrite mapi_length; eauto.
        - erewrite (update_with_list_no_update _ _ _ n) in H3; eauto.
          inv A.
          exploit LEQ0; eauto; dcr; clear LEQ0.
          rewrite H1 in H5. rewrite pos_app_not_in in H5.
          rewrite <- drop_drop. rewrite H1.
          assert (length Fb = length (List.map (fst ∘ fst) Fb) + 0).
          rewrite map_length; omega. rewrite H8.
          rewrite drop_app. simpl. instantiate (1:=x + length Fb). admit. eauto.
          eexists (x2 - length Fb). repeat rewrite drop_drop.
          split. rewri
        }
      * intros.
        decide (f ∈ of_list (List.map (fst ∘ fst) Fb)).
        eapply update_with_list_lookup_in_list in i1. dcr.
        erewrite H12. inv_map H10. congruence. repeat rewrite map_length.
        unfold I.mkBlocks, I.mkBlocks, mapi. rewrite mapi_length. reflexivity.
        erewrite (update_with_list_no_update _ _ _ n); eauto.
      * intros. no_step.
      * no_step.
        rewrite Ldef in H. inv H. simpl in *. repeat get_functional; subst. eauto.
        repeat get_functional; subst. eauto.
        edestruct H4; eauto; dcr. simpl in *. eapply get_drop in H7. get_functional; subst.
        simpl in*. congruence.
    + eapply option2status_inv in EQ0. exfalso. eapply EX; eauto.
  - no_step.
  - case_eq (omap (exp_eval E) Y); intros.
    + extern_step.
      * eexists (ExternI f l 0); eexists; try (now (econstructor; eauto)).
      * eexists; split. econstructor; eauto.
        eapply labIndicesSim_sim; econstructor; eauto.
      * eexists; split. econstructor; eauto.
        eapply labIndicesSim_sim; econstructor; eauto.
    + no_step.
  - one_step. eapply labIndicesSim_sim. econstructor; eauto.
    econstructor. intros.
    + decide (f ∈ of_list (List.map (fst ∘ fst) F)).
      * eapply update_with_list_lookup_in_list in i. dcr.
        erewrite H3 in H. subst. invc H5. clear H3.
        inv_map H2. inv_map H1.
        unfold I.mkBlocks, I.mkBlock in *. inv_mapi H4.
        repeat get_functional; subst.
        destruct x4 as [[fb Zb] sb]; unfold comp in *; simpl in *.
        pose proof EQ0 as SM.
        eapply smap_spec in EQ0; eauto. destruct EQ0; eauto; dcr. monadS_inv H3.
        simpl in *.
        assert (length F0 = length ((List.map (fun x1 : var * params * nstmt => fst (fst x1)) F0)) + 0).
        rewrite map_length; eauto.
        assert (length F0 = length (IL.I.mkBlocks x) + 0).
        unfold IL.I.mkBlocks, mapi.
        rewrite mapi_length; eauto. eapply smap_length in SM; eauto. omega.
        eexists 0; split; eauto. simpl.
        { econstructor. intros.
          inv LA. exploit LEQ; eauto; dcr.
          assert (length F0 = length ((List.map (fun x1 : var * params * nstmt => fst (fst x1)) F0))).
          rewrite map_length; eauto.
          assert (length F0 = length (IL.I.mkBlocks x)).
          unfold IL.I.mkBlocks, mapi. rewrite mapi_length; eauto.
          eapply smap_length in SM; eauto.
          eexists (length F0+ x1).
          split. rewrite H11 at 1. rewrite H13. repeat rewrite drop_app; eauto.
          split; eauto. intros. rewrite H11 in H14. rewrite drop_app in H14; eauto.
          split; eauto. split; eauto.
          intros. setoid_rewrite H13 at 1. rewrite drop_app.
          rewrite H11. rewrite drop_app. eauto.
          rewrite H11.
          rewrite pos_app_not_in; eauto.
          rewrite <- H11. orewrite (length F0 + x1 + f'0 = length F0 + (x1 + f'0)).
          eapply pos_add; eauto.

        }*)
        admit.
        split; eauto. simpl. admit.
        split; eauto.
        split; eauto. simpl. intros.
        pose proof (smap_spec _ SM). edestruct H8; eauto; dcr.
        monadS_inv H10; simpl in *. eexists. repeat split; eauto.
        eapply get_app. unfold IL.I.mkBlocks, mapi. admit. admit.
        admit.
        repeat rewrite map_length. unfold I.mkBlocks, mapi.
        rewrite mapi_length; eauto.
      * erewrite (update_with_list_no_update _ _ _ n) in H.
        inv LA. exploit LEQ; eauto; clear LEQ.
        instantiate (1:=x1 - length F). admit.
        exploit smap_length; eauto.
        dcr.
        assert (length (IL.I.mkBlocks x) = length (List.map (fst ∘ fst) F)). {
          rewrite map_length. unfold IL.I.mkBlocks, mapi.
          rewrite mapi_length; eauto.
        }
        eexists (length (IL.I.mkBlocks x) + x2); split; eauto.
        rewrite H5 at 1. repeat rewrite drop_app; eauto.
        split. rewrite H5. rewrite drop_app. eauto.
        split. eauto.
        split. intros. rewrite drop_app. rewrite H5. rewrite drop_app. eauto.
        rewrite H5. rewrite map_length.
        rewrite pos_app_not_in in H0; eauto. eapply pos_ge in H0.
        rewrite map_length in H0. omega.
    + intros.
      decide (f ∈ of_list (List.map (fst ∘ fst) F)).
      * pose proof (pos_app_in k _ symb i0); eauto. erewrite H0 in H. clear H0.
        eapply update_with_list_lookup_in_list in i0. dcr.
        erewrite H2. invc H4. inv_map H0. congruence.
        repeat rewrite map_length. unfold I.mkBlocks, mapi. rewrite mapi_length; eauto.
      * erewrite (update_with_list_no_update _ _ _ n).
        pose proof (pos_app_not_in k _ symb n); eauto. erewrite H0 in H. clear H0.
        eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
