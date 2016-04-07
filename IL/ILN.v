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
        * decide (l = l'); subst.
          decide (length Z = length Y).
          case_eq (omap (exp_eval V) Y); intros; try now (right; stuck2).
          left. eexists EvtTau. econstructor. econstructor; eauto.
          orewrite (l' + 0=l'). eauto.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
        * right; stuck2. rewrite Ldef in H. inv H. eauto.
      + right. stuck.
    - right. stuck.
    - case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      left. eexists (EvtExtern (ExternI f l default_val)). eauto using step.
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
        * decide (l = l').
          decide (length Z = length Y).
          case_eq (omap (exp_eval V) Y); intros;[| now (right; stuck2)].
          left. eexists EvtTau. econstructor. econstructor; eauto.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
        * right; stuck2. rewrite Ldef in H. inv H. eauto.
      + right. stuck.
    - right. stuck.
    - case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      left. eexists (EvtExtern (ExternI f l default_val)). eauto using step.
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


Lemma pos_drop_eq symb (l:lab) x
: pos symb l 0 = Some x
  -> drop x symb = l::tl (drop x symb).
Proof.
  general induction symb.
  unfold pos in H; fold pos in H. cases in H.
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
  + eapply IHn; eauto. simpl in H; cases in H.
    * inv H.
    * eapply (pos_sub 1); eauto.
Qed.

Require Import InRel Sawtooth.

Lemma mkBlocks_I_less
      : forall F' L F (n k : nat) (b : I.block),
          get (mapi_impl (I.mkBlock L F') k F) n b -> I.block_f b <= k + length F - 1.
Proof.
  intros. general induction F; simpl in *.
  - inv H; simpl in *; try omega.
  - inv H; simpl in *; try omega.
    eapply IHF in H4; eauto. omega.
Qed.

Instance block_type_I : BlockType (I.block) := {
  block_n := I.block_f
                                              }.

Inductive lab_approx : list var -> list IL.I.block -> list I.block -> Prop :=
  Lai symb L' LB
    (LEQ: forall f f' Lb F i,
            get LB i (I.blockI Lb F f')
            -> get symb i f
            -> (*lab_approx (drop (i-f') symb) (drop (i-f') L')  (drop (i-f') LB)
              /\ *) (forall f blk, Lb f = Some blk -> f ∉ of_list (List.map (fst ∘ fst) F)
                          -> exists j, pos (drop (i - f') symb) f 0 = Some j /\
                                 get (drop (i - f') LB) j blk)
              /\ (forall f i' k, pos (drop (i-f' + length F) symb) f k = Some i' -> exists blk, Lb f = Some blk)
              /\ (exists Z s, get F f' (f, Z, s))
              /\ (forall fn fb Z s, get F fn (fb,Z,s) ->
                              (forall b n, n < fn -> get F n b -> fst (fst b) <> fb) ->
                              exists s', get (drop (i-f') L') fn
                                        (IL.I.blockI Z s' fn)
                                    /\ labIndices (drop (i-f') symb) s
                                      = Success s'
                                    /\ pos (drop (i-f') symb) fb 0 = Some fn)
              /\ (exists symb', drop (i-f') symb
                          = (List.map (fst ∘ fst) F ++ symb')%list)
              /\ (exists LB', drop (i-f') LB
                          = (I.mkBlocks Lb F ++ LB')%list)
              /\ i >= f'

    )
    (ST:sawtooth LB)
 : lab_approx symb L' LB.

Lemma lab_approx_drop symb L' LB
: forall f f' Lb F i,
    get LB i (I.blockI Lb F f')
    -> get symb i f
    -> i >= f'
    -> lab_approx symb L' LB
    -> lab_approx (drop (i -f') symb) (drop (i -f') L') (drop (i -f') LB).
Proof.
  intros.
  econstructor; intros. repeat rewrite drop_drop.
  eapply get_drop in H3.
  eapply get_drop in H4.
  inv H2; exploit LEQ; eauto; dcr; clear LEQ.
  exploit (sawtooth_resetting ST _ H H3); eauto. simpl in *.
  orewrite (i0 - f'0 + (i - f') = (i - f') + i0 - f'0).
  split; eauto. split; eauto.
  orewrite (i0 - f'0 + length F0 + (i - f') = i - f' + i0 - f'0 + length F0). eauto.
  split; eauto.
  split; eauto.
  inv H2; clear LEQ.
  eapply sawtooth_drop in H; eauto.
Qed.



Inductive labIndicesSim : I.state -> IL.I.state -> Prop :=
  | labIndicesSimI (L:env (option I.block)) L' E s s' symb LB
    (EQ:labIndices symb s = Success s')
    (LA:lab_approx symb L' LB)
(*    (LL:forall l b, L (counted l) = Some b -> fst (fst (I.block_F b)) = l) *)
    (EX:forall f i k, pos symb f k = Some i -> exists blk, L f = Some blk)
    (*    (SM:forall l blk, L l = Some blk -> I.block_f blk < length (I.block_F blk)) *)
    (BL:forall f blk, L f = Some blk -> exists j, pos symb f 0 = Some j /\
                                        get LB j blk)
    : labIndicesSim (L, E, s) (L', E, s').

Lemma length_mkBlocks_1 X (L:list X) L' Lb
: length L = length L'
  -> length (I.mkBlocks Lb L') = length L.
Proof.
  intros. unfold I.mkBlocks, mapi. rewrite mapi_length; eauto.
Qed.

Lemma length_mkBlocks_2 X (L:list X) L' Lb
: length L = length L'
  -> length L = length (I.mkBlocks Lb L').
Proof.
  intros. unfold I.mkBlocks, mapi. rewrite mapi_length; eauto.
Qed.

Hint Resolve length_mkBlocks_1 length_mkBlocks_2 : len.

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
  - eapply option2status_inv in EQ0.
    edestruct EX as [[Lb F f]]; eauto.
    edestruct BL as [i [A B]]; eauto.
    inv LA. edestruct (pos_get_first _ _ _ EQ0); dcr; eauto. symmetry in H3; invc H3.
    assert (x = i) by congruence; subst; clear_dup.
    orewrite (i - 0 = i) in H1.
    edestruct LEQ as [C2 [C3 [[Z [s C4]] [C5 [C6 [C7 C8]]]]]]; eauto.
    decide (length Z = length Y).
    case_eq (omap (exp_eval E) Y); intros.
    edestruct C5 as [s' [D1 [D2 D3]]]; eauto.
    {
      edestruct C6.
      intros. eapply H5. instantiate (1:=i - f + n). omega.
      eapply get_drop. rewrite H3.
      eapply get_app. eapply (map_get_1 (fst ∘ fst) H6).
    }
    + one_step. orewrite (l + 0 = l). eauto. simpl.
      eapply get_drop in D1; eauto.
      orewrite (i - f + f = i) in D1. eauto.
      simpl. congruence.
      eapply labIndicesSim_sim.
      econstructor; eauto. simpl.
      * eapply lab_approx_drop; eauto.
      * intros.
        decide (f0 ∈ of_list (List.map (fst ∘ fst) F)).
        eapply update_with_list_lookup_in_list in i1. dcr.
        erewrite H7. simpl in *. inv_map H4. eauto. eauto with len.
        erewrite (update_with_list_no_update _ _ _ n); eauto.
        destruct C6. rewrite H4 in H3.
        rewrite pos_app_not_in in H3.
        eapply C3. rewrite Plus.plus_comm. rewrite <- drop_drop. rewrite H4.
        erewrite <- map_length. erewrite drop_length_eq. eauto. eauto.
      * intros. destruct C6; subst. rewrite H4.
        decide (f0 ∈ of_list (List.map (fst ∘ fst) F)).
        edestruct (of_list_get_first _ i0) as [n]; eauto. dcr. hnf in H7. subst x0.
        rewrite pos_app_in; eauto.
        pose proof H8.
        eapply update_with_list_lookup_in_list_first in H8; dcr.
        erewrite H12 in H3. subst x0.
        eexists; split. eapply get_first_pos; eauto.
        rewrite H6. eapply get_app.
        inv_map H11; eauto.
        eauto with len.
        eauto.
        erewrite (update_with_list_no_update _ _ _ n) in H3; eauto.
        edestruct C2; eauto; dcr.
        rewrite H4 in H7. eexists; eauto.
    +  intros. no_step.
    +  no_step.
       rewrite Ldef in H. inv H. simpl in *. repeat get_functional; subst. eauto.
       repeat get_functional; subst. eauto.
       edestruct C5; eauto; dcr. simpl in *.
       intros. eapply H5. instantiate (1:=i - f + n0). omega.
       eapply get_drop. rewrite H3.
       eapply get_app. eapply (map_get_1 (fst ∘ fst) H6).
       eapply get_drop in H3. orewrite (i - f + f = i) in H3.
       get_functional; subst. simpl in *. congruence.
  - no_step.
  - case_eq (omap (exp_eval E) Y); intros.
    + extern_step.
      * eexists (ExternI f l default_val); eexists; try (now (econstructor; eauto)).
      * eexists; split. econstructor; eauto.
        eapply labIndicesSim_sim; econstructor; eauto.
      * eexists; split. econstructor; eauto.
        eapply labIndicesSim_sim; econstructor; eauto.
    + no_step.
  - one_step. eapply labIndicesSim_sim. econstructor; eauto.
    instantiate (1:=(I.mkBlocks L F++LB)%list).
    econstructor. intros.
    eapply get_app_cases in H. destruct H.
    * {
        unfold I.mkBlocks in H. inv_mapi H.
        exploit @get_length; eauto. unfold mapi in H2. rewrite mapi_length in H2.
        eapply get_in_range_app in H0.
        orewrite (f' - f' = 0); simpl.
        split.
        - intros. edestruct BL; eauto; dcr.
          eexists (length F0 + x2); split.
          rewrite pos_app_not_in; eauto.
          rewrite map_length. eapply pos_add; eauto.
          eapply get_app_right.
          unfold I.mkBlocks, mapi. rewrite mapi_length. reflexivity. eauto.
        - split. intros. erewrite <- map_length in H3.
          rewrite drop_length_eq in H3.
          eapply EX; eauto.
          split; eauto. destruct x1 as [[? ?] ?].
          inv_map H0; unfold comp in *; simpl in *.
          do 2 eexists; eauto.
          split; eauto.
          intros. eapply smap_spec in EQ0; eauto; dcr. destruct EQ0; dcr.
          monadS_inv H6. simpl in *. eexists. repeat split; eauto.
          unfold IL.I.mkBlocks. eapply get_app.
          intros.
          eapply (mapi_get_1 0 (IL.I.mkBlock)) in H7. eauto.
          assert (get (List.map (fst ∘ fst) F0) fn fb).
          eapply (map_get_1 (fst ∘ fst) H3).
          rewrite pos_app_in.
          eapply get_first_pos; eauto.
          intros. inv_map H8. eapply H4; eauto.
          eapply get_in_of_list; eauto.
          split; eauto.
        - rewrite map_length; eauto.
      }
    * dcr.
      assert (length (List.map (fst ∘ fst) F) = length (I.mkBlocks L F)) by eauto with len.
      assert (length F = length (I.mkBlocks L F)) by eauto with len.
      orewrite (i =  length (List.map (fst ∘ fst) F) + (i -  length (I.mkBlocks L F))) in H0.
      eapply shift_get in H0.
      inv LA; exploit LEQ; eauto; dcr; clear LEQ.
      orewrite (i - f' = i - length (I.mkBlocks L F) - f' + length (I.mkBlocks L F)).
      split.
      repeat rewrite <- drop_drop. repeat rewrite drop_length_eq.
      Typeclasses eauto := 5.
      setoid_rewrite <- H at 2. rewrite drop_length_eq. eauto.
      split; eauto.
      orewrite (i - length (I.mkBlocks L F) - f' + length (I.mkBlocks L F) +
         length F0 = i - length (I.mkBlocks L F) - f' +
                     length F0 + length (I.mkBlocks L F)).
      setoid_rewrite <- H at 2.
      rewrite <- drop_drop. rewrite drop_length_eq. eauto.
      split; eauto.
      split; eauto.
      rewrite <- drop_drop.
      assert (length (I.mkBlocks L F) = length (IL.I.mkBlocks x)).
      eapply smap_length in EQ0.
      unfold I.mkBlocks. unfold IL.I.mkBlocks. unfold mapi.
      repeat rewrite mapi_length. congruence.
      setoid_rewrite H4 at 2. rewrite drop_length_eq.
      setoid_rewrite <- H at 3. rewrite <- drop_drop. rewrite drop_length_eq.
      setoid_rewrite <- H at 4. rewrite <- drop_drop. rewrite drop_length_eq. eauto.
      split; eauto.
      setoid_rewrite <- H at 2. rewrite <- drop_drop. rewrite drop_length_eq. eauto.
      split; eauto.
      rewrite <- drop_drop. rewrite drop_length_eq. eauto.
      omega.
    * { inv LA. revert ST. clear_all.
        intros. econstructor; eauto.
        unfold I.mkBlocks, mapi.
        generalize 0. generalize F at 1.
        general induction F; simpl; eauto.
        econstructor.
        econstructor. eapply IHF. econstructor; simpl. reflexivity.
      }
    * {
        intros.
        decide (f ∈ of_list (List.map (fst ∘ fst) F)).
        - eapply update_with_list_lookup_in_list in i0. dcr.
          rewrite H2. simpl in *. inv_map H0. eauto.
          eauto with len.
        -  erewrite (update_with_list_no_update _ _ _ n); eauto.
           rewrite pos_app_not_in in H; eauto.
      }
    * { intros.
        decide (f ∈ of_list (List.map (fst ∘ fst) F)).
        - edestruct (of_list_get_first _ i) as [n]; eauto. dcr. hnf in H1. subst x1.
          rewrite pos_app_in; eauto.
          pose proof H2.
          eapply update_with_list_lookup_in_list_first in H0; dcr.
          erewrite H5 in H. subst x1.
          erewrite get_first_pos; eauto.
          eexists; split; eauto.
          inv_map H3. eapply get_app; eauto.
          eauto with len.
          eauto.
        - erewrite update_with_list_no_update in H; eauto.
          edestruct BL; eauto; dcr.
          eexists; split; eauto using get_shift.
          repeat rewrite pos_app_not_in; eauto.
          assert (length (List.map (fst ∘ fst) F) = length (I.mkBlocks L F))
                 by eauto with len.
          rewrite H0. eapply pos_add; eauto.
      }
Qed.
