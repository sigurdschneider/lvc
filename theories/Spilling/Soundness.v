Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI Spilling DoSpill.

Set Implicit Arguments.


Definition discard_sl := mapAnn (fun (a : (* = mapAnn ? snd *)
      set var * set var * option (list (set var * set var)))
                                           => match a with (_,_,rm) => rm end).




Definition slot_merge slot := List.map (fun (RM : set var * set var)
                                           => fst RM ∪ map slot (snd RM)).

Definition discard_merge_sl (slot : var -> var) :=
mapAnn (fun (a : set var * set var * option (list (set var * set var)))
         => match a with
            | (_,_,None)
              => None
            | (_,_,Some rms)
              => Some (slot_merge slot rms)
           end).


Lemma discard_merge_sl_step
      (slot : var -> var)
      (sl : ann (set var * set var * option (list (set var * set var))))
  :
    discard_merge_sl slot sl =
    match sl with
    | ann0 (_,_,None)
      => ann0 None
    | ann1 (_,_,None) sl1
      => ann1 None (discard_merge_sl slot sl1)
    | ann2 (Sp,L,None) sl1 sl2
      => ann2 None (discard_merge_sl slot sl1)
                   (discard_merge_sl slot sl2)
    | annF (_,_,None) F sl2
      => annF None (discard_merge_sl slot ⊝ F)
                   (discard_merge_sl slot sl2)
    | ann0 (_,_,Some rm)
      => ann0 (Some (slot_merge slot rm))
    | ann1 (_,_,Some rm) sl1
      => ann1 (Some (slot_merge slot rm)) (discard_merge_sl slot sl1)
    | ann2 (_,_,Some rm) sl1 sl2
      => ann2 (Some (slot_merge slot rm)) (discard_merge_sl slot sl1)
                   (discard_merge_sl slot sl2)
    | annF (_,_,Some rm) F sl2
      => annF (Some (slot_merge slot rm)) (discard_merge_sl slot ⊝ F)
                   (discard_merge_sl slot sl2)
    end.
Proof.
  induction sl; destruct a as [spl rm]; induction rm;
    unfold discard_merge_sl; fold discard_merge_sl; simpl; destruct spl;
      reflexivity.
Qed.


(*
Fixpoint do_spill_rm
(slot : var -> var)
(sl0: ann (set var * set var * option (list (set var * set var ))))
{struct sl0}
: ann (set var * set var * option (list (set var * set var)))
  :=
    let Sp0 := fst (fst (getAnn sl0)) in
    let L0  := snd (fst (getAnn sl0)) in
    (fix f sl n {struct n} :=
      let Sp := fst (fst (getAnn sl)) in
      let L  := snd (fst (getAnn sl)) in
      let rm := snd (getAnn sl) in
      match n with
      | 0 =>
        match sl0 with
        | ann0 (Sp,L,rm)
          => sl
        | ann1 (Sp,L,rm) sl_s
          => ann1 (Sp,L,rm) (do_spill_rm slot sl_s)
        | ann2 (Sp,L,rm) sl_s sl_t
          => ann2 (Sp,L,rm) (do_spill_rm slot sl_s)
                            (do_spill_rm slot sl_t)
        | annF (Sp,L,rm) sl_F sl_t
          => annF (Sp,L,rm) (do_spill_rm slot ⊝ sl_F)
                            (do_spill_rm slot    sl_t)
        end
      | S n =>
        if [cardinal Sp = 0]
        then
          if [cardinal L = 0]
          then
            match sl0 with
            | ann0 (Sp,L,rm)
              => sl
            | ann1 (Sp,L,rm) sl_s
              => ann1 (Sp,L,rm) (do_spill_rm slot sl_s)
            | ann2 (Sp,L,rm) sl_s sl_t
              => ann2 (Sp,L,rm) (do_spill_rm slot sl_s)
                                (do_spill_rm slot sl_t)
            | annF (Sp,L,rm) sl_F sl_t
              => annF (Sp,L,rm) (do_spill_rm slot ⊝ sl_F)
                                (do_spill_rm slot    sl_t)
            end
          else
            let L' := of_list (tl (elements L)) in
            ann1 (∅,∅,None) (f (setTopAnn sl (Sp,L',rm)) n)
        else
          let Sp' := of_list (tl (elements Sp)) in
          ann1 (∅,∅,None) (f (setTopAnn sl (Sp',L,rm)) n)
      end
    ) sl0 (cardinal Sp0 + cardinal L0)
.

*)
(*
Fixpoint do_spill_rm'
(slot : var -> var)
(sl: ann (set var * set var * option (list (set var * set var ))))
{struct sl}
: ann (set var * set var * option (list (set var * set var)))
  :=
    let Sp := fst (fst (getAnn sl)) in
    let L  := snd (fst (getAnn sl)) in
    (fix f n {struct n} :=
      match n with
      | 0 =>
        match sl with
        | ann0 _
          => sl
        | ann1 a sl_s
          => ann1 a (do_spill_rm' slot sl_s)
        | ann2 a sl_s sl_t
          => ann2 a (do_spill_rm' slot sl_s)
                    (do_spill_rm' slot sl_t)
        | annF a sl_F sl_t
          => annF a (do_spill_rm' slot ⊝ sl_F)
                    (do_spill_rm' slot   sl_t)
        end
      | S n =>
        if [cardinal Sp + cardinal L = 0]
        then
          match sl with
          | ann0 a
            => sl
          | ann1 a sl_s
            => ann1 a (do_spill_rm' slot sl_s)
          | ann2 a sl_s sl_t
            => ann2 a (do_spill_rm' slot sl_s)
                      (do_spill_rm' slot sl_t)
          | annF a sl_F sl_t
            => annF a (do_spill_rm' slot ⊝ sl_F)
                      (do_spill_rm' slot    sl_t)
          end
        else
          ann1 (∅,∅,None) (f n)
      end
    ) (cardinal Sp + cardinal L)
.
*)
Function count
         (sl : ann (set var * set var * option (list (set var * set var))))
  := cardinal (fst (fst (getAnn sl))) + cardinal (snd (fst (getAnn sl))).

Fixpoint do_spill_rm'
         (slot : var -> var)
         (n : nat)
         (sl: ann (set var * set var * option (list (set var * set var ))))
         {struct sl}
  : ann (set var * set var * option (list (set var * set var)))
  :=
    let rm := snd (getAnn sl) in
    (fix add_nones n
        :=
    match n with
    | 0 =>
        match sl with
        | ann0 a => sl
        | ann1 a sl_s
          => ann1 a (do_spill_rm' slot (count sl_s) sl_s)
        | ann2 a sl_s sl_t
          => ann2 a (do_spill_rm' slot (count sl_s) sl_s)
                    (do_spill_rm' slot (count sl_t) sl_t)
        | annF a sl_F sl_t
          => annF a ((fun sl_s => do_spill_rm' slot (count sl_s) sl_s) ⊝ sl_F)
                    (do_spill_rm' slot (count   sl_t) sl_t)
        end
    | S n =>
        ann1 (∅,∅,None) (add_nones n)
    end) n
.



Definition do_spill_rm
           (slot : var -> var)
           (sl : ann (set var * set var * option (list (set var * set var))))
  := do_spill_rm' slot (count sl) sl.



Lemma do_spill_rm_s
      (slot : var -> var)
      (sl : ann (set var * set var * option (list (set var * set var))))
      (n : nat)
  :
    do_spill_rm' slot (S n) sl
    = ann1 (∅,∅,None) (do_spill_rm' slot n sl)
.
Proof.
  unfold do_spill_rm' at 1.
  destruct sl;
    simpl;
    reflexivity.
Qed.


Fixpoint spill_live
(Lv : list (set var))
(ZL : list (params))
(G : set var)
(s : stmt)
(rm : ann (option (list (set var))))
{struct s}
: ann (set var)
:=
match s, rm with
| stmtLet x e t, ann1 _ rm  (* checked *)
     => let lv_t := spill_live Lv ZL (singleton x) t rm in
        ann1 ((getAnn lv_t) \ singleton x ∪ Exp.freeVars e ∪ G) lv_t

| stmtReturn e, ann0 _ (* checked *)
     => ann0 (Op.freeVars e ∪ G)

| stmtIf e t v, ann2 _ rm_t rm_v (* checked *)
     => let lv_t := spill_live Lv ZL ∅ t rm_t in
        let lv_v := spill_live Lv ZL ∅ v rm_v in
        ann2 (getAnn lv_t ∪ getAnn lv_v ∪ Op.freeVars e ∪ G) lv_t lv_v

| stmtApp f Y, ann0 _ (* checked *)
     => let blv := nth (counted f) Lv ∅ in
        let Z   := nth (counted f) ZL nil in
        (* attention: (forall (n : nat) (y : op), get Y n y -> live_op_sound y lv) *)
        ann0 (blv \ of_list Z ∪ G)

| stmtFun F t, annF (Some Lv') rm_F rm_t (* checked *)
     => let lv_t := spill_live (Lv' ++ Lv) (fst ⊝ F ++ ZL) ∅ t rm_t in
        let lv_F := (fun ps rm_s
                 => spill_live (Lv' ++ Lv) (fst ⊝ F ++ ZL) ∅
                               (snd ps) rm_s) ⊜ F rm_F in
        (* maybe i will need a guarantee of ❬F❭ = ❬als❭ somewhere *)
        annF (getAnn lv_t ∪ G) lv_F lv_t

| _,_ => ann0 G

end.


Lemma spill_live_G
      (Lv : list (set var))
      (ZL : list (params))
      (x : var)
      (s : stmt)
      (a : ann (option (list (set var))))
  :
    x ∈ getAnn (spill_live Lv ZL (singleton x) s a).
Proof.
  induction s,a ; simpl; eauto with cset.
  - destruct a; simpl; eauto.
    cset_tac.
Qed.



(* move somewhere *)
Lemma setTopAnn_setTopAnn
      (X : Type)
      (x x' : X)
      (a : ann X)
  :
    setTopAnn (setTopAnn a x') x = setTopAnn a x.
Proof.
  induction a; simpl; eauto.
Qed.


(* TODO: move to DoSpill.v *)
Lemma do_spill_empty_invariant
      (slot : var -> var)
      (s : stmt)
      (Sp' L' : set var)
      (rm : option ( list (set var * set var)))
      (sl sl' : ann (set var * set var * option ( list (set var * set var))))
  :
    sl' = setTopAnn sl (Sp',L',rm)
    -> Empty (fst (fst (getAnn sl)))
    -> Empty (snd (fst (getAnn sl)))
    -> Empty Sp'
    -> Empty L'
    -> do_spill slot s sl = do_spill slot s sl'
.
Proof.
  intros top_sl' Empty_Sp Empty_L Empty_Sp' Empty_L'.
  rewrite top_sl'.
  rewrite do_spill_empty;
    try rewrite getAnn_setTopAnn; eauto.
  rewrite do_spill_empty;
    try rewrite getAnn_setTopAnn; eauto.
  unfold setTopAnn.
  induction sl; simpl; reflexivity.
Qed.
(*
Lemma dms_dsr_empty_invariant
      (slot : var -> var)
      (n n': nat)
      (Sp' L' : set var)
      (rm : option (list (set var * set var)))
      (sl sl' : ann (set var * set var * option (list (set var * set var))))
:
  sl' = setTopAnn sl (Sp',L',snd (getAnn sl))
  -> Empty (fst (fst (getAnn sl)))
  -> Empty (snd (fst (getAnn sl)))
  -> Empty Sp'
  -> Empty L'
  -> discard_merge_sl slot (do_spill_rm' slot n  sl)
   = discard_merge_sl slot (do_spill_rm' slot n' sl')
.
Proof.
  intros top_sl' Empty_Sp Empty_L Empty_Sp' Empty_L'.
  rewrite top_sl'.
  rewrite do_spill_rm_empty;
    try rewrite getAnn_setTopAnn; eauto.
  rewrite do_spill_rm_empty;
    try rewrite getAnn_setTopAnn; eauto.
  unfold setTopAnn.
  do 2 rewrite discard_merge_sl_step.
  induction sl; simpl; destruct a; destruct p;
    simpl; reflexivity.
Qed.
*)
Definition sub_spill
           (sl' sl : ann (set var * set var * option (list (set var * set var))))
  :=
    sl' = setTopAnn sl (getAnn sl') (*Note that rm=rm' *)
    /\ fst (fst (getAnn sl')) ⊆ fst (fst (getAnn sl))
    /\ snd (fst (getAnn sl')) ⊆ snd (fst (getAnn sl))
    /\ snd (getAnn sl') = snd (getAnn sl)
.


Lemma do_spill_rm_zero
      (slot : var -> var)
      (sl : ann (set var * set var * option (list (set var * set var))))
  :
    do_spill_rm' slot 0 sl
    = match sl with
       | ann0 (Sp, L, rm) => ann0 (Sp, L, rm)
       | ann1 (Sp, L, rm) sl_s => ann1 (Sp, L, rm) (do_spill_rm slot sl_s)
       | ann2 (Sp, L, rm) sl_s sl_t =>
           ann2 (Sp, L, rm) (do_spill_rm slot sl_s) (do_spill_rm slot sl_t)
       | annF (Sp, L, rm) sl_F sl_t =>
           annF (Sp, L, rm) (do_spill_rm slot ⊝ sl_F) (do_spill_rm slot sl_t)
       end
.
Proof.
  unfold do_spill_rm'.
  induction sl; fold do_spill_rm';
    destruct a;
    destruct p;
    reflexivity.
Qed.


Lemma tl_list_incl
      (X : Type) `{OrderedType X}
      (L : list X)
  :
    of_list (tl L) ⊆ of_list L
.
Proof.
  general induction L; simpl; eauto with cset.
Qed.


Lemma tl_set_incl
      (X : Type) `{OrderedType X}
      (s : set X)
  :
    of_list (tl (elements s)) ⊆ s
.
Proof.
  rewrite tl_list_incl.
  hnf. intros. eapply elements_iff. cset_tac.
Qed.





Lemma count_reduce_L
      (sl : ann (set var * set var * option (list (set var * set var))))
      (n m : nat)
  :
    count sl = S n
    -> cardinal (snd (fst (getAnn sl))) = S m
    -> count (setTopAnn sl (fst (fst (getAnn sl)),
                           of_list (tl (elements (snd (fst (getAnn sl))))),
                           snd (getAnn sl)))
      = n
.
Proof.
  intros count_sl card_L.
  unfold count in *.
  rewrite getAnn_setTopAnn.
  simpl.
  rewrite cardinal_set_tl with (n:=m).
  - omega.
  - rewrite of_list_elements. assumption.
Qed.





Lemma count_reduce_Sp
      (sl : ann (set var * set var * option (list (set var * set var))))
      (n m : nat)
  :
    count sl = S n
    -> cardinal (fst (fst (getAnn sl))) = S m
    -> count (setTopAnn sl (of_list (tl (elements (fst (fst (getAnn sl))))),
                           snd (fst (getAnn sl)),
                           snd (getAnn sl)))
      = n
.
Proof.
  intros count_sl card_Sp.
  unfold count in *.
  rewrite getAnn_setTopAnn.
  simpl.
  rewrite cardinal_set_tl with (n:=m).
  - omega.
  - rewrite of_list_elements. assumption.
Qed.



Lemma spill_live_sound_s
      (slot : var -> var)
      (n : nat)
      (ZL : list params)
      (G : set var)
      (Λ : list (set var * set var))
      (Lv : list (set var))
      (s : stmt)
      (sl sl': ann (set var * set var * option (list (set var * set var))))
  :
    sub_spill sl' sl
    -> n = count sl'
    -> let sl0 := setTopAnn sl (∅,∅,snd (getAnn sl)) in
   (forall G', live_sound Imperative ZL Lv
              (do_spill slot s sl0)
              (spill_live (slot_merge slot Λ) ZL G'
                          (do_spill slot s sl0)
                          (discard_merge_sl slot (do_spill_rm' slot 0 sl))))
-> live_sound Imperative ZL Lv
              (do_spill slot s sl')
              (spill_live (slot_merge slot Λ) ZL G
                          (do_spill slot s sl')
                          (discard_merge_sl slot (do_spill_rm' slot n sl))).
Proof.

set (Sp' := fst (fst (getAnn sl'))).
set (L'  := snd (fst (getAnn sl'))).
set (rm' := snd (getAnn sl')).
intros sub_sl n_count sl0 strong_sls.

remember (cardinal Sp') as n_Sp'.
symmetry in Heqn_Sp'.
rename Heqn_Sp' into card_Sp'.
revert dependent sl'.
revert G.
revert n.
induction n_Sp';
  intros n G sl' Sp' L' rm' sub_sl n_count card_Sp'.

- remember (cardinal L') as n_L'.
  symmetry in Heqn_L'.
  rename Heqn_L' into card_L'.
  revert dependent sl'.
  revert G.
  revert n.
  induction n_L';
    intros n G sl' Sp' L' rm' sub_sl n_count card_Sp' card_L'.

  {
    assert (count sl' = 0) as count_sl'.
    { unfold count. subst Sp'. subst L'.
      rewrite card_Sp'. rewrite card_L'. omega. }
    rewrite do_spill_empty_invariant
    with (Sp':=∅) (L':=∅) (rm:=rm') (sl':=sl0);
      simpl; eauto; try apply empty_1;
      try apply cardinal_Empty; eauto.

    + rewrite n_count.
      rewrite count_sl'.
      rewrite do_spill_rm_zero.
      destruct sl; destruct a; destruct p; apply strong_sls.
    + subst sl0.
      unfold sub_spill in sub_sl.
      destruct  sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
      rewrite <- eq_rm.
      rewrite top_sl'.
      rewrite setTopAnn_setTopAnn.
      rewrite getAnn_setTopAnn.
      subst rm'.
      reflexivity.
  }


  rewrite do_spill_L.
  Focus 2. rewrite cardinal_Empty. subst Sp'. assumption.
  Focus 2. clear - card_L'. intro N.
           apply cardinal_Empty in N. subst L'. omega.

  rewrite n_count.
  unfold count.
  subst Sp'.
  subst L'.
  rewrite card_L'.
  rewrite card_Sp'.
  simpl.

  rewrite do_spill_rm_s.

  rewrite discard_merge_sl_step.

  constructor; fold spill_live.

  * apply IHn_L'.
    -- unfold sub_spill.
       unfold sub_spill in sub_sl.
       destruct sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
       repeat split; rewrite getAnn_setTopAnn; simpl; eauto.
       ++ rewrite top_sl'. rewrite setTopAnn_setTopAnn.
          rewrite getAnn_setTopAnn. reflexivity.
       ++ rewrite tl_set_incl. assumption.

    -- rewrite count_reduce_L with (n:=n_L') (m:=n_L'); eauto.
       unfold count. rewrite card_Sp'. rewrite card_L'. eauto.
    -- rewrite getAnn_setTopAnn.
       simpl.
       assumption.
    -- rewrite getAnn_setTopAnn.
       simpl. erewrite cardinal_set_tl. eauto.
       rewrite of_list_elements. rewrite card_L'. eauto.
    * apply live_exp_sound_incl
        with (lv':=Exp.freeVars (Operation (Var (slot
                         (hd 0 (elements (snd (fst (getAnn sl'))))))))).
      -- apply live_freeVars.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G.

- rewrite do_spill_Sp.
  Focus 2. subst Sp'. clear - card_Sp'. intro N.
           apply cardinal_Empty in N. omega.

  rewrite n_count.
  unfold count.
  subst Sp'.
  rewrite card_Sp'.
  simpl.


  rewrite do_spill_rm_s with (n:=n_Sp' + cardinal L').

  econstructor; fold spill_live.
  * apply IHn_Sp'.
    -- unfold sub_spill.
       unfold sub_spill in sub_sl.
       destruct sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
       repeat split; rewrite getAnn_setTopAnn; simpl; eauto.
       ++ rewrite top_sl'. rewrite setTopAnn_setTopAnn.
          rewrite getAnn_setTopAnn. reflexivity.
       ++ rewrite tl_set_incl. assumption.
    -- rewrite count_reduce_Sp with (n:=n_Sp' + cardinal L') (m:=n_Sp'); eauto.
       unfold count. rewrite card_Sp'. subst L'. omega.
    -- rewrite getAnn_setTopAnn.
       simpl.
       erewrite cardinal_set_tl; eauto.
       rewrite of_list_elements.
       rewrite card_Sp'.
       omega.
     * apply live_exp_sound_incl
        with (lv':= singleton (hd 0 (elements (fst (fst (getAnn sl')))))).
      -- econstructor. econstructor. eauto with cset.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G.
Qed.


Lemma sub_spill_refl sl
  :
    sub_spill sl sl
.
Proof.
  unfold sub_spill.
  repeat split.
    simpl; eauto.
  - unfold setTopAnn.
    destruct sl; destruct a; destruct p;
      simpl; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma spill_live_sound
(k : nat)
(slot : var -> var)
(n : nat)
(ZL : list params)
(G : set var)
(Λ : list (set var * set var))
(R M : set var)
(Lv : list (set var))
(s : stmt)
(sl : ann (set var * set var * option (list (set var * set var))))
(alv : ann (set var))
:  app_expfree s
-> spill_sound k ZL Λ (R,M) s sl
-> live_sound Imperative ZL Lv s alv
-> live_sound Imperative ZL Lv
              (do_spill slot s sl)
              (spill_live (slot_merge slot Λ) ZL G
                          (do_spill slot s sl)
                          (discard_merge_sl slot (do_spill_rm slot sl))).

Proof.
intros aeFree spillSound lvSound.

general induction lvSound;
  inversion_clear aeFree;
  inversion_clear spillSound;
  apply spill_live_sound_s;
  try apply sub_spill_refl; eauto.
- rewrite do_spill_empty.
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.
  Focus 2. simpl. apply empty_1.
  Focus 2. simpl. apply empty_1.

  econstructor.
  + eapply IHlvSound; eauto.
  + apply live_exp_sound_incl with (lv':=Exp.freeVars e).
    * apply Exp.live_freeVars.
    * clear. cset_tac.
  +  clear. cset_tac.
  + apply spill_live_G.
- rewrite do_spill_empty.
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.
  Focus 2. simpl. apply empty_1.
  Focus 2. simpl. apply empty_1.

  econstructor.
  + eapply IHlvSound1; eauto.
  + eapply IHlvSound2; eauto.
  + apply live_op_sound_incl with (lv':=Op.freeVars e).
    * apply Op.live_freeVars.
    * clear. cset_tac.
  + clear. cset_tac.
  + clear. cset_tac.
- admit.
- rewrite do_spill_empty.
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.
  Focus 2. simpl. apply empty_1.
  Focus 2. simpl. apply empty_1.

  econstructor.
  + apply live_op_sound_incl with (lv':=Op.freeVars e).
    * apply Op.live_freeVars.
    * clear. cset_tac.
- admit.

Admitted.
