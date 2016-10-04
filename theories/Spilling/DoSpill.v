Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import Spilling SpillUtil.


Fixpoint slot_lift_params
           (slot : var -> var)
           (RM : ⦃var⦄ * ⦃var⦄)
           (Z : params)
  : params
  :=
    match Z with
    | nil => nil
    | z::Z => if [z ∈ fst RM ∩ snd RM]
             then z::(slot z)::(slot_lift_params slot RM Z)
             else if [z ∈ fst RM]
                  then z::(slot_lift_params slot RM Z)
                  else (slot z)::(slot_lift_params slot RM Z)
    end
.



Lemma slot_lift_params_app
      L1 L2 L1' L2' slot
  :
    length L1 = length L1'
    -> slot_lift_params slot ⊜ L1 L1'
                       ++ slot_lift_params slot ⊜ L2 L2'
      = slot_lift_params slot ⊜ (L1 ++ L2) (L1' ++ L2')
.
Proof.
  intros.
  rewrite zip_app; eauto with len.
Qed.



Fixpoint slot_lift_args
         (slot : var -> var)
         (RM : ⦃var⦄ * ⦃var⦄)
         (Y : args)
  : args
  := match Y with
     | nil => nil
     | y::Y
       => match y with
         | Var v => if [v ∈ fst RM ∩ snd RM]
                   then (Var v)::(Var (slot v))
                               ::(slot_lift_args slot RM Y)
                   else if [v ∈ fst RM]
                        then (Var v)::(slot_lift_args slot RM Y)
                        else (Var (slot v))
                               ::(slot_lift_args slot RM Y)
         | _ => y::(slot_lift_args slot RM Y)
         end
     end
.


Definition write_spills
           (slot : var -> var)
           (Z : params)
           (s : stmt)
  : stmt
  := fold_right (fun x s => stmtLet (slot x) (Operation (Var x)) s) s Z
.

Definition write_loads
           (slot : var -> var)
           (Z : params)
           (s : stmt)
  : stmt
  := fold_right (fun x s => stmtLet x (Operation (Var (slot x))) s) s Z
.


Lemma write_spills_empty
      (slot : var -> var)
      (s : stmt)
  :
    write_spills slot nil s = s
.
Proof.
  simpl.
  reflexivity.
Qed.


Lemma write_loads_empty
      (slot : var -> var)
      (s : stmt)
  :
    write_loads slot nil s = s
.
Proof.
  simpl.
  reflexivity.
Qed.


Lemma write_spills_s
      (slot : var -> var)
      (xs : list var)
      (x : var)
      (s : stmt)
  :
    write_spills slot (x::xs) s
    = stmtLet (slot x) (Operation (Var x)) (write_spills slot xs s)
.
Proof.
  simpl.
  reflexivity.
Qed.




Lemma write_loads_s
      (slot : var -> var)
      (xs : list var)
      (x : var)
      (s : stmt)
  :
    write_loads slot (x::xs) s
    = stmtLet x (Operation (Var (slot x))) (write_loads slot xs s)
.
Proof.
  simpl.
  reflexivity.
Qed.




Definition do_spill_rec
           (slot : var -> var)
           (s : stmt)
           (sl : spilling)
           (do_spill' : forall (s' : stmt)
                           (sl' : spilling),
                            stmt)
  : stmt
  :=
    match s,sl with
    | stmtLet x e s, ann1 _ sl1
      => stmtLet x e (do_spill' s sl1)

    | stmtIf e s1 s2, ann2 _ sl1 sl2
      => stmtIf e (do_spill' s1 sl1) (do_spill' s2 sl2)

    | stmtFun F t, annF (_,_,Some (inl rms)) sl_F sl_t
      => stmtFun
          (pair ⊜
                (slot_lift_params slot ⊜ (snd ⊝ rms) (fst ⊝ F))
                 (* (fun (Zs : params * stmt) (rm : ⦃var⦄ * ⦃var⦄)
                  => slot_lift_params slot (snd rm) (fst Zs)) ⊜ F rms)*)
                ((fun (Zs : params * stmt) (sl_s : spilling)
                  => do_spill' (snd Zs) sl_s) ⊜ F sl_F)
  (* we can't write "(do_spill' ⊜ (snd ⊝ F) sl_F)" because termination wouldn't be obvious *)
          )
          (do_spill' t sl_t)

    | stmtApp f Y, ann0 (_,_,Some (inr M))
      => stmtApp f ((slot_lift_args slot M Y)

    | _,_
      => s
    end
.



(* this algorithm prefers variables in the memory in function applications *)
Fixpoint do_spill
           (slot : var -> var)
           (s : stmt)
           (sl : spilling)
           {struct s}
  : stmt
  :=
    write_spills slot (elements (getSp sl)) (
        write_loads slot (elements (getL sl)) (
            do_spill_rec slot s sl (do_spill slot)
        )
     )
.

(*
Fixpoint do_spill
           (slot : var -> var)
           (M : set var)
           (s : stmt)
           (sl : spilling)
  : stmt
  :=
    write_spills slot (elements (getSp sl)) (
        write_loads slot (elements (getL sl)) (
            let do_spill' := do_spill slot (getSp sl ∪ M) in
            match s,sl with
            | stmtLet x e s, ann1 _ sl1
              => stmtLet x e (do_spill' s sl1)

            | stmtIf e s1 s2, ann2 _ sl1 sl2
              => stmtIf e (do_spill' s1 sl1) (do_spill' s2 sl2)

            | stmtFun F t, annF (_,_,Some rms) sl_F sl_t
              => stmtFun
                  ((fun pf sf => (pf,sf))
                     ⊜ ((fun (Zs : params * stmt) (rm : set var * set var)
                         => slot_lift_params slot (snd rm) ⊝ (fst Zs)) ⊜ F rms)
                     ((fun (Zs : params * stmt) (sl_s : spilling)
                       => do_spill' (snd Zs) sl_s) ⊜ F sl_F)
                  )
                  (do_spill' t sl_t)

            | stmtApp f Y, ann0 _
              => stmtApp f ((slot_lift_args slot M) ⊝ Y)

            | _,_
              => s
            end
        )
     )
.
 *)


(*

Lemma slot_lift_args_Equal_M
      (slot : var -> var)
      (M M' : set var)
      (y y' : op)
  :
    M [=] M'
    -> y === y'
    -> slot_lift_args slot M y = slot_lift_args slot M' y'
.
Proof.
  intros eq_M eq_y.
  destruct y;
    destruct y';
    isabsurd;
    simpl;
    eauto.
  inv eq_y.
  decide (v0 ∈ M).
  - rewrite eq_M in i.
    decide (v0 ∈ M').
    + reflexivity.
    + contradiction.
  - rewrite eq_M in n.
    decide (v0 ∈ M').
    + contradiction.
    + reflexivity.
Qed.


Lemma slot_lift_args_Equal_M_Y
      (slot : var -> var)
      (M M' : set var)
      (Y Y' : args)
  :
    M [=] M'
    -> Y === Y'
    -> slot_lift_args slot M ⊝ Y = slot_lift_args slot M' ⊝ Y'
.
Proof.
  intros eq_M eq_Y.
  general induction Y;
    inv eq_Y;
    simpl; eauto.
  erewrite slot_lift_args_Equal_M; eauto.
  f_equal.
  apply IHY; eauto.
Qed.


Lemma do_spill_rec_Equal_M
      (slot : var -> var)
      (M M' : set var)
      (s : stmt)
      (sl : spilling)
  :
    M [=] M'
    -> do_spill_rec slot M s sl = do_spill_rec slot M' s sl
.
Proof.
  intro eq_M.
  destruct s; simpl; eauto.
  destruct sl; simpl; eauto.
  unfold do_spill_rec.
  enough (slot_lift_args slot M ⊝ Y = slot_lift_args slot M' ⊝ Y) as H.
  {
    rewrite H.
    reflexivity.
  }
  apply slot_lift_args_Equal_M_Y; eauto.
Qed.


Lemma do_spill_Equal_M
      (slot : var -> var)
      (M M' : ⦃ var ⦄)
      (s : stmt)
      (sl : spilling)
  :
    M [=] M'
    -> do_spill slot M s sl = do_spill slot M' s sl
.
Proof.
  intros eq_M.
  revert M M' sl eq_M.
  sind s;
    intros;
    destruct s;
    simpl;
    do 2 f_equal;
    destruct sl;
    eauto.
  - rewrite (IH s) with (M':= getSp (ann1 a sl) ∪ M'); eauto.
    rewrite eq_M.
    eauto.
  - erewrite (IH s1) with (M':= getSp (ann2 a sl1 sl2) ∪ M'); eauto.
    + erewrite (IH s2) with (M':= getSp (ann2 a sl1 sl2) ∪ M'); eauto.
      rewrite eq_M.
      eauto.
    + rewrite eq_M.
      eauto.
  - erewrite slot_lift_args_Equal_M_Y; eauto.
    rewrite eq_M.
    reflexivity.
  - destruct a;
      destruct p;
      destruct o;
      eauto.
    f_equal.
    + eapply zip_ext_get2; eauto.
      * rewrite !zip_length.
        eauto.
      * intros.
        inv_get.
        f_equal.
        apply IH; eauto.
        rewrite eq_M.
        eauto.
    + apply IH; eauto.
      rewrite eq_M.
      eauto.
Qed.


Lemma do_spill_rec_do_spill_Equal_M
      (slot : var -> var)
      (M M' : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
  :
    M [=] M'
    -> do_spill_rec slot M s sl (do_spill slot M)
      = do_spill_rec slot M' s sl (do_spill slot M')
.
Admitted.
(*
Lemma do_spill_rec_do_spill_Equal_M
      (slot : var -> var)
      (M M' : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
      (do_spill' : forall (M0 : ⦃var⦄)
                      (s0 : stmt)
                      (sl0 : spilling),
          stmt)
  :
    M [=] M'
    -> do_spill' M = do_spill' M'
    -> do_spill_rec slot M s sl (do_spill' M)
      = do_spill_rec slot M' s sl (do_spill' M')
.
Proof.
  intros eq_M.
  general induction s;
    simpl; eauto.
  erewrite slot_lift_args_Equal_M_Y;
    eauto.
Qed.



Lemma do_spill_Equal_M
          (slot : var -> var)
          (M M' : set var)
          (s : stmt)
          (sl : spilling)
  :
    M [=] M'
    -> (forall M0 M0', M0 [=] M0'
                 -> do_spill_rec slot M0 s sl (do_spill slot M0)
                   = do_spill_rec slot M0' s sl (do_spill slot M0'))
    -> do_spill slot M s sl
      = do_spill slot M' s sl
.
Proof.
  intros eq_M eq_dsr.
  general induction s;
    unfold do_spill;
    f_equal;
    f_equal;
    destruct sl;
    eauto;
    apply eq_dsr;
    rewrite eq_M;
    reflexivity.
Qed.
*)
(*
Lemma do_spill_rec_Equal_M'
      (slot : var -> var)
      (M M' : ⦃ var ⦄)
      (s : stmt)
      (sl : spilling)
  :
    M [=] M'
    -> do_spill_rec slot M s sl (do_spill slot M)
      = do_spill_rec slot M' s sl (do_spill slot M')
.
Proof.
  intros eq_M.
  general induction s.
    simpl; eauto.
  - destruct sl; eauto.
    erewrite do_spill_Equal_M; eauto.
  - admit.
  - admit.
  - destruct sl; eauto.
    destruct a;
      destruct p;
      destruct o;
      eauto.
    erewrite do_spill_Equal_M; eauto.
    replace ((fun (Zs : params * stmt) (sl_s : spilling) => do_spill slot M (snd Zs) sl_s) ⊜ F sa)
    with ((fun (Zs : params * stmt) (sl_s : spilling) => do_spill slot M' (snd Zs) sl_s) ⊜ F sa).
    + reflexivity.
    + f_equal.
      extensionality ps'.
      extensionality sl'.
      symmetry.
      eapply do_spill_Equal_M; eauto.
      intros.
      apply do_spill_rec_do_spill_Equal_M.

uecouiaeou
*)
*)


Lemma do_spill_rec_s
      (slot : var -> var)
      (Sp' L': ⦃ var ⦄)
      (s : stmt)
      (sl : spilling)
  :
    do_spill_rec slot s sl
    = do_spill_rec slot s (setTopAnn sl (Sp',L',snd (getAnn sl)))
.
Proof.
  destruct s, sl;
    simpl;
    unfold do_spill_rec;
    try reflexivity;
  destruct a;
    destruct p;
    destruct o;
    eauto.
Qed.

Lemma do_spill_empty
      (slot : var -> var)
      (s : stmt)
      (sl : spilling)
  :
    count sl = 0
    -> do_spill slot s sl
      = do_spill_rec slot s sl (do_spill slot)
.
Proof.
  intros count_zero.
  apply count_zero_Empty_Sp in count_zero as Empty_Sp.
  apply count_zero_Empty_L  in count_zero as Empty_L.
  unfold do_spill.
  rewrite elements_Empty in Empty_Sp.
  rewrite elements_Empty in Empty_L.
  induction s;
    rewrite Empty_Sp;
    rewrite Empty_L;
    rewrite write_spills_empty;
    rewrite write_loads_empty;
    fold do_spill;
    reflexivity.
Qed.



Lemma do_spill_extract_writes
      (slot : var -> var)
      (s : stmt)
      (sl : spilling)
  :
    do_spill slot s sl
    = write_spills slot (elements (getSp sl))
         (write_loads slot (elements (getL sl))
             (do_spill slot s (setTopAnn sl (∅,∅,snd (getAnn sl)))))
.
Proof.
  symmetry.
  rewrite do_spill_empty.
  - rewrite do_spill_rec_s with (Sp':=∅) (L':=∅).
    rewrite setTopAnn_setTopAnn.
    destruct s,sl;
      simpl; eauto;
    do 2 f_equal;
    destruct a;
    simpl;
    destruct o;
      destruct p;
      reflexivity.
  - unfold count.
    rewrite getAnn_setTopAnn.
    simpl.
    eauto.
Qed.



Lemma do_spill_sub_empty_invariant
      (slot : var -> var)
      (Sp' L': ⦃ var ⦄)
      (s : stmt)
      (sl : spilling)
  :
    count sl = 0
    -> Sp' [=] ∅
    -> L' [=] ∅
    ->  do_spill slot s sl
       = do_spill slot s (setTopAnn sl (Sp',L',snd (getAnn sl)))
.
Proof.
  intros count_zero Sp_empty L_empty.
  rewrite do_spill_empty; eauto.
  rewrite do_spill_empty;
    swap 1 2.
  {
    unfold count.
    rewrite getAnn_setTopAnn.
    simpl.
    rewrite Sp_empty.
    rewrite L_empty.
    eauto.
  }
  destruct s, sl;
    simpl; eauto;
  destruct a;
    destruct p;
    destruct o;
    simpl; eauto.
Qed.


(*
Lemma do_spill_Sp
      (slot : var -> var)
      (s : stmt)
      (sl : ann (set var * set var * option (list (set var * set var))))
  :
    let Sp := fst (fst (getAnn sl)) in
    let L  := snd (fst (getAnn sl)) in
    let x  := hd 0 (elements Sp) in
    let Sp':= of_list (tl (elements Sp)) in
    ~ Empty Sp
    -> do_spill slot s sl
      = stmtLet (slot x)
                (Operation (Var x))
                (do_spill slot s (setTopAnn sl (Sp',L,snd (getAnn sl))))
.
Proof.
  intros Sp L x Sp' NEmpty_Sp.
  assert (~ cardinal Sp = 0) as Sp_nonzero.
  { intro N. apply NEmpty_Sp. rewrite cardinal_Empty. eauto. }
  assert (exists n, cardinal Sp = S n) as [n card_Sp].
  { exists (cardinal Sp - 1). omega. }
  subst Sp.
  subst L.
  assert (forall (t : set var), (S n) + cardinal t = S (n + cardinal t)) as nL_card_S.
  { intros t. omega. }
  induction s;
    simpl;
    rewrite card_Sp;
    rewrite nL_card_S;
    rewrite getAnn_setTopAnn; simpl;
    rewrite card_Sp;
    simpl;
    subst x;
    subst Sp';
    rewrite cardinal_tl with (n:=n);
    eauto;
    reflexivity.
Qed.

Lemma do_spill_L
      (slot : var -> var)
      (s : stmt)
      (sl : spilling)
  :
    cardinal (getSp sl) = 0
    -> cardinal (getL sl) > 0
    -> do_spill slot s sl
      = write_loads
                (Operation (Var (slot x)))
                (do_spill slot s (setTopAnn sl (Sp,L',snd (getAnn sl))))
.
Proof.
  intros Sp L x L' Empty_Sp NEmpty_L.
  assert (~ cardinal L = 0) as L_nonzero.
  { intro N. apply NEmpty_L. rewrite cardinal_Empty. eauto. }
  assert (exists n, cardinal L = S n) as [n card_L].
  { exists (cardinal L - 1). omega. }
  assert (cardinal Sp = 0) as card_Sp.
  { apply cardinal_Empty. assumption. }
  subst Sp.
  subst L.
  induction s;
    simpl;
      rewrite card_L;
      rewrite card_Sp;
    simpl;
    rewrite getAnn_setTopAnn;
    rewrite card_L;
      rewrite card_Sp;
    simpl;
      subst x;
      subst L';
      rewrite cardinal_tl with (n:=n);
      eauto;
    rewrite card_Sp;
      simpl;
    reflexivity.
Qed.















*)