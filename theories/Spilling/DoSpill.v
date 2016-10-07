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


Definition slot_lift_args
           (slot : var -> var)
           (M : set var)
  : op -> op
  := (fun y => match y with
            | Var v => if [v ∈ M] then Var (slot v) else Var v
            | _ => y
            end)
.

Fixpoint extend_args
         (Y : args)
         (ib : list bool)
  : args
  := match Y with
     | nil => nil
     | y :: Y => match ib with
                 | nil => y :: Y
                 | true  :: ib => y :: y :: extend_args Y ib
                 | false :: ib => y :: extend_args Y ib
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


Definition mark_elements
           (*(X : Type)
           `{OrderedType X}*)
           (L : list var)
           (s : ⦃var⦄)
  : list bool
  := (fun x => if [x ∈ s] then true else false) ⊝ L
.



Definition do_spill_rec
           (slot : var -> var)
           (s : stmt)
           (sl : spilling)
           (IB : list (list bool))
           (do_spill' : forall (s' : stmt)
                          (sl' : spilling)
                          (IB' : list (list bool)),
                            stmt)
  : stmt
  :=
    match s,sl with
    | stmtLet x e s, ann1 _ sl1
      => stmtLet x e (do_spill' s sl1 IB)

    | stmtIf e s1 s2, ann2 _ sl1 sl2
      => stmtIf e (do_spill' s1 sl1 IB) (do_spill' s2 sl2 IB)

    | stmtFun F t, annF (_,_,Some (inl rms)) sl_F sl_t
      => let IB' := mark_elements ⊜ (fst ⊝ F) ((fun rm => fst rm ∩ snd rm) ⊝ rms) ++ IB in
      stmtFun
          (pair ⊜
                (slot_lift_params slot ⊜ rms (fst ⊝ F))
                ((fun (Zs : params * stmt) (sl_s : spilling)
                  => do_spill' (snd Zs) sl_s IB') ⊜ F sl_F)
  (* we can't write "(do_spill' ⊜ (snd ⊝ F) sl_F)" because termination wouldn't be obvious *)
          )
          (do_spill' t sl_t IB')

    | stmtApp f Y, ann0 (_,_,Some (inr Sl))
      => stmtApp f (slot_lift_args slot Sl
                                  ⊝ (extend_args Y (nth f IB nil)))

    | _,_
      => s
    end
.


Fixpoint do_spill
           (slot : var -> var)
           (s : stmt)
           (sl : spilling)
           (IB : list (list bool))
           {struct s}
  : stmt
  :=
    write_spills slot (elements (getSp sl)) (
        write_loads slot (elements (getL sl)) (
            do_spill_rec slot s sl IB (do_spill slot)
        )
     )
.



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
      (IB : list (list bool))
  :
    count sl = 0
    -> do_spill slot s sl IB
      = do_spill_rec slot s sl IB (do_spill slot)
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
      (IB : list (list bool))
  :
    do_spill slot s sl IB
    = write_spills slot (elements (getSp sl))
         (write_loads slot (elements (getL sl))
             (do_spill slot s (setTopAnn sl (∅,∅,snd (getAnn sl))) IB))
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
      (IB : list (list bool))
  :
    count sl = 0
    -> Sp' [=] ∅
    -> L' [=] ∅
    ->  do_spill slot s sl IB
       = do_spill slot s (setTopAnn sl (Sp',L',snd (getAnn sl))) IB
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
