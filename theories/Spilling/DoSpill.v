Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI Spilling SpillUtil.

Fixpoint do_spill
         (slot : var -> var)
         (s : stmt)
         (sl0 : ann (set var * set var * option(list(set var * set var))))
         {struct s}
  : stmt :=



  let Sp0 := fst (fst (getAnn sl0)) in
  let L0  := snd (fst (getAnn sl0)) in
  let rm  := snd (getAnn sl0) in

(fix f sl n {struct n} :=
  let Sp := fst (fst (getAnn sl)) in
  let L  := snd (fst (getAnn sl)) in
  match n with
    | 0 =>
     match s,sl with
     | stmtLet x e s, ann1 _ sl_s
       => stmtLet x e (do_spill slot s sl_s)
     | stmtIf e s t, ann2 _ sl_s sl_t
       => stmtIf e (do_spill slot s sl_s) (do_spill slot t sl_t)
     | stmtFun F t, annF _ sl_F sl_t
       => stmtFun
            ((fun Zs sl_s => (fst Zs (* todo: really? I think it's fine *)
                                    , do_spill slot (snd Zs) sl_s)) ⊜ F sl_F)
                           (do_spill slot t sl_t)

     | _,_
       => s
     end
    | S n =>

  if
    [cardinal Sp = 0]
  then
    if
      [cardinal L = 0]
    then
     match s,sl with
     | stmtLet x e s, ann1 _ sl_s
       => stmtLet x e (do_spill slot s sl_s)
     | stmtIf e s t, ann2 _ sl_s sl_t
       => stmtIf e (do_spill slot s sl_s) (do_spill slot t sl_t)
     | stmtFun F t, annF _ sl_F sl_t
       => stmtFun
            ((fun Zs sl_s => (fst Zs (* todo: really? I think it's fine *)
                                    , do_spill slot (snd Zs) sl_s)) ⊜ F sl_F)
                           (do_spill slot t sl_t)

     | _,_
       => s
     end

    else
      let x := hd 0 (elements L) in
      let L':= of_list (tl (elements L)) in
      stmtLet x (Operation (Var (slot x))) (f (setTopAnn sl (Sp,L',rm)) n)

  else
    let x  := hd 0 (elements Sp) in
    let Sp':= of_list (tl (elements Sp)) in
    stmtLet (slot x) (Operation (Var x)) (f (setTopAnn sl (Sp',L,rm)) n)
  end
) sl0 (cardinal Sp0 + cardinal L0)
.



Lemma do_spill_empty
      (slot : var -> var)
      (s : stmt)
      (sl : ann (set var * set var * option (list (set var * set var))))
  :
    Empty (fst (fst (getAnn sl)))
    -> Empty (snd (fst (getAnn sl)))
    -> do_spill slot s sl
      =

      match s,sl with
     | stmtLet x e s, ann1 _ sl_s
       => stmtLet x e (do_spill slot s sl_s)
     | stmtIf e s t, ann2 _ sl_s sl_t
       => stmtIf e (do_spill slot s sl_s) (do_spill slot t sl_t)
     | stmtFun F t, annF _ sl_F sl_t
       => stmtFun
            ((fun Zs sl_s => (fst Zs, do_spill slot (snd Zs) sl_s)) ⊜ F sl_F)
            (do_spill slot t sl_t)

     | _,_
       => s
      end.
Proof.
  intros Empty_Sp Empty_L.
  remember (fst (fst (getAnn sl))) as Sp.
  remember (snd (fst (getAnn sl))) as L.
  assert (cardinal Sp = 0) as zero_Sp.
  { apply cardinal_Empty. eauto. }
  assert (cardinal L = 0) as zero_L.
  { apply cardinal_Empty. eauto. }
  induction sl, s; simpl in *; rewrite <- HeqSp; rewrite <- HeqL;
    simpl; rewrite zero_Sp; rewrite zero_L; simpl; eauto.
Qed.





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
    rewrite getAnn_setTopAnn;
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
      (sl : ann (set var * set var * option (list (set var * set var))))
  :
    let Sp := fst (fst (getAnn sl)) in
    let L  := snd (fst (getAnn sl)) in
    let x  := hd 0 (elements L) in
    let L' := of_list (tl (elements L)) in
    Empty Sp
    -> ~ Empty L
    -> do_spill slot s sl
      = stmtLet x
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