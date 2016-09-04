Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI Spilling.

Set Implicit Arguments.


Fixpoint write_spills (slot: var->var) (xs:list var) (s:stmt) : stmt :=
match xs with
| nil => s
| x::xs => stmtLet (slot x) (Operation (Var x)) (write_spills slot xs s)
end.

Fixpoint write_loads (slot: var-> var) (xs:list var) (s:stmt) : stmt :=
match xs with
| nil => s
| x::xs => stmtLet x (Operation (Var (slot x))) (write_loads slot xs s)
end.


Fixpoint do_spill
(slot: var -> var)
(s:stmt)
(sl:ann (set var * set var * option (list (set var * set var)))) : stmt :=

let Sp := fst (fst (getAnn sl)) in
let L  := snd (fst (getAnn sl)) in

write_spills slot (elements Sp)
  (write_loads slot (elements L)

    (match s,sl with
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
     end))
.

Fixpoint test
         (s : set var)
         (n : nat)
         {struct n}
  : set var
  :=
    match n with
    | 0 => s
    | S n => test (of_list (tl (elements s))) n
    end.


Fixpoint do_spill'
         (slot : var -> var)
         (s : stmt)
         (sl : ann (set var * set var * option(list(set var * set var))))
         {struct s}
  : stmt :=



  let Sp := fst (fst (getAnn sl)) in
  let L  := snd (fst (getAnn sl)) in
  let rm := snd (getAnn sl) in

(fix f sl n {struct n} :=
  match n with
    | 0 =>
     match s,sl with
     | stmtLet x e s, ann1 _ sl_s
       => stmtLet x e (do_spill' slot s sl_s)
     | stmtIf e s t, ann2 _ sl_s sl_t
       => stmtIf e (do_spill' slot s sl_s) (do_spill' slot t sl_t)
     | stmtFun F t, annF _ sl_F sl_t
       => stmtFun
            ((fun Zs sl_s => (fst Zs (* todo: really? I think it's fine *)
                                    , do_spill' slot (snd Zs) sl_s)) ⊜ F sl_F)
                           (do_spill' slot t sl_t)

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
       => stmtLet x e (do_spill' slot s sl_s)
     | stmtIf e s t, ann2 _ sl_s sl_t
       => stmtIf e (do_spill' slot s sl_s) (do_spill' slot t sl_t)
     | stmtFun F t, annF _ sl_F sl_t
       => stmtFun
            ((fun Zs sl_s => (fst Zs (* todo: really? I think it's fine *)
                                    , do_spill' slot (snd Zs) sl_s)) ⊜ F sl_F)
                           (do_spill' slot t sl_t)

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
) sl (cardinal Sp + cardinal L)
.



Lemma do_spill_empty
      (slot : var -> var)
      (s : stmt)
      (sl : ann (set var * set var * option (list (set var * set var))))
  :
    Empty (fst (fst (getAnn sl)))
    -> Empty (snd (fst (getAnn sl)))
    -> do_spill' slot s sl
      =

      match s,sl with
     | stmtLet x e s, ann1 _ sl_s
       => stmtLet x e (do_spill' slot s sl_s)
     | stmtIf e s t, ann2 _ sl_s sl_t
       => stmtIf e (do_spill' slot s sl_s) (do_spill' slot t sl_t)
     | stmtFun F t, annF _ sl_F sl_t
       => stmtFun
            ((fun Zs sl_s => (fst Zs, do_spill' slot (snd Zs) sl_s)) ⊜ F sl_F)
            (do_spill' slot t sl_t)

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

Lemma discard_merge_sl_1
      (slot : var -> var)
      (Sp L : set var)
      (sl : ann (set var * set var * option ( list (set var * set var))))
  :
    discard_merge_sl slot (ann1 (Sp,L,None) sl) = ann1 None (discard_merge_sl slot sl).
Proof.
  eauto.
Qed.

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
    unfold discard_merge_sl; fold discard_merge_sl; simpl; admit.
(* trivial! but how to kill the stupid let (_,_) ?? *)
Admitted.



(*
Lemma discard_merge_sl_set_invariant
      (slot : var -> var)
      (a a' : ann (set var * set var * option(list(set var * set var))))
  :
    a === a'
      -> discard_merge_sl slot a === discard_merge_sl slot a'.
Proof.
  intro aEq.
  induction a, a'; try isabsurd.
  - econstructor.

    destruct a as [[Sp L] [rm |]];
      destruct a0 as [[Sp0 L0] [rm0|]];
      inversion_clear aEq; inversion_clear H; inversion_clear H1.
    + econstructor. simpl. induction rm,rm0; try isabsurd.
      * econstructor.
      * econstructor.
        -- admit.
        -- admit.
    + econstructor.
  - econstructor.
    + destruct a as [[Sp L] [rm |]];
        destruct a1 as [[Sp1 L1] [rm1 |]];
        inversion_clear aEq; inversion_clear H; inversion_clear H1; admit.
    + admit.
  - econstructor.
    + destruct a as [[Sp L] [rm |]];
        destruct a1 as [[Sp1 L1] [rm1 |]];
        inversion_clear aEq; inversion_clear H; inversion_clear H1; admit.
    + admit.
    + admit.
  - admit.
Admitted.
*)

Lemma ann_R_seteq
      (X : Type) `{OrderedType X}
      (a b : ann X)
  :
    a === b
    -> ann_R _eq a b.
Proof.
  intros eq_ab.
  induction a,b ; try isabsurd; inversion eq_ab.
  * apply annLt0. eauto.
      * apply annLt1; eauto.
      * apply annLt2; eauto.
      * apply annLtF; eauto.
Qed.

Lemma ann_seteq_0
      (X : Type) `{OrderedType X}
      (x x' : X)
  :
    x === x'
    -> ann0 x === ann0 x'.
Proof.
  intros eq_x.
  apply ann_R_Equivalence.
  - apply OT_Equivalence.
  - econstructor. eauto.
Qed.




Lemma ann_seteq_1
      (X : Type) `{OrderedType X}
      (x x' : X)
      (a b : ann X)
  :
    x === x'
    -> a === b
    -> ann1 x a === ann1 x' b.
Proof.
  intros eq_x eq_ab.
  apply ann_R_Equivalence.
  - apply OT_Equivalence.
  - econstructor.
    + eauto.
    + apply ann_R_seteq. eauto.
Qed.

Lemma ann_seteq_2
      (X : Type) `{OrderedType X}
      (x x' : X)
      (a a' b b': ann X)
  :
    x === x'
    -> a === a'
    -> b === b'
    -> ann2 x a b === ann2 x' a' b'.
Proof.
  intros eq_x eq_a eq_b.
  apply ann_R_Equivalence.
  - apply OT_Equivalence.
  - econstructor.
    + eauto.
    + apply ann_R_seteq. eauto.
    + apply ann_R_seteq. eauto.
Qed.


Lemma ann_seteq_F
      (X : Type) `{OrderedType X}
      (x x' : X)
      (a a': ann X)
      (F F': list (ann X))
  :
    x === x'
    -> a === a'
    -> F === F'
    -> annF x F a === annF x' F' a'.
Proof.
  intros eq_x eq_a eq_F.
  apply ann_R_Equivalence.
  - apply OT_Equivalence.
  - econstructor.
    + eauto.
    + revert dependent F'. revert F. induction F.
      * induction F'.
        -- eauto.
        -- isabsurd.
      * destruct F'.
        -- isabsurd.
        -- intros. simpl. f_equal. apply IHF.
           inversion_clear eq_F.
           apply H0.
    + intros n a0 b get_a0 get_b.
      enough (a0 === b) as eq_ab.
      * rewrite eq_ab.
        apply ann_R_refl.
      * eapply get_PIR2 with (L:=F') (L':=F) (n:=n).
        -- symmetry in eq_F. eauto.
        -- eauto.
        -- eauto.
    + apply ann_R_seteq. eauto.
Qed.



Lemma ann_seteq_s_t_1
      (s s' t t' : set var)
      (rm : option(list(set var * set var)))
      (sl : ann (set var * set var * option(list(set var * set var))))
  :
    s === s'
    -> t === t'
        -> ann1 (s,t,rm) sl === ann1 (s',t',rm) sl.
Proof.
  intros eq_s eq_t.
  apply ann_R_Equivalence.
      - apply OT_Equivalence.
      - econstructor.
        + econstructor.
          * econstructor; eauto.
          * eauto.
        + eauto.
Qed.


Fixpoint add_nones
         (n : nat)
         (b : ann (set var * set var * option(list( set var * set var))))
  : ann (set var * set var * option (list ( set var * set var)))
      :=
        match n with
        |   0 => b
        | S(n)=> ann1 (∅,∅,None) (add_nones n b)
        end.




Fixpoint do_spill_rm
(slot : var -> var)
(sl: ann (set var * set var * option (list (set var * set var ))))
: ann (set var * set var * option (list (set var * set var)))
:=
match sl with
| ann0 (Sp,L,rm)           => add_nones (cardinal Sp + cardinal L)
                                         sl
| ann1 (Sp,L,rm) sl_s      => add_nones (cardinal Sp + cardinal L)
                                        (ann1 (Sp,L,rm) (do_spill_rm slot sl_s))
| ann2 (Sp,L,rm) sl_s sl_t => add_nones (cardinal Sp + cardinal L)
                                        (ann2 (Sp,L,rm) (do_spill_rm slot sl_s)
                                                        (do_spill_rm slot sl_t))
| annF (Sp,L,rm) sl_F sl_t => add_nones (cardinal Sp + cardinal L)
                                  (annF (Sp,L,rm) (do_spill_rm slot ⊝ sl_F)
                                                  (do_spill_rm slot sl_t))
end.

(*
Fixpoint do_spill_rm
(slot : var -> var)
(sl: ann (set var * set var * option (list (set var * set var ))))
: ann (set var * set var * option (list (set var * set var)))
  :=
    add_nones (cardinal Sp + cardinal L)

match sl with
| ann0 (Sp,L,rm)           => sl
| ann1 (Sp,L,rm) sl_s      => ann1 (Sp,L,rm) (do_spill_rm slot sl_s)
| ann2 (Sp,L,rm) sl_s sl_t => ann2 (Sp,L,rm) (do_spill_rm slot sl_s)
                                             (do_spill_rm slot sl_t)
| annF (Sp,L,rm) sl_F sl_t => annF (Sp,L,rm) (do_spill_rm slot ⊝ sl_F)
                                             (do_spill_rm slot sl_t)
end.
*)

Lemma do_spill_rm_empty'
(slot : var -> var)
(sl : ann (set var * set var * option (list (set var * set var ))))
(rm : option(list(set var * set var)))
  : getAnn sl === (∅,∅,rm)
    -> do_spill_rm slot sl ===
     match sl with
     | ann0 _ => ann0 (∅,∅,rm)
     | ann1 _ sl_s => ann1 (∅,∅,rm) (do_spill_rm slot sl_s)
     | ann2 _ sl_s sl_t => ann2 (∅,∅,rm) (do_spill_rm slot sl_s)
                                         (do_spill_rm slot sl_t)
     | annF _ sl_F sl_t => annF (∅,∅,rm) (do_spill_rm slot ⊝ sl_F)
                                         (do_spill_rm slot sl_t)
     end.
Proof. (*
intros emptySpL.
induction sl; simpl in *. (*+TODO+*)
- eauto.
- rewrite empty_cardinal. simpl. eauto.
- rewrite empty_cardinal. simpl. eauto.
- rewrite empty_cardinal. simpl. eauto.
Qed.
        *)
Admitted.

Lemma do_spill_rm_empty
(slot : var -> var)
(sl : ann (set var * set var * option (list (set var * set var ))))
(rm : option(list(set var * set var)))
  : getAnn sl = (∅,∅,rm)
    -> do_spill_rm slot sl =
     match sl with
     | ann0 _ => ann0 (∅,∅,rm)
     | ann1 _ sl_s => ann1 (∅,∅,rm) (do_spill_rm slot sl_s)
     | ann2 _ sl_s sl_t => ann2 (∅,∅,rm) (do_spill_rm slot sl_s)
                                         (do_spill_rm slot sl_t)
     | annF _ sl_F sl_t => annF (∅,∅,rm) (do_spill_rm slot ⊝ sl_F)
                                         (do_spill_rm slot sl_t)
     end.
Proof.
intros emptySpL.
induction sl; simpl in *; rewrite emptySpL.
- eauto.
- rewrite empty_cardinal. simpl. eauto.
- rewrite empty_cardinal. simpl. eauto.
- rewrite empty_cardinal. simpl. eauto.
Qed.


Lemma do_spill_rm_empty''
(slot : var -> var)
(sl : ann (set var * set var * option (list (set var * set var ))))
  : Empty (fst (fst (getAnn sl)))
    -> Empty (snd (fst (getAnn sl)))
    -> do_spill_rm slot sl =
     match sl with
     | ann0 (Sp,L,rm) => ann0 (Sp,L,rm)
     | ann1 (Sp,L,rm) sl_s => ann1 (Sp,L,rm) (do_spill_rm slot sl_s)
     | ann2 (Sp,L,rm) sl_s sl_t => ann2 (Sp,L,rm) (do_spill_rm slot sl_s)
                                         (do_spill_rm slot sl_t)
     | annF (Sp,L,rm) sl_F sl_t => annF (Sp,L,rm) (do_spill_rm slot ⊝ sl_F)
                                         (do_spill_rm slot sl_t)
     end.
Proof.

intros Sp_Empty L_Empty.
induction sl; destruct a as [[Sp L] rm']; simpl in *;
  apply cardinal_Empty in Sp_Empty; apply cardinal_Empty in L_Empty;
  rewrite Sp_Empty; rewrite L_Empty; simpl; eauto.
Qed.

Lemma do_spill_rm_s
      (slot : var -> var)
      (sl : ann (set var * set var * option (list (set var * set var))))
      (n : nat)
  :
    cardinal (fst (fst (getAnn sl))) + cardinal (snd (fst (getAnn sl))) = S n
    -> do_spill_rm slot sl
      = ann1 (∅,∅,None)
             (add_nones n (
     match sl with
     | ann0 (Sp,L,rm) => ann0 (Sp,L,rm)
     | ann1 (Sp,L,rm) sl_s => ann1 (Sp,L,rm) (do_spill_rm slot sl_s)
     | ann2 (Sp,L,rm) sl_s sl_t => ann2 (Sp,L,rm) (do_spill_rm slot sl_s)
                                         (do_spill_rm slot sl_t)
     | annF (Sp,L,rm) sl_F sl_t => annF (Sp,L,rm) (do_spill_rm slot ⊝ sl_F)
                                         (do_spill_rm slot sl_t)
     end)).
Proof.
  intros card_s.
  induction sl; destruct a as [[Sp L] rm']; simpl in *; rewrite card_s; simpl; eauto.
Qed.



Lemma do_spill_Sp
      (slot : var -> var)
      (s : stmt)
      (sl : ann (set var * set var * option (list (set var * set var))))
  :
    let Sp := fst (fst (getAnn sl)) in
    let L  := snd (fst (getAnn sl)) in
    let x  := hd 0 (elements L) in
    let Sp':= of_list (tl (elements Sp)) in
    ~ Empty Sp
    -> do_spill' slot s sl
      = stmtLet (slot x)
                (Operation (Var x))
                (do_spill' slot s (setTopAnn sl (Sp',L,snd (getAnn sl))))
.
Proof.
  intros Sp0 L0 x Sp' NEmpty_Sp.
  assert (~ cardinal Sp0 = 0) as Sp_nonzero.
  { intro N. apply NEmpty_Sp. rewrite cardinal_Empty. eauto. }
  subst Sp0...
  subst L0...
  destruct (getAnn sl) as [[Sp L] rm].
  admit.
Admitted.

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
  -> do_spill' slot s sl
    = stmtLet x
              (Operation (Var (slot x)))
              (do_spill' slot s (setTopAnn sl (Sp,L',snd (getAnn sl)))).
Admitted.

(*
Corollary do_spill_rm_empty_1
          (slot : var -> var)
          (s t : set var)
          (sl : ann (set var * set var * option(list(set var * set var))))
  : s === ∅
    -> t === ∅
    -> do_spill_rm slot (ann1 (s,t,None) sl)
                === ann1 (s,t,None) (do_spill_rm slot sl)
.
Proof. (*
  intros s_eq t_eq.
  assert (tada := ann_seteq_s_t_1 (*s ∅ t ∅*) None (do_spill_rm slot sl) s_eq t_eq).
  rewrite tada.
  rewrite do_spill_rm_empty'.
  - eauto.
  - simpl. apply injective_projections; simpl.
    + apply injective_projections; simpl. eauto. rewrite s_eq. | rewrite t_eq]. eauto. reflexivity. eauto.
Qed.
*)
Admitted.
*)

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

Lemma write_spills_empty
(slot : var -> var)
(s : stmt)
: write_spills slot nil s = s.
Proof.
simpl.
eauto.
Qed.

Lemma write_loads_empty
(slot : var -> var)
(s : stmt)
: write_loads slot nil s = s.
Proof.
simpl.
eauto.
Qed.


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

Lemma setTopAnn_setTopAnn
      (X : Type)
      (x x' : X)
      (a : ann X)
  :
    setTopAnn (setTopAnn a x') x = setTopAnn a x.
Proof.
  induction a; simpl; eauto.
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
    -> do_spill' slot s sl = do_spill' slot s sl'
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

Lemma dms_dsr_empty_invariant
      (slot : var -> var)
      (Sp' L' : set var)
      (rm : option (list (set var * set var)))
      (sl sl' : ann (set var * set var * option (list (set var * set var))))
:
  sl' = setTopAnn sl (Sp',L',snd (getAnn sl))
  -> Empty (fst (fst (getAnn sl)))
  -> Empty (snd (fst (getAnn sl)))
  -> Empty Sp'
  -> Empty L'
  -> discard_merge_sl slot (do_spill_rm slot sl)
   = discard_merge_sl slot (do_spill_rm slot sl')
.
Proof.
  intros top_sl' Empty_Sp Empty_L Empty_Sp' Empty_L'.
  rewrite top_sl'.
  rewrite do_spill_rm_empty'';
    try rewrite getAnn_setTopAnn; eauto.
  rewrite do_spill_rm_empty'';
    try rewrite getAnn_setTopAnn; eauto.
  unfold setTopAnn.
  do 2 rewrite discard_merge_sl_step.
  induction sl; simpl; destruct a; destruct p;
    simpl; reflexivity.
Qed.





Lemma spill_live_sound_s
(slot : var -> var) (*maybe needs restrictions*)
(ZL : list params)
(G : set var)
(Λ : list (set var * set var))
(Lv : list (set var))
(s : stmt)
(sl : ann (set var * set var * option (list (set var * set var))))
  :
  let sl' := setTopAnn sl (∅,∅,snd (getAnn sl)) in
  (forall G', live_sound Imperative ZL Lv
                (do_spill' slot s sl')
                (spill_live (slot_merge slot Λ) ZL G'
                            (do_spill' slot s sl')
                            (discard_merge_sl slot (do_spill_rm slot sl')))
  )
-> live_sound Imperative ZL Lv
              (do_spill' slot s sl)
              (spill_live (slot_merge slot Λ) ZL G
                          (do_spill' slot s sl)
                          (discard_merge_sl slot (do_spill_rm slot sl))).
Proof.

set (Sp := fst (fst (getAnn sl))).
set (L  := snd (fst (getAnn sl))).
set (rm := snd (getAnn sl)).
intros sl' strong_sls.


remember (cardinal Sp) as n_Sp.
symmetry in Heqn_Sp.
revert dependent sl.
revert G.
induction n_Sp;
  intros G sl Sp L rm sl' strong_sls card_Sp.

- remember (cardinal L) as n_L.
  symmetry in Heqn_L.
  revert dependent sl.
  revert G.
  induction n_L;
    intros G sl Sp L rm sl' strong_sls card_Sp card_L.

  {
    rewrite do_spill_empty_invariant
    with (Sp':=∅) (L':=∅) (rm:=rm) (sl':=sl');
      subst Sp; subst L; simpl; eauto; try apply empty_1;
      try apply cardinal_Empty; eauto.
    + rewrite dms_dsr_empty_invariant
      with (Sp':=∅) (L':=∅) (sl':=sl');
        eauto; try apply empty_1;
        apply cardinal_Empty; assumption.
  }

  rewrite do_spill_rm_s with (n:=n_L).
  Focus 2. subst Sp. rewrite card_Sp.
           subst L. rewrite card_L.
           omega.

  rewrite do_spill_L.
  Focus 2. subst Sp. rewrite cardinal_Empty. assumption.
  Focus 2. subst L. clear - card_L. intro N.
           apply cardinal_Empty in N. omega.

  econstructor; fold spill_live.
  * assert (forall sl, add_nones n_L
              match sl with
              | ann0 (Sp, L, rm) => ann0 (Sp, L, rm)
              | ann1 (Sp, L, rm) sl_s => ann1 (Sp, L, rm) (do_spill_rm slot sl_s)
              | ann2 (Sp, L, rm) sl_s sl_t =>
                  ann2 (Sp, L, rm) (do_spill_rm slot sl_s) (do_spill_rm slot sl_t)
              | annF (Sp, L, rm) sl_F sl_t =>
                  annF (Sp, L, rm) (do_spill_rm slot ⊝ sl_F) (do_spill_rm slot sl_t)
              end
              = do_spill_rm slot
                   (setTopAnn sl (fst (fst (getAnn sl)),
                                  of_list (tl (elements (snd (fst (getAnn sl))))),
                                  snd (getAnn sl)
                                 )
                   )
             ) as eq_dsr.
    {
      admit. (* solvable, maybe complicated *)
    }
    rewrite eq_dsr. clear eq_dsr.
    apply IHn_L.
    -- rewrite setTopAnn_setTopAnn.
       rewrite getAnn_setTopAnn.
       subst sl'. subst rm.
       simpl.
       apply strong_sls.
    -- rewrite getAnn_setTopAnn.
       simpl. subst Sp. assumption.
    -- rewrite getAnn_setTopAnn.
       simpl. admit. (* okay, needs lemma:          cardinal L = S n_L
                     -> cardinal (of_list (tl (elements (L)))) =   n_L *)
    * apply live_exp_sound_incl
        with (lv':=Exp.freeVars (Operation (Var (slot
                         (hd 0 (elements (snd (fst (getAnn sl))))))))).
      -- apply live_freeVars.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G.

- rewrite do_spill_rm_s with (n:=n_Sp + cardinal L).
  Focus 2. subst Sp. rewrite card_Sp.
           subst L. omega.

  rewrite do_spill_Sp. (*Lemma not yet proven*)
  Focus 2. subst Sp. clear - card_Sp. intro N.
           apply cardinal_Empty in N. omega.

  econstructor; fold spill_live.
  * assert (forall sl, add_nones (n_Sp + cardinal L)
              match sl with
              | ann0 (Sp, L, rm) => ann0 (Sp, L, rm)
              | ann1 (Sp, L, rm) sl_s => ann1 (Sp, L, rm) (do_spill_rm slot sl_s)
              | ann2 (Sp, L, rm) sl_s sl_t =>
                  ann2 (Sp, L, rm) (do_spill_rm slot sl_s) (do_spill_rm slot sl_t)
              | annF (Sp, L, rm) sl_F sl_t =>
                  annF (Sp, L, rm) (do_spill_rm slot ⊝ sl_F) (do_spill_rm slot sl_t)
              end
              = do_spill_rm slot
                   (setTopAnn sl (of_list (tl (elements (fst (fst (getAnn sl))))),
                                  snd (fst (getAnn sl)),
                                  snd (getAnn sl)
                                 )
                   )
             ) as eq_dsr.
    {
      admit. (* solvable, maybe complicated *)
    }
    rewrite eq_dsr. clear eq_dsr.
    apply IHn_Sp.
    -- rewrite setTopAnn_setTopAnn.
       rewrite getAnn_setTopAnn.
       subst sl'. subst rm.
       simpl.
       apply strong_sls.
    -- rewrite getAnn_setTopAnn.
       simpl. admit. (* okay, needs lemma:   cardinal L = S n_L
                     -> cardinal (of_list (tl (elements (L)))) =   n_L *)
    * apply live_exp_sound_incl
        with (lv':=Exp.freeVars (Operation (Var (
                         (hd 0 (elements (snd (fst (getAnn sl))))))))).
      -- apply live_freeVars.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G.
Admitted.


Lemma spill_live_sound
(k : nat)
(slot : var -> var) (*maybe needs restrictions*)
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
              (do_spill' slot s sl)
              (spill_live (slot_merge slot Λ) ZL G
                          (do_spill' slot s sl)
                          (discard_merge_sl slot (do_spill_rm slot sl))).

Proof.
intros aeFree spillSound lvSound.
(*induction (elements (fst (fst (getAnn sl)))).
general induction spillSound; inversion_clear lvSound; inversion_clear aeFree;
simpl.
 *)
(*
set (Sp := fst (fst (getAnn sl))).
set (L  := snd (fst (getAnn sl))).
set (rm := snd (getAnn sl)).
assert (getAnn sl = (Sp,L,rm)) as gA_sl.
{ induction sl; simpl in *; destruct a as [[Sp' L'] rm'];
    subst Sp; subst L; subst rm; simpl; reflexivity.
}
 *)
general induction lvSound;
  inversion_clear aeFree;
  inversion_clear spillSound;
  apply spill_live_sound_s; intros G'.
- rewrite do_spill_empty.
  rewrite do_spill_rm_empty''.
  rewrite discard_merge_sl_step; simpl.
  Focus 2. simpl. apply empty_1.
  Focus 2. simpl. apply empty_1.
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
  rewrite do_spill_rm_empty''.
  rewrite discard_merge_sl_step; simpl.
  Focus 2. simpl. apply empty_1.
  Focus 2. simpl. apply empty_1.
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
  rewrite do_spill_rm_empty''.
  rewrite discard_merge_sl_step; simpl.
  Focus 2. simpl. apply empty_1.
  Focus 2. simpl. apply empty_1.
  Focus 2. simpl. apply empty_1.
  Focus 2. simpl. apply empty_1.

  econstructor.
  + apply live_op_sound_incl with (lv':=Op.freeVars e).
    * apply Op.live_freeVars.
    * clear. cset_tac.
- admit.

Admitted.


enough (forall Sp' sl', Sp' ⊆ Sp
          -> sl'= setTopAnn sl (Sp',L,rm)
          -> live_sound Imperative ZL Lv (do_spill' slot s sl')
                    (spill_live (slot_merge slot Λ) ZL G (do_spill' slot s sl')
                                (discard_merge_sl slot (do_spill_rm slot sl')))
       ) as strong_Sp_sls.
{
  apply strong_Sp_sls with (Sp':=Sp).
  - eauto with cset.
  - symmetry. apply setTopAnn_eta. eauto.
}

intros Sp' sl' sub_Sp top_sl'.
assert (Sp' = fst (fst (getAnn sl'))) as HeqSp'.
{ rewrite top_sl'. rewrite getAnn_setTopAnn. simpl. eauto. }
assert (getAnn sl' = (Sp',L,rm)) as gA_sl'.
{
  rewrite top_sl'. rewrite getAnn_setTopAnn. reflexivity.
}

remember (cardinal Sp') as n_Sp'.
symmetry in Heqn_Sp'.
revert dependent sl'. revert dependent Sp'. revert G.
induction n_Sp'; intros G Sp' sub_Sp card_Sp' sl' top_sl' HeqSp' gA_sl'.
- enough (forall L' sl'', L' ⊆ L
           -> sl'' = setTopAnn sl' (Sp',L',rm)
           -> live_sound Imperative ZL Lv (do_spill' slot s sl'')
                    (spill_live (slot_merge slot Λ) ZL G (do_spill' slot s sl'')
                                (discard_merge_sl slot (do_spill_rm slot sl'')))
         ) as strong_L_sls.
  {
    apply strong_L_sls with (L':=L).
    - eauto with cset.
    - symmetry. apply setTopAnn_eta. eauto.
  }
  intros L' sl'' sub_L top_sl''.
  assert (L' = snd (fst (getAnn sl''))) as HeqL'.
  { rewrite top_sl''. rewrite getAnn_setTopAnn. simpl. eauto. }
  assert (Sp'= fst (fst (getAnn sl''))) as HeqSp''.
  { rewrite top_sl''. rewrite getAnn_setTopAnn. simpl. eauto. }
  assert (getAnn sl'' = (Sp',L',rm)) as gA_sl''.
  {
    rewrite top_sl''. rewrite getAnn_setTopAnn. reflexivity.
  }

  remember (cardinal L') as n_L'.
  symmetry in Heqn_L'.
  revert dependent sl''.
  revert dependent L'.
  revert G.
  induction n_L'; intros G L' sub_L card_L' sl'' top_sl'' HeqL' HeqSp'' gA_sl''.

  + assert (sl'' = setTopAnn sl (Sp',L',rm)) as top_sl.
    { rewrite top_sl''. rewrite top_sl'. rewrite setTopAnn_setTopAnn. eauto. }

    revert dependent sl''.
    revert spillSound.
    revert G R M.
    induction lvSound; intros G R M spillSound sl'';
      inversion_clear spillSound; inversion_clear aeFree;
        intros top_sl'' HeqL'' HeqSp'' gA_sl'' top_sl.
    * (*cbn zeta. intros _ sub_Sp Heq_sl' gA_sl' sub_L top_sl'' gA_sl'' Heq_sl''.*)
      simpl in sub_Sp, gA_sl', sub_L, top_sl'', gA_sl''.
      rewrite do_spill_empty.
      rewrite do_spill_rm_empty''.
      rewrite discard_merge_sl_step; simpl.
      rewrite top_sl.
      simpl.
      Focus 2. apply cardinal_Empty. rewrite <- HeqSp''. assumption.
      Focus 2. apply cardinal_Empty. rewrite <- HeqL''.  assumption.
      Focus 2. apply cardinal_Empty. rewrite <- HeqSp''. assumption.
      Focus 2. apply cardinal_Empty. rewrite <- HeqL''.  assumption.
      destruct rm ; econstructor.
      -- apply IHlvSound with (R:={x; R\K∪L0}) (M:=Sp0∪M); eauto.
         ++ econstructor.
      -- admit.
      -- admit.
      -- admit.
    * admit.
    * admit.
    * admit.
    * admit.
    (*
    revert dependent R.
    revert dependent M.
    induction lvSound.
    * simpl.
    assert (cardinal Sp = 0 /\ cardinal L = 0) as [card_Sp card_L].
    { clear - Heqn. split; omega. }
    assert (Empty Sp /\ Empty L) as [Empty_Sp Empty_L].
    { clear - card_Sp card_L. split; apply cardinal_Empty; eauto. }
    assert (elements Sp = nil /\ elements L = nil) as [nil_Sp nil_L].
    { split; apply elements_Empty; eauto. }

    rewrite nil_Sp. rewrite nil_L.
    rewrite write_spills_empty. rewrite write_loads_empty.


    rewrite <- Heqn. unfold add_nones.
    rewrite discard_merge_sl_1.
    simpl. econstructor.
    * eapply IHlvSound; eauto.
    * apply live_exp_sound_incl with (lv':=Exp.freeVars e).
      -- apply Exp.live_freeVars.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G. *)

  + rewrite do_spill_rm_s with (n:=n_L').
    Focus 2. rewrite <- HeqL'. rewrite <- HeqSp''.
             rewrite card_Sp'. rewrite card_L'. omega.

    rewrite do_spill_L. (* Lemma not yet proven *)
    Focus 2. rewrite <- HeqSp''. apply cardinal_Empty. eauto.
    Focus 2. rewrite <- HeqL'. clear - card_L'.
             intro N. apply cardinal_Empty in N. omega.

    econstructor; fold spill_live.
    * assert (forall sl, add_nones n_L'
              match sl with
              | ann0 (Sp, L, rm) => ann0 (Sp, L, rm)
              | ann1 (Sp, L, rm) sl_s => ann1 (Sp, L, rm) (do_spill_rm slot sl_s)
              | ann2 (Sp, L, rm) sl_s sl_t =>
                  ann2 (Sp, L, rm) (do_spill_rm slot sl_s) (do_spill_rm slot sl_t)
              | annF (Sp, L, rm) sl_F sl_t =>
                  annF (Sp, L, rm) (do_spill_rm slot ⊝ sl_F) (do_spill_rm slot sl_t)
              end
              = do_spill_rm slot
                   (setTopAnn sl (fst (fst (getAnn sl)),
                                  of_list (tl (elements (snd (fst (getAnn sl))))),
                                  snd (getAnn sl)
                                 )
                   )
             ) as eq_dsr.
      {
        admit. (* solvable, maybe complicated *)
      }
      rewrite eq_dsr. clear eq_dsr.
      apply IHn_L' with (L':=of_list (tl (elements (snd (fst (getAnn sl''))))));
        simpl; eauto.

      -- rewrite <- HeqL'. admit. (* easy *) (* needs lemma of_list_monotone *)
      -- rewrite <- HeqL'. admit. (* okay *) (* needs lemma of_list_tl_subset *)
      -- rewrite <- HeqSp''. rewrite <- HeqL'.
         rewrite gA_sl''. simpl. eauto.
         rewrite top_sl''. rewrite setTopAnn_setTopAnn. eauto.
      -- rewrite getAnn_setTopAnn. simpl. eauto.
      -- rewrite getAnn_setTopAnn. simpl. eauto.
      -- rewrite getAnn_setTopAnn. rewrite <- HeqSp''.
         rewrite <- HeqL'. rewrite gA_sl''. simpl. eauto.

    * apply live_exp_sound_incl
        with (lv':=Exp.freeVars (Operation (Var (slot
                         (hd 0 (elements (snd (fst (getAnn sl''))))))))).
      -- apply live_freeVars.
      -- clear. cset_tac.
    * rewrite <- HeqSp''. rewrite <- HeqL'. clear. cset_tac.
      (* this is not performant *)
    * apply spill_live_G.

- rewrite do_spill_rm_s with (n:=n_Sp').
  admit. admit. (* analogous *)

Admitted.



Print Syntax error: '.' expected after [vernac:command] (in [vernac_aux]).
















general induction lvSound;  inversion_clear spillSound;

inversion_clear aeFree as [x' e' s' eaFree_s
                          |e'
                          |e' s' t' aeFree_s eaFree_t
                          |f' Y' aeFree_var
                          |F' t' aeFree_F aeFree_t];
 clear sl; try rename sl0 into sl.

- remember (elements Sp) as xs.  remember (elements L) as ys.
  remember (cardinal Sp + cardinal L) as n.
  revert dependent Sp.
  revert dependent L.
  induction n; intros.
  + simpl.
    assert (cardinal Sp = 0 /\ cardinal L = 0) as [card_Sp card_L].
    { clear - Heqn. split; omega. }
    assert (Empty Sp /\ Empty L) as [Empty_Sp Empty_L].
    { clear - card_Sp card_L. split; apply cardinal_Empty; eauto. }
    assert (elements Sp = nil /\ elements L = nil) as [nil_Sp nil_L].
    { split; apply elements_Empty; eauto. }

    rewrite nil_Sp. rewrite nil_L.
    rewrite write_spills_empty. rewrite write_loads_empty.


    rewrite <- Heqn. unfold add_nones.
    rewrite discard_merge_sl_1.
    simpl. econstructor.
    * eapply IHlvSound; eauto.
    * apply live_exp_sound_incl with (lv':=Exp.freeVars e).
      -- apply Exp.live_freeVars.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G.

  + assert (cardinal Sp > 0 \/ cardinal L > 0) as SpL_non_zero.
    {
      clear - Heqn. decide (cardinal Sp = 0).
      - right. rewrite e in Heqn. simpl in Heqn. omega.
      - left. omega.
    }
    simpl.
    rewrite <- Heqxs. rewrite <- Heqys.
    change (add_nones (cardinal Sp + cardinal L) (ann1 (Sp, L, ⎣⎦) (do_spill_rm slot sl)))
           with (do_spill_rm slot (ann1 (Sp,L,None) sl)).
    rewrite do_spill_rm_s with (n:=cardinal Sp + cardinal L - 1).

    Focus 2.
      simpl.
      assert (cardinal Sp + cardinal L > 0) as SpL_gt0.
      { clear - Heqn. omega. }
      omega.

    rewrite discard_merge_sl_1.
    simpl.
    destruct xs.
    * simpl. destruct ys.
      -- admit. (* see above *)
      -- simpl. econstructor.
         ++ replace (write_loads slot ys (stmtLet x e (do_spill slot s sl)))
               with (do_spill slot (stmtLet x e s) (ann1 (∅,of_list ys,None) sl)).
            (*change (add_nones (cardinal Sp + cardinal L - 1)
                              (ann1 (Sp,L,None) (do_spill_rm slot sl)))
                   with (do_spill_rm slot (ann1 (Sp,L,None) sl)).
            apply IHn. *) admit. admit.
         ++

  (* *)

  induction xs,ys.
  + simpl.
    rewrite <- Heqxs. rewrite write_spills_empty.
    rewrite <- Heqys. rewrite write_loads_empty.

    change (live_sound Imperative ZL Lv (stmtLet x e (do_spill slot s sl))
             (spill_live (slot_merge slot Λ) ZL G (stmtLet x e (do_spill slot s sl))
               (discard_merge_sl slot (do_spill_rm slot (ann1 (Sp,L,None) sl))))).

    assert (  discard_merge_sl slot (do_spill_rm slot (ann1 (Sp,L,None) sl))
            = discard_merge_sl slot((ann1 (Sp,L,None) (do_spill_rm slot sl))))
                  as dms.
    {
      rewrite do_spill_rm_empty''; simpl; eauto.
      - apply elements_Empty. eauto.
      - apply elements_Empty. eauto.
    }

    rewrite dms.
    rewrite discard_merge_sl_1.
    simpl. econstructor.

    * eapply IHlvSound; eauto.
    * apply live_exp_sound_incl with (lv':=Exp.freeVars e).
      -- apply Exp.live_freeVars.
      -- cset_tac.
    * cset_tac.
    * apply spill_live_G.

  + simpl.
    rewrite <- Heqxs. simpl.
    rewrite <- Heqys. unfold write_loads. fold write_loads.
    change (live_sound Imperative ZL Lv
     (stmtLet v (Operation (Var (slot v)))
        (write_loads slot ys (stmtLet x e (do_spill slot s sl))))
     (spill_live (slot_merge slot Λ) ZL G
        (stmtLet v (Operation (Var (slot v)))
           (write_loads slot ys (stmtLet x e (do_spill slot s sl))))
        (discard_merge_sl slot
           (do_spill_rm slot (ann1 (Sp,L,None) sl))))).

    rewrite do_spill_rm_s with (n:= cardinal Sp + cardinal L - 1).
    Focus 2. simpl. admit.
    rewrite discard_merge_sl_1.

    simpl. econstructor.
    * admit. (* difficult *)
    * apply live_exp_sound_incl with (lv':=singleton (slot v)).
      -- econstructor. econstructor. cset_tac.
      -- cset_tac.
    * cset_tac.
    * apply spill_live_G.



         rewrite <- write_spills_empty
        with (slot:=slot) (s:=write_loads slot ys (stmtLet x e (do_spill slot s sl))).

      replace (write_spills slot nil (write_loads slot ys (stmtLet x e (do_spill slot s sl))))
      with (do_spill slot (stmtLet x e s) (ann1 (∅,of_list ys,None) sl)).

      eapply IHlvSound; eauto.
    assert ( do_spill_rm slot (ann1 (Sp,L,None) sl)
           = ann1 (∅,∅,None)
                  (do_spill_rm slot (ann1 (∅,of_list ys,None) sl))) as dms_cons.
    {
      rewrite do_spill_rm_s with (n:=cardinal Sp + cardinal L).
      Focus 2. simpl.
      -


(*+TODO+*)

    rewrite annEq.
    replace (((fix f (n : nat) (b : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕)) {struct n} :
               ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕) :=
               match n with
               | 0 => b
               | S n0 => ann1 (∅, ∅, ⎣⎦) (f n0 b)
               end) (cardinal Sp + cardinal L) (ann1 (Sp, L, ⎣⎦) (do_spill_rm slot sl)))) with (ann1 (∅,∅,None) (do_spill_rm slot sl)).
    Focus 2. rewrite emptySp. rewrite emptyL.
    apply do_spill_rm_empty.
    simpl.
    rewrite emptySp. rewrite emptyL.
    econstructor.
    * eapply IHspillSound; eauto.
    * apply live_exp_sound_incl with (lv':=Exp.freeVars e).
      -- apply Exp.live_freeVars.
      -- cset_tac.
    * eauto.
    * admit.
  + rewrite write_spills_empty.
    rewrite write_spills_empty in IHl.
    simpl. econstructor.
    * admit.
    * econstructor. econstructor. cset_tac.
    * eauto.
    * revert a. admit. (*this is unprovable*)
  + rewrite write_loads_empty.
    rewrite write_loads_empty in IHl.
    simpl. econstructor.
    * admit.
    * econstructor. econstructor. cset_tac.
    * eauto.
    * admit. (*this is unprovable*)
  + admit.
- induction (elements Sp); induction (elements L).
  + rewrite write_loads_empty. rewrite write_spills_empty.
    simpl. econstructor. apply Op.live_freeVars.
  + rewrite write_spills_empty.
    rewrite write_spills_empty in IHl.
    simpl. eapply LOpr.

- apply live_exp_sound_incl with (lv':=Exp.freeVars e).
  + apply Exp.live_freeVars.
  + cset_tac.
- admit.
- admit.
- econstructor. econstructor. cset_tac.
- simpl. induction (elements Sp), (elements L); simpl.
  + econstructor; eauto.
    * apply live_exp_sound_incl with (lv':=Exp.freeVars e).
      -- apply Exp.live_freeVars.
      -- cset_tac.
    * admit. (*Why do we need this condition?*)
  + admit.
  + admit.
  + admit.
- apply do_spill_empty_if in IHlvSound1.
  apply do_spill_empty_if.
  +
enough (forall sl1 sl2, live_sound Imperative ZL Lv (do_spill slot s1
   (ann2 (∅,∅,None) sl1 sl2))
   (spill_live slot Λ ZL (do_spill slot s1 (ann2 (∅,∅,None) sl1 sl2))
                                           (ann2 (∅,∅,None) sl1 sl2))
  -> live_sound Imperative ZL Lv (stmtIf e ).
   * apply H8.
eapply IHlvSound1. ; admit.
- econstructor; admit.
- econstructor. apply Op.live_freeVars.
- econstructor; admit.

Op.live_freeVars

Theorem spill_sound_correct L E E' : spill_sound k Lsl (R,M) s alv asl
-> (forall x : var, In x R -> E x = E' x)
-> (forall x : var, In x S -> E x = E' (slot x))
-> sim'r Bisim (L,E,s) (L,E', doSpill slot s asl).
