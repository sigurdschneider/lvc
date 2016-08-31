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

Definition discard_sl := mapAnn (fun (a : (* = mapAnn ? snd *)
      set var * set var * option (list (set var * set var)))
                                           => match a with (_,_,rm) => rm end).

Definition discard_merge_sl (slot : var -> var) :=
mapAnn (fun (a : set var * set var * option (list (set var * set var)))
         => match a with
            | (_,_,None)
              => None
            | (_,_,Some rms)
              => Some ((fun rm => match rm with
                                  | (R,M) => R ∪ map slot M
                                  end) ⊝ rms)
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
(*
Lemma do_spill_empty_let
(slot : var -> var)
(Λ : list (set var * set var))
(ZL : list params)
(Lv : list (set var))
(x : var)
(e : exp)
(s : stmt)
(sl : ann (set var * set var * option (list (set var * set var))))
:    live_sound Imperative ZL Lv
          (do_spill slot (stmtLet x e s) (ann1 (∅,∅,None) sl))
     (spill_live slot Λ ZL
          (do_spill slot (stmtLet x e s) (ann1 (∅,∅,None) sl))
          (ann1 None (discard_sl sl)))

  -> live_sound Imperative ZL Lv
          (stmtLet x e (do_spill slot s sl))
     (spill_live slot Λ ZL
          (stmtLet x e (do_spill slot s sl))
          (ann1 None (discard_sl sl))).
Proof.
intros lvSound.
simpl.
inversion_clear lvSound.
rewrite elements_empty in H.
rewrite write_loads_empty in H.
rewrite write_spills_empty in H.

rewrite elements_empty in H0.
rewrite write_loads_empty in H0.
rewrite write_spills_empty in H0.

rewrite elements_empty in H1.
rewrite write_loads_empty in H1.
rewrite write_spills_empty in H1.

rewrite elements_empty in H2.
rewrite write_loads_empty in H2.
rewrite write_spills_empty in H2.

simpl in *.

econstructor; simpl; eauto.
Qed.

Lemma do_spill_empty_let'
(slot : var -> var)
(Λ : list (set var * set var))
(ZL : list params)
(Lv : list (set var))
(x : var)
(e : exp)
(s : stmt)
(lv : ann (set var))
(sl : ann (set var * set var * option (list (set var * set var))))
:    live_sound Imperative ZL Lv
          (do_spill slot (stmtLet x e s) (ann1 (∅,∅,None) sl))
          lv

  -> live_sound Imperative ZL Lv
          (stmtLet x e (do_spill slot s sl))
          lv.
Proof.
intros lvSound.
simpl.
inversion_clear lvSound.
rewrite elements_empty in H.
rewrite write_loads_empty in H.
rewrite write_spills_empty in H.

rewrite elements_empty in H0.
rewrite write_loads_empty in H0.
rewrite write_spills_empty in H0.

rewrite elements_empty in H1.
rewrite write_loads_empty in H1.
rewrite write_spills_empty in H1.

rewrite elements_empty in H2.
rewrite write_loads_empty in H2.
rewrite write_spills_empty in H2.

simpl in *.

econstructor; simpl; eauto.
Qed.

Lemma do_spill_empty_if
(slot : var -> var)
(Λ : list (set var * set var))
(ZL : list params)
(Lv : list (set var))
(lv : ann (set var))
(e : op)
(s t : stmt)
(sl_s sl_t : ann (set var * set var * option (list (set var * set var))))
:    live_sound Imperative ZL Lv
          (do_spill slot (stmtIf e s t) (ann2 (∅,∅,None) sl_s sl_t))
          lv

  -> live_sound Imperative ZL Lv
          (stmtIf e (do_spill slot s sl_s) (do_spill slot t sl_t))
          lv.
Proof.
intros lvSound.
simpl.
inversion_clear lvSound.

rewrite elements_empty in H.
rewrite write_loads_empty in H.
rewrite write_spills_empty in H.

rewrite elements_empty in H0.
rewrite write_loads_empty in H0.
rewrite write_spills_empty in H0.

rewrite elements_empty in H1.
rewrite write_loads_empty in H1.
rewrite write_spills_empty in H1.

simpl in *.

econstructor; simpl; eauto.
Qed.
*)
(*
Lemma do_spill_empty
(slot : var -> var)
(Λ : list (set var * set var))
(ZL : list params)
(Lv : list (set var))
(s : stmt)
(sl : ann (set var * set var * option (list (set var * set var))))
: live_sound Imperative ZL Lv (do_spill slot s sl)
        (spill_live slot Λ ZL (do_spill slot s sl) sl)
    -> fst (getAnn sl) === (∅,∅) ->
 match s, sl with
  | stmtLet x e t, ann1 (_,_,_) sl_t
    => live_sound Imperative ZL Lv (stmtLet x e (do_spill slot t sl_t))
             (spill_live slot Λ ZL (stmtLet x e (do_spill slot t sl_t)) sl)
  | stmtIf e t v, ann2 (_,_,_) sl_t sl_v
    => live_sound Imperative ZL Lv (stmtIf e (do_spill slot t sl_t)
                                             (do_spill slot v sl_v))
             (spill_live slot Λ ZL (stmtIf e (do_spill slot t sl_t)
                                             (do_spill slot v sl_v)) sl)
  | _,_ => True
end.
Proof.
intros lvSound fstEmpty.
destruct s,sl ; simpl; eauto.
- intros.


apply IHlvSound; simpl.
- admit.
- admit.
Admitted.

 *)


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


Definition slot_merge slot := List.map (fun (RM : set var * set var)
                                           => fst RM ∪ map slot (snd RM)).

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
              (do_spill slot s sl)
              (spill_live (slot_merge slot Λ) ZL G
                          (do_spill slot s sl)
                          (discard_merge_sl slot (do_spill_rm slot sl))).

Proof.
intros aeFree spillSound lvSound.
(*induction (elements (fst (fst (getAnn sl)))).
general induction spillSound; inversion_clear lvSound; inversion_clear aeFree;
simpl.
 *)

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
  induction n; intros; simpl.
  + assert (cardinal Sp = 0 /\ cardinal L = 0) as [card_Sp card_L].
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
      -- cset_tac.
    * cset_tac.
    * apply spill_live_G.

  + rewrite <- Heqxs. rewrite <- Heqys.
    rewrite do_spill_rm_s with (n:=cardinal Sp + cardinal L - 1).
    Focus 2. (* unprovable ?! *)
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
