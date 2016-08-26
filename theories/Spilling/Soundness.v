Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI Spilling.

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

Fixpoint do_spill_rm
(slot : var -> var)
(sl: ann (set var * set var * option (list (set var * set var ))))
: ann (set var * set var * option (list (set var * set var)))
:=
let add_nones := (fix f (n:nat)
                        (b:ann(set var * set var * option(list(set var * set var))))
                      := match n with
                         |   0  => b
                         | S(n) => ann1 (∅,∅,None) (f n b) end) in
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

| _,_ => ann0 ∅

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

general induction lvSound; inversion_clear spillSound;

inversion_clear aeFree as [x' e' s' eaFree_s
                          |e'
                          |e' s' t' aeFree_s eaFree_t
                          |f' Y' aeFree_var
                          |F' t' aeFree_F aeFree_t]. simpl; eauto.
(*
induction (elements Sp); induction (elements L).
- admit.
- admit.
- admit.
-
try rewrite write_loads_empty; try rewrite write_spills_empty; simpl; eauto;*)

- (*revert dependent sl.*) induction (elements Sp); induction (elements L).
  (*intros sl0 H7.*)
  + rewrite write_spills_empty. rewrite write_loads_empty.
    simpl. econstructor.
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
