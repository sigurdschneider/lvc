Require Import Coq.Arith.Lt Coq.Arith.Plus Coq.Classes.RelationClasses List.
Require Import Util.

(** * AllInRel: Inductive characterization of lists which are element-wise in relation *)

Set Implicit Arguments.


Section AIR3.
  Variable X Y Z : Type.
  Variable R : list X -> Y -> Z -> Type.
  
  Inductive AIR3 
    : list X -> list Y -> list Z -> Type :=
  | AIR3_nil : AIR3 nil nil nil
  | AIR3_cons x XL y z (pf:R (x::XL) y z)
    (YL:list Y) (ZL:list Z) :
    AIR3 XL YL ZL ->
    AIR3 (x::XL) (y::YL) (z::ZL).

  Lemma AIR3_nth LT L L' l blkt : 
    AIR3 LT L L' 
    -> get LT l blkt
    -> {blk:Y & { blk':Z & (get L l blk * get L' l blk' * R (drop l LT) blk blk')%type } }.
  Proof.
    intros. revert l blkt X1.
    induction X0; intros; simpl. isabsurd.
    inv X1. eexists. eexists. 
    split; eauto using get.
    edestruct IHX0 as [blk [blk' [[A B] C]]]; eauto.
    eexists; eexists; repeat split; eauto using get.
  Qed.

  Lemma AIR3_drop LT L L' n 
    : AIR3 LT L L' -> AIR3 (drop n LT) (drop n L) (drop n L').
  Proof.
    revert LT L L'.
    induction n; simpl; intros; eauto.
    destruct L,L'; inv X0; simpl; eauto using AIR3.
  Qed.
  
End AIR3.



Section AIR4.
  Variable W X Y Z : Type.
  Variable R : list W -> list X -> Y -> Z -> Type.
  
  Inductive AIR4 
    : list W -> list X -> list Y -> list Z -> Type :=
  | AIR4_nil : AIR4 nil nil nil nil
  | AIR4_cons (w:W) (WL:list W) x XL y z (pf:R (w::WL) (x::XL) y z)
    (YL:list Y) (ZL:list Z) :
    AIR4 WL XL YL ZL ->
    AIR4 (w::WL) (x::XL) (y::YL) (z::ZL).

  Lemma AIR4_nth WL LT L L' l blkw blkt : 
    AIR4 WL LT L L' 
    -> get WL l blkw
    -> get LT l blkt
    -> {blk:Y & { blk':Z & (get L l blk * get L' l blk' * R (drop l WL) (drop l LT) blk blk')%type } }.
  Proof.
    intros. revert l blkt blkw X1 X2.
    induction X0; intros; simpl. isabsurd.
    inv X1. inv X2. eexists. eexists. 
    split; eauto using get.
    inv X2.
    edestruct IHX0 as [blk [blk' [[A B] C]]]; eauto.
    eexists; eexists; repeat split; eauto using get.
  Qed.

  Lemma AIR4_drop WL LT L L' n 
    : AIR4 WL LT L L' -> AIR4 (drop n WL) (drop n LT) (drop n L) (drop n L').
  Proof.
    revert WL LT L L'.
    induction n; simpl; intros; eauto.
    destruct L,L'; inv X0; simpl; eauto using AIR3.
  Qed.
  
End AIR4.


(*
Inductive AllInRel {X Y : Type} (R:X->Y->Type) 
 : list X -> list Y -> Prop :=
| AllInRel_nil : AllInRel R nil nil
| AllInRel_cons (x:X) (y:Y) (pf:R x y)
           (XL:list X) (YL:list Y) :
           AllInRel R XL YL ->
           AllInRel R (x::XL) (y::YL).


(* ** Basic Properties *)

Lemma AllInRel_refl {X:Type} {n':nat} {R:X->X->Prop} 
  (R_refl:forall x, R x x) (E:list X)
: AllInRel R E E.
induction E. constructor. constructor.
apply R_refl. exact IHE.
Qed.

Lemma AllInRel_trans {X:Type} {n':nat} {R:X->X->Prop} 
  (R_trans: forall x y z, R x y -> R y z -> R x z) 
  {E E' E'':list X} 
: AllInRel R E E' -> AllInRel R E' E'' -> AllInRel R E E''.
intros. revert E'' H0; induction H; intros; inversion H0; subst; eauto using @AllInRel.
Qed.

(* ** Interface with get and nth, nth_error, and nth_default *)

Lemma AllInRel_get {X Y:Type} {R:X->Y->Prop}
  (XL:list X) (YL:list Y) n x y
  : get XL n x -> get YL n y ->
  AllInRel R XL YL -> R x y.
Proof.
intros. revert XL YL H H0 H1. induction n; intros. inv H. inv H1. inv H0. assumption. 
inv H. inv H0. inv H1. eauto.
Qed.

Lemma AllInRel_nth_error {X Y:Type} {DX:Defaulted X} {R:X->Y->Prop}
  (XL:list X) (YL:list Y) n x y
  : get YL n y -> nth_error XL n = Some x ->
  AllInRel R XL YL -> R x y.
Proof.
intros. revert XL YL H H0 H1. induction n; intros. inv H. inv H1. inv H0. assumption.
inv H. inv H1. eauto.
Qed.

Lemma AllInRel_nth {X Y:Type} {DX:Defaulted X} {R:X->Y->Prop}
  (XL:list X) (YL:list Y) n x y
  : get YL n y ->
  AllInRel R XL YL -> R (nth n XL x) y.
Proof.
intros. revert XL YL H H0. induction n; intros. inv H. inv H0. unfold nth_default. unfold nth_error. simpl. assumption. 
inv H. inv H0. unfold nth_default. simpl. unfold nth_default in IHn. eauto.
Qed.

Lemma AllInRel_nth_default {X Y:Type} {DX:Defaulted X} {R:X->Y->Prop}
  (XL:list X) (YL:list Y) n x y
  : get YL n y ->
  AllInRel R XL YL -> R (nth_default x XL n) y.
Proof.
intros. revert XL YL H H0. induction n; intros. inv H. inv H0. unfold nth_default. unfold nth_error. simpl. assumption. 
inv H. inv H0. unfold nth_default. simpl. unfold nth_default in IHn. eauto.
Qed.

(* ** Relational Lifting with bottom in the form of (None:option X) *)
Inductive sndNoneOrR {X Y:Type} (R:X->Y->Prop) 
  : option X -> option Y -> Prop :=
| sndOpt_None (x:option X) : sndNoneOrR R x None
| sndOpt_Some (x:X) (y:Y) : R x y -> sndNoneOrR R (Some x) (Some y)
.

Inductive sndNoneOrRX {X Y:Type} (R:X->Y->Prop) 
  : X -> option Y -> Prop :=
| sndNoneOrRX_None (x:X) : sndNoneOrRX R x None
| sndNoneOrRX_Some (x:X) (y:Y) : R x y -> sndNoneOrRX R x (Some y)
.
*)
