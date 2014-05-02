Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Liveness Coherence ParamsMatch Sim MoreList Restrict ILIToILF.

Set Implicit Arguments.

Opaque compute_prop.

Definition addParam x (DL:list (set var)) (AP:list (set var)) := 
  zip (fun (DL:set var) AP => if [x ∈ DL] 
                   then {{x}} ∪ AP else AP) DL AP.

(*
Definition addParams Z DL (AP:list (set var)) := 
  fold_left (fun AP x => addParam x DL AP) Z AP.
*)

Definition addParams Z DL (AP:list (set var)) := 
  zip (fun DL AP => (of_list Z ∩ DL) ∪ AP) DL AP.

Definition oget {X} `{OrderedType X} (s:option (set X)) :=
  match s with Some s => s | None => ∅ end.

Definition addAdds s DL (AP:list (option (set var))) := 
  zip (fun (DL:set var) AP => mdo t <- AP; Some ((s ∩ DL) ∪ t)) DL AP.

Lemma addParam_length x DL AP
 : length DL = length AP
   -> length (addParam x DL AP) = length DL.
Proof.
  intros. unfold addParam. repeat rewrite zip_length.
  rewrite <- H. repeat rewrite Min.min_idempotent. eauto.
Qed.

Lemma addAdds_length Z DL AP
 : length DL = length AP
   -> length (addAdds Z DL AP) = length DL.
Proof.
  intros. unfold addAdds. rewrite zip_length. rewrite H.
  rewrite Min.min_idempotent. eauto.
Qed.

Definition killExcept f (AP:list (set var)) :=
  mapi (fun n x => if [n = counted f] then Some x else None) AP.

Definition ounion {X} `{OrderedType X} (s t: option (set X)) :=
  match s, t with 
    | Some s, Some t => Some (s ∪ t)
    | Some s, None => Some s
    | None, Some t => Some t
    | _, _ => None
  end.

Definition oto_list {X} `{OrderedType X} (s:option (set X)) :=
  match s with Some s => to_list s | None => nil end.
  

Fixpoint computeParameters (DL: list (set var)) (ZL:list (list var)) (AP:list (set var)) 
         (s:stmt) (an:ann (set var)) {struct s}
: ann (list var) * list (option (set var)) :=
  match s, an with
    | stmtExp x e s, annExp _ an => 
      let (ar, r) := computeParameters DL ZL (addParam x DL AP) s an in
      (annExp nil ar, r) 
    | stmtIf x s t, annIf _ ans ant => 
      let (ars, rs) := computeParameters DL ZL AP s ans in
      let (art, rt) := computeParameters DL ZL AP t ant in
      (annIf nil ars art, zip ounion rs rt)
    | stmtGoto f Y, annGoto lv => (annGoto nil, killExcept f AP)
    | stmtReturn x, annReturn _ => (annReturn nil, (mapi (fun _ _ => None) AP))
    | stmtLet Z s t, annLet lv ans ant =>
      let DL' := getAnn ans \ of_list Z in
      let (ars, rs) := computeParameters (DL' :: DL) 
                                        (Z :: ZL)
                                        (∅ :: addParams Z DL AP)
                                        s
                                        ans in
      let (art, rt) := computeParameters (DL':: DL) 
                                        (Z :: ZL)
                                        (∅:: AP) 
                                        t 
                                        ant in
      let ur := zip ounion rs rt in
      let ur' := (addAdds 
                  (oget (hd None ur))
                  (DL) (tl ur)) in 
      (annLet (oto_list (hd None ur)) ars art, ur')
    | s, a => (annReturn nil, nil)
  end.

Local Notation "≽" := (fstNoneOrR (flip Subset)).
Local Notation "≼" := (fstNoneOrR (Subset)).
Local Notation "A ≿ B" := (list_eq (fstNoneOrR (flip Subset)) A B) (at level 60).

Instance fstNoneOrR_flip_Subset_trans {X} `{OrderedType X} : Transitive ≽.
hnf; intros. inv H; inv H0.
- econstructor.
- inv H1. econstructor. transitivity y0; eauto.
Qed.

Instance fstNoneOrR_flip_Subset_trans2 {X} `{OrderedType X} : Transitive (fstNoneOrR Subset).
hnf; intros. inv H; inv H0.
- econstructor.
- inv H1. econstructor. transitivity y0; eauto.
Qed.

Instance list_eq_trans {A} (R : relation A) `{Transitive _ R} : 
  Transitive (list_eq R).
Proof.
  intros; hnf; intros. general induction H0.
  - inv H1. econstructor.
  - inv H2. econstructor. eauto. eauto.
Qed.

Instance instance_list_eq_sym {A} (R : relation A) `{Symmetric _ R} : 
  Symmetric (list_eq R).
Proof.
  intros; hnf; intros. general induction H0.
  - econstructor.
  - econstructor; eauto.
Qed.

Lemma trs_monotone (DL DL' : list (option (set var))) ZL s lv a
 : trs DL ZL s lv a
   -> DL ≿ DL'
   -> trs DL' ZL s lv a.
Proof.
  intros. general induction H; eauto using trs.
  + econstructor. 
    eapply IHtrs; eauto. eapply restrict_subset2; eauto. reflexivity.
  + destruct (list_eq_get H2 H); eauto; dcr. inv H5.
    econstructor; eauto. rewrite <- H1; eauto.
  + econstructor; eauto. 
    eapply IHtrs1. repeat rewrite restrict_incl; try reflexivity.
    constructor; eauto. reflexivity.
    eapply restrict_subset2; eauto. reflexivity.
    eapply IHtrs2. constructor; eauto. reflexivity.
Qed.

Lemma list_eq_get2 {X:Type} (L L':list X) eqA n x
  : list_eq eqA L L' -> get L' n x -> exists x', get L n x' /\ eqA x' x.
Proof.
  intros. general induction H.
  inv H0. 
  inv H1. eauto using get. 
  edestruct IHlist_eq; eauto. firstorder using get.
Qed.

Lemma list_eq_restrict A B s
:  A ≿ B 
   -> restrict A s ≿ B.
Proof.
  intros. general induction H; simpl.
  - econstructor.
  - econstructor; eauto. 
    + inv H; simpl. 
      * econstructor.
      * destruct if. econstructor; eauto. econstructor.
Qed.

Lemma to_list_nil {X} `{OrderedType X} 
  : to_list ∅ = nil.
Proof.
  eapply elements_Empty.
  cset_tac; intuition.
Qed.

Lemma list_eq_length A R l l'
  : @list_eq A R l l' -> length l = length l'.
Proof.
  intros. general induction H; simpl; eauto.
Qed.

Lemma trs_monotone3 (DL : list (option (set var))) AP AP' ZL s lv a
 : trs DL (zip (fun Z a => match a with Some a => Z++to_list a | None => Z end) ZL AP) s lv a
   -> list_eq (fstNoneOrR Subset) AP AP'
   -> trs DL (zip (fun Z a => match a with Some a => Z++to_list a | None => Z end) ZL AP') s lv a.
Proof.
  intros. general induction H; eauto using trs.
(*  + econstructor. 
    eapply IHtrs; eauto. eapply list_eq_restrict; eauto.*)
  + edestruct get_zip as  [? []]; eauto; dcr.
(*    destruct (list_eq_get2 H3 H7); eauto; dcr.*)
    destruct (list_eq_get H2 H5); eauto; dcr.
    exploit zip_get. eapply H3. eapply H7.
    econstructor. eauto. eapply X. eauto. 
  + econstructor; eauto.
    pose proof (IHtrs1 (Some ∅::AP) (Some ∅::AP') (Za::ZL0)) as A.
    Opaque to_list.
    simpl zip in A.
    rewrite to_list_nil in A. rewrite app_nil_r in A.
    eapply A. reflexivity. econstructor. reflexivity. eauto. 
    (*
    simpl. destruct if. econstructor. constructor.
    hnf. cset_tac; intuition. eapply list_eq_restrict; eauto.
    econstructor. econstructor. eapply list_eq_restrict; eauto.*)
    pose proof (IHtrs2 (Some ∅::AP) (Some ∅::AP') (Za::ZL0)) as A. 
    simpl zip in A. 
    rewrite to_list_nil in A. rewrite app_nil_r in A.
    eapply A. reflexivity. econstructor. reflexivity. eauto.
Qed.

Definition elem_eq {X} `{OrderedType X} (x y: list X) := of_list x [=] of_list y.

Instance elem_eq_refl {X} `{OrderedType X} : Reflexive elem_eq.
hnf; intros. hnf. cset_tac; intuition.
Qed.


Lemma trs_AP_seteq (DL : list (option (set var))) AP AP' s lv a
 : trs DL AP s lv a
   -> list_eq elem_eq AP AP'
   -> trs DL AP' s lv a.
Proof.
  intros. general induction H; eauto using trs.
  + destruct (list_eq_get H2 H0); eauto; dcr.
    econstructor; eauto.
  + econstructor. 
    - eapply IHtrs1. econstructor; eauto; reflexivity.
    - eapply IHtrs2. econstructor; eauto; reflexivity.
Qed.


Lemma trs_AP_incl (DL : list (option (set var))) AP AP' s lv a
 : trs DL AP s lv a
   -> list_eq (fun x y => of_list y ⊆ of_list x) AP AP'
   -> trs DL AP' s lv a.
Proof.
  intros. general induction H; eauto using trs.
  + destruct (list_eq_get H2 H0); eauto; dcr.
    econstructor; eauto.
  + econstructor. 
    - eapply IHtrs1. econstructor; eauto; reflexivity.
    - eapply IHtrs2. econstructor; eauto; reflexivity.
Qed.

Lemma trs_AP_incl' (DL : list (option (set var))) AP AP' s lv a
 : trs DL AP s lv a
   -> list_eq (fun x y => of_list x ⊆ of_list y) AP AP'
   -> trs DL AP' s lv a.
Proof.
  intros. general induction H; eauto using trs.
  + destruct (list_eq_get H2 H0); eauto; dcr.
    econstructor; eauto.
  + econstructor.
    - eapply IHtrs1. econstructor; eauto; reflexivity.
    - eapply IHtrs2. econstructor; eauto; reflexivity.
Qed.

Lemma list_eq_flip {X} (R:X->X->Prop) l l'
      : list_eq R l l'
        -> list_eq (flip R) l' l.
Proof.
  intros. general induction H.
  - econstructor.
  - econstructor; eauto.
Qed.

Definition map_to_list {X} `{OrderedType X} (AP:list (option (set X))) := List.map (fun a => match a with Some a => to_list a | None => nil end) AP.

Lemma list_eq_Subset_of_list (AP AP': list (option (set var)))
: list_eq (fstNoneOrR Subset) AP AP'
  -> list_eq (fun x y => of_list y ⊆ of_list x) (map_to_list AP') (map_to_list AP).
Proof.
  intros. general induction H; simpl.
  + econstructor.
  + econstructor. destruct a, a'; cset_tac; intuition.
    - rewrite of_list_3. rewrite of_list_3 in H1. inv H. intuition.
    - inv H.
    - exfalso; cset_tac; intuition. simpl in *. cset_tac; intuition.
    - eauto.
Qed.

Lemma trs_monotone3' (DL : list (option (set var))) AP AP' s lv a
 : trs DL (List.map oto_list AP) s lv a
   -> list_eq (fstNoneOrR Subset) AP AP'
   -> trs DL (List.map oto_list AP') s lv a.
Proof.
  intros. eapply trs_AP_incl'; eauto. eapply list_eq_flip.
  eapply list_eq_Subset_of_list; eauto.
Qed.


Lemma list_eq_addParam DL AP x
  : length AP = length DL
    -> PIR2 Subset AP (addParam x DL AP).
Proof.
  intros A. 
  eapply length_length_eq in A.
  general induction A.
  - constructor.
  - econstructor.
    + destruct if; cset_tac; intuition.
    + exploit (IHA x0); eauto.
Qed.



Lemma list_eq_map_some {X} R (AP AP':list X)
: length AP = length AP'
  -> list_eq R AP AP'
  -> list_eq (fstNoneOrR R) (List.map Some AP) (List.map Some AP').
Proof.
  intros. general induction H0. 
  + econstructor.
  + simpl. econstructor.
    - econstructor; eauto.
    - eauto.
Qed.

Lemma list_eq_map_some_option {X} R (AP AP':list X)
: length AP = length AP'
  -> list_eq R AP AP'
  -> list_eq (option_eq R) (List.map Some AP) (List.map Some AP').
Proof.
  intros. general induction H0. 
  + econstructor.
  + simpl. econstructor.
    - econstructor; eauto.
    - eauto.
Qed.

Lemma zip_length2 {X Y Z} {f:X->Y->Z} DL ZL
: length DL = length ZL
  -> length (zip f DL ZL) = length DL.
Proof.
  intros. rewrite zip_length. rewrite H. rewrite Min.min_idempotent. eauto.
Qed.

Lemma addParams_length Z DL AP
 : length DL = length AP
   -> length (addParams Z DL AP) = length DL.
Proof.
  unfold addParams; intros.
  rewrite zip_length2; congruence.
Qed.

Lemma list_eq_ounion {X} `{OrderedType X} (A B C:list (option (set X)))
: length A = length B
  -> length B = length C
  -> list_eq ≽ A C
  -> list_eq ≽ B C
  -> list_eq ≽ (zip ounion A B) C.
Proof.
  intros. eapply length_length_eq in H0. eapply length_length_eq in H1.
  general induction H0; inv H1; simpl.
  - econstructor.
  - simpl in *. inv H2; inv H3. 
    exploit IHlength_eq; eauto.
    inv H7; inv H8; simpl; try now (econstructor; [econstructor; eauto| eauto]).
    econstructor; eauto. econstructor. unfold flip in *.
    cset_tac; intuition.
Qed.

Lemma list_eq_ounion' {X} `{OrderedType X} (A B C:list (option (set X)))
: length A = length B
  -> length B = length C
  -> list_eq ≼ C A
  -> list_eq ≼ C B
  -> list_eq ≼ C (zip ounion A B).
Proof.
  intros. eapply length_length_eq in H0. eapply length_length_eq in H1.
  general induction H0; inv H1; simpl.
  - econstructor.
  - simpl in *. inv H2; inv H3. 
    exploit IHlength_eq; eauto.
    inv H7; inv H8; simpl; try now (econstructor; [econstructor; eauto| eauto]).
    econstructor; eauto. econstructor. unfold flip in *.
    cset_tac; intuition.
Qed.

Lemma list_eq_option_eq_Subset_zip {X} `{OrderedType X} (A B C:list (option (set X)))
: length A = length B
  -> length B = length C
  -> list_eq (option_eq Subset) C A
  -> list_eq (option_eq Subset) C B
  -> list_eq (option_eq Subset) C (zip ounion A B).
Proof.
  intros. eapply length_length_eq in H0. eapply length_length_eq in H1.
  general induction H0; inv H1; simpl.
  - econstructor.
  - simpl in *. inv H2; inv H3. 
    exploit IHlength_eq; eauto.
    inv H7; inv H8; simpl; try now (econstructor; [econstructor; eauto| eauto]).
    econstructor; eauto. econstructor. unfold flip in *.
    cset_tac; intuition.
Qed.


Lemma length_tl X (l:list X)
  : length (tl l) = length l - 1.
Proof.
  destruct l; simpl; eauto; omega.
Qed.

Definition lminus (s:set var) L := s \ of_list L.

Lemma addParam_zip_lminus_length DL ZL AP x
: length AP = length DL
  -> length DL = length ZL
  -> length (addParam x (zip lminus DL ZL) AP) = length DL.
Proof.
  intros. rewrite addParam_length; rewrite zip_length2; eauto.
Qed.

Lemma addParams_zip_lminus_length DL ZL AP Z
: length AP = length DL
  -> length DL = length ZL
  -> length (addParams Z (zip lminus DL ZL) AP) = length DL.
Proof.
  intros. rewrite addParams_length; rewrite zip_length2; eauto.
Qed.

Lemma computeParameters_length DL ZL AP s lv an' LV
:live_sound (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> length AP = length DL
  -> length DL = length ZL 
  -> length LV = length DL.
Proof. 
  intros LS CPEQ LEQ LEQ2. general induction LS; simpl in *; try let_case_eq; inv CPEQ.
  - rewrite LEQ. eapply IHLS; eauto. rewrite addParam_zip_lminus_length; eauto.
  - repeat let_case_eq; inv CPEQ.
    exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    repeat rewrite zip_length. rewrite X, X0. rewrite <- LEQ.
    rewrite Min.min_idempotent. eauto.
  - eapply mapi_length.
  - eapply mapi_length.
  - repeat let_case_eq; inv CPEQ.
    exploit IHLS2. Focus 2. instantiate (6:=getAnn als::DL).
    instantiate (5:=Z::ZL). eapply eq0. reflexivity. simpl. congruence.
    simpl; congruence. 
    exploit IHLS1. Focus 2. instantiate (6:=getAnn als::DL).
    instantiate (5:=Z::ZL). eapply eq. reflexivity. simpl. 
    rewrite addParams_zip_lminus_length. reflexivity. eauto. eauto.
    simpl; eauto.
    rewrite addAdds_length.
    rewrite zip_length. rewrite <- LEQ2, <- LEQ.
    rewrite Min.min_idempotent. omega.
    repeat rewrite zip_length. 
    assert (b1 = b2) by congruence. subst.
    rewrite length_tl. rewrite zip_length.
    rewrite X, X0. rewrite LEQ2. repeat rewrite Min.min_idempotent.
    simpl; omega.
Qed.

(*
Lemma list_eq_addAdds s DL b
: length DL = length b
  -> list_eq ≽ (addAdds s DL b) b.
Proof.
  intros. eapply length_length_eq in H.
  general induction H.
  - econstructor.
  - simpl. econstructor.
    + destruct if. 
      * destruct y; econstructor; reflexivity.
      * destruct y; simpl. econstructor; simpl. hnf. cset_tac; intuition.
        
    + eauto.
Qed.
*)

Instance instance_option_eq_trans_R X {R: relation X} `{Transitive _ R}
 : Transitive (option_eq R).
Proof.
  hnf; intros. inv H0; inv H1.
  + econstructor.
  + econstructor; eauto.
Qed.

Instance instance_option_eq_refl_R X {R: relation X} `{Reflexive _ R}
 : Reflexive (option_eq R).
Proof.
  hnf; intros. destruct x.
  + econstructor; eauto.
  + econstructor.
Qed.

Instance instance_option_eq_sym_R X {R: relation X} `{Symmetric _ R}
 : Symmetric (option_eq R).
Proof.
  hnf; intros. inv H0.
  + econstructor.
  + econstructor; eauto.
Qed.

Inductive ifSndR {X Y} (R:X -> Y -> Prop) : X -> option Y -> Prop :=
  | ifsndR_None x : ifSndR R x None
  | ifsndR_R x y : R x y -> ifSndR R x (Some y).

Lemma list_eq_ifSndR_right {X} `{OrderedType X} A B C
: PIR2 (ifSndR Subset) B A
-> PIR2 Subset C B
-> PIR2 (ifSndR Subset) C A.
Proof.
  intros. general induction H1; simpl in *.
  + inv H0. econstructor.
  + inv H0. inv pf0.
    - econstructor. 
      * econstructor.
      * eauto.
    - econstructor; eauto. econstructor; cset_tac; intuition.
Qed.


Lemma ifSndR_zip_ounion {X} `{OrderedType X} A B C
: PIR2 (ifSndR Subset) C A
  -> PIR2 (ifSndR Subset) C B
  -> PIR2 (ifSndR Subset) C (zip ounion A B).
Proof.
  intros. 
  general induction H0. 
  - inv H1; econstructor.
  - inv H1. 
    inv pf; inv pf0; simpl; try now (econstructor; [econstructor; eauto| eauto]).
    econstructor; eauto. econstructor.
    cset_tac; intuition.
Qed.

Lemma ifSndR_addAdds s DL A B
 : length DL = length A
   -> PIR2 (ifSndR Subset) A B
   -> PIR2 (ifSndR Subset) A (addAdds s DL B).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; inv H0; simpl.
  + constructor. 
  + econstructor; eauto.
    - inv pf; simpl; econstructor.
      * cset_tac; intuition.
Qed.


Lemma addParams_Subset Z DL AP
: length DL = length AP
  -> PIR2 Subset AP (addParams Z DL AP).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl.
  + econstructor.
  + econstructor; eauto.
    cset_tac; intuition.
Qed.


Lemma computeParameters_AP_LV DL ZL AP s lv an' LV
:live_sound (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> length AP = length DL
  -> length DL = length ZL
  -> PIR2 (ifSndR Subset) AP LV.
Proof.
  intros LS CPEQ LEQ. 
  general induction LS; simpl in * |- *; repeat let_case_eq; invc CPEQ.
  - exploit IHLS; eauto using addParam_zip_lminus_length.
    eapply list_eq_ifSndR_right. eapply X.
    eapply list_eq_addParam; eauto.
    rewrite zip_length2; eauto. 
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    exploit computeParameters_length; try eapply eq; eauto. 
    exploit computeParameters_length; try eapply eq0; eauto.
    eapply ifSndR_zip_ounion; eauto.
  - clear_all. unfold killExcept, mapi. generalize 0.
    general induction AP; simpl. econstructor.
    destruct if. econstructor. econstructor. firstorder. eauto.
    econstructor. econstructor. eauto.
  - clear_all. unfold mapi. generalize 0.
    general induction AP; simpl. econstructor.
    econstructor. econstructor. eauto.
  - exploit IHLS1. Focus 2. instantiate (6:=getAnn als::DL).
    instantiate (5:=Z::ZL). eapply eq. reflexivity. simpl. 
    rewrite addParams_zip_lminus_length; eauto. simpl; eauto.
    exploit IHLS2. Focus 2. instantiate (6:=getAnn als::DL).
    instantiate (5:=Z::ZL). eapply eq0. reflexivity. simpl. congruence.
    simpl; eauto. 
    inv X; inv X0. simpl.
    eapply ifSndR_addAdds. 
    rewrite zip_length2. eauto. eauto.
    eapply ifSndR_zip_ounion; eauto.
    eapply list_eq_ifSndR_right; eauto.
    eapply addParams_Subset. rewrite zip_length2; eauto.
Qed.

Instance PIR2_trans {X} (R:relation X) `{Transitive _ R} 
: Transitive (PIR2 R).
Proof.
  hnf; intros.
  general induction H0; simpl in *.
  + inv H1. econstructor.
  + inv H1.
    - econstructor; eauto.
Qed.

Inductive ifFstR {X Y} (R:X -> Y -> Prop) : option X -> Y -> Prop :=
  | IfFstR_None y : ifFstR R None y
  | IfFstR_R x y : R x y -> ifFstR R (Some x) y.

Lemma ifFstR_zip_ounion {X} `{OrderedType X} A B C
: PIR2 (ifFstR Subset) A C
  -> PIR2 (ifFstR Subset) B C
  -> PIR2 (ifFstR Subset) (zip ounion A B) C.
Proof.
  intros. 
  general induction H0. 
  - inv H1; econstructor.
  - inv H1. 
    inv pf; inv pf0; simpl; try now (econstructor; [econstructor; eauto| eauto]).
    econstructor; eauto. econstructor.
    cset_tac; intuition.
Qed.


Lemma ifFstR_addAdds s A B
: PIR2 (ifFstR Subset) B  A
  -> PIR2 (ifFstR Subset) (addAdds s A B) A.
Proof.
  intros. 
  general induction H; simpl.
  + constructor. 
  + econstructor; eauto.
    - inv pf; simpl; econstructor.
      * cset_tac; intuition.
Qed.

Lemma addParam_Subset x DL AP
: PIR2 Subset AP DL
  -> PIR2 Subset (addParam x DL AP) DL.
Proof.
  intros. general induction H; simpl.
  + constructor.
  + econstructor. destruct if; eauto. 
    cset_tac; intuition. hnf in H1; subst; eauto.
    eauto.
Qed.

Lemma addParams_Subset2 Z DL AP
: PIR2 Subset AP DL
  -> PIR2 Subset (addParams Z DL AP) DL.
Proof.
  intros. general induction H; simpl.
  + econstructor.
  + econstructor; eauto.
    cset_tac; intuition.
Qed.


Lemma computeParameters_LV_DL DL ZL AP s lv an' LV
:live_sound (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> length AP = length DL
  -> length DL = length ZL
  -> PIR2 Subset AP (zip lminus DL ZL)
  -> PIR2 (ifFstR Subset) LV (zip lminus DL ZL).
Proof.
  intros LS CPEQ LEQ. 
  general induction LS; simpl in * |- *; repeat let_case_eq; invc CPEQ.
  - exploit IHLS; eauto using addParam_zip_lminus_length.
    eapply addParam_Subset; eauto.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    exploit computeParameters_length; try eapply eq; eauto. 
    exploit computeParameters_length; try eapply eq0; eauto.
    eapply ifFstR_zip_ounion; eauto.
  - revert LEQ H4 H3. clear_all; intros. eapply length_length_eq in LEQ. 
    eapply length_length_eq in H3. 
    unfold killExcept, mapi. generalize 0.
    general induction LEQ; inv H3; simpl. econstructor. inv H4.
    destruct if; econstructor; eauto. constructor; eauto. 
    econstructor.
  - revert LEQ H0. clear_all. unfold mapi. generalize 0. intros.
    eapply length_length_eq in LEQ. eapply length_length_eq in H0. 
    general induction LEQ; inv H0; simpl.
    econstructor. 
    econstructor; try econstructor; eauto.
  - exploit IHLS1. Focus 2. instantiate (6:=getAnn als::DL).
    instantiate (5:=Z::ZL). eapply eq. reflexivity. simpl. 
    rewrite addParams_zip_lminus_length; eauto. simpl; eauto. simpl.
    econstructor; eauto. cset_tac; intuition. 
    eapply addParams_Subset2; eauto.
    exploit IHLS2. Focus 2. instantiate (6:=getAnn als::DL).
    instantiate (5:=Z::ZL). eapply eq0. reflexivity. simpl. congruence.
    simpl; eauto. econstructor; eauto. cset_tac; intuition.
    inv X; inv X0. simpl. 
    eapply ifFstR_addAdds; eauto.
    eapply ifFstR_zip_ounion; eauto.
Qed.

Lemma ounion_comm {X} `{OrderedType X} (s t:option (set X))
  : option_eq Equal (ounion s t) (ounion t s).
Proof.
  destruct s,t; simpl; try now econstructor.
  - econstructor. cset_tac; intuition.
Qed.

Lemma zip_list_eq X Y (eqA:Y -> Y -> Prop) (f:X -> X -> Y) l l'
  : (forall x y, eqA (f x y) (f y x))
    -> list_eq eqA (zip f l l') (zip f l' l).
Proof.
  general induction l; destruct l'; simpl; try now econstructor.
  econstructor; eauto.
Qed.

Lemma list_eq_zip_ounion {X} `{OrderedType X} (b:list (option (set X))) b'
  : length b = length b'
    -> list_eq (fstNoneOrR Subset) b (zip ounion b b').
Proof.
  intros. eapply length_length_eq in H0. 
  general induction H0; simpl.
  - econstructor.
  - econstructor; eauto.
    + destruct x,y; simpl; econstructor; cset_tac; intuition.
Qed.

Lemma list_eq_zip_ounion' {X} `{OrderedType X} (b:list (option (set X))) b'
  : length b = length b'
    -> list_eq (fstNoneOrR Subset) b (zip ounion b' b).
Proof.
  intros. eapply length_length_eq in H0. 
  general induction H0; simpl.
  - econstructor.
  - econstructor; eauto.
    + destruct x,y; simpl; econstructor; cset_tac; intuition.
Qed.

Definition ominus (s : set var) (t : option (set var)) := mdo t' <- t; ⎣s \ t' ⎦.

(*
Lemma zip_contra_ounion DL b b' 
  :  
    length DL = length b
    -> length b = length b'
    -> zip (fun (s : set var) (t : option (set var)) => mdo t' <- t; ⎣s \ t' ⎦)
          DL b
          ≿ zip (fun (s : set var) (t : option (set var)) => mdo t' <- t; ⎣s \ t' ⎦)
          DL (zip ounion b b').
Proof. 
  intros. eapply length_length_eq in H. eapply length_length_eq in H0.
  general induction H; inv H0; simpl. 
  - reflexivity.
  - econstructor; eauto.
    + destruct y, y0; simpl; econstructor; unfold flip; cset_tac; intuition.
Qed.
*)

Lemma zip_ominus_contra DL b b' 
  : length DL = length b
    -> length b = length b'
    -> list_eq (fstNoneOrR Subset) b b'
    -> zip ominus DL b ≿ zip ominus DL b'.
Proof. 
  intros. eapply length_length_eq in H. eapply length_length_eq in H0.
  general induction H; inv H0; simpl. 
  - reflexivity.
  - econstructor; eauto.
    + destruct y, y0; simpl; try now econstructor. 
      * inv H1. inv H5. econstructor. unfold flip; cset_tac; intuition.
      * inv H1. inv H5.
    + inv H1. eauto.
Qed.

Lemma addParam_x DL AP x n ap' dl
  : get (addParam x DL AP) n ap'
    -> get DL n dl
    -> x ∉ ap' -> x ∉ dl.
Proof.
  unfold addParam; intros.
  edestruct get_zip as [? []]; eauto; dcr. clear H.
  repeat get_functional; subst.
  destruct if in H2; simpl in *. 
  + cset_tac; intuition.
  + cset_tac; intuition.
Qed.

Lemma list_eq_not_in LV x DL AP
: length DL = length AP
  -> PIR2 (ifSndR Subset) (addParam x DL AP) LV
  ->  forall (n : nat) (lv0 dl : set var),
       get LV n ⎣lv0 ⎦ -> get DL n dl -> x ∉ lv0 -> x ∉ dl.
Proof.
  intros LEN LEQ. intros. eapply length_length_eq in LEN.
  general induction n; simpl in *.
  - inv H; inv H0. invc LEN. simpl in LEQ. invc LEQ.
    destruct if in pf; inv pf.
    + exfalso; cset_tac; intuition.
    + eauto.
  - invc H; invc H0. invc LEN. simpl in LEQ. invc LEQ.
    eauto.
Qed.

Lemma zip_bounded DL LV lv x
: length DL = length LV
  -> bounded (List.map Some DL) lv
  -> (forall n lv dl, get LV n (Some lv) -> get DL n dl -> x ∉ lv -> x ∉ dl)
  -> bounded (zip (fun (s : set var) (t : option (set var)) => mdo t' <- t; ⎣s \ t' ⎦) DL LV) (lv \ {{ x }} ).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl; eauto.
  destruct y; simpl in * |- *. 
  + split.
    - destruct_prop (x0 ∈ s). 
      * cset_tac; intuition. intro; intuition.
      * exploit H1; eauto using get. cset_tac; intuition.
    - destruct H0; eapply IHlength_eq; eauto.
      intros. eauto using get.
  + eapply IHlength_eq; eauto using get. intuition.
Qed.


Lemma restrict_zip_ominus DL LV lv x al
:  length DL = length LV
-> (forall n lv dl, get LV n (Some lv) -> get DL n dl -> x ∉ lv -> x ∉ dl)
-> al \ {{x}} ⊆ lv
->  restrict (zip ominus DL LV) al
 ≿ restrict (zip ominus DL LV) (lv \ {{x}}).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl in *.
  - econstructor.
  - econstructor.
    + destruct y; intros; simpl.
      repeat destruct if; try now econstructor.
      * econstructor. reflexivity.
      * destruct_prop (x0 ∈ s). exfalso. eapply n.
        hnf; intros. destruct_prop (a === x0). rewrite e in H2.
        exfalso; cset_tac; intuition.
        rewrite <- H1.
        cset_tac; intuition. 
        exploit H0; eauto using get.
        exfalso. eapply n. rewrite <- H1. cset_tac; intuition.
      * econstructor.
    + eapply IHlength_eq; eauto using get.
Qed.

Lemma restrict_zip_ominus' DL LV lv x al
:  length DL = length LV
-> (forall n lv dl, get LV n (Some lv) -> get DL n dl -> x ∉ lv -> x ∉ dl)
-> al \ {{x}} ⊆ lv
->  restrict (zip ominus DL LV) al
 ≿ restrict (zip ominus DL LV) (lv \ {{x}}).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl in *.
  - econstructor.
  - econstructor.
    + destruct y; intros; simpl.
      repeat destruct if; try now econstructor.
      * econstructor. reflexivity.
      * destruct_prop (x0 ∈ s). exfalso. eapply n.
        hnf; intros. destruct_prop (a === x0). rewrite e in H2.
        exfalso; cset_tac; intuition.
        rewrite <- H1.
        cset_tac; intuition. 
        exploit H0; eauto using get.
        exfalso. eapply n. rewrite <- H1. cset_tac; intuition.
      * econstructor.
    + eapply IHlength_eq; eauto using get.
Qed.

Lemma get_mapi_impl X Y L (f:nat->X->Y) n x k
 : get L n x
   -> get (mapi_impl f k L) n (f (n+k) x).
Proof.
  intros. general induction H; simpl; eauto using get.
  econstructor. orewrite (S (n + k) = n + (S k)). eauto.
Qed.

Lemma get_mapi X Y L (f:nat->X->Y) n x
 : get L n x
   -> get (mapi f L) n (f n x).
Proof.
  intros. exploit (get_mapi_impl f 0 H); eauto.
  orewrite (n + 0 = n) in X0. eauto.
Qed.

Lemma killExcept_get l AP s
: get AP (counted l) s -> 
  get (killExcept l AP) (counted l) (Some s).
Proof.
  intros. exploit (get_mapi (fun (n : nat) (x : set var) => if [n = counted l] then ⎣x ⎦ else ⎣⎦) H); eauto.
  destruct if in X; eauto.
  exfalso; eauto.
Qed.
    
Lemma restrict_get L s t n
: get L n (Some s)
  -> s ⊆ t
  -> get (restrict L t) n (Some s).
Proof.
  intros. general induction H; simpl.
  + destruct if.
    - econstructor.
    - exfalso; eauto.
    + econstructor; eauto.
Qed.

Transparent addAdds.


Lemma list_eq_addAdds s DL b
: length DL = length b
  -> list_eq ≼ b (addAdds s DL b).
Proof.
  intros. eapply length_length_eq in H.
  general induction H.
  - econstructor.
  - simpl. econstructor.
    + destruct y.
      * econstructor. cset_tac; intuition.
      * constructor.
    + eauto.
Qed.

Ltac length_equify := 
  repeat (match goal with
            | [ H : length ?A = length ?B |- _ ] => 
              eapply length_length_eq in H
          end).


Lemma computeParameters_trs DL ZL AP s an' LV lv
: length DL = length ZL
  -> length ZL = length AP
  -> live_sound (zip pair DL ZL) s lv
  -> computeParameters (zip lminus DL ZL) ZL AP s lv = (an', LV)
  -> PIR2 Subset AP (zip lminus DL ZL)
  -> trs (restrict (zip ominus (zip lminus DL ZL) LV) (getAnn lv))
        (List.map oto_list LV)  s lv an'.
Proof.
  intros. general induction H1; simpl in *.
  - let_case_eq. inv H4.
    eapply trsExp. 
    eapply trs_monotone.
    eapply IHlive_sound; try eapply eq; eauto using addParam_Subset. 
    rewrite addParam_length. rewrite zip_length.
    rewrite <- H2. rewrite Min.min_idempotent. eauto.
    rewrite zip_length2; congruence.
    exploit computeParameters_AP_LV; eauto; try congruence.
    eapply addParam_zip_lminus_length; congruence.
    exploit computeParameters_length; eauto; try congruence.
    eapply addParam_zip_lminus_length; congruence.
    rewrite restrict_comp_meet. 
    assert (SEQ:lv ∩ (lv \ {{x}}) [=] lv \ {{x}}) by (cset_tac; intuition).
    rewrite SEQ. eapply restrict_zip_ominus; eauto.
    rewrite zip_length2; eauto.
    eapply list_eq_not_in; try eapply X. rewrite zip_length2; congruence.
  - repeat let_case_eq. invc H4. 
    exploit computeParameters_length; eauto; try congruence. congruence.
    exploit computeParameters_length; try eapply eq; eauto; try congruence. 
    congruence.
    econstructor.
    + eapply trs_monotone.
      eapply trs_monotone3'.
      eapply IHlive_sound1; try eapply eq; eauto; try congruence. 
      eapply list_eq_zip_ounion. congruence.
      eapply restrict_subset2; eauto. 
      eapply zip_ominus_contra; try congruence.
      rewrite zip_length2; congruence.
      rewrite zip_length2; congruence.
      eapply list_eq_zip_ounion; congruence.
    + eapply trs_monotone.
      eapply trs_monotone3'.
      eapply IHlive_sound2; try eapply eq0; eauto.
      eapply list_eq_zip_ounion'. congruence.
      eapply restrict_subset2; eauto.
      eapply zip_ominus_contra; eauto. 
      rewrite zip_length2; congruence.
      rewrite zip_length2; congruence.
      eapply list_eq_zip_ounion'; congruence.
  - edestruct get_zip as [? [? []]]; dcr; eauto. inv H10.
    edestruct (get_length_eq _ H9 H4).
    exploit killExcept_get; eauto.
    exploit (zip_get lminus). eapply H7. apply H9.
    exploit (zip_get ominus). eapply X0. eapply X. 
    exploit map_get_1. eapply X.
    econstructor.
    eapply restrict_get. eapply X1. unfold lminus. cset_tac; intuition.
    eapply X2. unfold lminus. cset_tac; intuition.
  - econstructor.
  - repeat let_case_eq. invc H4.
    exploit (computeParameters_length (getAnn als::DL) (Z::ZL)); try eapply eq0; simpl; eauto; try congruence. 
    exploit (computeParameters_length (getAnn als::DL) (Z::ZL)); try eapply eq; simpl; eauto; try congruence. 
    rewrite addParams_zip_lminus_length; congruence.
    exploit (computeParameters_LV_DL (getAnn als::DL) (Z::ZL)); try eapply eq;
    simpl; eauto.
    rewrite addParams_zip_lminus_length; congruence.
    econstructor; eauto. cset_tac; intuition.
    eapply addParams_Subset2; eauto.
    exploit (computeParameters_LV_DL (getAnn als::DL) (Z::ZL)); try eapply eq0;
    simpl; eauto.
    congruence.
    econstructor; eauto. cset_tac; intuition.
    econstructor.
    + inv X1; inv X2.
      exploit trs_monotone3'.
      eapply (IHlive_sound1 (getAnn als::DL) (Z::ZL)); simpl; eauto; try congruence.
      simpl. rewrite addParams_zip_lminus_length; congruence.
      econstructor. cset_tac; intuition.
      eapply addParams_Subset2; eauto.
      instantiate (1:=addAdds (oget (ounion x x0))
                              ((getAnn als \ of_list Z) :: zip lminus DL ZL)
                              (ounion x x0 :: zip ounion XL XL0)).
      simpl.
      econstructor.  unfold lminus in *.
      inv pf; inv pf0; econstructor; simpl.
      clear_all; cset_tac; intuition.
      clear_all; cset_tac; intuition.
      simpl in *.
      transitivity (zip ounion XL XL0).
      eapply list_eq_zip_ounion; congruence.
      eapply list_eq_addAdds. repeat rewrite zip_length2; congruence.
      eapply trs_monotone. simpl.
      simpl addAdds in X3. 
      destruct (ounion x x0). simpl in *.
      assert (s0 ∩ (getAnn als \ of_list Z) ∪ s0 [=] s0).
      cset_tac; intuition. eapply trs_AP_seteq. eapply X3.
      econstructor; try reflexivity. unfold elem_eq.
      repeat rewrite of_list_3. rewrite H4. 
      reflexivity. 
      simpl in X3. eapply X3.
      simpl.
      econstructor. destruct if. 
      destruct x, x0; simpl; try now econstructor.
      * repeat destruct if; unfold lminus in * |- *. econstructor.
      unfold flip; clear_all. repeat rewrite of_list_app.
      rewrite of_list_3. cset_tac; intuition.
      exfalso; intuition.
      * unfold lminus. destruct if. 
        econstructor.
        unfold flip; clear_all. repeat rewrite of_list_app.
        rewrite of_list_3. cset_tac; intuition.
        econstructor.
      * exfalso. eapply n. reflexivity.
      * rewrite restrict_comp_meet. 
        assert (lv ∩ (getAnn als \ of_list (Z ++ oto_list (ounion x x0)))
               [=] (getAnn als \ of_list (Z ++ oto_list (ounion x x0)))).
        repeat rewrite of_list_app. cset_tac; intuition.
        rewrite H4. 
        exploit (computeParameters_AP_LV (getAnn als::DL) (Z::ZL)); try eapply eq; simpl; eauto; simpl; eauto; try congruence.
        rewrite addParams_zip_lminus_length; congruence.
        simpl in *.
        assert (length XL = length XL0) by congruence. inv X4.  
        revert H2 H3 H6 pf pf0 H H7 H8 H10. clear_all.
        repeat rewrite of_list_app. 
        intros.  
        length_equify. 
        general induction H; inv H0; inv H1; inv H5; inv H6; inv H7; simpl; try econstructor; eauto.
        inv H2; inv H3; inv pf; inv pf0; inv pf1; simpl; try now econstructor.
        {repeat destruct if; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. cset_tac; intuition. }
        {repeat destruct if; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. cset_tac; intuition. }
        {repeat destruct if; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
        {repeat destruct if; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
        {repeat destruct if; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
        {repeat destruct if; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
        {repeat destruct if; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
        {repeat destruct if; try now (econstructor; hnf; cset_tac; intuition).
        exfalso. eapply n. repeat rewrite of_list_3. cset_tac; intuition. }
   +  inv X1; inv X2.
      exploit trs_monotone3'.
      eapply (IHlive_sound2 (getAnn als::DL) (Z::ZL)); simpl; eauto; simpl; try congruence.
      econstructor. cset_tac; intuition. eauto.
      instantiate (1:=addAdds (oget (ounion x x0))
                              ((getAnn als \ of_list Z) :: zip lminus DL ZL)
                              (ounion x x0 :: zip ounion XL XL0)).
      simpl. econstructor. 
      destruct x,x0; simpl; econstructor.
      clear_all; cset_tac; intuition.
      clear_all; cset_tac; intuition.
      simpl.       simpl in *.
      transitivity (zip ounion XL XL0). 
      eapply list_eq_zip_ounion'; eauto; congruence.
      eapply list_eq_addAdds. repeat rewrite zip_length2; eauto; congruence.
      eapply trs_monotone. simpl in X1. 
      simpl. destruct (ounion x x0). simpl in *. 
      eapply trs_AP_seteq. eapply X3.
      econstructor; try reflexivity. unfold elem_eq. repeat rewrite of_list_3. 
      cset_tac; intuition. 
      eapply X3. 
      econstructor. destruct x,x0. simpl. 
      destruct if. unfold lminus. econstructor. 
      unfold flip; clear_all. repeat rewrite of_list_app.
      rewrite of_list_3. cset_tac; intuition.
      econstructor.
      simpl. econstructor.
      simpl. destruct if. 
      constructor. unfold flip, lminus; clear_all. repeat rewrite of_list_app.
      rewrite of_list_3. cset_tac; intuition.
      econstructor.                        
      simpl. simpl in *. econstructor.
      eapply restrict_subset2; eauto. 
      eapply zip_ominus_contra.
      rewrite zip_length2; eauto. simpl in *; congruence.
      rewrite addAdds_length. rewrite zip_length2; eauto.
      repeat rewrite zip_length2; eauto. 
      simpl. simpl in *. rewrite zip_length2; eauto; congruence.
      eapply list_eq_trans. eapply fstNoneOrR_flip_Subset_trans2.
      eapply list_eq_zip_ounion'. Focus 2.
      eapply list_eq_addAdds. simpl.
      repeat rewrite zip_length2; eauto. simpl in *. congruence. 
      simpl in *. congruence. simpl in *. congruence.
Qed.

Print Assumptions computeParameters_trs.

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)

