Require Import Le Plus List Setoid Coq.Arith.Compare.
Require Import Val Env Map EnvTy AllInRel IL IL_raise AutoIndTac.

Open Scope map_scope.

Set Implicit Arguments.

Definition typelist := list ty.

Inductive argsOfType (ET:onv ty) : args -> typelist -> Type :=
| WTA_nil : argsOfType ET nil nil
| WTA_cons x t Y YT : argsOfType ET Y YT -> ET [x] = Some t -> 
  argsOfType ET (x::Y) (t::YT).

(*
Definition argsOfType (ET:onv ty) (args:env var) ET' 
  := agree_on (image _ args) ET ET'.*)


Lemma argsOfType_subEnv ET ET' Y Z
  : argsOfType ET' Y Z -> subEnv ET' ET -> argsOfType ET Y Z.
Proof.
  intros. general induction X; eauto using argsOfType.
Qed.

(*
Lemma argsOfType_length ET Y Z
  : argsOfType ET Y Z
  -> length Y = length Z.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma argsOfType_length_eq ET Y ZT
  : argsOfType ET Y ZT -> length_eq Y ZT.
Proof.
  intros. general induction X; eauto using length_eq.
Qed.
*)
(*
Fixpoint updET (ET:onv ty) (Z:params) (ZT:typelist) := 
  match Z, ZT with 
    | x::Z, t::ZT => (updET ET Z ZT)[x<-Some t]
    | _, _ => ET
  end.

Lemma updET_no_param ET Z ZT x
  : x ∉ fromList Z
  -> updET ET Z ZT [x] = ET[x].
Proof.
  intros. general induction Z; destruct ZT; simpl; eauto. 
  destruct_prop (a=x); subst; simplify lookup.
  exfalso; eapply H. simpl; cset_tac; firstorder.
  simpl in H. assert (~x ∈ fromList Z) by (cset_tac; firstorder).
  eauto.
Qed.

Fixpoint updD' (D:env nat) (Z:params) := 
  match Z with 
    | x::Z => (updD' D Z)[x<-S (D[x])]
    | _ => D
  end.
*)

Definition updET X (ET : onv X) (ZT : list X) (Z : params)
  : onv X := 
  update_with_list Z (List.map Some ZT) ET.


Definition updD (D:env nat) (Z:params) := 
  update_with_list Z (List.map S (lookup_list D Z)) D.


Lemma updD_no_param D Z x
  : x ∉ fromList Z
  -> updD D Z [x] = D[x].
Proof.
  intros; unfold updD. eapply update_with_list_no_update; eauto.
Qed.

Lemma updD_param D Z x
  : x ∈ fromList Z
  -> updD D Z [x] = S (D[x]).
Proof.
  intros. unfold updD. 
  general induction Z; unfold updD; simpl in *. 
  exfalso; simpl in *; cset_tac; eauto. 
  destruct_prop (a=x); subst; simplify lookup; eauto.
  eapply IHZ. cset_tac; firstorder.
Qed.



(** ** Type System *)
Inductive block_ty : Type := BTy 
  {
    block_ET : onv ty;
    block_D : env nat;
    block_decls : list ty;
    block_rt : ty
  }.


  Inductive stmtOfType (LT:list block_ty) (ET:onv ty) (D:env nat)
    : stmt -> ty -> Type :=
  | WT_Assn
    x e b t rt
    :  expOfType ET e t
    -> stmtOfType LT (ET[x<-Some t]) (D[x<-S(D[x])]) b rt
    -> stmtOfType LT ET D (stmtExp x e b) rt

  | WT_If x b1 b2 t rt 
   (xdef: ET[x] = Some t)
    :  stmtOfType LT ET D b1 rt
    -> stmtOfType LT ET D b2 rt
    -> stmtOfType LT ET D (stmtIf x b1 b2) rt

  | WT_Goto l Y blk
    (Ldef:get LT (counted l) blk)
    (argT:argsOfType ET Y (block_decls blk))
    (gotoComp:subEnv (block_ET blk) ET)
    (closureOk:forall x, (block_ET blk)[x] <> None ->  (block_D blk)[x] = D[x])
    : stmtOfType LT ET D (stmtGoto l Y) (block_rt blk)

  | WT_Let ET' s (Z:params) (ZT:list ty) b rt rt'
    (WK:subEnv ET' ET)
    :  stmtOfType (BTy ET' D ZT rt::LT) (updET ET' ZT Z) (updD D Z) s rt
    -> stmtOfType (BTy ET' D ZT rt::LT) ET D b rt'
    -> stmtOfType LT ET D (stmtLet s Z b) rt'

  | WT_Return x t (xdef: ET[x] = Some t)
    : stmtOfType LT ET D (stmtReturn x) t.

  Definition labenvOfType (L:labenv) (LT: list block_ty) : Type := 
    forall n ET D pt rt blk, get LT n (BTy ET D pt rt) -> get L n blk -> 
      stmtOfType (drop n LT) (updET ET pt (block_Z blk)) (updD D (block_Z blk)) 
        (block_s blk)  rt
      * envOfType (block_E blk) ET.

  Lemma labenvOfType_drop L LT n
   : labenvOfType L LT -> labenvOfType (drop n L) (drop n LT).
  Proof.
    revert L LT; induction n; intros; simpl; eauto.
    eapply IHn. destruct L, LT; simpl; isabsurd; eauto.
    hnf; intros. eapply getLS in X0. eapply getLS in X1.
    instantiate (1:=b) in X1. instantiate (1:=b0) in X0.
    pose proof (X _ _ _ _ _ _ X0 X1). simpl in X2. eapply X2. 
  Qed.

  Lemma labenvOfType_upd L LT E ET D Z ZT s rt
    (Ed:envOfType E ET) 
    (sTD:stmtOfType (BTy ET D ZT rt::LT) (updET ET ZT Z) (updD D Z) s rt)
    : labenvOfType L LT
    -> labenvOfType (blockI E s Z::L) (BTy ET D ZT rt::LT).
  Proof.
    intros.
    hnf. intros ? ? ? ? ? ? A B. destruct n; inv A; inv B; simpl in *. 
    destr; eauto.
    eauto. 
  Qed.

  Lemma stmtOfType_raiseL LT' LT cont D D' ET ET' rt rt'
    : stmtOfType (LT' ++ LT) ET D cont rt
    -> stmtOfType (LT' ++ (BTy ET' D' nil rt' :: LT)) ET D
    (raiseL (length LT') 1 cont) rt.
  Proof.
    intros A. remember (LT' ++ LT). revert LT LT' ET' Heql.
    induction A; intros; subst; simpl; eauto using stmtOfType.
    destruct (Compare_dec.lt_dec (labN l) (length LT')).
    eapply get_app_le in Ldef; eauto. 
    econstructor; eauto using get_app.
    assert (counted l = length LT' + (counted l - length LT')). simpl. omega.
    rewrite H in Ldef.
    eapply shift_get in Ldef. econstructor.
    assert (counted (labInc l 1) = counted l + 1). induction l; simpl; omega.
    rewrite H0. rewrite H. repeat rewrite <- plus_assoc. 
    eapply get_shift. orewrite (counted l - length LT' + 1 = S (counted l - length LT')).
    constructor. eassumption.
    assumption. eassumption. eassumption.
    econstructor; eauto. specialize (IHA1 LT0 (BTy ET' _ ZT rt:: LT') ET'0 eq_refl). 
    simpl in IHA1. eapply IHA1.
    specialize (IHA2 LT0 (BTy ET' _ ZT rt:: LT') ET'0 eq_refl). eauto.
  Qed. 
(*
  Lemma envOfType_upd ET bE Ef (bZ:params) bZT Y bET
    (argT:argsOfType ET Y bZT) (gotoComp:subEnv bET ET)
    (Efd:envOfType Ef ET) (blk_env : envOfType bE bET)
    : envOfType (update_with_list bZ (lookup_list Ef Y) bE) (updET bET bZ bZT).
  Proof.
    general induction argT; inv LEQ; simpl; eauto.
    simpl. eapply envOfType_update; eauto. 
  Qed.
*)

  Lemma stmtOfType_subEnv LT s D ET' ET rt (WK:subEnv ET' ET)
    :  stmtOfType LT ET' D s rt 
    -> stmtOfType LT ET D s rt.
  Proof.
    intros A. general induction A; eauto using stmtOfType.
    econstructor. instantiate (1:=t). eauto using expOfType_subEnv.
    eapply IHA; eauto. eapply subEnv_update; eauto. 

    eauto using stmtOfType, argsOfType_subEnv, subEnv_trans.
    
    eauto using stmtOfType, subEnv_trans.
  Qed.

Lemma preservation_exp E D ET (ETd:envOfType E ET) L LT (LTd:labenvOfType L LT) rt x e b
  (std:stmtOfType LT ET D (stmtExp x e b) rt) v
  (evalOk:exp_eval E e = Some v)
  : { t:ty & (envOfType (E[x<-v]) (ET[x<-Some t]) 
    * stmtOfType LT (ET[x <- Some t]) (D[x <- S (D[x])]) b rt
    * expOfType ET e t * valOfType v t)%type }.
Proof.
  intros.
  inv std. eexists t. 
  edestruct exp_type_soundness as [v' [A B]]; eauto.
  assert (v=v') by congruence; subst; eauto.
  split; eauto using stmtOfType, envOfType_update.
Qed.

Lemma preservation_if E D ET (ETd:envOfType E ET) L LT (LTd:labenvOfType L LT) rt x b1 b2
  (std:stmtOfType LT ET D (stmtIf x b1 b2) rt)
  : (stmtOfType LT ET D b1 rt
    * stmtOfType LT ET D b2 rt
    * { t: ty & ET[x] = Some t })%type.
Proof.
  intros.
  inv std.  split; eauto.
Qed.
(*
Lemma preservation_goto L LT (LTd:labenvOfType L LT) E D ET (ETd:envOfType E ET)
  l Y rt (sd:stmtOfType LT ET D (stmtGoto l Y) rt) blk (Ldef:get L (counted l) blk)
  : { BET : onv ty & { ZT : typelist & { D' : env nat &
    (labenvOfType (drop (counted l) L) (drop (counted l) LT) 
      * envOfType (update_with_list (block_Z blk) (lookup_list E Y) (block_E blk)) (updET BET (block_Z blk) ZT)
      * stmtOfType (drop (counted l) LT) (updET BET (block_Z blk) ZT) (updD D' (block_Z blk))
        (block_s blk) rt
      * unique (block_Z blk))%type } } }.
Proof.
  inv sd. 
  destruct blk, blk0.
  pose proof (LTd _ _ _ _ _ _ Ldef0 Ldef). decompose records; simpl in *; subst.
  do 3 eexists. split; eauto. split; eauto. split; eauto 10 using labenvOfType_drop. 
  eapply envOfType_upd; eauto using argsOfType_length_eq, length_eq_sym, length_eq_trans. 
Qed.
*)
(*
Lemma preservation_let E D ET (ETd:envOfType E ET) L LT (LTd:labenvOfType L LT)
  s Z rt b (std:stmtOfType LT ET D (stmtLet s Z b) rt)
  : {ET' : onv ty & { ZT:typelist & { rt' : ty &  
    (stmtOfType (BTy ET' D ZT rt':: LT) ET D b rt
      *  labenvOfType (blockI E s Z :: L) (BTy ET' D ZT rt' :: LT))%type } } }.
Proof.
  intros.
  inv std. do 3 eexists; split; eauto using stmtOfType_subEnv.
  eapply labenvOfType_upd; eauto. eauto using envOfType_weakening. 
Qed.


Ltac provide_preservation :=
  let t := fresh "t" in
    let A := fresh "A" in 
      let B := fresh "B" in 
        let etd := fresh "etd" in 
          let ETX := fresh "ETX" in 
  match goal with
    | [ Etd : envOfType ?E ?ET, Ltd: labenvOfType ?L ?LT, 
      expEv : exp_eval ?E ?e = Some _,
      std : stmtOfType ?LT ?ET _ (stmtExp _ ?e _) _ |- _ ] =>
      edestruct (preservation_exp Etd Ltd std) as [t [[[A B] etd] vtd]]; eauto
    | [ Etd : envOfType ?E ?ET, Ltd: labenvOfType ?L ?LT,
      std : stmtOfType ?LT ?ET _ (stmtIf _ _ _) _ |- _ ] =>
      edestruct (preservation_if Etd Ltd std) as [[A B] [t xty]]; eauto
    | [ H : stmtOfType _ _ _ (stmtGoto _ _) _ |- _ ] =>
      edestruct (preservation_goto _ _ H) as [BET [ZT [D' [[[A B] C] U]]]]; eauto
    | [ H : stmtOfType _ _ _ (stmtLet _ _ _ _) _ |- _ ] =>
      edestruct preservation_let as [ETX [A B]]; eauto
  end.
*)



Module Type TypeSystemParameters.
  Variable let_weakening : onv ty -> onv ty -> Prop.
  Variable block_env_typing : env val -> onv ty -> Prop.
  Variable goto_compatibility : onv ty -> onv ty -> Prop.
  Variable param_convention : params -> Prop.

  Hypothesis let_weakening_subEnv 
    : forall ET ET' ET'', subEnv ET' ET'' -> let_weakening ET ET' -> let_weakening ET ET''.

  Hypothesis goto_compatibility_subEnv 
    : forall ET ET' ET'', subEnv ET' ET'' -> goto_compatibility ET ET' -> goto_compatibility ET ET''.

  Hypothesis typing_let_block_env
    : forall E ET ET',
      envOfType E ET 
      -> let_weakening ET' ET 
      -> block_env_typing E ET'.

End TypeSystemParameters.

Module TypeSystem (Export params:TypeSystemParameters).
  Include params.
  
  Inductive block_ty : Type := BTy 
    {
      block_ET : onv ty;
      block_decls : list ty;
      block_rt : ty
    }.

  Inductive stmtOfType (LT:list block_ty) (ET:onv ty)
    : stmt -> ty -> Type :=
  | WT_Assn 
    x e b t rt 
    :  expOfType ET e t
    -> stmtOfType LT  (ET[x<-Some t]) b rt
    -> stmtOfType LT ET (stmtExp x e b) rt

  | WT_If x b1 b2 t rt
    (xdef: ET[x] = Some t)
    :  stmtOfType LT ET b1 rt
    -> stmtOfType LT ET b2 rt
    -> stmtOfType LT ET (stmtIf x b1 b2) rt

  | WT_Goto l Y blk rt
    (Ldef:get LT (counted l) blk)
    (argT:argsOfType ET Y (block_decls blk))
    (rtOk:block_rt blk = rt)
    (gotoComp:goto_compatibility (block_ET blk) ET)
    : stmtOfType LT ET (stmtGoto l Y) rt

  | WT_Let ET' s Z ZT b rt rt'
    :  let_weakening ET' ET
    -> param_convention Z
    -> stmtOfType (BTy ET' ZT rt::LT) (updET ET' ZT Z) s rt
    -> stmtOfType (BTy ET' ZT rt::LT) ET b rt'
    -> stmtOfType LT ET (stmtLet s Z b) rt'

  | WT_Return x t (xdef: ET[x] = Some t)
    : stmtOfType LT ET (stmtReturn x) t.

  Definition labenvOfType (L:labenv) (LT: list block_ty) : Type := 
    forall n ET pt rt blk, get LT n (BTy ET pt rt) -> get L n blk -> 
      (stmtOfType (drop n LT) (updET ET pt (block_Z blk)) (block_s blk) rt
      * block_env_typing (block_E blk) ET)%type.

  Lemma labenvOfType_drop L LT n
   : labenvOfType L LT -> labenvOfType (drop n L) (drop n LT).
  Proof.
    revert L LT; induction n; intros; simpl; eauto.
    eapply IHn. destruct L, LT; simpl; isabsurd; eauto.
    hnf; intros. eapply getLS in X0. eapply getLS in X1.
    instantiate (1:=b) in X1. instantiate (1:=b0) in X0.
    pose proof (X _ _ _ _ _ X0 X1). simpl in X2. eapply X2. 
  Qed.

  Lemma labenvOfType_upd L LT E ET Z ZT s rt
    (Ed:block_env_typing E ET) 
    (sTD:stmtOfType (BTy ET ZT rt::LT) (updET ET ZT Z) s rt)
    : labenvOfType L LT
    -> labenvOfType (blockI E s Z::L) (BTy ET ZT rt::LT).
  Proof.
    intros.
    hnf. intros ? ? ? ? ? A B. destruct n; inv A; inv B; simpl in *. 
    destr; eauto.
    eauto. 
  Qed.

  Lemma stmtOfType_raiseL LT' LT cont ET ET' rt rt'
    : stmtOfType (LT' ++ LT) ET cont rt
    -> stmtOfType (LT' ++ (BTy ET' nil rt' :: LT)) ET
    (raiseL (length LT') 1 cont) rt.
  Proof.
    intros A. remember (LT' ++ LT). revert LT LT' ET' Heql.
    induction A; intros; subst; simpl; eauto using stmtOfType.
    destruct (Compare_dec.lt_dec (labN l) (length LT')).
    eapply get_app_le in Ldef; eauto. 
    econstructor; eauto using get_app.
    assert (counted l = length LT' + (counted l - length LT')). simpl. omega.
    rewrite H in Ldef.
    eapply shift_get in Ldef. econstructor.
    assert (counted (labInc l 1) = counted l + 1). induction l; simpl; omega.
    rewrite H0. rewrite H. repeat rewrite <- plus_assoc. 
    eapply get_shift. orewrite (counted l - length LT' + 1 = S (counted l - length LT')).
    constructor. eassumption.
    assumption. reflexivity.
    assumption.
    econstructor; eauto. specialize (IHA1 LT0 (BTy ET' ZT rt:: LT') ET'0 eq_refl). 
    simpl in IHA1. eapply IHA1.
    specialize (IHA2 LT0 (BTy ET' ZT rt:: LT') ET'0 eq_refl). eauto.
  Qed. 
  
  Lemma stmtOfType_subEnv LT s ET' ET rt (WK:subEnv ET' ET)
    : stmtOfType LT ET' s rt -> stmtOfType LT ET s rt.
  Proof.
    intros A.
    general induction A; simpl; eauto using stmtOfType.
    econstructor;
      eauto using expOfType_subEnv, subEnv_update.
    
    eapply WT_Goto; eauto. 
 (* eapply argsOfType_subEnv; eauto.
    eapply goto_compatibility_subEnv; eauto.
    eapply WT_Let; eauto. eapply let_weakening_subEnv; eauto.
  Qed. *)
    Admitted.

Lemma preservation_exp E ET (ETd:envOfType E ET) L LT (LTd:labenvOfType L LT) rt x e b
  (std:stmtOfType LT ET (stmtExp x e b) rt) v
  (evalOk:exp_eval E e = Some v)
  : { t:ty & (envOfType (E[x<-v]) (ET[x<-Some t]) 
    * stmtOfType LT (ET[x<-Some t]) b rt)%type }.
Proof.
  intros.
  inv std.  eexists t. 
  edestruct exp_type_soundness as [v' [A B]]; eauto.
  assert (v=v') by congruence; subst; eauto.
  split; eauto using stmtOfType_subEnv,
  envOfType_update; eauto. 
Qed.

Lemma preservation_if E ET (ETd:envOfType E ET) L LT (LTd:labenvOfType L LT) rt x b1 b2
  (std:stmtOfType LT ET (stmtIf x b1 b2) rt)
  : (stmtOfType LT ET b1 rt
    * stmtOfType LT ET b2 rt)%type.
Proof.
  intros.
  inv std.  split; eauto using stmtOfType_subEnv.
Qed.

Lemma preservation_let E ET (ETd:envOfType E ET) L LT (LTd:labenvOfType L LT)
  s Z rt b (std:stmtOfType LT ET (stmtLet s Z b) rt)
  : {ET' : onv ty & { ZT : list ty & { rt' : ty & (stmtOfType (BTy ET' ZT rt':: LT) ET b rt
  *  labenvOfType (blockI E s Z :: L)
     (BTy ET' ZT rt' :: LT))%type } } }.
Proof.
  intros.
  inv std. do 3 eexists; split; eauto using stmtOfType_subEnv.
  eapply labenvOfType_upd; eauto using typing_let_block_env.
Qed.


Ltac provide_progress :=
  match goal with
    | [ H : stmtOfType _ _ (stmtExp _ _ _) _ |- _ ] =>
      edestruct preservation_exp as [t [A B]]; eauto
    | [ H : stmtOfType _ _ (stmtIf _ _ _) _ |- _ ] =>
      edestruct preservation_if as [A B]; eauto
    | [ H : stmtOfType _ _ (stmtLet _ _ _ _) _ |- _ ] =>
      edestruct preservation_let as [ETX [A B]]; eauto
  end.

End TypeSystem.

Module TSP_Imp <: TypeSystemParameters.
  Definition let_weakening := fun _ :onv ty => fun _ : onv ty => True.
  Definition goto_compatibility := (@subEnv ty).
  Definition block_env_typing := fun (E:env val) => fun (ET:onv ty) => True.
  Definition param_convention := fun (Z:params) => Z = nil.

  Lemma let_weakening_subEnv ET ET' ET''
    : subEnv ET' ET'' -> let_weakening ET ET' -> let_weakening ET ET''.
  Proof.
    inversion 2. firstorder.
  Qed.
  
  Lemma goto_compatibility_subEnv ET ET' ET''
    : subEnv ET' ET'' -> goto_compatibility ET ET' -> goto_compatibility ET ET''.
  Proof.
    unfold goto_compatibility; intros; eauto using subEnv_trans.
  Qed.

  Lemma goto_block_env_typing E bET ET (ETd:envOfType E ET)
    : goto_compatibility bET ET -> block_env_typing E bET -> envOfType E bET.
  Proof.
    intros; eapply envOfType_weakening; eauto. 
  Qed.

  Lemma envOfType_upd ET bE Ef (bZ:params) bZT Y bET
    (argT:argsOfType ET Y bZT) (gotoComp:goto_compatibility bET ET)
    (Efd:envOfType Ef ET) (blk_env : block_env_typing bE bET)
    : envOfType (updE Ef Ef bZ Y) (updET bET bZT bZ).
  Proof.
    (*general induction argT; inv LEQ; simpl; eauto using envOfType_weakening, 
      envOfType_update.*)
    Admitted.

  Lemma typing_let_block_env E ET ET'
    : envOfType E ET -> let_weakening ET' ET -> block_env_typing E ET'.
  Proof.
    unfold block_env_typing. inversion 2; subst; intros; eauto using envOfType_empty.
  Qed.


End TSP_Imp.

Module TSP_Fun <: TypeSystemParameters.
  Definition let_weakening := (@subEnv ty).
  Definition goto_compatibility := (@subEnv ty).
  Definition block_env_typing := envOfType.
  Definition param_convention := fun (Z:params) => True.

  Lemma let_weakening_subEnv ET ET' ET''
    : subEnv ET' ET'' -> let_weakening ET ET' -> let_weakening ET ET''.
  Proof.
    intros. eapply subEnv_trans; eauto.
  Qed.
  
  Lemma goto_compatibility_subEnv ET ET' ET''
    : subEnv ET' ET'' -> goto_compatibility ET ET' -> goto_compatibility ET ET''.
  Proof.
    intros; eapply subEnv_trans; eauto.
  Qed.

  Lemma goto_block_env_typing E bET ET (ETd:envOfType E ET)
    : goto_compatibility bET ET -> block_env_typing E bET -> envOfType E bET.
  Proof.
    intros; eapply envOfType_weakening; eauto. 
  Qed.

  Lemma envOfType_upd ET bE Ef bZ bZT Y bET
    (argT:argsOfType ET Y bZT) (gotoComp:goto_compatibility bET ET)
    (Efd:envOfType Ef ET) (blk_env : block_env_typing bE bET)
    : envOfType (updE bE Ef bZ Y) (updET bET bZT bZ).
  Proof.
    (* general induction argT; inv LEQ; simpl; eauto using envOfType_update. *)
  Admitted.


  Lemma block_env_typing_envOfType E ET
    : block_env_typing E ET -> envOfType E ET.
  Proof.
    trivial.
  Qed.
  
  Lemma typing_let_block_env E ET ET'
    : envOfType E ET -> let_weakening ET' ET -> block_env_typing E ET'.
  Proof.
    intros. eapply envOfType_weakening; eauto.
  Qed.

End TSP_Fun.

Module ImpTS := TypeSystem TSP_Imp.
Module FunTS := TypeSystem TSP_Fun.



(* 
*** Local Variables: ***
*** coq-load-path: ("infra" "constr" "il" "isa" ".") ***
*** End: ***
*)
