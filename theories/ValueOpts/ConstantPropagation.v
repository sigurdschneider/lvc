Require Import CSet Le Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Indexwise.
Require Import CSet Val Var Env IL Sim Fresh Annotation LabelsDefined DecSolve OptionR.

Require Import RenamedApart SetOperations Eqn ValueOpts Infra.Lattice WithTop.

Set Implicit Arguments.
Unset Printing Records.

(* Constant Propagation *)

Require compcert.lib.Integers.


(* None is top *)
Definition aval := option (withTop val).

Coercion option_as_unkown A (a:option A) :=
  match a with
  | Some a => Known a
  | None => Unknown
  end.

Fixpoint op_eval (E:onv (withTop val)) (e:op) : aval :=
  match e with
    | Con v => Some (wTA v)
    | Var x => E x
    | UnOp o e => match op_eval E e with
                 | Some (wTA v) =>
                   match Val.unop_eval o v with
                   | Some v => Some (wTA v)
                   | None => None
                   end
                   | v => v
                 end
    | BinOp o e1 e2 =>
       match op_eval E e1 with
       | Some (wTA v1) =>
         match op_eval E e2 with
         | Some (wTA v2) =>
           match Val.binop_eval o v1 v2 with
           | Some v => Some (wTA v)
           | None => None
           end
         | v => v
         end
       | v => v
       end

  end.

Definition exp_eval (E:onv (withTop val)) (e:exp) : aval :=
  match e with
  | Operation e => op_eval E e
  | _ => Some Top
  end.

Inductive isEqCmp : op -> Prop :=
  IisEqCmp x c : isEqCmp (BinOp BinOpEq (Var x) (Con c)).

Instance isEqCmp_dec e : Computable (isEqCmp e).
Proof.
  destruct e; try dec_solve.
  destruct e1, e2; decide (b = BinOpEq); subst; try dec_solve.
Defined.

Definition getEqCmpVar (e:op) :=
  match e with
    | BinOp BinOpEq (Var x) (Con c) => x
    | _ => 0
  end.

Definition getEqCmpCon (e:op) :=
  match e with
    | BinOp BinOpEq (Var x) (Con c) => c
    | _ => default_val
  end.

Definition aval2bool (v:aval) :=
  match v with
  | Some Top => Some Top
  | Some (wTA v) => Some (wTA (val2bool v))
  | _ => None
  end.

Lemma oval2bool_some v b
: aval2bool v = Some (wTA b) ->
  exists v', v = (Some (wTA v')) /\ val2bool v' = b.
Proof.
  destruct v; try destruct w; simpl; intros; inv H; eauto.
Qed.

Inductive cp_sound (AE:onv (withTop val)) :
                     list (params*list aval)
                     -> list bool
                     -> stmt
                     -> ann bool
                     -> Prop :=
| CPOpr (x:var) Cp Rch (b:bool) r e s
  : cp_sound AE Cp Rch s r
    -> (b -> exp_eval AE e = AE x)
    -> (b -> getAnn r)
    -> cp_sound AE Cp Rch (stmtLet x e s) (ann1 b r)
| CPIf Cp Rch e (b:bool) s1 s2 (r1 r2:ann bool)
       (Cond1:cp_sound AE Cp Rch s1 r1)
       (Cond2:cp_sound AE Cp Rch s2 r2)
       (Reach1:b -> op_eval AE e <> None -> aval2bool (op_eval AE e) <> Some (wTA false) -> getAnn r1)
       (Reach2:b -> poLe (Some (wTA val_false)) (op_eval AE e) -> getAnn r2)
  : cp_sound AE Cp Rch (stmtIf e s1 s2) (ann2 b r1 r2)
| CPGoto l Y Cp Rch Z aY (b bf:bool)
  : get Cp (counted l) (Z,aY)
    -> get Rch (counted l) bf
    -> length Z = length Y
    -> (b -> PIR2 poLe (List.map (op_eval AE) Y) aY)
    -> (b -> bf)
    -> cp_sound AE Cp Rch (stmtApp l Y) (ann0 b)
| CPReturn Cp Rch e b
  : cp_sound AE Cp Rch (stmtReturn e) (ann0 b)
| CPLet Cp Rch F t (b:bool) (rF:list (ann bool)) (r:ann bool) (rfLen:❬F❭=❬rF❭)
   (Reach1:b -> getAnn r)
  : (forall n Zs r,
        get F n Zs ->
        get rF n r ->
        cp_sound AE (List.map (fun Zs => (fst Zs, lookup_list AE (fst Zs))) F ++ Cp)
                 (getAnn ⊝ rF ++ Rch)
                 (snd Zs) r)
    -> cp_sound AE (List.map (fun Zs => (fst Zs, lookup_list AE (fst Zs))) F ++ Cp)
               (getAnn ⊝ rF ++ Rch) t r
    -> cp_sound AE Cp Rch (stmtFun F t) (annF b rF r).

Definition indexwise_R1 {A} (P:A->Prop) LA :=
forall n a, get LA n a -> P a.

Definition indexwise_R1_dec {A} {P:A->Prop} LA (Rdec:(forall n a, get LA n a -> Computable (P a)))
      : Computable (indexwise_R1 P LA).
unfold Computable. revert LA Rdec. fix 1. intros LA Rdec.
destruct LA; try now left; isabsurd.
intros. destruct (Rdec 0 a).
- eauto using get.
- destruct (indexwise_R1_dec LA); clear indexwise_R1_dec; eauto using get.
  + left. hnf; intros. inv H; eauto.
  + right; intro HH. eapply n; hnf; intros; eapply HH; eauto using get.
- right; intro HH. eapply n; hnf; intros; eapply HH; eauto using get.
Defined.

Instance cp_sound_dec AE Rch ZL s r : Computable (cp_sound AE ZL Rch s r).
Proof.
  hnf. revert AE Rch ZL r; sind s; intros; destruct s; destruct r; try dec_solve.
  - edestruct (IH s); eauto;
      decide (a -> exp_eval AE e = AE x); try dec_solve;
        decide (a -> getAnn r); try dec_solve.
  - edestruct (IH s2 ltac:(eauto) AE Rch ZL); eauto; [| dec_solve];
      edestruct (IH s1 ltac:(eauto) AE Rch ZL); eauto; [| dec_solve];
        decide (op_eval AE e = None);
        decide (aval2bool (op_eval AE e) = Some (wTA false));
        (decide (poLe (Some (wTA val_false)) (op_eval AE e)));
        decide (a); decide (getAnn r1); decide (getAnn r2); try dec_solve.
  - destruct (get_dec ZL (counted l)) as [[[]]|]; try dec_solve.
    destruct (get_dec Rch (counted l)) as [[]|]; try dec_solve.
    decide (length l0 = length Y); try dec_solve.
    decide (a -> PIR2 poLe (List.map (op_eval AE) Y) l1);
      try dec_solve.
    decide (a -> x); try dec_solve.
  - assert (SZ:size s < size (stmtFun F s)) by eauto.
    decide (❬F❭=❬sa❭); [|dec_solve].
    edestruct (IH s SZ AE (getAnn ⊝ sa ++ Rch) (List.map (fun Zs => (fst Zs, lookup_list AE (fst Zs))) F ++ ZL) r); [|dec_solve].
    exploit (@indexwise_R2_dec _ _ (fun Zs r => cp_sound AE ((fun Zs0 : params * stmt => (fst Zs0,
        lookup_list AE (fst Zs0))) ⊝ F ++ ZL)(getAnn ⊝ sa ++ Rch)  (snd Zs) r) F); eauto.
    intros. eapply IH; eauto. destruct H;[|dec_solve].
    decide (a -> getAnn r); dec_solve.
Defined.

Require Import Reachability.

Definition cop2bool AE e := aval2bool (op_eval AE e).

Lemma impb_lift (b b':bool)
  : (b -> b')
    -> impb b b'.
Proof.
  unfold impb; cases; eauto.
Qed.

Local Hint Resolve impb_lift.

Lemma test AE ZL Rch s r
  : cp_sound AE ZL Rch s r
    -> reachability (cop2bool AE) Sound Rch s r.
Proof.
  intros CPS.
  general induction CPS; econstructor; simpl; eauto.
  - intros. unfold cop2bool in *. eapply Reach1; eauto.
    intro. rewrite H2 in *. simpl in *. congruence.
  - intros. unfold cop2bool in *. eapply Reach2; eauto.
    case_eq (op_eval AE e); intros. rewrite H2 in *. simpl in *.
    simpl in *; destruct w; try congruence; eauto.
    econstructor; eauto. econstructor; eauto.
    simpl in *.
    case_eq (val2bool a); intros; rewrite H3 in *; try congruence.
    unfold val2bool in H3. cases in H3.
    econstructor; eauto. econstructor; eauto. reflexivity.
    congruence.
    rewrite H2 in H. simpl in *. congruence.
Qed.