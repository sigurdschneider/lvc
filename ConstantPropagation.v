
Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import CSet Val Var Env EnvTy IL ParamsMatch Sim SimApx Fresh Annotation MoreExp Coherence.

Require Import Liveness Filter ValueOpts.

Set Implicit Arguments.
Unset Printing Records.

(* Constant Propagation *)


(* None is top *)
Definition aval := option val.



Definition binop_eval (o:binop) (v1 v2:aval) : option aval := 
  match v1, v2 with 
    | Some v1, Some v2 => 
      match Exp.binop_eval o v1 v2 with
        | None => None (* if binop_eval says None, it's undefined, so we yield bottom, not top *)
        | Some x => Some (Some x)
      end
      | _, _  => Some None (* if v1 or v2 is top, we yield top *)
  end.

Fixpoint exp_eval (E:onv aval) (e:exp) : option aval :=
  match e with
    | Con v => Some (Some v)
    | Var x => E x
    | BinOp o e1 e2 => mdo v1 <- exp_eval E e1; 
                      mdo v2 <- exp_eval E e2;
                      binop_eval o v1 v2
  end.

Inductive le : option aval -> option aval -> Prop :=
  | leTop x : le x (Some None)
  | leValVal y : le (Some (Some y)) (Some (Some y))
  | leBotBot y : le None (Some (Some y))
  | leBot  : le None None.



Inductive cp_sound : list (params*list (option aval)) 
                      -> stmt 
                      -> ann (onv aval) 
                      -> ann (set var) 
                      -> Prop :=
| CPOpr (x:var) Cp b e (Gamma:onv aval) al lv alv
  : cp_sound Cp b al alv
    -> agree_on eq (getAnn alv \ {{x}}) Gamma (getAnn al)
    -> exp_eval Gamma e = getAnn al x
    -> cp_sound Cp (stmtExp x e b) (ann1 Gamma al) (ann1 lv alv)
| CPIf Cp e b1 b2 Gamma lv al1 al2 alv1 alv2 
  : agree_on eq lv Gamma (getAnn al1)
    -> agree_on eq lv Gamma (getAnn al2)
    (* these conditions make it conditional constant propagation *)
    -> (exp_eval Gamma e <> Some (Some 1) -> cp_sound Cp b1 al1 alv1)
    -> (exp_eval Gamma e <> Some (Some 0) -> cp_sound Cp b2 al2 alv2)
    -> cp_sound Cp (stmtIf e b1 b2) (ann2 Gamma al1 al2) (ann2 lv alv1 alv2)
| CPGoto l Y Cp Gamma lv Z Yf
  : get Cp (counted l) (Z,Yf)
    -> PIR2 le (List.map (exp_eval Gamma) Y) Yf
    -> cp_sound Cp (stmtGoto l Y) (ann0 Gamma) (ann0 lv)
| CPReturn Cp e  Gamma lv
  : cp_sound Cp (stmtReturn e) (ann0 Gamma) (ann0 lv)
| CPLet Cp s Z b Gamma lv Yf als alb alvs alvb
  : cp_sound ((Z,Yf)::Cp) s als alvs
  -> cp_sound ((Z,Yf)::Cp) b alb alvb
  -> agree_on eq lv (Gamma[Z <-- Yf]) (getAnn als)
  -> agree_on eq lv Gamma (getAnn alb)
  -> cp_sound Cp (stmtLet Z s b) (ann2 Gamma als alb) (ann2 lv alvs alvb).

Definition cp_eqns (E:onv aval) (lv:set var) : eqns :=
  fold (fun x L => match E x with 
                 | Some (Some c) => (Var x, Con c)::L
                 | _ =>  L
                  end) lv nil.

: cp_eqns E lv 

Instance entails_refl 
: Reflexive (entails).
Proof.
  hnf; intros. unfold entails; intros; split; eauto; try reflexivity.
Qed.

Lemma entails_monotonic_add Gamma Γ' gamma 
: entails Gamma Γ' -> entails (gamma::Gamma) Γ'.
Proof.
  unfold entails; intros; dcr; split.
  - intros. eapply H0. hnf; intros. eapply H; eauto using get.
  - rewrite H1. rewrite eqns_freeVars_add. cset_tac; intuition.
Qed.


Inductive same_shape (A B:Type) : ann B -> ann A -> Prop :=
| SameShape0 a b
  : same_shape (ann0 a) (ann0 b)
| SameShape1 a b an bn 
  : same_shape an bn 
    -> same_shape (ann1 a an) (ann1 b bn)
| SameShape2 a b an bn an' bn'
  : same_shape an bn
    -> same_shape an' bn'
    -> same_shape (ann2 a an an') (ann2 b bn bn').


Fixpoint zip2Ann X Y Z (f:X->Y->Z) (a:ann X) (b:ann Y) z : ann Z := 
  match a, b with
    | ann1 a an, ann1 a' an' => ann1 (f a a') (zip2Ann f an an' z)
    | ann2 a an1 an2, ann2 a' an1' an2' => ann2 (f a a') 
                                               (zip2Ann f an1 an1' z)
                                               (zip2Ann f an2 an2' z) 
    | ann0 a, ann0 b => ann0 (f a b)
    | _, _ => z
  end.

(*
Lemma zip2Ann_get X Y Z f a b
: getAnn (zip2Ann f a b) = f (getAnn a) (getAnn b).
*)

Definition cp_eqns_ann (a:ann (onv aval)) (b:ann (set var)) : ann eqns :=
  zip2Ann cp_eqns a b (ann0 nil).

Definition cp_choose_exp E e :=
  match exp_eval E e with 
    | Some (Some c) => Con c
    | _ => e
  end.


Fixpoint cp_choose s (a:ann (onv aval)) : ann args :=
  match s, a with
    | stmtExp x e s, ann1 E an => 
      ann1 (cp_choose_exp E e::nil) (cp_choose s an)
    | stmtIf e s t, ann2 E ans ant => 
        ann2 (cp_choose_exp E e::nil) (cp_choose s ans) (cp_choose t ant)
    | stmtGoto f Y, ann0 E => 
      ann0 (List.map (cp_choose_exp E) Y)
    | stmtReturn e, ann0 E => ann0 (cp_choose_exp E e::nil)
    | stmtLet Z s t, ann2 E ans ant => 
      ann2 nil (cp_choose s ans) (cp_choose t ant)
    | _, _ => ann0 nil 
  end.

Lemma exp_eval_moreDefined e lv Gamma v
: (forall x v, Gamma x = Some (Some v) -> moreDefined (cp_eqns Gamma lv) (cp_eqns Gamma lv) (Var x) (Con v))
  -> live_exp_sound e lv
   -> exp_eval Gamma e = ⎣⎣v ⎦ ⎦
   -> moreDefined (cp_eqns Gamma lv) (cp_eqns Gamma lv) e (Con v).
Proof.
  intros. general induction H0; simpl in * |- *; hnf; intros; simpl; eauto using fstNoneOrR. 
  - econstructor; eauto.
  - eapply H0; eauto.
  - monad_inv H1.
    destruct x, x0; isabsurd.
    exploit IHlive_exp_sound1; eauto.
    exploit IHlive_exp_sound2; eauto.
    exploit X; try eapply H0; eauto. exploit X0; try eapply H0; eauto.
    simpl in * |- *. inv X1; inv X2; simpl.
    + econstructor.
    + econstructor.
    + econstructor.
    + destruct (Exp.binop_eval o v0 v1). inv EQ2. econstructor. eauto.
      congruence.
Qed.

Lemma zip2Ann_get X Y Z (f:X->Y->Z) a b z
: 
  same_shape a b
  -> getAnn (zip2Ann f a b z) = f (getAnn a) (getAnn b).
Proof.
  intros. general induction H; simpl; eauto.
Qed.

Lemma cp_sound_eqn Lv Cp Es s al alv ang
: let Gamma := (zip2Ann cp_eqns al alv (ann0 nil)) in
live_sound Lv s alv
-> cp_sound Cp s al alv
-> same_shape al alv
-> (forall (x0 : var) (v0 : val),
   (getAnn al) x0 = ⎣⎣v0 ⎦ ⎦ ->
   moreDefined (cp_eqns (getAnn al) (getAnn alv)) (cp_eqns (getAnn al) (getAnn alv)) (Var x0) (Con v0))
-> ssa s ang
-> eqn_sound Es s Gamma Gamma ang (cp_choose s al).
Proof.
  intros. subst Gamma. 
  general induction H0; invt live_sound; invt same_shape; invt ssa; simpl.
  - econstructor.
    eapply IHcp_sound; eauto. simpl in * |- *.
    + admit.
    + rewrite zip2Ann_get; eauto.
      
    + rewrite zip2Ann_get; eauto. admit.
    + unfold cp_choose_exp. case_eq (exp_eval Gamma e); intros.
      case_eq a; intros; subst.
      * eapply exp_eval_moreDefined; eauto.
      * reflexivity.
      * reflexivity.
    + unfold cp_choose_exp. case_eq (exp_eval Gamma e); intros; eauto.
      case_eq a; intros; subst; simpl. eapply incl_empty. eassumption.
  - econstructor.
    


Qed.

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
