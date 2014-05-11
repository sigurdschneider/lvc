
Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import CSet Val Var Env EnvTy IL ParamsMatch Sim SimApx Fresh Annotation MoreExp Coherence.

Require Import Liveness Filter SetOperations ValueOpts.

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

Definition cp_eqn E x := 
  match E x with 
    | Some (Some c) => {{(Var x, Con c)}}
    | _ => ∅
  end.

Definition cp_eqns (E:onv aval) (lv:set var) : eqns :=
  fold union (map (cp_eqn E) lv) ∅.

Instance cp_eqns_morphism_equal E
: Proper (Equal ==> Equal) (cp_eqns E).
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite H. reflexivity.
Qed.

Instance cp_eqns_morphism_subset E
: Proper (Subset ==> Subset) (cp_eqns E).
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite H. reflexivity.
Qed.

Instance cp_eqns_morphism_flip_subset E
: Proper (flip Subset ==> flip Subset) (cp_eqns E).
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite <- H. reflexivity.
Qed.

Lemma cp_eqns_union E lv lv'
: cp_eqns E (lv ∪ lv') [=] cp_eqns E lv ∪ cp_eqns E lv'.
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite map_app.
  rewrite fold_union_app. reflexivity.
  intuition.
Qed.

Instance entails_refl 
: Reflexive (entails).
Proof.
  hnf; intros. unfold entails; intros; split; eauto; try reflexivity.
Qed.

Lemma entails_monotonic_add Gamma Γ' gamma 
: entails Gamma Γ' -> entails (gamma ∪ Gamma) Γ'.
Proof.
  unfold entails; intros; dcr; split.
  - intros. eapply H0. hnf; intros. eapply H; eauto. cset_tac; intuition.
  - rewrite H1. rewrite eqns_freeVars_union. cset_tac; intuition.
Qed.

Lemma map_agree X `{OrderedType X} Y `{OrderedType Y} 
      lv (f:X->Y) `{Proper _ (_eq ==> _eq) f} (g:X->Y) `{Proper _ (_eq ==> _eq) g}
: agree_on _eq lv f g
  -> map f lv [=] map g lv.
Proof.
  intros. intro.
  repeat rewrite map_iff; eauto.
  split; intros []; intros; dcr; eexists x; split; eauto.
  + specialize (H3 x H5). rewrite <- H3; eauto.
  + specialize (H3 x H5). rewrite H3; eauto.
Qed.

Lemma cp_eqn_agree lv E E'
: agree_on eq lv E E'
-> agree_on _eq lv (cp_eqn E) (cp_eqn E').
Proof.
  unfold agree_on, cp_eqn; intros.
  rewrite H; eauto.
Qed.

Lemma cp_eqns_agree lv E E'
: agree_on eq lv E E'
  -> cp_eqns E lv [=] cp_eqns E' lv.
Proof.
  intros. hnf; intro. unfold cp_eqns.
  rewrite map_agree; eauto using cp_eqn_agree. reflexivity.
  intuition. intuition.
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
  zip2Ann cp_eqns a b (ann0 ∅).

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

Lemma in_or_not X `{OrderedType X} x s
:   { x ∈ s /\ s [=] s \ {{x}} ∪ {{x}} }
  + { x ∉ s /\ s [=] s \ {{x}} }.
Proof.
  decide (x ∈ s); [left|right]; split; eauto.
  - cset_tac; intuition. decide (_eq a x); eauto.
    rewrite H1; eauto.
  - cset_tac; intuition. intro. rewrite H1 in H0; eauto.
Qed.

Lemma entails_union_split Gamma Γ' Γ''
: entails Gamma (Γ' ∪ Γ'')
-> entails Gamma (Γ')
/\ entails Gamma (Γ'').
Proof.
  unfold entails, satisfiesAll.
  split; intros; dcr.
    + split; intros. eapply H0; eauto. cset_tac; intuition.
      rewrite <- H1. rewrite eqns_freeVars_union. eapply incl_left.
    + split; intros. eapply H0; eauto. cset_tac; intuition.
      rewrite <- H1. rewrite eqns_freeVars_union. eapply incl_right.
Qed.

Lemma entails_union Gamma Γ' Γ''
: entails Gamma (Γ')
/\ entails Gamma (Γ'')
-> entails Gamma (Γ' ∪ Γ'').
Proof.
  unfold entails, satisfiesAll.
  split; intros; dcr.
  + intros. cset_tac. destruct H1; eauto.
  + rewrite eqns_freeVars_union. cset_tac; intuition.
Qed.

Instance option_R_trans `{Transitive} : Transitive (option_R R).
Proof.
  hnf; intros. inv H0; inv H1. econstructor; eauto.
Qed.

Lemma cp_eqns_in AE x lv v
  : x \In lv
    -> AE x = ⎣⎣v ⎦ ⎦
    -> (Var x, Con v) ∈ cp_eqns AE lv.
Proof.
  intros. unfold cp_eqns.
  eapply fold_union_incl.
  instantiate (1:={{ (Var x, Con v) }}). cset_tac; intuition.
  assert (cp_eqn AE x = {{ (Var x, Con v) }}).
  unfold cp_eqn. rewrite H0. reflexivity.
  rewrite <- H1. eapply map_1; eauto.
  intuition.
Qed.

Lemma cp_eqns_satisfies_env AE E x v lv
: x ∈ lv
  -> AE x = ⎣⎣v ⎦ ⎦
  -> satisfiesAll E (cp_eqns AE lv)
  -> E x = ⎣v ⎦.
Proof.
  intros. exploit H1; eauto.
  instantiate (1:=(Var x, Con v)). 
  eapply cp_eqns_in; eauto.
  hnf in X; simpl in *. inv X; eauto.
Qed.

Lemma exp_eval_same e lv AE E v v'
:   live_exp_sound e lv
    -> exp_eval AE e = ⎣⎣v ⎦ ⎦
    -> satisfiesAll E (cp_eqns AE lv)
    -> Exp.exp_eval E e = Some v'
    -> option_R eq ⎣v' ⎦ ⎣v ⎦.
Proof.
  intros. general induction H; simpl in * |- *; eauto using option_R.
  - exploit cp_eqns_satisfies_env; eauto.
    rewrite X; eauto using option_R.
  - monad_inv H1. monad_inv H3.
    destruct x, x0; isabsurd.
    exploit IHlive_exp_sound1; eauto.
    exploit IHlive_exp_sound2; eauto.
    rewrite EQ0, EQ4; simpl. rewrite EQ5.
    inv X. inv X0. simpl in *. rewrite EQ5 in EQ2.
    inv EQ2. constructor; eauto.
Qed.
  
Lemma exp_eval_entails AE e v x lv
: live_exp_sound e lv
  -> exp_eval AE e = ⎣⎣v ⎦ ⎦
  -> entails ({{ (Var x, e) }} ∪ cp_eqns AE lv) {{(Var x, Con v)}}.
Proof.
  intros.
  unfold entails; split; intros. unfold satisfiesAll, satisfies; intros.
  exploit (H1 (Var x, e)); eauto. 
  cset_tac; intuition. cset_tac. invc H2; simpl in *; subst; simpl. 
  inv X.
  eapply satisfiesAll_union in H1; dcr.
  exploit exp_eval_same; try eapply H1; eauto.
  etransitivity. instantiate (1:=(eqns_freeVars {{(Var x, e)}})).
  unfold eqns_freeVars.
  repeat rewrite map_single; eauto using freeVars_Proper.
  repeat rewrite (@fold_single _ _ _ Equal). 
  simpl. cset_tac; intuition.
  eapply Equal_ST. eapply union_m. eapply transpose_union.
  eapply Equal_ST. eapply union_m. eapply transpose_union.
  assert ( {(Var x, e); {}} ⊆ {(Var x, e); {}} ∪ cp_eqns AE lv).
  cset_tac; intuition.
  rewrite <- H1. reflexivity.
Qed. 

Lemma entails_empty s
: entails s ∅.
Proof.
  hnf; intros. split; intros.
  - hnf; intros. cset_tac; intuition.
  - rewrite (incl_empty _ s). reflexivity.
Qed.
  

Lemma cp_sound_eqn Lv Cp Es s al alv ang
: let Gamma := (zip2Ann cp_eqns al alv (ann0 ∅)) in
live_sound Lv s alv
-> cp_sound Cp s al alv
-> same_shape al alv
-> ssa s ang
-> eqn_sound Es s Gamma Gamma ang (cp_choose s al).
Proof.
  intros. subst Gamma. 
  general induction H0; invt live_sound; invt same_shape; invt ssa; simpl.
  - econstructor.
    eapply IHcp_sound; eauto. simpl in * |- *.
    + rewrite zip2Ann_get; eauto.
      destruct (in_or_not x (getAnn alv)); dcr.
      * rewrite H7. rewrite cp_eqns_union. eapply entails_union; split.
        { 
          rewrite <- (cp_eqns_agree H); eauto.
          eapply entails_monotonic_add.
          rewrite <- H13. reflexivity.
        } 
        { 
          unfold cp_eqns. rewrite map_single; [| intuition].
          rewrite (@fold_single _ _ _ Equal).
          unfold cp_eqn at 2. case_eq (getAnn al x); intros.
          destruct a. rewrite H8 in H1.
          intros. rewrite union_comm, empty_neutral_union.
          eapply exp_eval_entails; eauto. 
          rewrite empty_neutral_union.
          eapply entails_empty.
          rewrite empty_neutral_union.
          eapply entails_empty.
          eapply Equal_ST.
          eapply union_m.
          eapply transpose_union.
        }
        
      * rewrite H7. rewrite <- (cp_eqns_agree H); eauto.
        eapply entails_monotonic_add.
        rewrite <- H13. reflexivity.
    + rewrite zip2Ann_get; eauto. admit.
    +
      Lemma 
        : moreDefined (cp_eqns Gamma lv) (cp_eqns Gamma lv) e (cp_choose_exp Gamma e)
      unfold cp_choose_exp. case_eq (exp_eval Gamma e); intros.
      case_eq a; intros; subst.
      * hnf; intros.
        case_eq (Exp.exp_eval E e); intros.
        exploit exp_eval_same; try eapply H17; eauto.
        simpl; eauto. inv X; econstructor; eauto.
        econstructor.
      * reflexivity.
      * reflexivity.
    + unfold cp_choose_exp. case_eq (exp_eval Gamma e); intros; eauto.
      case_eq a; intros; subst; simpl. eapply incl_empty. eassumption.
  - admit.
  - admit.
  - econstructor. 
    
    


Qed.

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
