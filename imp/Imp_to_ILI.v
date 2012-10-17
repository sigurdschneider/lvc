Require Import List Plus.
Require Import Var Imp Imp_Types IL IL_raise IL_Types AutoIndTac EnvTy.

Import ImpTS.

Set Implicit Arguments.

(** Control Structure Compilation *)

(** In this file we compile traditional structured control flow 
   to recursive functions *)

Fixpoint compile (c:com) (cont:stmt) : stmt :=
match c with
  | Skip => cont
  | Ass x e => stmtExp x e cont
  | Seq c c' => compile c (compile c' cont)
  | If x c c' =>
    let cont' := raiseL 0 1 cont in (* avoid exponential blow-up by not duplicating continuations of conditionals *)
      let s := (stmtIf x (compile c  (stmtGoto (LabI 0) nil)) 
                         (compile c' (stmtGoto (LabI 0) nil))) in
      stmtLet cont' nil s
  | While x c =>
    let cont' := raiseL 0 1 cont in
      let body := compile c (stmtGoto (LabI 0) nil) in
        let s := (stmtIf x body cont') in
          stmtLet s nil (stmtGoto (LabI 0) nil)
end.

Lemma compile_typed ET c ET' (cd:comOfType ET c ET') rt
  : forall LT cont, 
    stmtOfType LT ET' cont rt 
    -> stmtOfType LT ET (compile c cont) rt.
Proof.
  general induction cd; simpl; eauto. 
  econstructor; eauto using stmtOfType, subEnv_update, subEnv_refl.

  econstructor. instantiate (1:=ET'). firstorder.  firstorder.
  simpl.  eapply stmtOfType_raiseL with (LT':=nil). simpl. 
  instantiate (1:=rt). cbv; eauto.
  econstructor; eauto; try instantiate (1:=ET); firstorder. 
  eapply IHcd1. econstructor. constructor. simpl. econstructor.
  reflexivity. hnf; firstorder. 
  eapply IHcd2. econstructor. constructor. simpl. econstructor.
  reflexivity. hnf; firstorder.
  econstructor. instantiate (1:=ET). firstorder. firstorder. 
  econstructor. instantiate (1:=t). instantiate (1:=nil). cbv; eauto.
  instantiate (1:=rt).
  eapply IHcd. econstructor. constructor. constructor. reflexivity. hnf; firstorder.
  eapply stmtOfType_raiseL with (LT':=nil); eauto.
  econstructor. constructor. simpl. econstructor. reflexivity. simpl. hnf. intros. eassumption.
Qed.

Lemma raiseL_through a k c cont
  :  raiseL a k (compile c cont) = compile c (raiseL a k cont). 
Proof.
  revert a k cont; induction c; intros; simpl; try rewrite IHc; try rewrite IHc1; try rewrite IHc2; eauto.
f_equal. pose proof (raiseL_swap a k 0). 
assert (a + 1 + 0 = S a) by omega. rewrite H0 in H. rewrite H. f_equal. f_equal. omega.
f_equal. f_equal. pose proof (raiseL_swap a k 0). 
assert (a + 1 + 0 = S a) by omega. rewrite H0 in H. rewrite H. f_equal. f_equal. f_equal. omega. 
Qed.

Theorem compile_correct_star E c E' : sem E c E' 
  -> forall L cont, exists L',
    star istep (E,  L,     compile c cont) 
               (E',  L'++L, raiseL 0 (length L') cont).
Proof.
  intros A. pattern E, c, E'.
  eapply (sem_mut_ind) with (P0:= (fun (E:env val) x c E' =>
      forall (L : labenv) (EB:env val) cont,
      exists L',
        star istep (E, blockI EB
          (stmtIf x
            (compile c (stmtGoto (LabI 0) nil))
            (raiseL 0 1 cont)) nil::L,
          stmtIf x
            (compile c (stmtGoto (LabI 0) nil))
            (raiseL 0 1 cont))
        (E', L'++L, raiseL 0 (length L') cont))); intros.

  (* Skip *)
  exists nil; simpl. rewrite raiseL_null; eauto using star.

  (* Assignment *)
  inv H. exists nil; simpl. rewrite raiseL_null;
    econstructor; econstructor; eassumption; eauto using star.

  (* Sequentialization *)
  edestruct H0 with (L:=L) as [L1 HL1]; eauto.
  edestruct H2 with (L:=L1++L) as [L2 HL2]; eauto. 
  exists (L2++L1).
  rewrite app_length. rewrite <- app_assoc. eapply star_trans; eauto. 
  rewrite raiseL_through. rewrite <- raiseL_cumm. eauto.
  
  (* if true *)
  edestruct H1 as [L1 HL1]; eauto.
  instantiate (1:=(stmtGoto (LabI 0) nil)) in HL1.
  simpl. eexists. econstructor. econstructor.
  econstructor. econstructor. assumption. 
  eapply star_trans. eassumption. simpl.
  econstructor. econstructor. simpl. eapply get_shift; constructor.
  reflexivity. simpl.
  instantiate (1:= blockI E0 (raiseL 0 1 cont) nil::nil). simpl.
  rewrite drop_app; simpl. eapply star_refl.

  (* if false *)
  edestruct H1 as [L1 HL1]; eauto.
  instantiate (1:=(stmtGoto (LabI 0) nil)) in HL1.
  simpl. eexists. econstructor. constructor.
  econstructor. eapply istepIfF. assumption. 
  eapply star_trans. eassumption. simpl.
  econstructor. econstructor. simpl. eapply get_shift; constructor.
  reflexivity. simpl.
  instantiate (1:= blockI E0 (raiseL 0 1 cont) nil::nil). simpl.
  rewrite drop_app; simpl. eapply star_refl. 
  
  (* while case *)
  edestruct H0. simpl. 
  eexists. econstructor. constructor. econstructor.
  constructor. constructor. reflexivity. simpl.
  instantiate (1:=x0). 
  instantiate (1:=cont) in H1. instantiate (1:=L) in H1. 
  eapply H1.  

  (* while true *)
  edestruct H1; eauto. 
  edestruct H3. eexists. 
  econstructor. constructor. assumption.
  eapply star_trans. eapply H4. simpl.
  econstructor. constructor. simpl. eapply get_shift. constructor.
  simpl. reflexivity.
  simpl. rewrite drop_app. simpl. instantiate (1:=cont) in H5. 
  instantiate (1:=L) in H5. instantiate (1:=EB) in H5. 
  instantiate (1:=x1). simpl. eapply H5.


  (* while false *)
  eexists (blockI EB _ nil::nil). 
  econstructor. eapply istepIfF. assumption.
  simpl. eapply star_refl.

  assumption.
Qed.

Theorem compile_correct E c E' x : sem E c E' 
  -> ievalsTo (E, nil, compile c (stmtReturn x)) (E'[x]). 
Proof.
  intros. destruct (compile_correct_star H nil (stmtReturn x)).
  eauto using ievalsTo_star.
Qed.

(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr" "../il" "../isa" "../") ***
*** End: ***
*)
