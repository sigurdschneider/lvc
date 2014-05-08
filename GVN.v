Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL ParamsMatch Sim SimApx Alpha Coherence Fresh Annotation.

Require Import Liveness Filter.

Set Implicit Arguments.
Unset Printing Records.


Definition eqn := (exp * exp)%type.

Instance OrderedType eqn : OrderedType eqn.
Admitted.

Definition satisfies (E:onv val) (gamma:eqn) := 
  exp_eval E (fst gamma) = exp_eval E (snd gamma).

Inductive moreDef {X} : option X -> option X -> Prop :=
  | moreDefSome v v' : moreDef (Some v) (Some v')
  | moreDefNone x : moreDef None x.

Definition satisfiesAll (E:onv val) (Gamma:set eqn) := 
  forall gamma, gamma ∈ Gamma -> satisfies E gamma.

Definition entails Gamma Γ' := forall E, satisfiesAll E Gamma -> satisfiesAll E Γ'. 

Definition moreDefined Gamma e e' := 
  forall E E', satisfiesAll E Gamma -> satisfiesAll E' Gamma -> fstNoneOrR eq (exp_eval E e) (exp_eval E' e').

Definition moreDefinedArgs Gamma Y Y' := 
  forall E E', satisfiesAll E Gamma -> satisfiesAll E' Gamma -> 
          fstNoneOrR eq (omap (exp_eval E) Y) (omap (exp_eval E') Y').

(*Definition moreDefined Gamma Γ' e e' := 
  forall E, satisfies E Gamma -> forall E', satisfies E' Γ' -> moreDef (exp_eval E e) (exp_eval E' e').*)

Definition freeVars (gamma:exp * exp) := 
  Exp.freeVars (fst gamma) ∪ Exp.freeVars (snd gamma).

Definition remove (Gamma:set eqn) G :=
  filter (fun gamma => B[freeVars gamma ∩ G [=] ∅]) Gamma.

Definition subst_eqn (ϱ : env exp) (e: eqn) :=
  (subst_exp ϱ (fst e), subst_exp ϱ (snd e)).

Definition subst_eqns (ϱ : env exp) (G:set eqn) :=
  map (subst_eqn ϱ) G.

Definition sid := fun x => Var x.

Definition eqns_freeVars (Gamma:set eqn) := fold union (map freeVars Gamma) ∅.

Inductive eqn_sound : list (params*set eqn) 
                      -> stmt 
                      -> ann (set eqn) 
                      -> ann (list exp) 
                      -> Prop :=
| EqnOpr x Lv b e al Gamma e' al' 
  : eqn_sound Lv b al al'
    (* make sure the rest conforms to the new assignment *)
    -> entails (Gamma ∪ {{ (Var x,e) }}) (getAnn al)
    -> moreDefined Gamma e e'
    -> eqns_freeVars (getAnn al) [<=] eqns_freeVars Gamma ++ {x; {}}
    -> eqn_sound Lv (stmtExp x e b) (ann1 Gamma al) (ann1 (e'::nil) al')
| EqnIf Lv e e' b1 b2 Gamma al1 al2 al1' al2'
  : eqn_sound Lv b1 al1 al1'
  -> eqn_sound Lv b2 al2 al2'
  -> entails Gamma (getAnn al1)
  -> entails Gamma (getAnn al2)
  -> eqns_freeVars (getAnn al1)[<=]eqns_freeVars Gamma
  -> eqns_freeVars (getAnn al2)[<=]eqns_freeVars Gamma
  -> moreDefined Gamma e e'
  -> eqn_sound Lv (stmtIf e b1 b2) (ann2 Gamma al1 al2) (ann2 (e'::nil) al1' al2')
| EqnGoto l Y Y' Lv Gamma Z EqS
  : get Lv (counted l) (Z,EqS)
    -> length Y = length Y'
    -> entails Gamma (subst_eqns (sid [Z <-- Y']) EqS)
    -> moreDefinedArgs Gamma Y Y'
    -> eqn_sound Lv (stmtGoto l Y) (ann0 Gamma) (ann0 Y')
| EqnReturn Lv e e' Gamma
  : entails Gamma {{(e,e')}}
    -> eqn_sound Lv (stmtReturn e') (ann0 Gamma) (ann0 (e::nil))
| EqnLet Lv s Z b Gamma EqS als alb als' alb'
  : eqn_sound ((Z,EqS)::Lv) s als als'
  -> eqn_sound ((Z,EqS)::Lv) b alb alb'
  -> entails (Gamma ∪ EqS) (getAnn alb)
  -> entails Gamma (getAnn alb)
  -> eqn_sound Lv (stmtLet Z s b) (ann2 Gamma als alb) (ann2 nil als' alb').

Fixpoint compile (s:stmt) (a:ann (list exp)) :=
  match s, a with
    | stmtExp x _ s, ann1 (e'::nil) an => 
      stmtExp x e' (compile s an)
    | stmtIf _ s t, ann2 (e'::nil) ans ant => 
      stmtIf e' (compile s ans) (compile t ant)
    | stmtGoto f _, ann0 Y' => 
      stmtGoto f Y'
    | stmtReturn _, ann0 (e'::nil) => stmtReturn e'
    | stmtLet Z s t, ann2 nil ans ant => 
      stmtLet Z (compile s ans) (compile t ant)
    | s, _ => s
  end.

Definition ArgRel (G:(params * set eqn)) (VL VL': list val) : Prop := 
  True.

Definition ParamRel (G:(params * set eqn)) (Z Z' : list var) : Prop := 
  Z = Z'.


Definition blockRel (AL:list (params*set eqn)) (L:F.labenv) (L':F.labenv) := 
  forall n blk lvZ, get AL n lvZ -> get L n blk -> True.


(* problem is Gamma that satisfies nothing 
Lemma entails_freeVars Gamma Γ'
 : entails Gamma Γ' -> eqns_freeVars Γ' ⊆ eqns_freeVars Gamma.
Proof.
  intros. hnf in H.
  unfold eqns_freeVars in *.
  hnf. intros. 
  assert (exists l, l ∈ (map freeVars Γ') /\ a ∈ l) by admit.
  destruct H1. dcr. eapply map_2 in H2.
  destruct H2. dcr. decide (a \In fold union (map freeVars Gamma) {}); eauto.
  exfalso. hnf in n.
  (* construct E that maps x to None *).
  
  
  
Qed.
*)

Lemma sim_DVE r L L' V V' s LV eqns repl G G'
:
  satisfiesAll V (getAnn eqns) 
-> satisfiesAll V' (getAnn eqns)
-> eqn_sound LV s eqns repl
-> simL' r ArgRel ParamRel LV L L'
-> ssa G s G'
-> eqns_freeVars (getAnn eqns) ⊆ G
-> paco2 (@psimapx F.state _ F.state _) r (L,V, s) (L',V', compile s repl).
Proof.
  general induction s; simpl; invt eqn_sound; invt ssa; simpl in * |- *.
  + specialize (H13 V V'). exploit H13; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl; eauto. stuck.
    - pfold. econstructor; try eapply plusO.
      econstructor; eauto using eq_sym.
      econstructor; eauto using eq_sym.
      left. eapply IHs; eauto.
      eapply H10. admit. eapply H10. admit. 
      rewrite <- H4. eauto.
  + specialize (H17 V V'). exploit H17; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl; eauto. stuck.
    - pfold. case_eq (val2bool y); intros. 
      econstructor; try eapply plusO.
      econstructor; eauto using eq_sym.
      econstructor; eauto using eq_sym.
      left. eapply IHs1; eauto.
      rewrite <- H4; eauto. 
      econstructor; try eapply plusO.
      econstructor 3; eauto using eq_sym.
      econstructor 3; eauto using eq_sym.
      left. eapply IHs2; try eapply H9; eauto.
      rewrite <- H4; eauto. 
  + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    (* hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
    (*    decide (length Z = length Y). *)
    specialize (H13 V V'). exploit H13; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl. eauto. stuck.
    - unfold simL in H1.
      edestruct AIR5_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption.
      edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr. 
      simpl in *. repeat get_functional; subst.
      inv H23. hnf in H27. subst bZ.
      eapply sim_drop_shift. eapply H28; eauto. eapply I.
    - pfold. econstructor 3; try eapply star_refl. eauto. stuck; eauto.
  + pfold. econstructor 2; try eapply star_refl.
    simpl. eapply H7 in H.
    eapply H7. rewrite H; eauto. simpl. 
    stuck. stuck.
  + pfold. econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    simpl. left. eapply IHs2; eauto. 
    - simpl in *; eapply agree_on_incl; eauto.
    - eapply simL_mon; eauto. eapply simL_extension'; eauto.
      hnf; intros. hnf in H3. hnf in H2. dcr; subst.
      split; eauto. eapply filter_filter_by_length; eauto.
      hnf; intros.
      eapply IHs1; eauto.
      * hnf in H2. dcr; subst. simpl.
        eapply agree_on_update_filter'. eauto.
        eapply agree_on_incl; eauto.
      * split; reflexivity.
Qed.

Print Assumptions sim_DVE.

(*           
Lemma sim_DVE L L' V V' s LV lv
: agree_on (getAnn lv) V V'
-> true_live_sound LV s lv
-> simL' r ArgRel ParamRel LV L L'
-> @simapx F.state _ F.state _ (L,V, s) (L',V', compile s lv).
Proof.
  general induction s; simpl; inv H0; simpl in * |- *.
  + case_eq (exp_eval V e); intros. destruct if. 
    - eapply simS; try eapply plusO.
      econstructor; eauto.
      econstructor; eauto. instantiate (1:=v).
      erewrite exp_eval_live; eauto using agree_on_sym.
      eapply IHs; eauto. eapply agree_on_update_same. 
      eapply agree_on_incl; eauto. 
    - eapply simapx_expansion_closed; 
      [ | eapply S_star; [ econstructor; eauto | eapply star_refl ]
        | eapply star_refl].
      eapply IHs; eauto. eapply agree_on_update_dead; eauto.
      eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition.
    - eapply simErr; [| eapply star_refl|]; eauto. stuck.
  + case_eq (val2bool (V x)); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto. econstructor; eauto. 
    rewrite <- H; eauto. eapply IHs1; eauto using agree_on_incl.
    eapply simS; try eapply plusO.
    econstructor 3; eauto. econstructor 3; eauto.
    rewrite <- H; eauto. eapply IHs2; eauto using agree_on_incl.
  + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
(*    hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
    decide (length Z = length Y). 
    unfold simL in H1.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr. 
    simpl in *. repeat get_functional; subst.
    inv H16. hnf in H20. dcr; simpl in *. subst bZ.
    eapply simS; try eapply plusO.
    econstructor; eauto. simpl. congruence.
    econstructor; eauto. simpl. hnf in H21. dcr. simpl in *. subst.
    simpl.  
    eapply argsLive_filter_length; eauto.
    simpl in * |- *.
    unfold updE. eapply H21.
    hnf. simpl. 
    rewrite <- lookup_list_filter_by_commute.
    exploit argsLive_filter_filter_by; eauto.
    rewrite <- X. eapply lookup_list_agree.
    eapply agree_on_incl; eauto using agree_on_sym.
    eapply filter_incl; eauto.
    congruence.
    rewrite lookup_list_length; congruence.
    subst. rewrite lookup_list_length.
    eapply argsLive_filter_length; eauto.
    eapply simE; try eapply star_refl; eauto; stuck.
    eapply simE; try eapply star_refl; eauto; stuck; eauto.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    simpl in *. repeat get_functional; subst.

  + eapply simE; try eapply star_refl.
    simpl. rewrite H; eauto. simpl. 
    stuck. stuck.
  + econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    simpl. eapply IHs2; eauto. 
    - simpl in *; eapply agree_on_incl; eauto.
    - eapply simL_extension; eauto. hnf; intros.
      eapply IHs1; eauto.
      * hnf in H2. subst. simpl.
        eapply agree_on_update_filter'. eauto.
        eapply agree_on_incl; eauto.
      * split; reflexivity.
Qed.
*)

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
