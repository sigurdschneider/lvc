Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL ParamsMatch Sim SimApx Alpha Coherence Fresh Annotation MoreExp.

Require Import Liveness Filter.

Set Implicit Arguments.
Unset Printing Records.


Definition eqn := (exp * exp)%type.

Instance OrderedType : OrderedType exp.

Admitted.

Definition satisfies (E:onv val) (gamma:eqn) := 
  exp_eval E (fst gamma) = exp_eval E (snd gamma).

Inductive moreDef {X} : option X -> option X -> Prop :=
  | moreDefSome v v' : moreDef (Some v) (Some v')
  | moreDefNone x : moreDef None x.

Definition satisfiesAll (E:onv val) (Gamma:set eqn) := 
  forall gamma, gamma ∈ Gamma -> satisfies E gamma.

Definition sem_entails Gamma Γ' := forall E, satisfiesAll E Gamma -> satisfiesAll E Γ'. 

Definition freeVars (gamma:exp * exp) := 
  Exp.freeVars (fst gamma) ∪ Exp.freeVars (snd gamma).

Definition eqns_freeVars (Gamma:set eqn) := fold union (map freeVars Gamma) ∅.

Definition entails Gamma Γ' := (forall E, satisfiesAll E Gamma -> satisfiesAll E Γ') 
/\ eqns_freeVars Γ' ⊆ eqns_freeVars Gamma. 

Definition moreDefined Gamma Γ' e e' := 
  forall E E', satisfiesAll E Gamma -> satisfiesAll E' Γ' -> fstNoneOrR eq (exp_eval E e) (exp_eval E' e').

Definition moreDefinedArgs Gamma Γ' Y Y' := 
  forall E E', satisfiesAll E Gamma -> satisfiesAll E' Γ' -> 
          fstNoneOrR eq (omap (exp_eval E) Y) (omap (exp_eval E') Y').

(*Definition moreDefined Gamma Γ' e e' := 
  forall E, satisfies E Gamma -> forall E', satisfies E' Γ' -> moreDef (exp_eval E e) (exp_eval E' e').*)


Definition remove (Gamma:set eqn) G :=
  filter (fun gamma => B[freeVars gamma ∩ G [=] ∅]) Gamma.

Definition subst_eqn (ϱ : env exp) (e: eqn) :=
  (subst_exp ϱ (fst e), subst_exp ϱ (snd e)).

Definition subst_eqns (ϱ : env exp) (G:set eqn) :=
  map (subst_eqn ϱ) G.

Definition sid := fun x => Var x.


Inductive eqn_sound : list (params*set eqn*set eqn*set eqn*set eqn) 
                      -> stmt 
                      -> ann (set eqn) 
                      -> ann (set eqn) 
                      -> ann (list exp) 
                      -> Prop :=
| EqnOpr x Lv b e Gamma al Γ' (al':ann (set eqn)) e' al' cl
  : eqn_sound Lv b al al' cl
    (* make sure the rest conforms to the new assignment *)
    -> entails (Gamma ∪ {{ (Var x,e) }}) (getAnn al)
    -> entails (Γ' ∪ {{ (Var x,e') }}) (getAnn al')
    -> moreDefined Gamma Γ' e e'
    -> eqn_sound Lv (stmtExp x e b) (ann1 Gamma al) (ann1 Γ' al') (ann1 (e'::nil) cl)
| EqnIf Lv e e' b1 b2 Gamma Γ' al1 al2 al1' al2' cl1 cl2
  : eqn_sound Lv b1 al1 al1' cl1
  -> eqn_sound Lv b2 al2 al2' cl2
 (* TODO: include information about condition *)
  -> entails Gamma (getAnn al1)
  -> entails Gamma (getAnn al2)
  -> entails Γ' (getAnn al1')
  -> entails Γ' (getAnn al2')
  -> moreDefined Gamma Γ' e e'
  -> eqn_sound Lv (stmtIf e b1 b2) (ann2 Gamma al1 al2) (ann2 Γ' al1' al2') (ann2 (e'::nil) cl1 cl2)
| EqnGoto l Y Y' Lv Gamma Γ' Z Γf Γf' EqS EqS'
  : get Lv (counted l) (Z,Γf, EqS, Γf',EqS')
    -> length Y = length Y'
    -> entails Gamma (subst_eqns (sid [Z <-- Y]) EqS)
    -> entails Γ' (subst_eqns (sid [Z <-- Y']) EqS')
    -> moreDefinedArgs Gamma Γ' Y Y'
    -> eqn_sound Lv (stmtGoto l Y) (ann0 Gamma) (ann0 Γ') (ann0 Y')
| EqnReturn Lv e e' Gamma Γ'
  : moreDefined Gamma Γ' e e'
    -> eqn_sound Lv (stmtReturn e) (ann0 Gamma) (ann0 Γ') (ann0 (e'::nil))
| EqnLet Lv s Z b Gamma Γ' EqS EqS' als alb als' alb' cls clb
  : eqn_sound ((Z,Gamma, EqS, Γ', EqS')::Lv) s als als' cls
  -> eqn_sound ((Z,Gamma, EqS, Γ', EqS')::Lv) b alb alb' clb
  -> entails (Gamma ∪ EqS) (getAnn als)
  -> entails Gamma (getAnn alb)
  -> entails (Γ' ∪ EqS') (getAnn als')
  -> entails Γ' (getAnn alb')
  -> eqns_freeVars EqS ⊆ eqns_freeVars Gamma ++ of_list Z
  -> eqns_freeVars EqS' ⊆ eqns_freeVars Γ' ++ of_list Z
  -> eqn_sound Lv (stmtLet Z s b) (ann2 Gamma als alb) (ann2 Γ' als' alb') (ann2 nil cls clb).

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

Definition ArgRel (G:list var*set eqn*set eqn*set eqn*set eqn) (VL VL': list val) : Prop := 
  let '(Z, Gamma, EqS, Γ', EqS') := G in
  length Z = length VL 
  /\ length VL = length VL' 
  /\ (forall E:onv val, satisfiesAll E Gamma -> 
                  satisfiesAll (E[Z <-- List.map Some VL]) (Gamma ∪ EqS))
  /\ (forall E:onv val, satisfiesAll E Γ' -> 
                  satisfiesAll (E[Z <-- List.map Some VL']) (Γ' ∪ EqS')).


Definition ParamRel (G:params*set eqn*set eqn*set eqn*set eqn) (Z Z' : list var) : Prop := 
  let '(Zb, Gamma, EqS, Γ', EqS') := G in  
  Z = Z' /\ Zb = Z.


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

Lemma eqns_freeVars_add Gamma x e
  : eqns_freeVars (Gamma ++ {{(Var x, e)}}) [=] eqns_freeVars (Gamma) ∪ {{ x }} ∪ Exp.freeVars e.
Proof.
Admitted.

Lemma eqns_freeVars_union Gamma Γ'
  : eqns_freeVars (Gamma ++ Γ') [=] eqns_freeVars (Gamma) ∪ eqns_freeVars Γ'.
Proof.
Admitted.

Ltac dowith c t :=
  match goal with 
    | [ H : c _ _ _ _ |- _ ] => t H
  end.

Lemma sim_DVE r L L' V V' s LV eqns eqns' repl G G'
:
  satisfiesAll V (getAnn eqns) 
-> satisfiesAll V' (getAnn eqns')
-> eqn_sound LV s eqns eqns' repl
-> simL' r ArgRel ParamRel LV L L'
-> ssa G s G'
-> eqns_freeVars (getAnn eqns) ⊆ G
-> paco2 (@psimapx F.state _ F.state _) r (L,V, s) (L',V', compile s repl).
Proof.
  general induction s; simpl; invt eqn_sound; invt ssa; simpl in * |- *.
  + unfold moreDefined in H15; exploit H15; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl; eauto. stuck.
    - pfold. econstructor; try eapply plusO.
      econstructor; eauto using eq_sym.
      econstructor; eauto using eq_sym.
      left. eapply IHs; eauto.
      eapply H10. admit. eapply H14. admit.
      destruct H10. rewrite eqns_freeVars_add in H9.
      rewrite H9. rewrite H13. rewrite H4. clear_all; cset_tac; intuition.
  + unfold moreDefined in H18; exploit H18; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl; eauto. stuck.
    - pfold. case_eq (val2bool y); intros. 
      econstructor; try eapply plusO.
      econstructor; eauto using eq_sym.
      econstructor; eauto using eq_sym.
      left. eapply IHs1; eauto. 
      eapply H10; eauto.
      eapply H13; eauto.
      destruct H10. rewrite <- H4; eauto. 
      econstructor; try eapply plusO.
      econstructor 3; eauto using eq_sym.
      econstructor 3; eauto using eq_sym.
      left. eapply IHs2; try eapply H9; eauto.
      eapply H11; eauto.
      eapply H17; eauto.
      destruct H11. rewrite <- H4; eauto.
  + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    (* hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
    decide (length bZ = length Y).
    hnf in H15. exploit H15; eauto. inv X.
    - pfold. econstructor 3; try eapply star_refl. eauto. stuck.
    - edestruct AIR5_length; try eassumption; dcr.
      edestruct get_length_eq; try eassumption.
      edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr. 
      simpl in *. repeat get_functional; subst.
      inv H24. hnf in H28; simpl in H28; dcr; subst.
      eapply sim_drop_shift. eapply H29; eauto. hnf. simpl; repeat split. 
      exploit omap_length; eauto. unfold var in *. rewrite e. congruence.
      intros. hnf in H9. dcr.
      Lemma satisfiesAll_subst E Z EqS Y Γf y
      :  length Z = length Y
         -> eqns_freeVars EqS ⊆ eqns_freeVars Γf ∪ of_list Z
         -> eqns_freeVars Γf ∩ of_list Z = ∅
         -> ⎣y ⎦ = omap (exp_eval E) Y
         -> satisfiesAll E Γf
         -> satisfiesAll E (subst_eqns (sid [Z <-- Y]) EqS)
         -> satisfiesAll (E [Z <-- List.map Some y]) (Γf ++ EqS).
      Proof.
        intros.
        Lemma satisfiesAll_union E Gamma Γ'
              : satisfiesAll E (Gamma ∪ Γ')
                <-> satisfiesAll E Gamma /\ satisfiesAll E Γ'.
        Proof.
          split.
          intros H; split; hnf; intros; eapply H; cset_tac; intuition.
          intros [A B]; hnf; intros. cset_tac. destruct H; auto.
        Qed.
        eapply satisfiesAll_union; split.
        Lemma satisfiesAll_update_dead E Gamma Z vl
        : length Z = length vl
          -> satisfiesAll E Gamma
          -> eqns_freeVars Gamma ∩ of_list Z = ∅
          -> satisfiesAll (E[Z <-- vl]) Gamma.
        Proof.
          intros. hnf; intros. hnf; intros.
          hnf in H; exploit H; eauto. hnf in X.
          erewrite exp_eval_agree; try eapply X.
          symmetry. 
          erewrite exp_eval_agree; try eapply X; eauto using eq_sym.
          symmetry. 
          erewrite <- minus_inane_set.
          eapply update_with_list_agree_minus; eauto. reflexivity.
          exfalso; admit.
          erewrite <- minus_inane_set.
          symmetry.
          eapply update_with_list_agree_minus; eauto. reflexivity.
          exfalso; admit.
          eapply H0; eauto.
        Qed.
        eapply satisfiesAll_update_dead; eauto. 
        rewrite map_length; eauto.
        exploit omap_length; eauto. congruence.
        revert_except EqS. pattern EqS.
        eapply set_induction; intros. 
        - hnf; intros. exfalso.  eapply H. eapply H6.
        - hnf; intros. rewrite Add_Equal in H1.
          rewrite H1 in H8. eapply add_iff in H8. destruct H8.
          hnf. hnf in H7.
          unfold satisfies in H7.
          specialize (H7 (subst_eqn (sid [Z <-- Y]) x)).
          Lemma eval_exp_subst E y Y Z e
          : length Z = length Y
            -> ⎣y ⎦ = omap (exp_eval E) Y
            -> exp_eval (E [Z <-- List.map Some y]) e = 
              exp_eval E (subst_exp (sid [Z <-- Y]) e). 
          Proof.
            general induction e; simpl; eauto.
            decide (v ∈ of_list Z).
            eapply length_length_eq in H.
            general induction H; simpl in * |- *; eauto.
            symmetry in H0. monad_inv H0. simpl.
            lud; eauto. eapply IHlength_eq; eauto.
            cset_tac; intuition.
            remember (sid [Z <-- Y] v); intros. symmetry in Heqy0; eauto.
            eapply update_with_list_lookup_not_in in Heqy0. 
            remember (E [Z <-- List.map Some y] v); intros. 
            symmetry in Heqy1.
            eapply update_with_list_lookup_not_in in Heqy1; eauto.
            subst; simpl; eauto. eauto.
            erewrite IHe1; eauto.
            erewrite IHe2; eauto.
          Qed.
          intros. assert (x = gamma) by admit. subst gamma.
          repeat erewrite eval_exp_subst; eauto. eapply H7.
          eapply map_1. admit. rewrite H1. cset_tac; eauto.
          eapply H; eauto. rewrite <- H3. admit.
          hnf; intros. eapply H7. admit.
      Qed.
      eapply satisfiesAll_subst; eauto.
      admit. admit.

    - pfold. econstructor 3; try eapply star_refl. eauto. stuck; eauto.
      get_functional; subst. simpl in *. congruence.
    - pfold. econstructor 3; try eapply star_refl. eauto. stuck; eauto.
  + simpl. hnf in H7; exploit H7; eauto. inv X; eauto.
    - pfold. econstructor 3; try eapply star_refl. simpl. congruence.
      stuck.
    - pfold. econstructor 2; try eapply star_refl. simpl. congruence.
      stuck. stuck.
  + pfold. econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    simpl. left. eapply IHs2; eauto.
    - eapply H11; eauto.
    - eapply H14; eauto.
    - eapply simL_mon; eauto. eapply simL_extension'; eauto.
      * hnf; intros. destruct a as [[[[Zb Γb] EqSb] Γb'] EqSb'].
        hnf in H5. hnf in H6. dcr; subst.
        split; eauto. unfold var in *. congruence.
      * hnf; intros. hnf in H5; dcr.
        eapply IHs1; eauto.
        eapply H10. specialize (H23 V). eapply H23; eauto.
        eapply H12. eapply H26; eauto.
        destruct H10. rewrite H10. rewrite eqns_freeVars_union.
         rewrite H18. rewrite H4. clear_all; cset_tac; intuition.
      * hnf; split; eauto.
    - destruct H11. rewrite H6; eauto.
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
