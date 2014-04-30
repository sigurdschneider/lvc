Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL ParamsMatch Sim SimApx Alpha Coherence Fresh.

Require Import Liveness.

Set Implicit Arguments.
Unset Printing Records.

Opaque compute_prop.

Notation "B[ x ]" := (if [ x ] then true else false).

Fixpoint filter_by {A B} (f:A -> bool) (L:list A) (L':list B) : list B :=
  match L, L' with
    | x :: L, y::L' => if f x then y :: filter_by f L L' else filter_by f L L' 
    | _, _ => nil
  end.

Fixpoint compile (s:stmt) (a:ann live) :=
  match s, a with
    | stmtExp x e s, annExp lv an => 
      if [x ∈ getAnn an] then stmtExp x e (compile s an)
                         else compile s an
    | stmtIf x s t, annIf _ ans ant => stmtIf x (compile s ans) (compile t ant)
    | stmtGoto f Y, annGoto lv => 
      stmtGoto f (List.filter (fun y => B[y ∈ lv]) Y) 
    | stmtReturn x, annReturn _ => stmtReturn x
    | stmtLet Z s t, annLet lv ans ant => 
      stmtLet (List.filter (fun x => B[x ∈ getAnn ans]) Z)
              (compile s ans) (compile t ant)
    | s, _ => s
  end.

Definition ArgRel (G:(live * params)) (VL VL': list val) : Prop := 
  VL' = (filter_by (fun x => B[x ∈ (fst G)]) (snd G) VL) /\
  length (snd G) = length VL.

Definition ParamRel (G:(live * params)) (Z Z' : list var) : Prop := 
  Z' = (List.filter (fun x => B[x ∈ (fst G)]) Z) /\ snd G = Z.

Lemma lookup_list_filter_by_commute A B C (V:A->B) (Z:list C) Y p
: length Z = length Y 
  -> lookup_list V (filter_by p Z Y) =
    filter_by p Z (lookup_list V Y).
Proof.
  intros. eapply length_length_eq in H. 
  general induction H; simpl; eauto.
  + destruct if; simpl; rewrite IHlength_eq; eauto.
Qed.

Lemma argsLive_filter_length lv blv Z Y
: argsLive lv blv Y Z
  -> length (List.filter (fun x : var => B[x ∈ blv]) Z) =
    length (List.filter (fun y : var => B[y ∈ lv]) Y).
Proof.
  intros. general induction H; simpl; eauto.
  destruct_prop (z ∈ blv); destruct_prop (y ∈ lv); try tauto; simpl.
  - rewrite IHargsLive; eauto.
Qed.

Lemma filter_incl lv Y
  : of_list (List.filter (fun y : var => B[y ∈ lv]) Y) ⊆ lv.
Proof.
  general induction Y; simpl. 
  - cset_tac; intuition.
  - destruct_prop (a ∈ lv); simpl. cset_tac; intuition. rewrite <- H0; eauto.
    rewrite <- IHY; eauto.
    eauto.
Qed.

Tactic Notation "destruct-if" "in" hyp(H) :=
  match goal with 
    | H : context [if sumbool_bool ?P then _ else _] |- _ => destruct P
    | H : context [if ?P then _ else _] |- _ => destruct P
  end.

Tactic Notation "destruct-if" :=
  match goal with
    | |- context [if (if ?P then true else false) then _ else _] => destruct P
    | |- context [if ?P then _ else _] => destruct P
  end.

Lemma argsLive_filter_filter_by lv blv Y Z
: argsLive lv blv Y Z
  -> List.filter (fun y : var => B[y ∈ lv]) Y
    = filter_by (fun x : var => B[x ∈ blv]) Z Y.
Proof.
  intros. general induction H; simpl; eauto.
  repeat destruct-if; try tauto.
  rewrite IHargsLive; eauto.
Qed.

Lemma agree_on_update_filter lv (V:var -> val) Z VL 
: length Z = length VL
  -> agree_on lv 
             (V [Z <-- VL])
             (V [List.filter (fun x => B[x ∈ lv]) Z <--
                             filter_by (fun x => B[x ∈ lv]) Z VL]).
Proof.
  intros. eapply length_length_eq in H.
  general induction H.
  - eapply agree_on_refl.
  - simpl. repeat destruct-if. simpl. eapply agree_on_update_same.
    eapply agree_on_incl. eapply IHlength_eq. cset_tac; intuition.
    eapply agree_on_update_dead; eauto.
Qed.

Lemma agree_on_update_filter' (lv:set var) (V V':var -> val) Z VL 
: length Z = length VL
  -> agree_on (lv \ of_list Z) V V'
  -> agree_on lv 
             (V [Z <-- VL])
             (V' [List.filter (fun x => B[x ∈ lv]) Z <--
                             filter_by (fun x => B[x ∈ lv]) Z VL]).
Proof.
  intros.
  pose proof (update_with_list_agree _ VL H0 H).
  eapply agree_on_trans. eapply H1.
  eapply agree_on_update_filter. eauto.
Qed.

Lemma filter_filter_by_length {X} {Y} (Z:list X) (VL:list Y) 
: length Z = length VL
  -> forall p, length (List.filter p Z) =
    length (filter_by p Z VL).
Proof.
  intros. eapply length_length_eq in H.
  general induction H; simpl; eauto.
  destruct if; simpl. rewrite IHlength_eq; eauto. eauto.
Qed.

Definition blockRel (AL:list (live*params)) L (L':F.labenv) := (forall n blk lvZ, get AL n lvZ -> get L n blk -> block_Z blk = snd lvZ).

Fixpoint lowerL (d:nat) (k:nat) (s:stmt) :=
  match s with
    | stmtExp x e s => stmtExp x e (lowerL d k s)
    | stmtIf x s t => stmtIf x (lowerL d k s) (lowerL d k t)
    | stmtGoto l Y => 
      if [(counted l) < d]
        then stmtGoto l Y
        else stmtGoto (LabI (counted l - k)) Y
    | stmtReturn x => stmtReturn x
    | stmtLet Z s t => stmtLet Z (lowerL (S d) k s) (lowerL (S d) k t) 
  end.

(*
Lemma sim_drop_shift r (L:F.labenv) E s n
: length L >= n
  -> paco2 (@psimapx F.state _ F.state _) r (drop n L, E, lowerL 0 n s)
        (L, E, s).
Proof.
  revert_all; pcofix CIH; intros. destruct s; simpl.
  - pfold. case_eq (exp_eval E e); intros.
    econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    right. eapply CIH; eauto.
    econstructor 2; try eapply star_refl; eauto. stuck. stuck.
  - pfold. case_eq (val2bool (E x)); intros.
    econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    right; eauto.
    econstructor; try eapply plusO.
    econstructor 3; eauto.
    econstructor 3; eauto.
    eauto.
  - destruct if. exfalso. omega.
    destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    destruct_prop (length (F.block_Z (F.blockI bE bZ bs)) = length Y).
    pfold. econstructor; try eapply plusO.
    econstructor; eauto. simpl. admit.
    econstructor; eauto. simpl.
    right. rewrite drop_drop. orewrite (labN l - n 
Admitted.
*)

Lemma plus_is_step_star (X : Type) (R : rel X) x y
: plus R x y -> exists z, R x z /\ star R z y.
Proof.
  intros. general induction H; eauto using star_refl.
  - destruct IHplus; eauto using plus_star.
Qed.

Lemma get_drop_lab0 (L:F.labenv) l blk
:  get L (counted l) blk
   -> get (drop (labN l) L) (counted (LabI 0)) blk.
Proof.
  intros. eapply drop_get; simpl. orewrite (labN l + 0 = labN l); eauto.
Qed.

Lemma drop_get_lab0 (L:F.labenv) l blk
: get (drop (labN l) L) (counted (LabI 0)) blk
  -> get L (counted l) blk.
Proof.
  intros. eapply get_drop in H; simpl in *. orewrite (labN l + 0 = labN l) in H; eauto.
Qed.

Lemma sim_drop_shift r l L E Y L' E' Y'
: paco2 (@psimapx F.state _ F.state _) r (drop (labN l) L, E, stmtGoto (LabI 0) Y)
        (drop (labN l) L', E', stmtGoto (LabI 0) Y')
  -> paco2 (@psimapx F.state _ F.state _) r (L, E, stmtGoto l Y)
          (L', E', stmtGoto l Y').
Proof.
  intros. pinversion H; subst.
  eapply plus_is_step_star in H0.
  eapply plus_is_step_star in H1.
  destruct H0; destruct H1; dcr. inv H3.
  simpl in *. inv H1; simpl in *.
  pfold. econstructor; try eapply star_plus.
  econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
  econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
  eauto.
  inv H1; inv H2; simpl in *.
  pfold. econstructor 2; try eapply star_refl; eauto. stuck.
  eapply H3. econstructor. 
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  stuck. eapply H4. econstructor.
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  pfold. inv H5. econstructor 2. 
  Focus 2. eapply star_refl.
  Focus 2. econstructor 2. 
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  eauto. simpl; eauto. stuck.
  eapply H3. econstructor.
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  eauto.
  pfold. inv H5. econstructor 2. 
  Focus 2. econstructor 2. 
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  eauto. 
  Focus 2. eapply star_refl.
  simpl; eauto. eauto. stuck.
  eapply H4. econstructor.
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  pfold. inv H5. inv H7. econstructor 2. 
  Focus 2. econstructor 2. 
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  eauto. 
  Focus 2. econstructor 2. 
  econstructor; eauto using get_drop_lab0, drop_get_lab0. 
  eauto. eauto. eauto. eauto.
  inv H1. pfold. econstructor 3; try eapply star_refl; eauto.
  stuck. destruct H2. econstructor. econstructor.
  Focus 2. eapply drop_get. simpl. orewrite (labN l + 0 = labN l).
  eauto. eauto. reflexivity. 
  pfold. econstructor 3; eauto.
  inv H3; simpl in *.
  econstructor.
  econstructor. Focus 2. eapply get_drop in Ldef.
  orewrite (labN l + 0 = labN l) in Ldef. eauto. eauto. reflexivity.
  eauto.
  eapply psimapxd_mon.
Qed.

Lemma sim_DVE r L L' V V' s LV lv
: agree_on (getAnn lv) V V'
-> true_live_sound LV s lv
-> simL' r ArgRel ParamRel LV L L'
-> paco2 (@psimapx F.state _ F.state _) r (L,V, s) (L',V', compile s lv).
Proof.
  general induction s; simpl; inv H0; simpl in * |- *.
  + case_eq (exp_eval V e); intros. destruct if. 
    - pfold. econstructor; try eapply plusO.
      econstructor; eauto.
      econstructor; eauto. instantiate (1:=v).
      erewrite exp_eval_live; eauto using agree_on_sym.
      left. eapply IHs; eauto. eapply agree_on_update_same. 
      eapply agree_on_incl; eauto.
    - eapply simapx_expansion_closed; 
      [ | eapply S_star; [ econstructor; eauto | eapply star_refl ]
        | eapply star_refl]. 
      eapply IHs; eauto. eapply agree_on_update_dead; eauto.
      eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition.
    - pfold. econstructor 3; [| eapply star_refl|]; eauto. stuck.
  + case_eq (val2bool (V x)); intros.
    pfold; econstructor; try eapply plusO.
    econstructor; eauto. econstructor; eauto. 
    rewrite <- H; eauto. left. eapply IHs1; eauto using agree_on_incl.
    pfold; econstructor; try eapply plusO.
    econstructor 3; eauto. econstructor 3; eauto.
    rewrite <- H; eauto. left; eapply IHs2; eauto using agree_on_incl. 
  + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    (* hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
(*    destruct_prop (length Z = length Y). *)
    unfold simL in H1.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr. 
    simpl in *. repeat get_functional; subst.
    inv H16. hnf in H20. dcr; simpl in *. subst bZ.
    eapply sim_drop_shift. eapply H21.
    hnf; intros; simpl. subst. split.
    rewrite <- lookup_list_filter_by_commute.
    exploit argsLive_filter_filter_by; eauto.
    rewrite <- X. eapply lookup_list_agree.
    eapply agree_on_incl; eauto using agree_on_sym.
    eapply filter_incl; eauto. congruence.
    rewrite lookup_list_length; eauto.
    pfold; eapply psimE; try eapply star_refl; eauto; stuck. eauto.
    hnf in H1.
    edestruct AIR5_nth2 as [? [? [? []]]]; eauto; dcr.
    eauto.
  + pfold. econstructor 2; try eapply star_refl.
    simpl. rewrite H; eauto. simpl. 
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
    destruct_prop (length Z = length Y). 
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
    admit.
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

(*

Fixpoint natural {P} (f:P -> list var -> list var) (VL:list (option P)) (s:stmt) : stmt :=
  match s with
   | stmtExp x e s => stmtExp x e (natural f VL s)
   | stmtIf x s1 s2 => stmtIf x (natural f VL s1) (natural f VL s2)
   | stmtGoto l Y => match nth_error VL (counted l) with 
                     | Some (Some p) => stmtGoto l (f p Y)
                     | _ => stmtGoto l Y
                     end
   | stmtReturn x => stmtReturn x
   | stmtLet Z s1 s2 => stmtLet Z (natural f (None::VL) s1) (natural f (None::VL) s2)
   end.

Inductive simB {P} (R: P -> list val -> list val -> Prop) 
: P -> F.labenv -> F.labenv -> F.block -> F.block -> Prop :=
| simBI p L L' E E' Z Z' s s'
  : 
    (forall VL VL', R p VL VL'  
                       -> sim (L, E[Z <-- VL], s) 
                              (L', E'[Z' <-- VL'], s'))
    -> simB R p L L' (F.blockI E Z s) (F.blockI E' Z' s').

Definition simL P (R: P -> list val -> list val -> Prop) PL L L' 
  := AIR5 (simB R) PL L L' L L'.

Definition comp {P} (R R':P -> list val -> list val -> Prop) p VL VL' :=
  exists VL'', R p VL VL'' /\ R' p VL'' VL'.

Definition compf {P} (f f':P -> list val -> list val) p VL :=
  f' p (f p VL).

Definition implements {P} (R:P -> list val -> list val -> Prop) (f:P -> list var -> list var)
  := forall (p:P) (L:list var) E, R p (lookup_list E L) (lookup_list E (f p L)).

Lemma subst_lemma_R P (R: P -> list val -> list val -> Prop) s s' V E E' Z Z' L1 L2 t p PL f
: (forall L L', simL R PL L L' -> 
       forall VL VL', R p VL VL' ->
        sim (L, E[Z <-- VL], s) 
            (L', E'[Z' <-- VL'], s'))
  -> simL R PL L1 L2
  -> implements R f
  -> sim ((F.blockI E Z s :: L1)%list, V, t)
         ((F.blockI E' Z' s' :: L2)%list, V, natural f (List.map Some (p::PL)) t).
Proof.
Admitted.

Lemma R_intro P (R: P -> list val -> list val -> Prop) V L1 L2 t PL f
: simL R PL L1 L2
  -> implements R f
  -> sim (L1, V, t)
         (L2, V, natural f (List.map Some PL) t).
Proof.
Admitted.


Lemma simL_split P (R R': P -> list val -> list val -> Prop) L1 L3 PLA
 : simL (comp R R') PLA L1 L3 -> exists PLB PLC L2,
simL R PLB L1 L2 /\ simL R' PLC L2 L3.
Proof.
  intros. hnf in H. induction H. do 3 eexists nil; split; econstructor.
  edestruct IHAIR5 as [A [B []]]; dcr.
  inv pf.
  
Qed.
*)

(*

Lemma R_natural P (R R': P -> list val -> list val -> Prop) s s' E E' L1 L2 L3 PL PL' f'
: (forall L L', simL R PL L L' -> 
        sim (L, E, s) 
            (L', E', s'))
  -> simL R PL L1 L2
  -> simL R' PL' L2 L3
  -> implements R' f'
  -> sim (L1, E, s)
         (L3, E', natural f' (List.map Some PL') s').
Proof.
  intros. 
  simpl.
  refine (sim_trans (H _ _ _ ) _ ); try eassumption.
  eapply R_intro; eauto.
Qed.



Lemma sim_shift P (R R': P -> list val -> list val -> Prop) s s' E E' L1 p PL f
: implements R f
  -> (forall L L', simL R  PL L L' ->
       forall VL VL', R p VL VL' ->
        sim (L, E, s)
            (L', E', s'))
  -> sim (L1, E, natural f (List.map Some (p::PL)) s)
         (L1, E', s').
Proof.
  
Admitted.


Definition inv {P} (R: P -> list val -> list val -> Prop) p x y
 := R p y x.

Lemma simL_sym P (R: P -> list val -> list val -> Prop) PL L L'
 : simL R PL L L' -> simL (inv R) PL L' L.
Admitted.

(*
Lemma R_natural' P (R: P -> list val -> list val -> Prop) s s' E E' L PL f'
: (forall L L', simL R PL L L' -> 
        sim (L, E, s) 
            (L', E', s'))
  -> implements (inv R) f'
  -> @sim F.state _ F.state _ (L, E, s)
         (L, E', natural f' (List.map Some PL) s').
Proof.
  intros. 
  simpl.
  refine (sim_trans (H _ _ _ ) _); try eassumption.
  eapply R_intro; eauto. eapply simL_sym; eauto.
Qed.
*)

Lemma simL_extension' P (R: P -> list val -> list val -> Prop) (f: P -> list var -> list var) PL s s' E E' Z Z' L L' p
: simL R PL L L' 
  -> (forall L L', simL R PL L L' -> 
                   forall VL VL', R p VL VL'  
                                  -> sim (L, E[Z <-- VL], s) 
                                         (L', E'[Z' <-- VL'], s'))
  -> simL R (p::PL) (F.blockI E Z s :: L) (F.blockI E' Z' s' :: L').
Proof.
  intros.
  hnf; intros. econstructor; eauto. econstructor; eauto; intros.

  + refine (sim_trans (subst_lemma_R _ _ _  _ _ _ _ _ _ _ ) _); try eassumption.
    instantiate (1:=f). admit.
    eapply sim_sym.
    eapply R_natural.
    intros. eapply sim_sym. eapply H0; eauto.
    eapply simL_sym; eauto.
    instantiate (1:=(F.blockI E Z s::L)).
    econstructor. econstructor.
    instantiate (1:= inv R). admit. 
    
    
    
    
    Focus 3.
    instantiate (3:=E'). instantiate (2:=s'). instantiate (1:=L').
    refine (sim_trans (H0 _ _ _ _ _ _) (sim_refl _)); try eassumption.
    
Admitted.


Fixpoint compile (s:stmt) (a:ann live) :=
  match s, a with
    | stmtExp x e s, annExp lv an => 
      if [x ∈ getAnn an] then stmtExp x e (compile s an)
                         else compile s an
    | stmtIf x s t, annIf _ ans ant => stmtIf x (compile s ans) (compile t ant)
    | stmtGoto f Y, annGoto lv => 
      stmtGoto f (List.filter (fun x => if [x ∈ lv] then true else false) Y)
    | stmtReturn x, annReturn _ => stmtReturn x
    | stmtLet Z s t, annLet lv ans ant => 
      stmtLet (List.filter (fun x => if [x ∈ getAnn ans] then true else false) Z) 
              (compile s ans) (compile t ant)
    | s, _ => s
  end.

Lemma sim_DCE L L' V V' s G lv
: agree_on (getAnn lv) V V'
-> true_live_sound G s lv
-> simL LiveRel G L L'
-> @sim F.state _ F.state _ (L,V, s) (L',V', compile s lv).
Proof.
    general induction s; simpl; inv H0; simpl in * |- *.
  + case_eq (exp_eval V e); intros. destruct if. 
    - eapply simS; try eapply plusO.
      econstructor; eauto.
      econstructor; eauto. instantiate (1:=v). admit.
      eapply IHs; eauto. eapply agree_on_update_same. 
      eapply agree_on_incl; eauto. 
    - eapply sim_expansion_closed.
    Focus 2. eapply S_star. econstructor; eauto. 
    eapply star_refl. Focus 2. eapply star_refl.
    eapply IHs; eauto. eapply agree_on_update_dead; eauto.
    eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition. 
    - admit.
  + admit.
  + (* destruct (get_dec L (counted l)). destruct s as [[]].
    destruct_prop (length block_Z = length Y). 
    unfold simL in H1.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR4_nth as [?[?]]; try eassumption; dcr. 
    simpl in *. repeat get_functional; subst.
    inv H14. eapply simS; try eapply plusO.
    econstructor; eauto. simpl. rewrite lookup_list_length. congruence.
    econstructor; eauto. simpl. congruence.
    simpl. unfold updE. assert (lookup_list V (lookup_list ϱ Y) = lookup_list V' Y).
    rewrite <- comp_lookup_list. 
    admit.
    rewrite H5. eapply H19.
    eapply simE; try eapply star_refl; eauto; stuck.
    get_functional; subst. eapply n. simpl in *. rewrite len.
    rewrite lookup_list_length; eauto.
    edestruct AIR4_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR4_nth as [?[?]]; try eassumption; dcr. 
    simpl in *. repeat get_functional; subst.
    inv H14; simpl in *. eapply n. congruence.
    eapply simE; try eapply star_refl; eauto; stuck; eauto.
    edestruct AIR4_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption. eauto. *)
(*
    admit.
  + eapply simE; try eapply star_refl.
    simpl. rewrite H; eauto. simpl. 
    stuck. stuck.
  + econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    simpl. eapply IHs2; eauto. 
    simpl in *; eapply agree_on_incl; eauto.
    eapply simL_extension; eauto. intros.
    eapply IHs1; eauto.
    admit. admit.
Qed.



Fixpoint compile_spill (spill:list var) (cont:stmt) :=
  match spill with
  | nil => cont
  | x::spill => stmtExp x (Var x) (compile_spill spill cont)
  end.

Fixpoint compile_reload (reload:list var) (cont:stmt) :=
  match spill with
  | nil => cont
  | x::spill => stmtExp x (Var x) (compile_spill spill cont)
  end.


Fixpoint compile (s:stmt) (an:ann (list var*list var)) : stmt :=
  match s, an with
    | stmtExp x e s, annExp (spill,reload) an => 
      compile_spill spill (compile_reload reload (stmtExp x e (compile s an)))
    | stmtIf x s t, annIf (spill,reload) ans ant => 
      compile_spill spill (compile_reload reload (stmtIf x (compile s ans) (compile t ant)))
    | stmtGoto f Y, annGoto (spill,reload) => 
      compile_spill spill (compile_reload reload (stmtGoto f (Y++Za)))
    | stmtReturn x, annReturn (spill,reload) => 
      compile_spill spill (compile_reload reload (stmtReturn x))
    | stmtLet Z s t, annLet (spill, reload) ans ant =>
      compile_spill spill (compile_reload reload (stmtLet (Z++Za) (compile s ans) (compile t ant)))
    | s, _ => s
  end.

Lemma subst_alpha ϱ ϱ' s
: inverse_on (freeVars s) ϱ ϱ'
  -> alpha ϱ ϱ' s (substVars ϱ s).
Proof.
  general induction s; simpl in * |- *.
  econstructor. admit.
  eapply IHs. 
  econstructor. eauto. admit.
  eauto. eauto.
  econstructor. eauto. admit.
  econstructor. eauto. admit.
  econstructor. eauto. eapply IHs1.
  eapply IHs2.
Qed.

Fixpoint substVars (ϱ:var -> var) (s:stmt) : stmt :=
  match s with
   | stmtExp x e s => stmtExp x e (substVars (ϱ[x <- x]) s)
   | stmtIf x s1 s2 => stmtIf (ϱ x) (substVars ϱ s1) (substVars ϱ s2)
   | stmtGoto l Y => stmtGoto l (lookup_list ϱ Y)
   | stmtReturn x => stmtReturn (ϱ x)
   | stmtLet Z s1 s2 => stmtLet Z (substVars (ϱ[Z <-- Z]) s1) (substVars ϱ s2)
   end.

Lemma sim_eta L L' V V' s ϱ
: (forall x, V' x = V (ϱ x))
-> simL L L'
-> @sim F.state _ F.state _ (L,V,substVars ϱ s) (L',V',s).
Proof.
Admitted.
*)
(*
  revert_all. cofix; intros.
  destruct s; simpl.
  case_eq (exp_eval V e); intros.
  eapply simS; try eapply plusO.
  econstructor. eauto. 
  econstructor. instantiate (1:=v). admit.
  eapply sim_eta. admit.
  admit.
  case_eq (val2bool (V' x)); intros.
  econstructor; try eapply plusO.
  econstructor. rewrite <- H; eauto.
  econstructor; eauto. admit.
  econstructor; try eapply plusO.
  eapply F.stepIfF. rewrite <- H. eauto.
  eapply F.stepIfF. eauto.
  admit.
  admit.
  admit.
  econstructor; try eapply plusO.
  econstructor. 
  econstructor.
Admitted.
*)
(*
Lemma sim_spill L V V' ϱ (x y:var) s s'
: s = substVars (ϱ[y <-ϱ x]) s'
  -> (forall x, V' x = V (ϱ x))
  -> @sim F.state _ F.state _ (L,V,s) (L,V',(stmtExp y (Var x) s')).
Proof.
  intros. 
  eapply sim_expansion_closed. 
  Focus 2. eapply star_refl.
  Focus 2. eapply S_star. econstructor. simpl. reflexivity. eapply star_refl.
  rewrite H.
  eapply sim_eta. 
  intros. lud. 
  rewrite H0; eauto.
  rewrite <- H0; eauto. eapply simLeq_refl.
Qed.
*)
Unset Printing Records. 


(*
Inductive simL : F.labenv -> F.labenv -> Prop :=
  | simLnil : simL nil nil
  | simLcons L L' E E' Z Z' s s'
    : (forall VL, 
         sim (F.blockI E Z s::L, E[Z <-- VL], s) 
             (F.blockI E' Z' s'::L', E'[Z' <-- VL], s'))
      -> length Z = length Z'
      -> simL L L'
      -> simL (F.blockI E Z s::L) (F.blockI E' Z' s'::L').

Lemma simL_refl L : simL L L.
Proof.
  induction L; eauto using simL.
  destruct a. econstructor; intros; eauto. eapply sim_refl.
Qed.

Lemma simL_get L L' n blk blk'
: simL L L'
  -> get L n blk
  -> get L' n blk'
  -> (forall VL, 
         sim (L, F.block_E blk[block_Z blk <-- VL], block_s blk) 
             (L', F.block_E blk'[block_Z blk' <-- VL], block_s blk')) 
     /\ length (block_Z blk) = length (block_Z blk').
Proof.
  intros. general induction H0. inv H1; inv H.
  simpl. split; eauto. 
Qed.
*)    



(*
Lemma subst_lemma_sim L' s s' V E E' Z Z' L1 L2 t
: simLeq L1 L2
  -> (forall VL L L', simLeq L L' -> 
        diverges F.step (L, E[Z <-- VL], s) 
         -> diverges F.step (L', E'[Z' <-- VL], s'))
  -> length Z = length Z'
  -> length L1 = length L2
  -> sim ((L' ++ F.blockI E Z s :: L1)%list, V, t)
         ((L' ++ F.blockI E' Z' s' :: L2)%list, V, t).
Proof.
  revert_all; cofix; intros.
  destruct t.
  + exfalso; clear_all; admit.
  + exfalso; clear_all; admit.
  + destruct (get_subst _ _ _ Ldef) as [|[]].
    - econstructor. econstructor. eapply len. eapply get_app; eauto. reflexivity.
      pose proof (get_range H6). rewrite drop_length; eauto.
      rewrite drop_length in H5. eapply subst_lemma_div; eauto. eauto.
    - destruct H6; dcr; subst; simpl in *. 
      econstructor. constructor. instantiate (1:= F.blockI E' Z' s').
      simpl. eauto. congruence. simpl. rewrite H8. eapply get_length_app.
      reflexivity. simpl. rewrite H8. rewrite drop_length_eq.
      eapply (subst_lemma_div nil); eauto. simpl.
      rewrite H8 in H5. rewrite drop_length_eq in H5.
      unfold updE. eapply H0. Focus 2. unfold updE in H5. eapply H5.
      eapply simLeq_refl. 
      edestruct get_length_eq; try eassumption.
      econstructor. econstructor. Focus 2. 
      rewrite cons_app. rewrite app_assoc.
      eapply get_app_right; eauto. simpl.
      repeat rewrite app_length; simpl. omega.
      Focus 2. 
      reflexivity. Focus 2. simpl. rewrite drop_length_gr; eauto.
      pose proof (H _ _ _ H7 H6).
      unfold updE. unfold updE in H5.
      rewrite drop_length_gr in H5.
      refine (sim_codiverge (H9 _) H5). eassumption. 
      exfalso; clear_all; admit.
  + exfalso; clear_all; admit.
  + econstructor. econstructor.
    rewrite cons_app. rewrite app_assoc.
    eapply (subst_lemma_div (F.blockI V Z0 s0::nil ++ L')%list); eauto.
Qed.

  + eapply simS; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    eapply (subst_lemma_sim (F.blockI V Z0 t1::L')); eauto.
Qed.
*)
*)

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
