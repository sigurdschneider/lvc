Require Import DecSolve IL Annotation Liveness TrueLiveness LengthEq.

Instance argsLive_dec Caller Callee Y Z
      : Computable (argsLive Caller Callee Y Z).
Proof.
  decide(length Y = length Z).
  - general induction Y; destruct Z; isabsurd.
    + left; econstructor.
    + decide (v ∈ Callee -> live_exp_sound a Caller);
      edestruct (IHY Caller Callee); try dec_solve; try eassumption;
      try inv an; eauto; try tauto.
  - right; intro. eapply argsLive_length in H. congruence.
Defined.

Definition live_sound_dec i Lv s slv (an:annotation s slv)
      : Computable (live_sound i Lv s slv).
Proof.
  revert i Lv slv an.
  sind s; intros; destruct s; destruct slv; try isabsurd.
  + edestruct (IH s); eauto; try inv an; eauto;
    decide (getAnn slv\{{x}} ⊆ a);
    decide (live_exp_sound e a);
    decide (x ∈ getAnn slv);
    try dec_solve.
  + edestruct (IH s1); try inv an; eauto;
    edestruct (IH s2); try inv an; eauto;
    decide (live_exp_sound e a);
    decide (getAnn slv1 ⊆ a);
    decide (getAnn slv2 ⊆ a);
    try dec_solve; try eassumption; try inv an; eauto.
  + destruct (get_dec Lv (counted l)) as [[[blv Z] ?]|?];
    (try (decide (isImperative i); [decide ((blv \ of_list Z) ⊆ a)|]));
    try decide (forall n y, get Y n y -> live_exp_sound y a);
    try decide (length Y = length Z); try dec_solve.
    - left; econstructor; eauto. destruct if; eauto.
    - right; intro. inv H; eauto. destruct if in H5; eauto.
      get_functional; subst. eauto.
    - left; econstructor; eauto. destruct if; eauto. intuition.
  + decide(live_exp_sound e a); try dec_solve.
  + edestruct (IH s); eauto; try inv an; eauto;
    decide (getAnn slv \ {{x}} ⊆ a);
    decide (x ∈ getAnn slv);
    try decide (forall n y, get Y n y -> live_exp_sound y a);
    try dec_solve.
  + edestruct (IH s0); eauto; try inv an; eauto; try dec_solve.
    decide (length s = length sa); try dec_solve;
    decide (getAnn slv ⊆ a); try dec_solve.
    exploit (@indexwise_R_dec' _ _
                               (fun Zs a0 => live_sound i (live_globals s sa ++ Lv) (snd Zs) a0) s sa).
    intros. eapply IH; eauto. inv an; eauto. destruct X; try dec_solve.
    exploit (@indexwise_R_dec' _ _
                               (fun Zs a0 =>  of_list (fst Zs)[<=]getAnn a0 /\
                                             (if isFunctional i then
                                                getAnn a0 \ of_list (fst Zs)[<=]a
                                              else True)) s sa).
    intros. decide (of_list (fst a0)[<=]getAnn b); try dec_solve.
    destruct if; try dec_solve. decide ( getAnn b \ of_list (fst a0)[<=]a); try dec_solve.
    destruct X; try dec_solve.
    Grab Existential Variables. eassumption. eassumption.
Defined.

Instance live_sound_dec_inst i Lv s slv `{Computable(annotation s slv)}
: Computable (live_sound i Lv s slv).
Proof.
  edestruct H.
  eapply live_sound_dec; eauto.
  right; intro. eauto using live_sound_annotation.
Defined.

Definition true_live_sound_dec i Lv s slv (an:annotation s slv)
      : Computable (true_live_sound i Lv s slv).
Proof.
  revert i Lv slv an.
  sind s; intros; destruct s; destruct slv; try isabsurd.
  + edestruct (IH s); eauto; try inv an; eauto;
    decide (getAnn slv\{{x}} ⊆ a);
    decide (x ∈ getAnn slv -> live_exp_sound e a);
    decide (x ∉ getAnn slv -> a ⊆ getAnn slv\{{x}});
    try dec_solve.
  + edestruct (IH s1); try inv an; eauto;
    edestruct (IH s2); try inv an; eauto;
    decide (exp2bool e = None -> live_exp_sound e a);
    decide (exp2bool e <> Some false -> getAnn slv1 ⊆ a);
    decide (exp2bool e <> Some true -> getAnn slv2 ⊆ a);
    try dec_solve; try eassumption; try inv an; eauto.
  + destruct (get_dec Lv (counted l)) as [[[blv Z] ?]|?];
    try decide (argsLive a blv Y Z); try dec_solve.
    exploit argsLive_length; eauto.
    decide (isImperative i); try dec_solve.
    decide ((blv \ of_list Z) ⊆ a).
    - left; econstructor; eauto. destruct if; eauto.
    - right; intro. inv H; eauto. destruct if in H5; eauto.
      get_functional; subst; eauto.
    - left; econstructor; eauto. destruct if; eauto. intuition.
  + decide(live_exp_sound e a); try dec_solve.
  + edestruct (IH s); eauto; try inv an; eauto;
    decide (getAnn slv \ {{x}} ⊆ a);
    try decide (forall n y, get Y n y -> live_exp_sound y a);
    try dec_solve.
  + edestruct (IH s0); eauto; try inv an; eauto; try dec_solve.
    decide (length s = length sa); try dec_solve;
    decide (getAnn slv ⊆ a); try dec_solve.
    exploit (@indexwise_R_dec' _ _
                               (fun Zs a0 =>
                                  true_live_sound i (live_globals s sa ++ Lv) (snd Zs) a0) s sa).
    intros. eapply IH; eauto. inv an; eauto. destruct X; try dec_solve.
    exploit (@indexwise_R_dec' _ _
                               (fun Zs a0 => if isFunctional i then
                                                getAnn a0 \ of_list (fst Zs)[<=]a
                                              else True) s sa).
    intros.
    destruct if; try dec_solve.
    decide ( getAnn b \ of_list (fst a0)[<=]a); try dec_solve. left; eauto. right; eauto.
    destruct X; try dec_solve.
    Grab Existential Variables. eassumption. eassumption.
Defined.

Instance true_live_sound_dec_inst i Lv s slv `{Computable(annotation s slv)}
: Computable (true_live_sound i Lv s slv).
Proof.
  edestruct H.
  eapply true_live_sound_dec; eauto.
  right; intro. eauto using true_live_sound_annotation.
Defined.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
