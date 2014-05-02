Require Import DecSolve IL Annotation Liveness LengthEq.

Definition live_sound_dec Lv s slv (an:annotation s slv)
      : Computable (live_sound Lv s slv).
Proof. 
  general induction s; destruct slv; try isabsurd.
  + edestruct IHs; eauto; try inv an; eauto;
    decide (getAnn slv\{{x}} ⊆ a);
    decide (live_exp_sound e a); try dec_solve.
  + edestruct IHs1; try inv an; eauto;
    edestruct IHs2; try inv an; eauto;
    decide (x ∈ a); 
    decide (getAnn slv1 ⊆ a); 
    decide (getAnn slv2 ⊆ a);
    try dec_solve; try eassumption; try inv an; eauto.
  + destruct (get_dec Lv (counted l)) as [[[blv Z] ?]|?];
    try decide ((blv \ of_list Z) ⊆ a);
    decide (of_list Y ⊆ a);
    try decide (length Y = length Z); try dec_solve.
  +  decide(x ∈ a); try dec_solve.
  + edestruct IHs1; eauto; try inv an; eauto;
    edestruct IHs2; eauto; try inv an; eauto;
    decide ((of_list Z) ⊆ getAnn slv1); 
    decide ((getAnn slv1 \ of_list Z) ⊆ a);
    decide (getAnn slv2 ⊆ a); try dec_solve.
    Grab Existential Variables. eassumption. eassumption.
Defined.


Instance live_sound_dec_inst Lv s slv `{Computable(annotation s slv)}
: Computable (live_sound Lv s slv).
Proof.
  edestruct H.
  eapply live_sound_dec; eauto.
  right; intro. eauto using live_sound_annotation.
Defined.

Definition true_live_sound_dec Lv s slv (an:annotation s slv)
      : Computable (true_live_sound Lv s slv).
Proof. 
  general induction s; destruct slv; try isabsurd.
  + edestruct IHs; eauto; try inv an; eauto;
    decide (getAnn slv\{{x}} ⊆ a);
    decide (x ∈ getAnn slv -> live_exp_sound e a); 
(*    decide (x ∉ getAnn slv -> a ⊆ getAnn slv\{{x}});*) try dec_solve. 
  + edestruct IHs1; try inv an; eauto;
    edestruct IHs2; try inv an; eauto;
    decide (x ∈ a); 
    decide (getAnn slv1 ⊆ a); 
    decide (getAnn slv2 ⊆ a);
    try dec_solve; try eassumption; try inv an; eauto.
  + destruct (get_dec Lv (counted l)) as [[[blv Z] ?]|?];
    try decide ((blv \ of_list Z) ⊆ a);
    try decide (argsLive a blv Y Z); try dec_solve.
    left. econstructor; eauto using argsLive_length.
  + decide(x ∈ a); try dec_solve.
  + edestruct IHs1; eauto; try inv an; eauto;
    edestruct IHs2; eauto; try inv an; eauto;
    decide ((getAnn slv1 \ of_list Z) ⊆ a);
    decide (getAnn slv2 ⊆ a); try dec_solve.
    Grab Existential Variables. eassumption. eassumption.
Defined.

Instance true_live_sound_dec_inst Lv s slv `{Computable(annotation s slv)}
: Computable (true_live_sound Lv s slv).
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
