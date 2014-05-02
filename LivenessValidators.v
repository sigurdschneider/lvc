Require Import DecSolve IL Annotation Liveness LengthEq.

Definition live_sound_dec Lv s slv (an:annotation s slv)
      : Computable (live_sound Lv s slv).
Proof. 
  constructor.
  general induction s; destruct slv; try isabsurd.
  + edestruct IHs; eauto; try inv an; eauto;
    destruct_prop (getAnn slv\{{x}} ⊆ a);
    destruct_prop (live_exp_sound e a); try dec_solve.
  + edestruct IHs1; try inv an; eauto;
    edestruct IHs2; try inv an; eauto;
    destruct_prop (x ∈ a); 
    destruct_prop (getAnn slv1 ⊆ a); 
    destruct_prop (getAnn slv2 ⊆ a);
    try dec_solve; try eassumption; try inv an; eauto.
  + destruct (get_dec Lv (counted l)) as [[[blv Z] ?]|?];
    try destruct_prop ((blv \ of_list Z) ⊆ a);
    destruct_prop (of_list Y ⊆ a);
    try destruct_prop (length Y = length Z); try dec_solve.
  +  destruct_prop(x ∈ a); try dec_solve.
  + edestruct IHs1; eauto; try inv an; eauto;
    edestruct IHs2; eauto; try inv an; eauto;
    destruct_prop ((of_list Z) ⊆ getAnn slv1); 
    destruct_prop ((getAnn slv1 \ of_list Z) ⊆ a);
    destruct_prop (getAnn slv2 ⊆ a); try dec_solve.
    Grab Existential Variables. eassumption. eassumption.
Defined.


Instance live_sound_dec_inst Lv s slv `{Computable(annotation s slv)}
: Computable (live_sound Lv s slv).
Proof.
  destruct H as [[]].
  eapply live_sound_dec; eauto.
  constructor. right; intro. eauto using live_sound_annotation.
Defined.

Definition true_live_sound_dec Lv s slv (an:annotation s slv)
      : Computable (true_live_sound Lv s slv).
Proof. 
  constructor.
  general induction s; destruct slv; try isabsurd.
  + edestruct IHs; eauto; try inv an; eauto;
    destruct_prop (getAnn slv\{{x}} ⊆ a);
    destruct_prop (x ∈ getAnn slv -> live_exp_sound e a); 
(*    destruct_prop (x ∉ getAnn slv -> a ⊆ getAnn slv\{{x}});*) try dec_solve. 
  + edestruct IHs1; try inv an; eauto;
    edestruct IHs2; try inv an; eauto;
    destruct_prop (x ∈ a); 
    destruct_prop (getAnn slv1 ⊆ a); 
    destruct_prop (getAnn slv2 ⊆ a);
    try dec_solve; try eassumption; try inv an; eauto.
  + destruct (get_dec Lv (counted l)) as [[[blv Z] ?]|?];
    try destruct_prop ((blv \ of_list Z) ⊆ a);
    try destruct_prop (argsLive a blv Y Z); try dec_solve.
    left. econstructor; eauto using argsLive_length.
  + destruct_prop(x ∈ a); try dec_solve.
  + edestruct IHs1; eauto; try inv an; eauto;
    edestruct IHs2; eauto; try inv an; eauto;
    destruct_prop ((getAnn slv1 \ of_list Z) ⊆ a);
    destruct_prop (getAnn slv2 ⊆ a); try dec_solve.
    Grab Existential Variables. eassumption. eassumption.
Defined.

Instance true_live_sound_dec_inst Lv s slv `{Computable(annotation s slv)}
: Computable (true_live_sound Lv s slv).
Proof.
  destruct H as [[]].
  eapply true_live_sound_dec; eauto.
  constructor. right; intro. eauto using true_live_sound_annotation.
Defined.

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
