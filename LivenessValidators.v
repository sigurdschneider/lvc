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

Local Hint Extern 1 =>
match goal with
  [ H : annotation _ _ |- annotation _ _ ] => inv H; eassumption
end.

Definition live_sound_dec i ZL Lv s slv
      : Computable (live_sound i ZL Lv s slv).
Proof.
  revert i ZL Lv slv.
  sind s; intros; destruct s; destruct slv;
    try solve [dec_right].
  - edestruct (IH s); eauto; [| dec_right ];
    ensure (getAnn slv\{{x}} ⊆ a);
    ensure (live_exp_sound e a);
    ensure (x ∈ getAnn slv); dec_solve.
  - edestruct (IH s1); eauto; [| dec_right ];
    edestruct (IH s2); eauto; [| dec_right ];
    ensure (live_exp_sound e a);
    ensure (getAnn slv1 ⊆ a);
    ensure (getAnn slv2 ⊆ a); dec_solve.
  - destruct (get_dec Lv (counted l)) as [[blv ?]|?]; [| dec_right];
      destruct (get_dec ZL (counted l)) as [[Z ?]|?]; [| dec_right];
    decide (isImperative i); [ensure ((blv \ of_list Z) ⊆ a); [|cases in H6; eauto]|];
    ensure (forall n y, get Y n y -> live_exp_sound y a);
      ensure (length Y = length Z);
    left; econstructor; eauto; cases; eauto.
  - decide(live_exp_sound e a); try dec_solve.
  - edestruct (IH s); eauto; [| dec_right];
      ensure (getAnn slv \ {{x}} ⊆ a);
      ensure (x ∈ getAnn slv);
      ensure (forall n y, get Y n y -> live_exp_sound y a);
      dec_solve.
  - edestruct (IH s0); eauto; [| dec_solve];
      ensure (length s = length sa);
      ensure (getAnn slv ⊆ a).
    exploit (@indexwise_R_dec' _ _
                               (fun Zs a0 => live_sound i (fst ⊝ s ++ ZL)
                                                     (getAnn ⊝ sa ++ Lv)
                                                     (snd Zs) a0) s sa).
    intros. eapply IH; eauto.
    destruct H; [| dec_solve].
    exploit (@indexwise_R_dec' _ _
                               (fun Zs a0 =>  of_list (fst Zs)[<=]getAnn a0 /\
                                             (if isFunctional i then
                                                getAnn a0 \ of_list (fst Zs)[<=]a
                                              else True)) s sa).
    + intros. ensure (of_list (fst a0)[<=]getAnn b).
      cases; [| dec_solve].
      ensure ( getAnn b \ of_list (fst a0)[<=]a); dec_solve.
    + destruct H; dec_solve.
Defined.

Hint Extern 5 =>
match goal with
| [ H : ?A = ⎣ true ⎦, H' : ?A = ⎣ false ⎦ |- _ ] => exfalso; congruence
| [ H : ?A = None , H' : ?A = Some _ |- _ ] => exfalso; congruence
| [ H : ?A <> ⎣ true ⎦ , H' : ?A <> ⎣ false ⎦ |- ?A = None ] =>
  case_eq (A); [intros [] ?| intros ?]; congruence
| [ H : ?A = ?B, H' : ?A <> ?B |- _ ] => exfalso; congruence
end.

Definition true_live_sound_dec i ZL Lv s slv
      : Computable (true_live_sound i ZL Lv s slv).
Proof.
  revert i ZL Lv slv.
  sind s; intros; destruct s; destruct slv;
    try solve [right; intro A; inversion A].
  - edestruct (IH s); eauto; [| dec_right ];
      ensure (getAnn slv \ singleton x ⊆ a);
      ensure (x ∈ getAnn slv -> live_exp_sound e a); dec_solve.
  - ensure (exp2bool e = None -> live_exp_sound e a);
      ensure (exp2bool e <> Some false -> getAnn slv1 ⊆ a);
      ensure (exp2bool e <> Some true -> getAnn slv2 ⊆ a);
      case_eq (exp2bool e); [ intros [] EQ| intros EQ ].
    + edestruct (IH s1); eauto; [ dec_solve | dec_right].
    + edestruct (IH s2); eauto; [ dec_solve | dec_right].
    + edestruct (IH s1); eauto; [| dec_right];
        edestruct (IH s2); eauto; [ dec_solve | dec_right].
  - destruct (get_dec ZL (counted l)) as [[Z ?]|?]; [| dec_right];
    destruct (get_dec Lv (counted l)) as [[blv ?]|?]; [| dec_right];
    ensure (argsLive a blv Y Z).
    exploit argsLive_length; eauto.
    decide (isImperative i); try dec_solve.
    + decide ((blv \ of_list Z) ⊆ a).
      * left; econstructor; eauto. cases; eauto.
      * dec_right. cases in H7. eauto.
    + left; econstructor; eauto. cases; eauto.
  - ensure (live_exp_sound e a). dec_solve.
  - edestruct (IH s); eauto; [| dec_right];
      ensure (getAnn slv \ singleton x ⊆ a);
      ensure (forall n y, get Y n y -> live_exp_sound y a);
      dec_solve.
  - edestruct (IH s0); eauto; [| dec_right];
      ensure (length s = length sa);
      ensure (getAnn slv ⊆ a).
    exploit (@indexwise_R_dec' _ _
                               (fun Zs a0 =>
                                  true_live_sound i (fst ⊝ s ++ ZL)
                                                  (getAnn ⊝ sa ++ Lv)
                                                  (snd Zs) a0) s sa).
    intros. eapply IH; eauto. destruct H; [| dec_right].
    decide (isFunctional i); [| left; econstructor; try cases; eauto].
    exploit (@indexwise_R_dec' _ _
                               (fun Zs a0 => getAnn a0 \ of_list (fst Zs)[<=]a) s sa).
    + intros.
      decide ( getAnn b \ of_list (fst a0)[<=]a).
      left; eauto. right; eauto.
    + destruct H. left; econstructor; try cases; eauto.
      dec_right. cases in H9; eauto.
Defined.
