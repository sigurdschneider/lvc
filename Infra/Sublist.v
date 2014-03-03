Require Import Plus List Get.
(* Inductive definition of a SubLists relation with explicit position *)

Inductive subList {X : Type} (L : list X) : list X -> nat -> Prop := 
| SubListNil n : subList L nil n 
| SubListCons l L' n : get L n l -> subList L L' (S n) -> subList L (l::L') n.
 
Lemma subList_app_r {X:Type} (P:list X) P1 P2 n:
subList P (P1++P2) n -> subList P P2 (n+length P1).
intros. remember (P1 ++ P2). revert P1 P2 Heql. induction H; intros.
 pose proof (app_eq_nil _ _ (eq_sym Heql)). destruct H. subst. constructor.
 destruct P1. simpl in *. subst. rewrite plus_0_r. constructor; auto.
 simpl in *. rewrite <- plus_Snm_nSm. simpl. eapply IHsubList. congruence.
Qed.
    
Lemma subList_app_l {X:Type} (P:list X) P1 P2 n:
subList P (P1++P2) n -> subList P P1 n.
revert n. induction P1; intros.
  constructor.
  inv H. constructor; auto.
Qed.

Lemma subList_refl' {X:Type} (L1 L2: list X):
subList (L1++L2) L2 (length L1). 
Proof.
 revert L1. induction L2; intros; simpl.
  constructor. 
  pose proof (IHL2 (L1++a:: nil)). 
  rewrite <- app_assoc in H. rewrite app_length in H. 
  rewrite plus_comm in H.  simpl in *.
 constructor; auto. rewrite <- (plus_0_r (length L1)). 
 apply get_shift. constructor.
Qed.

Lemma subList_refl {X:Type} (L: list X) :
subList L L 0.
pose proof (subList_refl' nil L).
simpl in *. auto.
Qed.

(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lyn")) ***
*** End: ***
*)
