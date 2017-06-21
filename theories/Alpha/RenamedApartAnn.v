Require Import CSet Util Map.
Require Import Env IL Alpha StableFresh Annotation RenamedApart SetOperations.
Require Import LabelsDefined PairwiseDisjoint AppExpFree.
Require Import Infra.PartialOrder CSetPartialOrder AnnotationLattice.

Require Import RenamedApart.

Set Implicit Arguments.

Definition renamedApartAnnF (renamedApartAnn:stmt -> set var -> ann (set var * set var)) G
           := fold_left (fun anFG (Zs:params*stmt) =>
                        let ans := renamedApartAnn (snd Zs) (G ∪ of_list (fst Zs)) in
                        (ans::fst anFG, snd anFG ∪ (of_list (fst Zs) ∪ snd (getAnn ans)))).

Fixpoint renamedApartAnn (s:stmt) (G:set var) : ann (set var * set var) :=
  match s with
    | stmtLet x e s =>
      let an := renamedApartAnn s {x; G} in
      ann1 (G, {x; snd (getAnn an) }) an
    | stmtIf e s t =>
      let ans := renamedApartAnn s G in
      let ant := renamedApartAnn t G in
      ann2 (G, snd (getAnn ans) ∪ snd (getAnn ant)) ans ant
    | stmtReturn e =>
      ann0 (G, ∅)
    | stmtApp f Y =>
      ann0 (G, ∅)
    | stmtFun F t =>
      let (ans, G') := renamedApartAnnF renamedApartAnn G F (nil, {}) in
      let ant := renamedApartAnn t G in
      annF (G, G' ∪ (snd (getAnn ant))) (rev ans) ant
  end.

Lemma fst_renamedApartAnn s G
 : fst (getAnn (renamedApartAnn s G)) = G.
Proof.
  sind s; destruct s; eauto.
  - simpl. let_pair_case_eq. simpl; eauto.
Qed.

Lemma snd_renamedApartAnnF' F L G G'
: (forall n Zs G',
     get F n Zs ->
     snd (getAnn (renamedApartAnn (snd Zs) G')) = definedVars (snd Zs))
  -> snd (renamedApartAnnF renamedApartAnn G F (L, G')) =
    fold_left union (defVarsZs definedVars ⊝ F) G'.
Proof.
  intros.
  general induction F; intros; simpl; eauto.
  - rewrite IHF; eauto using get.
    erewrite H; eauto using get.
Qed.

Lemma snd_renamedApartAnnF_nil' G F
: (forall n Zs, get F n Zs -> forall G, snd (getAnn (renamedApartAnn (snd Zs) G)) = definedVars (snd Zs))
  -> snd (renamedApartAnnF renamedApartAnn G F (nil, {})) = definedVarsF definedVars F.
Proof.
  intros. rewrite snd_renamedApartAnnF'; eauto.
Qed.

Lemma get_fst_renamedApartAnnF' G F n ans L G'
:  get (fst (renamedApartAnnF renamedApartAnn G F (L, G'))) n ans
   -> (get L (n - ❬F❭) ans /\ n >= ❬F❭ ) \/
     (n < ❬F❭ /\ exists Zs, get F (❬F❭ - S n) Zs
                      /\ ans = renamedApartAnn (snd Zs) (G ∪ of_list (fst Zs))).
Proof.
  general induction F; simpl in * |- *;[ isabsurd |].
  - left. split; eauto. orewrite (n - 0 = n). eauto. omega.
  - eapply IHF in H as [[? ?]|[? [? [? ?]]]]; simpl in *.
    + inv H; eauto using get.
      * right.
        assert (n = ❬F❭) by omega; subst.
        rewrite <- H4 in *.
        split; eauto. eauto using get.
      * left. orewrite (n - S ❬F❭ = n0). split; eauto. omega.
    + subst. right. split. omega.
      eexists x; split; eauto using get.
      orewrite (❬F❭ - n = S (❬F❭ - S n)). econstructor; eauto.
Qed.

Lemma get_fst_renamedApartAnnF G F n ans G'
:  get (fst (renamedApartAnnF renamedApartAnn G F (nil, G'))) n ans
   -> exists Zs, get F (❬F❭ - S n) Zs
           /\ ans = renamedApartAnn (snd Zs) (G ∪ of_list (fst Zs)).
Proof.
  intros. eapply get_fst_renamedApartAnnF' in H; destruct H; isabsurd.
  dcr; eauto.
Qed.

Lemma length_fst_renamedApartAnnF' G G' F L
: length (fst (renamedApartAnnF renamedApartAnn G F (L, G')))
  = ❬L❭ + length F.
Proof.
  general induction F; simpl; eauto.
  rewrite IHF; eauto; simpl. omega.
Qed.

Lemma length_fst_renamedApartAnnF G G' F
: length (fst (renamedApartAnnF renamedApartAnn G F (nil, G'))) = length F.
Proof.
  rewrite length_fst_renamedApartAnnF'. reflexivity.
Qed.

Smpl Add
      match goal with
      | [ H :  get (fst (renamedApartAnnF renamedApartAnn ?G (rev ?F) (nil, {})))
                   (❬fst (renamedApartAnnF renamedApartAnn ?G (rev ?F) (nil, {}))❭ - S ?n) ?b |- _ ] =>
        let GET := fresh "Get" in
        eapply get_fst_renamedApartAnnF in H as [? [GET ?]]; subst;
          rewrite length_fst_renamedApartAnnF in GET;
          eapply get_rev in GET;
          rewrite rev_length in GET
      | [ H :  get (fst (renamedApartAnnF renamedApartAnn ?G ?F (nil, {})))
                   (❬fst (renamedApartAnnF renamedApartAnn ?G ?F (nil, {}))❭ - S ?n) ?b |- _ ] =>
        let GET := fresh "Get" in
        eapply get_fst_renamedApartAnnF in H as [? [GET ?]]; subst;
          rewrite length_fst_renamedApartAnnF in GET
      end : inv_get.

Lemma get_index_rev k n
  : k - S (k - S (k - S n)) = k - S n.
  omega.
Qed.

Smpl Add
     match goal with
       [ H : get _ (?k - S (?k - S (?k - S ?n))) _ |- _ ] =>
       rewrite (get_index_rev k n) in H
     end : inv_get.

Lemma snd_renamedApartAnn s G
: snd (getAnn (renamedApartAnn s G)) = definedVars s.
Proof.
  revert G.
  induction s using stmt_ind'; simpl; intros; repeat let_pair_case_eq; simpl; eauto; subst.
  - rewrite (IHs); eauto.
  - rewrite (IHs1); eauto. rewrite (IHs2); eauto.
  - rewrite (IHs); eauto.
    rewrite snd_renamedApartAnnF_nil'; eauto.
Qed.

Lemma snd_renamedApartAnnF F L G G'
  : snd (renamedApartAnnF renamedApartAnn G F (L, G')) =
    fold_left union (defVarsZs definedVars ⊝ F) G'.
Proof.
  eapply snd_renamedApartAnnF'; eauto using snd_renamedApartAnn.
Qed.


Lemma renamedApartAnn_decomp s G
: pe (getAnn (renamedApartAnn s G)) (G, snd (getAnn (renamedApartAnn s G))).
Proof.
  destruct s; simpl; try reflexivity.
  - let_pair_case_eq; simpl_pair_eqs; subst; simpl; eauto.
Qed.


Ltac renamedApart_len_simpl :=
  match goal with
  | [ H : context [ fst (renamedApartAnnF _ ?G ?F (nil, ?G'))] |- _ ] =>
    rewrite (length_fst_renamedApartAnnF G G' F) in H
  | [ |- context [ fst (renamedApartAnnF _ ?G ?F (nil, ?G'))] ] =>
    rewrite (length_fst_renamedApartAnnF G G' F)
  end.

Smpl Add renamedApart_len_simpl : len.

Lemma add_minus_eq X `{OrderedType X} G1 G2 x G'
  :  G1 [=] G2 \ G' -> x ∉ G' -> {x; G1} [=] {x; G2} \ G'.
Proof.
  intros. rewrite H0; clear H0. cset_tac.
Qed.

Hint Resolve add_minus_eq : cset.

(*
Local Hint Extern 10 =>
match goal with
| [ |- context [ snd (getAnn (renamedApartAnn ?s ?G))] ] => setoid_rewrite snd_renamedApartAnn
| [ |- context [ snd (renamedApartAnnF renamedApartAnn ?G (nil, _) ?s) ] ]
  => setoid_rewrite snd_renamedApartAnnF
end : ann.

Lemma ann_R_pe_notOccur G1 G2 G' s
:  disj (occurVars s) G'
   -> G1 [=] G2 \ G'
   -> ann_R (@pe var _)
           (renamedApartAnn s G1)
           (mapAnn (pminus G') (renamedApartAnn s G2)).
Proof.
  revert G1 G2 G'.
  sind s; destruct s; intros; simpl in * |- *; eauto using pe, ann_R with cset;
  try now (econstructor; reflexivity).
  - econstructor; eauto 20 with pe ann cset.
  - econstructor; eauto with cset pe ann.
  - econstructor; eauto with cset pe ann.
  - econstructor; eauto with cset pe ann.
  - intros.
    repeat let_pair_case_eq; subst; simpl.
    econstructor; eauto 20 with cset pe ann.
    + rewrite List.map_length; eauto.
      repeat rewrite length_fst_renamedApartAnnF; eauto.
    + intros.
      inv_map H2.
      edestruct get_fst_renamedApartAnnF as [? [? ?]]; dcr; eauto. subst.
      edestruct get_fst_renamedApartAnnF as [? [? ?]]; dcr; try eapply H1; eauto. subst.
      get_functional; subst.
      eapply IH; eauto.
      * eapply disj_1_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union; eauto using map_get_1 with cset.
      * repeat rewrite minus_dist_union.
        rewrite H0.
        eapply union_eq_decomp; eauto.
        eapply disj_eq_minus; eauto.
        eapply disj_1_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1; eauto.
        eapply incl_right.
Qed.
 *)


Lemma fst_renamedApartAnnF_swap G G' F L
  : fst (renamedApartAnnF renamedApartAnn G F (L, G'))
    = fst (renamedApartAnnF renamedApartAnn G F (nil, G')) ++ L.
Proof.
  general induction F; simpl; eauto.
  setoid_rewrite IHF at 1.
  setoid_rewrite IHF at 2.
  rewrite <- !app_assoc.
  rewrite <- cons_app. reflexivity.
Qed.

Lemma fst_renamedApartAnnF_eq G G1 G2 F L
  : fst (renamedApartAnnF renamedApartAnn G F (L, G1))
    = fst (renamedApartAnnF renamedApartAnn G F (L, G2)).
Proof.
  general induction F; simpl; eauto.
Qed.

Ltac renamedApartAnnF_swap_normal :=
  repeat match goal with
           [ |- context [ renamedApartAnnF ?f ?G ?F (?L, ?G') ] ] =>
           match L with
           | nil => fail 1
           | _ => rewrite (@fst_renamedApartAnnF_swap G G' F L)
           end
         end.

Lemma fst_renamedApartAnnF_app G F F' L G'
  : fst (renamedApartAnnF renamedApartAnn G (F ++ F') (L, G'))
    = fst (renamedApartAnnF renamedApartAnn G F' (nil, snd ((renamedApartAnnF renamedApartAnn G F (nil, G')))))
          ++ fst (renamedApartAnnF renamedApartAnn G F (L, G')).
Proof.
  general induction F; simpl; eauto.
  - rewrite fst_renamedApartAnnF_swap. reflexivity.
  - rewrite IHF.
    rewrite !snd_renamedApartAnnF; eauto.
Qed.

Lemma fst_renamedApartAnnF_rev G F
  : fst (renamedApartAnnF renamedApartAnn G (rev F) (nil, G))
    = rev (fst (renamedApartAnnF renamedApartAnn G F (nil, G))).
Proof.
  induction F; simpl; eauto.
  renamedApartAnnF_swap_normal.
  rewrite !fst_renamedApartAnnF_app; simpl.
  rewrite rev_app_distr; simpl.
  f_equal. rewrite IHF.
  erewrite fst_renamedApartAnnF_eq; eauto.
Qed.

Lemma poEq_add X `{OrderedType X} (x y:X) s t
  : _eq x y
    -> poEq s t
    -> poEq {x; s} {y; t}.
Proof.
  intros. rewrite H0. rewrite H1. reflexivity.
Qed.

Hint Resolve poEq_add.

Lemma poEq_union X `{OrderedType X} s s' t t'
  : poEq s t
    -> poEq s' t'
    -> poEq (s ∪ s') (t ∪ t').
Proof.
  intros. rewrite H0. rewrite H1. reflexivity.
Qed.

Hint Resolve poEq_union.

Lemma poEq_rev X `{PartialOrder X} L L'
  : poEq L L'
    -> poEq (rev L) (rev L').
Proof.
  intros. general induction H0; simpl; eauto.

Qed.

Hint Resolve poEq_rev.

Lemma renamedApartAnnF_ext G G' F L1 L2 G1 G2
  (IH: forall (n : nat) (Zs : params * stmt),
      get F n Zs ->
      forall G G' : ⦃nat⦄,
      G ≣ G' -> renamedApartAnn (snd Zs) G ≣ renamedApartAnn (snd Zs) G')
  : G ≣ G'
    -> L1 ≣ L2
    -> G1 ≣ G2
    -> renamedApartAnnF renamedApartAnn G F (L1, G1) ≣
                     renamedApartAnnF renamedApartAnn G' F (L2, G2).
Proof.
  general induction F; simpl; eauto 200 using get.
Qed.

Lemma renamedApartAnn_ext G G' s
  : poEq G G'
    -> poEq (renamedApartAnn s G) (renamedApartAnn s G').
Proof.
  revert G G'.
  induction s using stmt_ind'; intros; simpl;
    repeat let_pair_case_eq; subst; eauto 200 using renamedApartAnnF_ext.
Qed.
