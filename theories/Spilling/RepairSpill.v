Require Import List Map Env AllInRel Exp MoreList.
Require Import IL.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound OneOrEmpty.
Require Import Take TakeSet MoreTac.

Goal forall s t u v w : ⦃var⦄, (s ∪ t) ∩ v [=] s ∪ t ∩ v.

Fixpoint repairSpill
         (k : nat)
         (ZL: list params)
         (Λ : list (⦃var⦄ * ⦃var⦄))
         (R M : ⦃var⦄)
         (s : stmt)
         (lv : ann ⦃var⦄)
         (sl : spilling)
         {struct s}
         ls
  : spilling :=
  match s,lv,sl with

  | stmtLet x e s, ann1 _ lv', ann1 (Sp,L,_) sl'
    => let Fv_e := Exp.freeVars e in
      let L'   := (M ∩ L) ∪ (Fv_e \ R) in
      let K    := of_list (take (cardinal (R ∪ L') - k) (elements (R \ Fv_e \ getAnn lv')
                                                                  ++ (elements R \ Fv_e)) in
      let R_e  := R \ K ∪ L' in
      let K_x  := one_or_empty_if' k R_e (R_e \ getAnn lv') in
      let Sp'  := (R ∩ Sp) ∪ (getAnn lv' ∩ (K ∪ K_x) \ M) in
      let R_s  := {x; R_e \ K_x} in
      ann1 (Sp',L',nil) (repairSpill k ZL Λ R_s (Sp' ∪ M) s lv' sl')

  | stmtReturn e, _, ann0 (Sp,L,_)
    => let Fv_e := Op.freeVars e in
      let L'   := (M ∩ L) ∪ Fv_e \ R in
      let K    := of_list (take (cardinal (R ∪ L') - k) (elements (R \ Fv_e))) in
      let R_e  := R \ K ∪ L' in
      let Sp'  := R ∩ Sp in
      ann0 (Sp',L',nil)

  | stmtIf e s1 s2, ann2 (Sp,L,_) lv1 lv2, ann2 (Sp,L,_) sl1 sl2
    => let Fv_e := Op.freeVars e in
      let L'   := (M ∩ L) ∪ Fv_e \ R in
      let K    := of_list (take (cardinal (R ∪ L') - k)
                                (elements (R \ Fv_e \ getAnn lv1 \ getAnn lv2)
                                          ++ elements R \ Fv_e)) in
       let R_e  := R \ K ∪ L' in
       let Sp'  := (R ∩ Sp) ∪ ((getAnn lv1 ∪ getAnn lv2) ∩ K \ M) in
       ann2 (Sp',L',nil)
            (repairSpill k ZL Λ R_e (Sp' ∪ M) s1 lv1 sl1)
            (repairSpill k ZL Λ R_e (Sp' ∪ M) s2 lv2 sl2)

  | stmtApp f Y, _, ann0 (Sp,L,(R',M')::nil)
    => let R_f := fst (nth (counted f) Λ (∅,∅)) in
      let M_f := snd (nth (counted f) Λ (∅,∅)) in
      let Z   := nth (counted f) ZL nil in
      let L'  := L ∪ R_f \ R \ of_list Z in
      let K   := of_list (take (cardinal (R ∪ L') - k) (elements (R \ R_f))) in
      let Sp' := Sp ∪ M_f \ M \ of_list Z in
      ann0 (Sp',L', (R \ K ∪ L', list_union (Op.freeVars ⊝ Y) \ (R \ K ∪ L))::nil)
      ann0 (Sp',L', (R \ K ∪ L',M')::nil)

  | stmtFun F t, annF LV als lv_t
    => let rms:= (fun f al =>
                   let Lv  := getAnn al in (* liveness in fn body *)
                   let Z  := fst f in    (* params of fn *)
                   let R_f := of_list (take k (elements Lv)) in
                   let M_f := Lv \ R_f in
                   (R_f, M_f)
                ) ⊜ F als in
       let ZL':= (fun f => fst f) ⊝ F ++ ZL in
       let Λ' := rms ++ Λ in


       annF (∅, ∅, rms)
            ((fun f rmlv
              => match rmlv with (rm, Lv)
                                => simplSpill k ZL' Λ' (fst rm) (snd rm) (snd f) Lv
                 end)
               ⊜ F ((fun rm al => (rm,al)) ⊜ rms als))
            (simplSpill k ZL' Λ' R M t lv_t)

  | _,_ => ann0 (∅, ∅, nil)

  end
.
