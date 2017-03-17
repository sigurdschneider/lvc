Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound OneOrEmpty.



Set Implicit Arguments.

(** * Register Liveness *)

Fixpoint reg_live 
         (Lv : list ⦃var⦄)
         (ZL : list params)
         (G : ⦃var⦄)
         (s : stmt)
         (sl : spilling)
         {struct s}
  : ann ⦃var⦄
  :=
    match s, sl with
    | stmtLet x e s, ann1 (Sp, L, _) sl'
      => let lv_s := reg_live Lv ZL (singleton x) s sl' in
        (* subtracting L might lead to unnecessary gaps in the liveness, but this is ok:
           variables are killed from the register directly after their last use *)
        ann1 (G ∪ Sp ∪ (((getAnn lv_s) \ singleton x ∪ Exp.freeVars e) \ L)) lv_s

    | stmtReturn e, ann0 (Sp, L, _)
      => ann0 (G ∪ Sp ∪ (Op.freeVars e \ L))

    | stmtIf e s1 s2, ann2 (Sp, L, _) sl1 sl2
      => let lv1 := reg_live Lv ZL ∅ s1 sl1 in
        let lv2 := reg_live Lv ZL ∅ s2 sl2 in
        ann2 (G ∪ Sp ∪ ((getAnn lv1 ∪ getAnn lv2 ∪ Op.freeVars e) \ L)) lv1 lv2

    | stmtApp f Y, ann0 (Sp, L, (_,Sl)::nil)
      => let blv := nth (counted f) Lv ∅ in
        let Z   := nth (counted f) ZL nil in
        ann0 (G ∪ Sp ∪ (((list_union (Op.freeVars ⊝ Y) ∩ Sl) ∪ blv \ of_list Z) \ L))

    | stmtFun F t, annF (Sp, L, rms) sl_F sl_t
      => let lv_t := reg_live (fst ⊝ rms ++ Lv) (fst ⊝ F ++ ZL) ∅ t sl_t in
        let lv_F := (fun ps sl_s => reg_live (fst ⊝ rms ++ Lv)
                                          (fst ⊝ F   ++ ZL)
                                          (of_list (fst ps))
                                          (snd ps)
                                           sl_s
                    ) ⊜ F sl_F in
        annF (G ∪ Sp ∪ ((getAnn lv_t ∪ G) \ L)) lv_F lv_t

    | _,_ => ann0 G
    end
.

                                               