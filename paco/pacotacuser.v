Require Export paconotation pacotac pacodef.
Set Implicit Arguments.

(** ** Type Class for acc, mult, fold and unfold
*)

Class paco_class (A : Prop) :=
{ pacoacctyp: Type
; pacoacc : pacoacctyp
; pacomulttyp: Type
; pacomult : pacomulttyp
; pacofoldtyp: Type
; pacofold : pacofoldtyp
; pacounfoldtyp: Type
; pacounfold : pacounfoldtyp
}.

Definition get_paco_cls {A} {cls: paco_class A} (a: A) := cls.

Create HintDb paco.

Ltac paco_class TGT method :=
  let typ := fresh "_typ_" in let lem := fresh "_lem_" in
  let TMP := fresh "_tmp_" in let X := fresh "_X_" in
  let CLS := fresh "_CLS_" in
  evar (typ: Type); evar (lem: typ);
  assert(TMP: TGT -> True) by (
    intros X; set (CLS := method _ (get_paco_cls X));
    repeat red in CLS; clear X; revert lem;
    match goal with [CLS := ?v |-_] => instantiate (1:= v) end;
    clear CLS; exact I);
  clear TMP; unfold typ in *; clear typ; revert lem.

(** ** pfold tactic
  - [pfold]
*)

Ltac pfold := let x := fresh "_x_" in
  repeat red;
  match goal with [|- ?G] => paco_class G (@pacofold) end;
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem end.

(** ** punfold tactic
  - [punfold H]
*)

Ltac punfold H := let x := fresh "_x_" in
  repeat red in H;
  let G := type of H in paco_class G (@pacounfold);
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem in H end;
  eauto with paco.

(** ** pmult tactic
  - [pmult]
*)

Ltac pmult := let x := fresh "_x_" in
  repeat red;
  match goal with [|- ?G] => paco_class G (@pacomult) end;
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem end.

(** ** pcofix tactic
  - [pcofix CIH [with r]]
*)

Tactic Notation "pcofix" ident(CIH) "with" ident(r) :=
  let x := fresh "_x_" in
  generalize _paco_mark_cons; repeat intro; repeat red;
  match goal with [|- ?G] =>
  paco_class G (@pacoacc); intro x;
  match G with
  | paco0 ?gf _ =>
      match goal with [x:=?lem|-_] => clear x; paco_cont0; eapply lem end; paco_post0 CIH with r
  | paco0_2_0 ?gf _ _ _ =>
      match goal with [x:=?lem|-_] => clear x; paco_cont0; eapply lem end; paco_post0 CIH with r
  | paco0_2_1 ?gf _ _ _ =>
      match goal with [x:=?lem|-_] => clear x; paco_cont0; eapply lem end; paco_post0 CIH with r
  | paco0_3_0 ?gf _ _ _ _ _ =>
      match goal with [x:=?lem|-_] => clear x; paco_cont0; eapply lem end; paco_post0 CIH with r
  | paco0_3_1 ?gf _ _ _ _ _ =>
      match goal with [x:=?lem|-_] => clear x; paco_cont0; eapply lem end; paco_post0 CIH with r
  | paco0_3_2 ?gf _ _ _ _ _ =>
      match goal with [x:=?lem|-_] => clear x; paco_cont0; eapply lem end; paco_post0 CIH with r
  | paco1 ?gf _ ?e0 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont1 e0; eapply lem end; paco_post1 CIH with r
  | paco1_2_0 ?gf _ _ _ ?e0 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont1 e0; eapply lem end; paco_post1 CIH with r
  | paco1_2_1 ?gf _ _ _ ?e0 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont1 e0; eapply lem end; paco_post1 CIH with r
  | paco1_3_0 ?gf _ _ _ _ _ ?e0 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont1 e0; eapply lem end; paco_post1 CIH with r
  | paco1_3_1 ?gf _ _ _ _ _ ?e0 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont1 e0; eapply lem end; paco_post1 CIH with r
  | paco1_3_2 ?gf _ _ _ _ _ ?e0 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont1 e0; eapply lem end; paco_post1 CIH with r
  | paco2 ?gf _ ?e0 ?e1 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont2 e0 e1; eapply lem end; paco_post2 CIH with r
  | paco2_2_0 ?gf _ _ _ ?e0 ?e1 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont2 e0 e1; eapply lem end; paco_post2 CIH with r
  | paco2_2_1 ?gf _ _ _ ?e0 ?e1 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont2 e0 e1; eapply lem end; paco_post2 CIH with r
  | paco2_3_0 ?gf _ _ _ _ _ ?e0 ?e1 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont2 e0 e1; eapply lem end; paco_post2 CIH with r
  | paco2_3_1 ?gf _ _ _ _ _ ?e0 ?e1 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont2 e0 e1; eapply lem end; paco_post2 CIH with r
  | paco2_3_2 ?gf _ _ _ _ _ ?e0 ?e1 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont2 e0 e1; eapply lem end; paco_post2 CIH with r
  | paco3 ?gf _ ?e0 ?e1 ?e2 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont3 e0 e1 e2; eapply lem end; paco_post3 CIH with r
  | paco3_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont3 e0 e1 e2; eapply lem end; paco_post3 CIH with r
  | paco3_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont3 e0 e1 e2; eapply lem end; paco_post3 CIH with r
  | paco3_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont3 e0 e1 e2; eapply lem end; paco_post3 CIH with r
  | paco3_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont3 e0 e1 e2; eapply lem end; paco_post3 CIH with r
  | paco3_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont3 e0 e1 e2; eapply lem end; paco_post3 CIH with r
  | paco4 ?gf _ ?e0 ?e1 ?e2 ?e3 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont4 e0 e1 e2 e3; eapply lem end; paco_post4 CIH with r
  | paco4_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont4 e0 e1 e2 e3; eapply lem end; paco_post4 CIH with r
  | paco4_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont4 e0 e1 e2 e3; eapply lem end; paco_post4 CIH with r
  | paco4_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont4 e0 e1 e2 e3; eapply lem end; paco_post4 CIH with r
  | paco4_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont4 e0 e1 e2 e3; eapply lem end; paco_post4 CIH with r
  | paco4_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont4 e0 e1 e2 e3; eapply lem end; paco_post4 CIH with r
  | paco5 ?gf _ ?e0 ?e1 ?e2 ?e3 ?e4 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont5 e0 e1 e2 e3 e4; eapply lem end; paco_post5 CIH with r
  | paco5_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont5 e0 e1 e2 e3 e4; eapply lem end; paco_post5 CIH with r
  | paco5_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont5 e0 e1 e2 e3 e4; eapply lem end; paco_post5 CIH with r
  | paco5_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont5 e0 e1 e2 e3 e4; eapply lem end; paco_post5 CIH with r
  | paco5_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont5 e0 e1 e2 e3 e4; eapply lem end; paco_post5 CIH with r
  | paco5_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont5 e0 e1 e2 e3 e4; eapply lem end; paco_post5 CIH with r
  | paco6 ?gf _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont6 e0 e1 e2 e3 e4 e5; eapply lem end; paco_post6 CIH with r
  | paco6_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont6 e0 e1 e2 e3 e4 e5; eapply lem end; paco_post6 CIH with r
  | paco6_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont6 e0 e1 e2 e3 e4 e5; eapply lem end; paco_post6 CIH with r
  | paco6_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont6 e0 e1 e2 e3 e4 e5; eapply lem end; paco_post6 CIH with r
  | paco6_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont6 e0 e1 e2 e3 e4 e5; eapply lem end; paco_post6 CIH with r
  | paco6_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont6 e0 e1 e2 e3 e4 e5; eapply lem end; paco_post6 CIH with r
  | paco7 ?gf _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont7 e0 e1 e2 e3 e4 e5 e6; eapply lem end; paco_post7 CIH with r
  | paco7_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont7 e0 e1 e2 e3 e4 e5 e6; eapply lem end; paco_post7 CIH with r
  | paco7_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont7 e0 e1 e2 e3 e4 e5 e6; eapply lem end; paco_post7 CIH with r
  | paco7_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont7 e0 e1 e2 e3 e4 e5 e6; eapply lem end; paco_post7 CIH with r
  | paco7_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont7 e0 e1 e2 e3 e4 e5 e6; eapply lem end; paco_post7 CIH with r
  | paco7_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont7 e0 e1 e2 e3 e4 e5 e6; eapply lem end; paco_post7 CIH with r
  | paco8 ?gf _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7; eapply lem end; paco_post8 CIH with r
  | paco8_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7; eapply lem end; paco_post8 CIH with r
  | paco8_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7; eapply lem end; paco_post8 CIH with r
  | paco8_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7; eapply lem end; paco_post8 CIH with r
  | paco8_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7; eapply lem end; paco_post8 CIH with r
  | paco8_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7; eapply lem end; paco_post8 CIH with r
  | paco9 ?gf _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont9 e0 e1 e2 e3 e4 e5 e6 e7 e8; eapply lem end; paco_post9 CIH with r
  | paco9_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont9 e0 e1 e2 e3 e4 e5 e6 e7 e8; eapply lem end; paco_post9 CIH with r
  | paco9_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont9 e0 e1 e2 e3 e4 e5 e6 e7 e8; eapply lem end; paco_post9 CIH with r
  | paco9_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont9 e0 e1 e2 e3 e4 e5 e6 e7 e8; eapply lem end; paco_post9 CIH with r
  | paco9_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont9 e0 e1 e2 e3 e4 e5 e6 e7 e8; eapply lem end; paco_post9 CIH with r
  | paco9_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont9 e0 e1 e2 e3 e4 e5 e6 e7 e8; eapply lem end; paco_post9 CIH with r
  | paco10 ?gf _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9; eapply lem end; paco_post10 CIH with r
  | paco10_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9; eapply lem end; paco_post10 CIH with r
  | paco10_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9; eapply lem end; paco_post10 CIH with r
  | paco10_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9; eapply lem end; paco_post10 CIH with r
  | paco10_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9; eapply lem end; paco_post10 CIH with r
  | paco10_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9; eapply lem end; paco_post10 CIH with r
  | paco11 ?gf _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10; eapply lem end; paco_post11 CIH with r
  | paco11_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10; eapply lem end; paco_post11 CIH with r
  | paco11_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10; eapply lem end; paco_post11 CIH with r
  | paco11_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10; eapply lem end; paco_post11 CIH with r
  | paco11_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10; eapply lem end; paco_post11 CIH with r
  | paco11_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10; eapply lem end; paco_post11 CIH with r
  | paco12 ?gf _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11; eapply lem end; paco_post12 CIH with r
  | paco12_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11; eapply lem end; paco_post12 CIH with r
  | paco12_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11; eapply lem end; paco_post12 CIH with r
  | paco12_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11; eapply lem end; paco_post12 CIH with r
  | paco12_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11; eapply lem end; paco_post12 CIH with r
  | paco12_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11; eapply lem end; paco_post12 CIH with r
  | paco13 ?gf _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12; eapply lem end; paco_post13 CIH with r
  | paco13_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12; eapply lem end; paco_post13 CIH with r
  | paco13_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12; eapply lem end; paco_post13 CIH with r
  | paco13_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12; eapply lem end; paco_post13 CIH with r
  | paco13_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12; eapply lem end; paco_post13 CIH with r
  | paco13_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12; eapply lem end; paco_post13 CIH with r
  | paco14 ?gf _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13; eapply lem end; paco_post14 CIH with r
  | paco14_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13; eapply lem end; paco_post14 CIH with r
  | paco14_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13; eapply lem end; paco_post14 CIH with r
  | paco14_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13; eapply lem end; paco_post14 CIH with r
  | paco14_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13; eapply lem end; paco_post14 CIH with r
  | paco14_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13; eapply lem end; paco_post14 CIH with r
  | paco15 ?gf _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14; eapply lem end; paco_post15 CIH with r
  | paco15_2_0 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14; eapply lem end; paco_post15 CIH with r
  | paco15_2_1 ?gf _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14; eapply lem end; paco_post15 CIH with r
  | paco15_3_0 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14; eapply lem end; paco_post15 CIH with r
  | paco15_3_1 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14; eapply lem end; paco_post15 CIH with r
  | paco15_3_2 ?gf _ _ _ _ _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 =>
      match goal with [x:=?lem|-_] => clear x; paco_cont15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14; eapply lem end; paco_post15 CIH with r
  end end.

Tactic Notation "pcofix" ident(CIH) := pcofix CIH with r.

(** ** [pclearbot] simplifies all hypotheses of the form [P \/ bot{n}] to [P].
*)

Ltac pclearbot :=
  let X := fresh "_X" in
  repeat match goal with
  | [H: _ \/ ?x |- _] => match x with appcontext[pacoid] => destruct H as [H|X]; [|contradiction X] end
  end.

(** ** [pdestruct H] and [pinversion H]
*)

Ltac pdestruct H := punfold H; destruct H; pclearbot.

Ltac pinversion H := punfold H; inversion H; pclearbot.

(** ** pmonauto tactic
  - [pmonauto]
*)

Ltac pmonauto :=
  let IN := fresh "IN" in try (repeat intro; destruct IN; eauto; fail).

(** Tactics for Internal Use Only *)

Ltac paco_cofix_auto :=
  cofix; repeat intro;
  match goal with [H: _ |- _] => destruct H end; econstructor;
  try (match goal with [H: _|-_] => apply H end); intros;
  lazymatch goal with [PR: _ |- _] => match goal with [H: _ |- _] => apply H in PR end end;
  repeat match goal with [ H : _ \/ _ |- _] => destruct H end; first [eauto; fail|eauto 10].

Ltac paco_revert :=
  match goal with [H: _ |- _] => revert H end.

Notation "p <_paco_0= q" :=
  (forall (PR: p : Prop), q : Prop)
  (at level 50, no associativity).

Notation "p <_paco_1= q" :=
  (forall _paco_x0 (PR: p _paco_x0 : Prop), q _paco_x0 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_2= q" :=
  (forall _paco_x0 _paco_x1 (PR: p _paco_x0 _paco_x1 : Prop), q _paco_x0 _paco_x1 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_3= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 (PR: p _paco_x0 _paco_x1 _paco_x2 : Prop), q _paco_x0 _paco_x1 _paco_x2 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_4= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_5= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_6= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_7= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_8= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_9= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_10= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_11= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_12= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_13= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_14= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 : Prop)
  (at level 50, no associativity).

Notation "p <_paco_15= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 _paco_x14 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 _paco_x14 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 _paco_x10 _paco_x11 _paco_x12 _paco_x13 _paco_x14 : Prop)
  (at level 50, no associativity).

