Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel.
Require Export EventsActivated StateType paco.

Set Implicit Arguments.
Unset Printing Records.

Class ProgramEquivalence S S' `{StateType S} `{StateType S'} := {
  progeq : (S -> S' -> Prop) -> S -> S' -> Prop
}.

Arguments ProgramEquivalence S S' {H} {H0}.

(* A proof relation is parameterized by analysis information A *)
Class ProofRelation (A:Type) := {
    (* Relates parameter lists according to analysis information *)
    ParamRel : A -> list var -> list var -> Prop;
    (* Relates argument lists according to analysis information
       and closure environments *)
    ArgRel : onv val -> onv val -> A-> list val -> list val -> Prop;
    (* Relates blocks according to analysis information *)
    BlockRel : A-> F.block -> F.block -> Prop;
    (* Ensures that argument lists match parameter lists *)
    RelsOK : forall E E' a Z Z' VL VL', ParamRel a Z Z' -> ArgRel E E' a VL VL' -> length Z = length VL /\ length Z' = length VL'
}.

Inductive simB (SIM:ProgramEquivalence F.state F.state) (r:F.state -> F.state -> Prop) {A} (AR:ProofRelation A)  : F.labenv -> F.labenv -> A -> F.block -> F.block -> Prop :=
| simBI a L L' V V' Z Z' s s'
  : ParamRel a Z Z'
    -> BlockRel a (F.blockI V Z s) (F.blockI V' Z' s')
    -> (forall E E' Y Y' Yv Y'v,
         omap (exp_eval E) Y = Some Yv
         -> omap (exp_eval E') Y' = Some Y'v
         -> ArgRel V V' a Yv Y'v
         -> progeq r (L, E, stmtApp (LabI 0) Y)
                        (L', E', stmtApp (LabI 0) Y'))
    -> simB SIM r AR L L' a (F.blockI V Z s) (F.blockI V' Z' s').

Definition simL' (SIM:ProgramEquivalence F.state F.state) r
           {A} AR (AL:list A) L L' := AIR5 (simB SIM r AR) L L' AL L L'.

Definition fexteq' (SIM:ProgramEquivalence F.state F.state)
           {A} AR (a:A) (AL:list A) E Z s E' Z' s' :=
  ParamRel a Z Z'
  /\
  forall VL VL' L L' (r:rel2 F.state (fun _ : F.state => F.state)),
    ArgRel E E' a VL VL'
    -> simL' SIM r AR AL L L'
    -> progeq r (L, E[Z <-- List.map Some VL], s)
            (L', E'[Z' <-- List.map Some VL'], s').


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
