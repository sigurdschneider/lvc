Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel InRel.
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
    (* Relates environments according to analysis information *)
    RelsOK : forall E E' a Z Z' VL VL', ParamRel a Z Z' -> ArgRel E E' a VL VL' -> length Z = length VL /\ length Z' = length VL'
}.


Inductive simB (SIM:ProgramEquivalence F.state F.state) (r:F.state -> F.state -> Prop) {A} (AR:ProofRelation A)  : list A -> F.labenv -> F.labenv -> A -> F.block -> F.block -> Prop :=
| simBI a L L' V V' Z Z' s s' n AL
  : ParamRel a Z Z'
    -> BlockRel a (F.blockI V Z s n) (F.blockI V' Z' s' n)
    -> (forall E E' Y Y' Yv Y'v,
         omap (exp_eval E) Y = Some Yv
         -> omap (exp_eval E') Y' = Some Y'v
         -> ArgRel V V' a Yv Y'v
         -> progeq r (L, E, stmtApp (LabI n) Y)
                        (L', E', stmtApp (LabI n) Y'))
    -> simB SIM r AR AL L L' a (F.blockI V Z s n) (F.blockI V' Z' s' n).

Definition simL' (SIM:ProgramEquivalence F.state F.state) r
           {A} AR (AL:list A) L L' := inRel (simB SIM r AR) AL L L'.

Definition fexteq' (SIM:ProgramEquivalence F.state F.state)
           {A} (AR:ProofRelation A) (a:A) (AL:list A) E Z s E' Z' s' :=
  ParamRel a Z Z'
  /\
  forall VL VL' L L' (r:rel2 F.state (fun _ : F.state => F.state)),
    ArgRel E E' a VL VL'
    -> simL' SIM r AR AL L L'
    -> progeq r (L, E[Z <-- List.map Some VL], s)
            (L', E'[Z' <-- List.map Some VL'], s').

(* A proof relation is parameterized by analysis information A *)
Class ProofRelationI (A:Type) := {
    (* Relates parameter lists according to analysis information *)
    ParamRelI : A -> list var -> list var -> Prop;
    (* Relates argument lists according to analysis information
       and closure environments *)
    ArgRelI :  A -> list val -> list val -> Prop;
    (* Relates blocks according to analysis information *)
    BlockRelI : A -> I.block -> I.block -> Prop;
    (* Relates environments according to analysis information *)
    RelsOKI : forall a Z Z' VL VL',
        ParamRelI a Z Z' -> ArgRelI a VL VL' ->
        length Z = length VL /\ length Z' = length VL'
}.

Inductive simIBlock (SIM:ProgramEquivalence I.state I.state)
          (r:I.state -> I.state -> Prop)
          {A} (AR:ProofRelationI A)
  : list A -> I.labenv -> I.labenv -> A -> I.block -> I.block -> Prop :=
| simIBI a L L' Z Z' s s' n AL
  : ParamRelI a Z Z'
    -> BlockRelI a (I.blockI Z s n) (I.blockI Z' s' n)
    -> (forall E E' Y Y' Yv Y'v,
         omap (exp_eval E) Y = Some Yv
         -> omap (exp_eval E') Y' = Some Y'v
         -> ArgRelI a Yv Y'v
         -> progeq r (L, E, stmtApp (LabI n) Y)
                        (L', E', stmtApp (LabI n) Y'))
    -> simIBlock SIM r AR AL L L' a (I.blockI Z s n) (I.blockI Z' s' n).

Definition simILabenv (SIM:ProgramEquivalence I.state I.state) r
           {A} AR (AL:list A) L L' := inRel (simIBlock SIM r AR) AL L L'.

Definition fexteqI (SIM:ProgramEquivalence I.state I.state)
           {A} (AR:ProofRelationI A) (a:A) (AL:list A) E Z s E' Z' s' :=
  ParamRelI a Z Z' /\
  forall VL VL' L L' (r:rel2 I.state (fun _ : I.state => I.state)),
    ArgRelI a VL VL'
    -> simILabenv SIM r AR AL L L'
    -> progeq r (L, E[Z <-- List.map Some VL], s)
            (L', E'[Z' <-- List.map Some VL'], s').
