Require Import CSet Le Coq.Classes.RelationClasses.

Require Import Plus Util AllInRel Map Indexwise.
Require Import CSet Val Var Env IL Sim Fresh Annotation LabelsDefined DecSolve OptionR.

Require Import RenamedApart SetOperations Eqn ValueOpts Infra.Lattice WithTop.

Set Implicit Arguments.
Unset Printing Records.

Require compcert.lib.Integers.


(* None is top *)
Definition aval := option (withTop val).

Coercion option_as_unkown A (a:option A) :=
  match a with
  | Some a => Known a
  | None => Unknown
  end.

Fixpoint op_eval (E:onv (withTop val)) (e:op) : aval :=
  match e with
    | Con v => Some (wTA v)
    | Var x => E x
    | UnOp o e => match op_eval E e with
                 | Some (wTA v) =>
                   match Val.unop_eval o v with
                   | Some v => Some (wTA v)
                   | None => None
                   end
                   | v => v
                 end
    | BinOp o e1 e2 =>
       match op_eval E e1 with
       | Some (wTA v1) =>
         match op_eval E e2 with
         | Some (wTA v2) =>
           match Val.binop_eval o v1 v2 with
           | Some v => Some (wTA v)
           | None => None
           end
         | v => v
         end
       | v => v
       end

  end.

Definition exp_eval (E:onv (withTop val)) (e:exp) : aval :=
  match e with
  | Operation e => op_eval E e
  | _ => Some Top
  end.

Definition cp_choose_op E e :=
  match op_eval E e with
    | Some (wTA c) => Con c
    | _ => e
  end.


Fixpoint constantPropagate (AE:onv (withTop val)) s {struct s} : stmt :=
  match s with
    | stmtLet x (Operation e) s =>
      stmtLet x (Operation (cp_choose_op AE e)) (constantPropagate AE s)
    | stmtLet x (Call f Y) s =>
      stmtLet x (Call f (List.map (cp_choose_op AE) Y))
              (constantPropagate AE s)
    | stmtIf e s t =>
      stmtIf (cp_choose_op AE e)
             (constantPropagate AE s)
             (constantPropagate AE t)
    | stmtApp f Y =>
      stmtApp f (List.map (cp_choose_op AE) Y)
    | stmtReturn e => stmtReturn (cp_choose_op AE e)
    | stmtFun F t =>
      stmtFun (List.map (fun Zs => (fst Zs, constantPropagate AE (snd Zs))) F)
              (constantPropagate AE t)
  end.
