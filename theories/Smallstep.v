From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Bigstep.
Import ListNotations.

(* stack frames *)
Inductive continuation : Type :=
  | KArg : var -> continuation                    (* y *)
  | KUpdate : var -> continuation                 (* !y *)
  | KEnd : continuation                           (* $ *)
  | KAlt : list var -> matching -> continuation   (* ?(A, m) *)
  | KPat : list var -> constructor -> list pattern -> matching -> continuation.
                                                  (* @(A, c(ps) ⇒ m) *)

Definition stack := list continuation.

Inductive control : Type :=
  | CtrlExpr : expr -> control                    (* E e - evaluate expression *)
  | CtrlMatch : list var -> matching -> control.  (* M A m - evaluate matching *)

Record config : Type := {
  cfg_heap : heap;
  cfg_ctrl : control;
  cfg_stack : stack
}.

Inductive step : config -> config -> Prop :=
  (** expr evaluation rules *)

  (* (e y) pushes y onto stack and evaluates e *)
  | StepApp1 : forall G e y St,
    step {| cfg_heap := G;
            cfg_ctrl := CtrlExpr (EApp e (EVar y));
            cfg_stack := St |}
          {| cfg_heap := G;
            cfg_ctrl := CtrlExpr e;
            cfg_stack := KArg y :: St |}

  (* lambda with arity > 0 consumes argument from stack *)
  | StepApp2 : forall G m y St n,
      matching_arity m = Some (S n) ->
      step {| cfg_heap := G;
              cfg_ctrl := CtrlExpr (ELam m);
              cfg_stack := KArg y :: St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlExpr (ELam (MSupply (EVar y) m));
              cfg_stack := St |}

  (* saturated matching (arity 0) switches to matching evaluation *)
  | StepSat : forall G m St,
      matching_arity m = Some 0 ->
      step {| cfg_heap := G;
              cfg_ctrl := CtrlExpr (ELam m);
              cfg_stack := St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlMatch [] m;
              cfg_stack := KEnd :: St |}

  (* lookup variable in heap and mark for update *)
  | StepVar : forall G y e St,
      heap_lookup G y = Some e ->
      step {| cfg_heap := G;
              cfg_ctrl := CtrlExpr (EVar y);
              cfg_stack := St |}
           {| cfg_heap := heap_remove G y;
              cfg_ctrl := CtrlExpr e;
              cfg_stack := KUpdate y :: St |}

  (* update heap with whnf *)
  | StepUpdate : forall G y w St,
      whnf w ->
      step {| cfg_heap := G;
              cfg_ctrl := CtrlExpr w;
              cfg_stack := KUpdate y :: St |}
           {| cfg_heap := heap_update G y w;
              cfg_ctrl := CtrlExpr w;
              cfg_stack := St |}
.

(* refl and transitive closure of step *)
Inductive step_star : config -> config -> Prop :=
  | step_refl : forall c,
      step_star c c
  | step_trans : forall c1 c2 c3,
      step c1 c2 ->
      step_star c2 c3 ->
      step_star c1 c3.
