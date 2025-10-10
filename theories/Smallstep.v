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

Fixpoint apply_args_to_expr (args : list var) (e : expr) : expr :=
  match args with
  | [] => e
  | y :: ys => apply_args_to_expr ys (EApp e (EVar y))
  end.

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

  (** matching evaluation rules *)

  (* return with non-empty argument stack applies arguments *)
  | StepReturn1A : forall G A e St,
      A <> [] ->
      step {| cfg_heap := G;
              cfg_ctrl := CtrlMatch A (MReturn e);
              cfg_stack := St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlMatch [] (MReturn (apply_args_to_expr A e));
              cfg_stack := St |}

  (* return with empty args and $ mark evaluates expression *)
  | StepReturn1B : forall G e St,
      step {| cfg_heap := G;
              cfg_ctrl := CtrlMatch [] (MReturn e);
              cfg_stack := KEnd :: St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlExpr e;
              cfg_stack := St |}

  (* Return2: return with empty args and alternative on stack discards alternative *)
  | StepReturn2 : forall G e A' m St,
      step {| cfg_heap := G;
              cfg_ctrl := CtrlMatch [] (MReturn e);
              cfg_stack := KAlt A' m :: St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlMatch [] (MReturn e);
              cfg_stack := St |}

  (* variable pattern performs substitution *)
  | StepBind : forall G y A x m St,
      step {| cfg_heap := G;
              cfg_ctrl := CtrlMatch (y :: A) (MMatch (PVar x) m);
              cfg_stack := St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlMatch A (subst_matching m y x);
              cfg_stack := St |}

  (* constructor pattern switches to expression evaluation *)
  | StepCons1 : forall G y A c ps m St,
      step {| cfg_heap := G;
              cfg_ctrl := CtrlMatch (y :: A) (MMatch (PCons c ps) m);
              cfg_stack := St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlExpr (EVar y);
              cfg_stack := KPat A c ps m :: St |}

  (* successful constructor match decomposes into nested matches *)
  | StepCons2 : forall G c args A ps m St,
      length args = length ps ->
      step {| cfg_heap := G;
              cfg_ctrl := CtrlExpr (ECons c (map EVar args));
              cfg_stack := KPat A c ps m :: St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlMatch A (build_nested_matches args ps m);
              cfg_stack := St |}

  (* constructor mismatch leads to failure *)
  | StepFail : forall G c c' args A ps m St,
      c <> c' ->
      step {| cfg_heap := G;
              cfg_ctrl := CtrlExpr (ECons c' args);
              cfg_stack := KPat A c ps m :: St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlMatch [] MFail;
              cfg_stack := St |}

  (* argument supply pushes argument onto local stack *)
  | StepArg : forall G A y m St,
      step {| cfg_heap := G;
              cfg_ctrl := CtrlMatch A (MSupply (EVar y) m);
              cfg_stack := St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlMatch (y :: A) m;
              cfg_stack := St |}

  (* alternative pushes second branch onto stack *)
  | StepAlt1 : forall G A m1 m2 St,
      step {| cfg_heap := G;
              cfg_ctrl := CtrlMatch A (MAlt m1 m2);
              cfg_stack := St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlMatch A m1;
              cfg_stack := KAlt A m2 :: St |}

  (* failure pops alternative from stack *)
  | StepAlt2 : forall G A' A m St,
      step {| cfg_heap := G;
              cfg_ctrl := CtrlMatch A' MFail;
              cfg_stack := KAlt A m :: St |}
           {| cfg_heap := G;
              cfg_ctrl := CtrlMatch A m;
              cfg_stack := St |}

  (* allocate bindings in heap with fresh variables *)
  (*| StepWhere : forall G A m binds St ys renamed_binds renamed_m,*)
  (*    length ys = length binds ->*)
  (*    (* ys are fresh *)*)
  (*    (forall y, In y ys -> heap_lookup G y = None) ->*)
  (*    (* perform renaming *)*)
  (*    renamed_binds = rename_bindings binds ys ->*)
  (*    renamed_m = rename_matching m ys binds ->*)
  (*    step {| cfg_heap := G;*)
  (*            cfg_ctrl := CtrlMatch A (MWhere m binds);*)
  (*            cfg_stack := St |}*)
  (*         {| cfg_heap := allocate_bindings G renamed_binds;*)
  (*            cfg_ctrl := CtrlMatch A renamed_m;*)
  (*            cfg_stack := St |}*)
.

(* refl and transitive closure of step *)
Inductive step_star : config -> config -> Prop :=
  | step_refl : forall c,
      step_star c c
  | step_trans : forall c1 c2 c3,
      step c1 c2 ->
      step_star c2 c3 ->
      step_star c1 c3.

Notation "c1 s=> c2" := (step c1 c2) (at level 70).
Notation "c1 s=>* c2" := (step_star c1 c2) (at level 70).

Lemma step_star_one : forall c1 c2,
  c1 s=> c2 -> c1 s=>* c2.
Proof.
  intros. eapply step_trans; eauto. constructor.
Qed.

Lemma step_star_trans : forall c1 c2 c3,
  c1 s=>* c2 -> c2 s=>* c3 -> c1 s=>* c3.
Proof.
  intros. induction H.
  - assumption.
  - eapply step_trans; eauto.
Qed.

Definition initial_config (e : expr) : config :=
  {| cfg_heap := empty_heap;
     cfg_ctrl := CtrlExpr e;
     cfg_stack := [] |}.

Definition is_final_expr (c : config) : Prop :=
  exists w, cfg_ctrl c = CtrlExpr w /\ whnf w /\ cfg_stack c = [].

Definition is_stuck (c : config) : Prop :=
  cfg_ctrl c = CtrlMatch [] MFail /\
  exists S, cfg_stack c = KEnd :: S.

(* Balanced evaluations (4.2) *)

Definition extends_stack (S S' : stack) : Prop :=
  exists prefix, S' = prefix ++ S.

Definition balanced_expr_eval (G : heap) (e : expr) (D : heap) (w : expr) (St : stack) : Prop :=
  {| cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |} s=>*
  {| cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |} /\
  whnf w.

Definition balanced_matching_eval (G : heap) (A : list var) (m : matching)
                                  (D : heap) (u : matching_result) (St : stack) : Prop :=
  match u with
  | MRReturn e =>
      {| cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |} s=>*
      {| cfg_heap := D; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := St |}
  | MRFail =>
      {| cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |} s=>*
      {| cfg_heap := D; cfg_ctrl := CtrlMatch [] MFail; cfg_stack := St |}
  end.

