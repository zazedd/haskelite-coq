From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common.
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
  c : nat; (* counter for freshness *)
  cfg_heap : heap;
  cfg_ctrl : control;
  cfg_stack : stack
}.

Reserved Notation "c1 s=> c2" (at level 70).
Inductive step : config -> config -> Prop :=
  (** expr evaluation rules *)

  (* (e y) pushes y onto stack and evaluates e *)
  | StepApp1 : forall c G e y St,
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (EApp e (EVar y)); cfg_stack := St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := KArg y :: St |}

  (* lambda with arity > 0 consumes argument from stack *)
  | StepApp2 : forall c G m y St n,
      matching_arity m = Some (S n) ->
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (ELam m); cfg_stack := KArg y :: St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (ELam (MSupply (EVar y) m)); cfg_stack := St |}

  (* saturated matching (arity 0) switches to matching evaluation *)
  | StepSat : forall c G m St,
      matching_arity m = Some 0 ->
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (ELam m); cfg_stack := St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] m; cfg_stack := KEnd :: St |}

  (* lookup variable in heap and mark for update *)
  | StepVar : forall c G y e St,
      heap_lookup G y = Some e ->
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (EVar y); cfg_stack := St |}
      s=>
      {| c := c; cfg_heap := heap_remove G y; cfg_ctrl := CtrlExpr e; cfg_stack := KUpdate y :: St |}

  (* update heap with whnf *)
  | StepUpdate : forall c G y w St,
      whnf w ->
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr w; cfg_stack := KUpdate y :: St |}
      s=>
      {| c := c; cfg_heap := heap_update G y w; cfg_ctrl := CtrlExpr w; cfg_stack := St |}

  (** matching evaluation rules *)

  (* return with non-empty argument stack applies arguments *)
  | StepReturn1A : forall c G A e St,
      A <> [] ->
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MReturn e); cfg_stack := St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] (MReturn (apply_args A e)); cfg_stack := St |}

  (* return with empty args and $ mark evaluates expression *)
  | StepReturn1B : forall c G e St,
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := KEnd :: St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |}

  (* Return2: return with empty args and alternative on stack discards alternative *)
  | StepReturn2 : forall c G e A' m St,
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := KAlt A' m :: St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := St |}

  (* variable pattern performs substitution *)
  | StepBind : forall c G y A x m St,
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch (y :: A) (MMatch (PVar x) m); cfg_stack := St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (subst_matching m y x); cfg_stack := St |}

  (* constructor pattern switches to expression evaluation *)
  | StepCons1 : forall c G y A con ps m St,
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch (y :: A) (MMatch (PCons con ps) m); cfg_stack := St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (EVar y); cfg_stack := KPat A con ps m :: St |}

  (* successful constructor match decomposes into nested matches *)
  | StepCons2 : forall c G con args A ps m St,
      length args = length ps ->
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (ECons con (map EVar args)); cfg_stack := KPat A con ps m :: St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (build_nested_matches args ps m); cfg_stack := St |}

  (* constructor mismatch leads to failure *)
  | StepFail : forall c G con con' args A ps m St,
      con <> con' ->
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (ECons con' args); cfg_stack := KPat A con ps m :: St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] MFail; cfg_stack := St |}

  (* argument supply pushes argument onto local stack *)
  | StepArg : forall c G A y m St,
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MSupply (EVar y) m); cfg_stack := St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch (y :: A) m; cfg_stack := St |}

  (* alternative pushes second branch onto stack *)
  | StepAlt1 : forall c G A m1 m2 St,
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MAlt m1 m2); cfg_stack := St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m1; cfg_stack := KAlt A m2 :: St |}

  (* failure pops alternative from stack *)
  | StepAlt2 : forall c G A' A m St,
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A' MFail; cfg_stack := KAlt A m :: St |}
      s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |}

  (* allocate bindings in heap with fresh variables *)
  | StepWhere : forall c G A m binds St ys renamed_binds renamed_m,
    (* generate fresh variables from counter *)
    ys = gen_n_fresh c (length binds) ->
    renamed_binds = rename_bindings binds ys ->
    renamed_m = rename_matching m ys binds ->
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MWhere m binds); cfg_stack := St |}
    s=>
    {| c := c + length binds; 
        cfg_heap := allocate_bindings G renamed_binds;
        cfg_ctrl := CtrlMatch A renamed_m;
        cfg_stack := St |}

where "c1 s=> c2" := (step c1 c2).

(* refl and transitive closure of step *)

Reserved Notation "c1 s=>* c2" (at level 40).
Inductive step_star : config -> config -> Prop :=
  | step_refl : forall c,
      c s=>* c
  | step_trans : forall c1 c2 c3,
      c1 s=> c2 ->
      c2 s=>* c3 ->
      c1 s=>* c3
where "c1 s=>* c2" := (step_star c1 c2).

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

Lemma map_EVar_inj : forall args1 args2,
      map EVar args1 = map EVar args2 -> args1 = args2.
Proof.
  intros.
  apply map_injective in H; auto.
  intros. inversion H0. reflexivity.
Qed.

Ltac solve_determinism_small :=
  match goal with
  | [ H1 : CtrlExpr ?e = CtrlExpr ?e2,
      H2 : whnf ?w |- _ ] =>
      inversion H1; subst;
      inversion H2; subst;
      try (match goal with
           | [ H1 : matching_arity ?m = Some 0,
               H2 : matching_arity ?m = Some (S ?n) |- _ ] =>
               rewrite H1 in H2; discriminate
           end)
  end.

Lemma small_step_deterministic : forall e e1 e2,
  e s=> e1 -> e s=> e2 -> e1 = e2.
Proof.
  intros e e1 e2 H1 H2.
  destruct e as [G ctrl St].
  inversion H1; inversion H2; subst;
  (* this generates lots of cases. most of them solvable by congruence*)
  try congruence;
  (* others solved by proving that the whnf is impossible *)
  try solve_determinism_small.

  inversion H10; subst.
  apply map_EVar_inj in H3; subst.
  inversion H11; subst.
  reflexivity.
Qed.

Lemma step_star_step : forall e1 e2 e3,
  e1 s=>* e2 ->
  e2 s=> e3 ->
  e1 s=>* e3.
Proof.
  intros e1 e2 e3 Hstar Hstep.
  induction Hstar.
  - eapply step_trans; eauto. constructor.
  - eapply step_trans; eauto.
Qed.


Definition initial_config (e : expr) : config :=
  {| c := 0;
     cfg_heap := empty_heap;
     cfg_ctrl := CtrlExpr e;
     cfg_stack := [] |}.

Definition is_final_expr (c : config) : Prop :=
  exists w, cfg_ctrl c = CtrlExpr w /\ whnf w /\ cfg_stack c = [].

Definition is_stuck (c : config) : Prop :=
  cfg_ctrl c = CtrlMatch [] MFail /\
  exists S, cfg_stack c = KEnd :: S.

Definition extends_stack (S S' : stack) : Prop :=
  exists prefix, S = prefix ++ S'.

Lemma extends_stack_refl : forall S,
  extends_stack S S.
Proof.
  intros. unfold extends_stack. exists []. reflexivity.
Qed.

Lemma extends_stack_trans : forall S1 S2 S3,
  extends_stack S1 S2 ->
  extends_stack S2 S3 ->
  extends_stack S1 S3.
Proof.
  intros S1 S2 S3 [p1 H1] [p2 H2].
  unfold extends_stack.
  exists (p1 ++ p2).
  rewrite H1, H2.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma extends_stack_cons : forall k S S',
  extends_stack S S' ->
  extends_stack (k :: S) S'.
Proof.
  intros k S S' [prefix Hext].
  unfold extends_stack.
  exists (k :: prefix).
  simpl. rewrite Hext.
  reflexivity.
Qed.

(* Balanced evaluations (4.2) *)

Fixpoint update_locs (S : stack) : var_set :=
  match S with
  | [] => []
  | KUpdate y :: S' => y :: update_locs S'
  | _ :: S' => update_locs S'
  end.

Lemma update_locs_preserved : forall S k,
  (forall y, k <> KUpdate y) ->
  update_locs (k :: S) = update_locs S.
Proof.
  intros.
  destruct k; simpl; auto.
  exfalso. apply (H v). reflexivity.
Qed.

Lemma update_locs_app : forall S1 S2,
  update_locs (S1 ++ S2) = update_locs S1 ++ update_locs S2.
Proof.
  intros S1. induction S1; intros S2; simpl.
  - reflexivity.
  - destruct a; simpl; auto.
    rewrite IHS1. reflexivity.
Qed.

Lemma update_locs_KEnd : forall S,
  update_locs (KEnd :: S) = update_locs S.
Proof. reflexivity. Qed.

Lemma update_locs_KArg : forall y S,
  update_locs (KArg y :: S) = update_locs S.
Proof. reflexivity. Qed.

Lemma update_locs_KAlt : forall A m S,
  update_locs (KAlt A m :: S) = update_locs S.
Proof. reflexivity. Qed.

Lemma update_locs_KPat : forall A con ps m S,
  update_locs (KPat A con ps m :: S) = update_locs S.
Proof. reflexivity. Qed.

Lemma update_locs_KUpdate : forall y S,
  update_locs (KUpdate y :: S) = y :: update_locs S.
Proof. reflexivity. Qed.

Lemma extends_stack_update_locs : forall S S',
  extends_stack S S' ->
  exists L', update_locs S = L' ++ update_locs S'.
Proof.
  intros S S' [p Hp].
  subst. rewrite update_locs_app.
  exists (update_locs p). reflexivity.
Qed.

Lemma any_stack_extends_empty : forall s,
  extends_stack s [].
Proof.
  intros. unfold extends_stack. exists s.
  rewrite app_nil_r. reflexivity.
Qed.

(* Balanced expression evaluation traces *)

Inductive balanced_step_expr : config -> config -> Prop :=
  (* Empty trace: whnf values are immediately balanced *)
  | BExprWhnf : forall c G w S,
      whnf w ->
      balanced_step_expr
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr w; cfg_stack := S |}
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr w; cfg_stack := S |}

  (* Application: app1 + bal_expr + app2 + bal_expr *)
  | BExprApp : forall c c1 c2 G e y m D O w St,
      (* push argument *)
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (EApp e (EVar y)); cfg_stack := St |} s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := KArg y :: St |} ->

      (* balanced evaluation of e to lambda *)
      balanced_step_expr
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := KArg y :: St |}
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr (ELam m); cfg_stack := KArg y :: St |} ->

      (* apply argument *)
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr (ELam m); cfg_stack := KArg y :: St |} s=>
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr (ELam (MSupply (EVar y) m)); cfg_stack := St |} ->

      (* balanced evaluation of result *)
      balanced_step_expr
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr (ELam (MSupply (EVar y) m)); cfg_stack := St |}
        {| c := c2; cfg_heap := O; cfg_ctrl := CtrlExpr w; cfg_stack := St |} ->

      (* overall is balanced *)
      balanced_step_expr
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (EApp e (EVar y)); cfg_stack := St |}
        {| c := c2; cfg_heap := O; cfg_ctrl := CtrlExpr w; cfg_stack := St |}

  (* Variable lookup: var1 + bal_expr + update *)
  | BExprVar : forall c c1 G y e D w St,
      heap_lookup G y = Some e ->
      ~ (In y (update_locs St)) ->
      (* lookup and push update marker *)
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (EVar y); cfg_stack := St |} s=>
      {| c := c; cfg_heap := heap_remove G y; cfg_ctrl := CtrlExpr e; cfg_stack := KUpdate y :: St |} ->

      (* balanced evaluation of e *)
      balanced_step_expr
        {| c := c; cfg_heap := heap_remove G y; cfg_ctrl := CtrlExpr e; cfg_stack := KUpdate y :: St |}
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := KUpdate y :: St |} ->

      (* update heap *)
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := KUpdate y :: St |} s=>
      {| c := c1; cfg_heap := heap_update D y w; cfg_ctrl := CtrlExpr w; cfg_stack := St |} ->

      (* overall is balanced *)
      balanced_step_expr
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (EVar y); cfg_stack := St |}
        {| c := c1; cfg_heap := heap_update D y w; cfg_ctrl := CtrlExpr w; cfg_stack := St |}

  (* sat lambda: sat + bal_matching + return *)
  | BExprSat : forall c c1 c2 G D O m e w St,
      matching_arity m = Some 0 ->
      (* witch to matching mode *)
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (ELam m); cfg_stack := St |} s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] m; cfg_stack := KEnd :: St |} ->

      (* balanced matching evaluation *)
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] m; cfg_stack := KEnd :: St |}
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := KEnd :: St |} ->

      (* return from matching *)
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := KEnd :: St |} s=>
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr e; cfg_stack := St |} ->

      (* balanced evaluation of result *)
      balanced_step_expr
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr e; cfg_stack := St |}
        {| c := c2; cfg_heap := O; cfg_ctrl := CtrlExpr w; cfg_stack := St |} ->

      (* overall is balanced *)
      balanced_step_expr
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (ELam m); cfg_stack := St |}
        {| c := c2; cfg_heap := O; cfg_ctrl := CtrlExpr w; cfg_stack := St |}

(* Balanced matching evaluation traces *)
with balanced_step_matching : config -> config -> Prop :=
  (* return with empty args *)
  | BMatchReturn : forall c G e St,
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := St |}
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := St |}

  (* return with fail *)
  | BMatchFail : forall c G St,
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] MFail; cfg_stack := St |}
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] MFail; cfg_stack := St |}

  (* non-empty args, apply *)
  | BMatchReturnArgs : forall c c' G D A e St,
      A <> [] ->
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MReturn e); cfg_stack := St |} s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] (MReturn (apply_args A e)); cfg_stack := St |} ->

      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] (MReturn (apply_args A e)); cfg_stack := St |}
        {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch [] (MReturn (apply_args A e)); cfg_stack := St |} ->

      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MReturn e); cfg_stack := St |}
        {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch [] (MReturn (apply_args A e)); cfg_stack := St |}

  (* supply: arg + bal_matching *)
  | BMatchArg : forall c c' G D A A' y m u St,
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MSupply (EVar y) m); cfg_stack := St |} s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch (y :: A) m; cfg_stack := St |} ->
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch (y :: A) m; cfg_stack := St |}
        {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |} ->
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MSupply (EVar y) m); cfg_stack := St |}
        {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |}

  (* binding: bind + bal_matching *)
  | BMatchBind : forall c c' G D A A' x y m u St,
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch (y :: A) (MMatch (PVar x) m); cfg_stack := St |} s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (subst_matching m y x); cfg_stack := St |} ->
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (subst_matching m y x); cfg_stack := St |}
        {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |} ->
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch (y :: A) (MMatch (PVar x) m); cfg_stack := St |}
        {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |}

  (* constructor match success: cons1 + bal_expr + cons2 + bal_matching *)
  | BMatchConsSuccess : forall c c1 c2 G D O A A' x cp ps m args u St,
      (* switch to expr evaluation *)
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch (x :: A) (MMatch (PCons cp ps) m); cfg_stack := St |} s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (EVar x); cfg_stack := KPat A cp ps m :: St |} ->

      (* balanced evaluation of variable to constructor *)
      balanced_step_expr
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (EVar x); cfg_stack := KPat A cp ps m :: St |}
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr (ECons cp (map EVar args)); cfg_stack := KPat A cp ps m :: St |} ->

      (* match succeeds *)
      length ps = length args ->
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr (ECons cp (map EVar args)); cfg_stack := KPat A cp ps m :: St |} s=>
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch A (build_nested_matches args ps m); cfg_stack := St |} ->

      (* balanced evaluation of continuation *)
      balanced_step_matching
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch A (build_nested_matches args ps m); cfg_stack := St |}
        {| c := c2; cfg_heap := O; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |} ->

      (* overall is balanced *)
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch (x :: A) (MMatch (PCons cp ps) m); cfg_stack := St |}
        {| c := c2; cfg_heap := O; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |}

  (* constructor match failure: cons1 + bal_expr + fail *)
  | BMatchConsFail : forall c c1 G D A x cp cp' ps m args St,
      cp <> cp' ->
      (* switch to expr evaluation *)
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch (x :: A) (MMatch (PCons cp ps) m); cfg_stack := St |} s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (EVar x); cfg_stack := KPat A cp ps m :: St |} ->

      (* balanced evaluation of variable to constructor *)
      balanced_step_expr
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (EVar x); cfg_stack := KPat A cp ps m :: St |}
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr (ECons cp' args); cfg_stack := KPat A cp ps m :: St |} ->

      (* match fails *)
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr (ECons cp' args); cfg_stack := KPat A cp ps m :: St |} s=>
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch [] MFail; cfg_stack := St |} ->

      (* overall is balanced *)
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch (x :: A) (MMatch (PCons cp ps) m); cfg_stack := St |}
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch [] MFail; cfg_stack := St |}

  (* alt left succeeds: alt1 + bal_matching + return2 *)
  | BMatchAltLeft : forall c c1 G D A m1 m2 e St,
      (* push alt *)
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MAlt m1 m2); cfg_stack := St |} s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m1; cfg_stack := KAlt A m2 :: St |} ->

      (* balanced evaluation of left branch *)
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m1; cfg_stack := KAlt A m2 :: St |}
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := KAlt A m2 :: St |} ->

      (* discard alt *)
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := KAlt A m2 :: St |} s=>
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := St |} ->

      (* overall is balanced *)
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MAlt m1 m2); cfg_stack := St |}
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := St |}

  (* alt left fails: alt1 + bal_matching + alt2 + balanced *)
  | BMatchAltRight : forall c c1 c2 G D O A A' m1 m2 u St,
      (* push alt *)
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MAlt m1 m2); cfg_stack := St |} s=>
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m1; cfg_stack := KAlt A m2 :: St |} ->

      (* balanced evaluation of left branch to failure *)
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m1; cfg_stack := KAlt A m2 :: St |}
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch [] MFail; cfg_stack := KAlt A m2 :: St |} ->

      (* pop and try right branch *)
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch [] MFail; cfg_stack := KAlt A m2 :: St |} s=>
      {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch A m2; cfg_stack := St |} ->

      (* balanced evaluation of right branch *)
      balanced_step_matching
        {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch A m2; cfg_stack := St |}
        {| c := c2; cfg_heap := O; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |} ->

      (* overall is balanced *)
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MAlt m1 m2); cfg_stack := St |}
        {| c := c2; cfg_heap := O; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |}

  (* where: allocate and continue *)
  | BMatchWhere : forall c G D A A' m binds u ys renamed_binds renamed_m St,
      ys = gen_n_fresh c (length binds) ->
      renamed_binds = rename_bindings binds ys ->
      renamed_m = rename_matching m ys binds ->
      (* allocate bindings *)
      {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MWhere m binds); cfg_stack := St |} s=>
      {| c := c + length binds; cfg_heap := allocate_bindings G renamed_binds; cfg_ctrl := CtrlMatch A renamed_m; cfg_stack := St |} ->

      (* balanced evaluation of body *)
      balanced_step_matching
        {| c := c + length binds; cfg_heap := allocate_bindings G renamed_binds; cfg_ctrl := CtrlMatch A renamed_m; cfg_stack := St |}
        {| c := c + length binds; cfg_heap := D; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |} ->

      (* overall is balanced *)
      balanced_step_matching
        {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A (MWhere m binds); cfg_stack := St |}
        {| c := c + length binds; cfg_heap := D; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |}
.

Lemma balanced_expr_same_stack : forall cfg1 cfg2,
  balanced_step_expr cfg1 cfg2 ->
  cfg_stack cfg1 = cfg_stack cfg2.
Proof.
  intros cfg1 cfg2 H.
  induction H; auto.
Qed.

Lemma balanced_matching_same_stack : forall cfg1 cfg2,
  balanced_step_matching cfg1 cfg2 ->
  cfg_stack cfg1 = cfg_stack cfg2.
Proof.
  intros cfg1 cfg2 H.
  induction H; auto.
Qed.

(* Balanced evaluations correspond to step_star *)
Lemma balanced_expr_to_steps : forall cfg1 cfg2,
  balanced_step_expr cfg1 cfg2 ->
  cfg1 s=>* cfg2
with balanced_matching_to_steps : forall cfg1 cfg2,
  balanced_step_matching cfg1 cfg2 ->
  cfg1 s=>* cfg2.
Proof.
  - intros cfg1 cfg2 H.
    induction H.
    + constructor.
    + (* BExprApp *)
      eapply step_star_trans. eapply step_star_one. eauto.
      eapply step_star_trans. eauto.
      eapply step_star_trans. eapply step_star_one. eauto.
      eauto.

    + (* BExprVar *)
      eapply step_star_trans. eapply step_star_one. eauto.
      eapply step_star_trans. eauto.
      eapply step_star_one. eauto.

    + (* BExprSat *)
      eapply step_star_trans. eapply step_star_one. eauto.
      eapply step_star_trans. eauto.
      eapply step_star_trans. eapply step_star_one. eauto.
      eauto.

  - intros cfg1 cfg2 H.
    induction H; try constructor.
    + (* BMatchReturnArgs *)
      eapply step_star_trans. eapply step_star_one. eauto. eauto.

    + (* BMatchArg *)
      eapply step_star_trans. eapply step_star_one. eauto. eauto.

    + (* BMatchBind *)
      eapply step_star_trans. eapply step_star_one. eauto. eauto.

    + (* BMatchConsSuccess *)
      eapply step_star_trans. eapply step_star_one. eauto.
      eapply step_star_trans. apply balanced_expr_to_steps. eauto.
      eapply step_star_trans. eapply step_star_one. eauto.
      eauto.

    + (* BMatchConsFail *)
      eapply step_star_trans. eapply step_star_one. eauto.
      eapply step_star_trans. apply balanced_expr_to_steps. eauto.
      eapply step_star_one. eauto.

    + (* BMatchAltLeft *)
      eapply step_star_trans. eapply step_star_one. eauto.
      eapply step_star_trans. eauto.
      eapply step_star_one. eauto.

    + (* BMatchAltRight *)
      eapply step_star_trans. eapply step_star_one. eauto.
      eapply step_star_trans. eauto.
      eapply step_star_trans. eapply step_star_one. eauto.
      eauto.

    + (* BMatchWhere *)
      eapply step_star_trans. eapply step_star_one. eauto.
      eauto.
Qed.

Lemma step_removes_KArg : forall cfg cfg',
  cfg s=> cfg' ->
  exists y St, cfg_stack cfg = KArg y :: St ->
  (cfg_stack cfg' = St \/
   exists y', cfg_stack cfg' = KArg y' :: St).
Proof.
  intros cfg cfg' Hstep.
  inversion Hstep; subst; simpl;
  try (exists y, St; intros H2; list_contradiction);
  try (exists "impossible"%string, St; intros H2; list_contradiction);
  try (exists "impossible"%string, St; intros H2; inversion H2).
  left. reflexivity.
Qed.

Lemma step_preserves_removes_or_adds_some_top : forall c1 c2 k St,
  cfg_stack c1 = k :: St ->
  c1 s=> c2 ->

  cfg_stack c2 = k :: St \/
  cfg_stack c2 = St \/
  (exists y, cfg_stack c2 = KArg y :: k :: St) \/
  (cfg_stack c2 = KEnd :: k :: St) \/
  (exists y, cfg_stack c2 = KUpdate y :: k :: St) \/
  (exists A con ps m, cfg_stack c2 = KPat A con ps m :: k :: St) \/
  (exists A m, cfg_stack c2 = KAlt A m :: k :: St).
Proof.
  intros c1 c2 k St Hstack Hstep.
  destruct c1 as [c1' G1 ctrl1 S1].
  simpl in Hstack. subst S1.

  inversion Hstep; subst; simpl in *; try discriminate;
  try (left; reflexivity); try (right; reflexivity);
  try (right; left; reflexivity).
  - right. right. left. exists y. reflexivity.
  - right. right. right. left. reflexivity.
  - right. right. right. right. left. exists y. reflexivity.
  - right. right. right. right. right. left. exists A, con, ps, m. reflexivity.
  - repeat right. exists A, m2. reflexivity.
Qed.

Lemma step_from_empty_stack : forall c G e c' G' ctrl' S',
  {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := [] |} s=>
  {| c := c'; cfg_heap := G'; cfg_ctrl := ctrl'; cfg_stack := S' |} ->
  (S' = [] /\ exists w, ctrl' = CtrlExpr w /\ whnf w) \/
  (exists y e', e = EApp e' (EVar y) /\ S' = [KArg y] /\ ctrl' = CtrlExpr e') \/
  (exists y e', heap_lookup G y = Some e' /\ e = EVar y /\ 
                S' = [KUpdate y] /\ ctrl' = CtrlExpr e') \/
  (exists m, e = ELam m /\ matching_arity m = Some 0 /\ 
             S' = [KEnd] /\ ctrl' = CtrlMatch [] m).
Proof.
  intros c G e c' G' ctrl' S' Hstep.
  inversion Hstep; subst; simpl in *; try discriminate.
  - right. left. exists y, e0. auto.
  - right. right. right. exists m. auto.
  - right. right. left. exists y, e0. auto.
Qed.

