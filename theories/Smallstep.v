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

Reserved Notation "c1 s=( St )=>* c2" (at level 40).
Inductive step_star_bal : config -> config -> stack -> Prop :=
  | step_refl_bal : forall c, forall St,
      extends_stack (cfg_stack c) St ->
      c s=( St )=>* c
  | step_trans_bal : forall c1 c2 c3, forall St,
      extends_stack (cfg_stack c1) St ->
      c1 s=> c2 ->
      c2 s=( St )=>* c3 ->
      c1 s=( St )=>* c3
where "c1 s=( St )=>* c2" := (step_star_bal c1 c2 St).

Lemma step_star_bal_one : forall c1 c2 St,
  extends_stack (cfg_stack c1) St ->
  extends_stack (cfg_stack c2) St ->
  c1 s=> c2 -> c1 s=( St )=>* c2.
Proof.
  intros. eapply step_trans_bal; eauto. constructor. assumption.
Qed.

Lemma step_star_bal_trans : forall c1 c2 c3 St,
  c1 s=( St )=>* c2 -> c2 s=( St )=>* c3 -> c1 s=( St )=>* c3.
Proof.
  intros. induction H.
  - assumption.
  - eapply step_trans_bal; eauto.
Qed.

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

Lemma any_stack_extends_empty : forall s,
  extends_stack s [].
Proof.
  intros. unfold extends_stack. exists s.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma balanced_implies_star : forall c1 c2 St,
  c1 s=( St )=>* c2 ->
  c1 s=>* c2.
Proof.
  intros. induction H.
  + constructor.
  + eapply step_trans; eauto.
Qed.

Lemma star_to_balanced_empty_end : forall c1 c2,
  c1 s=>* c2 ->
  cfg_stack c2 = [] ->
  c1 s=( [] )=>* c2.
Proof.
  intros c1 c2 Hstar.
  induction Hstar; intro Hst2.
  - constructor. apply any_stack_extends_empty.
  - eapply step_trans_bal.
    * apply any_stack_extends_empty.
    * exact H.
    * apply IHHstar. exact Hst2.
Qed.

Lemma step_star_balanced_empty_to_empty : forall c1 c2,
  cfg_stack c1 = [] ->
  cfg_stack c2 = [] ->
  c1 s=>* c2 <-> c1 s=( [] )=>* c2.
Proof.
  intros. split; intros.
  - apply star_to_balanced_empty_end; assumption.
  - eapply balanced_implies_star. exact H1.
Qed.

(* inversion lemams for balanced *)

Lemma step_star_bal_inv_whnf : forall c G w St S,
  whnf w ->
  extends_stack St S ->
  {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr w; cfg_stack := St |} s=( S )=>*
  {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr w; cfg_stack := St |}.
Proof. intros. constructor. assumption. Qed.

Lemma step_sat_analysis : forall c G m St c' D w,
  matching_arity m = Some 0 ->
  {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr (ELam m); cfg_stack := St |} s=( St )=>*
  {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |} ->
  whnf w ->
  exists c1 D1 e,
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch [] m; cfg_stack := KEnd :: St |} s=( KEnd :: St )=>*
    {| c := c1; cfg_heap := D1; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := KEnd :: St |} /\
    {| c := c1; cfg_heap := D1; cfg_ctrl := CtrlExpr e; cfg_stack := St |} s=( St )=>*
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |}.
Proof.
  intros.
  inversion H0; subst; auto.
  - inversion H1. rewrite H3 in H. discriminate.
  - exists c', D, w.
    split.
    + admit.
    + constructor. simpl. apply extends_stack_refl.
Admitted.

