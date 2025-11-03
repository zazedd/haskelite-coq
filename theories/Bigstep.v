From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common.
Import ListNotations.

Section FreshGen.
Context {FG : FreshVarGen}.

Inductive eval_expr : heap -> var_set -> expr -> 
                      heap -> expr -> Prop :=
  | EvalWhnf : forall G L w,
      whnf w ->
      eval_expr G L w G w

  | EvalSat : forall G L m e D O w,
      matching_arity m = Some 0 ->
      eval_matching G L [] m D (MRReturn e) ->
      eval_expr D L e O w ->
      eval_expr G L (ELam m) O w

  | EvalVar : forall G L y e D w,
      heap_lookup G y = Some e ->
      ~ (In y L) ->
      eval_expr (heap_remove G y) (y :: L) e D w -> (* black-holing *)
      eval_expr G L (EVar y) (heap_update D y w) w

  | EvalApp : forall G L e1 e2 m D O w x,
      eval_expr G L e1 D (ELam m) ->
      e2 = EVar x ->
      (* e2 should be a variable *)
      eval_expr D L (ELam (MSupply (EVar x) m)) O w ->
      eval_expr G L (EApp e1 e2) O w

with eval_matching : heap -> var_set -> list var -> matching -> 
                     heap -> matching_result -> Prop :=

  (*eval_matching c G (update_locs St) A (MReturn e0) D (MRReturn (apply_args A e0)) c'*)
  | EvalReturn : forall G L A e,
      eval_matching G L A (MReturn e) G (MRReturn (apply_args A e))

  | EvalMatchFail : forall G L,
      eval_matching G L [] MFail G MRFail

  | EvalArg : forall G L A x m D u,
      eval_matching G L (x :: A) m D u ->
      eval_matching G L A (MSupply (EVar x) m) D u

  | EvalBindVar : forall G L A x y m D u,
      eval_matching G L A (subst_matching m y x) D u ->
      eval_matching G L (y :: A) (MMatch (PVar x) m) D u

  | EvalConsMatch : forall G L A x cp ps m args D O u,
      eval_expr G L (EVar x) D (ECons cp (map EVar args)) ->
      length ps = length args ->
      eval_matching D L A (build_nested_matches args ps m) O u ->
      eval_matching G L (x :: A) (MMatch (PCons cp ps) m) O u

  | EvalConsFail : forall G L A x cp cp' ps m args D,
      eval_expr G L (EVar x) D (ECons cp' args) ->
      cp <> cp' ->
      eval_matching G L (x :: A) (MMatch (PCons cp ps) m) D MRFail

  | EvalAltLeft : forall G L A m1 m2 e D,
      eval_matching G L A m1 D (MRReturn e) ->
      eval_matching G L A (MAlt m1 m2) D (MRReturn e)

  | EvalAltRight : forall G L A m1 m2 D O u,
      eval_matching G L A m1 D MRFail ->
      eval_matching D L A m2 O u ->
      eval_matching G L A (MAlt m1 m2) O u

  | EvalWhere : forall G L A m binds D u ys renamed_binds renamed_m,
      (* generate fresh variables using counter *)
      ys = gen_fresh L (length binds) ->
      (* perform renaming *)
      renamed_binds = rename_bindings binds ys ->
      renamed_m = rename_matching m ys binds ->
      (* allocate renamed bindings and continue with incremented counter *)
      eval_matching (allocate_bindings G renamed_binds) L A renamed_m D u ->
      eval_matching G L A (MWhere m binds) D u
.


Scheme eval_expr_ind_mutual := Induction for eval_expr Sort Prop
with eval_matching_ind_mutual := Induction for eval_matching Sort Prop.

Combined Scheme eval_ind from eval_expr_ind_mutual, eval_matching_ind_mutual.

Lemma eval_expr_produces_whnf : forall G L e D w,
  eval_expr G L e D w -> whnf w.
Proof.
  intros. induction H; assumption.
Qed.

(* Determinism *)

Lemma heap_lookup_deterministic : forall h x e1 e2,
  heap_lookup h x = Some e1 ->
  heap_lookup h x = Some e2 ->
  e1 = e2.
Proof.
  intros h x e1 e2 H1 H2.
  unfold heap_lookup in *.
  apply StringMapFacts.MapsTo_fun with (m := h) (x := x).
  - apply StringMapFacts.find_mapsto_iff; auto.
  - apply StringMapFacts.find_mapsto_iff; auto.
Qed.

Ltac solve_determinism_expr expr_det :=
  match goal with
  | [ H1 : eval_expr ?G ?L ?e ?D1 ?w1,
      H2 : eval_expr ?G ?L ?e ?D2 ?w2 |- _ ] =>
      let HeqD := fresh "HeqD" in
      let Heqe := fresh "Heqe" in
      let Heqc := fresh "Heqc" in
      assert (D1 = D2 /\ w1 = w2) as [HeqD Heqe] by (eapply expr_det; eauto);
      try discriminate; try congruence; subst
  end.

Ltac solve_determinism_match match_det :=
  match goal with
  | [ H1 : eval_matching ?G ?L ?A ?m ?D1 ?u1,
      H2 : eval_matching ?G ?L ?A ?m ?D2 ?u2 |- _ ] =>
      let HeqD := fresh "HeqD" in
      let Hequ := fresh "Hequ" in
      let Heqc := fresh "Heqc" in
      assert (D1 = D2 /\ u1 = u2) as [HeqD Hequ] by (eapply match_det; eauto);
      try discriminate; try congruence; subst
  end.

Lemma eval_expr_deterministic : forall G L e D1 w1 D2 w2,
  eval_expr G L e D1 w1 ->
  eval_expr G L e D2 w2 ->
  D1 = D2 /\ w1 = w2
with eval_matching_deterministic : forall G L A m D1 u1 D2 u2,
  eval_matching G L A m D1 u1 ->
  eval_matching G L A m D2 u2 ->
  D1 = D2 /\ u1 = u2.
Proof.
  - intros G L e D1 w1 D2 w2 H1 H2.
    induction H1; inversion H2; subst; try congruence.
    + auto.
    + inversion H; subst. rewrite H0 in H5. discriminate.
    + inversion H.
    + inversion H.
    + inversion H3. subst. rewrite H5 in H. discriminate.
    + solve_determinism_match eval_matching_deterministic.
      inversion Hequ; subst.
      eapply IHeval_expr; eauto.
    + inversion H3.
    + assert (e = e0) as Heqe. { eapply heap_lookup_deterministic; eauto. }
      subst.
      solve_determinism_expr eval_expr_deterministic.
      subst. auto.
    + inversion H0.
    + inversion H6; subst.
      solve_determinism_expr eval_expr_deterministic.
      inversion Heqe; subst.
      apply IHeval_expr2. assumption.

  - intros G L A m D1 u1 D2 u2 H1 H2.
    induction H1; inversion H2; subst; try congruence; try auto.
    + solve_determinism_expr eval_expr_deterministic.
      injection Heqe as Heqargs.
      apply map_injective in Heqargs; subst.
      * apply IHeval_matching.
        assumption.
      * intros x1 x2 Heq.
        injection Heq. trivial.
    + solve_determinism_expr eval_expr_deterministic.
    + solve_determinism_expr eval_expr_deterministic.
    + split; [ | trivial ]; eapply eval_expr_deterministic; eauto.
    + solve_determinism_match eval_matching_deterministic.
    + solve_determinism_match eval_matching_deterministic.
    + solve_determinism_match eval_matching_deterministic. subst. auto.
Qed.

End FreshGen.
