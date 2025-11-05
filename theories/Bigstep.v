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

  | EvalBop : forall G L op e1 e2 n1 n2 n D1 D2,
      eval_expr G L e1 D1 (ENat n1) ->
      eval_expr D1 L e2 D2 (ENat n2) ->
      eval_bop op n1 n2 = Some n ->
      eval_expr G L (EBop op e1 e2) D2 (ENat n)

with eval_matching : heap -> var_set -> list var -> matching -> 
                     heap -> matching_result -> Prop :=

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

  | EvalNatMatch : forall G L A x n m D1 D2 u,
      eval_expr G L (EVar x) D1 (ENat n) ->
      eval_matching D1 L A m D2 u ->
      eval_matching G L (x :: A) (MMatch (PNat n) m) D2 u

  | EvalNatFail : forall G L A x n1 n2 m D,
      eval_expr G L (EVar x) D (ENat n2) ->
      n1 <> n2 ->
      eval_matching G L (x :: A) (MMatch (PNat n1) m) D MRFail

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
  intros. induction H; try assumption; try constructor.
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
    + inversion H0.
    + assert (H_e1: D1 = D3 /\ ENat n1 = ENat n0).
      { solve_determinism_expr eval_expr_deterministic; auto. }
      destruct H_e1 as [HeqD1 Heqw1].
      injection Heqw1 as Heqn1; subst D3 n0.

      assert (H_e2: D0 = D2 /\ ENat n2 = ENat n3).
      { eapply eval_expr_deterministic; eauto. }
      destruct H_e2 as [HeqD2 Heqw2].
      injection Heqw2 as Heqn2; subst D2 n3.

      rewrite H in H10.
      injection H10 as Heq; subst n4.
      auto.

  - intros G L A m D1 u1 D2 u2 H1 H2.
    induction H1; inversion H2; subst; try congruence; try auto.
    + (* EvalNatMatch vs EvalNatMatch *)
      assert (Hexpr_det: D1 = D3 /\ ENat n = ENat n).
      { apply eval_expr_deterministic with (G := G) (L := L) (e := EVar x); auto. }
      destruct Hexpr_det as [HeqD _]; subst D3.
      apply IHeval_matching in H11.
      assumption.

    + (* EvalNatMatch vs EvalNatFail, contradiction *)
      assert (H_expr: D1 = D2 /\ ENat n = ENat n2).
      { eapply eval_expr_deterministic; eauto. }
      destruct H_expr as [HeqD1 HeqN]; subst D2.
      injection HeqN as HeqN; subst n2.
      contradiction.

    + (* EvalNatFail vs EvalNatMatch, contradiction *)
      assert (H_expr: D = D1 /\ ENat n2 = ENat n1).
      { eapply eval_expr_deterministic; eauto. }
      destruct H_expr as [HeqD HeqN]; subst D1.
      injection HeqN as HeqN; subst n1.
      contradiction.

    + (* EvalNatFail vs EvalNatFail *)
      assert (H_expr: D = D2 /\ ENat n2 = ENat n3).
      { eapply eval_expr_deterministic; eauto. }
      destruct H_expr as [HeqD HeqN]; subst D2.
      injection HeqN as HeqN; subst n3.
      split; auto.

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
