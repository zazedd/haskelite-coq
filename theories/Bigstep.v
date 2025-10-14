From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common.
Import ListNotations.

Inductive eval_expr : nat -> heap -> var_set -> expr -> 
                      heap -> expr -> nat -> Prop :=
  | EvalWhnf : forall c G L w,
      whnf w ->
      eval_expr c G L w G w c

  | EvalSat : forall c c1 c2 G L m e D O w,
      matching_arity m = Some 0 ->
      eval_matching c G L [] m D (MRReturn e) c1 ->
      eval_expr c1 D L e O w c2 ->
      eval_expr c G L (ELam m) O w c2

  | EvalVar : forall c c' G L y e D w,
      heap_lookup G y = Some e ->
      ~ (In y L) ->
      eval_expr c (heap_remove G y) (y :: L) e D w c' -> (* black-holing *)
      eval_expr c G L (EVar y) (heap_update D y w) w c'

  | EvalApp : forall c c1 c2 G L e1 e2 m D O w x,
      eval_expr c G L e1 D (ELam m) c1 ->
      e2 = EVar x ->
      (* e2 should be a variable *)
      eval_expr c1 D L (ELam (MSupply (EVar x) m)) O w c2 ->
      eval_expr c G L (EApp e1 e2) O w c2

with eval_matching : nat -> heap -> var_set -> list var -> matching -> 
                     heap -> matching_result -> nat -> Prop :=
  | EvalReturn : forall c G L A e,
      eval_matching c G L A (MReturn e) G (MRReturn (apply_args A e)) c

  | EvalMatchFail : forall c G L,
      eval_matching c G L [] MFail G MRFail c

  | EvalArg : forall c c' G L A x m D u,
      eval_matching c G L (x :: A) m D u c' ->
      eval_matching c G L A (MSupply (EVar x) m) D u c'

  | EvalBindVar : forall c c' G L A x y m D u,
      eval_matching c G L A (subst_matching m y x) D u c' ->
      eval_matching c G L (y :: A) (MMatch (PVar x) m) D u c'

  | EvalConsMatch : forall c c1 c2 G L A x cp ps m args D O u,
      eval_expr c G L (EVar x) D (ECons cp (map EVar args)) c1 ->
      length ps = length args ->
      eval_matching c1 D L A (build_nested_matches args ps m) O u c2 ->
      eval_matching c G L (x :: A) (MMatch (PCons cp ps) m) O u c2

  | EvalConsFail : forall c c' G L A x cp cp' ps m args D,
      eval_expr c G L (EVar x) D (ECons cp' args) c' ->
      cp <> cp' ->
      eval_matching c G L (x :: A) (MMatch (PCons cp ps) m) D MRFail c'

  | EvalAltLeft : forall c c' G L A m1 m2 e D,
      eval_matching c G L A m1 D (MRReturn e) c' ->
      eval_matching c G L A (MAlt m1 m2) D (MRReturn e) c'

  | EvalAltRight : forall c c1 c2 G L A m1 m2 D O u,
      eval_matching c G L A m1 D MRFail c1 ->
      eval_matching c1 D L A m2 O u c2 ->
      eval_matching c G L A (MAlt m1 m2) O u c2

  | EvalWhere : forall c G L A m binds D u ys renamed_binds renamed_m,
      (* generate fresh variables using counter *)
      ys = gen_n_fresh c (length binds) ->
      (* perform renaming *)
      renamed_binds = rename_bindings binds ys ->
      renamed_m = rename_matching m ys binds ->
      (* allocate renamed bindings and continue with incremented counter *)
      eval_matching (c + length binds) (allocate_bindings G renamed_binds) L A renamed_m D u (c + length binds) ->
      eval_matching c G L A (MWhere m binds) D u (c + length binds)
.


Scheme eval_expr_ind_mutual := Induction for eval_expr Sort Prop
with eval_matching_ind_mutual := Induction for eval_matching Sort Prop.

Combined Scheme eval_ind from eval_expr_ind_mutual, eval_matching_ind_mutual.

  

Lemma whnf_self_eval : forall c G L e,
  whnf e -> eval_expr c G L e G e c.
Proof.
  intros. constructor. assumption.
Qed.

Lemma matching_arity_preserved_subst : forall m x y,
  matching_arity (subst_matching m y x) = matching_arity m.
Proof.
  intros.
  induction m; simpl; auto.
  + rewrite IHm. trivial.
  + rewrite IHm. trivial.
  + rewrite IHm1, IHm2. trivial.
Qed.

Lemma eval_expr_produces_whnf : forall c G L e D w c',
  eval_expr c G L e D w c' -> whnf w.
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
  | [ H1 : eval_expr ?c ?G ?L ?e ?D1 ?w1 ?c1,
      H2 : eval_expr ?c ?G ?L ?e ?D2 ?w2 ?c2 |- _ ] =>
      let HeqD := fresh "HeqD" in
      let Heqe := fresh "Heqe" in
      let Heqc := fresh "Heqc" in
      assert (D1 = D2 /\ w1 = w2 /\ c1 = c2) as [HeqD [Heqe Heqc]] by (eapply expr_det; eauto);
      try discriminate; try congruence; subst
  end.

Ltac solve_determinism_match match_det :=
  match goal with
  | [ H1 : eval_matching ?c ?G ?L ?A ?m ?D1 ?u1 ?c1,
      H2 : eval_matching ?c ?G ?L ?A ?m ?D2 ?u2 ?c2 |- _ ] =>
      let HeqD := fresh "HeqD" in
      let Hequ := fresh "Hequ" in
      let Heqc := fresh "Heqc" in
      assert (D1 = D2 /\ u1 = u2 /\ c1 = c2) as [HeqD [Hequ Heqc]] by (eapply match_det; eauto);
      try discriminate; try congruence; subst
  end.

Lemma eval_expr_deterministic : forall c G L e D1 w1 c2 D2 w2 c3,
  eval_expr c G L e D1 w1 c2 ->
  eval_expr c G L e D2 w2 c3 ->
  D1 = D2 /\ w1 = w2 /\ c2 = c3
with eval_matching_deterministic : forall c G L A m D1 u1 c2 D2 u2 c3,
  eval_matching c G L A m D1 u1 c2 ->
  eval_matching c G L A m D2 u2 c3 ->
  D1 = D2 /\ u1 = u2 /\ c2 = c3.
Proof.
  - intros c G L e D1 w1 c2 D2 w2 c3 H1 H2.
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
    + inversion H7; subst.
      solve_determinism_expr eval_expr_deterministic.
      inversion Heqe; subst.
      apply IHeval_expr2. assumption.

  - intros c G L A m D1 u1 c2 D2 u2 c3 H1 H2.
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
    + split; [|split]; [| trivial |]; eapply eval_expr_deterministic; eauto.
    + solve_determinism_match eval_matching_deterministic.
    + solve_determinism_match eval_matching_deterministic.
    + solve_determinism_match eval_matching_deterministic. subst. auto.
Qed.
