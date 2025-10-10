From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common.
Import ListNotations.

(* type for L, provides freshness *)
Definition var_set := list var.

Definition in_var_set (x : var) (s : var_set) : bool :=
  existsb (String.eqb x) s.

Open Scope string_scope.
Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

Fixpoint generate_fresh_vars (base : var) (n : nat) (avoid : list var) : list var :=
  match n with
  | O => []
  | S n' => 
      let candidate := base ++ "_" ++ string_of_nat (length avoid + n') in
      if in_dec string_dec candidate avoid then
        generate_fresh_vars base n' avoid
      else
        candidate :: generate_fresh_vars base n' (candidate :: avoid)
  end.

Inductive eval_expr : heap -> var_set -> expr -> heap -> expr -> Prop :=
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
      (* e2 should be a variable *)
      e2 = EVar x ->
      eval_expr D L (ELam (MSupply (EVar x) m)) O w ->
      eval_expr G L (EApp e1 e2) O w

with eval_matching : heap -> var_set -> list var -> matching -> heap -> matching_result -> Prop :=
  | EvalReturn : forall G L A e,
      eval_matching G L A (MReturn e) G (MRReturn (apply_args A e))

  | EvalMatchFail : forall G L A,
      eval_matching G L A MFail G MRFail

  | EvalArg : forall G L A x m D u,
      eval_matching G L (x :: A) m D u ->
      eval_matching G L A (MSupply (EVar x) m) D u

  | EvalBindVar : forall G L A x y m D u,
      eval_matching G L A (subst_matching m y x) D u ->
      eval_matching G L (y :: A) (MMatch (PVar x) m) D u

  | EvalConsMatch : forall G L A x c ps m args D O u,
      eval_expr G L (EVar x) D (ECons c (map EVar args)) ->
      length ps = length args ->
      eval_matching D L A (build_nested_matches args ps m) O u ->
      eval_matching G L (x :: A) (MMatch (PCons c ps) m) O u

  | EvalConsFail : forall G L A x c c' ps m args D,
      eval_expr G L (EVar x) D (ECons c' args) ->
      c <> c' ->
      eval_matching G L (x :: A) (MMatch (PCons c ps) m) D MRFail

  | EvalAltLeft : forall G L A m1 m2 e D,
      eval_matching G L A m1 D (MRReturn e) ->
      eval_matching G L A (MAlt m1 m2) D (MRReturn e)

  | EvalAltRight : forall G L A m1 m2 D O u,
      eval_matching G L A m1 D MRFail ->
      eval_matching D L A m2 O u ->
      eval_matching G L A (MAlt m1 m2) O u

  (* this would require a full alpha equivalence relation *)
  (*| EvalWhere : forall G L A m binds D u ys renamed_binds renamed_m,*)
  (*    length ys = length binds ->*)
  (*    (* ys are fresh w.r.t. G, L, A, m, and bindings *)*)
  (*    (forall y, In y ys -> ~In y L /\ heap_lookup G y = None) ->*)
  (*    (* perform renaming *)*)
  (*    renamed_binds = rename_bindings binds ys ->*)
  (*    renamed_m = rename_matching m ys binds ->*)
  (*    (* allocate renamed bindings in heap *)*)
  (*    eval_matching (allocate_bindings G renamed_binds) L A renamed_m D u ->*)
  (*    eval_matching G L A (MWhere m binds) D u*)

  (* for now, canonical naming is enough *)
  | EvalWhere : forall G L A m binds D u,
    let avoid := List.app L (map fst (StringMap.elements G)) in
    let ys := generate_fresh_vars "y" (length binds) avoid in
    eval_matching (allocate_bindings G (rename_bindings binds ys)) L A 
                  (rename_matching m ys binds) D u ->
    eval_matching G L A (MWhere m binds) D u
.

Close Scope string_scope.

Scheme eval_expr_ind_mutual := Induction for eval_expr Sort Prop
with eval_matching_ind_mutual := Induction for eval_matching Sort Prop.

Combined Scheme eval_ind from eval_expr_ind_mutual, eval_matching_ind_mutual.

Lemma whnf_self_eval : forall G L e,
  whnf e -> eval_expr G L e G e.
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
      assert (D1 = D2 /\ w1 = w2) as [?HeqD ?Heqe] by (eapply expr_det; eauto);
      try discriminate; try congruence; subst
  end.

Ltac solve_determinism_match match_det :=
  match goal with
  | [ H1 : eval_matching ?G ?L ?A ?m ?D1 ?u1,
      H2 : eval_matching ?G ?L ?A ?m ?D2 ?u2 |- _ ] =>
      assert (D1 = D2 /\ u1 = u2) as [?HeqD ?Hequ] by (eapply match_det; eauto);
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
    + split; [ | trivial]. eapply eval_expr_deterministic; eauto.
    + solve_determinism_match eval_matching_deterministic.
    + solve_determinism_match eval_matching_deterministic.
    + solve_determinism_match eval_matching_deterministic. subst. auto.
Qed.
