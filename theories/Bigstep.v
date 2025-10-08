From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.

From Haskelite Require Import Expr.
Import ListNotations.

Module StringDec <: DecidableType.
  Definition t := string.
  Definition eq := @eq string.
  Definition eq_refl := @eq_refl string.
  Definition eq_sym := @eq_sym string.
  Definition eq_trans := @eq_trans string.
  Definition eq_dec := string_dec.
End StringDec.

Module StringMap := FMapWeakList.Make(StringDec).
Module StringMapFacts := FMapFacts.Facts(StringMap).

Definition heap := StringMap.t expr.
Definition empty_heap : heap := StringMap.empty expr.

(* Lookup and update operations *)
Definition heap_lookup (h : heap) (x : var) : option expr :=
  StringMap.find x h.

Definition heap_update (h : heap) (x : var) (e : expr) : heap :=
  StringMap.add x e h.

Definition heap_remove (h : heap) (x : var) : heap :=
  StringMap.remove x h.

(* type for L, provides freshness *)
Definition var_set := list var.

Definition in_var_set (x : var) (s : var_set) : bool :=
  existsb (String.eqb x) s.

(* renamings only *)
Fixpoint subst_expr (e : expr) (y : var) (x : var) : expr :=
  match e with
  | EVar z => if String.eqb z x then EVar y else EVar z
  | EApp e1 e2 => EApp (subst_expr e1 y x) (subst_expr e2 y x)
  | ELam m => ELam (subst_matching m y x)
| ECons c es => ECons c (map (fun e => subst_expr e y x) es)
  end

with subst_matching (m : matching) (y : var) (x : var) : matching :=
  match m with
  | MReturn e => MReturn (subst_expr e y x)
  | MFail => MFail
  | MMatch p m' => MMatch p (subst_matching m' y x)
  | MSupply e m' => MSupply (subst_expr e y x) (subst_matching m' y x)
  | MAlt m1 m2 => MAlt (subst_matching m1 y x) (subst_matching m2 y x)
  | MWhere m' b => MWhere (subst_matching m' y x) (subst_bindings b y x)
  end

with subst_bindings (b : bindings) (y : var) (x : var) : bindings :=
  match b with
  | Bindings bs => Bindings (map (fun p => (fst p, subst_expr (snd p) y x)) bs)
  end.

Fixpoint apply_args (args : list var) (e : expr) : expr :=
  match args with
  | [] => e
  | y :: ys => apply_args ys (EApp e (EVar y))
  end.

Fixpoint build_pattern_match (es : list expr) (ps : list pattern) (m : matching) : matching :=
  match es, ps with
  | [], [] => m
  | e :: es', p :: ps' => 
      match e with
      | EVar x => MSupply (EVar x) (MMatch p (build_pattern_match es' ps' m))
      | _ => MFail  (* should not happen in normalized form *)
      end
  | _, _ => MFail
  end.

(* build y1 |> p1 => ... =>  yn |> pn =>  m *)
Fixpoint build_nested_matches (vars : list var) (pats : list pattern) (m : matching) : matching :=
  match vars, pats with
  | [], [] => m
  | v :: vs, p :: ps => MSupply (EVar v) (MMatch p (build_nested_matches vs ps m))
  | _, _ => MFail
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

  (*| EvalWhere : forall G L A m binds D u ys renamed_binds renamed_m,*)
  (*    length ys = length binds ->*)
  (*    (* ys are fresh w.r.t. G, L, A, m, and bindings *)*)
  (*    (forall y, In y ys -> ~In y L /\ heap_lookup G y = None) ->*)
  (*    (* perform renaming *)*)
  (*    renamed_binds = rename_bindings binds ys ->*)
  (*    renamed_m = rename_matching m ys binds ->*)
  (*    (* allocate renamed bindings in heap *)*)
  (*    eval_matching (allocate_bindings G renamed_binds) L A renamed_m D u ->*)
  (*    eval_matching G L A (MWhere m (Bindings binds)) D u*)
.

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

Lemma map_injective : forall {A B : Type} (f : A -> B) (l1 l2 : list A),
  (forall x y, f x = f y -> x = y) ->
  map f l1 = map f l2 ->
  l1 = l2.
Proof.
  intros A B f l1.
  induction l1; intros l2 Hinj Hmap.
  - destruct l2; auto. discriminate.
  - destruct l2.
    + discriminate.
    + simpl in Hmap. injection Hmap as Hhead Htail.
      f_equal.
      * apply Hinj. assumption.
      * apply IHl1; assumption.
Qed.

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
    + inversion H; subst.
      rewrite H0 in H5. discriminate.
    + inversion H.
    + inversion H.
    + inversion H3. subst.
      rewrite H5 in H.
      discriminate.
    + assert (D = D0 /\ MRReturn e = MRReturn e0) as [HeqD Heqe]. {
        eapply eval_matching_deterministic; eauto.
      }
      inversion Heqe; subst.
      eapply IHeval_expr; eauto.
    + inversion H3.
    + assert (e = e0) as Heqe. {
        eapply heap_lookup_deterministic; eauto.
      }
      subst.
      assert (D = D0 /\ w = w2) as [Heq1 Heq2]. {
        eapply eval_expr_deterministic; eauto.
      }
      subst. auto.
    + inversion H0.
    + inversion H6; subst.
      assert (D = D0 /\ ELam m = ELam m0) as [HeqD Heqm]. {
        eapply eval_expr_deterministic; eauto.
      }
      inversion Heqm; subst.
      apply IHeval_expr2. assumption.
  - intros G L A m D1 u1 D2 u2 H1 H2.
    induction H1; inversion H2; subst; try congruence; try auto.
    + assert (D = D0 /\ ECons c (map EVar args) = ECons c (map EVar args0)) as [HeqD Hcons]. {
        eapply eval_expr_deterministic; eauto.
      }
      injection Hcons as Heqargs.
      apply map_injective in Heqargs; subst.
      * apply IHeval_matching.
        assumption.
      * intros x1 x2 Heq.
        injection Heq. trivial.
    + assert (D = D2 /\ ECons c (map EVar args) = ECons c' args0) as [HeqD Hcons]. {
        eapply eval_expr_deterministic; eauto.
      }
      injection Hcons as Heqc _.
      congruence.
    + assert (D = D0 /\ ECons c' args = ECons c (map EVar args0)) as [HeqD Hcons]. {
        eapply eval_expr_deterministic; eauto.
      }
      injection Hcons as Heqc _.
      congruence.
    + split; [ | trivial].
      admit.
Admitted.



