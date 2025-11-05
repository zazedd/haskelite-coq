From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common Bigstep Smallstep.
Import ListNotations.

Section FreshGen.
Context {FG : FreshVarGen}.

Lemma whnf_lambda_arity : forall m,
  whnf (ELam m) ->
  exists n, matching_arity m = Some (S n).
Proof.
  intros m H.
  inversion H; subst.
  exists n. assumption.
Qed.

Lemma eval_expr_lambda_arity : forall G L e D m,
  eval_expr G L e D (ELam m) ->
  exists n, matching_arity m = Some (S n).
Proof.
  intros G L e D m Hexpr.
  apply whnf_lambda_arity.
  eapply eval_expr_produces_whnf.
  eassumption.
Qed.

Theorem bigstep_impl_balancedstep :
  (forall G L e D w,
    eval_expr G L e D w ->
    forall St,
               L = (update_locs St) ->
               balanced_step_expr
               {| cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |}
               {| cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |})
  /\
  (forall G L A m D u,
    eval_matching G L A m D u ->
    forall St,
               L = (update_locs St) ->
               balanced_step_matching
               {| cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |}
               {| cfg_heap := D; cfg_ctrl := CtrlMatch []
                                  (match u with MRReturn e => MReturn e | MRFail => MFail end);
                  cfg_stack := St |}).
Proof.
  apply eval_ind.
  - (* EvalWhnf *)
    intros G L w Hwhnf St HL.
    apply BExprWhnf. assumption.

  - (* EvalSat *)
    intros G L m e D O w Harity Hmatch IHmatch Heval IHeval St HL.
    eapply BExprSat.
    + exact Harity.
    + apply StepSat. exact Harity.
    + apply IHmatch. simpl. exact HL.
    + apply StepReturn1B.
    + apply IHeval. assumption.

  - (* EvalVar *)
    intros G L y e D w Hheap Hnotin Heval IHexpr St HL.
    eapply BExprVar.
    + exact Hheap.
    + subst L. exact Hnotin.
    + apply StepVar. exact Hheap.
    + apply IHexpr. simpl. subst L. reflexivity.
    + apply StepUpdate. eapply eval_expr_produces_whnf. eassumption.

  - (* EvalApp *)
    intros G L e1 e2 m D O w x Hexpr1 IHexpr1 Hvar Hexpr2 IHexpr2 St HL.
    subst e2.
    destruct (eval_expr_lambda_arity _ _ _ _ _ Hexpr1) as [n Harity].
    eapply BExprApp.
    + apply StepApp1.
    + apply IHexpr1. simpl. exact HL.
    + econstructor. exact Harity.
    + apply IHexpr2. exact HL.

  - (* EvalBop *)
    intros G L op e1 e2 n1 n2 n D1 D2 Hexpr1 IHexpr1 Hexpr2 IHexpr2 Hbop St HL.
    eapply BExprBop; try constructor; try eassumption; eauto.

  - (* EvalReturn *)
    intros G L A e St HL.
    destruct A as [| y A'].
    + simpl. apply BMatchReturn.
    + eapply BMatchReturnArgs.
      * discriminate.
      * apply StepReturn1A. discriminate.
      * apply BMatchReturn.

  - (* EvalMatchFail *)
    intros G L St HL.
    constructor.

  - (* EvalArg *)
    intros G L A x m D u Hmatch IHmatch St HL.
    eapply BMatchArg.
    + constructor.
    + apply IHmatch. exact HL.

  - (* EvalBindVar *)
    intros G L A x y m D u Hmatch IHmatch St HL.
    eapply BMatchBind.
    + constructor.
    + apply IHmatch. exact HL.

  - (* EvalNatMatch *)
    intros G L A x n m D1 D2 u Hexpr IHexpr Hmatching IHmatching St HL.
    eapply BMatchNatSuccess.
    + constructor.
    + eapply IHexpr. simpl. exact HL.
    + constructor.
    + eapply IHmatching. exact HL.

  - (* EvalNatFail *)
    intros G L A x n1 n2 m D Hexpr IHexpr Hneq St HL.
    eapply BMatchNatFail.
    + eassumption.
    + constructor.
    + apply IHexpr. simpl. exact HL.
    + constructor. assumption.

  - (* EvalConsMatch *)
    intros G L A x con ps m args D O u Hexpr IHexpr Hlen Hmatching IHmatching St HL.
    eapply BMatchConsSuccess.
    + constructor.
    + apply IHexpr. simpl. exact HL.
    + assumption.
    + constructor. symmetry. assumption.
    + apply IHmatching. assumption.

  - (* EvalConsFail *)
    intros G L A x con con' ps m args D Hexpr IHexpr Hneq St HL.
    eapply BMatchConsFail.
    + exact Hneq.
    + apply StepCons1.
    + apply IHexpr. simpl. exact HL.
    + apply StepFail. exact Hneq.

  - (* EvalAltLeft *)
    intros G L A m1 m2 e D Hmatch IHmatch St HL.
    apply BMatchAltLeft.
    + constructor.
    + apply IHmatch. simpl. exact HL.
    + constructor.

  - (* EvalAltRight *)
    intros G L A m1 m2 D O u Hmatch1 IHmatch1 Hmatch2 IHmatch2 St HL.
    eapply BMatchAltRight.
    + constructor.
    + apply IHmatch1. simpl. exact HL.
    + constructor.
    + apply IHmatch2. exact HL.

  - (* EvalWhere *)
    intros G L A m binds D u ys renamed_binds renamed_m Hys Hbinds Hm Hmatch IHmatch St HL.
    eapply BMatchWhere; try eassumption.
    + subst L. assumption.
    + econstructor; try eassumption. subst L. assumption.
    + apply IHmatch. assumption.
Qed.

Corollary initial_bigstep_impl_balancedstep :
  (forall e D w,
    eval_expr empty_heap [] e D w ->
    balanced_step_expr
      {| cfg_heap := empty_heap; cfg_ctrl := CtrlExpr e; cfg_stack := [] |}
      {| cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := [] |})
  /\
  (forall A D m u,
    eval_matching empty_heap [] A m D u ->
    balanced_step_matching
    {| cfg_heap := empty_heap; cfg_ctrl := CtrlMatch A m; cfg_stack := [] |}
    {| cfg_heap := D; cfg_ctrl := CtrlMatch []
                      (match u with MRReturn e => MReturn e | MRFail => MFail end);
      cfg_stack := [] |})
.
Proof.
  split.
  - intros. apply (proj1 bigstep_impl_balancedstep) with (L := []); auto.
  - intros. apply (proj2 bigstep_impl_balancedstep) with (L := []); auto.
Qed.

Theorem bigstep_impl_smallstep_star :
  (forall G L e D w St,
    eval_expr G L e D w ->
    L = update_locs St ->
    {| cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |} s=>*
    {| cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |})
  /\
  (forall G L A m D u St,
    eval_matching G L A m D u ->
    L = update_locs St ->
    {| cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |} s=>*
    {| cfg_heap := D;
       cfg_ctrl := CtrlMatch [] (match u with MRReturn e => MReturn e | MRFail => MFail end);
       cfg_stack := St |})
.
Proof.
  split.
  - intros G L e D w St Hexpr HL.
    apply balanced_expr_to_steps.
    apply (proj1 bigstep_impl_balancedstep) with (L := L); auto.
  - intros G L A m D u St Hmatching HL.
    apply balanced_matching_to_steps.
    apply (proj2 bigstep_impl_balancedstep) with (L := L); auto.
Qed.

Corollary initial_bigstep_impl_smallstep :
  (forall e D w,
    eval_expr empty_heap [] e D w ->
    {| cfg_heap := empty_heap; cfg_ctrl := CtrlExpr e; cfg_stack := [] |} s=>*
    {| cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := [] |})
  /\
  (forall A D m u,
    eval_matching empty_heap [] A m D u ->
    {| cfg_heap := empty_heap; cfg_ctrl := CtrlMatch A m; cfg_stack := [] |} s=>*
    {| cfg_heap := D; cfg_ctrl := CtrlMatch []
                      (match u with MRReturn e => MReturn e | MRFail => MFail end);
      cfg_stack := [] |})
.
Proof.
  split.
  - intros e D w Hexpr.
    apply bigstep_impl_smallstep_star with (L := []). assumption. reflexivity.
  - intros A D m u Hmatching.
    apply bigstep_impl_smallstep_star with (L := []). assumption. reflexivity.
Qed.

End FreshGen.
