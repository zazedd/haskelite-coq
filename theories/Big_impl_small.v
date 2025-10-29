From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common Bigstep Smallstep.
Import ListNotations.

Lemma whnf_lambda_arity : forall m,
  whnf (ELam m) ->
  exists n, matching_arity m = Some (S n).
Proof.
  intros m H.
  inversion H; subst.
  exists n. assumption.
Qed.

Lemma eval_expr_lambda_arity : forall c G L e D m c',
  eval_expr c G L e D (ELam m) c' ->
  exists n, matching_arity m = Some (S n).
Proof.
  intros c G L e D m c' H.
  apply whnf_lambda_arity.
  eapply eval_expr_produces_whnf.
  eassumption.
Qed.

(* theorem 4.1 *)
Theorem big_step_impl_small_step :
  (forall c G L e D w c',
    eval_expr c G L e D w c' ->
    forall St, {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |} s=>*
               {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |})
  /\
  (forall c G L A m D u c',
    eval_matching c G L A m D u c' ->
    forall St, {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |} s=>*
               {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch []
                                  (match u with MRReturn e => MReturn e | MRFail => MFail end);
                  cfg_stack := St |}).
Proof.
  apply eval_ind.
  - intros c G L w Hwhnf St.
    constructor.
  - intros c c1 c2 G L m e D O w Harity Hmatch IHmatch Heval IHeval St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepSat. eassumption.
      * apply step_refl.
    + eapply step_star_trans.
      * apply IHmatch.
      * eapply step_star_trans.
        ** eapply step_trans.
           -- apply StepReturn1B.
           -- apply step_refl.
        ** apply IHeval.

  - intros c c1 G L y e D w Hheap Hin Heval IHexpr St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepVar. eassumption.
      * apply step_refl.
    + eapply step_star_trans.
      * apply IHexpr.
      * eapply step_trans.
        ** apply StepUpdate. eapply eval_expr_produces_whnf. eassumption.
        ** apply step_refl.

  - intros c c1 c2 G L e1 e2 m D O w x Hexpr1 IHexpr Hvar Hexpr2 IHexpr2 St.
    subst e2.
    destruct (eval_expr_lambda_arity _ _ _ _ _ _ _ Hexpr1) as [n Harity].
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepApp1.
      * apply step_refl.
    + eapply step_star_trans.
      * apply IHexpr.
      * eapply step_star_trans.
        ** eapply step_trans.
           ++ eapply StepApp2. eassumption.
           ++ apply step_refl.
        ** apply IHexpr2.

  - intros c G L A e St.
    destruct A as [| y A'].
    + simpl. apply step_refl.
    + eapply step_star_trans.
      * eapply step_trans.
        ** apply StepReturn1A. discriminate.
        ** apply step_refl.
      * apply step_refl.

  - intros c G L St. apply step_refl.

  - intros c c' G L A x m D u _ IHmatch St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepArg.
      * apply step_refl.
    + apply IHmatch.

  - intros c c' G L A x y m D u _ IHmatch St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepBind.
      * apply step_refl.
    + apply IHmatch.

  - intros c c1 c2 G L A x con ps m args D O u Hexpr IHexpr Hlen Hmatching IHmatching St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepCons1.
      * apply step_refl.
    + eapply step_star_trans.
      * apply IHexpr.
      * eapply step_star_trans.
        ** eapply step_trans.
           ++ apply StepCons2. symmetry. assumption.
           ++ apply step_refl.
        ** apply IHmatching.

  - intros c c' G L A x con con' ps m args D Hexpr IHexpr Heqc St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepCons1.
      * apply step_refl.
    + eapply step_star_trans.
      * apply IHexpr.
      * eapply step_trans.
        ** apply StepFail. assumption.
        ** apply step_refl.

  - intros c c' G L A m1 m2 e D Hmatching IHmatch St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepAlt1.
      * apply step_refl.
    + eapply step_star_trans.
      * apply IHmatch.
      * eapply step_trans.
        ** apply StepReturn2.
        ** apply step_refl.

  - intros c c1 c2 G L A m1 m2 D O u Hmatching1 IHmatch1 Hmatching2 IHmatch2 St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepAlt1.
      * apply step_refl.
    + eapply step_star_trans.
      * apply IHmatch1.
      * eapply step_star_trans.
        ** constructor.
        ** eapply step_trans.
           ++ constructor.
           ++  apply IHmatch2.

  - intros c G L A m binds D u ys renamed_binds renamed_m Hys Hbinds Hm Hmatching IHmatch St.
    eapply step_star_trans.
    + constructor.
    + eapply step_trans.
      * apply StepWhere with (ys := ys); eassumption.
      * apply IHmatch.
Qed.

Theorem big_step_impl_balanced_step :
  (forall c G L e D w c',
    eval_expr c G L e D w c' ->
    forall St,
               L = (update_locs St) ->
               balanced_step_expr
               {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |}
               {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |})
  /\
  (forall c G L A m D u c',
    eval_matching c G L A m D u c' ->
    forall St,
               L = (update_locs St) ->
               balanced_step_matching
               {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |}
               {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch []
                                  (match u with MRReturn e => MReturn e | MRFail => MFail end);
                  cfg_stack := St |}).
Proof.
  apply eval_ind.
  - intros c G L w Hwhnf St HL.
    apply BExprWhnf. assumption.

  - intros c c1 c2 G L m e D O w Harity Hmatch IHmatch Heval IHeval St HL.
    eapply BExprSat.
    + exact Harity.
    + apply StepSat. exact Harity.
    + apply IHmatch. simpl. exact HL.
    + apply StepReturn1B.
    + apply IHeval. assumption.

  - intros c c1 G L y e D w Hheap Hnotin Heval IHexpr St HL.
    eapply BExprVar.
    + exact Hheap.
    + subst L. exact Hnotin.
    + apply StepVar. exact Hheap.
    + apply IHexpr. simpl. subst L. reflexivity.
    + apply StepUpdate. eapply eval_expr_produces_whnf. eassumption.

  - intros c c1 c2 G L e1 e2 m D O w x Hexpr1 IHexpr1 Hvar Hexpr2 IHexpr2 St HL.
    subst e2.
    destruct (eval_expr_lambda_arity _ _ _ _ _ _ _ Hexpr1) as [n Harity].
    eapply BExprApp.
    + apply StepApp1.
    + apply IHexpr1. simpl. exact HL.
    + econstructor. exact Harity.
    + apply IHexpr2. exact HL.

  - (* BMatchReturn *)
    intros c G L A e St HL.
    destruct A as [| y A'].
    + simpl. apply BMatchReturn.
    + eapply BMatchReturnArgs.
      * discriminate.
      * apply StepReturn1A. discriminate.
      * apply BMatchReturn.

  - (* BMatchFail *)
    intros c G L St HL.
    constructor.

  - (* BMatchArg *)
    intros c c' G L A x m D u Hmatch IHmatch St HL.
    eapply BMatchArg.
    + constructor.
    + apply IHmatch. exact HL.

  - (* BMatchBind *)
    intros c c' G L A x y m D u Hmatch IHmatch St HL.
    eapply BMatchBind.
    + constructor.
    + apply IHmatch. exact HL.

  - (* BMatchConsSuccess *)
    intros c c1 c2 G L A x con ps m args D O u Hexpr IHexpr Hlen Hmatching IHmatching St HL.
    eapply BMatchConsSuccess.
    + constructor.
    + apply IHexpr. simpl. exact HL.
    + assumption.
    + constructor. symmetry. assumption.
    + apply IHmatching. assumption.

  - (* BMatchConsFail *)
    intros c c' G L A x con con' ps m args D Hexpr IHexpr Hneq St HL.
    eapply BMatchConsFail.
    + exact Hneq.
    + apply StepCons1.
    + apply IHexpr. simpl. exact HL.
    + apply StepFail. exact Hneq.

  - (* BMatchAltLeft *)
    intros c c' G L A m1 m2 e D Hmatch IHmatch St HL.
    apply BMatchAltLeft.
    + constructor.
    + apply IHmatch. simpl. exact HL.
    + constructor.

  - (* BMatchAltRight *)
    intros c c1 c2 G L A m1 m2 D O u Hmatch1 IHmatch1 Hmatch2 IHmatch2 St HL.
    eapply BMatchAltRight.
    + constructor.
    + apply IHmatch1. simpl. exact HL.
    + constructor.
    + apply IHmatch2. exact HL.

  - (* BMatchWhere *)
    intros c G L A m binds D u ys renamed_binds renamed_m Hys Hbinds Hm Hmatch IHmatch St HL.
    eapply BMatchWhere; try eassumption.
    + econstructor; eassumption.
    + apply IHmatch. exact HL.
Qed.

Corollary initial_big_step_implies_balanced_step :
  (forall e D w c',
    eval_expr 0 empty_heap [] e D w c' ->
    balanced_step_expr
      {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlExpr e; cfg_stack := [] |}
      {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := [] |})
  /\
  (forall A D m u c',
    eval_matching 0 empty_heap [] A m D u c' ->
    balanced_step_matching
    {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlMatch A m; cfg_stack := [] |}
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch []
                      (match u with MRReturn e => MReturn e | MRFail => MFail end);
      cfg_stack := [] |})
.
Proof.
  split.
  - intros. apply (proj1 big_step_impl_balanced_step) with (L := []); auto.
  - intros. apply (proj2 big_step_impl_balanced_step) with (L := []); auto.
Qed.

Theorem big_step_impl_small_step' :
  (forall c G L e D w c',
    eval_expr c G L e D w c' ->
    forall St, (L = update_locs St) ->
               {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |} s=>*
               {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |})
  /\
  (forall c G L A m D u c',
    eval_matching c G L A m D u c' ->
    forall St, (L = update_locs St) ->
               {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |} s=>*
               {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch []
                                  (match u with MRReturn e => MReturn e | MRFail => MFail end);
                  cfg_stack := St |}).
Proof.
  split.
  - intros. apply balanced_expr_to_steps. apply (proj1 big_step_impl_balanced_step) with (L := L); assumption.
  - intros. apply balanced_matching_to_steps. apply (proj2 big_step_impl_balanced_step) with (L := L); assumption.
Qed.

Corollary initial_big_step_implies_small_step :
  (forall e D w c',
    eval_expr 0 empty_heap [] e D w c' ->
    {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlExpr e; cfg_stack := [] |} s=>*
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := [] |})
  /\
  (forall A D m u c',
    eval_matching 0 empty_heap [] A m D u c' ->
    {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlMatch A m; cfg_stack := [] |} s=>*
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch []
                      (match u with MRReturn e => MReturn e | MRFail => MFail end);
      cfg_stack := [] |})
.
Proof.
  split.
  - intros. apply (proj1 big_step_impl_small_step') with (L := []); auto.
  - intros. apply (proj2 big_step_impl_small_step') with (L := []); auto.
Qed.
