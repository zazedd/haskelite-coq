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


Theorem small_step_big_step_expr : forall c0 c1 G D e w St,
  {| c := c0; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |} s=>*
  {| c := c1; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |} ->
  whnf w ->
  eval_expr c0 G (update_locs St) e D w c1
with small_step_big_step_matching : forall c0 c1 G D A m u e St,
  {| c := c0; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |} s=>*
  {| c := c1; cfg_heap := D; cfg_ctrl := CtrlMatch [] 
    (match u with MRReturn e => MReturn e | MRFail => MFail end); 
    cfg_stack := St |} ->
  eval_matching c0 G (update_locs St) A m D e c1.
Proof.
  - intros count0 count1 G D e w St Hsteps Hwhnf.
    remember {| c := count0; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |} as cfg_start.
    remember {| c := count1; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |} as cfg_end.
    generalize dependent w.
    generalize dependent e.
    generalize dependent D.
    generalize dependent G.
    generalize dependent count1.
    generalize dependent count0.
    generalize dependent St.
    induction Hsteps; intros; subst.
    + inversion Heqcfg_end; subst. constructor. assumption.
    + apply (IHHsteps St count0 count1 G D e).
      * admit.
      * constructor.
      * assumption.

  - intros count0 count1 G D A m u e St Hsteps.
    remember {| c := count0; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |} as cfg_start.
    remember {| c := count1; cfg_heap := D; cfg_ctrl := 
      CtrlMatch [] (match u with MRReturn e => MReturn e | MRFail => MFail end); 
      cfg_stack := St |} as cfg_end.
    generalize dependent u.
    generalize dependent m.
    generalize dependent A.
    generalize dependent D.
    generalize dependent G.
    generalize dependent count1.
    generalize dependent count0.
    generalize dependent St.
    induction Hsteps; intros; subst.
    + inversion Heqcfg_end; subst. admit.
    + admit.
Admitted.

