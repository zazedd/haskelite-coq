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
Corollary big_step_impl_small_step :
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

Lemma self_nil : forall (A : Type) (x0 St : list A),
St = x0 ++ St -> x0 = [].
Proof.
  intros A x0 St H.
  symmetry in H.
  rewrite <- (app_nil_l St) in H.
  apply app_inv_tail in H.
  exact H.
Qed.

Theorem small_step_bal_impl_big_step_expr : forall c G e St c' D w,
  {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |} s=( St )=>*
  {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |} ->
  whnf w ->
  eval_expr c G (update_locs St) e D w c'.
Proof.
  intros c G e St c' D w Hsteps Hwhnf.
  remember {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |} as cfg_init.
  remember {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |} as cfg_final.
  revert c G e D w Heqcfg_init Heqcfg_final Hwhnf.
  induction Hsteps as [| c1 c2 ]; intros.
  - subst. injection Heqcfg_final as ? ? Hctrl. subst.
    constructor. assumption.

  - destruct c1 as [c1_cnt c1_heap c1_ctrl c1_stack].
    injection Heqcfg_init as Hc_eq Hheap_eq Hctrl_eq Hstack_eq. subst.
    destruct e as [x | e1 e2 | m | con args]; admit.
Admitted.

Theorem small_step_bal_impl_big_step_matching :
  forall c G A m St c' D u,
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |} s=( St )=>*
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch [] 
         (match u with MRReturn e => MReturn e | MRFail => MFail end);
       cfg_stack := St |} ->
    eval_matching c G (update_locs St) A m D u c'.
Proof.
  intros c G A m St c' D u Hsteps.
  remember {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |} as cfg_init.
  remember {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch []
                (match u with MRReturn e => MReturn e | MRFail => MFail end);
              cfg_stack := St |} as cfg_final.
  revert c G A m D u Heqcfg_init Heqcfg_final.
  induction Hsteps; intros; subst.
  - injection Heqcfg_final as ? ? Hctrl ?. subst.
    destruct u; constructor.

  - admit.
Admitted.

Theorem small_step_bal_to_big_step :
  (forall c G e St c' D w,
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |} s=( St )=>*
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |} ->
    whnf w ->
    eval_expr c G (update_locs St) e D w c')
  /\
  (forall c G A m St c' D u,
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |} s=( St )=>*
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch []
          (match u with MRReturn e => MReturn e | MRFail => MFail end);
        cfg_stack := St |} ->
    eval_matching c G (update_locs St) A m D u c').
Proof.
  split.
  - apply small_step_bal_impl_big_step_expr.
  - apply small_step_bal_impl_big_step_matching.
Qed.

Corollary small_step_to_big_step :
  (forall c G e c' D w,
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := [] |} s=>*
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := [] |} ->
    whnf w ->
    eval_expr c G [] e D w c')
  /\
  (forall c G A m c' D u,
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := [] |} s=>*
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch []
          (match u with MRReturn e => MReturn e | MRFail => MFail end);
        cfg_stack := [] |} ->
    eval_matching c G [] A m D u c').
Proof.
  split; intros;
  apply step_star_balanced_empty_to_empty in H; try reflexivity;
  apply small_step_bal_to_big_step in H; assumption.
Qed.
