From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common Bigstep Smallstep.
Import ListNotations.

Lemma eval_expr_produces_whnf : forall G L e D w,
  eval_expr G L e D w -> whnf w.
Proof.
  intros. induction H; assumption.
Qed.

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
  intros G L e D m H.
  apply whnf_lambda_arity.
  eapply eval_expr_produces_whnf.
  eassumption.
Qed.

(* theorem 4.1 *)
Theorem big_step_impl_small_step :
  (forall G L e D w,
    eval_expr G L e D w ->
    forall St, {| cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |} s=>*
               {| cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |})
  /\
  (forall G L A m D u,
    eval_matching G L A m D u ->
    forall St, {| cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |} s=>*
               {| cfg_heap := D; cfg_ctrl := CtrlMatch []
                                  (match u with MRReturn e => MReturn e | MRFail => MFail end); 
                  cfg_stack := St |}).
Proof.
  apply eval_ind.
  - intros G L w Hwhnf St.
    constructor.
  - intros G L m e D O w Harity Hmatch IHmatch Heval IHeval St.
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

  - intros G L y e D w Hheap Hin Heval IHexpr St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepVar. eassumption.
      * apply step_refl.
    + eapply step_star_trans.
      * apply IHexpr.
      * eapply step_trans.
        ** apply StepUpdate. eapply eval_expr_produces_whnf. eassumption.
        ** apply step_refl.

  - intros G L e1 e2 m D O w x Hexpr1 IHexpr Hvar Hexpr2 IHexpr2 St.
    subst e2.
    destruct (eval_expr_lambda_arity _ _ _ _ _ Hexpr1) as [n Harity].
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

  - intros G L A e St.
    destruct A as [| y A'].
    + simpl. apply step_refl.
    + eapply step_star_trans.
      * eapply step_trans.
        ** apply StepReturn1A. discriminate.
        ** apply step_refl.
      * apply step_refl.

  - intros G L st. apply step_refl.

  - intros G L A x m D u _ IHmatch St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepArg.
      * apply step_refl.
    + apply IHmatch.

  - intros G L A x y m D u _ IHmatch St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepBind.
      * apply step_refl.
    + apply IHmatch.

  - intros G L A x c ps m args D O u Hexpr IHexpr Hlen Hmatching IHmatching St.
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

  - intros G L A x c c' ps m args D Hexpr IHexpr Heqc St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepCons1.
      * apply step_refl.
    + eapply step_star_trans.
      * apply IHexpr.
      * eapply step_trans.
        ** apply StepFail. assumption.
        ** apply step_refl.

  - intros G L A m1 m2 e D Hmatching IHmatch St.
    eapply step_star_trans.
    + eapply step_trans.
      * apply StepAlt1.
      * apply step_refl.
    + eapply step_star_trans.
      * apply IHmatch.
      * eapply step_trans.
        ** apply StepReturn2.
        ** apply step_refl.

  - intros G L A m1 m2 D O u Hmatching1 IHmatch1 Hmatching2 IHmatch2 St.
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

  - intros G L A m binds D u avoid ys Hmatching IHmatch St.
    eapply step_star_trans.
    + constructor.
    + eapply step_trans.
      * constructor.
      * admit. (* need better alternative, maybe add an alpha equivalence relation and prove to aeq? *)
Admitted.

