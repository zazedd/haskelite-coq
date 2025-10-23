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

Lemma cons_self_contra {A} (x : A) (xs : list A) :
  x :: xs <> xs.
Proof.
  induction xs as [| y ys IH].
  - discriminate.
  - intros H. injection H as H1 H2. subst. auto.
Qed.

Ltac list_contradiction :=
  match goal with
  | H : ?L <> ?L |- _ => contradiction
  | H : _ :: ?L = ?L |- _ => apply cons_self_contra in H; contradiction
  | H : ?L = _ :: ?L |- _ => symmetry in H; apply cons_self_contra in H; contradiction
  end.

Lemma balanced_step_to_bigstep_expr : forall c G e D w St c',
  balanced_step_expr
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |}
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |} ->
  whnf w ->
  eval_expr c G (update_locs St) e D w c'

with balanced_step_to_bigstep_matching : forall c G A m D u St c',
  balanced_step_matching
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |}
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch A u; cfg_stack := St |} ->
  matching_final u ->
  match u with
  | MReturn e => eval_matching c G (update_locs St) A m D (MRReturn e) c'
  | MFail => A = [] /\ eval_matching c G (update_locs St) A m D MRFail c'
  | _ => False
  end.
Proof.
  - intros c G e D w St c' Hbal Hwhnf.
    inversion Hbal; subst.
    + constructor. assumption.
    + (* BExprApp *)
      assert (Heval1 : eval_expr c G (update_locs (KArg y :: St)) e0 D0 (ELam m) c1). {
        apply balanced_step_to_bigstep_expr with (St := KArg y :: St) (c' := c1).
        - auto.
        - admit.
      }

      assert (Heval2 : eval_expr c1 D0 (update_locs St) (ELam (MSupply (EVar y) m)) D w c').
      { apply balanced_step_to_bigstep_expr with (St := St) (c' := c'); assumption. }

      simpl in Heval1.
      eapply EvalApp; eauto.

    + (* BExprVar *)
      assert (Heval : eval_expr c (heap_remove G y) (update_locs (KUpdate y :: St)) e0 D0 w c').
      { apply balanced_step_to_bigstep_expr with (St := KUpdate y :: St) (c' := c'); auto. }

      simpl in Heval. rewrite <- update_locs_KUpdate in Heval.
      eapply EvalVar; eauto.
      (* missing blakholing invariant *)
      admit.

    + (* BExprSat *)
      assert (Hmatch : eval_matching c G (update_locs (KEnd :: St)) [] m D0 (MRReturn e0) c1). { 
        assert (Hmatch' := balanced_step_to_bigstep_matching c G [] m D0 (MReturn e0) (KEnd :: St) c1 H8).
        simpl in Hmatch'. apply Hmatch'. apply MFinal_Return. 
      }

      assert (Heval : eval_expr c1 D0 (update_locs St) e0 D w c'). {
        apply balanced_step_to_bigstep_expr with (St := St) (c' := c').
        - auto.
        - assumption.
      }

      eapply EvalSat; eauto.

  - intros c G A m D u St c' Hbal Hfinal.
    destruct u; try (exfalso; inversion Hfinal; fail).
    + (* MReturn *)
      inversion Hbal; subst; try discriminate; try list_contradiction.
      * constructor.
      * assert (Heval : eval_matching c G (update_locs (KAlt [] m2 :: St)) [] m1 D (MRReturn e) c').
        { apply (balanced_step_to_bigstep_matching c G [] m1 D (MReturn e) (KAlt [] m2 :: St) c'); auto. }

        simpl in Heval.
        eapply EvalAltLeft. exact Heval.
      * admit.

      * set (renamed_binds := rename_bindings binds (gen_n_fresh c (Datatypes.length binds))).
        set (renamed_m := rename_matching m0 (gen_n_fresh c (Datatypes.length binds)) binds).
        assert (Heval :
          eval_matching (c + length binds) (allocate_bindings G renamed_binds) (update_locs St) A renamed_m 
          D (MRReturn e) (c + length binds)).
        {
          apply (balanced_step_to_bigstep_matching (c + length binds) (allocate_bindings G renamed_binds) A renamed_m
                 D (MReturn e) St (c + length binds)); auto.
        }

        eapply EvalWhere; eauto.

    + (* MFail *)
      inversion Hbal; subst; try discriminate; try list_contradiction.
      * admit.
      * admit.
Admitted.


Theorem small_step_impl_bigstep_expr : forall e D w c',
  initial_config e s=>* {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := [] |} ->
  whnf w ->
  eval_expr 0 empty_heap (update_locs []) e D w c'

with small_step_impl_bigstep_matching : forall A m D u c',
  {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlMatch A m; cfg_stack := [] |} s=>* 
  {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch A u; cfg_stack := [] |} ->
  matching_final u ->
  match u with
  | MReturn e => eval_matching 0 empty_heap (update_locs []) A m D (MRReturn e) c'
  | MFail => A = [] /\ eval_matching 0 empty_heap (update_locs []) A m D MRFail c'
  | _ => False
  end.
Proof.
  - intros e D w c' Hsteps Hwhnf.
    apply balanced_step_to_bigstep_expr.
    + unfold initial_config in Hsteps. apply steps_to_balanced_expr in Hsteps. assumption.
    + assumption.

  - intros A m D u c' Hsteps Hu.
    apply balanced_step_to_bigstep_matching.
    + unfold initial_config in Hsteps. apply steps_to_balanced_matching in Hsteps. assumption.
    + assumption.
Qed.



