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

Lemma balanced_step_to_bigstep_expr' : forall c G e D w St c',
  balanced_step_expr
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |}
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |} ->
  whnf w ->
  eval_expr c G (update_locs St) e D w c'

with balanced_step_to_bigstep_matching' : forall c G A m D A' u St c',
  balanced_step_matching
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |}
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |} ->
  matching_final u ->
  match u with
  | MReturn e => eval_matching c G (update_locs St) A m D (MRReturn e) c'
  | MFail => A' = [] /\ eval_matching c G (update_locs St) A m D MRFail c'
  | _ => False
  end.
Proof.
  - intros c G e D w St c' Hbal Hwhnf.
    inversion Hbal; subst.
    + constructor. assumption.
    + (* BExprApp *)
      assert (Heval1 : eval_expr c G (update_locs (KArg y :: St)) e0 D0 (ELam m) c1). {
        apply balanced_step_to_bigstep_expr' with (St := KArg y :: St) (c' := c1).
        - auto.
        - inversion H8; subst.
          apply whnf_lambda with n. assumption.
      }

      assert (Heval2 : eval_expr c1 D0 (update_locs St) (ELam (MSupply (EVar y) m)) D w c').
      { apply balanced_step_to_bigstep_expr' with (St := St) (c' := c'); assumption. }

      simpl in Heval1.
      eapply EvalApp; eauto.

    + (* BExprVar *)
      assert (Heval : eval_expr c (heap_remove G y) (update_locs (KUpdate y :: St)) e0 D0 w c').
      { apply balanced_step_to_bigstep_expr' with (St := KUpdate y :: St) (c' := c'); auto. }

      simpl in Heval. rewrite <- update_locs_KUpdate in Heval.
      eapply EvalVar; eauto.

    + (* BExprSat *)
      assert (Hmatch : eval_matching c G (update_locs (KEnd :: St)) [] m D0 (MRReturn e0) c1). { 
        assert (Hmatch' := balanced_step_to_bigstep_matching' c G [] m D0 [] (MReturn e0) (KEnd :: St) c1 H8).
        simpl in Hmatch'. apply Hmatch'. apply MFinal_Return. 
      }

      assert (Heval : eval_expr c1 D0 (update_locs St) e0 D w c'). {
        apply balanced_step_to_bigstep_expr' with (St := St) (c' := c').
        - auto.
        - assumption.
      }

      eapply EvalSat; eauto.

  - intros c G A m D A' u St c' Hbal Hfinal.
    destruct u; try (exfalso; inversion Hfinal; fail).
    + (* MReturn *)
      inversion Hbal; subst; try discriminate.
      * constructor.
      * (* BMatchReturnArgs *)
        inversion H10; subst.
        -- apply EvalReturn.
        -- exfalso. list_contradiction.

      * (* BMatchArg *)
        assert (Heval : eval_matching c G (update_locs St) (y :: A) m0 D (MRReturn e) c').
        { apply balanced_step_to_bigstep_matching' with (A' := y :: A) (u := MReturn e); auto. }
        eapply EvalArg. eauto.

      * (* BMatchBind *)
        assert (Heval : eval_matching c G (update_locs St) A' (subst_matching m0 y x) D (MRReturn e) c').
        { apply balanced_step_to_bigstep_matching' with (A' := A') (u := MReturn e); auto. }
        eapply EvalBindVar. eauto.

      * (* BMatchConsSuccess *)
        assert (Heval_expr : eval_expr c G (update_locs (KPat A' cp ps m0 :: St)) (EVar x) D0 (ECons cp (map EVar args)) c1).
        { apply balanced_step_to_bigstep_expr'; auto. constructor. }

        assert (Heval_match : eval_matching c1 D0 (update_locs St) A' (build_nested_matches args ps m0) D (MRReturn e) c').
        { apply balanced_step_to_bigstep_matching' with (A' := A') (u := MReturn e); auto. }

        eapply EvalConsMatch; eauto.

      * (* BMatchAltLeft *)
        assert (Heval : eval_matching c G (update_locs (KAlt A m2 :: St)) A m1 D (MRReturn e) c').
        { apply balanced_step_to_bigstep_matching' with (A' := []) (u := MReturn e); auto. }
        simpl in Heval.
        eapply EvalAltLeft. eassumption.

      * (* BMatchAltRight *)
        assert (Hm1 := balanced_step_to_bigstep_matching' _ _ _ _ _ _ _ _ _ H9 MFinal_Fail).
        destruct Hm1 as [_ Hm1].

        assert (Hm2: eval_matching c1 D0 (update_locs St) A' m2 D (MRReturn e) c').
        { apply balanced_step_to_bigstep_matching' with (A' := A') (u := MReturn e); auto. }

        eapply EvalAltRight; eauto.

      * (* BMatchWhere *)
        set (renamed_binds := rename_bindings binds (gen_n_fresh c (Datatypes.length binds))).
        set (renamed_m := rename_matching m0 (gen_n_fresh c (Datatypes.length binds)) binds).
        assert (Heval :
          eval_matching (c + length binds) (allocate_bindings G renamed_binds) (update_locs St) A' renamed_m
          D (MRReturn e) (c + length binds)).
        {
          apply (balanced_step_to_bigstep_matching' (c + length binds) (allocate_bindings G renamed_binds) A' renamed_m
                 D A' (MReturn e) St (c + length binds)); auto.
        }

        eapply EvalWhere; eauto.

    + (* MFail *)
      inversion Hbal; subst; try discriminate.

      * (* BMatchArg *)
        exfalso.
        assert (Hcontra: y :: A = [] /\ eval_matching c G (update_locs St) (y :: A) m0 D MRFail c').
        { apply balanced_step_to_bigstep_matching' with (A' := y :: A) (u := MFail); auto. }
        destruct Hcontra as [Hempty _].
        discriminate.

      * (* BMatchBind *)
        assert (Hsubst_result : A' = [] /\ eval_matching c G (update_locs St) A' (subst_matching m0 y x) D MRFail c').
        {
          apply balanced_step_to_bigstep_matching' with (A' := A') (u := MFail); auto.
        }
        destruct Hsubst_result as [HA' Hsubst_eval].

        split; [ assumption | ].
        eapply EvalBindVar. eassumption.

      * (* BMatchConsSuccess *)
        assert (Hnested_result : A' = [] /\ eval_matching c1 D0 (update_locs St) A' (build_nested_matches args ps m0) D MRFail c').
        { apply balanced_step_to_bigstep_matching' with (A' := A') (u := MFail); auto. }
        destruct Hnested_result as [HA' Hnested_eval].
        assert (Hexpr : eval_expr c G (update_locs (KPat A' cp ps m0 :: St)) (EVar x) D0 (ECons cp (map EVar args)) c1).
        { apply balanced_step_to_bigstep_expr' with (w := ECons cp (map EVar args)); auto. constructor. }

        split; [ assumption | ].
        simpl in Hexpr.
        eapply EvalConsMatch; eauto.

      * (* BMatchConsFail *)
        assert (Hexpr : eval_expr c G (update_locs (KPat A0 cp ps m0 :: St)) (EVar x) D (ECons cp' args) c').
        { apply balanced_step_to_bigstep_expr' with (w := ECons cp' args); auto. constructor. }

        split; [ reflexivity | ].
        simpl in Hexpr.
        eapply EvalConsFail; eauto.

      * (* BMatchConsFail *)
        assert (HFail2 : A' = [] /\ eval_matching c1 D0 (update_locs St) A' m2 D MRFail c').
        {
          apply (balanced_step_to_bigstep_matching' c1 D0 A' m2 D A' MFail St c'); auto.
        }
        destruct HFail2 as [HA HEval2].
        split; auto.
        subst A'.
        assert (HFail1 : eval_matching c G (update_locs (KAlt [] m2 :: St)) [] m1 D0 MRFail c1).
        {
          rewrite update_locs_KAlt.
          apply (balanced_step_to_bigstep_matching' c G [] m1 D0 [] MFail (KAlt [] m2 :: St) c1); auto.
        }

        simpl in HFail1.
        eapply EvalAltRight; eauto.

      * (* BMatchAltRight fail *)
        assert (HFail : A' = [] /\ eval_matching (c + Datatypes.length binds)
                                    (allocate_bindings G
                                    (rename_bindings binds (gen_n_fresh c (Datatypes.length binds))))
                                    (update_locs St) A'
                                    (rename_matching m0 (gen_n_fresh c (Datatypes.length binds)) binds)
                                    D MRFail (c + Datatypes.length binds)).
        {
          apply (balanced_step_to_bigstep_matching'
                   (c + Datatypes.length binds)
                   (allocate_bindings G (rename_bindings binds (gen_n_fresh c (Datatypes.length binds))))
                   A'
                   (rename_matching m0 (gen_n_fresh c (Datatypes.length binds)) binds)
                   D A' MFail St (c + Datatypes.length binds));
          auto.
        }
        destruct HFail as [HA HEval].
        split; auto.
        eapply EvalWhere with (ys := gen_n_fresh c (Datatypes.length binds)); eauto.
Qed.

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
  - intros. eapply balanced_step_to_bigstep_expr'; eauto.
  - intros. eapply balanced_step_to_bigstep_matching'; eauto.
Qed.

