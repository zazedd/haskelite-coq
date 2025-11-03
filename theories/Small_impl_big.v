From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common Bigstep Smallstep.
Import ListNotations.

(** NOTE:
    this file takes quite a while to compile, and it might crash the LSP
    if you want to view the proof contexts, I recommend changing Qed. to Admitted.
    at the bottom of the proof, so that Coq doesn't try to generate a program from the proof and hang
    the LSP
*)

Lemma balanced_step_to_bigstep_expr_gen {FG : FreshVarGen} : forall G e D w St,
  balanced_step_expr
    {| cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |}
    {| cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |} ->
  whnf w ->
  eval_expr G (update_locs St) e D w

with balanced_step_to_bigstep_matching_gen {FG : FreshVarGen} : forall G A m D A' u St,
  balanced_step_matching
    {| cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |}
    {| cfg_heap := D; cfg_ctrl := CtrlMatch A' u; cfg_stack := St |} ->
  matching_final u ->
  match u with
  | MReturn e => eval_matching G (update_locs St) A m D (MRReturn e)
  | MFail => A' = [] /\ eval_matching G (update_locs St) A m D MRFail
  | _ => False
  end
.
Proof.
  - intros G e D w St Hbal Hwhnf.
    inversion Hbal; subst.
    + constructor. assumption.
    + (* BExprApp *)
      assert (Heval1 : eval_expr G (update_locs (KArg y :: St)) e0 D0 (ELam m)). {
        apply balanced_step_to_bigstep_expr_gen with (St := KArg y :: St).
        - auto.
        - inversion H6; subst.
          apply whnf_lambda with n. assumption.
      }

      assert (Heval2 : eval_expr D0 (update_locs St) (ELam (MSupply (EVar y) m)) D w).
      { apply balanced_step_to_bigstep_expr_gen with (St := St); assumption. }

      simpl in Heval1.
      eapply EvalApp; eauto.

    + (* BExprVar *)
      assert (Heval : eval_expr (heap_remove G y) (update_locs (KUpdate y :: St)) e0 D0 w).
      { apply balanced_step_to_bigstep_expr_gen with (St := KUpdate y :: St); auto. }

      simpl in Heval. rewrite <- update_locs_KUpdate in Heval.
      eapply EvalVar; eauto.

    + (* BExprSat *)
      assert (Hmatch : eval_matching G (update_locs (KEnd :: St)) [] m D0 (MRReturn e0)). {
        assert (Hmatch' := balanced_step_to_bigstep_matching_gen FG G [] m D0 [] (MReturn e0) (KEnd :: St) H6).
        simpl in Hmatch'. apply Hmatch'. apply MFinal_Return.
      }

      assert (Heval : eval_expr D0 (update_locs St) e0 D w).
      { apply balanced_step_to_bigstep_expr_gen with (St := St); auto. }

      eapply EvalSat; eauto.

  - intros G A m D A' u St Hbal Hfinal.
    destruct u; try (exfalso; inversion Hfinal; fail).
    + (* MReturn *)
      inversion Hbal; subst; try discriminate.
      * constructor.
      * (* BMatchReturnArgs *)
        inversion H8; subst.
        -- apply EvalReturn.
        -- contradiction.

      * (* BMatchArg *)
        assert (Heval : eval_matching G (update_locs St) (y :: A) m0 D (MRReturn e)).
        { apply balanced_step_to_bigstep_matching_gen with (A' := A') (u := MReturn e); auto. }
        eapply EvalArg. eauto.

      * (* BMatchBind *)
        assert (Heval : eval_matching G (update_locs St) A0 (subst_matching m0 y x) D (MRReturn e)).
        { apply balanced_step_to_bigstep_matching_gen with (A' := A') (u := MReturn e); auto. }
        eapply EvalBindVar. eauto.

      * (* BMatchConsSuccess *)
        assert (Heval_expr : eval_expr G (update_locs (KPat A0 cp ps m0 :: St)) (EVar x) D0 (ECons cp (map EVar args))).
        { apply balanced_step_to_bigstep_expr_gen; auto. constructor. }

        assert (Heval_match : eval_matching D0 (update_locs St) A0 (build_nested_matches args ps m0) D (MRReturn e)).
        { apply balanced_step_to_bigstep_matching_gen with (A' := A') (u := MReturn e); auto. }

        eapply EvalConsMatch; eauto.

      * (* BMatchAltLeft *)
        assert (Heval : eval_matching G (update_locs (KAlt A m2 :: St)) A m1 D (MRReturn e)).
        { apply balanced_step_to_bigstep_matching_gen with (A' := []) (u := MReturn e); auto. }
        simpl in Heval.
        eapply EvalAltLeft. eassumption.

      * (* BMatchAltRight *)
        assert (Hm1 := balanced_step_to_bigstep_matching_gen FG _ _ _ _ _ _ _ H7 MFinal_Fail).
        destruct Hm1 as [_ Hm1].

        assert (Hm2: eval_matching D0 (update_locs St) A m2 D (MRReturn e)).
        { apply balanced_step_to_bigstep_matching_gen with (A' := A') (u := MReturn e); auto. }

        eapply EvalAltRight; eauto.

      * (* BMatchWhere *)
        set (renamed_binds := rename_bindings binds (gen_fresh (update_locs St) (Datatypes.length binds))).
        set (renamed_m := rename_matching m0 (gen_fresh (update_locs St) (Datatypes.length binds)) binds).
        assert (Heval :
          eval_matching (allocate_bindings G renamed_binds) (update_locs St) A renamed_m D (MRReturn e)).
        {
          apply (balanced_step_to_bigstep_matching_gen FG (allocate_bindings G renamed_binds) A renamed_m
                 D A' (MReturn e) St); auto.
        }

        eapply EvalWhere; eauto.

    + (* MFail *)
      inversion Hbal; subst; try discriminate.
      * (* BMatchFail *)
        split; [ reflexivity | ].
        constructor.

      * (* BMatchArg *)
        assert (Hinner_result : A' = [] /\ eval_matching G (update_locs St) (y :: A) m0 D MRFail).
        { apply balanced_step_to_bigstep_matching_gen with (A' := A') (u := MFail); auto. }
        destruct Hinner_result as [HA' Hinner_eval].
        split; [ assumption | ].
        eapply EvalArg. eassumption.

      * (* BMatchBind *)
        assert (Hsubst_result : A' = [] /\ eval_matching G (update_locs St) A0 (subst_matching m0 y x) D MRFail).
        { apply balanced_step_to_bigstep_matching_gen with (A' := A') (u := MFail); auto. }
        destruct Hsubst_result as [HA' Hsubst_eval].

        split; [ assumption | ].
        eapply EvalBindVar. eassumption.

      * (* BMatchConsSuccess *)
        assert (Hnested_result : A' = [] /\ eval_matching D0 (update_locs St) A0 (build_nested_matches args ps m0) D MRFail).
        { apply balanced_step_to_bigstep_matching_gen with (A' := A') (u := MFail); auto. }
        destruct Hnested_result as [HA' Hnested_eval].
        assert (Hexpr : eval_expr G (update_locs (KPat A0 cp ps m0 :: St)) (EVar x) D0 (ECons cp (map EVar args))).
        { apply balanced_step_to_bigstep_expr_gen with (w := ECons cp (map EVar args)); auto. constructor. }

        split; [ assumption | ].
        simpl in Hexpr.
        eapply EvalConsMatch; eauto.

      * (* BMatchConsFail *)
        assert (Hexpr : eval_expr G (update_locs (KPat A0 cp ps m0 :: St)) (EVar x) D (ECons cp' args)).
        { apply balanced_step_to_bigstep_expr_gen with (w := ECons cp' args); auto. constructor. }

        split; [ reflexivity | ].
        simpl in Hexpr.
        eapply EvalConsFail; eauto.

      * (* BMatchAltRight fail *)
        assert (Hm1 : @nil var = [] /\ eval_matching G (update_locs (KAlt A m2 :: St)) A m1 D0 MRFail).
        { apply balanced_step_to_bigstep_matching_gen with (A' := []) (u := MFail); auto. }
        destruct Hm1 as [_ Hm1].

        assert (Hm2 : A' = [] /\ eval_matching D0 (update_locs St) A m2 D MRFail).
        { apply balanced_step_to_bigstep_matching_gen with (A' := A') (u := MFail); auto. }
        destruct Hm2 as [HA' Hm2].

        split; [ assumption | ].
        simpl in Hm1.
        eapply EvalAltRight; eauto.

      * (* BMatchWhere *)
        assert (HFail : A' = [] /\ eval_matching
                                    (allocate_bindings G
                                    (rename_bindings binds (gen_fresh (update_locs St) (Datatypes.length binds))))
                                    (update_locs St) A
                                    (rename_matching m0 (gen_fresh (update_locs St) (Datatypes.length binds)) binds)
                                    D MRFail).
        {
          apply (balanced_step_to_bigstep_matching_gen FG
                   (allocate_bindings G (rename_bindings binds (gen_fresh (update_locs St) (Datatypes.length binds))))
                   A
                   (rename_matching m0 (gen_fresh (update_locs St) (Datatypes.length binds)) binds)
                   D A' MFail St);
          auto.
        }
        destruct HFail as [HA HEval].
        split; auto.
        eapply EvalWhere with (ys := gen_fresh (update_locs St) (Datatypes.length binds)); eauto.
Qed.
