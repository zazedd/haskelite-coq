From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common Bigstep Smallstep Big_impl_small Small_impl_big.
Import ListNotations.

Theorem balanced_step_to_bigstep_expr : forall c G e D w St c',
  balanced_step_expr
    {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |}
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |} ->
  whnf w ->
  eval_expr c G (update_locs St) e D w c'

with balanced_step_to_bigstep_matching : forall c G A A' m D u St c',
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
  - intros. eapply balanced_step_to_bigstep_expr_gen; eauto.
  - intros. 
    destruct u; try (exfalso; inversion H0; fail).
    + assert (Hgen := balanced_step_to_bigstep_matching_gen c G A m D A' (MReturn e) St c' H H0).
      exact Hgen.
    + assert (Hgen := balanced_step_to_bigstep_matching_gen c G A m D A' MFail St c' H H0).
      exact Hgen.
Qed.

Corollary initial_balanced_step_to_bigstep_expr : forall e D w c',
  balanced_step_expr
    {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlExpr e; cfg_stack := [] |}
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := [] |} ->
  whnf w ->
  eval_expr 0 empty_heap [] e D w c'

with initial_balanced_step_to_bigstep_matching : forall A m D u c',
  balanced_step_matching
    {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlMatch A m; cfg_stack := [] |}
    {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch A u; cfg_stack := [] |} ->
  matching_final u ->
  match u with
  | MReturn e => eval_matching 0 empty_heap [] A m D (MRReturn e) c'
  | MFail => A = [] /\ eval_matching 0 empty_heap [] A m D MRFail c'
  | _ => False
  end.
Proof.
  - intros. 
    assert ([] = update_locs []) by reflexivity.
    rewrite H1.
    eapply balanced_step_to_bigstep_expr; eauto.
  - intros. 
    assert ([] = update_locs []) by reflexivity.
    rewrite H1.
    eapply balanced_step_to_bigstep_matching; eauto.
Qed.

Corollary initial_bigstep_iff_balanced_step_expr : forall e D w c',
  whnf w ->
  (eval_expr 0 empty_heap [] e D w c' <->
   balanced_step_expr
     {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlExpr e; cfg_stack := [] |}
     {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := [] |}).
Proof.
  intros e D w c' Hwhnf. split; intro H.
  + apply (proj1 big_step_impl_balanced_step) with (L := []); try assumption.
    assert ([] = update_locs []) by reflexivity. assumption.
  + apply initial_balanced_step_to_bigstep_expr; assumption.
Qed.

Corollary initial_bigstep_iff_balanced_step_matching : forall A m D e c',
  (eval_matching 0 empty_heap [] A m D (MRReturn e) c' <->
   balanced_step_matching
     {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlMatch A m; cfg_stack := [] |}
     {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch [] (MReturn e); cfg_stack := [] |}).
Proof.
  intros A m D e c'.
  split; intros H.
  - exact (proj2 big_step_impl_balanced_step 0 empty_heap [] A m D (MRReturn e) c' H [] eq_refl).
  - exact (balanced_step_to_bigstep_matching 0 empty_heap A [] m D (MReturn e) [] c' H (MFinal_Return e)).
Qed.

Corollary initial_bigstep_iff_balanced_step_matching_fail : forall m D c',
  (eval_matching 0 empty_heap [] [] m D MRFail c' <->
   balanced_step_matching
     {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlMatch [] m; cfg_stack := [] |}
     {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch [] MFail; cfg_stack := [] |}).
Proof.
  intros m D c'.
  split; intros H.
  - exact (proj2 big_step_impl_balanced_step 0 empty_heap [] [] m D MRFail c' H [] eq_refl).
  - assert (Hres := balanced_step_to_bigstep_matching 0 empty_heap [] [] m D MFail [] c' H MFinal_Fail).
    destruct Hres.
    simpl in H1. exact H1.
Qed.
