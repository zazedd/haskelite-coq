From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common Bigstep Smallstep Big_impl_small Small_impl_big.
Import ListNotations.

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
  - intros. eapply balanced_step_to_bigstep_expr_gen; eauto.
  - intros. eapply balanced_step_to_bigstep_matching_gen; eauto.
Qed.

