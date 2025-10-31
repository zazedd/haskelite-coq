From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common Bigstep Smallstep Big_impl_small Small_impl_big.
Import ListNotations.

(* main theorem *)
Theorem bigstep_iff_balanced_step_expr : forall c G L e D w St c',
  L = update_locs St ->
  whnf w ->
  (eval_expr c G L e D w c' <->
   balanced_step_expr
     {| c := c; cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |}
     {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |})

with bigstep_iff_balanced_step_matching : forall c G L A m D u St c',
  L = update_locs St ->
  matching_final u ->
  (match u with
   | MReturn e => eval_matching c G L A m D (MRReturn e) c'
   | MFail => eval_matching c G L A m D MRFail c'
   | _ => False
   end <->
   balanced_step_matching
     {| c := c; cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |}
     {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch [] u; cfg_stack := St |})
.
Proof.
  - intros c G L e D w St c' HL Hwhnf. split; intro H.
    + apply (proj1 bigstep_impl_balancedstep) with (L := L); assumption.
    + subst L. apply balanced_step_to_bigstep_expr_gen in H; assumption.

  - intros c G L A m D u St c' HL Hu.
    destruct u; try (exfalso; inversion Hu; fail).
    + split; intro H.
      * exact (proj2 bigstep_impl_balancedstep c G L A m D (MRReturn e) c' H St HL).
      * subst L. apply balanced_step_to_bigstep_matching_gen in H; auto.
    + split; intro H.
      * exact (proj2 bigstep_impl_balancedstep c G L A m D MRFail c' H St HL).
      * subst L. apply balanced_step_to_bigstep_matching_gen in H; auto.
        destruct H. assumption.
Qed.

Corollary initial_bigstep_iff_balanced_step_expr : forall e D w c',
  whnf w ->
  (eval_expr 0 empty_heap [] e D w c' <->
   balanced_step_expr
     {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlExpr e; cfg_stack := [] |}
     {| c := c'; cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := [] |})

with initial_bigstep_iff_balanced_step_matching : forall A m D u c',
  matching_final u ->
  (match u with
   | MReturn e => eval_matching 0 empty_heap [] A m D (MRReturn e) c'
   | MFail => eval_matching 0 empty_heap [] A m D MRFail c'
   | _ => False
   end <->
   balanced_step_matching
     {| c := 0; cfg_heap := empty_heap; cfg_ctrl := CtrlMatch A m; cfg_stack := [] |}
     {| c := c'; cfg_heap := D; cfg_ctrl := CtrlMatch [] u; cfg_stack := [] |})
.
Proof.
  - intros. apply bigstep_iff_balanced_step_expr with (c := 0) (G := empty_heap) (L := []). reflexivity. assumption.
  - intros. apply bigstep_iff_balanced_step_matching with (c := 0) (G := empty_heap) (L := []). reflexivity. assumption.
Qed.
