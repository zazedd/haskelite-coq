From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr Common Bigstep Smallstep Big_impl_small Small_impl_big.
Import ListNotations.

(* main theorem *)
Theorem bigstep_iff_balanced_step_expr {FG : FreshVarGen} : forall G L e D w St,
  L = update_locs St ->
  whnf w ->
  (eval_expr G L e D w <->
   balanced_step_expr
     {| cfg_heap := G; cfg_ctrl := CtrlExpr e; cfg_stack := St |}
     {| cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := St |})

with bigstep_iff_balanced_step_matching {FG : FreshVarGen} : forall G L A m D u St,
  L = update_locs St ->
  matching_final u ->
  (match u with
   | MReturn e => eval_matching G L A m D (MRReturn e)
   | MFail => eval_matching G L A m D MRFail
   | _ => False
   end <->
   balanced_step_matching
     {| cfg_heap := G; cfg_ctrl := CtrlMatch A m; cfg_stack := St |}
     {| cfg_heap := D; cfg_ctrl := CtrlMatch [] u; cfg_stack := St |})
.
Proof.
  - intros G L e D w St HL Hwhnf. split; intro H.
    + apply (proj1 bigstep_impl_balancedstep) with (L := L); assumption.
    + subst L. apply balanced_step_to_bigstep_expr_gen in H; assumption.

  - intros G L A m D u St HL Hu.
    destruct u; try (exfalso; inversion Hu; fail).
    + split; intro H.
      * exact (proj2 bigstep_impl_balancedstep G L A m D (MRReturn e) H St HL).
      * subst L. apply balanced_step_to_bigstep_matching_gen in H; auto.
    + split; intro H.
      * exact (proj2 bigstep_impl_balancedstep G L A m D MRFail H St HL).
      * subst L. apply balanced_step_to_bigstep_matching_gen in H; auto.
        destruct H. assumption.
Qed.

Corollary initial_bigstep_iff_balanced_step_expr {FG : FreshVarGen} : forall e D w,
  whnf w ->
  (eval_expr empty_heap [] e D w <->
   balanced_step_expr
     {| cfg_heap := empty_heap; cfg_ctrl := CtrlExpr e; cfg_stack := [] |}
     {| cfg_heap := D; cfg_ctrl := CtrlExpr w; cfg_stack := [] |})

with initial_bigstep_iff_balanced_step_matching {FG : FreshVarGen} : forall A m D u,
  matching_final u ->
  (match u with
   | MReturn e => eval_matching empty_heap [] A m D (MRReturn e)
   | MFail => eval_matching empty_heap [] A m D MRFail
   | _ => False
   end <->
   balanced_step_matching
     {| cfg_heap := empty_heap; cfg_ctrl := CtrlMatch A m; cfg_stack := [] |}
     {| cfg_heap := D; cfg_ctrl := CtrlMatch [] u; cfg_stack := [] |})
.
Proof.
  - intros. apply bigstep_iff_balanced_step_expr with (G := empty_heap) (L := []). reflexivity. assumption.
  - intros. apply bigstep_iff_balanced_step_matching with (G := empty_heap) (L := []). reflexivity. assumption.
Qed.
