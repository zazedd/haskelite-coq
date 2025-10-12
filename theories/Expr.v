From Coq Require Import String Arith List.
Import ListNotations.

Definition var := string.
Definition constructor := string.

Inductive pattern : Type :=
  | PVar : var -> pattern                          (* x *)
  | PCons : constructor -> list pattern -> pattern. (* c(p1,...,pn) *)

Inductive expr : Type :=
  | EVar : var -> expr                           (* x *)
  | EApp : expr -> expr -> expr                  (* e1 e2 *)
  | ELam : matching -> expr                      (* λm *)
  | ECons : constructor -> list expr -> expr     (* c(e1,...,en) *)

with matching : Type :=
  | MReturn : expr -> matching                   (* ⌈e⌉ *)
  | MFail : matching                             (* ⊥ *)
  | MMatch : pattern -> matching -> matching     (* p ⇒ m *)
  | MSupply : expr -> matching -> matching       (* e ⊲ m *)
  | MAlt : matching -> matching -> matching      (* m1 | m2 *)
  | MWhere : matching -> list (var * expr) -> matching    (* m where binds *)
.

Scheme expr_ind_mutual := Induction for expr Sort Prop
with matching_ind_mutual := Induction for matching Sort Prop.

Print expr_ind_mutual.

Fixpoint matching_arity (m : matching) : option nat :=
  match m with
  | MReturn _ => Some 0
  | MFail => Some 0
  | MMatch _ m' => 
      match matching_arity m' with
      | Some n => Some (S n)
      | None => None
      end
  | MSupply _ m' =>
      match matching_arity m' with
      | Some 0 => Some 0
      | Some (S n) => Some n
      | None => None
      end
  | MAlt m1 m2 =>
      match matching_arity m1, matching_arity m2 with
      | Some n1, Some n2 => if Nat.eqb n1 n2 then Some n1 else None
      | _, _ => None
      end
  | MWhere m' _ => matching_arity m'
  end.

Inductive whnf : expr -> Prop :=
  | whnf_lambda : forall m n,
      matching_arity m = Some (S n) ->  (* arity > 0 *)
      whnf (ELam m)
  | whnf_constructor : forall c args,
      whnf (ECons c args).

(* Matching results (μ) *)
Inductive matching_result : Type :=
  | MRReturn : expr -> matching_result    (* ⌈e⌉ *)
  | MRFail : matching_result.             (* ⊥ *)

(** Arity preservation *)

Lemma matching_arity_where : forall m binds,
  matching_arity (MWhere m binds) = matching_arity m.
Proof.
  reflexivity.
Qed.

Lemma matching_arity_preserved_under_pattern : forall p m n,
  matching_arity m = Some n -> matching_arity (MMatch p m) = Some (S n).
Proof.
  intros p m n H.
  simpl. rewrite H.
  reflexivity.
Qed.

(* alt branches must have equal arity to be well-formed *)
Lemma matching_arity_alt_defined : forall m1 m2 n,
  matching_arity (MAlt m1 m2) = Some n ->
  exists n1 n2, matching_arity m1 = Some n1 /\ matching_arity m2 = Some n2 /\ n1 = n2.
Proof.
  intros m1 m2 n H.
  simpl in H.
  destruct (matching_arity m1) as [n1 | ] eqn:H1; destruct (matching_arity m2) as [n2 | ] eqn:H2;
  try discriminate.
  destruct (Nat.eqb n1 n2) eqn:Heq; try discriminate.
  apply Nat.eqb_eq in Heq.
  exists n1, n2.
  auto.
Qed.

(** WHNF *)
Lemma lambda_whnf : forall m n,
  matching_arity m = Some (S n) -> whnf (ELam m).
Proof.
  intros. apply whnf_lambda with n. assumption.
Qed.

Lemma cons_whnf : forall c args,
  whnf (ECons c args).
Proof.
  constructor.
Qed.

Lemma not_whnf_var : forall x, ~whnf (EVar x).
Proof.
  intros x H. inversion H.
Qed.

Lemma not_whnf_app : forall f e, ~whnf (EApp f e).
Proof.
  intros f e H. inversion H.
Qed.

(** Structural properties *)
Lemma supply_reduces_arity : forall e m n,
  matching_arity m = Some (S n) ->
  matching_arity (MSupply e m) = Some n.
Proof.
  intros.
  simpl. rewrite H.
  reflexivity.
Qed.

Lemma supply_preserves_zero_arity : forall e m,
  matching_arity m = Some 0 ->
  matching_arity (MSupply e m) = Some 0.
Proof.
  intros.
  simpl. rewrite H.
  reflexivity.
Qed.

Lemma return_arity_zero : forall e, matching_arity (MReturn e) = Some 0.
Proof. reflexivity. Qed.

Lemma fail_arity_zero : matching_arity MFail = Some 0.
Proof. reflexivity. Qed.

(* fresh variable generator context *)
(* the counter is threaded through evaluation *)
Parameter gensym : nat -> var.

Axiom gensym_injective : forall n m,
  gensym n = gensym m -> n = m.

Fixpoint gen_n_fresh (c : nat) (n : nat) : list var :=
  match n with
  | 0 => []
  | S n' => gensym c :: gen_n_fresh (S c) n'
  end.

Lemma gen_n_fresh_length : forall c n,
  length (gen_n_fresh c n) = n.
Proof.
  intros c n. revert c.
  induction n; intros c; simpl; auto.
Qed.

Require Import Lia.

Lemma gen_n_fresh_NoDup : forall c n,
  NoDup (gen_n_fresh c n).
Proof.
  intros c n. revert c.
  induction n; intros c; simpl.
  - constructor.
  - constructor.
    + intros Hin.
      induction n; simpl in Hin.
      * inversion Hin.
      * destruct Hin as [Heq | Hin'].
        -- apply gensym_injective in Heq. lia.
        -- admit.
    + apply IHn.
Admitted.

Lemma gen_n_fresh_In : forall c n k,
  In (gensym k) (gen_n_fresh c n) <-> c <= k < c + n.
Proof.
  intros c n. revert c.
  induction n; intros c k; simpl.
  - split; intros H.
    + inversion H.
    + lia.
  - split; intros H.
    + destruct H.
      * apply gensym_injective in H. subst. lia.
      * apply IHn in H. lia.
    + destruct (Nat.eq_dec c k).
      * left. subst. reflexivity.
      * right. apply IHn. lia.
Qed.
