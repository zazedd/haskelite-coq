From Stdlib Require Import String List.
Import ListNotations.

(* Variable and constructor names *)
Definition var := string.
Definition constructor := string.

Inductive pattern : Type :=
  | PVar : var -> pattern                          (* x *)
  | PCons : constructor -> list pattern -> pattern. (* c(p1,...,pn) *)

(* Mutual inductive definitions for the syntax *)
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
  | MWhere : matching -> bindings -> matching    (* m where binds *)

with bindings : Type :=
  | Bindings : list (var * expr) -> bindings.    (* {x1 = e1; ...; xn = en} *)

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

Scheme expr_ind_mutual := Induction for expr Sort Prop
with matching_ind_mutual := Induction for matching Sort Prop
with bindings_ind_mutual := Induction for bindings Sort Prop.

Print expr_ind_mutual.

Lemma matching_arity_where : forall m binds,
  matching_arity (MWhere m binds) = matching_arity m.
Proof.
  reflexivity.
Qed.

Lemma matching_arity_preserved_under_pattern : forall p m n,
  matching_arity m = Some n -> matching_arity (MMatch p m) = Some (S n).
Proof.
  intros p m n H.
Admitted.

