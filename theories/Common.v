From Coq Require Import String Arith List.
From Coq Require Import FMaps FSets.
From Haskelite Require Import Expr.
Import ListNotations.

(* type for L, for blackholing *)
Definition var_set := list var.

Definition in_var_set (x : var) (s : var_set) : bool :=
  existsb (String.eqb x) s.

Definition bindings := list (var * expr).

Module StringDec <: DecidableType.
  Definition t := string.
  Definition eq := @eq string.
  Definition eq_refl := @eq_refl string.
  Definition eq_sym := @eq_sym string.
  Definition eq_trans := @eq_trans string.
  Definition eq_dec := string_dec.
End StringDec.

Module StringMap := FMapWeakList.Make(StringDec).
Module StringMapFacts := FMapFacts.Facts(StringMap).

Definition heap := StringMap.t expr.
Definition empty_heap : heap := StringMap.empty expr.

(* Lookup and update operations *)
Definition heap_lookup (h : heap) (x : var) : option expr :=
  StringMap.find x h.

Definition heap_update (h : heap) (x : var) (e : expr) : heap :=
  StringMap.add x e h.

Definition heap_remove (h : heap) (x : var) : heap :=
  StringMap.remove x h.

(* renamings only *)
Fixpoint subst_expr (e : expr) (y : var) (x : var) {struct e} : expr :=
  match e with
  | EVar z => if String.eqb z x then EVar y else EVar z
  | EApp e1 e2 => EApp (subst_expr e1 y x) (subst_expr e2 y x)
  | ELam m => ELam (subst_matching m y x)
  | ECons c es => ECons c (map (fun e => subst_expr e y x) es)
  end

with subst_matching (m : matching) (y : var) (x : var) {struct m} : matching :=
  match m with
  | MReturn e => MReturn (subst_expr e y x)
  | MFail => MFail
  | MMatch p m' => MMatch p (subst_matching m' y x)
  | MSupply e m' => MSupply (subst_expr e y x) (subst_matching m' y x)
  | MAlt m1 m2 => MAlt (subst_matching m1 y x) (subst_matching m2 y x)
  | MWhere m' b => MWhere (subst_matching m' y x) (map (fun p => (fst p, subst_expr (snd p) y x)) b)
  end
.

Fixpoint rename_bindings (b : list (var * expr)) (ys : list var) : list (var * expr) := 
  match b, ys with
  | [], [] | [], _ | _, [] => []
  | (x, e) :: xs, y :: ys => (y, e) :: rename_bindings xs ys
  end.

Definition rename_matching (m : matching) (ys : list var) (binds : list (var * expr)) : matching := 
  match m with
  | MWhere ms bs => let b := rename_bindings bs ys in MWhere ms b
  | _ => m
  end.

Definition allocate_bindings (G : heap) (b : list (var * expr)) : heap :=
  fold_left (fun acc (s : (var * expr)) => let (k, e) := s in heap_update acc k e) b G.

Open Scope string_scope.
Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

Fixpoint generate_fresh_vars (base : var) (n : nat) (avoid : list var) : list var :=
  match n with
  | O => []
  | S n' => 
      let candidate := base ++ "_" ++ string_of_nat (length avoid + n') in
      if in_dec string_dec candidate avoid then
        generate_fresh_vars base n' avoid
      else
        candidate :: generate_fresh_vars base n' (candidate :: avoid)
  end.
Close Scope string_scope.

(* build y1 |> p1 => ... =>  yn |> pn =>  m *)
Fixpoint build_nested_matches (vars : list var) (pats : list pattern) (m : matching) : matching :=
  match vars, pats with
  | [], [] => m
  | v :: vs, p :: ps => MSupply (EVar v) (MMatch p (build_nested_matches vs ps m))
  | _, _ => MFail
  end.

Fixpoint apply_args (args : list var) (e : expr) : expr :=
  match args with
  | [] => e
  | y :: ys => apply_args ys (EApp e (EVar y))
  end.

Lemma map_injective : forall {A B : Type} (f : A -> B) (l1 l2 : list A),
  (forall x y, f x = f y -> x = y) ->
  map f l1 = map f l2 ->
  l1 = l2.
Proof.
  intros A B f l1.
  induction l1; intros l2 Hinj Hmap.
  - destruct l2; auto. discriminate.
  - destruct l2.
    + discriminate.
    + simpl in Hmap. injection Hmap as Hhead Htail.
      f_equal.
      * apply Hinj. assumption.
      * apply IHl1; assumption.
Qed.

