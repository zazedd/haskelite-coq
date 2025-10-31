From Coq Require Import String Arith List.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
From Haskelite Require Import Expr Common Bigstep Smallstep.

Extract Constant String.eqb => "(=)".
Extract Constant string_dec => "(fun s1 s2 -> if s1 = s2 then Left else Right)".

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun fO fS n -> if n = 0 then fO () else fS (n-1))".

(* Extract bool *)
Extract Inductive bool => "bool" [ "true" "false" ].

(* Extract list *)
Extract Inductive list => "list" [ "[]" "(::)" ].

(* Extract option *)
Extract Inductive option => "option" [ "Some" "None" ].

(* Extract prod (pairs) *)
Extract Inductive prod => "(*)" [ "(,)" ].

(* Extract sumbool for decidability *)
Extract Inductive sumbool => "bool" [ "true" "false" ].

(*Extract Constant StringMap.t => "StringMap.t".*)
Extract Constant StringMap.empty => "StringMap.empty".
Extract Constant StringMap.add => "StringMap.add".
Extract Constant StringMap.find => "StringMap.find".
Extract Constant StringMap.remove => "StringMap.remove".
Extract Constant StringMap.elements => "StringMap.bindings".

Extraction Language OCaml.
Set Extraction AccessOpaque.
Set Extraction Output Directory "out".

Extraction "haskelite.ml"
  (* expr *)
  expr matching pattern whnf matching_arity matching_result

  (* common *)
  heap empty_heap heap_lookup heap_update heap_remove
  subst_expr subst_matching
  rename_bindings rename_matching allocate_bindings
  build_nested_matches apply_args
  var_set in_var_set generate_fresh_vars

  (* bigstep *)
  eval_expr eval_matching

  (* smallstep *)
  continuation stack control config
  step step_star
  initial_config is_final_expr is_stuck
  balanced_expr_eval balanced_matching_eval.

