Require Import RelationExtraction.
(* Set Mangle Names. *) (* We use FunInd, that is uncompatible with mangle names *)
(* From Equations Require Import Equations. *) (* TODO use Equations instead of FunInd? *)

Inductive n : Set := | Zero : n | Succ : n -> n.

Inductive add : n -> n -> n -> Prop :=
| addZero : forall o, add o Zero o
| addSucc : forall o m p, add o m p -> add o (Succ m) (Succ p).

Axiom (H : Prop).  (* no bug if H not fresh *)
Axiom (po : Prop). (* no bug if po not fresh *)
Axiom (add12_correct : Prop).
Axiom (true : Prop).
(* Axiom (add12 : Prop). *) (* TODO bug if add12 not fresh *)

Extraction Relation (add [1 2]).
Extraction Relation Single Relaxed (add [2 3]).
Extraction Relation Single (add [1 2 3]).
Extraction Relation Single Relaxed (add [3 2]).

Extraction Relation Fixpoint (add [1 2] Struct 2).
(*
Eval compute in (add12 (Succ (Succ Zero)) (Succ Zero)).
Eval compute in (add12 (Succ Zero) (Succ (Succ Zero))).
*)

(* Print add12.
Print add12_correct. *)

	  (*
Equations add12b (p1 p2 : n) : n :=
add12b p1 Zero := p1;
add12b p1 (Succ fix3) := let fix4 := add12 p1 fix3 in Succ fix4.
	   *)

(* Check FunctionalElimination_add12b.
Check add12_ind.

Check add12_correct. *)
	  
(* Print Registered. *)


Extraction Relation Fixpoint Relaxed (add [2 3]). (* no proof *)
(*
Eval compute in (add23 (Succ (Succ Zero)) (Succ Zero)).
Eval compute in (add23 (Succ Zero) (Succ (Succ Zero))).
*)

Fail Extraction Relation Fixpoint Relaxed (add [1 2 3]).
Fail Extraction Relation Relaxed (add [1 3]).
