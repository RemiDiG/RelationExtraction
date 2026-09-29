Require Import RelationExtraction.
(* Set Mangle Names. *) (* We use FunInd, that is uncompatible with mangle names *)

Inductive n : Set := | Zero : n | Succ : n -> n.

Inductive add : n -> n -> n -> Prop :=
| addZero : forall o, add o Zero o
| addSucc : forall o m p, add o m p -> add o (Succ m) (Succ p).

Axiom (H: Prop).  (* no bug if H not fresh *)
Axiom (po : Prop). (* no bug if po not fresh *)
(* Axiom (add12 : Prop). *) (* TODO bug if name add12 already there! *)
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

Extraction Relation Fixpoint Relaxed (add [2 3]). (* no proof *)
(*
Eval compute in (add23 (Succ (Succ Zero)) (Succ Zero)).
Eval compute in (add23 (Succ Zero) (Succ (Succ Zero))).
*)

Fail Extraction Relation Fixpoint Relaxed (add [1 2 3]).
Fail Extraction Relation Relaxed (add [1 3]).
