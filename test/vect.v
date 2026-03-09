(* Est-ce que l'extraction depuis Vect donne (à peu près) la définition par point  fixe ? *)
(* Limitation: pas de type parametrique ! donc ici des vecteurs de type Bool *)

Require Import RelationExtraction.


Inductive catList : list bool -> list bool -> list bool -> Prop :=
| nilList : forall (v : list bool), catList v nil v
| consList : forall (v : list bool) (u : list bool) w, catList v u w ->
  forall (a: bool), catList v (cons a u) (cons a w)
.

Fail Extraction Relation Fixpoint (catList [1 2]).


Inductive Vect : nat -> Type :=
| nil   : Vect 0
| cons  : forall (_ : bool) (n : nat), Vect n -> Vect (S n)
.

Inductive cat : forall (n : nat), Vect n -> forall (m : nat), Vect m -> Vect (m + n) -> Prop :=
| addnil : forall n (v : Vect n), cat n v 0 nil v
| addcons : forall n (v : Vect n) m (u : Vect m) w, cat n v m u w ->
  forall (a: bool), cat n v (S m) (cons a m u) (cons a (m+n) w)
.

Extraction Relation Fixpoint Relaxed (Vect [1]).
Print Vect_full.
Print Vect_full_equation.
Print Vect_full_ind.
Fail Extraction Relation Fixpoint Relaxed (cat [1 2 3 4]).

(* et voir aussi sur la version fordisme *)

Inductive VectFord (n : nat) : Type :=
| nilFord   : n = 0 -> VectFord n
| consFord  : forall (_ : bool) (m : nat), VectFord m -> n = S m -> VectFord n
.

Inductive catFord : forall (n : nat), VectFord n -> forall (m : nat), VectFord m -> VectFord (m + n) ->
  Prop :=
| addnilFord : forall n (v : VectFord n), catFord n v 0 (nilFord 0 eq_refl) v
| addconsFord : forall n (v : VectFord n) m (u : VectFord m) w,
  catFord n v m u w -> forall (a: bool), catFord n v (S m) (consFord _ a m u eq_refl) (consFord _ a (m+n) w eq_refl).

Fail Extraction Relation Fixpoint Relaxed (VectFord [1]).
Fail Extraction Relation Fixpoint Relaxed (catFord [1 2 3 4]).

