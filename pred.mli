(****************************************************************************)
(*  RelationExtraction - Extraction of inductive relations for Coq          *)
(*                                                                          *)
(*  This program is free software: you can redistribute it and/or modify    *)
(*  it under the terms of the GNU General Public License as published by    *)
(*  the Free Software Foundation, either version 3 of the License, or       *)
(*  (at your option) any later version.                                     *)
(*                                                                          *)
(*  This program is distributed in the hope that it will be useful,         *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           *)
(*  GNU General Public License for more details.                            *)
(*                                                                          *)
(*  You should have received a copy of the GNU General Public License       *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.   *)
(*                                                                          *)
(*  Copyright 2011, 2012 CNAM-ENSIIE                                        *)
(*                 Catherine Dubois <dubois@ensiie.fr>                      *)
(*                 David Delahaye <david.delahaye@cnam.fr>                  *)
(*                 Pierre-Nicolas Tollitte <tollitte@ensiie.fr>             *)
(****************************************************************************)

(* Internal dependencies *)
open Host_stuff
open Proof_scheme

(* Rocq dependencies *)
open Names

(* Extraction failure with some reason. *)
exception RelationExtractionError of string

(*************************)
(* Annotation for proofs *)
(*************************)

type annot_atom = {
  pa_prop_name : Id.t;
  pa_prem_name : Name.t;
}

(* An annot_atom for each constructor (of the Inductive). *)
type pannot = annot_atom list


(*********)
(* Types *)
(*********)

(* Generic type of a term *)
type clear_type = 
  | CTTuple of clear_type list (* Types of tuple's elements. *)
  | CTSum of Id.t list (* List of constructors of a sum type. *)
  | CTNone (* No type information. *)
type term_type = (clear_type * host_term_type)
type 't typed = ('t * term_type)


(************)
(* ML Terms *)
(************)

(* Mode *)
type mode_option = 
  | MInput
  | MOutput
  | MSkip (* used for host language stuff, must be ignored *)
type mode = mode_option list

type untyped_ml_pat =
(* Standard constructions *)
  | MLPVar of Id.t
  | MLPTuple of ml_pat list
  | MLPRecord of Id.t list * ml_pat list
  | MLPConstr of Id.t * ml_pat list
  | MLPConst of Id.t
  | MLPWild

(* Additionnal stuff *)
  (* Used for linearization. *)
  | MLPATrue | MLPAFalse
  (* Used by the fixpred library. *)
  | MLPASome of ml_pat | MLPANone
and ml_pat = untyped_ml_pat typed

type untyped_ml_term =
(* -- Begin: used by the specification -- *)
  | MLTVar of Id.t
  | MLTTuple of ml_term list
  | MLTRecord of Id.t list * ml_term list
  | MLTConstr of Id.t * ml_term list
  | MLTConst of Id.t
  | MLTFun of Id.t * ml_term list * mode option
  | MLTFunNot of Id.t * ml_term list * mode option
    (* MLTFun can be used to store function or inductive relations
       The "mode option" must be None for function and Some (...) for 
       predicates. *)
(* -- End: used by the specification -- *)
  | MLTMatch of ml_term * pannot * 
    (ml_pat * ml_term * pannot) list

(* Additionnal stuff *)
  (* Used for linearization. ml_terms are always variables. *)
  | MLTALin of (ml_term * ml_term) list
  (* Output of a complete extraction (only LTrue is used) : *)
  | MLTATrue | MLTAFalse
  (* Used by the fixpred library. *)
  | MLTASome of ml_term | MLTANone
  (* Default case in pattern matching *)
  | MLTADefault
and ml_term = untyped_ml_term typed

(* Pretty printer *)
val pp_ml_term : ml_term -> string
(*DEBUG*)
val pp_ml_pat : ml_pat -> string
val pp_ml_untyped_term : string -> untyped_ml_term -> string


(******************)
(* Specifications *)
(******************)

(* A premisse in a property (or constructor) of a specification. *)
type premisse =
  | PMTerm of ml_term * Id.t option
  | PMNot of premisse * Id.t option
  | PMOr of premisse list * Id.t option
  | PMAnd of premisse list * Id.t option
  | PMChoice of premisse list * Id.t option
(* The ident is used to tag premisses and follow them. *)

(* A property (or constructor) of a specification. *)
type property = {
  prop_name : Id.t;
  prop_vars : Id.t list;
  prop_prems : premisse list;
  prop_concl : ml_term;
}

(* Type of a specification. *)
type spec = {
  spec_name : Id.t;
  spec_args_types : term_type list;
  spec_props : property list;
} 

val pp_spec : spec -> string

(* Finds a premisse or a term from the premisse id (may raise Not_found if the
   premisse does not exists or if it is not a term). *)
(* TODO?: val find_premisse_by_name : 'htyp spec -> ident -> 'htyp premisse
val find_prem_term_by_name : 'htyp spec -> ident -> 'htyp ml_term *)


(****************)
(* ML functions *)
(****************)

(* A function in the ML-like intermediate language. *)
type ml_fun = {
  mlfun_name : Id.t;
  mlfun_args : Id.t list;
  mlfun_body : ml_term;
}

(* Pretty printer *)
val pp_ml_fun : ml_fun -> string


(*****************)
(* Fix functions *)
(*****************)

type fix_untyped_term =
(* Standard constructions. *)
  | FixVar of Id.t
(*  | FixRecord of ident list * fix_term list*)
  | FixConstr of Id.t * fix_term list
  | FixConst of Id.t
  | FixFun of Id.t * fix_term list
  | FixFunNot of Id.t * fix_term list
  | FixCase of fix_term * pannot * 
               (Id.t list * fix_term * pannot) list
  | FixLetin of Id.t * fix_term * fix_term * pannot
(* In letin, pannot contains props concerned by the letin,
   in match it contains props concerned by the pattern matching,
   in patterns, it contains the list of active props (props that can still
   appear in the output. *)

(* To be converted as standard constructions. *)
  | FixSome of fix_term
  | FixNone
  | FixTrue 
  | FixFalse 
and fix_term = fix_untyped_term typed

type fix_fun = {
  fixfun_name : Id.t;
  fixfun_args : Id.t list;
  fixfun_body : fix_term;
}

val pp_fix_term : fix_term -> string
val pp_fix_fun : fix_fun -> string


(*********)
(* Trees *)
(*********)

(* Predicate tree. Used to represent an inductive predicate before the code
   generation. *)
type tree

(* Pretty printer *)
val pp_tree : tree -> string


(**************)
(* Extraction *)
(**************)

(* Kind of recursion for extracted functions *)
type recursion_style =
  | StructRec of int (* Argument number, starting from 1 *)
  | FixCount

(* Extraction environment 
   This environment is used for one extraction command.
   One function or several mutualy recursive functions can be extracted.
   The mode of some other predicates can be given but they wont be extracted.
*)
type extract_env = {
  (* List of modes given of every predicates. If a predicate is not present in
     this list, we assume that it is already extracted in full mode. *)
  extr_modes : (Id.t * mode list) list;
  (* List of predicates that will be extracted. A mode must be given for them 
     in extr_modes. The optional ident is the extracted function name. 
     The boolean flag must be true for relaxed extraction (with
     pattern ordering in pattern matchings. Recursion style can be set when
     extracting to Coq. If it is not defined, it is supposed to be 
     StructRec 1. *)
  extr_extractions : (Id.t * (Id.t option * bool * recursion_style option)) 
                                                                           list;
  (* List of specification of the extracted predicates. *)
  extr_specs : (Id.t * spec) list;
  (* List of predicate trees built from the specification. *)
  extr_trees : (Id.t * tree) list;
  (* List of ml functions translated from the predicate trees. *)
  extr_mlfuns : (Id.t * ml_fun) list;
  (* List of fix functions compiled from the ml functions. *)
  extr_fixfuns : (Id.t * (fix_fun * fix_term proof_scheme)) list;
  (* Environment for the host language stuff. *)
  extr_henv : host_env;
  (* Functions for the host language stuff. *)
  extr_hf : host_functions;
  (* Info for fixpoints generation. Ids are the spec id & the fun name. *)
  (* bool : has the function been completed with option type? This can be 
            because the function is incomplete or the recursion kind is
            set to FixCount.
     recursion_style : final recursion kind of the function 
                       (may differ from the one from extr_extractions. *)
  extr_fix_env : ((Id.t * Id.t) * (bool * recursion_style)) list;
}

val extr_get_modes : extract_env -> Id.t -> mode list
val extr_get_spec : extract_env -> Id.t -> spec
val extr_get_spec_ord : extract_env -> Id.t -> bool
val extr_get_tree : extract_env -> Id.t -> tree
val extr_get_mlfun : extract_env -> Id.t -> ml_fun
val extr_get_fixfun : extract_env -> Id.t -> (fix_fun * fix_term proof_scheme)

(* Gets the recursion style of a function that was specified by the user. *)
val get_user_recursion_style : extract_env -> Id.t -> recursion_style option

(* Gets the completion status of a function (for the fixpred library). *)
val fix_get_completion_status : extract_env -> Id.t -> bool
(* Gets the recursion style of a function (for the fixpred library). *)
val fix_get_recursion_style : extract_env -> Id.t -> recursion_style
(* Sets the completion status of a function (for the fixpred library). *)
val fix_set_completion_status : extract_env -> Id.t -> bool -> extract_env
(* Sets the recursion style of a function (for the fixpred library). *)
val fix_set_recursion_style : extract_env -> Id.t -> recursion_style -> extract_env


(* Tests if the recursion style of a function is FixCount. *)
val is_rec_style_count : extract_env -> Id.t -> bool

val pp_extract_env : extract_env -> string

(* Get a fake type. *)
val unknown_type : extract_env -> term_type

(* Type a term with a fake type. *)
val fake_type : extract_env -> 't -> 't typed

(* Extraction aborted because it's impossible to insert the property 
   in the tree. The string is the reason. *)
exception RelationExtractionProp of Id.t option * string
val make_trees : extract_env -> extract_env

val make_ml_funs : extract_env -> extract_env

val get_out_terms_func : extract_env -> ml_term -> ml_term list
