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

(* Rocq dependencies *)
open Names

(* Host is the host language, Rocq. In order to generate 
   functions, we need to keep information from this language. Some part 
   (mostly typing information) is kept into the AST we manipulate by compiling 
   the predicates and the remaining part is kept into an host environment. 
*)

(* Find a Coq constr from its name (as an ident or a string) *)
val find_coq_constr_i : Id.t -> Constr.constr
val find_coq_constr_s : string -> Constr.constr

(* Host types. Type information for a term. This is kept into the AST. *)
type host_term_type = Constr.types option

(* Host environment. *)
type host_env = {
  ind_refs : (Id.t * Libnames.qualid) list;
  ind_grefs : (Id.t * Names.GlobRef.t) list;
  cstrs : (Id.t * Constr.constr) list;
}

(* Functions to manipulate Rocq data. *)
val rocq_get_fake_type : unit -> host_term_type
val rocq_get_bool_type : unit -> string list * host_term_type
