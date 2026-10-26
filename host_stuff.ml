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
open Libnames
open Nametab

let find_coq_constr_s (s : string) =
  UnivGen.constr_of_monomorphic_global (Global.env ()) (locate (qualid_of_string s))

let find_coq_constr_i (i : Id.t) =
  find_coq_constr_s (Id.to_string i)


(* Host types. Type information for a term. This is kept into the AST. *)
type host_term_type = Constr.types option

(* Host environment. *)
type host_env = {
  ind_refs : (Id.t * Libnames.qualid) list;
  ind_grefs : (Id.t * Names.GlobRef.t) list;
  cstrs : (Id.t * Constr.constr) list;
}

(* Functions for host langage manipulations. *)
let coq_get_fake_type () = None
let coq_get_bool_type () = (["true"; "false"], Some (find_coq_constr_s "Corelib.Init.Datatypes.bool"))
