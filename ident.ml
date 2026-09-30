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

(***************)
(* Identifiers *)
(***************)

(* Return a fresh name based on a scheme, using Rocq's implementation
   We keep in memory the names created but not yet given to Rocq *)
let to_avoid = ref Id.Set.empty

let fresh_id_helper (base_name: string) : Id.t =
  let id = Namegen.next_ident_away_in_goal (Global.env()) (Id.of_string base_name) !to_avoid in
  to_avoid := Id.Set.add id !to_avoid;
  id

let fresh_id (base_name: string) : Id.t =
  fresh_id_helper base_name

let reset_seen_id () : unit =
  to_avoid := Id.Set.empty

(* TODO[25/09/2026] internally None is the empty string, that is not valid as as identifier.
   We use Name to patch it quickly, to improve. *)
let name_to_string (n : Name.t) : string =
  match n with
  | Anonymous -> ""
  | Name id -> Id.to_string id

(* TODO[29/09/2026] Use Name instead of option?? *)
let name_to_option_id (n : Name.t) : Id.t option =
  match n with
  | Anonymous -> None
  | Name i -> Some i
