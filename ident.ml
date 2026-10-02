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

let fresh_id (base_name: string) : Id.t =
  let id = Namegen.next_ident_away_in_goal (Global.env()) (Id.of_string base_name) !to_avoid in
  to_avoid := Id.Set.add id !to_avoid;
  id

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

(* Identifiers for Rocq's constructors *)
(* TODO[02/10/2026] Use Rocq.lib_ref instead *)
let id_O = ref (Id.of_string "bug")
let create_id_O () : unit =
  id_O := fresh_id "O"
let get_id_O () : Id.t =
  !id_O

let id_S = ref (Id.of_string "bug")
let create_id_S () : unit =
  id_S := fresh_id "S"
let get_id_S () : Id.t =
  !id_S

let id_true = ref (Id.of_string "bug")
let create_id_true () : unit =
  id_true := fresh_id "true"
let get_id_true () : Id.t =
  !id_true

let id_false = ref (Id.of_string "bug")
let create_id_false () : unit =
  id_false := fresh_id "false"
let get_id_false () : Id.t =
  !id_false

let id_Some = ref (Id.of_string "bug")
let create_id_Some () : unit =
  id_Some := fresh_id "Some"
let get_id_Some () : Id.t =
  !id_Some

let id_None = ref (Id.of_string "bug")
let create_id_None () : unit =
  id_None := fresh_id "None"
let get_id_None () : Id.t =
  !id_None

let init_seen_id () : unit =
  reset_seen_id ();
  create_id_O ();
  create_id_S ();
  create_id_true ();
  create_id_false ();
  create_id_Some ();
  create_id_None ()
