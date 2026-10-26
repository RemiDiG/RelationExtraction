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
(*  Copyright 2011, 2012, 2014 CNAM-ENSIIE                                  *)
(*                 Catherine Dubois <dubois@ensiie.fr>                      *)
(*                 David Delahaye <david.delahaye@cnam.fr>                  *)
(*                 Pierre-Nicolas Tollitte <tollitte@ensiie.fr>             *)
(****************************************************************************)

(* Internal dependencies *)
open Host_stuff
open Ident
open Pred
open Coq_stuff
open Host2spec
open Fixpred
open Fixpointgen

(* Rocq dependencies *)
open Util
open Pp
open Declarations
open Nametab

(************************)
(* Predicate extraction *)
(************************)

(* TODO: order specifications (by dependency) before doing a fixpoint extraction. *)

let id_of_string_option s_opt = match s_opt with
  | None -> None
  | Some s -> Some (fresh_id s)

let rec find_func_name ind_ref modes = match modes with
  | (fn, ind_ref', _, rs)::modes ->
      if ind_ref == ind_ref' then (id_of_string_option fn, rs)
      else find_func_name ind_ref modes
  | [] -> raise Not_found


(* Extraction of dependencies *)
let extract_dependencies ~(opaque_access : Global.indirect_accessor) (henv : host_env) : unit  =
  (* We need a list of references; Extraction missing an entry point with GlobRef.t ?? *)
  let refl = List.map (fun (_, c) -> 
    match Constr.kind c with
      | Constr.Construct _ | Constr.Const _ ->
         Constrextern.extern_reference Names.Id.Set.empty (fst (Constr.destRef c))
      | _ -> assert false
  ) henv.cstrs in
  Extraction_plugin.Extract_env.full_extraction ~opaque_access:opaque_access None refl


let id_of_globref (ind_glb : Names.GlobRef.t) : Names.Id.t =
  let ind = Globnames.destIndRef ind_glb in
  let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
  oib.mind_typename

(* Main routine *)
let extract_relation_common ord ind_ref modes =
  let debug = false in
  
  (* Initialize identifiers for some Rocq constructors *)
  let () = init_seen_id () in
  
  (* Initial henv *)
  let ind_refs, ind_grefs = List.split (List.map (fun (_, ind_ref, _, _) ->
    let ind_glb = global ind_ref in
    let id = id_of_globref ind_glb in
    (id, ind_ref), (id, ind_glb)) modes) in
  let henv = { ind_refs = ind_refs; ind_grefs = ind_grefs; cstrs = [] } in
  
  (* Extractions *)
  let extractions = List.map (fun ind_ref ->
    let id = id_of_globref (global ind_ref) in
    let (fn, rs) = find_func_name ind_ref modes in
    id, (fn, ord, rs)) ind_ref in

  (* Modes *)
  let modes = List.map (fun (_, ind_ref, mode, _) -> (* TODO[26/10/2026] half of modes unused? *)
    let ind_glb = global ind_ref in
    let id = id_of_globref ind_glb in
    (id, [make_mode ind_glb (Some (adapt_mode ind_ref mode))])) modes in
  let eq_modes = [[MSkip;MInput;MOutput]; [MSkip;MOutput;MInput]; [MSkip;MInput;MInput]] in
  let modes = (Names.Id.of_string "eq", eq_modes)::modes in (* TODO[29/09/2026] "eq" ... *)

  (* Compilation *)
  let empty_env = {
    extr_modes = modes;
    extr_extractions = extractions;
    extr_specs = [];
    extr_trees = [];
    extr_mlfuns = [];
    extr_fixfuns = [];
    extr_henv = henv;
    extr_fix_env = [];
  } in
  let env = find_specifications empty_env in
  if debug then Printf.eprintf "%s\n" (pp_extract_env env) else ();
  let env = try Pred.make_trees env with
    | RelationExtractionProp (Some p_id, s) -> CErrors.user_err
      (str ("[RelationExtraction] Extraction failed at " ^ Names.Id.to_string p_id ^ ": " ^ s))
    | RelationExtractionProp (None, s) -> CErrors.user_err
      (str ("[RelationExtraction] Extraction failed: " ^ s))
  in
  if debug then Printf.eprintf "%s\n" (pp_extract_env env) else ();
  let env = Pred.make_ml_funs env in
  if debug then Printf.eprintf "%s\n" (pp_extract_env env) else ();

  (* Reset the created identifiers, to not be polluted by a previous run. *)
  let () = reset_seen_id () in
  
  env

let extract_relation_miniml ~opaque_access dep ord ind_ref modes =
  let env = extract_relation_common ord ind_ref modes in
  (* Before generating the MiniML code, we first extract all the dependences *)
  let () = if dep then extract_dependencies ~opaque_access:opaque_access env.extr_henv else () in
  Minimlgen.gen_miniml env

let relation_extraction_single_bool (b : bool) ~opaque_access modes =
  let (_, ind_ref, _, _) = List.hd modes in
  extract_relation_miniml ~opaque_access:opaque_access false b [ind_ref] modes
let relation_extraction_single = relation_extraction_single_bool false
let relation_extraction_single_order = relation_extraction_single_bool true

let relation_extraction_bool (b : bool) ~opaque_access modes =
  let ind_refs = List.map (fun (_, ind_ref, _, _) -> ind_ref) modes in
  extract_relation_miniml ~opaque_access:opaque_access true b ind_refs modes
let relation_extraction = relation_extraction_bool false
let relation_extraction_order = relation_extraction_bool true

let relation_extraction_fixpoint_bool (b : bool) modes =
  let ind_refs = List.map (fun (_, ind_ref, _, _) -> ind_ref) modes in
  let env = extract_relation_common b ind_refs modes in
  let env = build_all_fixfuns env in
  gen_fixpoint env
let relation_extraction_fixpoint = relation_extraction_fixpoint_bool false
let relation_extraction_fixpoint_order = relation_extraction_fixpoint_bool true

(* DEBUG HINT: Displaying a constant idr:
let cstr = constr_of_global (global idr) in
constr_display cstr; let cst = destConst cstr in
let cst_body = Global.lookup_constant cst in
let cstr = match cst_body.Declarations.const_body with 
  Def cs -> Declarations.force cs in
constr_display cstr *)

let extraction_print str =
  Printf.printf "%s\n" str
