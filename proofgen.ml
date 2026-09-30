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
(*  Copyright 2012 CNAM-ENSIIE                                              *)
(*                 Catherine Dubois <dubois@ensiie.fr>                      *)
(*                 David Delahaye <david.delahaye@cnam.fr>                  *)
(*                 Pierre-Nicolas Tollitte <tollitte@ensiie.fr>             *)
(****************************************************************************)

(* Internal dependencies *)
open Ident
open Pred
open Coq_stuff
open Minimlgen
open Reltacs

(* Rocq dependencies *)
open Constr
open Names
open Libnames
open Util

let build_ind_scheme fun_name fun_ind_name =
  (* fun_name is the identifier of the function we are working on
     fun_ind_name is the name of the induction hypothesis *)
  (* Get the name that FunInd give to the induction hypothesis. Copy-pasted from FunInd's files. *)
  let name = Namegen.next_ident_away_in_goal (Global.env ()) (Id.of_string "H") (Id.Set.empty) in
  if false then Printf.printf "\n%s\n%!" (Id.to_string name) else (); (* TODO[29/09/2026] debugging *)
  let ref_func = qualid_of_ident fun_name in
  let ih_ind = CAst.make (fun_ind_name) in
  let make_fscheme () =
    Funind_plugin.Gen_principle.build_scheme
      [ih_ind, ref_func, UnivGen.QualityOrSet.Qual (Sorts.Quality.QConstant Sorts.Quality.QProp)] in
  begin
    try make_fscheme () with Funind_plugin.Gen_principle.No_graph_found ->
      let () = Funind_plugin.Gen_principle.make_graph (Nametab.global ref_func) in
      make_fscheme ()
  end
  ;
  name

let build_correct_lemma (out_name: Id.t) env (id: Id.t) fixfun =
  let spec = extr_get_spec env id in
  let in_names = List.map Id.to_string fixfun.fixfun_args in
  let in_types = List.map get_coq_type (get_in_types (env, id)) in
  let out_type = get_out_type true (env, id) in
  let func = find_coq_constr_i fixfun.fixfun_name in
  let mode = List.hd (extr_get_modes env id) in
  let full = is_full_extraction mode in
  let compl = fix_get_completion_status env fixfun.fixfun_name in
  let tru = find_coq_constr_s "Corelib.Init.Datatypes.true" in
  let some = find_coq_constr_s "Corelib.Init.Datatypes.Some" in
  
  (* rels for the prem definition *)
  let in_start = if full then 1 else 2 in
  let _, in_rels = List.fold_right ( fun _ (i, rels) -> 
    (i+1, (mkRel i)::rels) ) in_names (in_start, []) in
  let out_term = if full then tru 
    else if compl then mkApp (some, [|out_type; mkRel 1|]) else mkRel 1 in

  (* rels for the concl definition (the premise add 1 index) *)
  let in_start' = if full then 2 else 3 in
  let _, in_rels' = List.fold_right ( fun _ (i, rels) -> 
    (i+1, (mkRel i)::rels) ) in_names (in_start', []) in
  let out_term' = if full then [] else [mkRel 2] in

  let eq = find_coq_constr_s "Corelib.Init.Logic.eq" in
  let pred = find_coq_constr_i spec.spec_name in
  let prem = 
    mkApp (eq, [|out_type; mkApp (func, Array.of_list in_rels); out_term|]) in
  let concl = mkApp (pred, Array.of_list (in_rels'@out_term')) in
  let cstr = mkProd(Context.anonR, prem, concl) in
  let cstr = mkProd (Context.nameR out_name, out_type, cstr) in
  let cstr = List.fold_right2 (fun n t c ->
    mkProd (Context.nameR (Id.of_string n), t, c)
  ) in_names in_types cstr in
  cstr

let gen_correction_proof env (id: Id.t) : unit =
  let id_po : Id.t = fresh_id "po" in
  let (fixfun, ps) = extr_get_fixfun env id in
  let mode = List.hd (extr_get_modes env id) in
  let compl = fix_get_completion_status env fixfun.fixfun_name in
  let full = is_full_extraction mode in
  
  (* Identifier for the induction scheme *)
  let fixfun_ind = fresh_id (Id.to_string fixfun.fixfun_name ^ "_ind") in
  (* Identifier for the lemma's name *)
  let fixfun_correct = fresh_id (Id.to_string fixfun.fixfun_name ^ "_correct") in
  (* TODO[30/09/2026] put these two directly in extr_get_fixfun? *)
  (* TODO[30/09/2026] warning if this is not fresh? *)

  (* Functional scheme, and its identifier *)
  let id_rec = build_ind_scheme fixfun.fixfun_name fixfun_ind in
  
  (* Lemma building *)
  let cstr = build_correct_lemma id_po env id fixfun in

  (* Proof registering *)
  let proof_register ps : unit =
    let info = Declare.Info.make () in
    let cinfo = Declare.CInfo.make ~name:fixfun_correct ~typ:(EConstr.of_constr cstr) () in
    let lemma = Declare.Proof.start ~cinfo ~info (Evd.from_env (Global.env())) in
    let lemma = make_proof_simple fixfun_ind id_po id_rec fixfun_correct (env, id) lemma ps in
    let (_ : _ list) = Declare.Proof.save_regular ~proof:lemma ~opaque:Vernacexpr.Transparent ~idopt:None in
    () in

  if (not compl) && (not full) then
    proof_register ps
  else
    ()


