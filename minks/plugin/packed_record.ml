(* Elpi's ordinary record-decl has only assumption fields. A constructor
   telescope can also carry Rocq local definitions for computed parent views. *)
open Names
module Conversion = Elpi.API.Conversion
module ContextualConversion = Elpi.API.ContextualConversion
module Rocq = Elpi_plugin.Rocq_elpi_HOAS

let declaration = ContextualConversion.{
  ty = Conversion.TyName "indt-decl";
  pp_doc = (fun fmt () -> Format.pp_print_string fmt "Record telescope");
  pp = (fun fmt _ -> Format.pp_print_string fmt "Record telescope");
  constants = [];
  readback = Rocq.lp2inductive_entry;
  embed = (fun ~depth:_ _ _ _ _ -> invalid_arg "input-only record declaration");
}

let declare (elims, entry, global_univs, binders, _, implicits) =
  let open Entries in
  let fields = match entry.mind_entry_inds with
    | [{ mind_entry_lc = [constructor]; _ }] -> Term.prod_decls constructor
    | _ -> CErrors.user_err Pp.(str "Expected a single record constructor.") in
  let entry = { entry with mind_entry_record = Some None;
    mind_entry_finite = Declarations.BiFinite } in
  Global.push_context_set global_univs;
  let mind = DeclareInd.declare_mutual_inductive_with_eliminations
      ~default_dep_elim:elims entry binders implicits in
  let ind = mind, 0 in
  let flags = List.rev_map (fun field -> Record.Data.{
    pf_coercion = None; pf_instance = None;
    pf_canonical = Context.Rel.Declaration.is_local_assum field }) fields in
  let projections = Record.Internal.declare_projections ind ~kind:Decls.Definition
      ~inhabitant_id:(Id.of_string "child") flags (List.map (fun _ -> []) fields) in
  if Dumpglob.dump () then begin
    let loc = Loc.get_current_command_loc () in
    let dump kind id = Dumpglob.dump_definition (CAst.make ?loc id) false kind in
    List.iter (fun o ->
      dump "rec" o.mind_entry_typename; List.iter (dump "constr") o.mind_entry_consnames
    ) entry.mind_entry_inds;
    List.iter (fun p -> match p.Structures.Structure.proj_name with
      | Name id -> dump "proj" id | Anonymous -> ()) projections
  end;
  Record.Internal.declare_structure_entry
    (Structures.Structure.make (Global.env ()) ind projections);
  ind, global_univs

let stored_projections ind =
  let record = Structures.Structure.find (Global.env ()) ind in
  List.filter_map (fun p ->
    if p.Structures.Structure.proj_true then
      match p.proj_body with
      | Some c -> Some (GlobRef.ConstRef c)
      | None -> CErrors.user_err Pp.(str "Missing component projection " ++ Name.print p.proj_name)
    else None
  ) record.projections
