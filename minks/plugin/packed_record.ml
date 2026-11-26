(* Elpi's ordinary record-decl has only assumption fields. A constructor
   telescope can also carry Rocq local definitions for computed parent views. *)
open Names
module Conversion = Elpi.API.Conversion
module ContextualConversion = Elpi.API.ContextualConversion
module Rocq = Elpi_plugin.Rocq_elpi_HOAS

(* Retain the user's header syntax across the synchronous Elpi layout pass.
   Re-elaborate the selected fields under these binders in a native Record. *)
let header = ref None
let with_header value = Flags.with_modified_ref header (fun _ -> Some value)

let telescope = ContextualConversion.{
  ty = Conversion.TyName "term";
  pp_doc = (fun fmt () -> Format.pp_print_string fmt "Field telescope");
  pp = (fun fmt _ -> Format.pp_print_string fmt "Field telescope");
  constants = [];
  readback = Rocq.lp2constr_closed;
  embed = (fun ~depth:_ _ _ _ _ -> invalid_arg "input-only field telescope");
}

(* The native declaration entry point leaves source locations to its caller. *)
let declare_native ~atts kind decl =
  let tag = match kind with Vernacexpr.Class _ -> "class" | _ -> "rec" in
  let open Vernacexpr in
  let open Vernacentries.Preprocessed_Mind_decl in
  match Vernacentries.preprocess_inductive_decl ~atts kind [decl] with
  | Record { flags; udecl; kind; primitive_proj; records } ->
    if Dumpglob.dump () then List.iter (fun {Record.Ast.name; idbuild; cfs} ->
      (* Generated fields have no written identifier location. Locate only
         their glob entries on the record name, or the command for a fully
         generated base. Keep authored field locations and the AST intact. *)
      let fallback = match name.CAst.loc with
        | Some _ as loc -> loc
        | None -> Loc.get_current_command_loc () in
      let located node = match node.CAst.loc with
        | Some _ -> node
        | None -> CAst.make ?loc:fallback node.CAst.v in
      Dumpglob.dump_definition (located name) false tag;
      Dumpglob.dump_definition (located idbuild) false "constr";
      List.iter (fun (field, _, _) -> match field with
        | AssumExpr (n, _, _) | DefExpr (n, _, _, _) ->
          Dumpglob.dump_constraint (located n) false "proj") cfs) records;
    (match Record.definition_structure ~flags udecl kind ~primitive_proj records with
     | [GlobRef.IndRef i] -> i
     | _ -> CErrors.anomaly Pp.(str "Expected one record declaration."))
  | Inductive _ -> CErrors.anomaly Pp.(str "Expected a record declaration.")

let declare ~scoped_term name sigma telescope =
  let open Vernacexpr in
  let name, universes, binders = match !header with
    | Some ((id, universes), binders) when Id.to_string id.CAst.v = name ->
      id, universes, binders
    | _ -> CAst.make (Id.of_string name), None, [] in
  let constructor = CAst.map (Nameops.add_prefix "Make") name in
  let field_flags = { rfu_attrs = []; rfu_coercion = NoCoercion;
    rfu_instance = NoInstance; rfu_priority = None; rfu_notation = [] } in
  let rec fields env t = match EConstr.kind sigma t with
    | Constr.Lambda (n, ty, rest) ->
      fields (EConstr.push_rel (LocalAssum (n, ty)) env) rest
    | Constr.Prod (n, ty, rest) ->
      let f = AssumExpr (CAst.make n.binder_name, [], scoped_term env sigma ty) in
      (f, field_flags) :: fields (EConstr.push_rel (LocalAssum (n, ty)) env) rest
    | Constr.LetIn (n, v, ty, rest) ->
      let f = DefExpr (CAst.make n.binder_name, [],
        scoped_term env sigma v, Some (scoped_term env sigma ty)) in
      (f, field_flags) :: fields (EConstr.push_rel (LocalDef (n, v, ty)) env) rest
    | Constr.Sort _ -> []
    | _ -> CErrors.anomaly Pp.(str "Invalid Minks field telescope.") in
  let decl = ((NoCoercion, (name, universes)), (binders, None), None,
    RecordDecl (Some constructor, fields (Global.env ()) telescope,
      Some (CAst.make (Id.of_string "child")))), [] in
  let poly = CAst.make ("universes", Attributes.VernacFlagList
    [CAst.make ("polymorphic", Attributes.VernacFlagEmpty)]) in
  declare_native ~atts:[poly] Vernacexpr.Record decl

let stored_projections ind =
  let record = Structures.Structure.find (Global.env ()) ind in
  List.filter_map (fun p ->
    if p.Structures.Structure.proj_true then
      match p.proj_body with
      | Some c -> Some (GlobRef.ConstRef c)
      | None -> CErrors.user_err Pp.(str "Missing component projection " ++ Name.print p.proj_name)
    else None
  ) record.projections
