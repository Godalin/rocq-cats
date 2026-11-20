open Names
open Constrexpr

type parameter = {
  name : Id.t;
  binder : local_binder_expr;
}

type origin = inductive * int

type role =
  | Mixin
  | Value of origin * Glob_term.binding_kind

type mixin_signature = {
  carrier_kind : Glob_term.binding_kind;
  roles : role list;
}

type inherited = {
  parameter : parameter;
  role : role;
  shared : bool;
}

type dependency = {
  reference : GlobRef.t;
  arguments : Id.t list;
  instance : instance_expr option;
  parameter : parameter;
  shared : bool;
}

let parameter_roles = Summary.ref ~name:"minks-parameter-roles" Indmap_env.empty

let save_roles =
  Libobject.declare_object
    (Libobject.superglobal_object_nodischarge "MINKS-PARAMETER-ROLES"
      ~cache:(fun (ind, roles) -> parameter_roles := Indmap_env.add ind roles !parameter_roles)
      ~subst:(Some (fun (subst, (ind, signature)) ->
        let subst_ind = Mod_subst.subst_ind subst in
        let roles = List.map (function
          | Mixin -> Mixin
          | Value ((owner, pos), kind) -> Value ((subst_ind owner, pos), kind))
          signature.roles in
        subst_ind ind, { signature with roles })))

let error message = CErrors.user_err (Pp.str message)

let read_parent parent =
  match parent.CAst.v with
  | CRef (name, instance) -> name, instance
  | _ -> error "Expected the name of a parent mixin."

let qualify reference = Libnames.qualid_of_path (Nametab.path_of_global reference)

let variable id = CAst.make (CRef (Libnames.qualid_of_ident id, None))

let parameter name kind ty =
  let binder = CLocalAssum ([CAst.make (Name name)], None, kind, ty) in
  { name; binder }

let raw_level level =
  if Univ.Level.is_set level then CSet else CRawType level

let quality_syntax qualities quality =
  match Sorts.Quality.var_index quality with
  | Some i -> qualities.(i)
  | None -> CRawQuality quality

let level_syntax levels level =
  match Univ.Level.var_index level with
  | Some i -> levels.(i)
  | None -> Glob_term.UNamed (raw_level level)

let instance_syntax (qualities, levels) instance =
  let qs, us = UVars.Instance.to_array instance in
  if Array.length qs = 0 && Array.length us = 0 then None
  else
    Some (Array.to_list (Array.map (quality_syntax qualities) qs),
          Array.to_list (Array.map (level_syntax levels) us))

let raw_sort instance sort =
  let print ~universes =
    Constrextern.extern_sort ~universes ~qualities:true Evd.empty sort
  in
  let sort =
    match instance with
    | None -> print ~universes:false
    | Some (qualities, levels) ->
      let quality, universes = print ~universes:true in
      let quality = Option.map (function
        | CRawQuality q -> quality_syntax qualities q
        | q -> q) quality
      in
      let universes = match universes with
        | Glob_term.UAnonymous _ -> universes
        | Glob_term.UNamed terms ->
          let level (u, offset) =
            match u with
            | CRawType raw ->
              (match level_syntax levels raw with
               | Glob_term.UNamed name -> Some (name, offset)
               | Glob_term.UAnonymous _ -> None)
            | _ -> Some (u, offset)
          in
          let explicit = List.filter_map level terms in
          if List.length explicit = List.length terms then Glob_term.UNamed explicit
          else snd (print ~universes:false)
      in
      quality, universes
  in
  CSort sort

let carrier_sort instance sort = CAst.make (raw_sort instance sort)

let value_type env instance names ty =
  let flags = PrintingFlags.make_raw (PrintingFlags.current_ignore_raw ()) in
  let flags = { flags with detype = {
    flags.detype with universes = Option.has_some instance
  } } in
  let ty = Vars.substl (List.map Constr.mkVar names) ty in
  let syntax = Constrextern.extern_constr ~flags env (Evd.from_env env) (EConstr.of_constr ty) in
  match instance with
  | None -> syntax
  | Some (qs, us) ->
    let quality = function CRawQuality q -> quality_syntax qs q | q -> q in
    let level = function
      | Glob_term.UNamed (CRawType u) -> level_syntax us u
      | u -> u in
    let reference (q, instance) =
      q, Option.map (fun (qualities, levels) -> List.map quality qualities, List.map level levels)
        instance in
    let rec rewrite () expression =
      let expression =
        Constrexpr_ops.map_constr_expr_with_binders (fun _ () -> ()) rewrite () expression in
      CAst.map (function
        | CRef (q, inst) -> let q, inst = reference (q, inst) in CRef (q, inst)
        | CAppExpl (head, args) -> CAppExpl (reference head, args)
        | CProj (explicit, head, args, body) -> CProj (explicit, reference head, args, body)
        | CSort (q, Glob_term.UNamed universe) ->
          let levels = List.map (fun (u, offset) ->
            match level (Glob_term.UNamed u) with
            | Glob_term.UNamed name -> name, offset
            | Glob_term.UAnonymous _ ->
              error "A named universe is required in this inherited value type."
          ) universe in
          CSort (Option.map quality q, Glob_term.UNamed levels)
        | term -> term) expression
    in
    rewrite () syntax

let dependency_type ty names =
  let head, operands = Constr.decompose_app_list ty in
  let reference, instance =
    match Constr.kind head with
    | Ind (ind, instance) -> GlobRef.IndRef ind, instance
    | Const (constant, instance) -> GlobRef.ConstRef constant, instance
    | _ -> error "Expected a parent mixin parameter indexed by earlier parameters."
  in
  let argument operand =
    match Constr.kind operand with
    | Rel i -> List.nth names (i - 1)
    | _ -> error "Mixin dependencies must use earlier parameters directly."
  in
  reference, instance, List.map argument operands

let merge_instance reference inherited incoming =
  match inherited, incoming with
  | None, instance | instance, None -> instance
  | Some (qs, us), Some (qs', us') ->
    let equal first second =
      let term args = CAst.make (CRef (qualify reference, Some args)) in
      Constrexpr_ops.constr_expr_eq (term first) (term second)
    in
    let choose anonymous eq first second =
      if anonymous first then second
      else if anonymous second || eq first second then first
      else error "Inherited universe instances disagree for a shared mixin."
    in
    let quality =
      choose (function CQAnon _ -> true | _ -> false)
        (fun q q' -> equal ([q], []) ([q'], []))
    in
    let level =
      choose (function Glob_term.UAnonymous _ -> true | _ -> false)
        Constrexpr_ops.univ_level_expr_eq
    in
    Some (List.map2 quality qs qs', List.map2 level us us')

let dependency_parameter reference name instance arguments =
  let ty = CAst.make (CAppExpl ((qualify reference, instance), List.map variable arguments)) in
  parameter name (Generalized (Glob_term.MaxImplicit, true)) ty

let add_dependency env reserved dependencies reference instance arguments =
  let same d = Environ.QGlobRef.equal env d.reference reference in
  match List.find_opt same dependencies with
  | Some d ->
    if not (List.equal Id.equal d.arguments arguments) then
      error "Inherited parents select different witnesses for the same mixin.";
    let instance = merge_instance reference d.instance instance in
    let name = d.parameter.name in
    let parameter = dependency_parameter reference name instance arguments in
    let updated = List.map (fun item ->
      if same item then { d with instance; parameter; shared = true } else item
    ) dependencies in
    updated, name
  | None ->
    let base = Libnames.qualid_basename (qualify reference) in
    let base = Id.of_string (String.uncapitalize_ascii (Id.to_string base)) in
    let name = Namegen.next_ident_away base reserved in
    let parameter = dependency_parameter reference name instance arguments in
    { reference; arguments; instance; parameter; shared = false } :: dependencies, name

let binder_id ann =
  match Context.binder_name ann with
  | Name name -> name
  | Anonymous -> Id.of_string "x"

let inheritance parents =
  let env = Global.env () in
  let inherit_parent (carrier, dependencies, values, order) (parent, syntax_instance) =
    let reference = Nametab.locate parent in
    let signature =
      match reference with
      | GlobRef.IndRef ind ->
        (match Indmap_env.find_opt ind !parameter_roles with
         | Some signature -> signature
         | None -> error "Parent must be declared with Minks.Mixin.")
      | _ -> error "Parent must be declared with Minks.Mixin."
    in
    let ty, context = Typeops.type_of_global_in_context env reference in
    let instance = Option.map (fun (qs, us) ->
      if (List.length qs, List.length us) <> UVars.AbstractContext.size context then
        error "Wrong number of universe arguments for the parent mixin.";
      Array.of_list qs, Array.of_list us) syntax_instance
    in
    let ann, carrier_ty, params =
      match Constr.kind ty with
      | Prod (ann, ty, rest) -> ann, ty, rest
      | _ -> error "A parent mixin must have a carrier parameter."
    in
    let carrier, carrier_kind =
      match carrier with
      | Some carrier -> carrier
      | None ->
        let ty = match Constr.kind carrier_ty with
          | Sort sort -> carrier_sort instance sort
          | Ind (ind, levels) ->
            let levels = Option.bind instance (fun i -> instance_syntax i levels) in
            CAst.make (CRef (qualify (GlobRef.IndRef ind), levels))
          | _ -> error "The carrier parameter of a parent mixin must be a sort or a complete structure."
        in
        let kind = signature.carrier_kind in
        parameter (binder_id ann) (Default kind) ty, kind
    in
    let used order = Id.Set.of_list (carrier.name :: order) in
    let note name order = if List.exists (Id.equal name) order then order else name :: order in
    let rec add_parameters dependencies values order names roles rest =
      match roles, Constr.kind rest with
      | Mixin :: roles, Prod (_, ty, rest) ->
        let dependency, levels, arguments = dependency_type ty names in
        let levels = Option.bind instance (fun i -> instance_syntax i levels) in
        let dependencies, name =
          add_dependency env (used order) dependencies dependency levels arguments
        in
        add_parameters dependencies values (note name order) (name :: names) roles rest
      | Value (origin, kind) :: roles, Prod (ann, ty, rest) ->
        let ty = value_type env instance names ty in
        let same ((owner, pos), _, _, _) =
          let other, other_pos = origin in
          pos = other_pos && Environ.QInd.equal env owner other in
        let values, name =
          match List.find_opt same values with
          | Some (_, _, parameter, _) ->
            let expected = parameter.binder in
            let actual = CLocalAssum ([CAst.make (Name parameter.name)], None,
              Default kind, ty) in
            if not (Constrexpr_ops.local_binder_eq expected actual) then
              error "Inherited value parameters have incompatible types.";
            List.map (fun ((origin, kind, parameter, _) as entry) ->
              if same entry then origin, kind, parameter, true else entry) values,
            parameter.name
          | None ->
            let name = Namegen.next_ident_away (binder_id ann) (used order) in
            let parameter = parameter name (Default kind) ty in
            (origin, kind, parameter, false) :: values, name
        in
        add_parameters dependencies values (note name order) (name :: names) roles rest
      | [], Sort _ ->
        let dependencies, name = add_dependency env (used order) dependencies
            reference syntax_instance (List.rev names) in
        Some (carrier, carrier_kind), dependencies, values, note name order
      | _ -> error "The parent mixin parameters do not match its Minks declaration."
    in
    add_parameters dependencies values order [carrier.name] signature.roles params
  in
  let carrier, dependencies, values, order =
    List.fold_left inherit_parent (None, [], [], []) parents in
  let inherited = List.rev_map (fun name ->
    match List.find_opt (fun (d : dependency) -> Id.equal d.parameter.name name) dependencies with
    | Some d -> { parameter = d.parameter; role = Mixin; shared = d.shared }
    | None ->
      let origin, kind, parameter, shared =
        List.find (fun (_, _, p, _) -> Id.equal p.name name) values in
      { parameter; role = Value (origin, kind); shared }) order in
  let shared, others = List.partition (fun (i : inherited) -> i.shared) inherited in
  Option.get carrier, shared @ others

let parameter_kinds binders =
  List.concat_map (function
    | CLocalAssum (names, _, Default kind, _) -> List.map (fun _ -> kind) names
    | _ -> error "Mixin value parameters must be ordinary binders."
  ) binders

let add_to_declaration parents decl =
  let ((name, (binders, extra), sort, fields), notations) = decl in
  let own = parameter_kinds binders in
  if parents = [] then
    match own with
    | carrier_kind :: values -> decl, carrier_kind, [], values
    | [] -> error "A root mixin must declare a carrier parameter."
  else
    let (carrier, carrier_kind), inherited = inheritance parents in
    let binders = carrier.binder :: List.map (fun (i : inherited) -> i.parameter.binder) inherited @ binders in
    ((name, (binders, extra), sort, fields), notations),
    carrier_kind, List.map (fun i -> i.role) inherited, own

let remember reference carrier_kind inherited added =
  let ind = match reference with
    | GlobRef.IndRef ind -> ind
    | _ -> error "A mixin must be a record declaration." in
  let roles = inherited @ List.mapi (fun pos kind -> Value ((ind, pos), kind)) added in
  Lib.add_leaf (save_roles (ind, { carrier_kind; roles }));
  List.filter_map (fun (pos, role) ->
    match role with Mixin -> None | Value _ -> Some (pos + 1)
  ) (List.mapi (fun pos role -> pos, role) roles)
