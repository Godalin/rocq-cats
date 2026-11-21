open Names
open Constrexpr

type parameter = {
  name : Id.t;
  binder : local_binder_expr;
}

type role =
  | Mixin of Id.t option
  | Value of Glob_term.binding_kind

type dependency = {
  key : Id.t option;
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
      ~subst:(Some (fun (subst, (ind, roles)) -> Mod_subst.subst_ind subst ind, roles)))

type combination = {
  constructor : GlobRef.t;
  components : Id.t list;
}

let combinations = Summary.ref ~name:"minks-combinations" Indmap_env.empty

let save_combination =
  Libobject.declare_object
    (Libobject.superglobal_object_nodischarge "MINKS-COMBINATION"
      ~cache:(fun (ind, shape) -> combinations := Indmap_env.add ind shape !combinations)
      ~subst:(Some (fun (subst, (ind, shape)) ->
        Mod_subst.subst_ind subst ind,
        { shape with constructor = Globnames.subst_global_reference subst shape.constructor })))

let error message = CErrors.user_err (Pp.str message)

let read_parent parent =
  match parent.CAst.v with
  | CRef (name, instance) -> name, instance, []
  | CApp ({ CAst.v = CRef (name, instance); _ }, args) -> name, instance, args
  | CAppExpl _ -> error "Pass ordinary mixin parameters without @ in extends."
  | _ -> error "Expected a parent mixin applied to its ordinary parameters."

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

let binder_name reference reserved key =
  let base = match key with
    | Some name -> name
    | None ->
      let name = Libnames.qualid_basename (qualify reference) in
      Id.of_string (String.uncapitalize_ascii (Id.to_string name)) in
  Namegen.next_ident_away base reserved

let add_dependency env reserved dependencies reference instance arguments key =
  let same d =
    Environ.QGlobRef.equal env d.reference reference &&
    (match d.key, key with Some x, Some y -> Id.equal x y | _ -> true) in
  match List.filter same dependencies with
  | [d] ->
    if not (List.equal Id.equal d.arguments arguments) then
      error "Inherited parents select different witnesses for the same mixin.";
    let instance = merge_instance reference d.instance instance in
    let name = d.parameter.name in
    let parameter = dependency_parameter reference name instance arguments in
    let key = match d.key with Some _ -> d.key | None -> key in
    let updated = List.map (fun item ->
      if same item then { d with key; instance; parameter; shared = true } else item
    ) dependencies in
    updated, name
  | [] ->
    let name = binder_name reference reserved key in
    let parameter = dependency_parameter reference name instance arguments in
    { key; reference; arguments; instance; parameter; shared = false } :: dependencies, name
  | _ -> error "More than one selected component matches an inherited mixin."

let argument_name own term =
  match term.CAst.v with
  | CRef (name, None) when Libnames.qualid_is_ident name ->
    let id = Libnames.qualid_basename name in
    if Id.Set.mem id own then id
    else error ("Unknown ordinary mixin parameter: " ^ Id.to_string id ^ ".")
  | _ -> error "Parent ordinary arguments must name parameters declared on the child."

let read_arguments own args =
  List.partition_map (fun (term, explicit) ->
    let value = argument_name own term in
    match Option.map (fun arg -> arg.CAst.v) explicit with
    | None -> Either.Left value
    | Some (ExplByName key) -> Either.Right (key, value)
    | Some (ExplByPos _) -> error "Supply an implicit ordinary parameter by name."
  ) args

let take_argument kind ann positional named =
  let binder = Context.binder_name ann in
  let name = match binder with Name id -> Id.to_string id | Anonymous -> "_" in
  match kind with
  | Glob_term.Explicit ->
    (match positional with
     | value :: rest -> value, rest, named
     | [] -> error ("Missing explicit ordinary parameter " ^ name ^ " of the parent mixin."))
  | Glob_term.NonMaxImplicit | Glob_term.MaxImplicit ->
    (match binder with
     | Name id ->
       (match List.assoc_opt id named with
        | Some value -> value, positional, List.remove_assoc id named
        | None -> error ("Pass implicit ordinary parameter " ^ name ^ " by name."))
     | Anonymous -> error "An implicit ordinary parameter used in extends must have a name.")

let expand_combination env reference syntax_instance instance shape names dependencies reserved =
  let ctor_ty, _ = Typeops.type_of_global_in_context env shape.constructor in
  let rec skip count ty =
    if count = 0 then ty else
    match Constr.kind ty with
    | Prod (_, _, rest) -> skip (count - 1) rest
    | _ -> error "Invalid fixed parameters in the exported mixin."
  in
  let rec expand dependencies reserved names keys ty =
    match keys, Constr.kind ty with
    | key :: keys, Prod (_, ty, rest) ->
      let component, levels, arguments = dependency_type ty names in
      let levels = Option.bind instance (fun i -> instance_syntax i levels) in
      let dependencies, name =
        add_dependency env reserved dependencies component levels arguments (Some key) in
      expand dependencies (Id.Set.add name reserved) (name :: names) keys rest
    | [], _ -> dependencies, reserved, List.rev names
    | _ -> error "The exported mixin does not match its component metadata."
  in
  let ty = skip (List.length names) ctor_ty in
  let deps, reserved, args = expand dependencies reserved names shape.components ty in
  let name = binder_name reference reserved None in
  let value = CAst.make (CAppExpl ((qualify shape.constructor, syntax_instance), List.map variable args)) in
  let binder = CLocalDef (CAst.make (Name name), None, value, None) in
  deps, Id.Set.add name reserved, binder

let inheritance own parents =
  let env = Global.env () in
  let inherit_parent (dependencies, reserved, views) (parent, syntax_instance, args) =
    let positional, named = read_arguments own args in
    let reference = Nametab.locate parent in
    let ind = match reference with
      | GlobRef.IndRef ind -> ind
      | _ -> error "Expected a registered Minks mixin." in
    let roles = match Indmap_env.find_opt ind !parameter_roles with
      | Some roles -> roles
      | None -> error "Expected a registered Minks mixin." in
    let combination = Indmap_env.find_opt ind !combinations in
    let ty, context = Typeops.type_of_global_in_context env reference in
    let instance = Option.map (fun (qs, us) ->
      if (List.length qs, List.length us) <> UVars.AbstractContext.size context then
        error "Wrong number of universe arguments for the parent mixin.";
      Array.of_list qs, Array.of_list us) syntax_instance
    in
    let add dependencies reserved reference instance arguments key =
      let dependencies, name =
        add_dependency env reserved dependencies reference instance arguments key in
      dependencies, Id.Set.add name reserved, name
    in
    let rec add_parameters dependencies reserved names roles rest positional named =
      match roles, Constr.kind rest with
      | _, LetIn (_, value, _, rest) ->
        add_parameters dependencies reserved names roles (Vars.subst1 value rest) positional named
      | Mixin key :: roles, Prod (_, ty, rest) ->
        let dependency, levels, arguments = dependency_type ty names in
        let levels = Option.bind instance (fun i -> instance_syntax i levels) in
        let dependencies, reserved, name = add dependencies reserved dependency levels arguments key in
        add_parameters dependencies reserved (name :: names) roles rest positional named
      | Value kind :: roles, Prod (ann, _, rest) ->
        let name, positional, named = take_argument kind ann positional named in
        add_parameters dependencies reserved (name :: names) roles rest positional named
      | [], Sort _ ->
        if positional <> [] || named <> [] then
          error "Unexpected or repeated ordinary argument in extends.";
        (match combination with
         | None ->
           let deps, reserved, _ =
             add dependencies reserved reference syntax_instance (List.rev names) None in
           deps, reserved, views
         | Some shape ->
           let deps, reserved, view =
             expand_combination env reference syntax_instance instance shape names dependencies reserved in
           deps, reserved, view :: views)
      | _ -> error "The parent mixin parameters do not match its Minks declaration."
    in
    add_parameters dependencies reserved [] roles ty positional named
  in
  let dependencies, _, views = List.fold_left inherit_parent ([], own, []) parents in
  let shared, others = List.partition (fun d -> d.shared) (List.rev dependencies) in
  shared @ others, List.rev views

let ordinary_parameters binders =
  List.concat_map (function
    | CLocalAssum (names, relevance, Default kind, ty) ->
      List.map (fun name ->
        (name.CAst.v, (CLocalAssum ([name], relevance, Default kind, ty), Value kind))
      ) names
    | _ -> error "Mixin value parameters must be ordinary binders."
  ) binders

let order_parameters ordinary inherited =
  let positions =
    List.fold_left (fun (pos, indexes) (name, _) ->
      let indexes = match name with
        | Name id -> Id.Map.add id pos indexes
        | Anonymous -> indexes in
      pos + 1, indexes
    ) (0, Id.Map.empty) ordinary |> snd
  in
  (* Keep the child's ordinary parameter order when inserting witnesses. *)
  let rec emit_through last index ordinary output =
    if index > last then index, ordinary, output
    else match ordinary with
    | (_, parameter) :: rest -> emit_through last (index + 1) rest (parameter :: output)
    | [] -> assert false
  in
  let _, ordinary, inherited =
    List.fold_left (fun (index, ordinary, output) dependency ->
      let last = List.fold_left (fun last name ->
        match Id.Map.find_opt name positions with None -> last | Some i -> max last i
      ) (-1) dependency.arguments in
      let index, ordinary, output = emit_through last index ordinary output in
      index, ordinary, (dependency.parameter.binder, Mixin dependency.key) :: output
    ) (0, ordinary, []) inherited in
  List.rev_append inherited (List.map snd ordinary)

let add_to_declaration parents decl =
  let ((name, (binders, extra), sort, fields), notations) = decl in
  let ordinary = ordinary_parameters binders in
  let own = List.fold_left (fun set (name, _) ->
    match name with Name id -> Id.Set.add id set | Anonymous -> set
  ) Id.Set.empty ordinary in
  let inherited, views = inheritance own parents in
  let binders, roles = List.split (order_parameters ordinary inherited) in
  ((name, (binders @ views, extra), sort, fields), notations), roles

let remember reference roles =
  let ind = match reference with
    | GlobRef.IndRef ind -> ind
    | _ -> error "A mixin must be a record declaration." in
  Lib.add_leaf (save_roles (ind, roles));
  List.filter_map (fun (pos, role) ->
    match role with Mixin _ -> None | Value _ -> Some pos
  ) (List.mapi (fun pos role -> pos, role) roles)

let () =
  let open Elpi.API in
  let open BuiltInPredicate in
  let module Rocq = Elpi_plugin.Rocq_elpi_HOAS in
  ignore (BuiltIn.declare ~file_name:"minks.combinations" [
    BuiltIn.MLCode (Pred ("minks.register-combination",
      In (Rocq.inductive, "Class",
      In (Rocq.gref, "Constructor",
      In (BuiltInData.int, "Parameter count",
      In (BuiltInData.list BuiltInData.string, "Component keys",
      Easy "Register an exported class for Mixin inheritance.")))),
      (fun ind constructor count components ~depth:_ ->
        let roles = List.init count (fun _ -> Value Glob_term.Explicit) in
        ignore (remember (GlobRef.IndRef ind) roles);
        let components = List.map Id.of_string components in
        Lib.add_leaf (save_combination (ind, { constructor; components })))),
      BuiltIn.DocAbove)
  ])
