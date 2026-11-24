open Names
open Constrexpr

type parameter = {
  name : Id.t;
  binder : local_binder_expr;
}

type role =
  | Mixin of Id.t option
  | Value

type selection = Witness of GlobRef.t | Ordinary

type dependency = {
  key : Id.t option;
  selection : selection;
  arguments : constr_expr list;
  instance : instance_expr option;
  parameter : parameter;
  shared : bool;
}

let parameter_roles = Summary.ref ~name:"minks-parameter-roles" Indmap_env.empty

let save_roles =
  Libobject.declare_object
    (Libobject.superglobal_object "MINKS-PARAMETER-ROLES"
      ~cache:(fun (ind, parents, roles) ->
        parameter_roles := Indmap_env.add ind (parents, roles) !parameter_roles)
      ~discharge:(fun (ind, parents, roles) ->
        let prefix = Global.section_instance (GlobRef.IndRef ind) in
        Some (ind, parents, Array.fold_left (fun rs _ -> Value :: rs) roles prefix))
      ~subst:(Some (fun (subst, (ind, parents, roles)) ->
        Mod_subst.subst_ind subst ind,
        List.map (Globnames.subst_global_reference subst) parents, roles)))

let value_positions roles =
  List.filter_map Fun.id (List.mapi (fun i -> function Mixin _ -> None | _ -> Some i) roles)

type combination = {
  constructor : GlobRef.t;
  components : Id.t list;
  ordinary_fields : Id.Set.t;
}

let combinations = Summary.ref ~name:"minks-combinations" Indmap_env.empty

let save_combination =
  Libobject.declare_object
    (Libobject.superglobal_object "MINKS-COMBINATION"
      ~discharge:(fun x -> Some x)
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

let application reference instance args =
  CAst.make (CAppExpl ((qualify reference, instance), args))

(* Retain the terms that Rocq inserted at the selected ordinary inputs. *)
let dependency_type parent_instance ty context inputs =
  let head, operands = Constr.decompose_app_list ty in
  let reference, instance =
    match Constr.kind head with
    | Ind (ind, instance) -> GlobRef.IndRef ind, instance
    | Const (constant, instance) -> GlobRef.ConstRef constant, instance
    | _ -> error "Expected a parent mixin parameter indexed by earlier parameters."
  in
  let rec argument operand =
    match Constr.kind operand with
    | Rel i -> List.nth inputs (i - 1)
    | Var id -> variable id
    | _ ->
      let fn, args = Constr.decompose_app_list operand in
      let global = match Constr.kind fn with
        | Const (c, u) -> Some (GlobRef.ConstRef c, u)
        | Ind (i, u) -> Some (GlobRef.IndRef i, u)
        | Construct (c, u) -> Some (GlobRef.ConstructRef c, u)
        | _ -> None in
      match global with
      | Some (ref, u) ->
        let levels = Option.bind parent_instance (fun i -> instance_syntax i u) in
        application ref levels (List.map argument args)
      | None ->
        (* Close the inherited term over its native telescope before applying
           the child's terms. Binders inside the inherited term cannot capture
           free names in the supplied arguments. *)
        let closed = Term.it_mkLambda_or_LetIn operand context in
        let env = Global.env () in
        let flags = PrintingFlags.make_raw (PrintingFlags.current ()) in
        let fn = Constrextern.extern_constr ~flags env (Evd.from_env env)
          (EConstr.of_constr closed) in
        Constrexpr_ops.mkAppC (fn, List.rev inputs)
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
  let ty = application reference instance arguments in
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
    (match d.selection with Witness r -> Environ.QGlobRef.equal env r reference | Ordinary -> false) &&
    (match d.key, key with Some x, Some y -> Id.equal x y | _ -> true) in
  match List.filter same dependencies with
  | [d] ->
    if List.length d.arguments <> List.length arguments then
      error "Inherited parents disagree on the arity of a shared mixin.";
    let instance = merge_instance reference d.instance instance in
    let name = d.parameter.name in
    let parameter = dependency_parameter reference name instance d.arguments in
    let key = match d.key with Some _ -> d.key | None -> key in
    let updated = List.map (fun item ->
      if same item then { d with key; instance; parameter; shared = true } else item
    ) dependencies in
    updated, name
  | [] ->
    let name = binder_name reference reserved key in
    let parameter = dependency_parameter reference name instance arguments in
    { key; selection = Witness reference; arguments; instance; parameter; shared = false } :: dependencies, name
  | _ -> error "More than one selected component matches an inherited mixin."

let read_arguments args =
  List.partition_map (fun (term, explicit) ->
    match Option.map (fun arg -> arg.CAst.v) explicit with
    | None -> Either.Left term
    | Some (ExplByName key) -> Either.Right (key, term)
    | Some (ExplByPos _) -> error "Supply an implicit ordinary parameter by name."
  ) args

let take_argument kind ann positional named =
  let binder = Context.binder_name ann in
  let name = match binder with Name id -> Id.to_string id | Anonymous -> "_" in
  match kind with
  | Glob_term.Explicit ->
    (match positional with
     | value :: rest -> value, rest, named
     | [] -> error ("Missing explicit ordinary parameter " ^ name ^ " of the parent."))
  | Glob_term.NonMaxImplicit | Glob_term.MaxImplicit ->
    (match binder with
     | Name id ->
       (match List.assoc_opt id named with
        | Some value -> value, positional, List.remove_assoc id named
        | None -> error ("Pass implicit ordinary parameter " ^ name ^ " by name."))
     | Anonymous -> error "An implicit ordinary parameter used in extends must have a name.")

(* Struct parents take only ordinary inputs. Normalize named and positional
   arguments to the declaration order consumed by the layout generator. *)
let struct_arguments qid args =
  let reference = Nametab.global qid in
  let env = Global.env () in
  let ty, _ = Typeops.type_of_global_in_context env reference in
  let implicits = Impargs.select_stronger_impargs (Impargs.implicits_of_global reference) in
  let positional, named = read_arguments args in
  let rec collect env ty statuses positional named =
    match Constr.kind (Reduction.whd_all env ty) with
    | Prod (ann, domain, body) ->
      let status, rest = match statuses with
        | [] -> None, [] | x :: xs -> x, xs in
      let term, positional, named =
        take_argument (Impargs.binding_kind_of_status status) ann positional named in
      let env = Environ.push_rel (Context.Rel.Declaration.LocalAssum (ann, domain)) env in
      term :: collect env body rest positional named
    | _ ->
      if positional <> [] || named <> [] then error "Unexpected or repeated parent argument.";
      []
  in
  collect env ty implicits positional named

(* A virtual mixin retains the ordinary binders of the exported layout. *)
let add_ordinary_field instance key ty ctx inputs reserved dependencies =
  let ty, arguments = match Constr.kind ty with
    | Sort (Sorts.Type u) ->
      let sort = match instance, Univ.Universe.level u with
        | Some (_, levels), Some level ->
          (match level_syntax levels level with
           | Glob_term.UNamed level -> None, Glob_term.UNamed [level, 0]
           | Glob_term.UAnonymous rigid -> None, Glob_term.UAnonymous rigid)
        | _ -> Constrexpr_ops.expr_Type_sort in
      CAst.make (CSort sort), []
    | _ ->
      let head, levels, args = dependency_type instance ty ctx inputs in
      let levels = Option.bind instance (fun i -> instance_syntax i levels) in
      application head levels args, args in
  let same d = match d.selection, d.key with
    | Ordinary, Some k -> Id.equal key k
    | _ -> false in
  match List.find_opt same dependencies with
  | Some d ->
    List.map (fun item -> if same item then { item with shared = true } else item)
      dependencies, d.parameter.name
  | None ->
    let name = Namegen.next_ident_away key reserved in
    let parameter = parameter name (Default Glob_term.Explicit) ty in
    { key = Some key; selection = Ordinary; arguments; instance = None;
      parameter; shared = false } :: dependencies, name

(* Rocq's concrete-syntax equality deliberately ignores the payload of
   tactic terms and holes. Such applications need their own typing check. *)
let rec needs_elaboration () found expr =
  found || match expr.CAst.v with
  | CGenarg _ | CGenargGlob _ | CHole _ | CEvar _ -> true
  | _ -> Constrexpr_ops.fold_constr_expr_with_binders (fun _ () -> ())
      needs_elaboration () false expr

let same_application a b =
  not (needs_elaboration () false a) && Constrexpr_ops.constr_expr_eq a b

let expand_combination env reference syntax_instance instance shape inputs dependencies reserved views =
  let ctor_ty, _ = Typeops.type_of_global_in_context env shape.constructor in
  let rec skip count ctx ty =
    if count = 0 then ctx, ty else
    match Constr.kind ty with
    | Prod (ann, domain, rest) ->
      skip (count - 1) (Context.Rel.Declaration.LocalAssum (ann, domain) :: ctx) rest
    | _ -> error "Invalid fixed parameters in the exported mixin."
  in
  let rec expand dependencies reserved ctx inputs keys ty =
    match keys, Constr.kind ty with
    | key :: keys, Prod (ann, ty, rest) ->
      let dependencies, name =
        if Id.Set.mem key shape.ordinary_fields then
          add_ordinary_field instance key ty ctx inputs reserved dependencies
        else
          let component, levels, arguments = dependency_type instance ty ctx inputs in
          let levels = Option.bind instance (fun i -> instance_syntax i levels) in
          add_dependency env reserved dependencies component levels arguments (Some key) in
      expand dependencies (Id.Set.add name reserved)
        (Context.Rel.Declaration.LocalAssum (ann, ty) :: ctx) (variable name :: inputs) keys rest
    | [], _ -> dependencies, reserved, List.rev inputs
    | _ -> error "The exported mixin does not match its component metadata."
  in
  let ctx, ty = skip (List.length inputs) [] ctor_ty in
  let deps, reserved, args = expand dependencies reserved ctx inputs shape.components ty in
  let value = application shape.constructor syntax_instance args in
  if List.exists (function
    | CLocalDef (_, _, previous, _) -> same_application previous value
    | _ -> false) views then deps, reserved, views
  else
    let name = binder_name reference reserved None in
    let binder = CLocalDef (CAst.make (Name name), None, value, None) in
    deps, Id.Set.add name reserved, binder :: views

(* The constructor of each virtual parent checks its selected components.
   For ordinary parents Rocq must also check the selected witness against
   each requested type, even if the class body ignores that parent. *)
let check_parent_uses reserved field_names dependencies uses =
  let declared = List.filter_map (fun d -> match d.selection with
    | Witness ref -> Some (d.parameter.name, application ref d.instance d.arguments)
    | Ordinary -> None) dependencies in
  let check (used, known, checks) (name, expected) =
    if List.exists (fun (id, ty) ->
      Id.equal id name && same_application ty expected) known
    then used, known, checks
    else
      let taken id = Id.Set.mem id used ||
        Nametab.locate_extended_all (Libnames.qualid_of_ident id) <> [] in
      let id = Namegen.next_ident_away_from (Id.of_string "minks_shared") taken in
      let local = CLocalDef (CAst.make (Name id), None, variable name, Some expected) in
      Id.Set.add id used, (name, expected) :: known, local :: checks in
  let _, _, checks = List.fold_left check
    (Id.Set.union reserved field_names, declared, []) uses in
  List.rev checks

(* The prefix and the public class are elaborated in separate universe
   contexts. Keep named levels and let Rocq infer fresh, unnamed levels
   again when it checks the public declaration. *)
let scoped_term env sigma value =
  let flags = PrintingFlags.make_raw (PrintingFlags.current ()) in
  let detype = { flags.detype with universes = true; qualities = true } in
  let hole = Glob_term.UAnonymous { rigid = UState.UnivFlexible false } in
  let quality = function CRawQuality (Sorts.Quality.QVar _) -> CQAnon None | q -> q in
  let level = function Glob_term.UNamed (CRawType _) -> hole | u -> u in
  let instance = Option.map (fun (qs, us) -> List.map quality qs, List.map level us) in
  let rec reopen () expr =
    let expr = Constrexpr_ops.map_constr_expr_with_binders (fun _ () -> ()) reopen () expr in
    CAst.map (function
      | CRef (r, u) -> CRef (r, instance u)
      | CAppExpl ((r, u), args) -> CAppExpl ((r, instance u), args)
      | CProj (p, (r, u), args, t) -> CProj (p, (r, instance u), args, t)
      | CArray (u, xs, v, t) -> CArray (instance u, xs, v, t)
      | CSort (q, Glob_term.UNamed us)
        when List.exists (function CRawType _, _ -> true | _ -> false) us ->
        CSort (Option.map quality q, hole)
      | term -> term) expr in
  reopen () (Constrextern.extern_constr ~flags:{ flags with detype } env sigma value)

(* Elaborate the ordinary actuals in the prefix of completed parents.
   The holes for inherited positions provide expected types for dependent
   arguments. The component table supplies the actual witnesses below. *)
let scoped_arguments env locals sigma reference instance roles kinds typ positional named =
  let rec collect ty roles kinds pos named = match roles, Constr.kind ty with
    | _, LetIn (_, v, _, body) -> collect (Vars.subst1 v body) roles kinds pos named
    | role :: rest, Prod (ann, _, body) ->
      let kind, kinds = match kinds with [] -> None, [] | k :: ks -> k, ks in
      let arg, pos, named = match role with
        | Mixin _ -> CAst.make (CHole None), pos, named
        | Value -> take_argument (Impargs.binding_kind_of_status kind) ann pos named in
      arg :: collect body rest kinds pos named
    | [], Sort _ when pos = [] && named = [] -> []
    | _ -> error "Unexpected or repeated ordinary argument in extends." in
  let args = collect typ roles kinds positional named in
  let sigma, checked = Constrintern.interp_type_evars env sigma
    (application reference instance args) in
  let _, values = EConstr.decompose_app_list sigma checked in
  List.filter_map Fun.id (List.map2 (fun role value -> match role with
    | Mixin _ -> None
    | Value ->
      if Evarutil.has_undefined_evars sigma value then
        error "Unresolved ordinary argument in the scope of this parent.";
      let value = List.fold_left (fun value d -> match d with
        | Context.Named.Declaration.LocalDef (ann, rhs, _) ->
          EConstr.Vars.replace_vars sigma [Context.binder_name ann, rhs] value
        | _ -> value) value locals in
      Some (scoped_term env sigma value)
  ) roles values)

let rec reserve_actual_names () names expr =
  let names = match expr.CAst.v with
    | CRef (qid, _) | CAppExpl ((qid, _), _) when Libnames.qualid_is_ident qid ->
      Id.Set.add (Libnames.qualid_basename qid) names
    | _ -> names in
  Constrexpr_ops.fold_constr_expr_with_binders (fun _ () -> ())
    reserve_actual_names () names expr

let inheritance universes ordinary own field_names parents =
  let env = Global.env () in
  let sigma, _, _ = Constrintern.interp_cumul_univ_decl_opt env universes in
  let header = List.map (fun (_, (binder, _)) -> binder) ordinary in
  let inherit_parent (dependencies, reserved, views, uses) (parent, syntax_instance, args) =
    let positional, named = read_arguments args in
    let reference = Nametab.locate parent in
    let ind = match reference with
      | GlobRef.IndRef ind -> ind
      | _ -> error "Expected a registered Minks mixin." in
    let roles = match Indmap_env.find_opt ind !parameter_roles with
      | Some (_, roles) -> roles
      | None -> error "Expected a registered Minks mixin." in
    let implicits = Impargs.select_stronger_impargs (Impargs.implicits_of_global reference) in
    let combination = Indmap_env.find_opt ind !combinations in
    let ty, context = Typeops.type_of_global_in_context env reference in
    let scope = header @ List.rev_map (fun d -> d.parameter.binder) dependencies @
      List.rev views in
    let sigma, (_, ((scope_env, locals), _, _)) =
      Constrintern.interp_named_context_evars env sigma scope in
    let values = scoped_arguments scope_env locals sigma reference syntax_instance
      roles implicits ty positional named in
    let reserved = List.fold_left (reserve_actual_names ()) reserved values in
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
    let rec add_parameters dependencies reserved ctx inputs roles rest values =
      match roles, Constr.kind rest with
      | _, LetIn (_, value, _, rest) ->
        add_parameters dependencies reserved ctx inputs roles (Vars.subst1 value rest) values
      | Mixin key :: roles, Prod (ann, ty, rest) ->
        let dependency, levels, arguments = dependency_type instance ty ctx inputs in
        let levels = Option.bind instance (fun i -> instance_syntax i levels) in
        let dependencies, reserved, name = add dependencies reserved dependency levels arguments key in
        add_parameters dependencies reserved (Context.Rel.Declaration.LocalAssum (ann, ty) :: ctx)
          (variable name :: inputs) roles rest values
      | Value :: roles, Prod (ann, ty, rest) ->
        let expr, values = match values with x :: xs -> x, xs | [] -> assert false in
        add_parameters dependencies reserved (Context.Rel.Declaration.LocalAssum (ann, ty) :: ctx)
          (expr :: inputs) roles rest values
      | [], Sort _ ->
        (match combination with
         | None ->
           let arguments = List.rev inputs in
           let deps, reserved, name =
             add dependencies reserved reference syntax_instance arguments None in
           let expected = application reference syntax_instance arguments in
           deps, reserved, views, (name, expected) :: uses
         | Some shape ->
           let deps, reserved, views = expand_combination env reference syntax_instance
             instance shape inputs dependencies reserved views in
           deps, reserved, views, uses)
      | _ -> error "The parent mixin parameters do not match its Minks declaration."
    in
    add_parameters dependencies reserved [] [] roles ty values
  in
  let dependencies, reserved, views, uses =
    List.fold_left inherit_parent ([], own, [], []) parents in
  let checks = check_parent_uses reserved field_names dependencies (List.rev uses) in
  List.rev dependencies, List.rev views @ checks

let ordinary_parameters binders =
  List.concat_map (function
    | CLocalAssum (names, relevance, Default kind, ty) ->
      List.map (fun name ->
        (name.CAst.v, (CLocalAssum ([name], relevance, Default kind, ty), Value))
      ) names
    | _ -> error "Mixin value parameters must be ordinary binders."
  ) binders

(* Elaborate the telescope with all ordinary inputs in scope. Rocq resolves
   the dependencies inside notations, implicit applications and projections.
   Only then choose the public order of its binders. *)
let parameter_references universes ordinary inherited =
  let env = Global.env () in
  let sigma, _, _ = Constrintern.interp_cumul_univ_decl_opt env universes in
  let binders = List.map (fun (_, (binder, _)) -> binder) ordinary @
    List.map (fun d -> d.parameter.binder) inherited in
  let sigma, (_, ((env, ctx), _, _)) =
    Constrintern.interp_named_context_evars env sigma binders in
  List.fold_left (fun refs d ->
    let id = Context.Named.Declaration.get_id d in
    Id.Map.add id (Termops.global_vars_set_of_decl env sigma d) refs
  ) Id.Map.empty ctx

let order_witnesses references inherited =
  let rec order pending =
    match pending with
    | [] -> []
    | _ ->
      let ready d = Id.Set.for_all (fun arg ->
        not (List.exists (fun prior -> Id.equal prior.parameter.name arg) pending)
      ) (Id.Map.find d.parameter.name references) in
      let next = match List.find_opt (fun d -> d.shared && ready d) pending with
        | Some d -> d
        | None -> (match List.find_opt ready pending with
          | Some d -> d
          | None -> error "Cyclic inherited mixin dependencies.") in
      next :: order (List.filter (fun d ->
        not (Id.equal d.parameter.name next.parameter.name)) pending)
  in
  order inherited

let add_to_declaration parents decl =
  let ((name, (binders, extra), sort, fields), notations) = decl in
  let ordinary = ordinary_parameters binders in
  let own = List.fold_left (fun set (name, _) ->
    match name with Name id -> Id.Set.add id set | Anonymous -> set
  ) Id.Set.empty ordinary in
  let visible = Id.Set.union own (Environ.ids_of_named_context_val
    (Environ.named_context_val (Global.env ()))) in
  let field_names = match fields with
    | Vernacexpr.RecordDecl (_, entries, _) ->
      List.fold_left (fun names (field, _) ->
        let field_name = match field with
          | Vernacexpr.AssumExpr (n, _, _) | Vernacexpr.DefExpr (n, _, _, _) -> n in
        match field_name.CAst.v with
        | Name id -> Id.Set.add id names | Anonymous -> names) Id.Set.empty entries
    | _ -> assert false in
  let _, (_, universes) = name in
  let inherited, views = inheritance universes ordinary visible field_names parents in
  let references = if inherited = [] then Id.Map.empty
    else parameter_references universes ordinary inherited in
  let inherited = order_witnesses references inherited in
  let parameters = List.map snd ordinary @ List.map (fun d ->
    let role = match d.selection with Witness _ -> Mixin d.key | Ordinary -> Value in
    d.parameter.binder, role) inherited in
  let binders, roles = List.split parameters in
  let witnesses = List.filter_map (fun d -> match d.selection with
    | Witness ref -> Some ref | Ordinary -> None) inherited in
  ((name, (binders @ views, extra), sort, fields), notations), roles, witnesses

let remember reference parents roles =
  let ind = match reference with
    | GlobRef.IndRef ind -> ind
    | _ -> error "A mixin must be a record declaration." in
  Lib.add_leaf (save_roles (ind, parents, roles))

let () =
  let open Elpi.API in
  let open BuiltInPredicate in
  let module Rocq = Elpi_plugin.Rocq_elpi_HOAS in
  let global ~depth hyps constraints state =
    let state, context, _, goals =
      Rocq.get_global_env_current_sigma ~depth hyps constraints state in
    state, context, constraints, goals in
  ignore (BuiltIn.declare ~file_name:"minks.combinations" [
    BuiltIn.MLCode (Pred ("minks.add-record",
      CIn (Packed_record.declaration, "Record telescope",
      Out (Rocq.inductive, "Structure",
      Full (global, "Declare a Rocq record with stored and computed fields."))),
      (fun decl _ ~depth:_ _ _ state ->
        if State.get Elpi_plugin.Rocq_elpi_builtins.tactic_mode state then
          error "A packed record must be declared by a command.";
        let ind, uctx = Packed_record.declare decl in
        Rocq.grab_global_env ~uctx state, ((), Some ind), [])),
      BuiltIn.DocAbove);
    BuiltIn.MLCode (Pred ("minks.stored-projections",
      In (Rocq.inductive, "Structure",
      Out (BuiltInData.list Rocq.gref, "Component projections",
      Easy "Read the projections of constructor arguments in declaration order.")),
      (fun ind _ ~depth:_ ->
        (), Some (Packed_record.stored_projections ind))),
      BuiltIn.DocAbove);
    BuiltIn.MLCode (Pred ("minks.mixin-header",
      In (Rocq.inductive, "Registered class",
      Out (BuiltInData.list Rocq.gref, "Direct parents",
      Out (BuiltInData.list BuiltInData.int, "Ordinary binder positions",
      Easy "Read the mixin header in the current section context."))),
      (fun ind _ _ ~depth:_ ->
        match Indmap_env.find_opt ind !parameter_roles with
        | None -> raise No_clause
        | Some (parents, roles) -> (((), Some parents), Some (value_positions roles)))),
      BuiltIn.DocAbove);
    BuiltIn.MLCode (Pred ("minks.register-combination",
      In (Rocq.inductive, "Class",
      In (Rocq.gref, "Constructor",
      In (BuiltInData.int, "Parameter count",
      In (BuiltInData.list BuiltInData.string, "Component keys",
      In (BuiltInData.list BuiltInData.string, "Ordinary field keys",
      Easy "Register an exported class for Mixin inheritance."))))),
      (fun ind constructor count components ordinary ~depth:_ ->
        let roles = List.init count (fun _ -> Value) in
        remember (GlobRef.IndRef ind) [] roles;
        let components = List.map Id.of_string components in
        let ordinary_fields = Id.Set.of_list (List.map Id.of_string ordinary) in
        Lib.add_leaf (save_combination (ind, { constructor; components; ordinary_fields })))),
      BuiltIn.DocAbove)
  ])
