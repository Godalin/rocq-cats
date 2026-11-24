(* A registry entry points at a checked constructor. Reading its telescope
   again also sees parameters generalized since the entry was registered. *)
open Names

type identity = Named of KerName.t | Native of GlobRef.t * string
module Identity = struct
  type t = identity
  let compare a b = match a, b with
    | Named x, Named y -> KerName.compare x y
    | Native (x, _), Native (y, _) -> GlobRef.UserOrd.compare x y
    | Named _, Native _ -> -1
    | Native _, Named _ -> 1
end

type layout = {
  owner : inductive;
  keys : identity array;
  header_kinds : Glob_term.binding_kind list;
}

let projections = Summary.ref ~name:"minks-key-origins" GlobRef.Map_env.empty
module Keys = Map.Make(Identity)
module KeySet = Set.Make(Identity)
let registry = Summary.ref ~name:"minks-component-keys" Keys.empty

let error s = CErrors.user_err (Pp.str s)
let header_kinds ind =
  let count = (Global.lookup_mind (fst ind)).mind_nparams in
  let statuses = Impargs.select_stronger_impargs
      (Impargs.implicits_of_global (GlobRef.IndRef ind)) in
  let rec take n = function
    | _ when n = 0 -> []
    | s :: rest -> Impargs.binding_kind_of_status s :: take (n - 1) rest
    | [] -> List.init n (fun _ -> Glob_term.Explicit) in
  take count statuses

let identity_of projection =
  match GlobRef.Map_env.find_opt projection !projections with
  | Some k -> k
  | None -> error "Missing registered component origin."

let same_key p q = Identity.compare (identity_of p) (identity_of q) = 0

(* Close the selected field over the complete ordinary telescope and its
   transitive field dependencies. Visit siblings by key so an unrelated
   field or another constructor order cannot change this judgment. *)
let descriptor env sigma layout index =
  let ind = layout.owner in
  let block = Environ.lookup_mind (fst ind) env in
  let sigma, ctor = Evd.fresh_global env sigma (GlobRef.ConstructRef (ind, 1)) in
  let ty = EConstr.to_constr sigma (Retyping.get_type_of env sigma ctor) in
  let params, body = Term.decompose_prod_n block.mind_nparams ty in
  let fields, _ = Term.decompose_prod_n (index + 1) body in
  let fields = Array.of_list (List.rev fields) in
  let dependencies i =
    Termops.free_rels sigma (EConstr.of_constr (snd fields.(i)))
    |> Int.Set.elements |> List.filter_map (fun r -> if r <= i then Some (i - r) else None)
    |> List.sort (fun a b -> Identity.compare layout.keys.(a) layout.keys.(b)) in
  let rec visit done_ i =
    if List.mem i done_ then done_
    else i :: List.fold_left visit done_ (dependencies i) in
  let order = List.rev (List.fold_left visit [] (dependencies index)) in
  (* Prior fields occupy the innermost de Bruijn positions. Reindex
     references into the dependency telescope, keeping inner binders and
     the relative order of ordinary parameters intact. *)
  let move i positions =
    let rec rename depth term = match Constr.kind term with
      | Rel r when r > depth ->
        let free = r - depth in
        let new_rel = if free > i then List.length positions + free - i
          else List.assoc (i - free) positions in
        Constr.mkRel (depth + new_rel)
      | _ -> Constr.map_with_binders succ rename depth term in
    rename 0 (snd fields.(i)) in
  let extend (ctx, prior) i =
    let positions = List.mapi (fun n j -> j, n + 1) prior in
    (fst fields.(i), move i positions) :: ctx, i :: prior in
  let deps, prior = List.fold_left extend ([],[]) order in
  let result = move index (List.mapi (fun n j -> j, n + 1) prior) in
  let closed = Term.compose_prod (deps @ params) result in
  let closed = Termops.it_mkNamedProd_wo_LetIn closed block.mind_hyps in
  (* Closing a Section replays registration with its discharged binder kinds. *)
  let kinds = List.filter_map (fun d ->
    if Context.Named.Declaration.is_local_assum d then Some None else None)
    block.mind_hyps @ List.map (fun k -> Some k) layout.header_kinds in
  let identities indices = List.map (Array.get layout.keys) indices in
  sigma, (kinds, identities (dependencies index), identities order, EConstr.of_constr closed)

(* Present the same closed telescope that Key-Reuse compares. Give its
   field binders the registered key names so dependencies remain readable
   even when their originating projections were renamed. *)
let key_name = function Named k -> Id.to_string (KerName.label k) | Native (_, k) -> k

let describe title (layout, index) =
  let env = Global.env () in
  let sigma, (kinds, direct, deps, ty) =
    descriptor env (Evd.from_env env) layout index in
  let flags = PrintingFlags.current () in
  let flags = { flags with extern = { flags.extern with implicits = true;
    implicits_explicit_args = false } } in
  let print env t = Printer.pr_lconstr_env ~flags env sigma t in
  let bind (env, ty, entries) (key, kind) =
    let binder, dom, body = Constr.destProd ty in
    let id = match key, binder.Context.binder_name with
      | Some dep, _ -> Id.of_string (key_name dep)
      | None, Name id -> id
      | None, Anonymous -> Id.of_string "x" in
    let id = Namegen.next_ident_away_in_goal env id Id.Set.empty in
    let open Pp in
    let entry = Id.print id ++ str " : " ++ print env dom in
    let entry = match kind with
      | Some Glob_term.MaxImplicit -> str "{" ++ entry ++ str "}"
      | Some Glob_term.NonMaxImplicit -> str "[" ++ entry ++ str "]"
      | _ -> str "(" ++ entry ++ str ")" in
    let decl = Context.Named.Declaration.LocalAssum
      ({ binder with Context.binder_name = id }, dom) in
    Environ.push_named Environ.ProofVar decl env, Vars.subst1 (Constr.mkVar id) body, (id, entry) :: entries in
  let bind_all env ty inputs =
    let env, ty, entries = List.fold_left bind (env, ty, []) inputs in
    let ids, entries = List.split (List.rev entries) in
    let text = match entries with
      | [] -> Pp.str "[]"
      | _ -> Pp.hov 0 (Pp.prlist_with_sep Pp.spc Fun.id entries) in
    env, ty, ids, text in
  let env, ty, _, params = bind_all env (EConstr.to_constr sigma ty)
      (List.map (fun k -> None, k) kinds) in
  let env, result, ids, fields = bind_all env ty (List.map (fun k -> Some k, None) deps) in
  let direct_ids = List.filter_map (fun (dep, id) ->
    if List.exists (fun k -> Identity.compare dep k = 0) direct then Some id else None
  ) (List.combine deps ids) in
  let open Pp in
  let first = Nametab.path_of_global (GlobRef.IndRef layout.owner) in
  v 0 (str "Minks key " ++ str title ++ fnl ()
    ++ str "First declared in: " ++ Libnames.pr_path first ++ fnl ()
    ++ str "Parameters: " ++ params ++ fnl ()
    ++ str "Component context: " ++ fields ++ fnl ()
    ++ str "Direct dependencies: [" ++ prlist_with_sep (fun () -> str ", ")
         Id.print direct_ids ++ str "]" ++ fnl ()
    ++ str "Field type: " ++ print env result)

(* Group paths by identity: unrelated structures may use the same alias.
   Keep every origin visible but print the checked telescope only once. *)
let inspect name resolved aliases references =
  let open Pp in
  let path r = Libnames.pr_path (Nametab.path_of_global r) in
  let add key line matches =
    Keys.update key (fun lines -> Some (line :: Stdlib.Option.value ~default:[] lines)) matches in
  let matches = List.fold_left (fun acc p -> Keys.add (identity_of p) [] acc)
      Keys.empty resolved in
  let matches = List.fold_left (fun acc p ->
    let key = identity_of p in
    let env = Global.env () in
    let owner = Structures.Structure.find_from_projection env (Globnames.destConstRef p) in
    add key (str name ++ str " is an alias for " ++ str (key_name key)
      ++ str " at Struct " ++ Printer.pr_inductive env owner.name) acc
  ) matches (List.sort_uniq GlobRef.UserOrd.compare aliases) in
  let matches = List.fold_left (fun acc p ->
    match GlobRef.Map_env.find_opt p !projections with
    | None -> acc
    | Some key -> add key (str "Projection " ++ path p ++ str " selects "
        ++ str (key_name key)) acc
  ) matches (List.sort_uniq GlobRef.UserOrd.compare references) in
  let qualify = not (Libnames.qualid_is_ident (Libnames.qualid_of_string name)) || Keys.cardinal matches > 1 in
  Keys.bindings matches |> List.map (fun (key, lines) ->
    let ((layout, _) as entry) = Keys.find key !registry in
    let title = match key with
      | Named kn when qualify ->
        let owner = Nametab.path_of_global (GlobRef.IndRef layout.owner) in
        let dir, _ = Libnames.repr_path owner in
        Libnames.string_of_path (Libnames.make_path dir (KerName.label kn))
      | _ -> key_name key in
    v 0 (prlist_with_sep fnl Fun.id
      (List.rev_append lines [describe title entry])))

let check key (old, i) (current, j) =
  let env = Global.env () in
  let sigma, (ks, direct, ds, t) = descriptor env (Evd.from_env env) old i in
  let sigma, (ls, other, es, u) = descriptor env sigma current j in
  let reject reason = CErrors.user_err Pp.(str "Incompatible component key " ++ str key
    ++ str " in " ++ Printer.pr_inductive env current.owner ++ str " ("
    ++ str reason ++ str "). First declared in " ++ Printer.pr_inductive env old.owner) in
  let same_keys = List.equal (fun d e -> Identity.compare d e = 0) in
  if not (List.equal (fun a b -> a = None || b = None || a = b) ks ls) then
    reject "different ordinary parameter count or binding kinds";
  if not (same_keys direct other && same_keys ds es) then
    reject "different component dependencies";
  if not (Option.has_some (Reductionops.infer_conv ~pb:Conversion.CONV env sigma t u)) then
    reject "the parameter or field types do not convert"

type declaration = {
  family : inductive;
  kinds : Glob_term.binding_kind list;
  fields : (string * GlobRef.t * bool) list;
}

let cache d =
  let own = Packed_record.stored_projections d.family in
  let rows = List.map2 (fun projection (name, source, local) ->
    let fresh = GlobRef.UserOrd.equal projection source in
    let identity = if not fresh then identity_of source
      else if local then
        Named (KerName.make (MutInd.modpath (fst d.family)) (Id.of_string name))
      else Native (projection, name) in
    name, projection, identity, local || fresh) own d.fields in
  let keys = Array.of_list (List.map (fun (_, _, k, _) -> k) rows) in
  if KeySet.cardinal (KeySet.of_list (Array.to_list keys)) <> Array.length keys then
    error "A structure cannot store the same component identity twice.";
  let layout = { owner = d.family; keys; header_kinds = d.kinds } in
  List.iteri (fun i (name, projection, key, declared) ->
    projections := GlobRef.Map_env.add projection key !projections;
    if declared then
      let entry = layout, i in
      match Keys.find_opt key !registry with
      | None -> registry := Keys.add key entry !registry
      | Some old -> check name old entry
  ) rows

let object_decl = Libobject.superglobal_object "MINKS-KEYS" ~cache
  ~discharge:(fun d -> Some d)
  ~subst:(Some (fun (s,d) ->
    {d with family = Mod_subst.subst_ind s d.family;
            fields = List.map (fun (n,p,l) ->
              n, Globnames.subst_global_reference s p, l) d.fields}))

let save = Libobject.declare_object { object_decl with
  rebuild_function = (fun d ->
    let added = (Global.lookup_mind (fst d.family)).mind_nparams - List.length d.kinds in
    {d with kinds = CList.firstn added (header_kinds d.family) @ d.kinds}) }

let register family names sources locals =
  let fields = List.map2 (fun n p -> n, p, List.mem n locals) names sources in
  Lib.add_leaf (save {family; kinds = header_kinds family; fields})
