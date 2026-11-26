(* Test the raw generator metadata independently of any documentation filter. *)
let read path =
  let input = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in input)
    (fun () -> really_input_string input (in_channel_length input))

let declarations path =
  read path |> String.split_on_char '\n'
    |> List.filter_map (fun line ->
      match String.split_on_char ' ' line with
      | [kind; range; scope; name] ->
          (match String.split_on_char ':' range with
          | [first; last] ->
              Some (scope, kind, name, int_of_string first, int_of_string last)
          | _ -> None)
      | _ -> None)

let require entries scope kind name =
  match List.filter (fun (s, k, n, _, _) -> s = scope && k = kind && n = name) entries with
  | [(_, _, _, first, last)] when first >= 0 && first <= last ->
      first, last
  | [] -> failwith ("Missing raw glob declaration: " ^ name)
  | _ -> failwith ("Duplicate or invalid raw glob declaration: " ^ name)

let () =
  let views = require (declarations Sys.argv.(3)) "DischargedViews" in
  if views "def" "BigToTiny" <> views "rec" "Tiny" then
    failwith "View discovered at End lost its structure declaration";
  let source = read Sys.argv.(1) in
  let require = require (declarations Sys.argv.(2)) "<>" in
  let at_name name range =
    let first, last = range in
    if String.sub source first (last - first + 1) <> name then
      failwith ("Authored glob location changed: " ^ name) in
  List.iter (fun (kind, name) -> at_name name (require kind name))
    ["class", "HasGlobValue"; "proj", "glob_value";
     "class", "HasGlobFlag"; "constr", "NewGlobFlag"; "proj", "glob_flag";
     "rec", "GlobParent"; "rec", "GlobChild"; "rec", "GlobNative"];
  List.iter (fun (owner, members) ->
    let position = require "rec" owner in
    List.iter (fun (tag, name) ->
      if require tag name <> position then
        failwith ("Wrong generating command for " ^ name)) members)
    ["GlobParent", ["rec", "TypeCarrier"; "constr", "MakeTypeCarrier";
       "proj", "TypeCarrier_carrier"; "constr", "MakeGlobParent";
       "proj", "GlobParent_carrier"; "proj", "chosenGlobPoint"];
     "GlobChild", ["constr", "MakeGlobChild"; "proj", "GlobChild_carrier";
       "proj", "GlobChild_globPoint"; "proj", "GlobChild_childPoint";
       "def", "GlobChildToGlobParent"; "def", "GlobChildOfGlobParent";
       "rec", "GlobOn"; "constr", "MakeGlobOn"; "proj", "GlobOn_childPoint";
       "def", "GlobChildToGlobOn"; "def", "GlobChildOfGlobOn"];
     "GlobNative", ["rec", "NativeGlobCarrier"; "constr", "MakeNativeGlobCarrier";
       "proj", "NativeGlobCarrierToNativeGlob"; "proj", "GlobNativeToNativeGlob";
       "proj", "GlobNative_globTag"]];
  print_endline "Minks raw glob declarations and source locations passed."
