(* Test the raw generator metadata independently of any documentation filter. *)
let read path =
  let input = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in input)
    (fun () -> really_input_string input (in_channel_length input))

let () =
  let source = read Sys.argv.(1) in
  let declarations = read Sys.argv.(2) |> String.split_on_char '\n'
    |> List.filter_map (fun line ->
      match String.split_on_char ' ' line with
      | [kind; range; "<>"; name] ->
          (match String.split_on_char ':' range with
          | [first; last] ->
              Some (kind, name, int_of_string first, int_of_string last)
          | _ -> None)
      | _ -> None) in
  let require kind name =
    match List.filter (fun (k, n, _, _) -> k = kind && n = name) declarations with
    | [(_, _, first, last)] when first >= 0 && first <= last
                                && last < String.length source ->
        first, last
    | [] -> failwith ("Missing raw glob declaration: " ^ name)
    | _ -> failwith ("Duplicate or invalid raw glob declaration: " ^ name) in
  let at_name name range =
    let first, last = range in
    if String.sub source first (last - first + 1) <> name then
      failwith ("Authored glob location changed: " ^ name) in
  List.iter (fun (kind, name) -> at_name name (require kind name))
    ["class", "HasGlobValue"; "proj", "glob_value";
     "class", "HasGlobFlag"; "proj", "glob_flag";
     "rec", "GlobParent"; "rec", "GlobChild"; "rec", "GlobNative"];
  List.iter (fun (owner, names) ->
    let position = require "rec" owner in
    List.iter (fun name ->
      if require "proj" name <> position then
        failwith ("Generated projection lost its record location: " ^ name)) names)
    ["GlobParent", ["GlobParent_carrier"; "chosenGlobPoint"];
     "GlobChild", ["GlobChild_carrier"; "GlobChild_globPoint"; "GlobChild_childPoint"];
     "GlobNative", ["GlobNativeToNativeGlob"; "GlobNative_globTag"]];
  List.iter (fun (kind, name) -> ignore (require kind name))
    ["constr", "MakeGlobParent"; "constr", "MakeGlobChild";
     "rec", "TypeCarrier";
     "proj", "TypeCarrier_carrier";
     "rec", "NativeGlobCarrier";
     "proj", "NativeGlobCarrierToNativeGlob";
     "def", "GlobChildToGlobParent";
     "rec", "GlobOn"; "proj", "GlobOn_childPoint"];
  print_endline "Minks raw glob declarations and source locations passed."
