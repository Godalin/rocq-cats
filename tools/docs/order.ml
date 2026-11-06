(* Partial editorial preferences keep unlisted modules discoverable.
   A directory entry also selects all its descendants. *)

(* 局部阅读偏好保留未列模块的自动发现；目录条目同时选择其后代模块。 *)

let entries text =
  String.split_on_char '\n' text |> List.map String.trim
  |> List.filter (fun line -> line <> "" && line.[0] <> '#')

let matches entry path =
  path = entry ||
  let prefix = entry ^ "/" in
  String.starts_with ~prefix path

let prefer entries paths =
  let rec choose seen remaining = function
    | [] -> remaining
    | entry :: rest ->
        if List.mem entry seen then
          failwith ("repeated reading-order entry: " ^ entry);
        if not (List.exists (matches entry) paths) then
          failwith ("unknown reading-order entry: " ^ entry);
        let selected, remaining = List.partition (matches entry) remaining in
        selected @ choose (entry :: seen) remaining rest
  in
  choose [] paths entries

(* Imports come from Rocq's compiled metadata, not a source-text heuristic. *)

(* 导入关系来自 Rocq 的编译元数据，不从源码文本猜测。 *)

let imports text =
  String.split_on_char '\n' text |> List.filter_map (fun line ->
    match String.split_on_char ' ' line |> List.filter ((<>) "") with
    | position :: name :: "<>" :: "<>" :: ["lib"]
      when String.starts_with ~prefix:"R" position -> Some name
    | _ -> None)
  |> List.sort_uniq String.compare

(* Every dependency precedes its client. DFS expands prerequisites of a
   preferred module before choosing a lower-priority, independent module. *)

(* 所有依赖均先于使用者；深度优先遍历先补齐偏好模块的依赖，再选择低优先级模块。 *)

let arrange ~dependencies paths =
  let states = Hashtbl.create (List.length paths) in
  List.iter (fun path -> Hashtbl.add states path 0) paths;
  let result = ref [] in
  let rec visit path =
    match Hashtbl.find_opt states path with
    | None | Some 2 -> ()
    | Some 1 -> failwith ("cyclic imports at " ^ path)
    | Some _ ->
        Hashtbl.replace states path 1;
        List.iter visit (dependencies path);
        Hashtbl.replace states path 2;
        result := path :: !result
  in
  List.iter visit paths; List.rev !result
