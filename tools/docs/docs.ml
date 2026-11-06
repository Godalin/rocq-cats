open Docs_filter
open Docs_pdf

let read path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let rec mkdir path =
  if not (Sys.file_exists path) then begin
    mkdir (Filename.dirname path); Unix.mkdir path 0o755
  end

let write path text =
  mkdir (Filename.dirname path);
  let oc = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () -> output_string oc text)

let suffix ending s = Filename.check_suffix s ending

let rec files dir =
  Sys.readdir dir |> Array.to_list |> List.sort String.compare
  |> List.concat_map (fun name ->
    let path = Filename.concat dir name in
    if Sys.is_directory path then files path else [path])

let replace text pattern replacement =
  Str.global_replace (Str.regexp_string pattern) replacement text

let html text =
  List.fold_left (fun s (a, b) -> replace s a b) text
    ["&", "&amp;"; "<", "&lt;"; ">", "&gt;"; "\"", "&quot;"]

let run ?log program args =
  if List.length args > 12 then
    Printf.printf "+ %s (%d arguments)\n%!" program (List.length args)
  else Printf.printf "+ %s\n%!"
    (String.concat " " (List.map Filename.quote (program :: args)));
  let output = match log with None -> Unix.stdout | Some path ->
    Unix.openfile path [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o644 in
  let pid = Fun.protect
    ~finally:(fun () -> if log <> None then Unix.close output)
    (fun () -> Unix.create_process program (Array.of_list (program :: args))
      Unix.stdin output (if log = None then Unix.stderr else output)) in
  match snd (Unix.waitpid [] pid) with
  | Unix.WEXITED 0 -> ()
  | _ -> failwith (program ^ " failed" ^
      match log with None -> "" | Some path -> "; inspect " ^ path)

type source = { path : string; name : string }

let module_name path =
  let stem = Filename.chop_extension path in
  let prefix, offset =
    if Filter.starts path 0 "theories/" then "Cats.", 9 else "CatsBook.", 5
  in
  prefix ^ String.map (function '/' -> '.' | c -> c)
    (String.sub stem offset (String.length stem - offset))

let metadata root source =
  Filename.concat root ("_build/default/" ^ Filename.chop_extension source.path ^ ".glob")

let decorate dir language other sources =
  files dir |> List.filter (suffix ".html") |> List.iter (fun path ->
    let filename = Filename.basename path in
    let source = List.find_opt (fun s -> s.name ^ ".html" = filename) sources in
    let link href title =
      "<a href=\"" ^ html href ^ "\">" ^ html title ^ "</a>" in
    let nav = "<nav>"
      ^ link "index.html" (if language = "zh" then "索引" else "Index") ^ " · "
      ^ link "toc.html" (if language = "zh" then "目录" else "Contents") ^ " · "
      ^ link ("../" ^ other ^ "/" ^ filename)
          (if other = "zh" then "中文" else "English")
      ^ (match source with None -> "" | Some s -> " · "
          ^ link ("../source/" ^ s.path) (if language = "zh" then "源码" else "Source"))
      ^ "</nav>" in
    let body = read path in
    let body = replace body "<html " ("<html lang=\"" ^ language ^ "\" ") in
    write path (replace body "<body>" ("<body>" ^ nav)))

let remove path = if Sys.file_exists path then Sys.remove path

let attributes name text =
  let regexp = Str.regexp (name ^ "=\"\\([^\"]*\\)\"") in
  let rec loop pos acc =
    try
      ignore (Str.search_forward regexp text pos);
      let value = Str.matched_group 1 text and last = Str.match_end () in
      loop last (value :: acc)
    with Not_found -> List.rev acc
  in
  loop 0 []

let decode s =
  let b = Buffer.create (String.length s) in
  let rec loop i =
    if i < String.length s then
      if s.[i] = '%' && i + 2 < String.length s then
        match int_of_string_opt ("0x" ^ String.sub s (i + 1) 2) with
        | Some n -> Buffer.add_char b (Char.chr n); loop (i + 3)
        | None -> Buffer.add_char b s.[i]; loop (i + 1)
      else (Buffer.add_char b s.[i]; loop (i + 1))
  in
  loop 0; Buffer.contents b

(* Rocq 9.0 may print named record constructors as plain variables without
   anchors. Add an anchor at that visible constructor, using glob references
   to distinguish constructors from ordinary identifiers. *)

(* Rocq 9.0 有时把具名记录构造器显示为无锚点变量；根据 glob 引用识别构造器，
   在其实际显示位置补锚点，不将普通标识符当作构造器。 *)

let constructor_anchors root output sources =
  let constructors = Hashtbl.create 16 in
  List.iter (fun source ->
    read (metadata root source) |> String.split_on_char '\n' |> List.iter (fun line ->
      match Str.split (Str.regexp "[ \t]+") line with
      | position :: name :: section :: symbol :: ["constr"]
        when Filter.starts position 0 "R" ->
          let id = if section = "<>" then symbol else section ^ "." ^ symbol in
          Hashtbl.replace constructors (name, id) ()
      | _ -> ())) sources;
  List.iter (fun tag -> List.iter (fun source ->
    let path = output ^ "/" ^ tag ^ "/" ^ source.name ^ ".html" in
    let text = ref (read path) in
    Hashtbl.iter (fun (name, id) () ->
      if name = source.name && not (List.mem id (attributes "id" !text)) then
        let token = "<span class=\"id\" title=\"var\">" ^ html id ^ "</span>" in
        text := Str.replace_first (Str.regexp_string token)
          ("<span id=\"" ^ html id ^ "\" class=\"id\" title=\"constructor\">"
            ^ html id ^ "</span>") !text) constructors;
    write path !text) sources) ["en"; "zh"]

(* Check both destination files and fragments, including Unicode symbols. *)

(* 同时检查目标文件及片段，涵盖 Unicode 符号。 *)

let check_links output =
  let pages = files output |> List.filter (suffix ".html") in
  let cache = Hashtbl.create 64 in
  let anchors path =
    match Hashtbl.find_opt cache path with
    | Some result -> result
    | None ->
        let text = read path in
        let result = attributes "id" text @ attributes "name" text |> List.map decode in
        Hashtbl.add cache path result; result
  in
  let errors = ref [] in
  List.iter (fun path ->
    attributes "href" (read path) |> List.iter (fun href ->
      if not (Str.string_match (Str.regexp "^[A-Za-z][A-Za-z0-9+.-]*:") href 0) then begin
        let file, fragment = match String.index_opt href '#' with
          | None -> href, ""
          | Some i -> String.sub href 0 i,
              String.sub href (i + 1) (String.length href - i - 1)
        in
        let target = if file = "" then path
          else Filename.concat (Filename.dirname path) (decode file) in
        if not (Sys.file_exists target) then
          errors := (path ^ ": missing " ^ href) :: !errors
        else if fragment <> "" && suffix ".html" target
          && not (List.mem (decode fragment) (anchors target)) then
          errors := (path ^ ": missing anchor " ^ href) :: !errors
      end)) pages;
  if !errors <> [] then failwith (String.concat "\n" (List.rev !errors));
  Printf.printf "Checked local links and anchors in %d HTML pages.\n%!" (List.length pages)

let pdf root output tag book paths =
  let dir = output ^ "/" ^ tag in
  mkdir dir;
  run "coqdoc" (["--latex"; "--utf8"; "--gallina"; "--body-only";
    "--no-index"; "--no-lib-name";
    "-R"; output ^ "/.inputs/" ^ tag ^ "/theories"; "Cats";
    "-R"; output ^ "/.inputs/" ^ tag ^ "/book"; "CatsBook";
    "-d"; dir; "-o"; dir ^ "/body.tex"] @ paths);
  let body = Pdf.compact (read (dir ^ "/body.tex")) in
  write (dir ^ "/body.tex") body;
  let symbols = Pdf.symbols body in
  write (dir ^ "/symbols.tex") symbols;
  let zh = tag = "zh" in
  let title = if book then (if zh then "范畴论教程" else "Category Theory Tutorials")
    else (if zh then "理论参考手册与教程" else "Theory Reference and Tutorials") in
  let template = read (root ^ "/tools/docs/pdf-template.tex") in
  let setup = (if zh then
      "\\renewcommand{\\contentsname}{目录}"
    else "\\renewcommand{\\contentsname}{Contents}")
    ^ (if book then
      "\n\\renewcommand{\\coqlibrary}[3]{\\hypertarget{coq:#1}{}}\n"
      ^ "\\let\\subsubsection\\subsection\n\\let\\subsection\\section\n"
      ^ "\\let\\section\\chapter" else "") in
  let document = template
    |> fun s -> replace s "@@SETUP@@" setup
    |> fun s -> replace s "@@TITLE@@" title
    |> fun s -> replace s "@@LANGUAGE@@" (if zh then "中文版" else "English Edition")
    |> fun s -> replace s "@@DESCRIPTION@@"
      (if zh then "来自同一双语源码；定义、定理与示例经过 Rocq 检查。"
       else "From one bilingual source tree. Definitions, theorems and examples checked by Rocq.") in
  let filename = "rocq-cats-" ^ tag in
  let digest = Digest.to_hex (Digest.string (document ^ body ^ symbols)) in
  let stamp = dir ^ "/inputs.digest" in
  if not (Sys.file_exists stamp && read stamp = digest) then
    List.iter (fun ending ->
      let path = dir ^ "/" ^ filename ^ ending in
      if Sys.file_exists path then Sys.remove path) [".aux"; ".toc"; ".out"];
  write (dir ^ "/" ^ filename ^ ".tex") document;
  Fun.protect ~finally:(fun () -> Sys.chdir root) (fun () ->
    Sys.chdir dir;
    for _ = 1 to 2 do
      run ~log:(dir ^ "/xelatex-output.log") "xelatex"
        ["-interaction=nonstopmode"; "-halt-on-error";
        "-file-line-error"; "-no-shell-escape"; filename ^ ".tex"]
    done);
  Pdf.check_log (read (dir ^ "/" ^ filename ^ ".log"));
  write stamp digest;
  Printf.printf "Validated PDF: %s/%s.pdf\n%!" dir filename

let build root strict format book =
  Sys.chdir root;
  run "dune" ["build"; "@all"];
  let sources = ["theories"; "book"] |> List.concat_map files
    |> List.filter (suffix ".v")
    |> List.map (fun path -> { path; name = module_name path })
    |> List.filter (fun s -> not book || Filter.starts s.path 0 "book/") in
  let output = root ^ (if format = "pdf" then "/_build/docs-pdf/"
      ^ (if book then "book" else "full") else "/_build/docs") in
  mkdir output;
  let warnings = ref [] in
  List.iter (fun s -> write (output ^ "/source/" ^ s.path) (read s.path)) sources;
  List.iter (fun (language, tag, other) ->
    let inputs = output ^ "/.inputs/" ^ tag in
    List.iter (fun directory -> mkdir (inputs ^ "/" ^ directory)) ["theories"; "book"];
    let paths = List.map (fun s ->
      let original = read s.path in
      let filtered, messages = Filter.filter language original in
      if tag = "en" then List.iter (fun (m : Filter.diagnostic) ->
        warnings := Printf.sprintf "%s:%d: %s" s.path m.line m.message :: !warnings) messages;
      let path = inputs ^ "/" ^ s.path in
      write path filtered;
      write (Filename.chop_extension path ^ ".glob")
        (Filter.glob ~original ~filtered (read (metadata root s)));
      path) sources in
    if format = "pdf" then pdf root output tag book paths else begin
      let dir = output ^ "/" ^ tag in
      mkdir dir;
      run "coqdoc" (["--html"; "--utf8"; "--gallina"; "--toc"; "--no-lib-name";
        "-R"; inputs ^ "/theories"; "Cats"; "-R"; inputs ^ "/book"; "CatsBook";
        "-d"; dir] @ paths);
      List.iter (fun name -> remove (dir ^ "/" ^ name)) ["symbols.html"; "site.css"];
      decorate dir tag other sources
    end)
    [Filter.En, "en", "zh"; Filter.Zh, "zh", "en"];
  if format = "html" then begin
    write (output ^ "/index.html")
      ("<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">"
      ^ "<title>Rocq-Cats</title></head><body><h1>Rocq-Cats</h1>"
      ^ "<a href=\"en/index.html\">English</a> · "
      ^ "<a href=\"zh/index.html\">中文</a></body></html>\n");
    remove (output ^ "/site.css")
  end;
  let messages = List.rev !warnings in
  write (output ^ "/warnings.txt") (String.concat "\n" messages ^ "\n");
  List.iter prerr_endline messages;
  if format = "html" then begin
    constructor_anchors root output sources;
    check_links output
  end;
  Printf.printf "Generated %s for %d modules in each language: %s\n%!"
    format (List.length sources) output;
  if strict && messages <> [] then failwith "unclassified or unpaired documentation"

let () =
  try
    let strict = ref false and book = ref false and format = ref "html" in
    Arg.parse ["--strict", Arg.Set strict, "Reject language-classification diagnostics";
      "--book", Arg.Set book, "Export only the shared tutorial chapters (PDF)"]
      (function "build" -> () | "pdf" -> format := "pdf"
        | s -> raise (Arg.Bad ("unknown command: " ^ s)))
      "dune exec tools/docs/docs.exe -- (build|pdf) [--book] [--strict]";
    if !book && !format <> "pdf" then invalid_arg "--book requires pdf";
    build (Unix.realpath (Sys.getcwd ())) !strict !format !book
  with
  | Failure message | Invalid_argument message -> prerr_endline message; exit 1
  | Sys_error message -> prerr_endline message; exit 1
  | Unix.Unix_error (error, command, path) ->
      Printf.eprintf "%s: %s %s\n" (Unix.error_message error) command path;
      exit 1
