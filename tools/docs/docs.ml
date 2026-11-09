open Docs_filter
open Docs_pdf
module Order = Docs_order.Order

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

(* Local lists only express preferences; unlisted sources remain included. *)

(* 局部清单只表达阅读偏好，未列出的源码仍自动纳入。 *)

let preferences file paths =
  Order.prefer (Order.entries (read file)) paths

let rec source_files dir =
  let paths = Sys.readdir dir |> Array.to_list |> List.sort String.compare
    |> List.concat_map (fun name ->
      let path = Filename.concat dir name in
      if Sys.is_directory path then source_files path
      else if suffix ".v" path then [path] else []) in
  let config = dir ^ "/chapters" in
  if Sys.file_exists config then
    Order.prefer (Order.entries (read config)
      |> List.map (Filename.concat dir)) paths
  else paths

let module_name path =
  let stem = Filename.chop_extension path in
  "Cats." ^ String.map (function '/' -> '.' | c -> c)
    (String.sub stem 9 (String.length stem - 9))

let metadata root source =
  Filename.concat root ("_build/default/" ^ Filename.chop_extension source.path ^ ".glob")

let reading_order root sources =
  let by_name = Hashtbl.create (List.length sources) in
  let by_path = Hashtbl.create (List.length sources) in
  List.iter (fun s ->
    Hashtbl.add by_name s.name s.path; Hashtbl.add by_path s.path s) sources;
  let dependencies = Hashtbl.create (List.length sources) in
  List.iter (fun s ->
    let imports = Order.imports (read (metadata root s))
      |> List.filter_map (Hashtbl.find_opt by_name) in
    Hashtbl.add dependencies s.path imports) sources;
  Order.arrange ~dependencies:(Hashtbl.find dependencies)
    (List.map (fun s -> s.path) sources)
  |> List.map (Hashtbl.find by_path)

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

let pdf ?(design = false) root output tag paths =
  let dir = output ^ "/" ^ tag in
  mkdir dir;
  run "coqdoc" (["--latex"; "--utf8"; "--body-only"; "--gallina";
    "--no-index"; "--no-lib-name";
    "-R"; output ^ "/.inputs/" ^ tag ^ "/theories"; "Cats";
    "-d"; dir; "-o"; dir ^ "/body.tex"] @ paths);
  let zh = tag = "zh" in
  let body = Pdf.compact (read (dir ^ "/body.tex")) in
  let body = if design then Preview.body
    ~proof_anchor:"Cats.Cat.Natural.NatIso is iso" body else body in
  write (dir ^ "/body.tex") body;
  if design then begin
    write (dir ^ "/targets.tex") (Preview.targets body);
    List.iter (fun name -> write (dir ^ "/" ^ name) (read (output ^ "/" ^ name)))
      ["proof.tex"; "alectryon.sty"; "pygments.sty"]
  end;
  let proof = if design then read (dir ^ "/proof.tex") else "" in
  let symbols = Pdf.symbols (body ^ proof) in
  write (dir ^ "/symbols.tex") symbols;
  let title = if design then
      (if zh then "抽象范畴、函子与自然变换" else "Categories, Functors and Natural Transformations")
    else (if zh then "全库理论参考手册" else "Full-Library Theory Reference") in
  let logo = read (root ^ "/docs/branding/rocq-cats-preview.png") in
  write (dir ^ "/rocq-cats-logo.png") logo;
  let brand = "\\begin{center}\\includegraphics[width=.94\\textwidth]"
    ^ "{rocq-cats-logo.png}\\end{center}" in
  let template = read (root ^ "/tools/docs/pdf-template.tex") in
  let theme = if design then read (root ^ "/tools/docs/pdf-textbook.tex") else "" in
  let setup = theme ^ (if design && zh then
    "\n\\renewcommand{\\catsContinued}{续}" else "") ^ "\n" ^ (if zh then
      "\\renewcommand{\\contentsname}{目录}"
    else "\\renewcommand{\\contentsname}{Contents}") in
  let template = if design then Preview.document template else template in
  let document = template
    |> fun s -> replace s "@@SETUP@@" setup
    |> fun s -> replace s "@@BRAND@@" brand
    |> fun s -> replace s "@@TITLE@@" title
    |> fun s -> replace s "@@LANGUAGE@@" (if zh then "中文版" else "English Edition")
    |> fun s -> replace s "@@DESCRIPTION@@"
      (if zh then "来自同一双语源码；定义、定理与示例经过 Rocq 检查。"
       else "From one bilingual source tree. Definitions, theorems and examples checked by Rocq.") in
  let filename = "rocq-cats-" ^ tag in
  let assets = if design then
    read (dir ^ "/alectryon.sty") ^ read (dir ^ "/pygments.sty") else "" in
  let digest = Digest.to_hex
    (Digest.string (document ^ body ^ symbols ^ logo ^ proof ^ assets)) in
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

let build root strict format =
  Sys.chdir root;
  let paths = source_files "theories"
    |> preferences "docs/chapters" in
  let sources = List.map (fun path -> { path; name = module_name path }) paths in
  run "dune" ["build"; "@all"];
  let sources = reading_order root sources in
  let sources = if format = "design" then
    let names = Preview.modules (List.map (fun s -> s.name) sources) in
    List.filter (fun s -> List.mem s.name names) sources else sources in
  let output = root ^ (match format with
    | "pdf" -> "/_build/docs-pdf"
    | "design" -> "/_build/docs-design"
    | _ -> "/_build/docs") in
  mkdir output;
  if format = "design" then begin
    let input = output ^ "/proof-input.tex" in
    write input (Preview.proof_input ~kind:"Definition" ~ending:"Defined."
      ~name:"NatIso_is_iso" (read "theories/Cat/Natural.v"));
    let local = root ^ "/_build/docs-alectryon/bin/alectryon" in
    let program = if Sys.file_exists local then local else "alectryon" in
    run ~log:(output ^ "/alectryon.log") program
      ["--frontend"; "latex"; "--backend"; "latex";
       "--coq-driver"; "vsrocq"; "--latex-dialect"; "xelatex";
       "--pygments-style"; "friendly_grayscale";
       "--rocq-arg=-set"; "--rocq-arg=Printing Width=60";
       "--copy-assets"; "copy";
       "-R"; root ^ "/_build/default/theories"; "Cats";
       "-o"; output ^ "/proof.tex"; input]
  end;
  write (output ^ "/reading-order.txt")
    (String.concat "\n" (List.map (fun s -> s.name) sources) ^ "\n");
  let warnings = ref [] in
  List.iter (fun s -> write (output ^ "/source/" ^ s.path) (read s.path)) sources;
  List.iter (fun (language, tag, other) ->
    let inputs = output ^ "/.inputs/" ^ tag in
    mkdir (inputs ^ "/theories");
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
    if format = "pdf" || format = "design" then
      pdf ~design:(format = "design") root output tag paths else begin
      let dir = output ^ "/" ^ tag in
      mkdir dir;
      Sys.readdir dir |> Array.iter (fun name ->
        if suffix ".html" name
          && Filter.starts name 0 "Cats"
          && not (List.exists (fun s -> s.name ^ ".html" = name) sources)
        then remove (dir ^ "/" ^ name));
      run "coqdoc" (["--html"; "--utf8"; "--gallina"; "--toc"; "--no-lib-name";
        "-R"; inputs ^ "/theories"; "Cats";
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
  if format = "design" then
    Printf.printf "Generated a bilingual preview from Cat.Core through Cat.Natural (%d complete modules): %s\n%!"
      (List.length sources) output
  else Printf.printf "Generated %s for %d modules in each language: %s\n%!"
      format (List.length sources) output;
  if strict && messages <> [] then failwith "unclassified or unpaired documentation"

let () =
  try
    let strict = ref false and format = ref "html" in
    Arg.parse ["--strict", Arg.Set strict, "Reject language-classification diagnostics"]
      (function "build" -> () | "pdf" -> format := "pdf"
        | "design" -> format := "design"
        | s -> raise (Arg.Bad ("unknown command: " ^ s)))
      "dune exec tools/docs/docs.exe -- (build|pdf|design) [--strict]";
    build (Unix.realpath (Sys.getcwd ())) !strict !format
  with
  | Failure message | Invalid_argument message -> prerr_endline message; exit 1
  | Sys_error message -> prerr_endline message; exit 1
  | Unix.Unix_error (error, command, path) ->
      Printf.eprintf "%s: %s %s\n" (Unix.error_message error) command path;
      exit 1
