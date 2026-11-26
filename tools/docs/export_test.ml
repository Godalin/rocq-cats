open Docs_filter.Filter

let read path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let write path contents =
  let oc = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out oc)
    (fun () -> output_string oc contents)

let contains text token =
  let rec loop i =
    i + String.length token <= String.length text
    && (starts text i token || loop (i + 1))
  in
  loop 0

let run program args =
  let pid = Unix.create_process program (Array.of_list (program :: args))
    Unix.stdin Unix.stdout Unix.stderr in
  match snd (Unix.waitpid [] pid) with
  | Unix.WEXITED 0 -> ()
  | _ -> failwith (program ^ " failed in documentation integration test")

let () =
  let source = read Sys.argv.(3) in
  let proof = Docs_pdf.Preview.proof_input ~kind:"Definition" ~ending:"Defined."
    ~name:"nat_iso_is_iso" source in
  if List.length (Str.split_delim (Str.regexp_string "(* .unfold .all *)") proof)
    <> 3 then
    failwith "current preview proof lost its two focused-state annotations";
  let dir = Filename.temp_file "rocq_docs_" "" in
  Sys.remove dir; Unix.mkdir dir 0o700;
  let original = dir ^ "/Fixture.v" in
  let source =
    "From Stdlib Require Import String.\nOpen Scope string_scope.\n"
    ^ "(** * English tutorial heading\n\nRead [中文 token] and [⇒]. *)\n\n"
    ^ "(** * 中文教程标题\n\n阅读 [English token] 和 [⇒]。 *)\n\n"
    ^ "(** @lang both\n%\\begin{tikzcd} A \\arrow[r, \"f\"] & B"
    ^ "\\end{tikzcd}%\n*)\n\n"
    ^ "Definition quoted := \"(** fake documentation *) \"\"quoted\"\"\".\n"
    ^ "(* outer (* nested *) comment *)\n"
    ^ "(** [* -> <- <-> => <= >= <> ~ /\\ \\/ |- forall exists Π λ | _* _*N] *)\n\n"
    ^ "(** printing ⇒ %\\Rightarrow% #&rArr;# *)\n"
    ^ "(** [⇒] *)\n\n"
    ^ "Definition visible_sample := tt.\n"
    ^ "Abbreviation visible_alias := visible_sample.\n"
    ^ "Record DocumentedInterface := {\n"
    ^ "  (** FieldCarrier selects the carrier of the interface, retaining its"
    ^ " computational data rather than merely asserting that some carrier"
    ^ " exists. *)\n\n"
    ^ "  (** 字段载体选定接口的载体，保留可计算的数据，而不只是断言存在某个载体；"
    ^ "这段较长的说明仍应由原生注释机制隐藏，不应变成声明内部的空白缩进。 *)\n\n"
    ^ "  interface_carrier : Type;\n"
    ^ "  (** FieldIdentity acts on the selected carrier. *)\n\n"
    ^ "  (** 字段恒等作用于选定载体。 *)\n\n"
    ^ "  interface_identity : interface_carrier -> interface_carrier\n"
    ^ "}.\n"
    ^ "(* begin hide *)\nDefinition hidden_support := tt.\n(* end hide *)\n"
    ^ "Example verified_example : visible_alias = tt.\n"
    ^ "Proof. reflexivity. (* .unfold .all *) Qed.\n"
  in
  write original source;
  let annotated = Docs_pdf.Preview.proof_input ~name:"verified_example" source in
  if not (contains annotated "\\begin{alectryon}{coq}{none}")
    || not (contains annotated "reflexivity. (* .unfold .all *) Qed.") then
    failwith "native Alectryon input changed the proof or its annotations";
  run "rocq" ["compile"; "-q"; original];
  let metadata = read (dir ^ "/Fixture.glob") in
  if not (List.mem "Stdlib.Strings.String" (Docs_order.Order.imports metadata)) then
    failwith "compiled import metadata was not recognized";
  List.iter (fun (language, tag, present, absent) ->
    let output = dir ^ "/" ^ tag in
    Unix.mkdir output 0o700;
    let filtered, glob, messages = prepare language source metadata in
    if messages <> [] then failwith "unexpected fixture language diagnostics";
    write (output ^ "/Fixture.v") filtered;
    write (output ^ "/Fixture.glob") glob;
    run "rocq" ["doc"; "--utf8"; "--gallina"; "--no-externals"; "--no-index";
      "--no-lib-name"; "-o"; output ^ "/page.html"; output ^ "/Fixture.v"];
    let page = read (output ^ "/page.html") in
    if contains page "\\begin{tikzcd}" then
      failwith "PDF-only diagram leaked into HTML";
    List.iter (fun name -> if not (contains page name) then failwith ("missing " ^ name))
      [present; "visible_sample"; "verified_example"; "quoted"];
    List.iter (fun name -> if contains page name then failwith ("unexpected " ^ name))
      [absent; "hidden_support"; "reflexivity"];
    run "rocq" ["doc"; "--latex"; "--utf8"; "--gallina"; "--body-only";
      "--no-index"; "-d"; output; "-o"; output ^ "/page.tex"; output ^ "/Fixture.v"];
    let latex = read (output ^ "/page.tex") in
    List.iter (fun (text, escaped) ->
      List.iter (fun token -> if not (contains text token) then
        failwith ("source notation was substituted: " ^ token)) escaped)
      [page, [">*</span>"; "-&gt;"; "&lt;-&gt;"; "forall"; "exists"; "Π"; "λ"];
       latex, ["* -> <- <-> => <= >= <>"; "{forall}"; "{exists}"; "Π"; "λ"]];
    if not (contains latex "\\Rightarrow") then
      failwith "explicit source printing directive was discarded";
    List.iter (fun fragment -> if not (contains page fragment) then
      failwith ("missing compiled anchor: " ^ fragment))
      ["href=\"#interface_carrier\""; "id=\"visible_alias\""];
    List.iter (fun token -> if contains latex token then
      failwith ("implicit symbol substitution survived: " ^ token))
      ["\\ensuremath{\\times}"; "\\ensuremath{\\forall}";
       "\\ensuremath{\\rightarrow}"; "\\ensuremath{\\Rightarrow}"];
    (* Suppressed field prose must not turn into wide blank indentation. *)

    let indentation = Str.regexp "\\\\coqdocindent{\\([0-9.]+\\)em}" in
    let rec check_indentation offset =
      match Str.search_forward indentation latex offset with
      | _ ->
          let width = float_of_string (Str.matched_group 1 latex) in
          let ending = Str.match_end () in
          if width > 4. then
            failwith "hidden interface prose became visible indentation";
          check_indentation ending
      | exception Not_found -> ()
    in
    check_indentation 0;
    let carrier_prose, identity_prose = match language with
      | En -> "FieldCarrier", "FieldIdentity"
      | Zh -> "字段载体", "字段恒等" in
    let after text offset token =
      try Str.search_forward (Str.regexp_string token) text offset
        + String.length token
      with Not_found -> failwith ("missing interleaved field documentation: " ^ token)
    in
    List.iter (fun (text, carrier, identity) ->
      ignore (List.fold_left (after text) 0
        ["DocumentedInterface"; carrier_prose; carrier;
         identity_prose; identity]))
      [page, "interface_carrier", "interface_identity";
       latex, "interface\\_carrier", "interface\\_identity"];
    let presented = Docs_pdf.Pdf.decorate (Docs_pdf.Pdf.compact latex) in
    if not (contains presented "\\renewcommand{\\catsCodeTitle}{") then
      failwith "complete PDF lost shared interface frames";
    if contains presented "\\input{proof.tex}" then
      failwith "complete PDF unexpectedly requires native proof assets";
    let rec declarations text =
      let opening = "\\coqdef{" in
      try
        let start = Str.search_forward (Str.regexp_string opening) text 0 in
        let ending = String.index_from text start '}' + 1 in
        String.sub text start (ending - start)
          :: declarations (String.sub text ending (String.length text - ending))
      with Not_found -> []
    in
    if declarations presented <> declarations latex then
      failwith "complete-module preview lost or reordered declarations";
    if not (contains presented present) then
      failwith "complete-module preview lost source documentation";
    List.iter (fun token -> if not (contains latex token) then
      failwith ("missing LaTeX " ^ token))
      [present; "visible"; "\\begin{tikzcd}"; "\\arrow[r, \"f\"]"];
    List.iter (fun token -> if contains latex token then
      failwith ("unexpected LaTeX " ^ token))
      [absent; "@lang"; "hidden\\_support"; "reflexivity"];
    if not (contains (Docs_pdf.Pdf.targets presented) "catsTarget@Fixture.") then
      failwith "specimen declaration destinations were not retained")
    [En, "en", "English tutorial heading", "中文教程标题";
     Zh, "zh", "中文教程标题", "English tutorial heading"];
  let source = read Sys.argv.(1) and metadata = read Sys.argv.(2) in
  List.iter (fun (language, tag) ->
    let output = dir ^ "/minks-" ^ tag in
    Unix.mkdir output 0o700;
    let filtered, glob, messages = prepare language source metadata in
    if messages <> [] then failwith "unexpected Minks fixture diagnostics";
    let input = output ^ "/MinksExport.v" in
    write input filtered;
    write (output ^ "/MinksExport.glob") glob;
    run "rocq" ["doc"; "--utf8"; "--gallina"; "--no-externals";
      "--no-index"; "--no-lib-name"; "-R"; output; "CatsTests.documentation";
      "-o"; output ^ "/page.html"; input];
    let page = read (output ^ "/page.html") in
    List.iter (fun token -> if not (contains page token) then
      failwith ("missing compiled Minks declaration or reference: " ^ token))
      ["Minks"; "Mixin"; "Struct"; "exports";
       "id=\"HasExportPoint\""; "id=\"export_point\"";
       "id=\"ExportPointed\""; "id=\"MakeExportPointed\"";
       "id=\"ExportPointedToTypeCarrier\""; "id=\"ExportPointOn\"";
       "href=\"CatsTests.documentation.MinksExport.html#ExportPointed\"";
       "href=\"CatsTests.documentation.MinksExport.html#MakeExportPointed\"";
       "href=\"CatsTests.documentation.MinksExport.html#export_point\"";
       "selected_point"];
    let client, client_glob, _ = prepare language
      (read Sys.argv.(4)) (read Sys.argv.(5)) in
    let use = output ^ "/MinksExportUse.v" and combined = output ^ "/pdf.glob" in
    write use client;
    write combined (Docs_pdf.Pdf.link_glob [client_glob; glob]);
    run "rocq" ["doc"; "--latex"; "--glob-from"; combined; "--utf8"; "--gallina";
      "--body-only"; "--no-index"; "-R"; output; "CatsTests.documentation";
      "-o"; output ^ "/page.tex"; input; use];
    let latex = read (output ^ "/page.tex") in
    let definition = Str.regexp "\\\\coqdef{\\([^}]*\\)}{ExportPointed}{" in
    ignore (Str.search_forward definition latex 0);
    let target = Str.matched_group 1 latex in
    List.iter (fun (kind, name) ->
      let link = "\\coqref{" ^ target ^ "}{\\coqdoc" ^ kind ^ "{" ^ name ^ "}}" in
      if not (contains latex link) then
        failwith ("PDF reference did not link to Minks.Struct ExportPointed: " ^ name))
      ["constructor", "MakeExportPointed"; "definition", "ExportPointedToExportPointOn";
       "class", "ExportPointOn"];
    List.iter (fun token -> if not (contains latex token) then
      failwith ("missing Minks LaTeX declaration: " ^ token))
      ["HasExportPoint"; "ExportPointed"; "exports"; "ExportPointOn"])
    [En, "en"; Zh, "zh"];
  print_endline "Documentation export: bilingual native output, compiled Minks declarations and current preview input passed."
