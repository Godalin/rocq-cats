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
    ^ "(** printing ⇒ %\\Rightarrow% #&rArr;# *)\n"
    ^ "Definition visible_sample := tt.\n"
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
    ^ "Example verified_example : visible_sample = tt.\n"
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
    let filtered, messages = filter language source in
    if messages <> [] then failwith "unexpected fixture language diagnostics";
    write (output ^ "/Fixture.v") filtered;
    write (output ^ "/Fixture.glob") (glob ~original:source ~filtered metadata);
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
    (* Suppressed field prose must not turn into wide blank indentation. *)

    (* 被隐藏的字段正文不得变成很宽的空白缩进。 *)

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
  print_endline "Documentation export: language separation, proof hiding and shared LaTeX passed."
