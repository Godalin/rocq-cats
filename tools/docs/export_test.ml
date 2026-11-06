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
    ^ "(* begin hide *)\nDefinition hidden_support := tt.\n(* end hide *)\n"
    ^ "Example verified_example : visible_sample = tt.\n"
    ^ "Proof. reflexivity. Qed.\n"
  in
  write original source;
  run "coqc" ["-q"; original];
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
    run "coqdoc" ["--utf8"; "--gallina"; "--no-externals"; "--no-index";
      "--no-lib-name"; "-o"; output ^ "/page.html"; output ^ "/Fixture.v"];
    let page = read (output ^ "/page.html") in
    if contains page "\\begin{tikzcd}" then
      failwith "PDF-only diagram leaked into HTML";
    List.iter (fun name -> if not (contains page name) then failwith ("missing " ^ name))
      [present; "visible_sample"; "verified_example"; "quoted"];
    List.iter (fun name -> if contains page name then failwith ("unexpected " ^ name))
      [absent; "hidden_support"; "reflexivity"];
    run "coqdoc" ["--latex"; "--utf8"; "--gallina"; "--body-only";
      "--no-index"; "-d"; output; "-o"; output ^ "/page.tex"; output ^ "/Fixture.v"];
    let latex = read (output ^ "/page.tex") in
    List.iter (fun token -> if not (contains latex token) then
      failwith ("missing LaTeX " ^ token))
      [present; "visible"; "\\begin{tikzcd}"; "\\arrow[r, \"f\"]"];
    List.iter (fun token -> if contains latex token then
      failwith ("unexpected LaTeX " ^ token))
      [absent; "@lang"; "hidden\\_support"; "reflexivity"])
    [En, "en", "English tutorial heading", "中文教程标题";
     Zh, "zh", "中文教程标题", "English tutorial heading"];
  print_endline "Documentation export: language separation, proof hiding and shared LaTeX passed."
