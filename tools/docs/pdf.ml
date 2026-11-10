(* PDF presentation changes apply only after coqdoc has processed the shared,
   compiled sources; source positions and mathematical declarations stay intact. *)

(* PDF 排版调整仅作用于 coqdoc 处理共享编译源码后的结果，不改变源码位置或数学声明。 *)

let compact body =
  let indentation = Str.regexp "^\\\\coqdocindent{[0-9.]+em}$" in
  let is_indent line = line = "\\coqdocnoindent"
    || Str.string_match indentation line 0 in
  (* Coqdoc emits an empty row as an indentation prefix followed by eol,
     as well as using emptyline. Keep the prefix of each nonempty row. *)

  (* coqdoc 既用 emptyline，也用缩进前缀与 eol 表示空行。
     压缩时保留每个非空行的缩进前缀。 *)

  let rec code seen gap indent acc = function
    | [] -> List.rev acc
    | line :: rest ->
        let trimmed = String.trim line in
        if is_indent trimmed then code seen gap (Some line) acc rest
        else if trimmed = "\\coqdoceol" || trimmed = "\\coqdocemptyline" then
          code seen true None acc rest
        else if trimmed = "" then code seen gap indent acc rest
        else
          let acc = if seen && gap then "\\coqdocemptyline" :: acc else acc in
          let acc = match indent with None -> acc | Some line -> line :: acc in
          code true false None (line :: acc) rest
  in
  let rec block acc = function
    | [] -> invalid_arg "unterminated coqdoc code environment"
    | line :: rest when String.trim line = "\\end{coqdoccode}" ->
        code false false None [] (List.rev acc), line, rest
    | line :: rest -> block (line :: acc) rest
  in
  let rec loop = function
    | [] -> []
    | line :: rest when String.trim line = "\\begin{coqdoccode}" ->
        let contents, ending, rest = block [] rest in
        if contents = [] then loop rest
        else line :: contents @ (ending :: loop rest)
    | line :: rest -> line :: loop rest
  in
  String.concat "\n" (loop (String.split_on_char '\n' body))

let symbols body =
  let found = Hashtbl.create 128 in
  let rec loop i =
    if i < String.length body then begin
      let d = String.get_utf_8_uchar body i in
      if not (Uchar.utf_decode_is_valid d) then invalid_arg "invalid UTF-8 in LaTeX";
      let u = Uchar.to_int (Uchar.utf_decode_uchar d) in
      (* CJK text and punctuation use CTeX's selected Fandol fonts. *)

      (* 中日韩文字及标点使用 CTeX 选定的 Fandol 字体。 *)

      if u > 127 && not (Docs_filter.Filter.cjk u)
        && not (u >= 0x3000 && u <= 0x303f)
        && not (u >= 0xff00 && u <= 0xffef) then
        Hashtbl.replace found u (String.sub body i (Uchar.utf_decode_length d));
      loop (i + Uchar.utf_decode_length d)
    end
  in
  loop 0;
  Hashtbl.to_seq found |> List.of_seq |> List.sort compare
  |> List.map (fun (u, glyph) ->
    Printf.sprintf "\\newunicodechar{%s}{\\texorpdfstring{\\catsglyph{%X}}{%s}}"
      glyph u glyph)
  |> String.concat "\n"

let check_log log =
  let contains text token =
    let n = String.length token in
    let rec loop i = i + n <= String.length text
      && (String.sub text i n = token || loop (i + 1)) in
    loop 0
  in
  List.iter (fun token -> if contains log token then
    failwith ("PDF validation failed (" ^ token ^ "); inspect the XeLaTeX log"))
    ["Missing character:"; "Overfull \\hbox"; "Overfull \\vbox";
     "undefined references"; "multiply defined"; "Token not allowed in a PDF string"]

let find text token offset =
  try Str.search_forward (Str.regexp_string token) text offset
  with Not_found -> failwith ("PDF presentation: missing " ^ token)

let titled title kind block =
  (if title = "Theorem" then
    "\\tcbset{cats semantic/.style={cats theorem}}\n"
  else "\\tcbset{cats semantic/.style={}}\n")
  ^ "\\renewcommand{\\catsCodeTitle}{" ^ title ^ "}\n"
  ^ "\\renewcommand{\\catsCodeKind}{" ^ kind ^ "}\n" ^ block ^ "\n"

(* Only included declarations are valid local destinations in an excerpt. *)

(* 选段中只有实际纳入的声明才是有效的本地链接目标。 *)

let targets body =
  let pattern = Str.regexp "\\\\coqdef{\\([^}]*\\)}" in
  let rec loop offset =
    match Str.search_forward pattern body offset with
    | _ ->
        let name = Str.matched_group 1 body and ending = Str.match_end () in
        "\\expandafter\\def\\csname catsTarget@" ^ name ^ "\\endcsname{}\n"
        ^ loop ending
    | exception Not_found -> ""
  in
  loop 0

(* Preserve all prose and declarations, decorating only complete code blocks.
   An optional selected proof is rendered in place by Alectryon. *)

(* 保留全部正文与声明，只为完整代码块添加样式。
   可选的指定证明在原位置由 Alectryon 渲染。 *)

let decorate ?proof_anchor source =
  let opening = "\\begin{coqdoccode}" and closing = "\\end{coqdoccode}" in
  let capture pattern group block default =
    try ignore (Str.search_forward (Str.regexp pattern) block 0);
      Str.matched_group group block
    with Not_found -> default
  in
  let decorate block =
    let contents = String.sub block (String.length opening)
      (String.length block - String.length opening - String.length closing) in
    let blank = Str.global_replace
      (Str.regexp "\\\\coqdocemptyline\\|\\\\coqdocnoindent") "" contents
      |> String.trim in
    if blank = "" then ""
    else
      let name = capture "\\\\coqdef{[^}]*}{\\([^}]*\\)}" 1 block "" in
      match proof_anchor with
      | Some anchor when (try ignore (find block ("\\coqdef{" ^ anchor ^ "}") 0);
          true with Failure _ -> false) ->
          "\\coqdef{" ^ anchor ^ "}{}{}\n"
          ^ titled "Definition / Proof" name "\\input{proof.tex}"
      | _ ->
          let kind = capture "\\\\coqdockw{\\([^}]*\\)}" 1 block "Rocq" in
          let kind = if List.mem kind
            ["Class"; "Record"; "Definition"; "Program Definition";
             "Lemma"; "Theorem"; "Proposition"; "Corollary";
             "Instance"; "Program Instance"; "Global Instance"]
            then kind else "Rocq" in
          titled kind name block
  in
  let buffer = Buffer.create (String.length source) in
  let rec loop offset =
    match Str.search_forward (Str.regexp_string opening) source offset with
    | start ->
        Buffer.add_substring buffer source offset (start - offset);
        let stop = find source closing start + String.length closing in
        Buffer.add_string buffer (decorate (String.sub source start (stop - start)));
        loop stop
    | exception Not_found ->
        Buffer.add_substring buffer source offset (String.length source - offset)
  in
  loop 0; Buffer.contents buffer

let document ?(restrict_references = false) template =
  (* titlesec must precede hyperref so section bookmarks keep their anchors. *)

  (* titlesec 必须先于 hyperref 加载，保证节书签保留正确的锚点。 *)

  let template = Str.global_substitute
    (Str.regexp_string "\\usepackage{hyperref}")
    (fun _ -> "\\usepackage{titlesec}\n\\usepackage{hyperref}") template in
  if not restrict_references then template else
  Str.global_substitute (Str.regexp_string "\\begin{document}")
    (fun _ -> "\\begin{document}\n"
      ^ "\\renewcommand{\\coqref}[2]{\\ifcsname catsTarget@#1\\endcsname"
      ^ "\\hyperlink{coq:#1}{#2}\\else#2\\fi}\n"
      ^ "\\renewcommand{\\coqexternalref}[3]{#3}\n\\input{targets.tex}\n") template
