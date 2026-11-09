(* Preview a continuous range of complete modules in library reading order.
   Formatting follows bilingual filtering and compiled-reference processing. *)

(* 按全库阅读顺序预览连续的完整模块。
   排版在双语过滤及编译引用处理后进行。 *)

let find text token offset =
  try Str.search_forward (Str.regexp_string token) text offset
  with Not_found -> failwith ("PDF design specimen: missing " ^ token)

let modules names =
  let rec collect = function
    | [] -> failwith "preview reading order is missing Cats.Cat.Natural"
    | name :: rest -> name ::
        if name = "Cats.Cat.Natural" then [] else collect rest
  in
  let rec start = function
    | [] -> failwith "preview reading order is missing Cats.Cat.Core"
    | ("Cats.Cat.Core" :: _ as remaining) -> collect remaining
    | _ :: rest -> start rest
  in
  start names

let titled title kind block =
  (if title = "Theorem" then
    "\\tcbset{cats semantic/.style={cats theorem}}\n"
  else "\\tcbset{cats semantic/.style={}}\n")
  ^ "\\renewcommand{\\catsCodeTitle}{" ^ title ^ "}\n"
  ^ "\\renewcommand{\\catsCodeKind}{" ^ kind ^ "}\n" ^ block ^ "\n"

(* Feed the original module context and selected proof to Alectryon's native
   LaTeX frontend. Sentence annotations in the source select visible states. *)

(* 将原始模块上下文及选定证明交给 Alectryon 原生 LaTeX 前端。
   源码中的语句注解选定要显示的状态。 *)

let proof_input ?(kind = "Example") ?(ending = "Qed.") ~name source =
  let start = find source (kind ^ " " ^ name) 0 in
  let ending = find source ending start + String.length ending in
  "\\begin{alectryon}{coq}{none}\n" ^ String.sub source 0 start
  ^ "\n\\end{alectryon}\n\\begin{alectryon}{coq}{in}\n"
  ^ String.sub source start (ending - start) ^ "\n\\end{alectryon}\n"

(* Only declarations included in the specimen are valid local destinations. *)

(* 只有纳入小样的声明才是有效的本地链接目标。 *)

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
   One selected proof is rendered in place by Alectryon. *)

(* 保留全部正文与声明，只为完整代码块添加样式。
   一个选定证明在原位置由 Alectryon 渲染。 *)

let body ?proof_anchor source =
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

let document template =
  (* titlesec must precede hyperref so section bookmarks keep their anchors. *)

  (* titlesec 必须先于 hyperref 加载，保证节书签保留正确的锚点。 *)

  let template = Str.global_substitute
    (Str.regexp_string "\\usepackage{hyperref}")
    (fun _ -> "\\usepackage{titlesec}\n\\usepackage{hyperref}") template in
  Str.global_substitute (Str.regexp_string "\\begin{document}")
    (fun _ -> "\\begin{document}\n"
      ^ "\\renewcommand{\\coqref}[2]{\\ifcsname catsTarget@#1\\endcsname"
      ^ "\\hyperlink{coq:#1}{#2}\\else#2\\fi}\n"
      ^ "\\renewcommand{\\coqexternalref}[3]{#3}\n\\input{targets.tex}\n") template
