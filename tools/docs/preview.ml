(* Select unchanged coqdoc fragments, after bilingual filtering and linking.
   This bounded design specimen never changes full-library discovery. *)

(* 在双语过滤与链接后选取未改写的 coqdoc 片段。
   这个范围受限的设计小样不改变全库模块发现。 *)

let find text token offset =
  try Str.search_forward (Str.regexp_string token) text offset
  with Not_found -> failwith ("PDF design specimen: missing " ^ token)

let between text first last =
  let start = find text first 0 in
  let stop = find text last (start + String.length first) in
  String.sub text start (stop - start)

let code body token =
  let opening = "\\begin{coqdoccode}" and closing = "\\end{coqdoccode}" in
  let rec loop offset =
    let start = find body opening offset in
    let stop = find body closing start + String.length closing in
    let block = String.sub body start (stop - start) in
    if (try ignore (find block token 0); true with Failure _ -> false)
    then block else loop stop
  in
  loop 0

let titled title kind block =
  (if title = "Theorem" then
    "\\tcbset{cats semantic/.style={cats theorem}}\n"
  else "\\tcbset{cats semantic/.style={}}\n")
  ^ "\\renewcommand{\\catsCodeTitle}{" ^ title ^ "}\n"
  ^ "\\renewcommand{\\catsCodeKind}{" ^ kind ^ "}\n" ^ block ^ "\n"

(* Feed the original tutorial context and selected proof to Alectryon's native
   LaTeX frontend. Sentence annotations in the source select visible states. *)

(* 将原始教程上下文及选定证明交给 Alectryon 原生 LaTeX 前端。
   源码中的语句注解选定要显示的状态。 *)

let proof_input ~name source =
  let start = find source ("Example " ^ name) 0 in
  let ending = find source "Qed." start + String.length "Qed." in
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

let body ~zh source =
  let tr en cn = if zh then cn else en in
  let product_heading = tr
    "\\subsection{4. A product records both observations universally}"
    "\\subsection{4. 积以泛的方式记录两份观察}" in
  let narrative = between source product_heading "\\begin{coqdoccode}" in
  let diagram = between source "\\begin{tikzcd}" "\\end{tikzcd}"
    ^ "\\end{tikzcd}" in
  "\\chapter{" ^ tr "Products and their universal property" "积与泛性质" ^ "}\n"
  ^ "{\\sffamily\\small\\color{catsMuted}CatsBook.Basics}\\par\n"
  ^ narrative
  ^ titled "Definition" "BooleanPair" (code source "{BooleanPair}")
  ^ "\\[" ^ diagram ^ "\\]\n"
  ^ "\\chapter{" ^ tr "Structures and laws" "结构与定律" ^ "}\n"
  ^ tr "The same specified equality governs identities and composition.\n"
       "恒等与复合的定律使用同一个指定相等。\n"
  ^ titled "Theorem" "symm\\_id\\_l" (code source "{symm\\_id\\_l}")
  ^ "\\vspace*{.32\\textheight}\n"
  ^ "{\\sffamily\\small\\color{catsMuted}Cats.Cat.Core}\\par\n"
  ^ titled "Class" "Cat" (code source "\\coqdockw{Class}")
  ^ "\\section{" ^ tr "A proof from the tutorial" "教程中的一个证明" ^ "}\n"
  ^ tr "The goals after split appear at that step, before the remaining tactics.\n"
       "split 后的目标直接显示在这一步，之后继续剩余的证明策略。\n"
  ^ titled "Example / Proof" "boolean\\_limit\\_pair"
       "\\input{proof.tex}"

let document template =
  (* titlesec must precede hyperref so section bookmarks keep their anchors. *)

  (* titlesec 必须先于 hyperref 加载，保证节书签保留正确的锚点。 *)

  let template = Str.global_substitute
    (Str.regexp_string "\\usepackage{hyperref}")
    (fun _ -> "\\usepackage{titlesec}\n\\usepackage{hyperref}") template in
  let start = find template "\\begin{document}" 0 in
  String.sub template 0 start
  ^ "\\begin{document}\n\\pagenumbering{arabic}\n"
  ^ "\\renewcommand{\\coqref}[2]{\\ifcsname catsTarget@#1\\endcsname"
  ^ "\\hyperlink{coq:#1}{#2}\\else#2\\fi}\n"
  ^ "\\renewcommand{\\coqexternalref}[3]{#3}\n"
  ^ "\\input{targets.tex}\n"
  ^ "\\input{body.tex}\n\\end{document}\n"
