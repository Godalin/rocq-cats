open Docs_pdf.Pdf

let check message condition = if not condition then failwith message

let contains text token =
  let n = String.length token in
  let rec loop i = i + n <= String.length text
    && (String.sub text i n = token || loop (i + 1)) in
  loop 0

let () =
  let range = ["Cats.Cat.Core"; "Cats.Cat.Terminal";
    "Cats.Cat.Functor.Core"; "Cats.Cat.Natural"] in
  check "preview lost a complete intervening module or included outside modules"
    (Docs_pdf.Preview.modules ("Cats.Meta" :: range @ ["Cats.Cat.Product.Core"])
      = range);
  List.iter (fun names ->
    check "a missing preview boundary was silently accepted"
      (try ignore (Docs_pdf.Preview.modules names); false with Failure _ -> true))
    [["Cats.Cat.Core"]; ["Cats.Cat.Natural"]];
  let body = "\\begin{coqdoccode}\n\\coqdocemptyline\n\n\\coqdocemptyline\n"
    ^ "Definition kept.\n\\coqdocemptyline\n\\end{coqdoccode}\n"
    ^ "\\begin{verbatim}\n\\coqdocemptyline\n\\coqdocemptyline\n\\end{verbatim}" in
  let result = compact body in
  check "masked source whitespace was not compacted"
    (not (contains result "\\coqdocemptyline\n\n\\coqdocemptyline"));
  check "declaration was changed" (contains result "Definition kept.");
  check "verbatim content was changed"
    (contains result "\\begin{verbatim}\n\\coqdocemptyline\n\\coqdocemptyline");
  let field = "\\begin{coqdoccode}\n\\coqdocnoindent\n\\coqdoceol\n"
    ^ "\\coqdocindent{1.00em}\n\\coqdoceol\n\\coqdocemptyline\n"
    ^ "\\coqdocindent{1.00em}\n; field : Type\\coqdoceol\n"
    ^ "\\coqdocnoindent\n\\coqdoceol\n\\coqdocemptyline\n"
    ^ "\\coqdocindent{2.00em}\n:= value\\coqdoceol\n"
    ^ "\\coqdocindent{1.00em}\n\\coqdoceol\n\\end{coqdoccode}" in
  let compact_field = compact field in
  check "field padding survived or nonempty indentation changed"
    (compact_field = "\\begin{coqdoccode}\n\\coqdocindent{1.00em}\n"
      ^ "; field : Type\\coqdoceol\n\\coqdocemptyline\n"
      ^ "\\coqdocindent{2.00em}\n:= value\\coqdoceol\n"
      ^ "\\end{coqdoccode}");
  check "blank code still produces an empty frame"
    (compact ("\\begin{coqdoccode}\n\\coqdocindent{1.00em}\n"
      ^ "\\coqdoceol\n\\end{coqdoccode}") = "");
  check "code compaction is not idempotent"
    (compact compact_field = compact_field);
  let template = "\\usepackage{hyperref}\n\\begin{document}" in
  let full = document template in
  check "shared theme loads titlesec too late"
    (contains full "\\usepackage{titlesec}\n\\usepackage{hyperref}");
  check "complete editions unexpectedly restrict references"
    (not (contains full "targets.tex"));
  check "excerpts lost their restricted destinations"
    (contains (document ~restrict_references:true template) "targets.tex");
  let mappings = symbols "×C ⇒ ∀ κ ⦂ ∞ 中文，全角。 ×C" in
  List.iter (fun token -> check ("missing Unicode mapping " ^ token)
    (contains mappings token)) ["{D7}"; "{21D2}"; "{2982}"; "{221E}"];
  check "CJK punctuation must use CTeX" (not (contains mappings "中文"));
  check "fullwidth punctuation must use CTeX" (not (contains mappings "，"));
  List.iter (fun log ->
    check "a broken PDF log was accepted"
      (try check_log log; false with Failure _ -> true))
    ["Missing character: U+2982"; "Overfull \\hbox (1pt too wide)";
     "Overfull \\vbox"; "There were undefined references";
     "multiply defined"; "Token not allowed in a PDF string"];
  check_log "Underfull \\hbox: a loose line, not clipped content";
  print_endline "PDF presentation: whitespace, Unicode and log validation passed."
