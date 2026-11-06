open Docs_filter.Filter

let contains text part =
  let rec loop i =
    i + String.length part <= String.length text
    && (starts text i part || loop (i + 1))
  in
  loop 0

let check message condition = if not condition then failwith message

let position_laws source filtered =
  check "byte length changed" (String.length source = String.length filtered);
  String.iteri (fun i c ->
    if c = '\n' || c = '\r' then
      check "newline moved" (filtered.[i] = c)) source;
  let erased s =
    let out = Bytes.of_string s in
    List.iter (fun b -> blank out b.first b.last) (blocks s);
    Bytes.to_string out
  in
  check "code or ordinary comments changed" (erased source = erased filtered)

let () =
  let source =
    "(** * English heading\n\nRead [中文 identifiers] and [∀ x, x ≈ x]. *)\r\n\n"
    ^ "(** * 中文标题\n\n使用 [English identifiers] 和 [∀ x, x ≈ x]。 *)\n\n"
    ^ "Definition quoted := \"(** a fake comment *) \"\"*)\"\"\".\n"
    ^ "(* outer (* nested *) \"*)\" *)\n"
    ^ "(** printing ⇒ %\\Rightarrow% #&rArr;# *)\n"
    ^ "(* begin hide *)\nDefinition hidden := tt.\n(* end hide *)\n"
    ^ "(** [OnlyCode] << quoted 中文 >> $English$ *)\n"
    ^ "(** @lang both\n%\\begin{tikzcd} A \\arrow[r, \"f\"] & B"
    ^ "\\end{tikzcd}%\n*)\n"
  in
  let en, warnings = filter En source in
  let zh, _ = filter Zh source in
  check "paired comments should be classified" (warnings = []);
  check "English prose missing" (contains en "English heading");
  check "Chinese prose leaked" (not (contains en "中文标题"));
  check "Chinese prose missing" (contains zh "中文标题");
  check "English prose leaked" (not (contains zh "English heading"));
  List.iter (fun s ->
    check "printing directive lost" (contains s "printing ⇒");
    check "shared LaTeX diagram lost" (contains s "\\begin{tikzcd}");
    check "proof visibility lost" (contains s "(* begin hide *)");
    check "neutral code block lost" (contains s "[OnlyCode]")) [en; zh];
  position_laws source en; position_laws source zh;
  let mixed = "(** English sentence.\n中文说明。 *)\nDefinition x := tt.\n" in
  List.iter (fun language ->
    let result, warnings = filter language mixed in
    check "ambiguous prose was discarded" (result = mixed);
    check "ambiguous prose was not reported" (List.length warnings = 1)) [En; Zh];
  let marked =
    "(** @lang en\nAn explicit English block. *)\n"
    ^ "(** @lang zh\nType 值的中文说明。 *)\n"
    ^ "(** @lang both\n共同标题 / Shared heading *)\n"
  in
  let en, warnings = filter En marked in
  let zh, _ = filter Zh marked in
  check "explicit markers warned" (warnings = []);
  check "marker rendered as prose" (not (contains en "@lang"));
  check "explicit language leaked" (not (contains zh "explicit English"));
  check "shared block missing" (contains en "Shared heading" && contains zh "共同标题");
  position_laws marked en; position_laws marked zh;
  let metadata = "DIGEST " ^ Digest.to_hex (Digest.string source) ^ "\nFExample\n" in
  let generated = glob ~original:source ~filtered:en metadata in
  check "glob offsets changed" (contains generated "\nFExample\n");
  check "glob digest not updated"
    (starts generated 0 ("DIGEST " ^ Digest.to_hex (Digest.string en)));
  let aliases = metadata
    ^ "proj 1:2 <> eqι\nbinder 3:4 <> Γ:1\nind 5:6 <> Tree\n"
    ^ "R5:6 Example <> eqι:2 meth\nR7:8 Example <> Γ:1 var\n"
    ^ "R9:10 Example <> Γ:3 var\nR11:12 Other <> Γ:3 var\n"
    ^ "R13:14 Example <> Tree:4 ind\n" in
  let normalized = glob ~original:source ~filtered:en aliases in
  check "field alias not resolved" (contains normalized "Example <> eqι meth");
  check "declared binder lost" (contains normalized "Example <> Γ:1 var");
  check "missing local binder linked" (not (contains normalized "Example <> Γ:3 var"));
  check "external metadata changed" (contains normalized "Other <> Γ:3 var");
  check "recursive type alias not resolved" (contains normalized "Example <> Tree ind");
  check "stale metadata accepted"
    (try ignore (glob ~original:source ~filtered:en "DIGEST stale\n"); false
     with Invalid_argument _ -> true);
  check "unterminated comment accepted"
    (try ignore (filter En "(* outer (* nested *)"); false
     with Invalid_argument _ -> true);
  print_endline "Documentation filtering: lexical, language and position checks passed."
