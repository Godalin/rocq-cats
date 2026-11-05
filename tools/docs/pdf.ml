(* PDF presentation changes apply only after coqdoc has processed the shared,
   compiled sources; source positions and mathematical declarations stay intact. *)

(* PDF 排版调整仅作用于 coqdoc 处理共享编译源码后的结果，不改变源码位置或数学声明。 *)

let compact body =
  let lines = String.split_on_char '\n' body in
  let rec loop code empty = function
    | [] -> []
    | line :: rest ->
        let trimmed = String.trim line in
        if trimmed = "\\begin{coqdoccode}" then line :: loop true false rest
        else if trimmed = "\\end{coqdoccode}" then line :: loop false false rest
        else if code && trimmed = "\\coqdocemptyline" then
          if empty then loop code true rest else line :: loop code true rest
        else if trimmed = "" then line :: loop code empty rest
        else line :: loop code false rest
  in
  String.concat "\n" (loop false false lines)

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
