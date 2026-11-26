type language = En | Zh
type diagnostic = { line : int; message : string }
type block = { first : int; last : int; body : int; stop : int }
type kind = English | Chinese | Neutral | Mixed

(** Disable built-in symbol substitutions using native coqdoc directives.
    Explicit printing directives in the source remain available. *)

let printing_preamble =
  ["*"; "|"; "->"; "->~"; "->~~"; "<-"; "<->"; "=>"; "<="; ">=";
   "<>"; "~"; "/\\"; "\\/"; "|-"; "forall"; "exists"; "Π"; "λ"]
  |> List.map (fun token -> "(** remove printing " ^ token ^ " *)\n")
  |> String.concat ""

let starts s i token =
  i + String.length token <= String.length s
  && String.sub s i (String.length token) = token

let space = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false

let only_space s first last =
  let rec loop i = i = last || (space s.[i] && loop (i + 1)) in
  loop first

let line_at s pos =
  let n = ref 1 in
  for i = 0 to pos - 1 do if s.[i] = '\n' then incr n done;
  !n

let fail s pos message =
  invalid_arg (Printf.sprintf "line %d: %s" (line_at s pos) message)

(* Rocq strings escape quotes by doubling them, including inside comments. *)

let string_end s first =
  let rec loop i =
    if i >= String.length s then fail s first "unterminated string"
    else if starts s i "\"\"" then loop (i + 2)
    else if s.[i] = '"' then i + 1
    else loop (i + 1)
  in
  loop (first + 1)

let comment_end s first =
  let rec loop depth i =
    if i >= String.length s then fail s first "unterminated comment"
    else if starts s i "(*" then loop (depth + 1) (i + 2)
    else if starts s i "*)" then
      if depth = 1 then i + 2 else loop (depth - 1) (i + 2)
    else if s.[i] = '"' then loop depth (string_end s i)
    else loop depth (i + 1)
  in
  loop 1 (first + 2)

let blocks s =
  let rec loop i acc =
    if i = String.length s then List.rev acc
    else if s.[i] = '"' then loop (string_end s i) acc
    else if starts s i "(*" then
      let last = comment_end s i in
      let acc =
        if starts s i "(**" && last >= i + 5 then
          { first = i; last; body = i + 3; stop = last - 2 } :: acc
        else acc
      in
      loop last acc
    else loop (i + 1) acc
  in
  loop 0 []

let blank out first last =
  for i = first to last - 1 do
    if not (Bytes.get out i = '\n' || Bytes.get out i = '\r') then
      Bytes.set out i ' '
  done

(** Hide prose as an ordinary comment, preserving every byte position.
    Bare padding inside a declaration becomes visible indentation in coqdoc;
    native comment delimiters let coqdoc skip that padding instead. *)

let suppress out b =
  blank out b.first b.last;
  Bytes.blit_string "(*" 0 out b.first 2;
  Bytes.blit_string "*)" 0 out (b.last - 2) 2

let cjk u =
  (u >= 0x3400 && u <= 0x9fff)
  || (u >= 0xf900 && u <= 0xfaff)
  || (u >= 0x20000 && u <= 0x323af)

(* Language detection ignores coqdoc code, math and raw-output islands. *)

let classify s first last =
  let en = ref false and zh = ref false in
  let rec bracket depth i =
    if i >= last then last
    else if s.[i] = '[' then bracket (depth + 1) (i + 1)
    else if s.[i] = ']' then
      if depth = 1 then i + 1 else bracket (depth - 1) (i + 1)
    else bracket depth (i + 1)
  in
  let rec island closing i =
    if i >= last then last
    else if starts s i closing then i + String.length closing
    else island closing (i + 1)
  in
  let rec loop i =
    if i < last then
      if starts s i "(*" then loop (comment_end s i)
      else if s.[i] = '[' then loop (bracket 1 (i + 1))
      else if starts s i "<<" then loop (island ">>" (i + 2))
      else if List.mem s.[i] ['$'; '%'; '#'] then
        loop (island (String.make 1 s.[i]) (i + 1))
      else
        let d = String.get_utf_8_uchar s i in
        if not (Uchar.utf_decode_is_valid d) then fail s i "invalid UTF-8";
        let u = Uchar.to_int (Uchar.utf_decode_uchar d) in
        if cjk u then zh := true;
        if (u >= 65 && u <= 90) || (u >= 97 && u <= 122) then en := true;
        loop (i + Uchar.utf_decode_length d)
  in
  loop first;
  match !en, !zh with
  | true, false -> English
  | false, true -> Chinese
  | false, false -> Neutral
  | true, true -> Mixed

let body_text s b = String.trim (String.sub s b.body (b.stop - b.body))

let directive s b =
  let t = body_text s b in
  List.exists (fun prefix -> starts t 0 prefix)
    ["printing "; "remove printing "; "begin hide"; "end hide";
     "begin show"; "end show"]

let marker s b =
  let rec trim i = if i < b.stop && space s.[i] then trim (i + 1) else i in
  let first = trim b.body in
  if not (starts s first "@lang ") then None
  else
    let rec word i =
      if i < b.stop && not (space s.[i]) then word (i + 1) else i
    in
    let last = word (first + 6) in
    let name = String.sub s (first + 6) (last - first - 6) in
    let kind = match name with
      | "en" -> English | "zh" -> Chinese | "both" -> Neutral
      | _ -> fail s first "expected @lang en, @lang zh or @lang both"
    in
    Some (kind, first, last)

(** Keep every non-documentation byte at its original position. *)

let filter language source =
  let out = Bytes.of_string source in
  let diagnostics = ref [] in
  let warn b message =
    diagnostics := { line = line_at source b.first; message } :: !diagnostics
  in
  let keep b kind =
    match language, kind with
    | En, Chinese | Zh, English -> suppress out b
    | _ -> ()
  in
  let explicit b =
    match marker source b with
    | None -> false
    | Some (kind, first, last) ->
        blank out first last; keep b kind; true
  in
  let kind b = classify source b.body b.stop in
  let rec loop = function
    | [] -> ()
    | b :: rest when directive source b -> loop rest
    | b :: rest when explicit b -> loop rest
    | a :: b :: rest
      when kind a = English && marker source b = None
        && not (directive source b) && only_space source a.last b.first
        && List.mem (kind b) [Chinese; Mixed] ->
        keep a English; keep b Chinese; loop rest
    | b :: rest ->
        let k = kind b in
        (match k with
         | Mixed -> warn b "unclassified mixed-language block; kept in both outputs"
         | English | Chinese ->
             warn b "unpaired language block; add its translation or an @lang marker"
         | Neutral -> ());
        keep b k; loop rest
  in
  loop (blocks source);
  Bytes.to_string out, List.rev !diagnostics

(* Keep these declarations visible in coqdoc's proof-hiding mode. The
   generated copy uses native show markers around each complete command. *)

let show_declarations source =
  let length = String.length source in
  let rec command_end i =
    if i = length then fail source i "unterminated declaration"
    else if starts source i "(*" then command_end (comment_end source i)
    else if source.[i] = '"' then command_end (string_end source i)
    else if starts source i ".." then command_end (i + 2)
    else if source.[i] = '.'
      && (i + 1 = length || space source.[i + 1] || starts source (i + 1) "(*")
    then i + 1
    else command_end (i + 1)
  in
  let commands = ["Minks.Mixin"; "Minks.Struct"; "Abbreviation"] in
  let rec scan line_start i edits packed =
    if i = length then List.rev edits, packed
    else if starts source i "(*" then scan None (comment_end source i) edits packed
    else if source.[i] = '"' then scan None (string_end source i) edits packed
    else if source.[i] = '\n' then scan (Some (i + 1)) (i + 1) edits packed
    else if space source.[i] then scan line_start (i + 1) edits packed
    else match line_start with
    | None -> scan None (i + 1) edits packed
    | Some opening ->
      match List.find_opt (fun command ->
        let next = i + String.length command in
        next < length && starts source i command && space source.[next]) commands with
      | None -> scan None (i + 1) edits packed
      | Some command ->
          let after = i + String.length command in
          let ending = command_end after in
          let packed = if command = "Minks.Struct" then
            let rec name j = if space source.[j] then name (j + 1) else j in
            (i, name after) :: packed
            else packed in
          let edits = (ending, "\n(* end show *)\n")
            :: (opening, "(* begin show *)\n") :: edits in
          scan None ending edits packed
  in
  scan (Some 0) 0 [] []

let insert source edits =
  let result = Buffer.create (String.length source) in
  let last = List.fold_left (fun last (at, text) ->
    Buffer.add_substring result source last (at - last);
    Buffer.add_string result text;
    at) 0 edits in
  Buffer.add_substring result source last (String.length source - last);
  Buffer.contents result

(** Remap compiled byte ranges past the coqdoc preamble and show markers.
    The generated copy receives its own source digest. *)

let glob ?(prefix = "") ?(edits = []) ?(packed = []) ~original ~filtered contents =
  let first = try String.index contents '\n' with Not_found -> String.length contents in
  let header = String.sub contents 0 first in
  let digest s = Digest.to_hex (Digest.string s) in
  if header <> "DIGEST " ^ digest original then
    invalid_arg "stale or unsupported .glob; rebuild the original Rocq module";
  let lines = String.split_on_char '\n' contents in
  let words line = String.split_on_char ' ' line |> List.filter ((<>) "") in
  let library = List.find_opt (fun s -> starts s 0 "F") lines
    |> Option.map (fun s -> String.sub s 1 (String.length s - 1)) in
  let binders = Hashtbl.create 32 and declarations = Hashtbl.create 32 in
  List.iter (fun line -> match words line with
    | ["binder"; _; section; name] -> Hashtbl.replace binders (section, name) ()
    | [kind; _; section; name] when not (starts kind 0 "R") ->
        Hashtbl.replace declarations (section, name) ()
    | _ -> ()) lines;
  let normalize line = match words line with
    | [pos; lib; section; name; kind]
      when starts pos 0 "R" && Some lib = library
        && not (Hashtbl.mem binders (section, name)) ->
        (match String.rindex_opt name ':' with
         | Some i when i + 1 < String.length name
             && String.for_all (fun c -> c >= '0' && c <= '9')
               (String.sub name (i + 1) (String.length name - i - 1)) ->
             let base = String.sub name 0 i in
             if Hashtbl.mem declarations (section, base) then
               Some (String.concat " " [pos; lib; section; base; kind])
             else if kind = "var" then None else Some line
         | _ -> Some line)
    | _ -> Some line
  in
  (* Undeclared local aliases in Rocq 9.0 metadata have no link target.
     Resolve field aliases to their declaration; other locals remain text. *)

  let shift n =
    let n = int_of_string n in
    string_of_int (if n < 0 then n else
      List.fold_left (fun position (at, text) ->
        if at <= n then position + String.length text else position)
        (n + String.length prefix) edits)
  in
  let range_bounds range = match String.split_on_char ':' range with
    | [first; last] -> first, last
    | _ -> invalid_arg "unsupported .glob byte range"
  in
  let shift_range range =
    let first, last = range_bounds range in
    shift first ^ ":" ^ shift last
  in
  let shift_line line = match words line with
    | [pos; lib; section; name; kind] when starts pos 0 "R" ->
        String.concat " " ["R" ^ shift_range
          (String.sub pos 1 (String.length pos - 1)); lib; section; name; kind]
    | [kind; range; section; name] ->
        let first, _ = range_bounds range in
        (match List.assoc_opt (int_of_string first) packed with
         | None -> String.concat " " [kind; shift_range range; section; name]
         | Some at ->
             (* Elpi locates generated members on the entire command. Anchor
                them on the packed name so each anchor is emitted once. *)
             let position = shift (string_of_int at) in
             let range = position ^ ":" ^ position in
             let declaration = String.concat " " [kind; range; section; name] in
             let constructor = "Make" ^ name in
             if kind = "rec" && not (Hashtbl.mem declarations (section, constructor))
               && starts original at name
               && (let next = at + String.length name in
                   space original.[next] || original.[next] = '.') then
               declaration ^ "\n"
               ^ String.concat " " ["constr"; range; section; constructor]
             else declaration)
    | _ -> line
  in
  "DIGEST " ^ digest (prefix ^ filtered) ^ "\n"
  ^ (List.tl lines |> List.filter_map normalize |> List.map shift_line
      |> String.concat "\n")

let prepare language source metadata =
  let filtered, diagnostics = filter language source in
  let edits, packed = show_declarations source in
  let filtered = insert filtered edits in
  let prefix = printing_preamble in
  prefix ^ filtered, glob ~prefix ~edits ~packed ~original:source ~filtered metadata,
  diagnostics
