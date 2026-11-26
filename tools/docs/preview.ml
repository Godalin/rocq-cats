(* Preview a continuous range of complete modules in library reading order.
   Formatting follows bilingual filtering and compiled-reference processing. *)

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

(* Feed the original module context and selected proof to Alectryon's native
   LaTeX frontend. Sentence annotations in the source select visible states. *)

let proof_input ?(kind = "Example") ?(ending = "Qed.") ~name source =
  let start = Pdf.find source (kind ^ " " ^ name) 0 in
  let ending = Pdf.find source ending start + String.length ending in
  "\\begin{alectryon}{coq}{none}\n" ^ String.sub source 0 start
  ^ "\n\\end{alectryon}\n\\begin{alectryon}{coq}{in}\n"
  ^ String.sub source start (ending - start) ^ "\n\\end{alectryon}\n"
