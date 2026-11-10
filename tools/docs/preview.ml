(* Preview a continuous range of complete modules in library reading order.
   Formatting follows bilingual filtering and compiled-reference processing. *)

(* 按全库阅读顺序预览连续的完整模块。
   排版在双语过滤及编译引用处理后进行。 *)

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

(* 将原始模块上下文及选定证明交给 Alectryon 原生 LaTeX 前端。
   源码中的语句注解选定要显示的状态。 *)

let proof_input ?(kind = "Example") ?(ending = "Qed.") ~name source =
  let start = Pdf.find source (kind ^ " " ^ name) 0 in
  let ending = Pdf.find source ending start + String.length ending in
  "\\begin{alectryon}{coq}{none}\n" ^ String.sub source 0 start
  ^ "\n\\end{alectryon}\n\\begin{alectryon}{coq}{in}\n"
  ^ String.sub source start (ending - start) ^ "\n\\end{alectryon}\n"
