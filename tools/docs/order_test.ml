open Docs_order.Order

let check label condition = if not condition then failwith label

let rejects f = try ignore (f ()); false with Failure _ -> true

let () =
  let discovered = ["Cat/Core.v"; "Cat/More.v"; "Book/Example.v"; "New.v"] in
  check "partial preferences dropped or reordered unlisted modules"
    (prefer ["Book"; "Cat/Core.v"] discovered =
      ["Book/Example.v"; "Cat/Core.v"; "Cat/More.v"; "New.v"]);
  check "overlapping file/directory preferences duplicated modules"
    (prefer ["Cat/Core.v"; "Cat"] discovered = discovered);
  check "repeated preference accepted"
    (rejects (fun () -> prefer ["Cat"; "Cat"] discovered));
  check "unknown preference accepted"
    (rejects (fun () -> prefer ["Absent.v"] discovered));
  check "non-library references became import edges"
    (imports "FCats.Cat.Core\nR1:2 Cats.Set.Core <> <> lib\n\
       R3:4 Cats.Other <> term def\nR5:6 Cats.Set.Core <> <> lib\n"
      = ["Cats.Set.Core"]);
  let dependencies = function
    | "Core" -> ["Set"]
    | "Set" -> ["Meta"]
    | "Client" -> ["Helper"; "Core"]
    | "Helper" -> ["Core"]
    | _ -> [] in
  let ordered = arrange ~dependencies
    ["Core"; "Client"; "Independent"; "Helper"; "Set"; "Meta"; "New"] in
  check "dependencies or manual preferences lost"
    (ordered = ["Meta"; "Set"; "Core"; "Helper"; "Client"; "Independent"; "New"]);
  check "independent module changed"
    (arrange ~dependencies:(fun _ -> []) ["Only"] = ["Only"]);
  check "dependency cycle accepted"
    (rejects (fun () -> arrange
      ~dependencies:(function "A" -> ["B"] | "B" -> ["A"] | _ -> [])
      ["Entry"; "A"; "B"]));
  print_endline "Reading order: sparse preferences, imports and topology passed."
