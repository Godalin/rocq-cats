(lang dune 3.20)

(using coq 0.10)

(generate_opam_files)

(package
 (name rocq-categories)
 (synopsis "rocq-cats")
 (description "A Rocq package for category theory.")
 (depends rocq-stdlib)
 (license MIT))
