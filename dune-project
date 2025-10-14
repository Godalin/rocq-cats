(lang dune 3.17)

(using coq 0.10)

(name rocq-cats)

(generate_opam_files)

(package
 (name rocq-cats)
 (synopsis "rocq-cats")
 (description "A Rocq package for category theory.")
 (depends rocq-stdlib)
 (license MIT))
