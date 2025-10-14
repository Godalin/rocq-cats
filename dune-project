(lang dune 3.17)

(using coq 0.10)

(generate_opam_files)

(subst disabled)

(name rocq-cats)

(version dev)

(package
 (name rocq-cats)
 (synopsis "rocq-cats")
 (description "A Rocq package for category theory.")
 (depends rocq-prover coq)
 (license MIT))
