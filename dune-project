(lang dune 3.17)

(using coq 0.10)

(generate_opam_files)

(subst disabled)

(name rocq-cats)

(version dev)

(authors "Linyu Yang <yly1228@foxmail.com>")

(maintainers "Linyu Yang <yly1228@foxmail.com>")

(homepage https://github.com/Godalin/rocq-cats)

(bug_reports https://github.com/Godalin/rocq-cats)

(license GPL-3.0-or-later)

(package
 (name rocq-cats)
 (synopsis "rocq-cats")
 (description "A Rocq package for category theory.")
 (depends
  (rocq-prover
   (>= 9.0))
  (rocq-stdlib
   (>= 9.0))
  (coq
   (>= 9.0))))
