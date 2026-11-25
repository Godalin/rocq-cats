#!/bin/sh
# Print the installed build toolchain, including optional and compiler dependencies.
exec opam list "$@" --installed --short --columns=package --recursive --post --depopts \
  --required-by=ocaml-base-compiler,dune,rocq-core,rocq-stdlib,rocq-elpi,elpi
