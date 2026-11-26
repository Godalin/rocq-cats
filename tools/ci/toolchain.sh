#!/bin/sh
# Print the portable build toolchain, including optional and compiler dependencies.
# CI forces colored output even when redirected; the lock is plain text.
packages=$(opam list "$@" --color=never --installed --short --columns=package \
  --recursive --post --depopts \
  --required-by=ocaml-base-compiler,dune,rocq-core,rocq-stdlib,rocq-elpi,elpi) \
  || exit "$?"
# This Linux-only system-header probe supplies no compiler or Rocq artifacts.
printf '%s\n' "$packages" | sed '/^conf-linux-libc-dev[.]/d'
