# Supply Dune independently; use the caller's Rocq and OCaml environment.
let
  nixpkgs = builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/d357a2b54f0b6dc4aeb4e993190a52cf151b6f24.tar.gz";
    sha256 = "sha256-Thn0OE71NF80ZfOMGCgJvKtbCcnnz0fToT/qsvb/Gtc=";
  };
  pkgs = import nixpkgs {};
in
pkgs.mkShellNoCC {
  packages = [ pkgs.ocamlPackages.dune_3 ];
}
