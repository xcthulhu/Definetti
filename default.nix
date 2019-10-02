{ compiler ? "ghc844" }:

let
  src = (import <nixpkgs> {}).fetchFromGitHub {
    owner = "NixOS";
    repo  = "nixpkgs";
    inherit (builtins.fromJSON (builtins.readFile ./nixpkgs.json)) rev sha256;
  };
  pkgs = import src {};

  # TODO: Pin haskell-z3

  haskellPackages = pkgs.haskell.packages.${compiler};
  package = haskellPackages.callCabal2nix "definetti" ./. {};

in
pkgs.haskell.lib.overrideCabal package (oldAttrs: {
  buildDepends = [ pkgs.z3 ];
})
