{ compiler ? "ghc822" }:

let

  src = (import <nixpkgs> {}).fetchFromGitHub {
    owner = "NixOS";
    repo  = "nixpkgs";
    inherit (builtins.fromJSON (builtins.readFile ./nixpkgs.json)) rev sha256;
  };

  pkgs = import src {};

  package = pkgs.haskell.packages.${compiler}.callCabal2nix "definetti" ./. { };

in

  pkgs.haskell.lib.overrideCabal package (oldAttrs: {
    # TODO: Maybe don't need this?
    testSystemDepends = [ pkgs.glpk ];
  })
