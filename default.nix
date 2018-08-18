{ bootstrap ? import <nixpkgs> {}, compiler ? "ghc822" }:

let

  nixpkgs = builtins.fromJSON (builtins.readFile ./nixpkgs.json);

  src = bootstrap.fetchFromGitHub {
    owner = "NixOS";
    repo  = "nixpkgs";
    inherit (nixpkgs) rev sha256;
  };

  pkgs = import src {};

  package = pkgs.haskell.packages.${compiler}.callCabal2nix "definetti" ./. { };

in

  pkgs.haskell.lib.overrideCabal package (oldAttrs: {
    testSystemDepends = [ pkgs.glpk ];
  })
