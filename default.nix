{ compiler ? "ghc843" }:

let

  src = (import <nixpkgs> {}).fetchFromGitHub {
    owner = "NixOS";
    repo  = "nixpkgs";
    inherit (builtins.fromJSON (builtins.readFile ./nixpkgs.json)) rev sha256;
  };

  pkgs = import src {};

  haskellPackages = pkgs.haskell.packages.${compiler};

in

  haskellPackages.callCabal2nix "definetti" ./. {}
