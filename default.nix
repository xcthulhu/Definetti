# Can't use ghc843 because glpk doesn't support it
{ compiler ? "ghc822" }:

let

  src = (import <nixpkgs> {}).fetchFromGitHub {
    owner = "NixOS";
    repo  = "nixpkgs";
    inherit (builtins.fromJSON (builtins.readFile ./nixpkgs.json)) rev sha256;
  };

  pkgs = import src {};
  haskellPackages = pkgs.haskell.packages.${compiler}.override {
    overrides = haskellPackagesNew: haskellPackagesOld: rec {
      # TODO: Hopefully this will not be necessary when unliftio 0.2.8.1+ backports to ghc 8.2.2, or glpk supports ghc843
      stm = haskellPackagesNew.callCabal2nix "stm" (pkgs.fetchFromGitHub{
        owner = "haskell";
        repo = "stm";
        rev = "5ea70d4e15d461888866796a164bf9c177a1e8b8";
        sha256 = "1i564qsk6p81b1f8xpv4gp75f0jwh3fcjaldsrxk7qcb0kjkynd3";
      }) {};
    };
  };

in

  haskellPackages.callCabal2nix "definetti" ./. {}
