{pkgs ? import <nixpkgs> {}}:
let
  package = pkgs.haskell.lib.overrideCabal (import ./default.nix {}) (oldAttrs: {
    testSystemDepends = let oldTestSystemDepends = if oldAttrs ? testSystemDepends
                                                   then oldAttrs.testSystemDepends
                                                   else [];
                        in [ pkgs.haskellPackages.ghcid ] ++ oldTestSystemDepends;
  });
in
  package.env
