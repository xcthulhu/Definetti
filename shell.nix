{pkgs ? import <nixpkgs> {}}:
let
  package = pkgs.haskell.lib.overrideCabal (import ./default.nix {}) (oldAttrs: {
    testSystemDepends = let oldTestSystemDepends = if oldAttrs ? testSystemDepends
                                                   then oldAttrs.testSystemDepends
                                                   else [];
                        in oldTestSystemDepends ++ [ pkgs.haskellPackages.ghcid
                                                     pkgs.haskellPackages.cabal-install
                                                   ];
  });
in
  package.env
