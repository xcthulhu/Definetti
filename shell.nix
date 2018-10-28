{pkgs ? import <nixpkgs> {}}:
let
  package = pkgs.haskell.lib.overrideCabal (import ./default.nix {}) (oldAttrs: {
    testSystemDepends = let oldTestSystemDepends = if oldAttrs ? testSystemDepends
                                                   then oldAttrs.testSystemDepends
                                                   else [];
                        in oldTestSystemDepends ++ [ pkgs.haskellPackages.ghcid
                                                     pkgs.haskellPackages.cabal-install
                                                   ];
    buildDepends      = let oldBuildDepends = if oldAttrs ? buildDepends
                                              then oldAttrs.buildDepends
                                              else [];
                        in oldBuildDepends ++ [ pkgs.git 
                                                pkgs.stack 
                                              ];

  });
in
  package.env
