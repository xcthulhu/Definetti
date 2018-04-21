{ bootstrap ? import <nixpkgs> {}, compiler ? "ghc822" }:
(import ./default.nix { inherit bootstrap compiler; }).env
