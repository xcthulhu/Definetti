{ bootstrap ? import <nixpkgs> {} }:
(import ./default.nix { inherit bootstrap; }).env
