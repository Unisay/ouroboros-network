{ system ? builtins.currentSystem
, crossSystem ? null
, config ? {}
, overlays ? []
, profiling ? false
}:

let
  sources = import ./nix/sources.nix;
  iohkNix = import sources.iohk-nix {
    sourcesOverride = sources;
  };
  haskellNix = import sources."haskell.nix";
  args = haskellNix // {
    inherit system crossSystem;
    overlays = (haskellNix.overlays or []) ++ overlays;
    config = (haskellNix.config or {}) // config;
  };
  nixpkgs = import sources.nixpkgs;
  pkgs = nixpkgs args;
  haskellPackages = import ./nix/pkgs.nix {
    inherit pkgs profiling;
    src = ./.;
  };
  # TODO: add haskellPackages and fix svclib
  lib = pkgs.lib;
  niv = (import sources.niv {}).niv;
  isOuroboros= with lib; package:
    (package.isHaskell or false) &&
      ((hasPrefix "ouroboros-" package.identifier.name) ||
       (elem package.identifier.name [ "text-class" "bech32" ]));
  filterOuroborosPackages = pkgs.lib.filterAttrs (_: package: isOuroboros package);
  getPackageChecks = pkgs.lib.mapAttrs (_: package: package.checks);
in lib // {
  inherit (pkgs.haskell-nix.haskellLib) collectComponents;
  inherit
    niv
    sources
    haskellPackages
    pkgs
    iohkNix
    isOuroboros
    getPackageChecks
    filterOuroborosPackages;
}
