{ system ? builtins.currentSystem
, crossSystem ? null
, config ? {}
, profiling ? false
, commonLib ? import ./lib.nix { inherit system crossSystem config profiling; }
, pkgs ? commonLib.pkgs
, customConfig ? {}
, interactive ? false
, gitrev ? commonLib.iohkNix.commitIdFromGitRepoOrZero ./.git
, withHoogle ? true
}:

let
  lib = commonLib.pkgs.lib;
  inherit (commonLib) haskellPackages;

  recRecurseIntoAttrs = with pkgs; pred: x: if pred x then recurseIntoAttrs (lib.mapAttrs (n: v: if n == "buildPackages" then v else recRecurseIntoAttrs pred v) x) else x;
  projectHaskellPackages = recRecurseIntoAttrs (x: with pkgs; lib.isAttrs x && !lib.isDerivation x)
    # we are only intersted in listing the project packages
    (pkgs.lib.filterAttrs (with pkgs.haskell-nix.haskellLib; (n: p: p != null && (isLocalPackage p && isProjectPackage p) || n == "shellFor"))
      haskellPackages);

  self = with commonLib; {
    haskellPackages = projectHaskellPackages;
    inherit (iohkNix) check-hydra;

    # `tests` are the test suites which have been built.
    tests = collectComponents "tests" isOuroboros haskellPackages;
    # `checks` are the result of executing the tests.
    checks = pkgs.recurseIntoAttrs (getPackageChecks (filterOuroborosPackages haskellPackages));
    # `benchmarks` are only built, not run.
    benchmarks = collectComponents "benchmarks" isOuroboros haskellPackages;

    validate-mainnet-test = import ./nix/validate-mainnet.nix
      {pkgs = commonLib.pkgs; byron-db-converter = haskellPackages.ouroboros-consensus.exes.ouroboros-consensus; };

    shell = haskellPackages.shellFor {

      #packages = ps: with ps; [
      #  haskellPackages.ouroboros-network
      #  haskellPackages.ouroboros-consensus
      #  haskellPackages.cardano-config
      #];

      # Builds a Hoogle documentation index of all dependencies,
      # and provides a "hoogle" command to search the index.
      inherit withHoogle;

      # You might want some extra tools in the shell (optional).
      buildInputs = (with haskellPackages; [
        #weeder.components.exes.weeder
        #hlint.components.exes.hlint
        #cabal-install.components.exes.cabal
        #ghcid.components.exes.ghcid
        pkgs.haskellPackages.terminfo
      ]) ++ (with pkgs; [
        pkgconfig
        sqlite-interactive
        tmux
      ]);

      # Prevents cabal from choosing alternate plans, so that
      # *all* dependencies are provided by Nix.
      exactDeps = true;
    };

  };

in self
