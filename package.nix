{
  lib,
  version ? null,
  coq,
  rocq,
  rocqPkgs,
  coqPkgs,
  ...
}:

{
  haskelite = rocqPkgs.mkRocqDerivation {
    pname = "haskelite";
    owner = "zazed";

    inherit version;

    buildInputs = [
      coq
      rocq
      rocq.ocamlPackages.dune_3
      rocq.ocamlPackages.ocaml
      rocqPkgs.stdlib
    ];

    propagatedBuildInputs =
      # Rocq libraries
      with rocqPkgs;
      with coqPkgs;
      with rocq.ocamlPackages;
      [
        rocq-core
        stdlib
      ];

    src = ./.;

    buildPhase = ''
      runHook preBuild
      unset COQPATH
      export COQLIB=${rocq}/lib/rocq
      dune build
      runHook postBuild
    '';

    meta = {
      description = "Haskelite-coq";
      license = lib.licenses.gpl3Only;
    };
  };
}
