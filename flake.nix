{
  description = "Haskelite-coq build and devshell";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        coqDeps = with pkgs; [
          ocaml
          dune_3

          coq_8_20
          coqPackages_8_20.stdlib
        ];

        devDeps = with pkgs; [
          coqPackages_8_20.coq-lsp
        ];
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = coqDeps ++ devDeps;
        };

        packages.default = pkgs.coqPackages_8_20.mkCoqDerivation {
          pname = "haskelite";
          owner = "zazedd";
          version = "0.1.0";
          src = ./.;

          buildInputs = coqDeps;
          propagatedBuildInputs = coqDeps;

          buildPhase = ''
            dune build
          '';

          installPhase = ''
            mkdir -p $out/lib/coq/user-contrib/haskelite
            cp -r _build/default/theories/* $out/lib/coq/user-contrib/haskelite
          '';
        };
      }
    );
}
