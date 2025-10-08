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
          tree-sitter
          python3
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
      }
    );
}
