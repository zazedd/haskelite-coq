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
          dune_3

          rocq-core_9_1
          rocqPackages.stdlib
        ];
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = coqDeps;
        };
      }
    );
}
