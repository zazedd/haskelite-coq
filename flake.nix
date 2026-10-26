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

        latex-packages = with pkgs; [
          (texlive.combine {
            inherit (texlive)
              sttools
              scheme-medium
              framed
              titlesec
              cleveref
              multirow
              wrapfig
              tabu
              threeparttable
              threeparttablex
              makecell
              environ
              biblatex
              biber
              fvextra
              upquote
              catchfile
              xstring
              csquotes
              minted
              dejavu
              comment
              footmisc
              xltabular
              ltablex
              dashrule
              ifmtarg
              soul
              xpatch
              preprint
              ;
          })
        ];
      in
      {
        devShells = {
          default = pkgs.mkShell {
            buildInputs = coqDeps ++ devDeps;
          };
          paper = pkgs.mkShell {
            buildInputs = [
              pkgs.texliveFull
              latex-packages
            ];
          };
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
