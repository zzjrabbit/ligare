{
  description = "Ligare language development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        haskellEnv = pkgs.haskellPackages.ghcWithPackages (hp: with hp; [
          cabal-install
          haskell-language-server
          megaparsec
        ]);
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            haskellEnv
            pkgs.haskellPackages.fourmolu
            pkgs.cabal-install
          ];
        };
      });
}

