{
  description = "F* development environment using official FStar flake";

  inputs = {
    # F* 公式リポジトリを直接参照
    fstar.url = "github:FStarLang/FStar";
    # 公式が使っている nixpkgs のバージョンに合わせることで不整合を防ぐ
    nixpkgs.follows = "fstar/nixpkgs";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, fstar, nixpkgs, utils }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        # 公式 flake から提供されているパッケージを取得
        fstar-pkg = fstar.packages.${system}.fstar;
        z3-pkg = fstar.packages.${system}.z3;
        # libraryへのパスを自動でincludeするラッパーコマンド
        fstarCmd = pkgs.writeShellScriptBin "fstar" ''
          exec ${fstar-pkg}/bin/fstar.exe \
            --include ${fstar-pkg}/lib/fstar \
            --cache_checked_modules \
            --cache_dir .fstar-cache \
            "$@"
        '';
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            fstar-pkg
            z3-pkg
            fstarCmd
            # 抽出(Extraction)やビルドに必要な最小構成
            pkgs.ocaml
            pkgs.ocamlPackages.findlib
            pkgs.ocamlPackages.zarith
          ];

        shellHook = ''
          echo "--- F* Development Environment (Official Flake) ---"
          FSTAR_BIN=$(which fstar.exe)
          FSTAR_ROOT=$(dirname $(dirname "$FSTAR_BIN"))
          echo "F* location: $FSTAR_BIN"
          fstar --version
          z3 --version
        '';
        };
      });
}
