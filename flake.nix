{
  inputs = {
    fstar.url = "github:FStarLang/FStar";
    nixpkgs.follows = "fstar/nixpkgs";
    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, fstar, nixpkgs, utils, purescript-overlay }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system; 
          overlays = [
            purescript-overlay.overlays.default
          ];
        };
        fstar-pkg = fstar.packages.${system}.fstar;
        z3-pkg = fstar.packages.${system}.z3;

        fstarCmd = pkgs.writeShellScriptBin "fstar" ''
          exec ${fstar-pkg}/bin/fstar.exe \
            --include ${fstar-pkg}/lib/fstar \
            --cache_checked_modules \
            --cache_dir .fstar-cache \
            "$@"
        '';

        buildRuntimeCmd = pkgs.writeShellScriptBin "hoop-build-runtime" ''
          export PATH=${fstar-pkg}/bin:${z3-pkg}/bin:${pkgs.ocaml}/bin:${pkgs.ocamlPackages.js_of_ocaml-compiler}/bin:$PATH

          if [ ! -x ./scripts/build-runtime.sh ]; then
            echo "hoop-build-runtime: Cannot find ./scripts/build-runtime.sh" >&2
            echo "                    Try again in the project root." >&2
            exit 1
          fi
          exec ./scripts/build-runtime.sh "$@"
        '';
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            fstar-pkg
            z3-pkg
            fstarCmd
            buildRuntimeCmd
            pkgs.ocaml
            pkgs.ocamlPackages.findlib
            pkgs.ocamlPackages.zarith
            pkgs.ocamlPackages.js_of_ocaml-compiler
          ] ++ (with pkgs;
          [ purs 
            spago-unstable
            purs-tidy-bin.purs-tidy-0_10_0
            purs-backend-es
            nodejs_24
            pnpm
            esbuild
            gnuplot            
          ]);

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
