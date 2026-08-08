{
  inputs = {
    # Pinned to a release tag, not master. `flake.lock` already pins the exact
    # revision, so a fresh clone is reproducible either way -- what this buys is
    # that `nix flake update` (run to bump, say, purescript-overlay) cannot drag
    # F* to master as a side effect. Changing the F* version is now an explicit
    # edit to this line, visible in review.
    #
    # Note `nixpkgs.follows = "fstar/nixpkgs"` below: moving F* also moves ocaml
    # and js_of_ocaml, so the generated bundle is expected to change with it.
    fstar.url = "github:FStarLang/FStar/v2026.08.02";
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
            pkgs.ocamlPackages.js_of_ocaml-ppx
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
