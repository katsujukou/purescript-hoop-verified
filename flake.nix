{
  inputs = {
    # Pinned to a release tag, not master. `flake.lock` already pins the exact
    # revision, so a fresh clone is reproducible either way -- what this buys is
    # that `nix flake update` (run to bump, say, purescript-overlay) cannot drag
    # F* to master as a side effect. Changing the F* version is now an explicit
    # edit to this line, visible in review.
    #
    # Note `nixpkgs.follows = "fstar/nixpkgs"` below: moving F* also moves ocaml
    # and Melange, so the generated bundle is expected to change with it.
    fstar.url = "github:FStarLang/FStar/v2026.08.02";
    nixpkgs.follows = "fstar/nixpkgs";

    # Melange is taken from nixpkgs -- that is, from F*'s nixpkgs, via the
    # `follows` above -- and NOT from its own flake. That is a deliberate
    # choice, measured rather than assumed, and worth recording because the
    # opposite looks obviously better: nixpkgs carries Melange 5.1.0-53 while
    # upstream is two majors ahead at 7.0.1, and 7.0.1 fixes the relocation of
    # relative `mel.module` externals during inlining, which is precisely the
    # mechanism `runtime/ml/melange/hoop_ffi.ml` uses to reach `hoop_prim.js`.
    #
    # Both newer routes were built and run against `scripts/build-runtime.sh`.
    # Neither works, for the same underlying reason:
    #
    #   github:melange-re/melange/7.0.1-55
    #     Builds a *development* version, not the tag: the store path is
    #     `melange-dev` and `melc --version` reports "Melange n/a ()". Its
    #     `dune-package` declares `(lang dune 3.25)`.
    #
    #   nix-ocaml/nix-overlays (Melange's own nixpkgs), melange 7.0.0
    #     A proper release build -- and its `dune-package` also declares
    #     `(lang dune 3.25)`. dune 3.23.1 rejects the language version
    #     outright; dune 3.24.1 gets past that and then fails to resolve
    #     `melange.ppx`.
    #
    # dune's newest *release* is 3.24.2. Version 3.25 is unreleased, so no
    # released dune can consume Melange 7.x's installed metadata. Adopting it
    # would mean pinning dune to master -- exactly the kind of drift the F*
    # pin above exists to prevent, and on the tool that compiles the shipped
    # bundle.
    #
    # Revisit when nixpkgs carries a Melange 7.x that a released dune can
    # read. Until then the two-line `cp hoop_prim.js` in the build script is
    # the cheaper half of the trade, and `engine-smoke.mjs` covers it.
    #
    # One consequence of Melange being the default backend, since the note
    # above predates it: the shipped bundle is now produced by Melange, so
    # moving F* moves the *extracted OCaml* but no longer the code generator.
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
          # Melange is the only backend.
          #
          # Melange resolves its own stdlib through OCAMLPATH rather than by
          # sitting next to melc, so dune cannot find `melange.js` without it.
          export PATH=${fstar-pkg}/bin:${z3-pkg}/bin:${pkgs.ocaml}/bin:${pkgs.ocamlPackages.melange}/bin:${pkgs.dune_3}/bin:${pkgs.esbuild}/bin:$PATH

          # The version component is the OCaml that built *Melange*, which is
          # only the same as `ocamlPackages.ocaml` while both come from this
          # package set. Sourcing Melange elsewhere moves it -- 5.1.0-53 is
          # OCaml 5.3.0, 7.0.0 is 5.2.1, the flake's dev build is 5.5.0 -- and
          # a stale path here does not fail loudly: dune simply reports that it
          # cannot find `melange.js`, which reads like a Melange problem. Hence
          # the check.
          MEL_SITE=${pkgs.ocamlPackages.melange}/lib/ocaml/${pkgs.ocamlPackages.ocaml.version}/site-lib
          if [ ! -d "$MEL_SITE/melange" ]; then
            echo "hoop-build-runtime: no Melange stdlib at $MEL_SITE." >&2
            echo "                    The OCaml version in flake.nix's OCAMLPATH no" >&2
            echo "                    longer matches the one Melange was built with." >&2
            exit 1
          fi
          export OCAMLPATH=$MEL_SITE''${OCAMLPATH:+:$OCAMLPATH}

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
            # dune loads the OCaml compiler for its default context and fails
            # with "Program ocamlc not found" without it, whatever melc brings.
            pkgs.ocaml
            # dune resolves `melange.ppx` through findlib; without it the
            # Melange build fails with "Library melange.ppx not found".
            pkgs.ocamlPackages.findlib
            pkgs.ocamlPackages.melange
            pkgs.dune_3
            # `melange.ppx` -- which `runtime/ml/melange/hoop_ffi.ml` needs for
            # its `[@mel.*]` attributes -- depends on ppxlib, and dune resolves
            # it through OCAMLPATH. It used to arrive only as a transitive
            # dependency of js_of_ocaml-ppx, so it was listed explicitly against
            # the day the jsoo backend was dropped. That day came; this line is
            # what kept the Melange build working through it.
            pkgs.ocamlPackages.ppxlib
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
