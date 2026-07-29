#!/usr/bin/env bash
#
# runtime/Hoop.Runtime.fst --[F* verification]--> OCaml --[js_of_ocaml]--> src/Hoop/Engine.js
#
# Every tool comes from the nix devShell. Intermediate artifacts land in build/.
# src/Hoop/Engine.js is generated -- do not edit it by hand.
#
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FST_DIR="$ROOT/runtime"
ML_DIR="$ROOT/runtime/ml"
BUILD="$ROOT/build"
OUT="$ROOT/src/Hoop/Engine.js"

# Checked files go where the LSP looks for them. The flake's `fstar` wrapper
# passes `--cache_dir .fstar-cache` relative to its cwd, and the VS Code
# extension runs F* with cwd set to the directory holding Hoop.fst.config.json
# (the repository root), so both resolve to this same directory. Verifying
# every module here keeps the editor from reporting stale checked files.
CACHE="$ROOT/.fstar-cache"

# Modules to verify, in dependency order. Interfaces (.fsti) are picked up
# automatically when present.
VERIFY_MODULES=(Hoop.Runtime Hoop.Runtime.Properties Hoop.Runtime.Test)

# Modules to extract to OCaml. Only the runtime itself becomes JavaScript;
# the others are specifications and proofs.
EXTRACT_MODULES=(Hoop.Runtime)

# Names the generated JS exposes. Must match the `export` calls in hoop_ffi.ml.
# All of them are uncurried multi-argument functions -- the PureScript side
# imports them through Fn2 / Fn3.
EXPORTS=(pureImpl bindImpl performImpl withImpl runImpl
         mkFullClauseImpl mkFastClauseImpl mkReturnImpl undefinedReturnImpl
         emptyClausesImpl emptyHandlersImpl insertClauseImpl insertClausesImpl)

# Name of the function js_of_ocaml wraps the generated code in. Engine.js calls it.
INIT_FN=hoopInit

log() { printf '\033[1;34m==>\033[0m %s\n' "$*"; }

# Report which binaries are actually being used. A stray fstar.exe or
# js_of_ocaml earlier on PATH otherwise causes confusing failures.
log "Tools"
for t in fstar.exe ocamlc js_of_ocaml; do
  p="$(command -v "$t" || true)"
  if [ -z "$p" ]; then
    echo "  $t: not found. Are you inside the nix devShell?" >&2
    exit 1
  fi
  printf '  %-12s %s\n' "$t" "$p"
done

# fstar.exe locates its standard library relative to its own path. A manually
# installed standalone binary has no ulib next to it and fails with
# "Namespace FStar cannot be found".
FSTAR_ULIB="$(dirname "$(dirname "$(command -v fstar.exe)")")/lib/fstar/ulib"
if [ ! -d "$FSTAR_ULIB" ]; then
  echo "ERROR: no ulib next to $(command -v fstar.exe) (looked in $FSTAR_ULIB)." >&2
  echo "       A different fstar.exe on PATH is probably being picked up." >&2
  exit 1
fi

rm -rf "$BUILD"
mkdir -p "$BUILD/ml" "$CACHE"

# --- 1. Verify -------------------------------------------------------------
log "[1/4] Verifying"
for m in "${VERIFY_MODULES[@]}"; do
  for ext in fsti fst; do
    src="$FST_DIR/$m.$ext"
    [ -f "$src" ] || continue
    printf '  %s\n' "$m.$ext"
    fstar.exe --cache_checked_modules --cache_dir "$CACHE" \
      --include "$FST_DIR" "$src"
  done
done

# --- 2. Extract to OCaml ---------------------------------------------------
log "[2/4] Extracting to OCaml"
for m in "${EXTRACT_MODULES[@]}"; do
  fstar.exe --cache_checked_modules --cache_dir "$CACHE" \
    --include "$FST_DIR" --codegen OCaml --extract "$m" \
    --odir "$BUILD/ml" "$FST_DIR/$m.fst"
done

# F*'s unbounded integers extract to zarith, which would drag a large numeric
# library into the JavaScript bundle. Nothing in the runtime should need them.
if grep -q 'Prims\.int' "$BUILD"/ml/*.ml; then
  echo "ERROR: extracted OCaml references Prims.int (zarith)." >&2
  echo "       Mark the nat/int-using definitions noextract, give them a ghost" >&2
  echo "       effect, or switch to machine integers." >&2
  grep -n 'Prims\.int' "$BUILD"/ml/*.ml >&2
  exit 1
fi

# --- 3. Compile to bytecode ------------------------------------------------
log "[3/4] Compiling OCaml"
cp "$ML_DIR"/shim/*.ml "$ML_DIR"/hoop_ffi.ml "$BUILD/ml/"

ML_FILES=(Prims.ml FStar_Pervasives_Native.ml FStar_List_Tot_Base.ml)
for m in "${EXTRACT_MODULES[@]}"; do
  ML_FILES+=("${m//./_}.ml")
done
ML_FILES+=(hoop_ffi.ml)

# The js_of_ocaml OCaml library is deliberately not linked: it pulls in
# Printf/Format and inflates the bundle roughly fourfold. hoop_ffi.ml declares
# the handful of primitives it needs directly, and those live in the jsoo
# runtime rather than the OCaml bytecode runtime, hence -no-check-prims.
# Warnings are silenced because extracted code produces a great many of them.
(
  cd "$BUILD/ml"
  ocamlc -no-check-prims -w -a "${ML_FILES[@]}" -o hoop.byte
)

# --- 4. Bundle to JavaScript -----------------------------------------------
log "[4/4] Bundling with js_of_ocaml"
# --target-env=browser: the default (isomorphic) bundles Node's filesystem
# layer, which calls require() at startup and so cannot be loaded as an ES
# module. This runtime never touches the filesystem, so dropping it is safe --
# the result still runs under both Node and the browser.
js_of_ocaml --target-env=browser --wrap-with-fun="$INIT_FN" \
  "$BUILD/ml/hoop.byte" -o "$BUILD/hoop.raw.js"

mkdir -p "$(dirname "$OUT")"
{
  cat <<EOF
// ---------------------------------------------------------------------------
// Generated file -- do not edit.
//
//   runtime/$( IFS=,; echo "${EXTRACT_MODULES[*]}" ).fst
//     -> F* verification -> OCaml extraction -> js_of_ocaml
//
// Regenerate with: hoop-build-runtime  (or ./scripts/build-runtime.sh)
// The handwritten boundary code lives in runtime/ml/hoop_ffi.ml.
// ---------------------------------------------------------------------------

EOF
  cat "$BUILD/hoop.raw.js"
  cat <<EOF

// Wrapped with --wrap-with-fun, the generated function takes the global object
// as its argument and returns the exports object that Js.export wrote into
// (jsoo_exports). Handing it an object whose prototype is the real global lets
// builtins such as Math resolve through, without polluting the real global.
const __hoop = ${INIT_FN}(Object.create(globalThis));
EOF
  echo
  for e in "${EXPORTS[@]}"; do
    echo "export const $e = __hoop.$e;"
  done
} > "$OUT"

log "Done: $(wc -c < "$OUT" | tr -d ' ') bytes"
