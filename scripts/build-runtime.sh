#!/usr/bin/env bash
#
# runtime/*.fst --[F* verification]--> OCaml --[js_of_ocaml]--> src/Hoop/Engine.js
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
# automatically when present. Reading the list top to bottom:
#
#   Handlers        the handler table, behind an interface
#   Syntax          the AST -- `comp_tree` and `frame`
#   Semantics       the reference machine, stack search and all
#   WellScopedness  the judgement that rules `Stuck` out
#   Metatheory      preservation and progress, proved of `Semantics`
#   Env             the evidence environment, behind an interface
#   Env.Stack       the environment a stack offers, and that the two agree.
#                   UNREFERENCED as of the tail-resumptive merge: it locates a
#                   prompt by the height it was installed at, and the machine's
#                   `MEnvF` frame makes a height into the reference stack
#                   unavailable. Kept verified pending a decision on its fate;
#                   nothing below depends on it.
#   Hoop.Runtime    THE MACHINE, and the only module the FFI touches:
#                   `Semantics` with the stack search replaced by an evidence
#                   lookup and with tail-resumptive (`fast`) clauses, linked to
#                   `Semantics` by a weak simulation through `erase_st`.
#   Test, Laws      leaves -- `assert_norm` fixtures and the monad laws
VERIFY_MODULES=(Hoop.Runtime.Handlers Hoop.Runtime.Syntax Hoop.Runtime.Semantics Hoop.Runtime.WellScopedness Hoop.Runtime.Metatheory Hoop.Runtime.Env Hoop.Runtime.Env.Stack Hoop.Runtime Hoop.Runtime.Test Hoop.Runtime.Laws)

# Modules to extract to OCaml, in dependency order -- this is also the order
# ocamlc links them in below. The four omitted are proof-only: `WellScopedness`,
# `Metatheory` and `Laws` are `prop` and `Lemma` throughout and extract to
# nothing, and `Test` is fixtures.
#
# `--extract` reads a module name as a namespace prefix as well, so asking for
# `Hoop.Runtime` offers up the whole `Hoop.Runtime.*` namespace. Every module in
# it now has an interface, and a module whose implementation is behind one is
# not offered, so nothing omitted here reaches build/ml. Give one of them an
# implementation-only module again and its .ml will reappear.
EXTRACT_MODULES=(Hoop.Runtime.Handlers Hoop.Runtime.Syntax Hoop.Runtime.Semantics Hoop.Runtime.Env Hoop.Runtime.Env.Stack Hoop.Runtime)

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

# F*'s own Prims realises integers with zarith, which would drag a large numeric
# library into the JavaScript bundle. runtime/ml/shim/Prims.ml replaces it with
# checked native ints instead; the three guards below are what make that
# substitution safe to rely on. See the header of that file for the argument.
#
# (a) The runtime counts stack frames, so `Prims.nat` is expected in the
#     extracted output. A signed `Prims.int` is not: the overflow check in the
#     shim tests for a negative result, which is only a sound test when no
#     genuinely negative value can arise. Mark such a definition `noextract` or
#     give it a ghost effect.
if grep -qE 'Prims\.int([^_A-Za-z0-9]|$)' "$BUILD"/ml/*.ml; then
  echo "ERROR: extracted OCaml references the signed Prims.int." >&2
  echo "       The shim's overflow check assumes every extracted integer is a" >&2
  echo "       nat. Mark the definition noextract or give it a ghost effect." >&2
  grep -nE 'Prims\.int([^_A-Za-z0-9]|$)' "$BUILD"/ml/*.ml >&2
  exit 1
fi

# (b) The handwritten shim and glue must not reach for a bignum library either,
#     and Prims.ml must still be the native-int realisation. Comments are
#     stripped first: Prims.ml's header discusses zarith at length, and a guard
#     that fires on its own documentation is one people route around.
strip_ocaml_comments() {
  awk '
    BEGIN { d = 0 }
    {
      out = ""
      for (i = 1; i <= length($0); i++) {
        two = substr($0, i, 2)
        if (two == "(*")      { d++;   i++; continue }
        if (d > 0 && two == "*)") { d--; i++; continue }
        if (d == 0) out = out substr($0, i, 1)
      }
      print out
    }' "$1"
}

for f in "$ML_DIR"/shim/*.ml "$ML_DIR"/hoop_ffi.ml; do
  if strip_ocaml_comments "$f" | grep -nE '\bZ\.|zarith|Stdint'; then
    echo "ERROR: $f references a bignum library." >&2
    exit 1
  fi
done
if ! grep -q 'type int = Stdlib\.Int\.t' "$ML_DIR/shim/Prims.ml"; then
  echo "ERROR: runtime/ml/shim/Prims.ml no longer realises Prims.int natively." >&2
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
$( for m in "${EXTRACT_MODULES[@]}"; do echo "//   runtime/$m.fst"; done )
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

# (c) The last word belongs to the bundle itself. Guards (a) and (b) read
#     sources; this one reads what actually ships, and so also catches a bignum
#     arriving through a route neither of them models. The size budget is the
#     same check by another route: linking zarith or Printf/Format multiplies
#     the output several times over, so a bundle that stays small has not.
if grep -qE 'ml_z_|caml_z_|BigInt|Stdint' "$OUT"; then
  echo "ERROR: the generated bundle contains bignum support code." >&2
  grep -noE 'ml_z_[a-z_]*|caml_z_[a-z_]*|BigInt|Stdint' "$OUT" | head >&2
  exit 1
fi

SIZE="$(wc -c < "$OUT" | tr -d ' ')"
BUDGET=60000
if [ "$SIZE" -gt "$BUDGET" ]; then
  echo "ERROR: bundle is $SIZE bytes, over the $BUDGET-byte budget." >&2
  echo "       Something heavy got linked in -- check for a new library" >&2
  echo "       dependency in hoop_ffi.ml or a shim that grew." >&2
  exit 1
fi

log "Done: $SIZE bytes (budget $BUDGET)"
