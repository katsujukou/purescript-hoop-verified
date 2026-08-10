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
#   Hoop.Runtime    THE MACHINE, and the only module the FFI touches:
#                   `Semantics` with the stack search replaced by an evidence
#                   lookup and with tail-resumptive (`fast`) clauses, linked to
#                   `Semantics` by a weak simulation through `erase_st`.
#   Test, Laws      leaves -- `assert_norm` fixtures and the monad laws
VERIFY_MODULES=(Hoop.Runtime.Handlers Hoop.Runtime.Syntax Hoop.Runtime.Semantics Hoop.Runtime.WellScopedness Hoop.Runtime.Metatheory Hoop.Runtime.Env Hoop.Runtime Hoop.Runtime.Test Hoop.Runtime.Laws)

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
EXTRACT_MODULES=(Hoop.Runtime.Handlers Hoop.Runtime.Syntax Hoop.Runtime.Semantics Hoop.Runtime.Env Hoop.Runtime)

# Names the generated JS exposes. Must match the `export` calls in hoop_ffi.ml.
# All of them are uncurried multi-argument functions -- the PureScript side
# imports them through Fn2 / Fn3.
EXPORTS=(pureImpl bindImpl performImpl withImpl runImpl
         newCellImpl readCellImpl writeCellImpl
         mkFullClauseImpl mkFastClauseImpl mkReturnImpl undefinedReturnImpl
         emptyClausesImpl emptyHandlersImpl insertClauseImpl insertClausesImpl)

# Name of the function js_of_ocaml wraps the generated code in. Engine.js calls it.
INIT_FN=hoopInit

# Which OCaml-to-JavaScript backend produces src/Hoop/Engine.js.
#
#   melange  (default)  runtime/ml/melange/hoop_ffi.ml, via dune and esbuild
#   jsoo                runtime/ml/hoop_ffi.ml, via ocamlc and js_of_ocaml
#
# Melange is the default because it is measurably better on every axis that was
# compared: ~39% off a State-heavy loop, ~19% off handler installation, and 60%
# off the gzipped bundle -- 9.8 KB to 3.9 KB, which every downstream bundle
# pays. The reason is not codegen cleverness but the boundary: a Melange
# `string` IS a JS string and a Melange `array` IS a JS array, so the four
# conversions jsoo performs on every `perform` and every `with` become
# identities. That is the boundary this runtime crosses more than any other.
#
# The jsoo path is kept, and kept working, for two reasons: it is the fallback
# if Melange ever stalls, and having two independent backends agree on
# `engine-smoke.mjs` is evidence about the boundary code that neither alone
# gives. It shares steps 1 and 2 with the Melange path, so the two always
# compile the same extracted machine.
BACKEND=${BACKEND:-melange}

# src/Hoop/Engine.js is committed, so it is minified by default: it is a
# generated artifact that every downstream bundle carries, and the readable
# form is three times the size for a file nobody edits.
#
#   --no-minify   emit it readable instead, for when something has to be
#                 investigated in the shipped runtime -- a stack trace, a
#                 profile, a suspicion about what a transition compiles to.
#                 Rebuild without the flag before committing; the header of
#                 the generated file records which form it is, so a readable
#                 build shows up in `git diff` as more than noise.
#
# Minification is the LAST step and the guards below never read its output:
# esbuild renames, and a guard that greps for a name the minifier has changed
# passes silently forever. They read build/hoop.raw.js, which is the same
# program.
MINIFY=1
for arg in "$@"; do
  case "$arg" in
    --no-minify) MINIFY=0 ;;
    -h|--help)
      echo "usage: $0 [--no-minify]   (BACKEND=melange|jsoo, default melange)"
      exit 0 ;;
    *) echo "ERROR: unknown option '$arg' (want: --no-minify)" >&2; exit 1 ;;
  esac
done

case "$BACKEND" in
  melange) BACKEND_TOOLS=(melc dune esbuild) ;;
  jsoo)    BACKEND_TOOLS=(ocamlc js_of_ocaml) ;;
  *) echo "ERROR: unknown BACKEND '$BACKEND' (want: melange | jsoo)" >&2; exit 1 ;;
esac

log() { printf '\033[1;34m==>\033[0m %s\n' "$*"; }

# Write $OUT from $BODY, minifying unless --no-minify, with a header naming the
# sources and the pipeline ($PIPELINE) that produced it. The header is prepended
# *after* minification, since esbuild would otherwise strip it -- and it is the
# only thing telling a reader of the committed file where it came from.
emit_engine() {
  local body="$BODY" note1 note2
  if [ "$MINIFY" = 1 ]; then
    esbuild --minify --format=esm "$BODY" --outfile="$BUILD/hoop.min.js" >/dev/null
    body="$BUILD/hoop.min.js"
    note1="// This build is minified, which is the committed form. Pass --no-minify"
    note2="// for a readable one when something here has to be investigated."
  else
    note1="// This build is READABLE, which is NOT the committed form -- it was built"
    note2="// with --no-minify. Rebuild without that flag before committing."
  fi
  mkdir -p "$(dirname "$OUT")"
  {
    echo "// ---------------------------------------------------------------------------"
    echo "// Generated file -- do not edit."
    echo "//"
    for m in "${EXTRACT_MODULES[@]}"; do echo "//   runtime/$m.fst"; done
    echo "//     -> $PIPELINE"
    echo "//"
    echo "// Regenerate with: hoop-build-runtime  (or ./scripts/build-runtime.sh)"
    echo "$note1"
    echo "$note2"
    echo "//"
    echo "// The handwritten boundary code -- the part no F* proof covers -- lives in"
    echo "//   $FFI_NOTE"
    echo "// ---------------------------------------------------------------------------"
    echo
    cat "$body"
  } > "$OUT"
}

# Report which binaries are actually being used. A stray fstar.exe or
# js_of_ocaml earlier on PATH otherwise causes confusing failures.
log "Tools (backend: $BACKEND)"
for t in fstar.exe "${BACKEND_TOOLS[@]}"; do
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
# checked native ints instead; guards (a), (b) and (d) below are what make that
# substitution safe to rely on. See the header of that file for the argument.
# Guard (c) is unrelated to Prims and stands on its own.
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

for f in "$ML_DIR"/shim/*.ml "$ML_DIR"/hoop_ffi.ml "$ML_DIR"/melange/hoop_ffi.ml; do
  if strip_ocaml_comments "$f" | grep -nE '\bZ\.|zarith|Stdint'; then
    echo "ERROR: $f references a bignum library." >&2
    exit 1
  fi
done
if ! grep -q 'type int = Stdlib\.Int\.t' "$ML_DIR/shim/Prims.ml"; then
  echo "ERROR: runtime/ml/shim/Prims.ml no longer realises Prims.int natively." >&2
  exit 1
fi

if [ "$BACKEND" = melange ]; then

# --- 3m. Compile with Melange ----------------------------------------------
# The repository does not become a dune project: the tree below is generated
# into build/, used once, and removed by the `rm -rf "$BUILD"` at the top of the
# next run. dune is an implementation detail of this step, the way ocamlc is of
# the jsoo one.
log "[3/4] Compiling with Melange"
MEL_FFI="$ML_DIR/melange"
WORK="$BUILD/melange"
mkdir -p "$WORK/src"

cat > "$WORK/dune-project" <<'EOF'
(lang dune 3.20)
(using melange 0.1)
EOF

# `-w -a` for the same reason the jsoo build passes it to ocamlc: extracted code
# produces a great many warnings and none of them is actionable here.
cat > "$WORK/src/dune" <<'EOF'
(melange.emit
 (target js)
 (alias default)
 (libraries melange.js)
 (preprocess (pps melange.ppx))
 (compile_flags (:standard -w -a))
 (module_systems es6))
EOF

cp "$BUILD"/ml/*.ml "$WORK/src/"
cp "$ML_DIR"/shim/*.ml "$WORK/src/"
cp "$MEL_FFI/hoop_ffi.ml" "$MEL_FFI/hoop_prim.js" "$WORK/src/"

(cd "$WORK" && dune build @default)

EMIT="$WORK/_build/default/src/js/src"
# The emitted modules import hoop_prim.js by relative path, so it has to sit
# beside them for esbuild to resolve it.
cp "$MEL_FFI/hoop_prim.js" "$EMIT/"

# --- 4m. Bundle to JavaScript ----------------------------------------------
log "[4/4] Bundling with esbuild"
# Melange exports every top-level value of a module, including internal helpers,
# and PureScript rejects an FFI module exporting an identifier it cannot spell
# -- Melange renames `throw` to `$$throw`, for one. This entry module narrows
# the surface to exactly the names PureScript binds, which is also what makes
# esbuild's tree shaking effective.
{
  echo "// Generated by scripts/build-runtime.sh -- do not edit."
  echo "export {"
  for e in "${EXPORTS[@]}"; do echo "  $e,"; done
  echo "} from './hoop_ffi.js'"
} > "$EMIT/entry.js"

esbuild --bundle --format=esm --platform=neutral \
  "$EMIT/entry.js" --outfile="$BUILD/hoop.raw.js" >/dev/null

# (c) No *generic* comparison left reachable -- the Melange reading of the guard
#     below. Melange specialises `=` at a known `string` to `===`, exactly as
#     the OCaml compiler does for jsoo; what it cannot specialise it routes
#     through `Caml_obj.caml_equal`, a structural walk. The machine compares
#     nothing but labels, so every comparison it makes should be the
#     specialised one.
#
#     Reachability, not presence, is the property, and here it is esbuild's tree
#     shaking that decides it -- so the bundle is the thing to read. esbuild
#     drops the module qualifier when it inlines, so the pattern matches the
#     bare function names rather than `Caml_obj.caml_equal`.
#
#     This was checked to FIRE, not merely to pass: a `poisonImpl` doing a
#     polymorphic comparison was added to the boundary, and `caml_equal` and
#     `caml_obj` appeared in the bundle. Neither is present otherwise, though
#     several other `caml_*` names are, which is why the pattern is specific.
if grep -qE '\bcaml_(equal|notequal|compare|obj)\b' "$BUILD/hoop.raw.js"; then
  echo "ERROR: the runtime performs a generic structural comparison." >&2
  echo "       Extracted code must compare only at types Melange can" >&2
  echo "       specialise -- see the note on mem_string in" >&2
  echo "       runtime/Hoop.Runtime.Handlers.fst." >&2
  grep -nE '\bcaml_(equal|notequal|compare|obj)\b' "$BUILD/hoop.raw.js" >&2
  exit 1
fi

BODY="$BUILD/hoop.raw.js"
PIPELINE="F* verification -> OCaml extraction -> Melange -> esbuild"
FFI_NOTE="runtime/ml/melange/hoop_ffi.ml and runtime/ml/melange/hoop_prim.js"
emit_engine

else

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

# (c) No *generic* comparison left reachable. `=` at a type the OCaml compiler
#     cannot see through becomes `caml_equal`, which goes through
#     `caml_compare_val` and tests each operand with `caml_is_ml_string` -- a
#     regular-expression match, per operand, per element scanned. At a known
#     `string` the compiler picks `caml_string_equal`, which js_of_ocaml turns
#     into `===`. The machine compares nothing but labels, so every comparison
#     it makes should be the specialised one.
#
#     Reachability, not presence, is the property, and js_of_ocaml's dead-code
#     elimination is what decides it: the shim still defines a polymorphic
#     `mem` that nothing calls, and a `mem` nobody calls costs nothing. So the
#     bundle is the thing to read. It is re-emitted with --pretty because the
#     shipped one has its runtime functions renamed; --pretty changes naming
#     and inlining only, not what survives elimination.
#
#     This catches a generic comparison whatever route it arrives by: a
#     comparison drifting to a type extraction leaves abstract, or a
#     polymorphic list operation coming back onto the hot path. The latter is
#     how it was reached before, and is why `Hoop.Runtime.Handlers` defines
#     `mem_string` and `Hoop.Runtime.Env.find_level` is `noextract` -- note
#     that reading the extracted .ml would *not* have caught that one, since
#     the comparison itself was inside the shim.
js_of_ocaml --target-env=browser --wrap-with-fun="$INIT_FN" --pretty \
  "$BUILD/ml/hoop.byte" -o "$BUILD/hoop.pretty.js"
if grep -qE 'caml_(equal|notequal|compare_val)\b' "$BUILD/hoop.pretty.js"; then
  echo "ERROR: the runtime performs a generic structural comparison." >&2
  echo "       Extracted code must compare only at types OCaml can" >&2
  echo "       specialise -- see the note on mem_string in" >&2
  echo "       runtime/Hoop.Runtime.Handlers.fst." >&2
  grep -nE 'caml_(equal|notequal|compare_val)\b' "$BUILD/hoop.pretty.js" >&2
  exit 1
fi

# The jsoo bundle is not a module on its own: it has to be given a global and
# unwrapped. Assembled here as readable JS so that the guards below -- and
# `--no-minify` -- see the same program that ships.
{
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
} > "$BUILD/hoop.engine.js"

BODY="$BUILD/hoop.engine.js"
PIPELINE="F* verification -> OCaml extraction -> js_of_ocaml"
FFI_NOTE="runtime/ml/hoop_ffi.ml"
emit_engine

fi  # BACKEND

# (d) The last word belongs to the bundle itself. Guards (a) and (b) read
#     sources; this one reads what actually ships, and so also catches a bignum
#     arriving through a route neither of them models. The size budget is the
#     same check by another route: linking zarith or Printf/Format multiplies
#     the output several times over, so a bundle that stays small has not.
#     Read against $BODY, not $OUT: those are the same program, but $OUT may
#     have been through the minifier, which renames -- and three of the four
#     names below are renameable. Grepping the shipped file would look stricter
#     and be weaker.
if grep -qE 'ml_z_|caml_z_|BigInt|Stdint' "$BODY"; then
  echo "ERROR: the generated bundle contains bignum support code." >&2
  grep -noE 'ml_z_[a-z_]*|caml_z_[a-z_]*|BigInt|Stdint' "$BODY" | head >&2
  exit 1
fi

#     The size budget is calibrated against the readable build for the same
#     reason: it is a check on what got *linked in*, and minification would
#     move the number for reasons that have nothing to do with that. The
#     shipped size is reported rather than checked.
SIZE="$(wc -c < "$BODY" | tr -d ' ')"
BUDGET=60000
if [ "$SIZE" -gt "$BUDGET" ]; then
  echo "ERROR: bundle is $SIZE bytes, over the $BUDGET-byte budget." >&2
  echo "       Something heavy got linked in -- check for a new library" >&2
  echo "       dependency in hoop_ffi.ml or a shim that grew." >&2
  exit 1
fi

SHIPPED="$(wc -c < "$OUT" | tr -d ' ')"
log "Done: $SHIPPED bytes shipped ($SIZE readable, budget $BUDGET)"
