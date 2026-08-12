#!/usr/bin/env bash
#
# Compile-fail regression tests.
#
# Some of what this library guarantees is that certain programs DO NOT compile:
# an ordinary `handler` must refuse a scoped clause, a monomorphic table must
# not pose at a family, and the two markers must not be swapped. A fixture
# asserting that cannot live in `test/`, which has to build.
#
# Each fixture in test-compile-fail/ is a module named `CompileFail`, carrying
# one or more `-- EXPECT: <substring>` lines. It is copied into the test glob,
# built alone, and required to FAIL with every expected substring present.
#
# Two failure modes this guards against, both of which have bitten:
#
#   * A fixture that fails for the wrong reason -- a typo, a missing import --
#     looks exactly like a fixture that fails for the right one. Hence EXPECT.
#   * The PureScript compiler reports ONE error per module. Two fixtures in one
#     module would mask each other and the masked one would appear to pass.
#     Hence one module per fixture, built one at a time.
set -euo pipefail

cd "$(dirname "$0")/.."

FIXTURES=(test-compile-fail/*.purs)
TMP=test/CompileFail.purs

cleanup() { rm -f "$TMP"; }
trap cleanup EXIT

if [ -e "$TMP" ]; then
  echo "error: $TMP already exists; refusing to overwrite" >&2
  exit 1
fi

fail=0
for f in "${FIXTURES[@]}"; do
  name="$(basename "$f" .purs)"

  expects=()
  while IFS= read -r line; do expects+=("$line"); done < <(sed -n 's/^-- EXPECT: //p' "$f")
  if [ "${#expects[@]}" -eq 0 ]; then
    echo "FAIL $name: fixture declares no '-- EXPECT:' line" >&2
    fail=1
    continue
  fi

  cp "$f" "$TMP"
  out="$(spago build 2>&1)" && status=0 || status=$?
  rm -f "$TMP"

  if [ "$status" -eq 0 ]; then
    echo "FAIL $name: expected a compile error, but the build succeeded" >&2
    fail=1
    continue
  fi

  missing=0
  for e in "${expects[@]}"; do
    if ! grep -qF -- "$e" <<<"$out"; then
      echo "FAIL $name: compile error did not mention: $e" >&2
      missing=1
    fi
  done

  if [ "$missing" -ne 0 ]; then
    echo "--- actual output ---" >&2
    sed -n '/^\[ERROR/,/^$/p' <<<"$out" | head -30 >&2
    echo "---------------------" >&2
    fail=1
  else
    echo "ok   $name"
  fi
done

# The fixtures are only meaningful if the tree builds without them.
if ! spago build >/dev/null 2>&1; then
  echo "FAIL: the tree does not build with the fixtures removed" >&2
  fail=1
fi

exit "$fail"
