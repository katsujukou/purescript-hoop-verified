#!/usr/bin/env bash
# Run every benchmark over a size sweep and plot the results with gnuplot.
#
#   ./bench.sh                 build, run, plot (defaults below)
#   SIZES="1000 10000" REPS=5 ./bench.sh
#   OPT=1 ./bench.sh           run the purs-backend-es output instead
#
# Timing is whole-process (node startup included) via time-run.pl, min of
# REPS runs per point. Outputs: out/bench-<name>.csv, out/bench.png,
# out/bench-summary.txt. Everything this script writes is prefixed with
# "bench" so it never clobbers other artifacts in out/.
set -euo pipefail
cd "$(dirname "$0")"

SIZES=${SIZES:-"1000 3000 10000 30000 100000 300000 1000000"}
REPS=${REPS:-3}
OPT=${OPT:-0}
# state (default) or catch. `catch` measures the price of virtualization:
# the same program with catch as a scoped operation vs as a handler
# installation, plus purescript-run for scale.
SUITE=${SUITE:-state}

# name (series label in the plot) -> module -> plot label
BENCHES_state=(
  "hoop-state-var:Benchmarks.CountStateVar:hoop (State via var-cell)"
  "hoop-state-full:Benchmarks.CountStateFull:hoop (State with full-handler)"
  "mtl-state:Benchmarks.CountMtlState:transformers State (tailRecM)"
  "run-state:Benchmarks.CountRun:purescript-run State"
  "effect-ref:Benchmarks.CountEffectRef:Effect + Ref"
  "st-ref:Benchmarks.CountSTRef:ST + STRef"
)

# BENCHES_catch=(
#   "catch-scoped:Benchmarks.CatchScoped:hoop scoped catch (no throw)"
#   "catch-install:Benchmarks.CatchInstall:hoop installed catch (no throw)"
#   "catch-install-hoisted:Benchmarks.CatchInstallHoisted:hoop installed catch, table hoisted (no throw)"
#   "catch-run:Benchmarks.CatchRun:purescript-run catch (no throw)"
#   "catch-scoped-throw:Benchmarks.CatchScopedThrow:hoop scoped catch (throw + recover)"
#   "catch-install-throw:Benchmarks.CatchInstallThrow:hoop installed catch (throw + recover)"
#   "catch-run-throw:Benchmarks.CatchRunThrow:purescript-run catch (throw + recover)"
#   "stateexc-scoped:Benchmarks.StateExcScoped:hoop State+Except, scoped catch"
#   "stateexc-install:Benchmarks.StateExcInstall:hoop State+Except, installed catch"
#   "stateexc-run:Benchmarks.RunStateExcept:purescript-run State+Except"
# )

case "$SUITE" in
  state) BENCHES=("${BENCHES_state[@]}"); PLOT=bench ;;
  # catch) BENCHES=("${BENCHES_catch[@]}"); PLOT=bench-catch ;;
  *) echo "unknown SUITE '$SUITE' (want: state | catch)" >&2; exit 1 ;;
esac

echo "== building (spago) =="
spago build -p benchmarks

OUTPUT_DIR="../../output"
if [ "$OPT" = "1" ]; then
  echo "== building (purs-backend-es) =="
  (cd .. && purs-backend-es build)
  OUTPUT_DIR="../../output-es"
fi

mkdir -p out

# One tiny ESM entry per benchmark so `node <entry> <n>` gives sizeArg
# its argument in argv[1] — no bundler needed.
for spec in "${BENCHES[@]}"; do
  name=${spec%%:*}
  rest=${spec#*:}
  module=${rest%%:*}
  cat > "out/bench-$name.mjs" <<EOF
import { main } from "$OUTPUT_DIR/$module/index.js";
main();
EOF
done

echo "== running (sizes: $SIZES; $REPS reps, min taken) =="
for spec in "${BENCHES[@]}"; do
  name=${spec%%:*}
  csv="out/bench-$name.csv"
  : > "$csv"
  for n in $SIZES; do
    best=""
    for _ in $(seq 1 "$REPS"); do
      t=$(perl ./time-run.pl node "out/bench-$name.mjs" "$n") || {
        echo "  $name n=$n: run FAILED, aborting this series" >&2
        break 2
      }
      if [ -z "$best" ] || awk -v a="$t" -v b="$best" 'BEGIN { exit !(a < b) }'; then
        best=$t
      fi
    done
    echo "$n,$best" >> "$csv"
    printf "  %-18s n=%-8s %ss\n" "$name" "$n" "$best"
  done
done

echo "== plotting =="
{
  echo "set terminal pngcairo size 1100,750 enhanced font 'sans,11'"
  echo "set output 'out/$PLOT.png'"
  title="hoop $SUITE benchmarks — wall clock (min of $REPS), node $(node --version)"
  [ "$OPT" = "1" ] && title="$title, purs-backend-es"
  echo "set title '$title'"
  echo "set datafile separator ','"
  echo "set logscale xy"
  echo "set xlabel 'n (iterations)'"
  echo "set ylabel 'seconds'"
  echo "set key left top"
  echo "set grid"
  echo "set format x '10^{%L}'"
  plots=()
  for spec in "${BENCHES[@]}"; do
    name=${spec%%:*}
    label=${spec##*:}
    [ -s "out/bench-$name.csv" ] || continue
    plots+=("'out/bench-$name.csv' using 1:2 with linespoints lw 2 ps 1.2 title '$label'")
  done
  if [ "${#plots[@]}" -gt 0 ]; then IFS=", "; echo "plot ${plots[*]}"; fi
} > "out/$PLOT.gp"
gnuplot "out/$PLOT.gp"

{
  echo "sizes: $SIZES  reps: $REPS  opt: $OPT  node: $(node --version)  date: $(date -u +%Y-%m-%dT%H:%MZ)"
  for spec in "${BENCHES[@]}"; do
    name=${spec%%:*}
    echo "-- $name"
    sed 's/,/  /' "out/bench-$name.csv"
  done
} | tee "out/$PLOT-summary.txt"

echo "== done: out/$PLOT.png =="
