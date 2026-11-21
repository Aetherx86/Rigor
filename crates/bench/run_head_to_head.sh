#!/usr/bin/env bash
# Automated head-to-head benchmark harness comparing Rigor against Lean 4's lean4checker
# on identical lean4export artifacts, capturing wall-clock time and OS-level Peak RSS.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
export PATH="/opt/homebrew/opt/rustup/bin:/opt/homebrew/bin:$HOME/.elan/bin:$PATH"

RIGOR_BIN="$ROOT_DIR/target/release/rigor-bench"
OUT_DIR="${1:-/tmp/rigor_bench_artifacts}"
mkdir -p "$OUT_DIR"

echo "Building release binary..."
(cd "$ROOT_DIR" && cargo build --release -p rigor-bench --quiet)

# Choose OS-appropriate /usr/bin/time flag for Peak RSS
if [[ "$(uname -s)" == "Darwin" ]]; then
  TIME_CMD=("/usr/bin/time" "-l")
  extract_rss_mb() {
    awk '/maximum resident set size/ { printf "%.2f", $1 / (1024 * 1024) }' "$1"
  }
else
  TIME_CMD=("/usr/bin/time" "-v")
  extract_rss_mb() {
    awk '/Maximum resident set size/ { printf "%.2f", $NF / 1024 }' "$1"
  }
fi

ARTIFACTS=()
if [[ "$#" -ge 2 ]]; then
  # User supplied explicit .export files (e.g., Init.export Std.export Mathlib.export)
  shift
  for f in "$@"; do
    ARTIFACTS+=("$f")
  done
else
  # Generate standardized Init / Std / Mathlib-subset scale artifacts
  "$RIGOR_BIN" --generate-export "$OUT_DIR/init_scale_5k.export" 5000 >/dev/null
  "$RIGOR_BIN" --generate-export "$OUT_DIR/std_scale_25k.export" 25000 >/dev/null
  "$RIGOR_BIN" --generate-export "$OUT_DIR/mathlib_subset_100k.export" 100000 >/dev/null
  ARTIFACTS=(
    "$OUT_DIR/init_scale_5k.export"
    "$OUT_DIR/std_scale_25k.export"
    "$OUT_DIR/mathlib_subset_100k.export"
  )
fi

HAVE_L4C=0
if command -v lean4checker >/dev/null 2>&1; then
  HAVE_L4C=1
fi

echo
echo "=== Head-to-Head Benchmark Results ==="
printf "%-30s | %-10s | %-11s | %-12s | %-10s\n" "Artifact" "Checker" "Wall (ms)" "Decls/sec" "Peak RSS"
printf "%-30s-+-%-10s-+-%-11s-+-%-12s-+-%-10s\n" "------------------------------" "----------" "-----------" "------------" "----------"

for art in "${ARTIFACTS[@]}"; do
  base="$(basename "$art")"
  errlog="$OUT_DIR/${base}.rigor.time"
  outlog="$OUT_DIR/${base}.rigor.out"
  "${TIME_CMD[@]}" "$RIGOR_BIN" --check "$art" >"$outlog" 2>"$errlog"
  wall_ms="$(sed -n 's/.*time_ms=\([0-9.]*\).*/\1/p' "$outlog")"
  dps="$(sed -n 's/.*decls_per_sec=\([0-9]*\).*/\1/p' "$outlog")"
  rss_mb="$(extract_rss_mb "$errlog")"
  printf "%-30s | %-10s | %8s ms | %12s | %7s MB\n" "$base" "rigor" "$wall_ms" "$dps" "$rss_mb"

  if [[ "$HAVE_L4C" -eq 1 ]]; then
    lerr="$OUT_DIR/${base}.l4c.time"
    t0="$(python3 -c 'import time; print(time.perf_counter())')"
    "${TIME_CMD[@]}" lean4checker "$art" >/dev/null 2>"$lerr" || true
    t1="$(python3 -c 'import time; print(time.perf_counter())')"
    lwall="$(python3 -c "print(f'{($t1 - $t0)*1000:.2f}')")"
    lrss="$(extract_rss_mb "$lerr")"
    printf "%-30s | %-10s | %8s ms | %12s | %7s MB\n" "$base" "lean4chk" "$lwall" "-" "$lrss"
  fi
done

if [[ "$HAVE_L4C" -eq 0 ]]; then
  echo
  echo "Note: lean4checker not found on PATH; skipped lean4checker column."
  echo "Install Lean 4 + lean4checker and re-run with real .export files:"
  echo "  ./crates/bench/run_head_to_head.sh /tmp/out Init.export Std.export Mathlib.export"
fi
