#!/usr/bin/env bash
set -euo pipefail

lean4export_bin="${MPC_LEAN4EXPORT:-lean4export}"
artifact_dir="${MPC_EXPORT_TEST_DIR:-.lake/build/export-tests}"
artifact="$artifact_dir/mpc-gcd-parity-arithmetic.ndjson"

if ! command -v "$lean4export_bin" >/dev/null 2>&1; then
  echo "error: lean4export not found; set MPC_LEAN4EXPORT" >&2
  exit 2
fi

mkdir -p "$artifact_dir"

lake build MPCFixtures.ExportArithmetic mpc-check-export

lean_path="$(pwd)/.lake/build/lib/lean"
LEAN_PATH="$lean_path" "$lean4export_bin" \
  MPCFixtures.ExportArithmetic \
  -- \
  MPCFixtures.ExportArithmetic.gcd_sum_diff_eq_one \
  > "$artifact"

.lake/build/bin/mpc-check-export "$artifact"
