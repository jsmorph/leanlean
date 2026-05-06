#!/usr/bin/env bash
set -euo pipefail

lean4export_bin="${MPC_LEAN4EXPORT:-lean4export}"
artifact_dir="${MPC_EXPORT_TEST_DIR:-.lake/build/export-tests}"

if ! command -v "$lean4export_bin" >/dev/null 2>&1; then
  echo "error: lean4export not found; set MPC_LEAN4EXPORT" >&2
  exit 2
fi

mkdir -p "$artifact_dir"

lake build MPCFixtures.ExportArithmetic MPCFixtures.ExportNestedIndexed MPCFixtures.ExportMutual mpc-check-export

checker=".lake/build/bin/mpc-check-export"
lean_path="$(pwd)/.lake/build/lib/lean"

run_generated() {
  local label="$1"
  local module="$2"
  local root="$3"
  local expected_fragment="$4"
  local artifact="$artifact_dir/$label.ndjson"
  local output
  local code

  echo "export: $label"
  LEAN_PATH="$lean_path" "$lean4export_bin" "$module" -- "$root" > "$artifact"

  echo "check: $label"
  set +e
  output="$("$checker" "$artifact" 2>&1)"
  code="$?"
  set -e

  printf '%s\n' "$output"
  if [[ "$code" != "0" ]]; then
    echo "error: $label returned exit code $code; expected 0" >&2
    exit 1
  fi
  local first_line="${output%%$'\n'*}"
  if [[ "$first_line" != "accepted" ]]; then
    echo "error: $label returned status $first_line; expected accepted" >&2
    exit 1
  fi
  if [[ "$output" != *"$expected_fragment"* ]]; then
    echo "error: $label output did not contain expected fragment: $expected_fragment" >&2
    exit 1
  fi
}

run_generated \
  "mpc-gcd-parity-arithmetic" \
  "MPCFixtures.ExportArithmetic" \
  "MPCFixtures.ExportArithmetic.gcd_sum_diff_eq_one" \
  "checked 493 declaration entries; environment size 571"

run_generated \
  "mpc-nested-indexed-param" \
  "MPCFixtures.ExportNestedIndexed" \
  "MPCFixtures.ExportNestedIndexed.paramValue" \
  "checked 7 declaration entries; environment size 18"

run_generated \
  "mpc-nested-indexed-local" \
  "MPCFixtures.ExportNestedIndexed" \
  "MPCFixtures.ExportNestedIndexed.NestedIndexedParamLocal" \
  "checked 6 declaration entries; environment size 17"

run_generated \
  "mpc-nested-pairbox" \
  "MPCFixtures.ExportNestedIndexed" \
  "MPCFixtures.ExportNestedIndexed.NestedPairBox" \
  "checked 2 declaration entries; environment size 7"

run_generated \
  "mpc-nested-indexed-pairbox" \
  "MPCFixtures.ExportNestedIndexed" \
  "MPCFixtures.ExportNestedIndexed.NestedIndexedPairBox" \
  "checked 6 declaration entries; environment size 16"

run_generated \
  "mpc-mutual-even-odd" \
  "MPCFixtures.ExportMutual" \
  "MPCFixtures.ExportMutual.squashedEvenTwo" \
  "checked 5 declaration entries; environment size 11"
