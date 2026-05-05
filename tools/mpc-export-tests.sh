#!/usr/bin/env bash
set -euo pipefail

lean4export_bin="${LEANLEAN_LEAN4EXPORT:-lean4export}"
artifact_dir="${LEANLEAN_EXPORT_TEST_DIR:-.lake/build/export-tests}"

if ! command -v "$lean4export_bin" >/dev/null 2>&1; then
  echo "error: lean4export not found; set LEANLEAN_LEAN4EXPORT" >&2
  exit 2
fi

mkdir -p "$artifact_dir"

lake build Faithfulness.ExportArithmetic Faithfulness.ExportNestedIndexed mpc-check-export

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
  "Faithfulness.ExportArithmetic" \
  "LeanLeanFaithfulness.ExportArithmetic.gcd_sum_diff_eq_one" \
  "checked 493 declaration entries; environment size 571"

run_generated \
  "mpc-nested-indexed-param" \
  "Faithfulness.ExportNestedIndexed" \
  "LeanLeanFaithfulness.ExportNestedIndexed.paramValue" \
  "checked 7 declaration entries; environment size 18"

run_generated \
  "mpc-nested-indexed-local" \
  "Faithfulness.ExportNestedIndexed" \
  "LeanLeanFaithfulness.ExportNestedIndexed.NestedIndexedParamLocal" \
  "checked 6 declaration entries; environment size 17"
