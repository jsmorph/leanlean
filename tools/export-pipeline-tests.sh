#!/usr/bin/env bash
set -euo pipefail

lean4export_bin="${LEANLEAN_LEAN4EXPORT:-lean4export}"
artifact_dir="${LEANLEAN_EXPORT_TEST_DIR:-.lake/build/export-tests}"

if ! command -v "$lean4export_bin" >/dev/null 2>&1; then
  echo "error: lean4export not found; set LEANLEAN_LEAN4EXPORT" >&2
  exit 2
fi

mkdir -p "$artifact_dir"

lake build Faithfulness.ExportSmoke Faithfulness.Accepted Faithfulness.ExportArithmetic leanlean-check-export

checker=".lake/build/bin/leanlean-check-export"
lean_path="$(pwd)/.lake/build/lib/lean"

run_case() {
  local label="$1"
  local module="$2"
  local root="$3"
  local artifact="$artifact_dir/$label.ndjson"

  echo "export: $label"
  LEAN_PATH="$lean_path" "$lean4export_bin" "$module" -- "$root" > "$artifact"
  "$checker" "$artifact"
}

run_case "box-unbox" "Faithfulness.ExportSmoke" "LeanLeanFaithfulness.ExportSmoke.unbox"
run_case "true-theorem" "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.trueTheorem"
run_case "opaque-definition" "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.opaqueTrue"
run_case "nat-literal" "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.literalNat"
run_case "quotient-value" "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.q"
run_case "subtype-value" "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.subtypeTrue"
run_case "recursive-list-length" "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.listLength"
run_case "gcd-parity-arithmetic" "Faithfulness.ExportArithmetic" "LeanLeanFaithfulness.ExportArithmetic.gcd_sum_diff_eq_one"

echo "arena-input: box-unbox"
IN="$artifact_dir/box-unbox.ndjson" "$checker"
