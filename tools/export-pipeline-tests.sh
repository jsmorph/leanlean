#!/usr/bin/env bash
set -euo pipefail

lean4export_bin="${LEANLEAN_LEAN4EXPORT:-lean4export}"
artifact_dir="${LEANLEAN_EXPORT_TEST_DIR:-.lake/build/export-tests}"

if ! command -v "$lean4export_bin" >/dev/null 2>&1; then
  echo "error: lean4export not found; set LEANLEAN_LEAN4EXPORT" >&2
  exit 2
fi

mkdir -p "$artifact_dir"

lake build \
  Faithfulness.ExportSmoke \
  Faithfulness.Accepted \
  Faithfulness.ExportArithmetic \
  Faithfulness.Arena.Bogus1 \
  Faithfulness.Arena.ProjOfProp \
  leanlean-check-export

checker=".lake/build/bin/leanlean-check-export"
lean_path="$(pwd)/.lake/build/lib/lean"

run_checker_expect() {
  local label="$1"
  local artifact="$2"
  local expected_status="$3"
  local expected_code="$4"
  local expected_fragment="${5:-}"
  local output
  local code

  set +e
  output="$("$checker" "$artifact" 2>&1)"
  code="$?"
  set -e

  printf '%s\n' "$output"
  if [[ "$code" != "$expected_code" ]]; then
    echo "error: $label returned exit code $code; expected $expected_code" >&2
    exit 1
  fi
  local first_line="${output%%$'\n'*}"
  if [[ "$first_line" != "$expected_status" ]]; then
    echo "error: $label returned status $first_line; expected $expected_status" >&2
    exit 1
  fi
  if [[ "$expected_fragment" != "" && "$output" != *"$expected_fragment"* ]]; then
    echo "error: $label output did not contain expected fragment: $expected_fragment" >&2
    exit 1
  fi
}

run_generated() {
  local label="$1"
  local expected_status="$2"
  local expected_code="$3"
  local module="$4"
  local root="$5"
  local expected_fragment="${6:-}"
  local artifact="$artifact_dir/$label.ndjson"

  echo "export: $label"
  LEAN_PATH="$lean_path" "$lean4export_bin" "$module" -- "$root" > "$artifact"
  run_checker_expect "$label" "$artifact" "$expected_status" "$expected_code" "$expected_fragment"
}

run_static() {
  local label="$1"
  local expected_status="$2"
  local expected_code="$3"
  local artifact="$4"
  local expected_fragment="${5:-}"

  echo "static: $label"
  run_checker_expect "$label" "$artifact" "$expected_status" "$expected_code" "$expected_fragment"
}

run_generated "box-unbox" "accepted" 0 "Faithfulness.ExportSmoke" "LeanLeanFaithfulness.ExportSmoke.unbox"
run_generated "true-theorem" "accepted" 0 "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.trueTheorem"
run_generated "opaque-definition" "accepted" 0 "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.opaqueTrue"
run_generated "nat-literal" "accepted" 0 "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.literalNat"
run_generated "quotient-value" "accepted" 0 "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.q"
run_generated "subtype-value" "accepted" 0 "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.subtypeTrue"
run_generated "recursive-list-length" "accepted" 0 "Faithfulness.Accepted" "LeanLeanFaithfulness.Accepted.listLength"
run_generated "gcd-parity-arithmetic" "accepted" 0 "Faithfulness.ExportArithmetic" "LeanLeanFaithfulness.ExportArithmetic.gcd_sum_diff_eq_one"
run_generated "arena-bogus-proof" "rejected" 1 "Faithfulness.Arena.Bogus1" "LeanLeanFaithfulness.Arena.Bogus1.thm" "LeanLeanFaithfulness.Arena.Bogus1.thm"
run_generated "arena-proj-of-prop" "rejected" 1 "Faithfulness.Arena.ProjOfProp" "LeanLeanFaithfulness.Arena.ProjOfProp.badFalse" "LeanLean.Expr.const \"True\" [] vs LeanLean.Expr.const \"False\" []"
run_static "arena-level-imax-normalization" "rejected" 1 "testdata/arena/level-imax-normalization.ndjson" "while replaying [\"down\"]"
run_static "arena-constlevels" "rejected" 1 "testdata/arena/constlevels.ndjson" "while replaying [\"_test\"]"
run_static "unsupported-partial-definition" "unsupported" 2 "testdata/unsupported/partial-definition.ndjson" "partial definition is outside the local export checker"
run_static "unsupported-unsafe-axiom" "unsupported" 2 "testdata/unsupported/unsafe-axiom.ndjson" "trusted replay rejects unsafe axiom"
run_static "unsupported-expression" "unsupported" 2 "testdata/unsupported/unsupported-expression.ndjson" "expression entry must have exactly one expression constructor"

echo "arena-input: box-unbox"
set +e
arena_output="$(IN="$artifact_dir/box-unbox.ndjson" "$checker" 2>&1)"
arena_code="$?"
set -e
printf '%s\n' "$arena_output"
if [[ "$arena_code" != "0" ]]; then
  echo "error: Arena input case returned exit code $arena_code; expected 0" >&2
  exit 1
fi
