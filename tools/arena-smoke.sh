#!/usr/bin/env bash
set -euo pipefail

checker="${LEANLEAN_CHECK_EXPORT:-.lake/build/bin/leanlean-check-export}"

lake build leanlean-check-export

run_expect() {
  local label="$1"
  local artifact="$2"
  local expected_status="$3"
  local expected_code="$4"
  local expected_fragment="${5:-}"
  local output
  local code

  echo "arena: $label"
  set +e
  output="$(IN="$artifact" "$checker" 2>&1)"
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

run_expect "level-imax-normalization" "testdata/arena/level-imax-normalization.ndjson" "rejected" 1 "while replaying [\"down\"]"
run_expect "constlevels" "testdata/arena/constlevels.ndjson" "rejected" 1 "while replaying [\"_test\"]"
