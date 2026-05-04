#!/usr/bin/env bash
set -euo pipefail

lake build \
  Faithfulness.Accepted \
  Faithfulness.UnsupportedModule \
  LeanLean.Export \
  leanlean-check-module

checker=".lake/build/bin/leanlean-check-module"

run_module_expect() {
  local label="$1"
  local expected_status="$2"
  local expected_code="$3"
  local module="$4"
  local root="$5"
  local expected_fragment="${6:-}"
  local output
  local code

  echo "module: $label"
  set +e
  output="$("$checker" --module "$module" --decl "$root" 2>&1)"
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

run_module_expect \
  "accepted-transparent-id" \
  "accepted" \
  0 \
  "Faithfulness.Accepted" \
  "LeanLeanFaithfulness.Accepted.transparentId" \
  "checked 1 declaration entries"

run_module_expect \
  "unsupported-unsafe-definition" \
  "unsupported" \
  2 \
  "Faithfulness.UnsupportedModule" \
  "LeanLeanFaithfulness.UnsupportedModule.unsafeId" \
  "trusted replay rejects unsafe definition"

run_module_expect \
  "rejected-supported-fragment" \
  "rejected" \
  1 \
  "LeanLean.Export" \
  "LeanLean.Export.checkString" \
  "Nat.Linear.Poly.denote_reverse"
