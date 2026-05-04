#!/usr/bin/env bash
set -euo pipefail

lake build leanlean-self-check

output="$(lake exe leanlean-self-check --generated-support 2>&1)"
printf '%s\n' "$output"

expect_fragment() {
  local fragment="$1"
  if [[ "$output" != *"$fragment"* ]]; then
    echo "error: generated-support output missing fragment: $fragment" >&2
    exit 1
  fi
}

expect_fragment "module LeanLean.Syntax: generated-support candidates"
expect_fragment "module LeanLean.Kernel: generated-support candidates"
expect_fragment "accepted"
expect_fragment "rejected"
expect_fragment "unsupported"
expect_fragment "assumed"
expect_fragment "support-outcome: module=LeanLean.Syntax outcome=accepted"
expect_fragment "support-outcome: module=LeanLean.Kernel outcome=accepted"
expect_fragment "candidate-summary:"
expect_fragment "assumption-summary:"
