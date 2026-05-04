#!/usr/bin/env bash
set -euo pipefail

lake build leanlean-self-check

output="$(lake exe leanlean-self-check --generated-inventory 2>&1)"
printf '%s\n' "$output"

expect_fragment() {
  local fragment="$1"
  if [[ "$output" != *"$fragment"* ]]; then
    echo "error: generated inventory output missing fragment: $fragment" >&2
    exit 1
  fi
}

expect_fragment "module LeanLean.Syntax: inventoried"
expect_fragment "module LeanLean.Kernel: inventoried"
expect_fragment "summary: class=match-helper"
expect_fragment "summary: class=no-confusion"
expect_fragment "summary: class=sparse-case-helper"
expect_fragment "summary: class=recursive-aux"
expect_fragment "outcome=accepted"
expect_fragment "outcome=rejected"
expect_fragment "outcome=unsupported"

detail_output="$(lake exe leanlean-self-check --generated-inventory --all 2>&1)"
if [[ "$detail_output" != *"detail:"* || "$detail_output" != *"dependencies="* ]]; then
  echo "error: generated inventory detail output missing declaration rows" >&2
  exit 1
fi
