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

expect_line() {
  local line="$1"
  if ! grep -Fqx "$line" <<< "$output"; then
    echo "error: generated-support output missing line: $line" >&2
    exit 1
  fi
}

expect_line_count() {
  local line="$1"
  local expected="$2"
  local count
  count="$(grep -Fxc "$line" <<< "$output" || true)"
  if [[ "$count" != "$expected" ]]; then
    echo "error: generated-support output line count for '$line' was $count; expected $expected" >&2
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
expect_fragment "candidate-summary: class=match-helper kind=definition status=accepted count=33"
expect_fragment "candidate-summary: class=match-helper kind=definition status=accepted count=147"
expect_fragment "candidate-summary: class=match-helper kind=definition status=rejected count=2"

assumption_summary_count="$(grep -c '^assumption-summary:' <<< "$output" || true)"
if [[ "$assumption_summary_count" != "25" ]]; then
  echo "error: generated-support output had $assumption_summary_count assumption summaries; expected 25" >&2
  exit 1
fi

expect_line "module LeanLean.Syntax: generated-support candidates 466, accepted 148, rejected 289, unsupported 29, assumed 194"
expect_line "assumption-summary: class=theorem kind=theorem status=assumed count=2"
expect_line "assumption-summary: class=no-confusion kind=definition status=assumed count=20"
expect_line "assumption-summary: class=non-source-definition kind=definition status=assumed count=8"
expect_line "assumption-summary: class=repr-support kind=definition status=assumed count=4"
expect_line "assumption-summary: class=sparse-case-helper kind=definition status=assumed count=14"
expect_line_count "assumption-summary: class=non-source-opaque kind=opaque status=assumed count=1" 2
expect_line "assumption-summary: class=private-or-aux kind=definition status=assumed count=2"
expect_line "assumption-summary: class=derived-decidable kind=definition status=assumed count=3"
expect_line "assumption-summary: class=aux-recursor kind=definition status=assumed count=15"
expect_line "assumption-summary: class=derived-decidable kind=theorem status=assumed count=120"
expect_line "assumption-summary: class=constructor-eliminator kind=definition status=assumed count=2"
expect_line "assumption-summary: class=match-helper kind=definition status=assumed count=3"
expect_line "module LeanLean.Kernel: generated-support candidates 1297, accepted 664, rejected 554, unsupported 79, assumed 366"
expect_line "assumption-summary: class=theorem kind=theorem status=assumed count=4"
expect_line "assumption-summary: class=no-confusion kind=definition status=assumed count=79"
expect_line "assumption-summary: class=derived-decidable kind=definition status=assumed count=20"
expect_line "assumption-summary: class=sparse-case-helper kind=definition status=assumed count=8"
expect_line "assumption-summary: class=repr-support kind=definition status=assumed count=11"
expect_line "assumption-summary: class=non-source-definition kind=definition status=assumed count=12"
expect_line "assumption-summary: class=derived-inhabited kind=definition status=assumed count=2"
expect_line "assumption-summary: class=private-or-aux kind=definition status=assumed count=6"
expect_line "assumption-summary: class=aux-recursor kind=definition status=assumed count=39"
expect_line "assumption-summary: class=derived-decidable kind=theorem status=assumed count=173"
expect_line "assumption-summary: class=constructor-eliminator kind=definition status=assumed count=6"
expect_line "assumption-summary: class=match-helper kind=definition status=assumed count=5"
