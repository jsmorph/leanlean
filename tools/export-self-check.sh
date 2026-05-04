#!/usr/bin/env bash
set -euo pipefail

lean4export_bin="${LEANLEAN_LEAN4EXPORT:-lean4export}"
artifact_dir="${LEANLEAN_EXPORT_SELF_CHECK_DIR:-.lake/build/export-self-check}"

if ! command -v "$lean4export_bin" >/dev/null 2>&1; then
  echo "error: lean4export not found; set LEANLEAN_LEAN4EXPORT" >&2
  exit 2
fi

mkdir -p "$artifact_dir"

lake build \
  LeanLean.Syntax \
  LeanLean.Kernel \
  leanlean-check-export

checker=".lake/build/bin/leanlean-check-export"
lean_path="$(pwd)/.lake/build/lib/lean"

run_export_self_check() {
  local label="$1"
  local module="$2"
  shift 2

  local artifact="$artifact_dir/$label.ndjson"
  local output
  local code

  echo "export-self-check: $label"
  LEAN_PATH="$lean_path" "$lean4export_bin" "$module" -- "$@" > "$artifact"

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
  if [[ "$output" != *"message: checked"* ]]; then
    echo "error: $label output did not report checked declarations" >&2
    exit 1
  fi
}

run_export_self_check \
  "syntax-selected-roots" \
  "LeanLean.Syntax" \
  "LeanLean.Name" \
  "LeanLean.Level" \
  "LeanLean.Literal" \
  "LeanLean.Expr" \
  "LeanLean.Level.defEq"

run_export_self_check \
  "kernel-selected-roots" \
  "LeanLean.Kernel" \
  "LeanLean.LevelContext" \
  "LeanLean.Telescope" \
  "LeanLean.Context" \
  "LeanLean.Result" \
  "LeanLean.Env" \
  "LeanLean.Binder" \
  "LeanLean.checkDefEqIn" \
  "LeanLean.replayDeclarations"
