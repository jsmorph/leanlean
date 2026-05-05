#!/usr/bin/env bash
set -euo pipefail

lean4export_bin="${LEANLEAN_LEAN4EXPORT:-lean4export}"
artifact_dir="${LEANLEAN_MPC_EXPORT_SELF_CHECK_DIR:-.lake/build/mpc-export-self-check}"

if ! command -v "$lean4export_bin" >/dev/null 2>&1; then
  echo "error: lean4export not found; set LEANLEAN_LEAN4EXPORT" >&2
  exit 2
fi

mkdir -p "$artifact_dir"

lake build \
  MPC.Name \
  MPC.Basic \
  MPC.Level \
  MPC.Expr \
  MPC.Context \
  mpc-check-export \
  leanlean-export-roots

checker=".lake/build/bin/mpc-check-export"
root_lister=".lake/build/bin/leanlean-export-roots"
lean_path="$(pwd)/.lake/build/lib/lean"

run_mpc_export_self_check() {
  local label="$1"
  local module="$2"
  local roots_file="$artifact_dir/$label.roots"
  local artifact="$artifact_dir/$label.ndjson"
  local output
  local code

  "$root_lister" --module "$module" --self-check > "$roots_file"
  mapfile -t roots < "$roots_file"

  if [[ "${#roots[@]}" == "0" ]]; then
    echo "error: $label has no roots" >&2
    exit 1
  fi

  echo "mpc-export-self-check: $label roots=${#roots[@]}"
  LEAN_PATH="$lean_path" "$lean4export_bin" "$module" -- "${roots[@]}" > "$artifact"

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

run_mpc_export_self_check "mpc-name" "MPC.Name"
run_mpc_export_self_check "mpc-basic" "MPC.Basic"
run_mpc_export_self_check "mpc-level" "MPC.Level"
run_mpc_export_self_check "mpc-expr" "MPC.Expr"
run_mpc_export_self_check "mpc-context" "MPC.Context"
