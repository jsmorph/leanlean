#!/usr/bin/env bash
set -euo pipefail

lean4export_bin="${LEANLEAN_LEAN4EXPORT:-lean4export}"
artifact_dir="${LEANLEAN_MPC_EXPORT_SELF_CHECK_DIR:-.lake/build/mpc-export-self-check}"
default_cache_db=".tmp/mpc-self-check-cache.db"
cache_db="${LEANLEAN_MPC_CACHE_DB-${LEANLEAN_MPC_LAYER_DB-$default_cache_db}}"

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
  MPC.Manifest \
  MPC.Env \
  MPC.Declaration \
  MPC.Packages.Literal \
  MPC.Packages.Equality \
  MPC.Packages.Quotient \
  MPC.Packages.Projection \
  MPC.Packages.PrimitiveNat \
  MPC.Packages.Inductive.Basic \
  MPC.Packages.Inductive.Positivity \
  MPC.Packages.Inductive.Recursor \
  MPC.Packages.Inductive.Admission \
  MPC.Packages.Inductive.Reduction \
  MPC.Packages.Inductive.Prop \
  MPC.Normalize \
  mpc-check-export \
  leanlean-export-roots

checker=".lake/build/bin/mpc-check-export"
root_lister=".lake/build/bin/leanlean-export-roots"
lean_path="$(pwd)/.lake/build/lib/lean"
cache_args=()

if [[ -n "$cache_db" ]]; then
  cache_args=(--cache-layer "$cache_db")
  echo "mpc-export-self-check: cache=$cache_db"
fi

run_mpc_export_self_check() {
  local label="$1"
  local module="$2"
  local roots_file="$artifact_dir/$label.roots"
  local artifact="$artifact_dir/$label.ndjson"
  local checker_args=()
  local expected_status="accepted"
  local expected_message_fragment="message: checked"
  local output
  local code

  if [[ "${#cache_args[@]}" != "0" ]]; then
    checker_args=("${cache_args[@]}")
    expected_status="cache-accepted"
    expected_message_fragment="message: reused"
  fi

  "$root_lister" --module "$module" --self-check > "$roots_file"
  mapfile -t roots < "$roots_file"

  if [[ "${#roots[@]}" == "0" ]]; then
    echo "error: $label has no roots" >&2
    exit 1
  fi

  echo "mpc-export-self-check: $label roots=${#roots[@]}"
  LEAN_PATH="$lean_path" "$lean4export_bin" "$module" -- "${roots[@]}" > "$artifact"

  set +e
  output="$("$checker" "${checker_args[@]}" "$artifact" 2>&1)"
  code="$?"
  set -e

  printf '%s\n' "$output"
  if [[ "$code" != "0" ]]; then
    echo "error: $label returned exit code $code; expected 0" >&2
    exit 1
  fi
  local first_line="${output%%$'\n'*}"
  if [[ "$first_line" != "$expected_status" ]]; then
    echo "error: $label returned status $first_line; expected $expected_status" >&2
    exit 1
  fi
  if [[ "$output" != *"$expected_message_fragment"* ]]; then
    echo "error: $label output did not report $expected_message_fragment" >&2
    exit 1
  fi
}

run_mpc_export_self_check "mpc-name" "MPC.Name"
run_mpc_export_self_check "mpc-basic" "MPC.Basic"
run_mpc_export_self_check "mpc-level" "MPC.Level"
run_mpc_export_self_check "mpc-expr" "MPC.Expr"
run_mpc_export_self_check "mpc-context" "MPC.Context"
run_mpc_export_self_check "mpc-manifest" "MPC.Manifest"
run_mpc_export_self_check "mpc-env" "MPC.Env" "layer"
run_mpc_export_self_check "mpc-declaration" "MPC.Declaration" "layer"
run_mpc_export_self_check "mpc-packages-literal" "MPC.Packages.Literal" "layer"
run_mpc_export_self_check "mpc-packages-equality" "MPC.Packages.Equality" "layer"
run_mpc_export_self_check "mpc-packages-quotient" "MPC.Packages.Quotient" "layer"
run_mpc_export_self_check "mpc-packages-projection" "MPC.Packages.Projection" "layer"
run_mpc_export_self_check "mpc-packages-primitive-nat" "MPC.Packages.PrimitiveNat" "layer"
run_mpc_export_self_check "mpc-packages-inductive-basic" "MPC.Packages.Inductive.Basic" "layer"
run_mpc_export_self_check "mpc-packages-inductive-positivity" "MPC.Packages.Inductive.Positivity" "layer"
run_mpc_export_self_check "mpc-packages-inductive-recursor" "MPC.Packages.Inductive.Recursor" "layer"
run_mpc_export_self_check "mpc-packages-inductive-admission" "MPC.Packages.Inductive.Admission" "layer"
run_mpc_export_self_check "mpc-packages-inductive-reduction" "MPC.Packages.Inductive.Reduction" "layer"
run_mpc_export_self_check "mpc-packages-inductive-prop" "MPC.Packages.Inductive.Prop" "layer"
run_mpc_export_self_check "mpc-normalize" "MPC.Normalize" "layer"
