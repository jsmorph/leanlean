#!/usr/bin/env bash
set -euo pipefail

lean4export_bin="${LEANLEAN_LEAN4EXPORT:-lean4export}"
artifact_dir="${LEANLEAN_EXPORT_FULL_SELF_CHECK_DIR:-.lake/build/export-full-self-check}"

if ! command -v "$lean4export_bin" >/dev/null 2>&1; then
  echo "error: lean4export not found; set LEANLEAN_LEAN4EXPORT" >&2
  exit 2
fi

mkdir -p "$artifact_dir"

lake build \
  LeanLean.Syntax \
  LeanLean.Kernel \
  leanlean-check-export \
  leanlean-export-roots

checker=".lake/build/bin/leanlean-check-export"
root_lister=".lake/build/bin/leanlean-export-roots"
lean_path="$(pwd)/.lake/build/lib/lean"

write_roots() {
  local label="$1"
  local module="$2"
  local roots_file="$artifact_dir/$label.roots"

  "$root_lister" --module "$module" --self-check > "$roots_file"
}

combine_roots() {
  local output="$1"
  shift

  sort -u "$@" > "$output"
}

run_export_full_self_check() {
  local label="$1"
  local module="$2"
  local roots_file="$3"

  local artifact="$artifact_dir/$label.ndjson"
  local output
  local code
  mapfile -t roots < "$roots_file"

  if [[ "${#roots[@]}" == "0" ]]; then
    echo "error: $label has no roots" >&2
    exit 1
  fi

  echo "export-full-self-check: $label roots=${#roots[@]}"
  LEAN_PATH="$lean_path" "$lean4export_bin" "$module" -- "${roots[@]}" > "$artifact"

  set +e
  output="$("$checker" --self-check-roots "$roots_file" "$artifact" 2>&1)"
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

  echo "export-full-self-check-gap: $label"
  set +e
  output="$("$checker" --gap-report --self-check-roots "$roots_file" "$artifact" 2>&1)"
  code="$?"
  set -e

  printf '%s\n' "$output"
  if [[ "$code" != "0" ]]; then
    echo "error: $label rooted gap report returned exit code $code; expected 0" >&2
    exit 1
  fi
  first_line="${output%%$'\n'*}"
  if [[ "$first_line" != "gap-report" ]]; then
    echo "error: $label rooted gap report returned status $first_line; expected gap-report" >&2
    exit 1
  fi
  if [[ "$output" != *"rooted-outcome: accepted"* ]]; then
    echo "error: $label rooted gap report did not accept under the rooted policy" >&2
    exit 1
  fi
  if [[ "$output" != *"summary: status=assumed"* ]]; then
    echo "error: $label rooted gap report did not report trusted-base assumptions" >&2
    exit 1
  fi
  if [[ "$output" != *"summary: status=trusted-check"* ]]; then
    echo "error: $label rooted gap report did not report trusted generated checks" >&2
    exit 1
  fi
}

write_roots "syntax-self-check" "LeanLean.Syntax"
write_roots "kernel-self-check-owned" "LeanLean.Kernel"
combine_roots \
  "$artifact_dir/kernel-self-check.roots" \
  "$artifact_dir/syntax-self-check.roots" \
  "$artifact_dir/kernel-self-check-owned.roots"

run_export_full_self_check \
  "syntax-self-check" \
  "LeanLean.Syntax" \
  "$artifact_dir/syntax-self-check.roots"

run_export_full_self_check \
  "kernel-self-check" \
  "LeanLean.Kernel" \
  "$artifact_dir/kernel-self-check.roots"
