#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: MPC_MATHLIB_DIR=<mathlib> tools/mpc-mathlib-probe.sh <module> <root> [root ...]" >&2
}

if [[ "$#" -lt 2 ]]; then
  usage
  exit 2
fi

if [[ "${MPC_MATHLIB_DIR+x}" != "x" || -z "$MPC_MATHLIB_DIR" ]]; then
  echo "error: set MPC_MATHLIB_DIR to an external mathlib checkout" >&2
  exit 2
fi

module="$1"
shift
roots=("$@")

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
mathlib_dir="$(cd -- "$MPC_MATHLIB_DIR" && pwd)"
lean4export_bin="${MPC_LEAN4EXPORT:-lean4export}"
probe_dir="${MPC_MATHLIB_PROBE_DIR:-$repo_root/.tmp/mathlib-probes}"

if [[ "${MPC_PROBE_LABEL+x}" == "x" && -n "$MPC_PROBE_LABEL" ]]; then
  label="$MPC_PROBE_LABEL"
elif [[ "${#roots[@]}" == "1" ]]; then
  label="$module-${roots[0]}"
else
  label="$module-${#roots[@]}-roots"
fi
label="$(printf '%s' "$label" | tr -c 'A-Za-z0-9_.-' '_')"

roots_file="$probe_dir/$label.roots"
artifact="$probe_dir/$label.ndjson"
export_log="$probe_dir/$label.export.log"
output="$probe_dir/$label.output"
checker="$repo_root/.lake/build/bin/mpc-check-export"
checker_args=()

if ! command -v "$lean4export_bin" >/dev/null 2>&1; then
  echo "error: lean4export not found; set MPC_LEAN4EXPORT" >&2
  exit 2
fi

if [[ "${MPC_CACHE_DB+x}" == "x" && -n "$MPC_CACHE_DB" ]]; then
  checker_args+=(--cache-layer "$MPC_CACHE_DB")
fi

if [[ "${MPC_PROBE_STATS:-0}" == "1" ]]; then
  checker_args+=(--stats-jsonl)
fi

mkdir -p "$probe_dir"
printf '%s\n' "${roots[@]}" > "$roots_file"

echo "mpc-mathlib-probe: mathlib=$mathlib_dir"
echo "mpc-mathlib-probe: module=$module"
echo "mpc-mathlib-probe: roots=${#roots[@]}"
echo "mpc-mathlib-probe: artifact=$artifact"

(cd "$repo_root" && lake build mpc-check-export)
(cd "$mathlib_dir" && lake build "$module")
rm -f "$artifact" "$export_log"

set +e
(cd "$mathlib_dir" && lake env "$lean4export_bin" "$module" -- "${roots[@]}") > "$artifact" 2> "$export_log"
export_code="$?"
set -e

if [[ "$export_code" != "0" || ! -s "$artifact" ]]; then
  if [[ -s "$export_log" ]]; then
    cat "$export_log" >&2
  fi
  if [[ "$export_code" == "0" ]]; then
    echo "error: lean4export produced an empty artifact" >&2
  else
    echo "error: lean4export failed with exit code $export_code" >&2
  fi
  exit 1
fi

artifact_lines="$(wc -l < "$artifact")"
if [[ "$artifact_lines" -le "1" ]]; then
  if [[ -s "$export_log" ]]; then
    cat "$export_log" >&2
  fi
  echo "error: lean4export produced no declaration rows for the requested roots" >&2
  exit 1
fi

set +e
"$checker" "${checker_args[@]}" "$artifact" > "$output" 2>&1
code="$?"
set -e

cat "$output"
exit "$code"
