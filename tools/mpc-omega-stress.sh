#!/usr/bin/env bash
set -euo pipefail

lean4export_bin="${MPC_LEAN4EXPORT:-lean4export}"
artifact_dir="${MPC_EXPORT_TEST_DIR:-.lake/build/export-tests}"
profile_dir="${MPC_PROFILE_DIR:-.tmp}"
timeout_seconds="${MPC_STRESS_TIMEOUT:-120}"
label="mpc-omega-nat-linear-bounds"
artifact="$artifact_dir/$label.ndjson"
profile="$profile_dir/$label.profile.jsonl"

if ! command -v "$lean4export_bin" >/dev/null 2>&1; then
  echo "error: lean4export not found; set MPC_LEAN4EXPORT" >&2
  exit 2
fi

mkdir -p "$artifact_dir" "$profile_dir"

lake build MPCFixtures.ExportOmega mpc-check-export

checker=".lake/build/bin/mpc-check-export"
lean_path="$(pwd)/.lake/build/lib/lean"

echo "export: $label"
LEAN_PATH="$lean_path" "$lean4export_bin" \
  MPCFixtures.ExportOmega \
  -- \
  MPCFixtures.ExportOmega.nat_linear_bounds \
  > "$artifact"

echo "profile: $label"
set +e
timeout "${timeout_seconds}s" "$checker" --profile-jsonl "$artifact" > "$profile" 2>&1
code="$?"
set -e

echo "artifact: $artifact"
echo "profile: $profile"
echo "exit-code: $code"
echo "profile-tail:"
tail -n 8 "$profile"

case "$code" in
  0|1|2|124)
    exit 0
    ;;
  *)
    exit "$code"
    ;;
esac
