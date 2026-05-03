#!/usr/bin/env bash
set -euo pipefail

lean4export_bin="${LEANLEAN_LEAN4EXPORT:-lean4export}"
artifact="${LEANLEAN_EXPORT_SMOKE_OUT:-.lake/build/leanlean-export-smoke.ndjson}"

lake build Faithfulness.ExportSmoke leanlean-check-export

LEAN_PATH="$(pwd)/.lake/build/lib/lean" \
  "$lean4export_bin" \
  Faithfulness.ExportSmoke \
  -- \
  LeanLeanFaithfulness.ExportSmoke.unbox \
  > "$artifact"

lake exe leanlean-check-export "$artifact"
