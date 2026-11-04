#!/usr/bin/env bash
# Check the main theorems with leanprover/comparator against the Mathlib-only statements in
# Comparator/Challenge.lean. Tools: comparator and lean4export built for v4.33.1, and landrun.
set -euo pipefail
cd "$(dirname "$0")/.."
T=${COMPARATOR_DIR:-$HOME/tools/comparator-4.33.1}/.lake
export COMPARATOR_LANDRUN=${COMPARATOR_LANDRUN:-$HOME/tools/bin/landrun}
export COMPARATOR_LEAN4EXPORT=${COMPARATOR_LEAN4EXPORT:-$T/packages/lean4export/.lake/build/bin/lean4export}
exec lake env "$T/build/bin/comparator" comparator.json
