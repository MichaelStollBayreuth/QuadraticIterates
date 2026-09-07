#!/usr/bin/env bash

# Run the leanprover/comparator check for this project locally.
#
# Certifies that the repository proves the challenge statements in the given config
# (default: all eight challenge theorems). See comparator/README.md for what is checked.
#
# Requires three binaries; override any location via the environment:
#   COMPARATOR_BIN         the `comparator` binary (built from leanprover/comparator)
#   COMPARATOR_LEAN4EXPORT `lean4export`, built at THIS project's Lean version (tag v4.xx.0)
#   COMPARATOR_LANDRUN     `landrun`, built from its `main` branch
# NB: rebuild lean4export whenever the project's Lean version changes (see ~/lean4/UPDATE.md).

set -euo pipefail

COMPARATOR_BIN="${COMPARATOR_BIN:-$HOME/lean4/comparator/.lake/build/bin/comparator}"
# Default lean4export: prefer a build matching this project's toolchain (a worktree named
# ~/lean4/lean4export-<version>, e.g. lean4export-v4.34.0-rc2), else the floating checkout.
TOOLCHAIN_VERSION="$(sed 's/^leanprover\/lean4://' "$(dirname "$0")/../lean-toolchain" 2>/dev/null || true)"
if [ -z "${COMPARATOR_LEAN4EXPORT:-}" ] \
    && [ -x "$HOME/lean4/lean4export-$TOOLCHAIN_VERSION/.lake/build/bin/lean4export" ]; then
  COMPARATOR_LEAN4EXPORT="$HOME/lean4/lean4export-$TOOLCHAIN_VERSION/.lake/build/bin/lean4export"
fi
: "${COMPARATOR_LEAN4EXPORT:=$HOME/lean4/lean4export/.lake/build/bin/lean4export}"
: "${COMPARATOR_LANDRUN:=$HOME/go/bin/landrun}"
export COMPARATOR_LEAN4EXPORT COMPARATOR_LANDRUN
export PATH="$(dirname "$COMPARATOR_LANDRUN"):$PATH"

# Config file to check (default: all challenge theorems).
CONFIG="${1:-comparator/challenges.json}"

# Move to the repository root (this script lives in scripts/).
cd "$(dirname "$0")/.."

# Fail early with a helpful message if a binary is missing.
for bin in "$COMPARATOR_BIN" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_LANDRUN"; do
  if [ ! -x "$bin" ]; then
    echo "ERROR: comparator binary not found or not executable: $bin" >&2
    echo "See comparator/README.md for how to build/install it; override via env vars." >&2
    exit 1
  fi
done

# Ensure the library oleans are current so the sandboxed Solution build reuses them.
lake build QuadraticIterates

# Run the check (exit 0 and "Your solution is okay!" = certified).
exec lake env "$COMPARATOR_BIN" "$CONFIG"
