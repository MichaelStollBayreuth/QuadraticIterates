#!/usr/bin/env bash

# Run the comparator check for this project locally, with Lake's built-in `lake comparator`
# (Lean v4.35.0 and later). It certifies that the repository proves the challenge statement(s) of
# the config (default: all challenge theorems); see comparator/README.md for what is checked.
#
# Usage: scripts/run-comparator.sh [CONFIG] [OPTIONS]
#   CONFIG   the challenge description (default: comparator/challenges.json)
#   OPTIONS  passed on to `lake comparator`, e.g. `--paranoid` to run all external checkers
#            bundled with Lean besides its own kernel
#
# Requires bubblewrap (`bwrap`) with unprivileged user namespaces; `lake comparator` builds and
# exports both modules inside its sandbox and never loads the project's `.olean`s itself.

set -euo pipefail

# Move to the repository root (this script lives in scripts/).
cd "$(dirname "$0")/.."

CONFIG="comparator/challenges.json"
if [ $# -gt 0 ] && [ "${1#-}" = "$1" ]; then
  CONFIG="$1"
  shift
fi

# Bring the library oleans up to date first: the sandbox cannot write to the project directory,
# and with a current build the sandboxed Solution build only replays it.
lake build QuadraticIterates

# Exit 0 and "Your solution is okay!" = certified; exit 1 = rejected; exit 2 = could not start.
exec lake comparator --config "$CONFIG" "$@"
