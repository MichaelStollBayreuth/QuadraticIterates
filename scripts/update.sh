#!/usr/bin/env bash

# Update Mathlib and the Lean toolchain.

# Download the latest lean-toolchain file from the Mathlib4 repository
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain

# Update all dependencies (Mathlib and doc-gen4, which is a plain requirement here).
# Afterwards, check that the doc-gen4 revision in lakefile.toml still matches the toolchain.
lake update
