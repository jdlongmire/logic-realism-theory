#!/bin/bash
# Clean LRT artifacts only, preserve Mathlib cache
# Usage: ./scripts/clean.sh

set -e
cd "$(dirname "$0")/.."

echo "Cleaning LRT build artifacts..."

# Remove LRT oleans only
find .lake/build/lib/LRT -name "*.olean" -delete 2>/dev/null || true
find .lake/build/lib/LRT -name "*.ilean" -delete 2>/dev/null || true
find .lake/build/lib/LRT -name "*.trace" -delete 2>/dev/null || true

# Remove LRT ir files
rm -rf .lake/build/ir/LRT 2>/dev/null || true

echo "Clean complete. Mathlib cache preserved."
