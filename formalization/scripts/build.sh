#!/bin/bash
# Build LRT formalization with Mathlib cache
# Usage: ./scripts/build.sh [--no-cache]

set -e
cd "$(dirname "$0")/.."

# Fetch Mathlib cache unless --no-cache
if [[ "$1" != "--no-cache" ]]; then
    echo "Fetching Mathlib cache..."
    lake exe cache get 2>/dev/null || echo "Cache fetch failed, building from source"
fi

echo "Building LRT formalization..."
lake build

echo "Build complete."
