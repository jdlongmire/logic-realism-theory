#!/bin/bash
# Safely update Mathlib with cache fetch
# Usage: ./scripts/update-mathlib.sh

set -e
cd "$(dirname "$0")/.."

echo "Updating Mathlib..."
lake update mathlib

echo "Fetching updated cache..."
lake exe cache get

echo "Rebuilding..."
lake build

echo "Mathlib update complete."
