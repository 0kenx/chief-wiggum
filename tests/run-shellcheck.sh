#!/usr/bin/env bash
# Replicates CI shellcheck lint locally
set -euo pipefail

cd "$(dirname "$0")/.."

echo "=== Shellcheck Lint ==="
echo ""

echo "Checking bin scripts..."
find bin -type f -perm +111 -exec shellcheck --severity=warning {} +

echo "Checking lib scripts..."
find lib -name "*.sh" -type f -exec shellcheck --severity=warning {} +

echo "Checking test scripts..."
find tests -name "*.sh" -type f -exec shellcheck --severity=warning {} +

echo "Checking hooks scripts..."
find hooks -name "*.sh" -type f -exec shellcheck --severity=warning {} +

echo "Checking root scripts..."
shellcheck --severity=warning install.sh install-symlink.sh

echo ""
echo "All shellcheck checks passed!"
