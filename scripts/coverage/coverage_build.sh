#!/usr/bin/env bash
# ──────────────────────────────────────────────────────────────────────
# coverage_build.sh — Build Zipperposition with bisect_ppx instrumentation
#
# Prerequisites:
#   opam install bisect_ppx       (if not already installed)
#
# Usage:
#   cd ~/zipperposition           (or ~/zipperposition-test)
#   bash ~/fyp-isabelle-fuzz/coverage_build.sh
#
# What it does:
#   1. Installs bisect_ppx via opam (idempotent)
#   2. Builds Zipperposition with coverage instrumentation via BISECT_ENABLE=yes
#   3. Outputs the instrumented binary path
# ──────────────────────────────────────────────────────────────────────
set -euo pipefail

ZP_DIR="${1:-$(pwd)}"

echo "╔══════════════════════════════════════════════════════════╗"
echo "║  Building Zipperposition with bisect_ppx instrumentation ║"
echo "╚══════════════════════════════════════════════════════════╝"
echo ""
echo "[*] Zipperposition source: $ZP_DIR"

cd "$ZP_DIR"

# ── Step 1: Ensure bisect_ppx is installed ───────────────────────────
echo ""
echo "[1/3] Checking bisect_ppx..."
if opam list bisect_ppx --installed -s 2>/dev/null | grep -q bisect_ppx; then
    echo "  ✓ bisect_ppx already installed"
else
    echo "  Installing bisect_ppx..."
    opam install bisect_ppx -y
fi

# ── Step 2: Clean previous build ─────────────────────────────────────
echo ""
echo "[2/3] Cleaning previous build..."
dune clean

# ── Step 3: Build with instrumentation ───────────────────────────────
echo ""
echo "[3/3] Building with BISECT_ENABLE=yes ..."
BISECT_ENABLE=yes dune build 2>&1 | tail -5

# ── Locate the binary ────────────────────────────────────────────────
BIN="$ZP_DIR/_build/default/src/main/zipperposition.exe"
if [ -f "$BIN" ]; then
    echo ""
    echo "════════════════════════════════════════════════════════════"
    echo "  ✓ Instrumented binary ready:"
    echo "    $BIN"
    echo ""
    echo "  Usage with coverage_compare.py:"
    echo "    python3 coverage_compare.py \\"
    echo "      --zp-instrumented $BIN \\"
    echo "      --baseline-dir ~/fyp-isabelle-fuzz/baseline_inputs \\"
    echo "      --targeted-dir ~/fyp-isabelle-fuzz/unique_inputs \\"
    echo "      --output-dir ~/fyp-isabelle-fuzz/coverage_results"
    echo "════════════════════════════════════════════════════════════"
else
    echo "[!] Build succeeded but binary not found at expected path."
    echo "    Looking for it..."
    find "$ZP_DIR/_build" -name "zipperposition.exe" -type f 2>/dev/null
    exit 1
fi
