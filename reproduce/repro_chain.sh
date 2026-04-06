#!/usr/bin/env bash
#
# repro_chain.sh — Full reproduction chain: Isabelle → Sledgehammer → Zipperposition
#
# This script demonstrates the complete bug path:
#   1. Runs Isabelle on the reproduction .thy file
#   2. Collects the generated .p files (retained via overlord)
#   3. Runs each .p file through Zipperposition in both modes
#   4. Shows exactly which files trigger bugs and what errors occur
#
# Usage:
#   bash repro_chain.sh [/path/to/zipperposition]
#
# Prerequisites:
#   - Isabelle 2025 on $PATH (or adjust ISABELLE_CMD below)
#   - Repro_LambdaFree.thy in the same directory as this script

set -uo pipefail

# ── Configuration ──
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ZP="${1:-zipperposition}"
ISABELLE_CMD="isabelle"
THY_FILE="$SCRIPT_DIR/Repro_LambdaFree.thy"
WORK_DIR="$HOME/fyp-isabelle-fuzz/repro_chain"
ISABELLE_HOME_USER="$HOME/.isabelle"

# ── Setup ──
mkdir -p "$WORK_DIR"
echo "============================================================"
echo "  REPRODUCTION CHAIN"
echo "  Zipperposition: $ZP"
echo "  Theory file:    $THY_FILE"
echo "  Work dir:       $WORK_DIR"
echo "============================================================"

# ── Step 0: Prepare session directory ──
SESSION_DIR="$WORK_DIR/session"
mkdir -p "$SESSION_DIR"
cp "$THY_FILE" "$SESSION_DIR/"

cat > "$SESSION_DIR/ROOT" <<'EOF'
session ReproLambdaFree = HOL +
  theories
    Repro_LambdaFree
EOF

# ── Step 1: Clean old .p files ──
echo ""
echo "[Step 1] Cleaning old problem files..."
find "$ISABELLE_HOME_USER" -name "prob_*.p" -delete 2>/dev/null || true

# ── Step 2: Run Isabelle build ──
echo "[Step 2] Running Isabelle build (this generates TPTP via Sledgehammer)..."
echo "         This may take 2-5 minutes..."
BUILD_LOG="$WORK_DIR/build.log"

$ISABELLE_CMD build -c -j1 -o threads=1 -D "$SESSION_DIR" 2>&1 | tee "$BUILD_LOG"
echo ""

# ── Step 3: Collect .p files ──
echo "[Step 3] Collecting generated .p files..."
P_DIR="$WORK_DIR/p_files"
mkdir -p "$P_DIR"
# Clean old
rm -f "$P_DIR"/*.p

count=0
while IFS= read -r f; do
    [ -e "$f" ] || continue
    cp "$f" "$P_DIR/"
    count=$((count + 1))
done < <(find "$ISABELLE_HOME_USER" -name "prob_*.p" 2>/dev/null | sort)

echo "  Collected $count .p files into $P_DIR"
echo ""

if [ "$count" -eq 0 ]; then
    echo "[!] No .p files found. Sledgehammer may not have run."
    echo "[!] Check build log: $BUILD_LOG"
    exit 1
fi

# ── Step 4: Test each .p file ──
echo "[Step 4] Testing each .p file with Zipperposition..."
echo ""

REPORT="$WORK_DIR/repro_results.txt"
: > "$REPORT"

confirmed=0
parse_errors=0
ok_count=0

for f in "$P_DIR"/*.p; do
    [ -e "$f" ] || continue
    fname="$(basename "$f")"

    echo "──────────────────────────────────────────────" | tee -a "$REPORT"
    echo "File: $fname" | tee -a "$REPORT"

    # Normal mode
    set +e
    normal_out=$("$ZP" --input tptp --output none --steps 1 --timeout 1 "$f" 2>&1)
    normal_exit=$?
    set -e

    # Lambda-free check
    set +e
    lf_out=$("$ZP" --input tptp --output none --check-lambda-free only "$f" 2>&1)
    lf_exit=$?
    set -e

    echo "  Normal mode:      exit=$normal_exit" | tee -a "$REPORT"
    echo "  Lambda-free mode: exit=$lf_exit" | tee -a "$REPORT"

    if printf '%s' "$lf_out" | grep -q "Failure("; then
        failure_line=$(printf '%s' "$lf_out" | grep "Failure(" | head -1)
        echo "  >>> BUG: Uncaught Failure()" | tee -a "$REPORT"
        echo "  >>> $failure_line" | tee -a "$REPORT"
        confirmed=$((confirmed + 1))
    elif printf '%s' "$lf_out" | grep -qi "parse error"; then
        echo "  >>> PARSE ERROR (TPTP keyword collision bug)" | tee -a "$REPORT"
        parse_errors=$((parse_errors + 1))
    else
        echo "  OK (no bug triggered)" | tee -a "$REPORT"
        ok_count=$((ok_count + 1))
    fi

    echo "" | tee -a "$REPORT"
done

echo "============================================================" | tee -a "$REPORT"
echo "SUMMARY" | tee -a "$REPORT"
echo "  Lambda-free Failure() bugs:  $confirmed" | tee -a "$REPORT"
echo "  Parse error bugs:            $parse_errors" | tee -a "$REPORT"
echo "  OK (no bug):                 $ok_count" | tee -a "$REPORT"
echo "  Total files tested:          $count" | tee -a "$REPORT"
echo "============================================================" | tee -a "$REPORT"
echo ""
echo "[*] Full results: $REPORT"
echo "[*] .p files:     $P_DIR"
echo ""
echo "To manually inspect a specific bug, run:"
echo "  $ZP --input tptp --output none --check-lambda-free only $P_DIR/<file>.p"
