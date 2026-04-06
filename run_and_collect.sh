#!/usr/bin/env bash
set -euo pipefail

SESSION_DIR="$HOME/fyp-isabelle-fuzz/session"
COLLECT_DIR="$HOME/fyp-isabelle-fuzz/collected"
LOG_DIR="$HOME/fyp-isabelle-fuzz/logs"
ISABELLE_HOME_USER_DIR="$HOME/.isabelle"

mkdir -p "$COLLECT_DIR" "$LOG_DIR"

RUN_ID=$(date +"%Y%m%d_%H%M%S")
RUN_OUT="$COLLECT_DIR/run_$RUN_ID"
BUILD_LOG="$LOG_DIR/build_$RUN_ID.log"

mkdir -p "$RUN_OUT"

echo "[*] Run ID: $RUN_ID"
echo "[*] Session dir: $SESSION_DIR"
echo "[*] Output dir:  $RUN_OUT"
echo "[*] Log file:    $BUILD_LOG"

echo "[*] Cleaning old problem files from Isabelle cache..."
find "$ISABELLE_HOME_USER_DIR" -name "prob_*.p" -delete 2>/dev/null || true
find "$ISABELLE_HOME_USER_DIR" -name "mash_*" -delete 2>/dev/null || true

echo "[*] Building Isabelle session (clean, single-threaded)..."
isabelle build -c -j1 -o threads=1 -D "$SESSION_DIR" 2>&1 | tee "$BUILD_LOG"

echo "[*] Collecting generated .p files..."
count=0

while IFS= read -r f; do
  [ -e "$f" ] || continue
  new_name="${RUN_ID}_$(basename "$f")"
  cp "$f" "$RUN_OUT/$new_name"
  count=$((count + 1))
done < <(find "$ISABELLE_HOME_USER_DIR" -name "prob_*.p" 2>/dev/null | sort)

echo "[*] Collected $count files into $RUN_OUT"

if [ "$count" -eq 0 ]; then
  echo "[!] No .p files were collected."
  echo "[!] Check build log: $BUILD_LOG"
else
  echo "[*] Collected files:"
  ls -l "$RUN_OUT"
fi