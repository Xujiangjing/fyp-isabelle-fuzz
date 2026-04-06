#!/usr/bin/env bash
set -uo pipefail

INPUT_DIR="$HOME/fyp-isabelle-fuzz/unique_inputs"
OUT_DIR="$HOME/fyp-isabelle-fuzz/replay_results"
LOG_FILE="$OUT_DIR/replay.log"
SUMMARY_FILE="$OUT_DIR/summary.tsv"

mkdir -p "$OUT_DIR"
: > "$LOG_FILE"
: > "$SUMMARY_FILE"

TARGET="${1:-zipperposition}"

if [ ! -x "$TARGET" ] && ! command -v "$TARGET" >/dev/null 2>&1; then
  echo "[!] Target not found or not executable: $TARGET"
  exit 1
fi

run_one() {
  local f="$1"
  local status

  if command -v gtimeout >/dev/null 2>&1; then
    gtimeout 10 "$TARGET" "$f" >> "$LOG_FILE" 2>&1
    status=$?
  elif command -v timeout >/dev/null 2>&1; then
    timeout 10 "$TARGET" "$f" >> "$LOG_FILE" 2>&1
    status=$?
  else
    # macOS 没有 timeout/gtimeout 时，直接跑
    # 这时可能 hang，所以更推荐你装 coreutils
    "$TARGET" "$f" >> "$LOG_FILE" 2>&1
    status=$?
  fi

  return $status
}

count=0

for f in "$INPUT_DIR"/*.p; do
  [ -e "$f" ] || continue
  count=$((count + 1))

  echo "==================================================" | tee -a "$LOG_FILE"
  echo "[*] File: $f" | tee -a "$LOG_FILE"

  run_one "$f"
  status=$?

  echo "[exit=$status]" | tee -a "$LOG_FILE"
  printf "%s\t%s\n" "$(basename "$f")" "$status" >> "$SUMMARY_FILE"
done

echo "[*] Replayed $count files"
echo "[*] Log saved to $LOG_FILE"
echo "[*] Summary saved to $SUMMARY_FILE"