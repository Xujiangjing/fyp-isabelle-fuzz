#!/usr/bin/env bash
set -euo pipefail

ZP="/Users/xujiangjing/Isabelle2025/Isabelle2025.app/contrib/zipperposition-2.1-1/x86_64-darwin/zipperposition"
INPUT_DIR="$HOME/fyp-isabelle-fuzz/unique_inputs"
OUT_DIR="$HOME/fyp-isabelle-fuzz/replay_batch_results"
mkdir -p "$OUT_DIR"

MAIN_LOG="$OUT_DIR/main_harness.log"
LAMBDA_LOG="$OUT_DIR/lambda_check.log"
SUMMARY="$OUT_DIR/summary.txt"

: > "$MAIN_LOG"
: > "$LAMBDA_LOG"
: > "$SUMMARY"

main_ok=0
main_nonzero=0
main_parse=0
main_exception=0

lambda_ok=0
lambda_nonzero=0
lambda_exception=0

echo "[*] Running main harness..." | tee -a "$SUMMARY"

for f in "$INPUT_DIR"/*.p; do
  [ -e "$f" ] || continue

  echo "==================================================" >> "$MAIN_LOG"
  echo "[FILE] $f" >> "$MAIN_LOG"

  set +e
  out=$(gtimeout 10 "$ZP" --input tptp --output none --steps 1 --timeout 1 "$f" 2>&1)
  status=$?
  set -e

  printf '%s\n' "$out" >> "$MAIN_LOG"
  echo "[exit=$status]" >> "$MAIN_LOG"

  if [ "$status" -eq 0 ]; then
    main_ok=$((main_ok + 1))
  else
    main_nonzero=$((main_nonzero + 1))
  fi

  if printf '%s' "$out" | grep -qi "parse error"; then
    main_parse=$((main_parse + 1))
  fi

  if printf '%s' "$out" | grep -qiE "exception|Failure\("; then
    main_exception=$((main_exception + 1))
  fi
done

echo "[*] Running lambda-free check..." | tee -a "$SUMMARY"

for f in "$INPUT_DIR"/*.p; do
  [ -e "$f" ] || continue

  echo "==================================================" >> "$LAMBDA_LOG"
  echo "[FILE] $f" >> "$LAMBDA_LOG"

  set +e
  out=$("$ZP" --input tptp --output none --check-lambda-free only "$f" 2>&1)
  status=$?
  set -e

  printf '%s\n' "$out" >> "$LAMBDA_LOG"
  echo "[exit=$status]" >> "$LAMBDA_LOG"

  if [ "$status" -eq 0 ]; then
    lambda_ok=$((lambda_ok + 1))
  else
    lambda_nonzero=$((lambda_nonzero + 1))
  fi

  if printf '%s' "$out" | grep -qiE "exception|Failure\("; then
    lambda_exception=$((lambda_exception + 1))
  fi
done

{
  echo "Main harness (--steps 1 --timeout 1):"
  echo "  ok=$main_ok"
  echo "  nonzero=$main_nonzero"
  echo "  parse_errors=$main_parse"
  echo "  exceptions=$main_exception"
  echo
  echo "Lambda-free only:"
  echo "  ok=$lambda_ok"
  echo "  nonzero=$lambda_nonzero"
  echo "  exceptions=$lambda_exception"
} | tee -a "$SUMMARY"

echo
echo "[*] Summary written to $SUMMARY"
echo "[*] Main log:   $MAIN_LOG"
echo "[*] Lambda log: $LAMBDA_LOG"