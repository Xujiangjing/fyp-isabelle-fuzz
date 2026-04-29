#!/usr/bin/env bash
set -u

# =========================
# Config
# =========================
ISABELLE_BIN="${ISABELLE_BIN:-isabelle}"
WORKDIR="${WORKDIR:-$HOME/fyp-isabelle-fuzz/ho_format_bug}"
SESSION_NAME="HO_Format_Bug"
THEORY_NAME="HO_Format_Bug"
OUTDIR="$WORKDIR/collected"
BEFORE_LIST="$WORKDIR/before_probs.txt"
AFTER_LIST="$WORKDIR/after_probs.txt"
NEW_LIST="$WORKDIR/new_probs.txt"
SUMMARY="$WORKDIR/summary.txt"

mkdir -p "$WORKDIR" "$OUTDIR"

echo "[*] WORKDIR = $WORKDIR"
echo "[*] ISABELLE_BIN = $ISABELLE_BIN"

# =========================
# Step 1: write ROOT
# =========================
cat > "$WORKDIR/ROOT" <<'EOF'
session HO_Format_Bug = HOL +
  options [document = false]
  theories
    HO_Format_Bug
EOF

# =========================
# Step 2: write theory
# =========================
cat > "$WORKDIR/$THEORY_NAME.thy" <<'EOF'
theory HO_Format_Bug
  imports Main
begin

lemma test_e_1: "(f :: nat => nat) x = f x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma test_vampire_1: "(f :: nat => nat) x = f x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma test_zipper_1: "(f :: nat => nat) x = f x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma test_e_2: "((\<lambda>y::nat. f y) x) = f x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma test_vampire_2: "((\<lambda>y::nat. f y) x) = f x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma test_zipper_2: "((\<lambda>y::nat. f y) x) = f x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma test_e_3: "map (f :: nat => nat) [x] = [f x]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma test_vampire_3: "map (f :: nat => nat) [x] = [f x]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma test_zipper_3: "map (f :: nat => nat) [x] = [f x]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

definition fof_val :: nat where "fof_val = 0"
definition tff_val :: nat where "tff_val = 0"
definition thf_val :: nat where "thf_val = 0"

lemma test_name_e: "fof_val + tff_val = tff_val + fof_val"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  by (simp add: fof_val_def tff_val_def)

lemma test_name_vampire: "fof_val + tff_val = tff_val + fof_val"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  by (simp add: fof_val_def tff_val_def)

lemma test_name_zipper: "fof_val + tff_val = tff_val + fof_val"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  by (simp add: fof_val_def tff_val_def)

end
EOF

echo "[*] Removing old prob files first..."
find "$HOME/.isabelle" -type f \( -name 'prob_*.p' -o -name 'prob_*_proof.p' \) -delete 2>/dev/null || true

# =========================
# Step 3: snapshot existing prob files
# =========================
echo "[*] Snapshotting existing prob_*.p files..."
find "$HOME/.isabelle" -type f \( -name 'prob_*.p' -o -name 'prob_*_proof.p' \) 2>/dev/null | sort > "$BEFORE_LIST"
echo "[*] Before count: $(wc -l < "$BEFORE_LIST" | tr -d ' ')"

# =========================
# Step 4: build session
# =========================
echo "[*] Running Isabelle build..."
"$ISABELLE_BIN" build -D "$WORKDIR" -v "$SESSION_NAME"
BUILD_RC=$?
echo "[*] Isabelle build exit code: $BUILD_RC"

# =========================
# Step 5: snapshot after build
# =========================
find "$HOME/.isabelle" -type f \( -name 'prob_*.p' -o -name 'prob_*_proof.p' \) 2>/dev/null | sort > "$AFTER_LIST"
echo "[*] After count: $(wc -l < "$AFTER_LIST" | tr -d ' ')"

comm -13 "$BEFORE_LIST" "$AFTER_LIST" > "$NEW_LIST" || true
NEW_COUNT=$(wc -l < "$NEW_LIST" | tr -d ' ')
echo "[*] New prob files: $NEW_COUNT"

# =========================
# Step 6: copy new files out
# =========================
rm -f "$OUTDIR"/*
while IFS= read -r f; do
  [ -f "$f" ] || continue
  base="$(basename "$f")"
  cp "$f" "$OUTDIR/$base"
done < "$NEW_LIST"

echo "[*] Copied new files to: $OUTDIR"

# =========================
# Step 7: analyze
# =========================
{
  echo "========================================"
  echo "HO FORMAT BUG EXPERIMENT SUMMARY"
  echo "========================================"
  echo
  echo "Workdir: $WORKDIR"
  echo "Collected: $OUTDIR"
  echo "Build exit code: $BUILD_RC"
  echo "New prob files: $NEW_COUNT"
  echo
} > "$SUMMARY"

analyze_file() {
  local f="$1"
  echo "----------------------------------------" >> "$SUMMARY"
  echo "FILE: $f" >> "$SUMMARY"

  echo "[header tags]" >> "$SUMMARY"
  grep -nE '^(fof|tff|thf)\(' "$f" | head -20 >> "$SUMMARY" || echo "(none)" >> "$SUMMARY"

  echo >> "$SUMMARY"
  echo "[suspicious higher-order markers]" >> "$SUMMARY"
  grep -nE 'thf\(|happ|ti[0-9]*_|tc_|lambda|lam|\\\$let|\\\$ite|\\^' "$f" | head -50 >> "$SUMMARY" || echo "(none)" >> "$SUMMARY"

  echo >> "$SUMMARY"
  echo "[first 20 lines]" >> "$SUMMARY"
  sed -n '1,20p' "$f" >> "$SUMMARY"

  echo >> "$SUMMARY"
}

for f in "$OUTDIR"/*.p; do
  [ -e "$f" ] || continue
  analyze_file "$f"
done

# =========================
# Step 8: optional prover replay
# =========================
{
  echo
  echo "========================================"
  echo "PROVER REPLAY"
  echo "========================================"
} >> "$SUMMARY"

run_cmd() {
  local label="$1"
  shift
  echo "[$label]" >> "$SUMMARY"
  "$@" >> "$SUMMARY" 2>&1
  echo >> "$SUMMARY"
}

have_cmd() {
  command -v "$1" >/dev/null 2>&1
}

for f in "$OUTDIR"/*.p; do
  [ -e "$f" ] || continue
  echo "----------------------------------------" >> "$SUMMARY"
  echo "REPLAY FILE: $f" >> "$SUMMARY"

  if have_cmd eprover; then
    run_cmd "eprover" timeout 20 eprover "$f"
  else
    echo "[eprover] not found" >> "$SUMMARY"
    echo >> "$SUMMARY"
  fi

  if have_cmd vampire; then
    run_cmd "vampire" timeout 20 vampire "$f"
  else
    echo "[vampire] not found" >> "$SUMMARY"
    echo >> "$SUMMARY"
  fi

  if have_cmd zipperposition; then
    run_cmd "zipperposition" timeout 20 zipperposition --input tptp --output none "$f"
  else
    echo "[zipperposition] not found" >> "$SUMMARY"
    echo >> "$SUMMARY"
  fi
done

# =========================
# Step 9: print hints
# =========================
echo
echo "[*] Done."
echo "[*] Summary file: $SUMMARY"
echo "[*] Collected prob files: $OUTDIR"
echo
echo "[*] Quick checks:"
printf '%s\n' "    grep -nE '^(fof|tff|thf)\(' $OUTDIR/*.p"
printf '%s\n' '    grep -nE '"'"'thf\(|happ|ti[0-9]*_|tc_|lambda|lam|\\$let|\\$ite|\^'"'"' '"$OUTDIR"'/*.p'
printf '%s\n' "    sed -n '1,120p' $SUMMARY"