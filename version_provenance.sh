#!/bin/bash
# version_provenance.sh — capture version info for all tools, multiple versions

OUTFILE="$HOME/fyp-isabelle-fuzz/version_provenance.txt"

# 定义工具列表：NAME PATH
TOOLS=(
    "Zipperposition-Isabelle /Applications/Isabelle2025-2.app/contrib/zipperposition-2.1-1/x86_64-darwin/zipperposition"
    "Zipperposition-Patched $HOME/provers/zipperposition/zipperposition.exe"
    "Eprover $HOME/provers/eprover"
    "Vampire $HOME/provers/vampire"
    "Z3-Isabelle /Applications/Isabelle2025.app/contrib/z3-4.4.0pre-4/x86_64-darwin/z3"
    "Z3-Latest $HOME/provers/z3-4.16/bin/z3"
    "CVC5 $HOME/provers/cvc5/cvc5"
)

{
echo "=================================================="
echo "Version Provenance Snapshot"
echo "Generated: $(date)"
echo "Host: $(uname -a)"
echo "=================================================="
echo

echo "--- Isabelle bundles ---"
ls -d /Applications/Isabelle*.app 2>/dev/null
echo

# 批量检测工具版本
for tool in "${TOOLS[@]}"; do
    NAME=$(echo $tool | cut -d' ' -f1)
    BIN=$(echo $tool | cut -d' ' -f2-)
    echo "--- $NAME ---"
    if [ -x "$BIN" ]; then
        "$BIN" --version 2>&1 | head -5
    else
        echo "$BIN: Not found or not executable"
    fi
    echo
done

# Isabelle 本体
ISABELLE_BIN="/Applications/Isabelle2025-2.app/Contents/MacOS/isabelle"
echo "--- Isabelle itself ---"
[ -x "$ISABELLE_BIN" ] && "$ISABELLE_BIN" version 2>&1 || echo "$ISABELLE_BIN: Not found"
echo

# AFL++ (Docker)
echo "--- AFL++ (in Docker) ---"
docker exec zipfuzz afl-fuzz -h 2>&1 | head -3 || echo "Docker container 'zipfuzz' not running"
echo

# OCaml + bisect_ppx
echo "--- OCaml + bisect_ppx ---"
opam --version
opam list bisect_ppx menhir dune 2>&1 | head -10
echo

# lcov
echo "--- lcov (E prover coverage) ---"
lcov --version 2>&1
gcov --version 2>&1 | head -1
echo

echo "=================================================="
echo "End of snapshot"
echo "=================================================="
} | tee "$OUTFILE"

echo
echo "[*] Saved to: $OUTFILE"