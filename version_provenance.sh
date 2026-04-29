#!/bin/bash
# version_provenance.sh — capture version info for all tools used in this project
# Run once, save the output, append to dissertation as Appendix A.6

OUTFILE="$HOME/fyp-isabelle-fuzz/version_provenance.txt"
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

echo "--- Zipperposition (Isabelle 2025-2 bundled) ---"
/Applications/Isabelle2025-2.app/contrib/zipperposition-2.1-1/x86_64-darwin/zipperposition --version 2>&1 | head -5
echo

echo "--- Zipperposition (your patched build) ---"
~/zipperposition-test/_build/default/src/main/zipperposition.exe --version 2>&1 | head -5
echo "Git status of patched fork:"
git -C ~/zipperposition-test log -1 --format="commit %H%nauthor %an%ndate %ci%nsubject %s" 2>&1
git -C ~/zipperposition-test rev-parse --abbrev-ref HEAD 2>&1
echo

echo "--- E prover (Isabelle bundled) ---"
/Applications/Isabelle2025-2.app/contrib/e-3.2/arm64-darwin/eprover --version 2>&1 | head -3
echo

echo "--- Z3 (Isabelle bundled, old) ---"
/Applications/Isabelle2025.app/contrib/z3-4.4.0pre-4/x86_64-darwin/z3 --version 2>&1
echo

echo "--- Z3 (latest, your install) ---"
~/z3-latest/bin/z3 --version 2>&1 || ~/z3-latest --version 2>&1
echo

echo "--- CVC5 (your build) ---"
~/cvc5/build/bin/cvc5 --version 2>&1 | head -5
echo

echo "--- Isabelle itself ---"
/Applications/Isabelle2025-2.app/Isabelle/bin/isabelle version 2>&1
echo

echo "--- AFL++ (in Docker) ---"
docker exec zipfuzz afl-fuzz -h 2>&1 | head -3 || echo "Docker container 'zipfuzz' not running"
echo

echo "--- OCaml + bisect_ppx ---"
opam --version
opam list bisect_ppx menhir dune 2>&1 | head -10
echo

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