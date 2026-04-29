from pathlib import Path
import sys

if len(sys.argv) < 3:
    print("Usage: python3 rebuild_tptp.py BLOCKDIR OUTPUT.p [skip_ids...]")
    sys.exit(1)

blockdir = Path(sys.argv[1])
outfile = Path(sys.argv[2])
skip_ids = set(sys.argv[3:])

parts = []
for p in sorted(blockdir.glob("*.txt")):
    if p.stem in skip_ids:
        continue
    parts.append(p.read_text(encoding="utf-8", errors="replace"))

outfile.write_text("".join(parts), encoding="utf-8")
print(f"Wrote {outfile}")