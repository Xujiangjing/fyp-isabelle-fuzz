from pathlib import Path
import sys

if len(sys.argv) != 3:
    print("Usage: python3 split_tptp_blocks.py INPUT.p OUTDIR")
    sys.exit(1)

inp = Path(sys.argv[1])
outdir = Path(sys.argv[2])
outdir.mkdir(parents=True, exist_ok=True)

text = inp.read_text(encoding="utf-8", errors="replace").splitlines()

blocks = []
cur = []

for line in text:
    # comment lines can be their own block if outside a declaration
    if not cur and line.startswith("%"):
        blocks.append([line])
        continue

    cur.append(line)

    # crude but effective for these Isabelle-produced files:
    # a declaration ends on a line whose stripped form ends with ")."
    if line.strip().endswith(")."):
        blocks.append(cur)
        cur = []

if cur:
    blocks.append(cur)

for i, block in enumerate(blocks):
    (outdir / f"{i:04d}.txt").write_text("\n".join(block) + "\n", encoding="utf-8")

print(f"Wrote {len(blocks)} blocks to {outdir}")