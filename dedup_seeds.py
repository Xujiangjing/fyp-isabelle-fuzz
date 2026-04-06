from pathlib import Path
import hashlib
import shutil

src = Path.home() / "fyp-isabelle-fuzz" / "master_seeds"
dst = Path.home() / "fyp-isabelle-fuzz" / "unique_inputs"
dst.mkdir(parents=True, exist_ok=True)

seen = {}
count = 0

for f in sorted(src.glob("*.p")):
    if f.name.endswith("_proof.p"):
        continue

    data = f.read_bytes()
    h = hashlib.sha256(data).hexdigest()

    if h not in seen:
        out = dst / f"{count:04d}_{f.name}"
        shutil.copy2(f, out)
        seen[h] = f.name
        count += 1

print(f"Unique non-proof seeds: {count}")
print(f"Output dir: {dst}")