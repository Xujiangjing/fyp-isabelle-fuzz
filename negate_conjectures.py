#!/usr/bin/env python3
"""
negate_conjectures.py — Negate the conjecture in TPTP .p files for soundness testing.

For each input file where the original conjecture is Theorem,
produces a negated version. If Zipperposition still returns Theorem
on the negated version, that's a soundness bug.
"""

import re
import sys
from pathlib import Path


def negate_file(content: str) -> str:
    """Negate the conjecture in a TPTP file.
    
    Finds the thf(conj_..., conjecture, FORMULA). declaration
    and wraps FORMULA with ~(...).
    """
    lines = content.split('\n')
    result = []
    i = 0
    
    while i < len(lines):
        line = lines[i]
        
        # Match actual conjecture declaration (not in comments)
        # Must start with thf( or fof( etc, not with %
        stripped = line.strip()
        if (not stripped.startswith('%') and 
            re.match(r'\s*(thf|tff|fof|cnf)\s*\(', stripped) and
            'conjecture' in stripped):
            
            # Collect the full statement (may span multiple lines)
            stmt_lines = [line]
            while i < len(lines) - 1 and not line.rstrip().endswith(').'):
                i += 1
                line = lines[i]
                stmt_lines.append(line)
            
            # Join into one string
            stmt = '\n'.join(stmt_lines)
            
            # Parse: thf(name, conjecture, FORMULA).
            # We need to wrap FORMULA with ~(...)
            # Find the position after "conjecture,"
            match = re.search(r'((?:thf|tff|fof|cnf)\s*\([^,]+,\s*conjecture\s*,)', stmt)
            if match:
                prefix = stmt[:match.end()]
                rest = stmt[match.end():]
                
                # rest is something like "\n    (((formula))))."
                # Remove the trailing ")." and add negation
                if rest.rstrip().endswith(').'):
                    # Find the last ")."
                    idx = rest.rstrip().rfind(').')
                    # Everything up to the last character before ")." is the formula body
                    # We need to find where the formula ends and the closing ")." is
                    
                    # Simpler approach: strip trailing ")." then re-add
                    formula_part = rest.rstrip()
                    # Remove final ")."
                    formula_part = formula_part[:-2]
                    # Remove the outermost closing paren that belongs to thf(...)
                    # Count parens to find it
                    
                    # Actually, the structure is:
                    # thf(name, conjecture, FORMULA).
                    # So after "conjecture," we have: FORMULA).
                    # The last ")" before "." closes the thf(...) 
                    # We need: thf(name, conjecture, ~(FORMULA)).
                    
                    # The structure after "conjecture," is:
                    #   FORMULA).
                    # where the last ) closes thf(... and . ends the statement
                    # We want: ~(FORMULA)).
                    formula_part = formula_part.rstrip()
                    if formula_part.endswith(')'):
                        formula_body = formula_part[:-1]  # remove closing ) of thf
                        negated = prefix + ' ~(' + formula_body.lstrip() + '))).'
                    else:
                        negated = prefix + ' ~(' + formula_part.lstrip() + '))).'
                    
                    result.append(negated)
                    i += 1
                    continue
            
            # If we couldn't parse it, keep original
            result.extend(stmt_lines)
            i += 1
            continue
        
        result.append(line)
        i += 1
    
    return '\n'.join(result)


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Negate conjectures in TPTP files")
    parser.add_argument("--input-dir", required=True, help="Directory with .p files")
    parser.add_argument("--output-dir", required=True, help="Output directory for negated files")
    args = parser.parse_args()
    
    input_dir = Path(args.input_dir)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    files = sorted(input_dir.glob("*.p"))
    count = 0
    
    for f in files:
        content = f.read_text(encoding='utf-8', errors='replace')
        
        # Only process files that have a conjecture
        if not re.search(r'^\s*(thf|tff|fof|cnf)\s*\([^,]+,\s*conjecture', content, re.MULTILINE):
            continue
        
        negated = negate_file(content)
        
        # Verify the negation actually changed something
        if negated == content:
            print(f"  [SKIP] {f.name} — negation failed")
            continue
        
        out_path = output_dir / f"neg_{f.name}"
        out_path.write_text(negated, encoding='utf-8')
        count += 1
    
    print(f"[*] Negated {count} files → {output_dir}")


if __name__ == "__main__":
    main()
