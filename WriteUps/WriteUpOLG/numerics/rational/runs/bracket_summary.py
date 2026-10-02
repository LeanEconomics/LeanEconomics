"""Summarise a resumable bracket run (derivcert.py mode fixed): leaves, coverage, worst margin.
Usage: python3 bracket_summary.py runs/bracket_g3_4to6.txt 0.04 0.06"""
import sys
from fractions import Fraction as F
res, rlo, rhi = sys.argv[1], F(sys.argv[2]), F(sys.argv[3])
rows = {}
for line in open(res):
    p = line.split()
    if len(p) >= 8 and p[0] == "cell":
        a, b = p[8].strip("[]").split(",")
        rows[p[1]] = (p[2] == "CERTIFIED", float(p[4]), float(p[6]), F(a), F(b))
leaves = {c: r for c, r in rows.items() if not (c + "L" in rows and c + "R" in rows)}
ok = [r for r in leaves.values() if r[0]]
bad = [c for c, r in leaves.items() if not r[0]]
print(f"{len(rows)} results, {len(leaves)} leaves ({len(rows)-len(leaves)} split), {len(bad)} uncertified leaves {bad}")
if ok:
    w = max(ok, key=lambda r: r[1] / r[2])
    print(f"worst B_d {max(r[1] for r in ok):.3f}; smallest |D'| {min(r[2] for r in ok):.3f}; "
          f"worst ratio B_d/|D'| {w[1]/w[2]:.3f} at [{float(w[3]):.5f},{float(w[4]):.5f}]")
    print(f"widths: min {float(min(r[4]-r[3] for r in ok)):.5f}, max {float(max(r[4]-r[3] for r in ok)):.5f}")
iv = sorted((r[3], r[4]) for r in ok)
cov, cur = True, rlo
for a, b in iv:
    if a > cur: cov = False; print(f"gap [{float(cur):.5f},{float(a):.5f}]")
    cur = max(cur, b)
if cur < rhi: cov = False; print(f"gap [{float(cur):.5f},{float(rhi):.5f}]")
print("COVERED: certified leaves cover the bracket" if cov else "NOT covered")
