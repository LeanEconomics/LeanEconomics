"""Certified bounds on capital supply S(r) at a single rate, from the point enclosure of derivcert.py.
The cohort-assets recursion A_0(a,z) = a, A_{k+1}(a,z) = a + sum_z' pi(z,z') A_k(g_{k+1}(a,z), z') is run
with the interval policy g_{k+1}(a,z) in [m_dn - c_hi, m_up - c_lo] at each grid point: saving is
nondecreasing in assets and so is A_k, so a lower bound on g is read at the grid point below it and an
upper bound at the grid point above, with outward rounding over D.  Then
S(r) = (1/J) sum_z nu_z A_{J-1}(0,z) lies in [S_lo, S_hi], and S < D or S > D is certified.
Usage: ENCL_FINE=fine python3 levelcert.py gamma r      (e.g. 3 1/25)"""
import sys, os, bisect, time
from fractions import Fraction as F
gam_s, r = sys.argv[1], F(sys.argv[2]); R = 1 + r
sys.argv = ['derivcert.py', gam_s]
import derivcert as dc
D, grid, NA, nz, J, y, Pi, nu = dc.D, dc.grid, dc.NA, dc.nz, dc.J, dc.y, dc.Pi, dc.nu
t0 = time.time()
_, L, reach, widths, dt = dc.run_cell((0, R, R))
print(f"point enclosure at r = {float(r):.4%} ({dt:.0f}s); newborn width {widths[-1]:.2e}; reach by age 1/10/30/60: "
      + ", ".join(f"{reach[j-1]/D:.2f}" for j in (1, 10, 30, 60)), flush=True)
m_dn = [[dc.q2i(y[z] + R * F(g, D), False) for g in grid] for z in range(nz)]
m_up = [[dc.q2i(y[z] + R * F(g, D), True) for g in grid] for z in range(nz)]
TOP = min(NA - 1, bisect.bisect_right(grid, 3 * max(reach)) + 2)   # the cohort never reads above this
Alo = [[grid[i] for i in range(TOP + 1)] for _ in range(nz)]      # stage 0: A_0 = a exactly
Ahi = [[grid[i] for i in range(TOP + 1)] for _ in range(nz)]      # None = no bound available (creeps in from TOP)
for k in range(J - 1):                                            # build A_{k+1} from A_k and g_{k+1}
    lo, hi, cc = L[k + 1]
    nlo = [[None] * (TOP + 1) for _ in range(nz)]; nhi = [[None] * (TOP + 1) for _ in range(nz)]
    for z in range(nz):
        for i in range(TOP + 1):
            g_lo = max(0, m_dn[z][i] - hi[z][i]); g_hi = max(0, m_up[z][i] - lo[z][i])
            ilo = bisect.bisect_right(grid, g_lo) - 1; ihi = bisect.bisect_left(grid, g_hi)
            if ilo <= TOP and all(Alo[zp][ilo] is not None for zp in range(nz) if Pi[z][zp]):
                slo = sum(Pi[z][zp] * Alo[zp][ilo] for zp in range(nz) if Pi[z][zp])
                nlo[z][i] = grid[i] + dc.dn(slo.numerator, slo.denominator)
            if ihi <= TOP and all(Ahi[zp][ihi] is not None for zp in range(nz) if Pi[z][zp]):
                shi = sum(Pi[z][zp] * Ahi[zp][ihi] for zp in range(nz) if Pi[z][zp])
                nhi[z][i] = grid[i] + dc.up(shi.numerator, shi.denominator)
    Alo, Ahi = nlo, nhi
    assert all(Ahi[z][0] is not None and Alo[z][0] is not None for z in range(nz)), f"bound unavailable at zero wealth, stage {k+1}"
S_lo = sum(nu[z] * Alo[z][0] for z in range(nz)) / J / D
S_hi = sum(nu[z] * Ahi[z][0] for z in range(nz)) / J / D
Dm = dc.Dem(r)
verdict = "S < D CERTIFIED" if S_hi < Dm else ("S > D CERTIFIED" if S_lo > Dm else "undecided")
print(f"r = {float(r):.4%}: S in [{float(S_lo):.5f}, {float(S_hi):.5f}], D = {float(Dm):.5f}  ->  {verdict}  ({time.time()-t0:.0f}s)")
