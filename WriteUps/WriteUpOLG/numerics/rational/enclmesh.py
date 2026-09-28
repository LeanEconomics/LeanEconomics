"""Rate-interval enclosures on a mesh of cells, and the pairwise increment certificate between cells.
gamma = argv[1], bracket [argv[2], argv[3]] in net rates, argv[4] cells.  Every cell [Ra, Rb] carries ONE
enclosure of the stage consumption valid for every rate in it: cash on hand m_dn at Ra and m_up at Rb,
Psi^lo with beta Rb, Psi^hi with beta Ra (Psi_R(m_R - c) is monotone in R through the coefficient and
through m, so the extreme rates give the extreme values; the certificate for a fixed rate in the cell
is then an instance of IntervalEuler's three theorems).  For two cells i < j the failure bound
    V_j(z) = max_i ( hi_j(a_{i+1}) - lo_i(a_i) - dr_min a_i )^+,   dr_min = Ra_j - Rb_i,
against the budget D(Rb_i - 1) - D(Ra_j - 1) certifies S(r2) - S(r1) > D(r2) - D(r1) for EVERY r1 in cell
i and r2 in cell j, i.e. no equilibrium in cell i together with one in cell j.  If every pair with
j - i >= m certifies, any two equilibrium rates are within m h of each other.
Grid, rounding, search and envelope as in encl.py (which this file extends; the single-rate case is h=0).
"""
from fractions import Fraction as F
from math import comb
import sys, time, bisect, os
from array import array
from multiprocessing import Pool

D = 10**15
def up(n, d):  return -((-n) // d)
def dn(n, d):  return n // d
def q2i(x, hi): return up(x.numerator*D, x.denominator) if hi else dn(x.numerator*D, x.denominator)
def icbrt_dn(n):                      # floor cube root, n >= 0
    if n <= 0: return 0
    x = int(round(n ** (1/3))) if n < 2**200 else 1 << ((n.bit_length() + 2)//3)
    while x*x*x > n: x -= max(1, (x*x*x - n) // (3*x*x) )
    while (x+1)**3 <= n: x += max(1, (n - (x+1)**3) // (3*(x+1)**2) + 1) if (x+1)**3 <= n else 0
    while x*x*x > n: x -= 1
    while (x+1)**3 <= n: x += 1
    return x
def icbrt_up(n):
    x = icbrt_dn(n)
    return x if x*x*x == n else x + 1
def iroot_dn(n, g):                   # floor g-th root of n >= 0
    if n <= 0: return 0
    x = 1 << ((n.bit_length() + g - 1) // g)          # >= true root
    while True:
        y = ((g - 1) * x + n // x**(g - 1)) // g
        if y >= x: break
        x = y
    while x**g > n: x -= 1
    while (x+1)**g <= n: x += 1
    return x
def iroot_up(n, g):
    x = iroot_dn(n, g)
    return x if x**g == n else x + 1
def pow_neg3(c, hi):                  # (c/D)^{-gam} as integer over D:  D^{gam+1} / c^gam
    assert c > 0
    return up(D**(gam+1), c**gam) if hi else dn(D**(gam+1), c**gam)
def root_neg3(x, hi):                 # (x/D)^{-1/gam} as integer over D:  root_gam(D^{gam+1} / x)
    assert x > 0
    return iroot_up(up(D**(gam+1), x), gam) if hi else iroot_dn(dn(D**(gam+1), x), gam)

# ------------------------------------------------------------------ calibration (rational)
nz, J = 7, 60
gam = int(sys.argv[1]) if len(sys.argv) > 1 else 3
beta, rho = F(24,25), F(9,10)
alpha, delta = F(9,25), F(2,25)
def rouwenhorst(n, rho):
    p = (1+rho)/2; P = [[p,1-p],[1-p,p]]
    for m in range(3, n+1):
        Q = [[F(0)]*m for _ in range(m)]
        for i in range(m-1):
            for j in range(m-1):
                Q[i][j] += p*P[i][j]; Q[i][j+1] += (1-p)*P[i][j]
                Q[i+1][j] += (1-p)*P[i][j]; Q[i+1][j+1] += p*P[i][j]
        P = [[Q[i][j]/sum(Q[i]) for j in range(m)] for i in range(m)]
    return P
Pi = rouwenhorst(nz, rho)
raw = [F(301,1000), F(449,1000), F(670,1000), F(1), F(1492,1000), F(2226,1000), F(3320,1000)]
nu = [F(comb(nz-1, i), 2**(nz-1)) for i in range(nz)]
mbar = sum(nu[i]*raw[i] for i in range(nz)); y = [r/mbar for r in raw]
def Dem(r): return alpha/((1-alpha)*(r+delta))

# ------------------------------------------------------------------ grid (integers over D)
AMAX = int(os.environ.get('ENCL_AMAX', '3000'))   # grid top; looseness beyond it creeps inward by ~1/R per stage
STEP_NUM, STEP_DEN = (10025, 10000) if os.environ.get('ENCL_FINE') else (101, 100)   # relative step above 3
grid = [i * (D // 400) for i in range(0, 1201)]         # 0 .. 3 step 0.0025
a = grid[-1]
while a < AMAX * D:
    a = up(a * STEP_NUM, STEP_DEN); grid.append(a)
NA = len(grid)
gridf = [g / D for g in grid]

# ------------------------------------------------------------------ enclosure machinery
def m_of(R, z, ap, hi):
    v = y[z] + R * F(ap, D)
    return q2i(v, hi)

def enc_c(lo, hi, zp, ap, want_low, RR=None, corner=None):
    R = None if RR is None else (RR[0] if want_low else RR[1])
    """rigorous bound on c_k(ap, zp) from the grid enclosures, by monotonicity and concavity, and
    by the certified corner region [0, astar_lo] where c = m exactly."""
    if ap <= 0: ap = 0
    if corner is not None and ap < corner[zp]:          # certified for a < corner (corner 0: nothing)
        return m_of(R, zp, ap, not want_low)          # low rate rounded down / high rate rounded up
    i = bisect.bisect_right(grid, ap) - 1
    if i >= NA - 1:                                            # beyond the grid: valid but loose
        return lo[zp][NA-1] if want_low else m_of(RR[1], zp, ap, True)
    a0, a1 = grid[i], grid[i+1]
    if want_low:
        l0, l1 = lo[zp][i], lo[zp][i+1]
        if corner is not None and a0 < corner[zp] - 1 and corner[zp] <= ap:   # chord from the last certified point
            a0 = corner[zp] - 1; l0 = m_of(R, zp, a0, False)
        if l1 >= l0: return l0 + dn((ap - a0) * (l1 - l0), a1 - a0)
        return min(l0, l1)
    else:
        # three upper bounds for a concave nondecreasing c on [a_i, a_{i+1}]: monotonicity,
        # the left secant extended forward, and the right secant extended backward
        best = hi[zp][i+1]
        if i >= 1:
            s_up = up((hi[zp][i] - lo[zp][i-1]) * D, a0 - grid[i-1])        # slope*D, rounded up
            best = min(best, hi[zp][i] + up((ap - a0) * s_up, D))
        if i + 2 < NA:
            s_lo = max(0, dn((lo[zp][i+2] - hi[zp][i+1]) * D, grid[i+2] - a1))   # slope*D, rounded down
            best = min(best, hi[zp][i+1] - dn((a1 - ap) * s_lo, D))
        return best

def psi(lo, hi, RR, z, ap, want_low, corner=None):
    """Psi^lo (want_low) or Psi^hi at stage k from the stage-k enclosures, valid for every rate in the
    cell RR = (Ra, Rb): the high rate in Psi^lo (bigger sum, smaller Psi), the low rate in Psi^hi."""
    bR = beta * (RR[1] if want_low else RR[0])
    S = 0
    for zp in range(nz):
        if Pi[z][zp] == 0: continue
        c = enc_c(lo, hi, zp, ap, want_low, RR, corner)               # low c for Psi^lo (bigger sum), high c for Psi^hi
        v = pow_neg3(c, hi=want_low)                       # round up for Psi^lo
        p = Pi[z][zp]
        S += up(v * p.numerator, p.denominator) if want_low else dn(v * p.numerator, p.denominator)
    S = up(S * bR.numerator, bR.denominator) if want_low else dn(S * bR.numerator, bR.denominator)
    if S <= 0:                                             # only possible when rounding down (Psi^hi)
        assert not want_low
        return 10**6 * D                                   # +infinity for our purposes: c <= m anyway
    return root_neg3(S, hi=not want_low)                   # Psi^lo rounded down, Psi^hi rounded up

def float_candidates(lo, hi, RR, corner=None, side='mid'):
    R = (RR[0] + RR[1]) / 2
    """float Newton on the MIDPOINT of the rigorous enclosure logic (same chord/secant/corner
    rules as enc_c, in floats), so the candidate sits within ~1e-12 of the rigorous fixed point."""
    lof = [[v / D for v in row] for row in lo]; hif = [[v / D for v in row] for row in hi]
    cf = None if corner is None else [v / D for v in corner]
    bR = float(beta * R); Rf = float(R); yf = [float(v) for v in y]
    Pif = [[float(Pi[z][zp]) for zp in range(nz)] for z in range(nz)]
    def enc_f(zp, ap, want_low):
        ap = max(ap, 0.0)
        if cf is not None and ap < cf[zp]: return yf[zp] + Rf * ap
        i = bisect.bisect_right(gridf, ap) - 1
        if i >= NA - 1: return lof[zp][NA-1] if want_low else yf[zp] + Rf * ap
        a0, a1 = gridf[i], gridf[i+1]
        if want_low:
            l0, l1 = lof[zp][i], lof[zp][i+1]
            if cf is not None and a0 < cf[zp] and cf[zp] <= ap: a0 = cf[zp]; l0 = yf[zp] + Rf * a0
            return l0 + (ap - a0) * (l1 - l0) / (a1 - a0) if l1 >= l0 else min(l0, l1)
        best = hif[zp][i+1]
        if i >= 1:
            best = min(best, hif[zp][i] + (ap - a0) * (hif[zp][i] - lof[zp][i-1]) / (a0 - gridf[i-1]))
        if i + 2 < NA:
            s_lo = max(0.0, (lof[zp][i+2] - hif[zp][i+1]) / (gridf[i+2] - a1))
            best = min(best, hif[zp][i+1] - (a1 - ap) * s_lo)
        return best
    def psi_f(z, ap):
        s = 0.0
        for zp in range(nz):
            if Pif[z][zp] == 0.0: continue
            c = (enc_f(zp, ap, True) if side == 'lo' else enc_f(zp, ap, False) if side == 'hi'
                 else 0.5 * (enc_f(zp, ap, True) + enc_f(zp, ap, False)))
            s += Pif[z][zp] * c ** (-gam)
        return (bR * s) ** (-1.0/gam)
    out = [[None]*NA for _ in range(nz)]
    for z in range(nz):
        psi0 = psi_f(z, 0.0)
        prev = None
        for i in range(NA):
            m = yf[z] + Rf * gridf[i]
            if m <= psi0: out[z][i] = None; continue
            c = prev if prev is not None and prev < m else 0.5 * m
            for _ in range(30):
                ap = m - c
                if ap < 0: c = 0.5 * (c + m); continue
                f0 = psi_f(z, ap) - c
                h = 1e-6 * max(ap, 1e-3)
                dpsi = (psi_f(z, ap + h) - psi_f(z, ap)) / h
                c_new = c + f0 / (1.0 + max(dpsi, 0.0))
                if c_new <= 0: c_new = 0.5 * c
                if c_new >= m: c_new = 0.5 * (c + m)
                done = abs(c_new - c) < 1e-13 * c
                c = c_new
                if done: break
            out[z][i] = c; prev = c
    return out

def step(lo, hi, RR, corner=None):
    """one rigorous stage step for the whole rate cell RR = (Ra, Rb): cash on hand m_dn at Ra and m_up at Rb,
    Psi^lo at Rb, Psi^hi at Ra; the enclosure holds for c_k(a, z; R) at every R in the cell."""
    Ra, Rb = RR
    cand_lo = float_candidates(lo, hi, RR, corner, 'lo'); cand_hi = float_candidates(lo, hi, RR, corner, 'hi')
    newcorner = [0]*nz
    nlo = [[0]*NA for _ in range(nz)]; nhi = [[0]*NA for _ in range(nz)]
    Rg = [q2i(Ra * F(g, D), False) for g in grid], [q2i(Rb * F(g, D), True) for g in grid]
    yz = [(q2i(v, False), q2i(v, True)) for v in y]
    stats_fallback = 0
    for z in range(nz):
        psi0_lo = psi(lo, hi, RR, z, 0, True, corner); psi0_hi = psi(lo, hi, RR, z, 0, False, corner)
        # corner certified for a <= astar at every rate in the cell: y_up + Rb a <= psi0_lo
        yu = q2i(y[z], True)
        newcorner[z] = dn((psi0_lo - yu) * Rb.denominator, Rb.numerator) + 1 if psi0_lo >= yu else 0
        for i in range(NA):
            m_dn = yz[z][0] + Rg[0][i]; m_up = yz[z][1] + Rg[1][i]
            # ----- lower bound: t <= Psi^lo(m - t) certifies t <= c*.  From a candidate t, the value
            # g = Psi^lo(m - t) is itself certified when t >= c*, since Psi^lo is nondecreasing in a'.
            if psi0_lo >= m_up:
                cL = m_dn                                        # certified corner
            else:
                cs = cand_lo[z][i] if cand_lo[z][i] is not None else m_dn / D
                t = int(cs * (1 - 1e-10) * D)
                if t >= m_dn: t = m_dn - 1
                if t <= 0: t = 1
                cL = None
                for _ in range(6):
                    g = psi(lo, hi, RR, z, m_dn - t, True, corner)
                    if t <= g: cL = t; break
                    t = g
                    if t <= 0: t = 1
                if cL is None:                                   # rigorous bisection fallback
                    stats_fallback += 1
                    L_, H_ = 1, m_dn - 1
                    while H_ - L_ > D // 10**9:
                        M_ = (L_ + H_) // 2
                        if M_ <= psi(lo, hi, RR, z, m_dn - M_, True, corner): L_ = M_
                        else: H_ = M_
                    cL = L_
            # ----- upper bound: t >= Psi^hi(m - t) certifies t >= c*; from below, h = Psi^hi(m - t) is certified.
            if psi0_hi >= m_dn:
                cH = m_up
            else:
                cs = cand_hi[z][i] if cand_hi[z][i] is not None else m_up / D
                t = int(cs * (1 + 1e-10) * D) + 1
                cH = None
                for _ in range(6):
                    if t >= m_up: cH = m_up; break
                    h = psi(lo, hi, RR, z, m_up - t, False, corner)
                    if t >= h: cH = t; break
                    t = h
                if cH is None:
                    stats_fallback += 1
                    L_, H_ = 1, m_up
                    while H_ - L_ > D // 10**9:
                        M_ = (L_ + H_) // 2
                        if M_ >= psi(lo, hi, RR, z, m_up - M_, False, corner): H_ = M_
                        else: L_ = M_
                    cH = H_
            nlo[z][i] = min(m_dn, cL); nhi[z][i] = min(m_up, cH)
            assert nlo[z][i] <= nhi[z][i]
    return nlo, nhi, stats_fallback, newcorner

def terminal(RR):
    lo = [[0]*NA for _ in range(nz)]; hi = [[0]*NA for _ in range(nz)]
    for z in range(nz):
        for i in range(NA):
            lo[z][i] = q2i(y[z] + RR[0] * F(grid[i], D), False); hi[z][i] = q2i(y[z] + RR[1] * F(grid[i], D), True)
    return lo, hi

def kappa_lower(R):
    """lower bounds on kappa_k(R), k = 0..J-1, from an upper bound on Thorn = (beta R)^{1/3}."""
    x = q2i(beta * R, True)
    Th_up = iroot_up(x * D**(gam-1), gam)                        # (x/D)^{1/gam} over D
    Rn, Rd = R.numerator, R.denominator
    k = [D]
    for _ in range(J - 1):
        kR = dn(k[-1] * Rn, Rd)                                  # kappa R rounded down
        k.append(dn(kR * D, Th_up + up(k[-1] * Rn, Rd)))        # kappa R / (Th + kappa R), rounded down
    return k


def Dm(r): return float(Dem(r))

def run_cell(args):
    ic, Ra, Rb = args
    RR = (Ra, Rb)
    t0 = time.time()
    lo, hi = terminal(RR); cc = None
    L = [(array('q', lo[0]), None, None)]  # placeholder replaced below
    L = []
    def pack(lo, hi, cc):
        return ([array('q', row) for row in lo], [array('q', row) for row in hi], None if cc is None else list(cc))
    L.append(pack(lo, hi, cc))
    widths = []
    for k in range(1, J):
        lo, hi, fb, cc = step(lo, hi, RR, cc)
        L.append(pack(lo, hi, cc))
        w = max(hi[z][i] - lo[z][i] for z in range(nz) for i in range(NA) if grid[i] <= 10*D)
        widths.append(w / D)
    # reach of this cell (valid for every rate in it: m_up at Rb, lower enclosure)
    r = [0]
    for j in range(1, J):
        k = J - j; lo_, hi_, cc_ = L[k]
        best = 0
        for z in range(nz):
            g = q2i(y[z] + Rb * F(r[-1], D), True) - enc_c(lo_, hi_, z, r[-1], True, RR, cc_)
            best = max(best, g)
        r.append(max(best, 0))
    return ic, L, r, widths, time.time() - t0

def pair_bound(Li, Lj, reach_i, reach_j, Rb_i, Ra_j, Rb_j):
    """B for r1 in cell i, r2 in cell j; the envelope at the higher cell's rates."""
    reach = [max(a_, b_) for a_, b_ in zip(reach_i, reach_j)]
    dr = Ra_j - Rb_i
    dr_n, dr_d = dr.numerator, dr.denominator
    ebar = []
    for j in range(1, J+1):
        k = J - j; lo1, hi1, _ = Li[k]; lo2, hi2, _ = Lj[k]
        tot = 0
        for z in range(nz):
            V = 0
            l1 = lo1[z]; h2 = hi2[z]; rj = reach[j-1]
            for i in range(NA - 1):
                if grid[i] > rj: break
                v = h2[i+1] - l1[i] - dn(grid[i] * dr_n, dr_d)
                if v > V: V = v
            tot += up(V * nu[z].numerator, nu[z].denominator)
        ebar.append(tot)
    kap = kappa_lower(Ra_j)                       # kappa_k(R) rises with R for gamma > 1: the cell's floor is at Ra_j
    e = 0; total = 0
    for j in range(1, J+1):
        total += e
        if j < J:
            Lj_up = up((D - kap[J - j]) * Rb_j.numerator, Rb_j.denominator)
            e = up(e * Lj_up, D) + ebar[j-1]
    return F(up(total, J), D), max(ebar) / D

def main():
    rlo, rhi, ncell = F(sys.argv[2]), F(sys.argv[3]), int(sys.argv[4])
    h = (rhi - rlo) / ncell
    cells = [(i, 1 + rlo + i*h, 1 + rlo + (i+1)*h) for i in range(ncell)]
    nproc = int(os.environ.get("ENCL_PROCS", "7"))
    print(f"gamma {gam}, bracket [{float(rlo):.4f}, {float(rhi):.4f}], {ncell} cells of width {float(h):.5f}, grid {NA} points, D = 1e15, {nproc} workers", flush=True)
    t0 = time.time()
    res = {}
    with Pool(nproc) as pool:
        for ic, L, r, widths, dt in pool.imap_unordered(run_cell, cells):
            res[ic] = (L, r)
            print(f"cell {ic:2d} [{float(cells[ic][1]-1):.4f},{float(cells[ic][2]-1):.4f}]: widths on a<=10 at stages 20/40/59: {widths[19]:.2e} {widths[39]:.2e} {widths[58]:.2e}; reach at ages 10/30/60: {r[9]/D:.2f} {r[29]/D:.2f} {r[59]/D:.2f}; {dt:.0f}s", flush=True)
    print(f"all cells done in {time.time()-t0:.0f}s; pairwise certificates:", flush=True)
    cert = {}
    for i in range(ncell):
        for j in range(i+2, ncell):
            Li, ri = res[i]; Lj, rj = res[j]
            B, ebmax = pair_bound(Li, Lj, ri, rj, cells[i][2], cells[j][1], cells[j][2])
            budget = Dem(cells[i][2] - 1) - Dem(cells[j][1] - 1)
            cert[(i, j)] = (B < budget, float(B), float(budget), ebmax)
    # the smallest separation m such that every pair with j - i >= m certifies
    m_ok = None
    for m in range(2, ncell):
        if all(cert[(i, j)][0] for i in range(ncell) for j in range(i+m, ncell)):
            m_ok = m; break
    for i in range(ncell):
        row = " ".join(("C" if cert[(i,j)][0] else ".") if j >= i+2 else ("-" if j > i else " ") for j in range(ncell))
        print(f"  cell {i:2d} | {row}", flush=True)
    for (i, j), (ok, B, bud, ebm) in sorted(cert.items()):
        if j - i <= 4 or not ok:
            print(f"  ({i:2d},{j:2d}) gap>={float(cells[j][1]-cells[i][2]):.4f}: B={B:.5f} budget={bud:.5f} max ebar={ebm:.4f} {'CERTIFIED' if ok else 'not'}", flush=True)
    if m_ok is None:
        print("no separation certifies every pair", flush=True)
    else:
        print(f"every pair of cells at least {m_ok} apart certifies: any two equilibrium rates in the bracket are within {float(m_ok*h):.5f} of each other ({m_ok} cells of width {float(h):.5f}); {time.time()-t0:.0f}s total", flush=True)

if __name__ == "__main__":
    main()
