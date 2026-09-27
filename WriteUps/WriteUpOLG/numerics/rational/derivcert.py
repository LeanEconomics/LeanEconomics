"""The derivative-form increment certificate: a rigorous lower bound on dS/dr from the enclosures.
Differentiating the Euler equality c^{-g} = beta R sum pi c_k(m - c, z')^{-g} in r at fixed a,
    dc/dr = ( -c/(g R) + Psi_x a + sum_z' w_z' dc_k/dr(x, z') ) / (1 + Psi_x),
    w_z' = beta R pi(z,z') c_k(x,z')^{-g-1} c^{g+1},  Psi_x = sum_z' w_z' d_x c_k(x,z') in [0, (sum w) R],
and dc/dr = a at the corner.  Upper and lower bounds U, L on dc_k/dr are carried on GRID INTERVALS
[a_i, a_{i+1}] (a derivative has no monotonicity to interpolate with): on an interval, a in [a_i,a_{i+1}],
c in [lo(a_i), hi(a_{i+1})], the saving x = m - c in [m_dn(a_i) - hi(a_i), m_up(a_{i+1}) - lo(a_{i+1})], the
next-stage consumption in the enclosure at the ends of that x-range (monotone), the weights between their
extreme values, U_k over the x-range the max over the grid intervals it meets.  Terminal: U_0 = L_0 = a.
The derivative-form failure of Theorem 1 is e = (dc/dr - a)^+ = (-dg/dr)^+, and the envelope gives
    dS/dr >= -(1/J) sum_k G_k sum_z nu_z max_{a in reach} e_{k+1}(a,z) =: -B_d   for every rate in the cell,
so E' = S' - D' > 0 on the cell whenever B_d < |D'| there.  On a cell [Ra, Rb] the enclosures are the cell's,
Rb is used where a larger rate enlarges the bound and Ra where a smaller one does.
Usage: derivcert.py gamma r_lo r_hi ncells   (ncells = 0: the single rate r_lo).
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
AMAX = 3000     # far above the reach: looseness beyond the grid top creeps inward by 1/R per stage
grid = [i * (D // 400) for i in range(0, 1201)]         # 0 .. 3 step 0.0025
a = grid[-1]
while a < AMAX * D:
    a = up(a * 101, 100); grid.append(a)
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

def float_candidates(lo, hi, RR, corner=None):
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
            c = 0.5 * (enc_f(zp, ap, True) + enc_f(zp, ap, False))
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
    cand = float_candidates(lo, hi, RR, corner)
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
                cs = cand[z][i] if cand[z][i] is not None else m_dn / D
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
                cs = cand[z][i] if cand[z][i] is not None else m_up / D
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



def run_cell(args):
    ic, Ra, Rb = args
    RR = (Ra, Rb)
    t0 = time.time()
    import pickle
    cache = f"cache_g{gam}_{Ra.numerator}_{Ra.denominator}_{Rb.numerator}_{Rb.denominator}.pkl"
    if os.path.exists(cache):
        with open(cache, "rb") as fh:
            L, r, widths = pickle.load(fh)
        return ic, L, r, widths, 0.0
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
    with open(cache, "wb") as fh:
        pickle.dump((L, r, widths), fh)
    return ic, L, r, widths, time.time() - t0

NS = int(sys.argv[5]) if len(sys.argv) > 5 else 1      # sub-intervals per grid interval in the derivative pass

def deriv_bound(L, reach, Ra, Rb):
    """the rigorous derivative recursion on (sub)intervals of the grid; returns (B_d, ebar list)."""
    RR = (Ra, Rb)
    gF = F(gam)
    # the fine grid: every grid interval split into NS equal parts; c bounds at its points from the enclosure
    fgrid = []
    for i in range(NA - 1):
        for t in range(NS):
            fgrid.append(grid[i] + (grid[i+1] - grid[i]) * t // NS)
    fgrid.append(grid[NA-1])
    NF = len(fgrid)
    ai = [F(g, D) for g in fgrid]
    # the recursion runs on the whole grid; beyond the grid top a bound is unavailable (None), and the
    # unavailability creeps inward by a factor of about 1 - 0.01 (R - 1)... per stage from the top at
    # 3000, never reaching the reach (~50).  A read of None from inside an age's reach is fatal.
    NI = NF - 1
    U = [[ai[i+1] for i in range(NI)] for _ in range(nz)]         # stage 0: dc/dr = a
    Lw = [[ai[i] for i in range(NI)] for _ in range(nz)]
    E = [None] * J                                                # E[k+1][z][i] = failure bound on interval i
    E[0] = [[F(0)] * NI for _ in range(nz)]
    y_dn = [q2i(v, False) for v in y]; y_up = [q2i(v, True) for v in y]
    for k in range(0, J-1):
        lo_k, hi_k, cor_k = L[k]; lo1, hi1, cor1 = L[k+1]
        Un = [[None]*NI for _ in range(nz)]; Ln = [[None]*NI for _ in range(nz)]; En = [[None]*NI for _ in range(nz)]
        for z in range(nz):
            for i in range(NI):
                a_lo, a_hi = ai[i], ai[i+1]
                if cor1 is not None and fgrid[i+1] <= cor1[z]:           # whole interval in the corner region
                    Un[z][i] = a_hi; Ln[z][i] = a_lo; En[z][i] = F(0); continue
                cl_i = enc_c(lo1, hi1, z, fgrid[i], True, RR, cor1); ch_i = enc_c(lo1, hi1, z, fgrid[i], False, RR, cor1)
                cl_i1 = enc_c(lo1, hi1, z, fgrid[i+1], True, RR, cor1); ch_i1 = enc_c(lo1, hi1, z, fgrid[i+1], False, RR, cor1)
                c_lo = F(cl_i, D); c_hi = F(ch_i1, D)
                m_dn_i = y_dn[z] + q2i(Ra * F(fgrid[i], D), False)
                m_up_i1 = y_up[z] + q2i(Rb * F(fgrid[i+1], D), True)
                x_lo = max(0, m_dn_i - ch_i); x_hi = max(0, m_up_i1 - cl_i1)
                i1 = bisect.bisect_right(fgrid, x_lo) - 1; i2 = bisect.bisect_right(fgrid, x_hi) - 1
                i1 = min(max(i1, 0), NI-1); i2 = min(max(i2, 0), NI-1)
                if x_hi >= grid[NA-1]:                                       # saving beyond the grid top
                    if fgrid[i] <= reach[J-k-2]:
                        raise RuntimeError(f"saving range leaves the grid: stage {k+1}, z {z}, a_i {fgrid[i]/D:.3f}")
                    Un[z][i] = None; Ln[z][i] = None; En[z][i] = None; continue
                vup = -c_lo / (gF * Rb); vlo = -c_hi / (gF * Ra); Wsum = F(0); bad = False
                for zp in range(nz):
                    p = Pi[z][zp]
                    if p == 0: continue
                    ck_lo = F(enc_c(lo_k, hi_k, zp, x_lo, True, RR, cor_k), D)
                    ck_hi = F(enc_c(lo_k, hi_k, zp, x_hi, False, RR, cor_k), D)
                    assert ck_lo > 0
                    w_lo = beta * Ra * p * c_lo**(gam+1) / ck_hi**(gam+1)
                    w_hi = beta * Rb * p * c_hi**(gam+1) / ck_lo**(gam+1)
                    Wsum += w_hi
                    seg = U[zp][i1:i2+1]; segL = Lw[zp][i1:i2+1]
                    if None in seg:
                        if fgrid[i] <= reach[J-k-2]:
                            raise RuntimeError(f"derivative bound read outside its validity: stage {k+1}, z {z}, a_i {grid[i]/D:.3f}")
                        bad = True; break
                    Umax = max(seg); Lmin = min(segL)
                    vup += (w_hi * Umax if Umax >= 0 else w_lo * Umax)
                    vlo += (w_lo * Lmin if Lmin >= 0 else w_hi * Lmin)
                if bad:
                    Un[z][i] = None; Ln[z][i] = None; En[z][i] = None; continue
                Pmax = Wsum * Rb                                           # Psi_x in [0, (sum w) R]
                u = max(vup, (vup + Pmax * a_hi) / (1 + Pmax))
                l = min(vlo, (vlo + Pmax * a_lo) / (1 + Pmax))
                if cor1 is not None and fgrid[i] < cor1[z]:                # interval straddles the corner
                    u = max(u, a_hi); l = min(l, a_lo)
                u = F(up(u.numerator * D, u.denominator), D)               # outward rounding keeps the
                l = F(dn(l.numerator * D, l.denominator), D)               # denominators bounded
                Un[z][i] = u; Ln[z][i] = l; En[z][i] = max(F(0), u - a_lo)
        U, Lw = Un, Ln; E[k+1] = En
    # failure by age (age j has stage J-j), maximised over the reach, nu-weighted
    ebar = []
    for j in range(1, J+1):
        k1 = J - j
        tot = F(0)
        for z in range(nz):
            V = F(0)
            for i in range(NI):
                if fgrid[i] > reach[j-1]: break
                assert E[k1][z][i] is not None
                if E[k1][z][i] > V: V = E[k1][z][i]
            tot += nu[z] * V
        ebar.append(tot)
    kap = kappa_lower(Ra)
    e = F(0); total = F(0)
    for j in range(1, J+1):
        total += e
        if j < J:
            Lj = (1 - F(kap[J-j], D)) * Rb
            e = Lj * e + ebar[j-1]
    return total / J, ebar

def main():
    rlo, rhi, ncell = F(sys.argv[2]), F(sys.argv[3]), int(sys.argv[4])
    if ncell == 0:
        cells = [(0, 1 + rlo, 1 + rlo)]
    else:
        h = (rhi - rlo) / ncell
        cells = [(i, 1 + rlo + i*h, 1 + rlo + (i+1)*h) for i in range(ncell)]
    nproc = int(os.environ.get("ENCL_PROCS", "7"))
    print(f"gamma {gam}, cells {[(float(c[1]-1), float(c[2]-1)) for c in cells]}, grid {NA} (x{NS} in the derivative pass), D = 1e15", flush=True)
    t0 = time.time()
    with Pool(min(nproc, len(cells))) as pool:
        for ic, L, r, widths, dt in pool.imap_unordered(run_cell, cells):
            Ra, Rb = cells[ic][1], cells[ic][2]
            t1 = time.time()
            Bd, ebar = deriv_bound(L, r, Ra, Rb)
            Dp = alpha / ((1 - alpha) * (Rb - 1 + delta)**2)               # |D'| at the cell's top rate
            print(f"cell {ic} [{float(Ra-1):.5f},{float(Rb-1):.5f}]: enclosure {dt:.0f}s (widths a<=10 at stage 59: {widths[58]:.2e}); "
                  f"derivative recursion {time.time()-t1:.0f}s: B_d = {float(Bd):.4f}  |D'| = {float(Dp):.2f}  "
                  f"-> {'E\' > 0 CERTIFIED on the cell' if Bd < Dp else 'not certified'}; "
                  f"ebar by age 1/2/5/10/30/59/60: " + " ".join(f"{float(ebar[j-1]):.4f}" for j in (1,2,5,10,30,59,60)), flush=True)
    print(f"total {time.time()-t0:.0f}s", flush=True)

if __name__ == "__main__":
    main()
