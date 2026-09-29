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



def run_cell(args):
    ic, Ra, Rb = args
    RR = (Ra, Rb)
    t0 = time.time()
    import pickle
    cache = f"cache_{os.environ.get('ENCL_FINE','')}g{gam}_{Ra.numerator}_{Ra.denominator}_{Rb.numerator}_{Rb.denominator}.pkl"
    if os.environ.get("ENCL_NOCACHE"):
        cache = None
    if cache is not None and os.path.exists(cache):
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
    if cache is not None:
        with open(cache, "wb") as fh:
            pickle.dump((L, r, widths), fh)
    return ic, L, r, widths, time.time() - t0

NS = int(sys.argv[5]) if len(sys.argv) > 5 else 1      # sub-intervals per grid interval in the derivative pass
MU = len(sys.argv) > 6 and sys.argv[6] == 'mu'         # carry the recursion in marginal utility
CRUDE = False                                          # set by the bootstrap for its first, robust pass


def stage_pass(lo_k, hi_k, cor_k, lo1, hi1, cor1, U, Lw, k, reach, Ra, Rb, fgrid, ai, y_dn, y_up, crude=False, cap_by_m=False, kap=None):
    """one stage of the interval derivative recursion: bounds (Un, Ln) on dc_{k+1}/dr on every grid
    interval, and the failure En, from the stage-k data (lo_k, hi_k, cor_k, U, Lw) and the stage-(k+1)
    consumption data (lo1, hi1, cor1).  With cap_by_m the stage-(k+1) consumption is bounded only by the
    propensity floor and cash on hand (no enclosure needed), for a first pass whose result seeds the
    transported enclosure."""
    global CRUDE
    RR = (Ra, Rb); gF = F(gam); NI = len(fgrid) - 1
    CRUDE_saved = CRUDE; CRUDE = crude
    Un = [[None]*NI for _ in range(nz)]; Ln = [[None]*NI for _ in range(nz)]; En = [[None]*NI for _ in range(nz)]
    for z in range(nz):
        for i in range(NI):
            a_lo, a_hi = ai[i], ai[i+1]
            if cor1 is not None and fgrid[i+1] <= cor1[z]:           # whole interval in the corner region
                Un[z][i] = a_hi; Ln[z][i] = a_lo; En[z][i] = F(0); continue
            m_dn_i = y_dn[z] + q2i(Ra * F(fgrid[i], D), False)
            m_up_i1 = y_up[z] + q2i(Rb * F(fgrid[i+1], D), True)
            if cap_by_m:                                                  # c in [kappa m, m]: no enclosure needed
                m_dn_i1 = y_dn[z] + q2i(Ra * F(fgrid[i+1], D), False)
                cl_i = dn(kap[k+1] * m_dn_i, D); ch_i = y_up[z] + q2i(Rb * F(fgrid[i], D), True)
                cl_i1 = dn(kap[k+1] * m_dn_i1, D); ch_i1 = m_up_i1
            else:
                cl_i = enc_c(lo1, hi1, z, fgrid[i], True, RR, cor1); ch_i = enc_c(lo1, hi1, z, fgrid[i], False, RR, cor1)
                cl_i1 = enc_c(lo1, hi1, z, fgrid[i+1], True, RR, cor1); ch_i1 = enc_c(lo1, hi1, z, fgrid[i+1], False, RR, cor1)
            c_lo = F(cl_i, D); c_hi = F(ch_i1, D)
            if c_lo <= 0:                                                # no information on this stage's consumption here
                if fgrid[i] <= reach[J-k-2]:
                    raise RuntimeError(f"zero consumption bound inside the reach: stage {k+1}, z {z}, a_i {fgrid[i]/D:.3f}")
                Un[z][i] = None; Ln[z][i] = None; En[z][i] = None; continue
            x_lo = max(0, m_dn_i - ch_i); x_hi = max(0, m_up_i1 - cl_i1)
            i1 = bisect.bisect_right(fgrid, x_lo) - 1; i2 = bisect.bisect_right(fgrid, x_hi) - 1
            i1 = min(max(i1, 0), NI-1); i2 = min(max(i2, 0), NI-1)
            if x_hi >= grid[NA-1]:                                       # saving beyond the grid top
                if fgrid[i] <= reach[J-k-2]:
                    raise RuntimeError(f"saving range leaves the grid: stage {k+1}, z {z}, a_i {fgrid[i]/D:.3f}")
                Un[z][i] = None; Ln[z][i] = None; En[z][i] = None; continue
            vup = -c_lo / (gF * Rb); vlo = -c_hi / (gF * Ra); Wsum = F(0); bad = False
            Wlo_cr = F(0); Ucr = None; Lcr = None
            for zp in range(nz):
                p = Pi[z][zp]
                if p == 0: continue
                ck_lo = F(enc_c(lo_k, hi_k, zp, x_lo, True, RR, cor_k), D)
                ck_hi = F(enc_c(lo_k, hi_k, zp, x_hi, False, RR, cor_k), D)
                if ck_lo <= 0:                                             # no information there (transport fallback)
                    if fgrid[i] <= reach[J-k-2]:
                        raise RuntimeError(f"zero lower bound inside the reach: stage {k+1}, z {z}, a_i {fgrid[i]/D:.3f}")
                    bad = True; break
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
                Wlo_cr += w_lo
                Ucr = Umax if Ucr is None else max(Ucr, Umax); Lcr = Lmin if Lcr is None else min(Lcr, Lmin)
            if bad:
                Un[z][i] = None; Ln[z][i] = None; En[z][i] = None; continue
            if CRUDE:                                                  # A max U instead of the weighted sum
                vup = -c_lo / (gF * Rb) + Wsum * max(Ucr, 0) + Wlo_cr * min(Ucr, 0)
                vlo = -c_hi / (gF * Ra) + Wsum * min(Lcr, 0) + Wlo_cr * max(Lcr, 0)
            Pmax = Wsum * Rb                                           # Psi_x in [0, (sum w) R]
            u = max(vup, (vup + Pmax * a_hi) / (1 + Pmax))
            l = min(vlo, (vlo + Pmax * a_lo) / (1 + Pmax))
            if x_lo <= 0 or (cor1 is not None and fgrid[i] < cor1[z]):  # possibly constrained: dc/dr = a there
                u = max(u, a_hi); l = min(l, a_lo)
            u = F(up(u.numerator * D, u.denominator), D)               # outward rounding keeps the
            l = F(dn(l.numerator * D, l.denominator), D)               # denominators bounded
            Un[z][i] = u; Ln[z][i] = l; En[z][i] = max(F(0), u - a_lo)
    CRUDE = CRUDE_saved
    return Un, Ln, En

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
    UL = [(U, Lw)]                                                # per-stage derivative bounds, for transport
    y_dn = [q2i(v, False) for v in y]; y_up = [q2i(v, True) for v in y]
    for k in range(0, J-1):
        lo_k, hi_k, cor_k = L[k]; lo1, hi1, cor1 = L[k+1]
        Un, Ln, En = stage_pass(lo_k, hi_k, cor_k, lo1, hi1, cor1, U, Lw, k, reach, Ra, Rb, fgrid, ai, y_dn, y_up, CRUDE)
        U, Lw = Un, Ln; E[k+1] = En
        UL.append((Un, Ln))
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
    return total / J, ebar, UL, fgrid


def deriv_bound_mu(L, reach, Ra, Rb):
    """The same recursion carried in MARGINAL UTILITY.  With mu = c^{-g} and D_k = d mu_k / dr,
        D_{k+1} = [ c^{-g}/R - g c^{-g-1} Psi_x a + beta R sum_z' pi D_k(x, z') ] / (1 + Psi_x),
    the propagation weights are the exact beta R pi(z,z') -- no power of consumption -- so enclosure
    error enters only the source term (additively) and the max of D_k over the saving range.  The
    consumption derivative is dc/dr = -D c^{g+1}/g, converted once per stage for the failure bound.
    Psi_x = sum w d_x c_k lies in [kappa_k R sum w_lo, R sum w_hi] by the propensity floor
    (stageMPC_mul_le_stageConsumption_sub) and monotone saving."""
    RR = (Ra, Rb)
    gF = F(gam)
    fgrid = []
    for i in range(NA - 1):
        for t in range(NS):
            fgrid.append(grid[i] + (grid[i+1] - grid[i]) * t // NS)
    fgrid.append(grid[NA-1])
    NF = len(fgrid); NI = NF - 1
    ai = [F(g, D) for g in fgrid]
    y_dn = [q2i(v, False) for v in y]; y_up = [q2i(v, True) for v in y]
    kap = kappa_lower(Ra)
    def rnd_hi(v): return F(up(v.numerator * D, v.denominator), D)
    def rnd_lo(v): return F(dn(v.numerator * D, v.denominator), D)
    def corner_D(z, i):
        m_lo = F(y_dn[z] + q2i(Ra * F(fgrid[i], D), False), D); m_hi = F(y_up[z] + q2i(Rb * F(fgrid[i+1], D), True), D)
        return (-gF * ai[i+1] / m_lo**(gam+1), -gF * ai[i] / m_hi**(gam+1))      # (lo, hi)
    Dhi = [[None]*NI for _ in range(nz)]; Dlo = [[None]*NI for _ in range(nz)]
    for z in range(nz):
        for i in range(NI):
            l, h = corner_D(z, i); Dlo[z][i] = rnd_lo(l); Dhi[z][i] = rnd_hi(h)
    E = [None] * J
    E[0] = [[F(0)] * NI for _ in range(nz)]
    for k in range(0, J-1):
        lo_k, hi_k, cor_k = L[k]; lo1, hi1, cor1 = L[k+1]
        s_lo = F(kap[k], D) * Ra; s_hi = Rb
        Dhn = [[None]*NI for _ in range(nz)]; Dln = [[None]*NI for _ in range(nz)]; En = [[None]*NI for _ in range(nz)]
        for z in range(nz):
            for i in range(NI):
                a_lo, a_hi = ai[i], ai[i+1]
                if cor1 is not None and fgrid[i+1] <= cor1[z]:
                    l, h = corner_D(z, i); Dln[z][i] = rnd_lo(l); Dhn[z][i] = rnd_hi(h); En[z][i] = F(0); continue
                cl_i = enc_c(lo1, hi1, z, fgrid[i], True, RR, cor1); ch_i = enc_c(lo1, hi1, z, fgrid[i], False, RR, cor1)
                cl_i1 = enc_c(lo1, hi1, z, fgrid[i+1], True, RR, cor1); ch_i1 = enc_c(lo1, hi1, z, fgrid[i+1], False, RR, cor1)
                c_lo = F(cl_i, D); c_hi = F(ch_i1, D)
                m_dn_i = y_dn[z] + q2i(Ra * F(fgrid[i], D), False)
                m_up_i1 = y_up[z] + q2i(Rb * F(fgrid[i+1], D), True)
                x_lo = max(0, m_dn_i - ch_i); x_hi = max(0, m_up_i1 - cl_i1)
                if x_hi >= grid[NA-1]:
                    if fgrid[i] <= reach[J-k-2]:
                        raise RuntimeError(f"saving range leaves the grid: stage {k+1}, z {z}, a_i {fgrid[i]/D:.3f}")
                    Dhn[z][i] = None; Dln[z][i] = None; En[z][i] = None; continue
                i1 = bisect.bisect_right(fgrid, x_lo) - 1; i2 = bisect.bisect_right(fgrid, x_hi) - 1
                i1 = min(max(i1, 0), NI-1); i2 = min(max(i2, 0), NI-1)
                Wlo = F(0); Whi = F(0); Phi = F(0); Plo = F(0); bad = False
                for zp in range(nz):
                    p = Pi[z][zp]
                    if p == 0: continue
                    ck_lo = F(enc_c(lo_k, hi_k, zp, x_lo, True, RR, cor_k), D)
                    ck_hi = F(enc_c(lo_k, hi_k, zp, x_hi, False, RR, cor_k), D)
                    assert ck_lo > 0
                    Wlo += beta * Ra * p * c_lo**(gam+1) / ck_hi**(gam+1)
                    Whi += beta * Rb * p * c_hi**(gam+1) / ck_lo**(gam+1)
                    segh = Dhi[zp][i1:i2+1]; segl = Dlo[zp][i1:i2+1]
                    if None in segh or None in segl:
                        if fgrid[i] <= reach[J-k-2]:
                            raise RuntimeError(f"derivative bound read outside its validity: stage {k+1}, z {z}, a_i {fgrid[i]/D:.3f}")
                        bad = True; break
                    dh = max(segh); dl = min(segl)
                    Phi += beta * (Rb if dh > 0 else Ra) * p * dh
                    Plo += beta * (Ra if dl > 0 else Rb) * p * dl
                if bad:
                    Dhn[z][i] = None; Dln[z][i] = None; En[z][i] = None; continue
                Ps_lo = s_lo * Wlo; Ps_hi = s_hi * Whi
                S_hi = c_lo**(-gam) / Ra - gF * Ps_lo * a_lo / c_hi**(gam+1)
                S_lo = c_hi**(-gam) / Rb - gF * Ps_hi * a_hi / c_lo**(gam+1)
                N_hi = S_hi + Phi; N_lo = S_lo + Plo
                dhi = N_hi / (1 + Ps_lo) if N_hi > 0 else N_hi / (1 + Ps_hi)
                dlo = N_lo / (1 + Ps_hi) if N_lo > 0 else N_lo / (1 + Ps_lo)
                if cor1 is not None and fgrid[i] < cor1[z]:
                    l, h = corner_D(z, i); dlo = min(dlo, l); dhi = max(dhi, h)
                dhi = rnd_hi(dhi); dlo = rnd_lo(dlo)
                dcdr_hi = (-dlo) * (c_hi**(gam+1) if dlo < 0 else c_lo**(gam+1)) / gF
                Dhn[z][i] = dhi; Dln[z][i] = dlo; En[z][i] = max(F(0), dcdr_hi - a_lo)
        Dhi, Dlo = Dhn, Dln; E[k+1] = En
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
    e = F(0); total = F(0)
    for j in range(1, J+1):
        total += e
        if j < J:
            Lj = (1 - F(kap[J-j], D)) * Rb
            e = Lj * e + ebar[j-1]
    return total / J, ebar


def transport(L0, UL, half, corner_cell):
    """cell enclosure from the point enclosure L0 at the cell's midpoint and a bound |dc_k/dr| <= U on
    the cell: c(a; r) = c(a; r0) + int dc/dr, so [lo - U h/2, hi + U h/2] holds for every r in the cell.
    U at a grid point is the larger bound on the two grid intervals meeting it (the derivative pass runs
    on the grid itself here, NS = 1)."""
    out = []
    for k in range(J):
        lo0, hi0, _ = L0[k]
        Un, Ln = UL[k]
        NI = len(Un[0])
        lo = []; hi = []
        for z in range(nz):
            lz = array('q', lo0[z]); hz = array('q', hi0[z])
            for i in range(NA):
                cands = []
                for ii in (i-1, i):
                    if 0 <= ii < NI and Un[z][ii] is not None and Ln[z][ii] is not None:
                        cands.append(max(abs(Un[z][ii]), abs(Ln[z][ii])))
                if not cands:
                    lz[i] = 0; hz[i] = q2i(y[z] + F(4, 1) * F(grid[i], D), True)   # no bound: c <= m, loose but valid
                    continue
                Ub = max(cands) * half
                d = up(Ub.numerator * D, Ub.denominator)
                lz[i] = max(0, lo0[z][i] - d); hz[i] = hi0[z][i] + d
            lo.append(lz); hi.append(hz)
        out.append((lo, hi, corner_cell[k]))
    return out

def cell_bootstrap(ic, Ra, Rb, rounds=3):
    """certify E' > 0 on the cell [Ra, Rb] by bootstrapping the transport."""
    global CRUDE
    h = Rb - Ra; R0 = (Ra + Rb) / 2
    t0 = time.time()
    _, C0, reach0, w0, _ = run_cell((ic, Ra, Rb))                  # crude cell enclosure (valid on the cell)
    _, L0, reachP, wP, _ = run_cell((ic, R0, R0))                  # tight point enclosure at the midpoint
    print(f"cell {ic} [{float(Ra-1):.5f},{float(Rb-1):.5f}]: crude cell widths at stage 59 {w0[58]:.2e}, point {wP[58]:.2e}; enclosures {time.time()-t0:.0f}s", flush=True)
    corner_cell = [C0[k][2] for k in range(J)]
    CRUDE = True
    Bd, ebar, UL, fgrid = deriv_bound(C0, reach0, Ra, Rb)
    CRUDE = False
    print(f"  crude pass on the cell enclosure: B_d = {float(Bd):.2f}; {time.time()-t0:.0f}s", flush=True)
    Dp = alpha / ((1 - alpha) * (Rb - 1 + delta)**2)
    for it in range(rounds):
        C = transport(L0, UL, h / 2, corner_cell)
        w = max(C[59][1][z][i] - C[59][0][z][i] for z in range(nz) for i in range(NA) if grid[i] <= 10*D) / D
        Bd, ebar, UL, fgrid = deriv_bound(C, reach0, Ra, Rb)
        print(f"  round {it+1}: transported widths at stage 59 (a<=10) {w:.2e}; B_d = {float(Bd):.3f} vs |D'| = {float(Dp):.2f} -> {'CERTIFIED' if Bd < Dp else 'not yet'}; ebar 1/5/10/30: " + " ".join(f"{float(ebar[j-1]):.4f}" for j in (1,5,10,30)) + f"; {time.time()-t0:.0f}s", flush=True)
        if Bd < Dp: break
    return ic, bool(Bd < Dp), float(Bd), float(Dp)


def transport_stage(L0k, Un, Ln, h2, RR, C0k=None):
    """the enclosure at every grid point over the cell from the point enclosure at its midpoint and the
    derivative bounds on the two grid intervals meeting the point: c(a; r) = c(a; r0) + int dc/dr."""
    lo0, hi0, _ = L0k
    NI = len(Un[0])
    lo = []; hi = []
    for z in range(nz):
        lz = array('q', lo0[z]); hz = array('q', hi0[z])
        for i in range(NA):
            cands = [max(abs(Un[z][ii]), abs(Ln[z][ii])) for ii in (i-1, i)
                     if 0 <= ii < NI and Un[z][ii] is not None and Ln[z][ii] is not None]
            if not cands:                                            # no assumption here: the crude cell
                if C0k is not None:                                  # enclosure, valid without one
                    lz[i] = C0k[0][z][i]; hz[i] = C0k[1][z][i]
                else:
                    lz[i] = 0; hz[i] = q2i(y[z] + RR[1] * F(grid[i], D), True)
                continue
            d = (max(cands) * h2); d = up(d.numerator * D, d.denominator)
            m_up = q2i(y[z] + RR[1] * F(grid[i], D), True)
            lz[i] = max(0, lo0[z][i] - d); hz[i] = min(hi0[z][i] + d, m_up)
        lo.append(lz); hi.append(hz)
    return lo, hi

def deriv_bound_transport(L0, reachP, Ra, Rb, C0=None):
    """E' > 0 on the cell [Ra, Rb] from the point enclosure L0 at its midpoint: at each stage the
    derivative bound over the cell is seeded by the propensity floor (phase A), the cell enclosure of the
    stage is the point enclosure transported by that seed, and the bound is recomputed on it (phase B)."""
    assert NS == 1
    RR = (Ra, Rb); h2 = (Rb - Ra) / 2
    fgrid = list(grid); NI = NA - 1
    ai = [F(g, D) for g in grid]
    y_dn = [q2i(v, False) for v in y]; y_up = [q2i(v, True) for v in y]
    kap = kappa_lower(Ra)
    # the terminal stage over the cell: c = m exactly
    lo0 = [array('q', [y_dn[z] + q2i(Ra * F(g, D), False) for g in grid]) for z in range(nz)]
    hi0 = [array('q', [y_up[z] + q2i(Rb * F(g, D), True) for g in grid]) for z in range(nz)]
    C = [(lo0, hi0, None)]
    U = [[ai[i+1] for i in range(NI)] for _ in range(nz)]
    Lw = [[ai[i] for i in range(NI)] for _ in range(nz)]
    E = [[[F(0)] * NI for _ in range(nz)]]
    reach_proxy = [r + D for r in reachP]                          # provisional: the cell's reach is checked after
    t0 = time.time()
    for k in range(0, J-1):
        lo_k, hi_k, cor_k = C[k]
        if C0 is not None:                                             # seed: the crude cell enclosure's stage k+1
            UnA, LnA, _ = stage_pass(lo_k, hi_k, cor_k, C0[k+1][0], C0[k+1][1], C0[k+1][2], U, Lw, k, reach_proxy, Ra, Rb, fgrid, ai, y_dn, y_up)
        else:
            UnA, LnA, _ = stage_pass(lo_k, hi_k, cor_k, None, None, None, U, Lw, k, reach_proxy, Ra, Rb, fgrid, ai, y_dn, y_up, crude=True, cap_by_m=True, kap=kap)
        # the cell's certified corner at stage k+1: y_up + Rb a <= Psi^lo(0) from the stage-k cell data
        cor1 = []
        for z in range(nz):
            p0 = psi(lo_k, hi_k, RR, z, 0, True, cor_k)
            cor1.append(dn((p0 - y_up[z]) * Rb.denominator, Rb.numerator) + 1 if p0 >= y_up[z] else 0)
        lo1, hi1 = transport_stage(L0[k+1], UnA, LnA, h2, RR)
        Un, Ln, En = stage_pass(lo_k, hi_k, cor_k, lo1, hi1, cor1, U, Lw, k, reach_proxy, Ra, Rb, fgrid, ai, y_dn, y_up)
        lo1, hi1 = transport_stage(L0[k+1], Un, Ln, h2, RR)
        C.append((lo1, hi1, cor1)); U, Lw = Un, Ln; E.append(En)
        if k % 10 == 9:
            w = max(hi1[z][i] - lo1[z][i] for z in range(nz) for i in range(NA) if grid[i] <= 10*D) / D
            print(f"    stage {k+1}: cell widths on a<=10 {w:.2e}; {time.time()-t0:.0f}s", flush=True)
    # the reach over the cell, from the transported enclosures
    r = [0]
    for j in range(1, J):
        kk = J - j; lo_, hi_, cc_ = C[kk]
        best = 0
        for z in range(nz):
            g = q2i(y[z] + Rb * F(r[-1], D), True) - enc_c(lo_, hi_, z, r[-1], True, RR, cc_)
            best = max(best, g)
        r.append(max(best, 0))
    ebar = []
    for j in range(1, J+1):
        k1 = J - j
        tot = F(0)
        for z in range(nz):
            V = F(0)
            for i in range(NI):
                if grid[i] > r[j-1]: break
                if E[k1][z][i] is None:
                    raise RuntimeError(f"no derivative bound inside the cell's reach: age {j}, z {z}, a {grid[i]/D:.3f}")
                if E[k1][z][i] > V: V = E[k1][z][i]
            tot += nu[z] * V
        ebar.append(tot)
    e = F(0); total = F(0)
    for j in range(1, J+1):
        total += e
        if j < J:
            Lj = (1 - F(kap[J-j], D)) * Rb
            e = Lj * e + ebar[j-1]
    return total / J, ebar, r


def deriv_bound_fixed(L0, UL0, reachP, Ra, Rb, lam, C0=None):
    """E' > 0 on the cell [Ra, Rb] with the transport FROZEN at lam times the midpoint's own derivative
    bound and verified afterwards.  Assume |dc_k/dr| <= M_k := lam * U0_k on the cell; then the cell
    enclosure is C_k = L0_k -+ M_k h/2, the derivative pass on the C_k gives U_k, and if U_k < M_k
    strictly on every interval that carries an assumption, the assumption holds on the whole cell: the
    set of rates at which every C_k holds is closed, contains the midpoint, and by the bound U_k < M_k
    and continuity of c in r is open in the cell as well (a continuation argument).  No feedback."""
    assert NS == 1
    RR = (Ra, Rb); h2 = (Rb - Ra) / 2
    fgrid = list(grid); NI = NA - 1
    ai = [F(g, D) for g in grid]
    y_dn = [q2i(v, False) for v in y]; y_up = [q2i(v, True) for v in y]
    kap = kappa_lower(Ra)
    lamF = F(lam); muF = F(MU_FLOOR)
    # the derivative bound at stage k and wealth a only matters inside a zone Z_k closed under reading:
    # an interval at (k+1, a') reads stage-k values at the saving x <= (1 - kappa_{k+1})(y_max + R a')
    # (propensity floor), and the failure is evaluated inside the age's reach; so
    #   Z_{J-1} = reach + margin,  Z_k = max(reach_age + margin, (1 - kappa_{k+1})(y_max + R Z_{k+1})),
    # which stays bounded (about 330) because (1 - kappa) R < 1.  Assumptions and their verification are
    # confined to a <= Z_k; above, the crude cell enclosure stands in and is never read from the zone.
    ymax_up = max(y_up)
    Zk = [None] * J
    for k in range(J - 1, -1, -1):
        zr = int(F(reachP[J - 1 - k], 1) * F(6, 5)) + 2 * D
        if k < J - 1:
            nxt = (1 - F(kap[k+1], D)) * (F(ymax_up, D) + Rb * F(Zk[k+1], D))
            zn = up(nxt.numerator * D, nxt.denominator) + D
            zr = max(zr, zn)
        Zk[k] = zr
    print(f"    assumption zone: stage 0 {Zk[0]/D:.1f}, stage 30 {Zk[30]/D:.1f}, stage 59 {Zk[59]/D:.1f}", flush=True)
    def scaled(UL, k):
        # M = lam * max(|U0|, |L0|, a_hi) + mu: the assumed bound covers the constrained case dc/dr = a on
        # every interval (the cell pass may find saving non-positive where the point pass did not), and an
        # absolute floor mu keeps tiny point bounds from failing the ratio test
        Un, Ln = UL
        Mu = [[None]*len(Un[0]) for _ in range(nz)]; Ml = [[None]*len(Un[0]) for _ in range(nz)]
        for z in range(nz):
            for i in range(len(Un[0])):
                if Un[z][i] is None or Ln[z][i] is None: continue
                if grid[i] > min(ASSUME_TOP * D, Zk[k]): continue      # no assumption where it is not used
                m_ = lamF * max(abs(Un[z][i]), abs(Ln[z][i])) + muF          # the floor mu covers the
                                                                             # near-corner intervals
                Mu[z][i] = m_; Ml[z][i] = -m_
        return Mu, Ml
    M = [scaled(UL0[k], k) for k in range(J)]
    reach_proxy = [r + D for r in reachP]
    t0 = time.time()
    for rnd in range(6):
        # the frozen cell enclosures and their corners
        lo0 = [array('q', [y_dn[z] + q2i(Ra * F(g, D), False) for g in grid]) for z in range(nz)]
        hi0 = [array('q', [y_up[z] + q2i(Rb * F(g, D), True) for g in grid]) for z in range(nz)]
        C = [(lo0, hi0, None)]
        for k in range(1, J):
            lo_k, hi_k = transport_stage(L0[k], M[k][0], M[k][1], h2, RR, None if C0 is None else C0[k])
            lo_p, hi_p, cor_p = C[k-1]
            cor = []
            for z in range(nz):
                p0 = psi(lo_p, hi_p, RR, z, 0, True, cor_p)
                cor.append(dn((p0 - y_up[z]) * Rb.denominator, Rb.numerator) + 1 if p0 >= y_up[z] else 0)
            C.append((lo_k, hi_k, cor))
        # the derivative pass on the frozen enclosures
        U = [[ai[i+1] for i in range(NI)] for _ in range(nz)]
        Lw = [[ai[i] for i in range(NI)] for _ in range(nz)]
        E = [[[F(0)] * NI for _ in range(nz)]]
        ULc = [(U, Lw)]
        for k in range(0, J-1):
            lo_k, hi_k, cor_k = C[k]; lo1, hi1, cor1 = C[k+1]
            Un, Ln, En = stage_pass(lo_k, hi_k, cor_k, lo1, hi1, cor1, U, Lw, k, reach_proxy, Ra, Rb, fgrid, ai, y_dn, y_up)
            U, Lw = Un, Ln; E.append(En); ULc.append((Un, Ln))
        # verification: U < M wherever an assumption was made; drop assumptions the pass could not check
        worst = F(0); nbad = 0; ndrop = 0
        for k in range(1, J):
            Mu, Ml = M[k]; Un, Ln = ULc[k]
            # where the pass gives no bound the assumption is unverifiable: drop it, and with it every
            # assumption at that stage from ten percent below (the zone creeps inward by four percent a
            # round, so this converges in a couple of rounds instead of a dozen)
            for z in range(nz):
                for i in range(NI):
                    if Mu[z][i] is None: continue
                    if Un[z][i] is None:
                        Mu[z][i] = None; Ml[z][i] = None; ndrop += 1; continue
                    m_ = max(abs(Mu[z][i]), abs(Ml[z][i])); u_ = max(abs(Un[z][i]), abs(Ln[z][i]))
                    if m_ == 0:
                        if u_ > 0: nbad += 1
                        continue
                    ratio = u_ / m_
                    if ratio >= 1:
                        nbad += 1
                        if nbad <= 5: print(f"      violation: stage {k}, z {z}, a {grid[i]/D:.4f}, U0-based M {float(m_):.4f}, cell U {float(u_):.4f}, cell L {float(Ln[z][i]):.4f}", flush=True)
                    if ratio > worst: worst = ratio
        print(f"    round {rnd+1}: max U/M = {float(worst):.3f}, violations {nbad}, assumptions dropped {ndrop}; {time.time()-t0:.0f}s", flush=True)
        if nbad == 0 and ndrop == 0: break
        if nbad > 0: return None, None, None, float(worst)
    if nbad > 0 or ndrop > 0:
        return None, None, None, float(worst)
    # certified: the reach over the cell and the failure bound
    r = [0]
    for j in range(1, J):
        kk = J - j; lo_, hi_, cc_ = C[kk]
        best = 0
        for z in range(nz):
            g = q2i(y[z] + Rb * F(r[-1], D), True) - enc_c(lo_, hi_, z, r[-1], True, RR, cc_)
            best = max(best, g)
        r.append(max(best, 0))
    ebar = []
    for j in range(1, J+1):
        k1 = J - j
        tot = F(0)
        for z in range(nz):
            V = F(0)
            for i in range(NI):
                if grid[i] > r[j-1]: break
                if E[k1][z][i] is None:
                    raise RuntimeError(f"no derivative bound inside the cell's reach: age {j}, z {z}, a {grid[i]/D:.3f}")
                if E[k1][z][i] > V: V = E[k1][z][i]
            tot += nu[z] * V
        ebar.append(tot)
    e = F(0); total = F(0)
    for j in range(1, J+1):
        total += e
        if j < J:
            Lj = (1 - F(kap[J-j], D)) * Rb
            e = Lj * e + ebar[j-1]
    return total / J, ebar, r, float(worst)

def _cell_star(c):
    return cell_certify_fixed(*c)

def cell_certify_fixed(ic, Ra, Rb):
    R0 = (Ra + Rb) / 2
    t0 = time.time()
    _, L0, reachP, wP, dt = run_cell((ic, R0, R0))
    C0 = None                                                        # the fallback above the zone is never read
    if os.environ.get("ENCL_CRUDE"):
        _, C0, reach0, w0, dt0 = run_cell((ic, Ra, Rb))
    Bd0, ebar0, UL0, _ = deriv_bound(L0, reachP, R0, R0)
    Dp = alpha / ((1 - alpha) * (Rb - 1 + delta)**2)
    print(f"cell {ic} [{float(Ra-1):.5f},{float(Rb-1):.5f}]: point enclosure {dt:.0f}s, point B_d = {float(Bd0):.3f}; {time.time()-t0:.0f}s", flush=True)
    for lam in LAMS:
        Bd, ebar, rc, worst = deriv_bound_fixed(L0, UL0, reachP, Ra, Rb, lam, C0)
        if Bd is None:
            print(f"  lambda {lam}: assumption not verified (max U/M {worst:.3f}); {time.time()-t0:.0f}s", flush=True)
            continue
        print(f"  lambda {lam}: verified (max U/M {worst:.3f}); B_d = {float(Bd):.3f} vs |D'| = {float(Dp):.2f} -> {'CERTIFIED' if Bd < Dp else 'NOT'}; ebar 1/2/5/10/30: " + " ".join(f"{float(ebar[j-1]):.4f}" for j in (1,2,5,10,30)) + f"; {time.time()-t0:.0f}s", flush=True)
        return ic, bool(Bd < Dp), float(Bd), float(Dp)
    return ic, False, float('inf'), float(Dp)

LAMS = [int(v) for v in os.environ.get("ENCL_LAMS", "2,4,8").split(",")]
MU_FLOOR = F(os.environ.get("ENCL_MU", "1/50"))
ASSUME_TOP = int(os.environ.get("ENCL_ASSUME_TOP", "1500"))   # assumptions only below this wealth

def cell_certify(ic, Ra, Rb):
    R0 = (Ra + Rb) / 2
    t0 = time.time()
    _, L0, reachP, wP, dt = run_cell((ic, R0, R0))
    _, C0, reach0, w0, dt0 = run_cell((ic, Ra, Rb))                  # crude cell enclosure, the seed
    Bd, ebar, rc = deriv_bound_transport(L0, reachP, Ra, Rb, C0)
    Dp = alpha / ((1 - alpha) * (Rb - 1 + delta)**2)
    print(f"cell {ic} [{float(Ra-1):.5f},{float(Rb-1):.5f}]: point enclosure {dt:.0f}s (width at stage 59 {wP[58]:.2e}); B_d = {float(Bd):.3f} vs |D'| = {float(Dp):.2f} -> {'CERTIFIED' if Bd < Dp else 'NOT'}; ebar 1/2/5/10/30: " + " ".join(f"{float(ebar[j-1]):.4f}" for j in (1,2,5,10,30)) + f"; reach 10/30/60: {rc[9]/D:.1f} {rc[29]/D:.1f} {rc[59]/D:.1f}; {time.time()-t0:.0f}s", flush=True)
    return ic, bool(Bd < Dp), float(Bd), float(Dp)

def main():
    rlo, rhi, ncell = F(sys.argv[2]), F(sys.argv[3]), int(sys.argv[4])
    if len(sys.argv) > 6 and sys.argv[6] == 'fixed':
        assert NS == 1
        h = (rhi - rlo) / ncell
        cells = [(i, 1 + rlo + i*h, 1 + rlo + (i+1)*h) for i in range(ncell)]
        nproc = int(os.environ.get("ENCL_PROCS", "7"))
        print(f"gamma {gam}, frozen-transport cells: {ncell} of width {float(h):.5f} on [{float(rlo):.4f},{float(rhi):.4f}], grid {NA}, lambdas {LAMS}, mu {MU_FLOOR}", flush=True)
        t0 = time.time()
        resfile = os.environ.get("ENCL_RESULTS")                     # resumable: one line per finished cell
        done = {}
        if resfile and os.path.exists(resfile):
            for line in open(resfile):
                parts = line.split()
                if len(parts) >= 4 and parts[0] == "cell":
                    done[int(parts[1])] = parts[2] == "CERTIFIED"
        todo = [c for c in cells if c[0] not in done]
        print(f"{len(done)} cells already done, {len(todo)} to run", flush=True)
        res = list(done.items())
        with Pool(min(nproc, max(1, len(todo)))) as pool:
            for ic, ok, Bd, Dp in pool.starmap(cell_certify_fixed, todo, chunksize=1) if False else pool.imap_unordered(_cell_star, todo):
                res.append((ic, ok))
                if resfile:
                    with open(resfile, "a") as fh:
                        fh.write(f"cell {ic} {'CERTIFIED' if ok else 'NOT'} B_d {Bd:.4f} Dp {Dp:.3f} r [{float(cells[ic][1]-1):.5f},{float(cells[ic][2]-1):.5f}]\n")
        allok = all(ok for _, ok in res) and len(res) == ncell
        print(("ALL CELLS CERTIFIED: E' > 0 on the bracket" if allok else f"NOT all cells certified ({sum(1 for _, ok in res if ok)} of {ncell})") + f"; {time.time()-t0:.0f}s", flush=True)
        return
    if len(sys.argv) > 6 and sys.argv[6] == 'cells':
        assert NS == 1
        h = (rhi - rlo) / ncell
        cells = [(i, 1 + rlo + i*h, 1 + rlo + (i+1)*h) for i in range(ncell)]
        nproc = int(os.environ.get("ENCL_PROCS", "7"))
        print(f"gamma {gam}, transported cells: {ncell} of width {float(h):.5f} on [{float(rlo):.4f},{float(rhi):.4f}], grid {NA}", flush=True)
        t0 = time.time()
        with Pool(min(nproc, len(cells))) as pool:
            res = pool.starmap(cell_certify, cells)
        allok = all(ok for _, ok, _, _ in res)
        for ic, ok, Bd, Dp in sorted(res):
            print(f"  cell {ic}: B_d = {Bd:.3f} vs {Dp:.2f} {'CERTIFIED' if ok else 'NOT'}", flush=True)
        print(("ALL CELLS CERTIFIED: E' > 0 on the bracket" if allok else "NOT all cells certified") + f"; {time.time()-t0:.0f}s", flush=True)
        return
    if len(sys.argv) > 6 and sys.argv[6] == 'boot':
        assert NS == 1, "the bootstrap transports on the grid itself"
        h = (rhi - rlo) / ncell
        cells = [(i, 1 + rlo + i*h, 1 + rlo + (i+1)*h) for i in range(ncell)]
        nproc = int(os.environ.get("ENCL_PROCS", "7"))
        print(f"gamma {gam}, bootstrap over {ncell} cells of width {float(h):.5f} on [{float(rlo):.4f},{float(rhi):.4f}], grid {NA}", flush=True)
        t0 = time.time()
        with Pool(min(nproc, len(cells))) as pool:
            res = pool.starmap(cell_bootstrap, cells)
        allok = all(ok for _, ok, _, _ in res)
        for ic, ok, Bd, Dp in sorted(res):
            print(f"  cell {ic}: B_d = {Bd:.3f} vs {Dp:.2f} {'CERTIFIED' if ok else 'NOT'}", flush=True)
        print(("ALL CELLS CERTIFIED: E' > 0 on the bracket" if allok else "NOT all cells certified") + f"; {time.time()-t0:.0f}s", flush=True)
        return
    if ncell == 0:
        cells = [(0, 1 + rlo, 1 + rlo)]
    else:
        h = (rhi - rlo) / ncell
        cells = [(i, 1 + rlo + i*h, 1 + rlo + (i+1)*h) for i in range(ncell)]
    nproc = int(os.environ.get("ENCL_PROCS", "7"))
    print(f"gamma {gam}, cells {[(float(c[1]-1), float(c[2]-1)) for c in cells]}, grid {NA} (x{NS} in the derivative pass{', marginal-utility form' if MU else ''}), D = 1e15", flush=True)
    t0 = time.time()
    with Pool(min(nproc, len(cells))) as pool:
        for ic, L, r, widths, dt in pool.imap_unordered(run_cell, cells):
            Ra, Rb = cells[ic][1], cells[ic][2]
            t1 = time.time()
            out = (deriv_bound_mu if MU else deriv_bound)(L, r, Ra, Rb); Bd, ebar = out[0], out[1]
            Dp = alpha / ((1 - alpha) * (Rb - 1 + delta)**2)               # |D'| at the cell's top rate
            print(f"cell {ic} [{float(Ra-1):.5f},{float(Rb-1):.5f}]: enclosure {dt:.0f}s (widths a<=10 at stage 59: {widths[58]:.2e}); "
                  f"derivative recursion {time.time()-t1:.0f}s: B_d = {float(Bd):.4f}  |D'| = {float(Dp):.2f}  "
                  f"-> {'E\' > 0 CERTIFIED on the cell' if Bd < Dp else 'not certified'}; "
                  f"ebar by age 1/2/5/10/30/59/60: " + " ".join(f"{float(ebar[j-1]):.4f}" for j in (1,2,5,10,30,59,60)), flush=True)
    print(f"total {time.time()-t0:.0f}s", flush=True)

if __name__ == "__main__":
    main()
