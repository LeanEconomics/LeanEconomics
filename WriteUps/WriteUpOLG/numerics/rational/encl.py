"""Rigorous enclosure of the life-cycle consumption functions at two rates, and the increment
certificate.  gamma = 3.  Every quantity is an integer over D = 10**15 and every operation rounds
OUTWARD, so [lo, hi] is a true enclosure of the stage consumption c_k(a, z; R) at every grid point,
extended between grid points by monotonicity and concavity of c in a (both proved lemmas).

Soundness of a step (what the Lean theorem would say).  With Psi_k(a') = [beta R sum_z' pi(z,z')
c_k(a',z')^{-g}]^{-1/g}, the stage-(k+1) consumption at (a, z) with m = y_z + R a is
    c = m                      if Psi_k(0) >= m            (corner: Euler under the cap)
    c = c*, c* = Psi_k(m - c*) otherwise                   (interior: both Euler inequalities),
Psi_k increasing in a' and in c_k.  If Psi^lo <= Psi <= Psi^hi pointwise then
    c_L <= Psi^lo(m - c_L)  ==>  c_L <= c*,      c_H >= Psi^hi(m - c_H)  ==>  c_H >= c*,
because c |-> Psi(m - c) - c is strictly decreasing.  Hence lo = min(m, c_L), hi = min(m, c_H).
Formalised: LeanEconomics/OLG/IntervalEuler.lean -- le_stageConsumption_of_cert,
stageConsumption_le_of_cert, stageConsumption_eq_resources_of_cert (the corner test), and
le_of_chord / le_of_left_secant / le_of_right_secant for the bounds between grid points (enc_c).

The certificate then bounds the failure of Theorem 1 at every age and earnings state,
    V_j(z) <= max_i ( hi_2(a_{i+1}) - lo_1(a_i) - dr a_i )^+     over grid intervals in the reach,
mass-weights it by the invariant law nu (exact), and runs the increment envelope
    e_1 = 0, e_{j+1} = L_j e_j + ebar_j,  L_j = (1 - kappa_{J-j}(R2)) R2,   B = mean_j e_j,
which must be below the budget D(r1) - D(r2).
"""
from fractions import Fraction as F
from math import comb
import sys, time, bisect

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
beta, R1, R2, rho = F(24,25), F(26,25), F(53,50), F(9,10)
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
budget = alpha/((1-alpha)*(R1-1+delta)) - alpha/((1-alpha)*(R2-1+delta))
dr = R2 - R1

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

def enc_c(lo, hi, zp, ap, want_low, R=None, corner=None):
    """rigorous bound on c_k(ap, zp) from the grid enclosures, by monotonicity and concavity, and
    by the certified corner region [0, astar_lo] where c = m exactly."""
    if ap <= 0: ap = 0
    if corner is not None and ap < corner[zp]:          # certified for a < corner (corner 0: nothing)
        return m_of(R, zp, ap, not want_low)
    i = bisect.bisect_right(grid, ap) - 1
    if i >= NA - 1:                                            # beyond the grid: valid but loose
        return lo[zp][NA-1] if want_low else m_of(R, zp, ap, True)
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

def psi(lo, hi, R, z, ap, want_low, corner=None):
    """Psi^lo (want_low) or Psi^hi at stage k from the stage-k enclosures."""
    bR = beta * R
    S = 0
    for zp in range(nz):
        if Pi[z][zp] == 0: continue
        c = enc_c(lo, hi, zp, ap, want_low, R, corner)               # low c for Psi^lo (bigger sum), high c for Psi^hi
        v = pow_neg3(c, hi=want_low)                       # round up for Psi^lo
        p = Pi[z][zp]
        S += up(v * p.numerator, p.denominator) if want_low else dn(v * p.numerator, p.denominator)
    S = up(S * bR.numerator, bR.denominator) if want_low else dn(S * bR.numerator, bR.denominator)
    if S <= 0:                                             # only possible when rounding down (Psi^hi)
        assert not want_low
        return 10**6 * D                                   # +infinity for our purposes: c <= m anyway
    return root_neg3(S, hi=not want_low)                   # Psi^lo rounded down, Psi^hi rounded up

def float_candidates(lo, hi, R, corner=None):
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

def step(lo, hi, R, corner=None):
    """one rigorous stage step: from stage-k enclosures (+ certified corner) to stage k+1."""
    cand = float_candidates(lo, hi, R, corner)
    newcorner = [0]*nz
    nlo = [[0]*NA for _ in range(nz)]; nhi = [[0]*NA for _ in range(nz)]
    Ra = [q2i(R * F(g, D), False) for g in grid], [q2i(R * F(g, D), True) for g in grid]
    yz = [(q2i(v, False), q2i(v, True)) for v in y]
    stats_fallback = 0
    for z in range(nz):
        psi0_lo = psi(lo, hi, R, z, 0, True, corner); psi0_hi = psi(lo, hi, R, z, 0, False, corner)
        # corner certified for a <= astar: y_up + R a <= psi0_lo  (m_up(a) <= psi0_lo)
        yu = q2i(y[z], True)
        newcorner[z] = dn((psi0_lo - yu) * R.denominator, R.numerator) + 1 if psi0_lo >= yu else 0
        for i in range(NA):
            m_dn = yz[z][0] + Ra[0][i]; m_up = yz[z][1] + Ra[1][i]
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
                    g = psi(lo, hi, R, z, m_dn - t, True, corner)
                    if t <= g: cL = t; break
                    t = g
                    if t <= 0: t = 1
                if cL is None:                                   # rigorous bisection fallback
                    stats_fallback += 1
                    L_, H_ = 1, m_dn - 1
                    while H_ - L_ > D // 10**9:
                        M_ = (L_ + H_) // 2
                        if M_ <= psi(lo, hi, R, z, m_dn - M_, True, corner): L_ = M_
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
                    h = psi(lo, hi, R, z, m_up - t, False, corner)
                    if t >= h: cH = t; break
                    t = h
                if cH is None:
                    stats_fallback += 1
                    L_, H_ = 1, m_up
                    while H_ - L_ > D // 10**9:
                        M_ = (L_ + H_) // 2
                        if M_ >= psi(lo, hi, R, z, m_up - M_, False, corner): H_ = M_
                        else: L_ = M_
                    cH = H_
            nlo[z][i] = min(m_dn, cL); nhi[z][i] = min(m_up, cH)
            assert nlo[z][i] <= nhi[z][i]
    return nlo, nhi, stats_fallback, newcorner

def terminal(R):
    lo = [[0]*NA for _ in range(nz)]; hi = [[0]*NA for _ in range(nz)]
    for z in range(nz):
        for i in range(NA):
            lo[z][i] = q2i(y[z] + R * F(grid[i], D), False); hi[z][i] = q2i(y[z] + R * F(grid[i], D), True)
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

def main():
    t0 = time.time()
    lo1, hi1 = terminal(R1); lo2, hi2 = terminal(R2); c1 = None; c2 = None
    L1 = [(lo1, hi1, c1)]; L2 = [(lo2, hi2, c2)]
    for k in range(1, J):
        lo1, hi1, f1, c1 = step(lo1, hi1, R1, c1); lo2, hi2, f2, c2 = step(lo2, hi2, R2, c2)
        L1.append((lo1, hi1, c1)); L2.append((lo2, hi2, c2))
        w1 = max(hi1[z][i] - lo1[z][i] for z in range(nz) for i in range(NA) if grid[i] <= 10*D)
        w2 = max(hi2[z][i] - lo2[z][i] for z in range(nz) for i in range(NA) if grid[i] <= 10*D)
        print(f"stage {k:2d}: max width on a<=10  R1 {w1/D:.3e}  R2 {w2/D:.3e}   fallbacks {f1}+{f2}   {time.time()-t0:6.0f}s", flush=True)
    # ---- reach (upper bound on assets by age), R1 economy and R2 economy
    def reach_seq(Lx, R):
        r = [0]
        for j in range(1, J):
            k = J - j; lo, hi, cc = Lx[k]
            best = 0
            for z in range(nz):
                g = q2i(y[z] + R * F(r[-1], D), True) - enc_c(lo, hi, z, r[-1], True, R, cc)
                best = max(best, g)
            r.append(max(best, 0))
        return r
    rr1 = reach_seq(L1, R1); rr2 = reach_seq(L2, R2)
    reach = [max(a_, b_) for a_, b_ in zip(rr1, rr2)]
    print("reach (max over the two economies) at ages 1,10,30,60:", [reach[j-1]/D for j in (1,10,30,60)])
    # ---- failure bound per age and state, mass-weighted
    ebar = []
    dr_n, dr_d = dr.numerator, dr.denominator
    for j in range(1, J+1):
        k = J - j; lo1, hi1, _ = L1[k]; lo2, hi2, _ = L2[k]
        tot = 0
        for z in range(nz):
            V = 0
            for i in range(NA - 1):
                if grid[i] > reach[j-1]: break
                v = hi2[z][i+1] - lo1[z][i] - dn(grid[i] * dr_n, dr_d)
                if v > V: V = v
            tot += up(V * nu[z].numerator, nu[z].denominator)
        ebar.append(tot)
    # ---- envelope
    kap2 = kappa_lower(R2)
    e = 0; total = 0; emax = 0
    for j in range(1, J+1):
        total += e
        if j < J:
            Lj_up = up((D - kap2[J - j]) * R2.numerator, R2.denominator)        # (1 - kappa_{J-j}) R2, rounded up
            e = up(e * Lj_up, D) + ebar[j-1]
        emax = max(emax, e)
    B = F(up(total, J), D)
    print(f"ebar_j (mean over ages) = {sum(ebar)/J/D:.5f}, max = {max(ebar)/D:.5f}, ages with ebar>0: {sum(1 for v in ebar if v>0)}")
    print(f"B = {float(B):.5f}   budget = {float(budget):.5f}   ->  {'CERTIFIED' if B < budget else 'NOT certified'}   ({time.time()-t0:.0f}s)")
    for j in (1, 2, 5, 10, 20, 30, 40, 50, 59, 60):
        print(f"   age {j:2d}: ebar {ebar[j-1]/D:.5f}")

if __name__ == "__main__":
    main()
