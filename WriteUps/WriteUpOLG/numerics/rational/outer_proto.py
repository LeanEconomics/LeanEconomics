"""Prototype of the outer-range checker (to be replayed in Lean): rigorous interval bounds, over a cell
of rates [r1, r2], on the affine ceiling C(r) >= S(r) (valid where the cap is slack, r below the rate of
time preference) and on the clamped floor F(r) <= S(r) (valid where feasible saving stays under the cap).
Integers over D with outward rounding; Fractions only for exact comparisons.
Usage: python3 outer_proto.py ceil r_lo r_hi width | floor r_lo r_hi width"""
import sys
from fractions import Fraction as F
from math import comb
D = 10**12
def up(n, d): return -((-n) // d)
def dn(n, d): return n // d
def icbrt_dn(n):
    if n <= 0: return 0
    x = 1 << ((n.bit_length() + 2) // 3)
    while True:
        y = (2 * x + n // (x * x)) // 3
        if y >= x: break
        x = y
    while x**3 > n: x -= 1
    while (x+1)**3 <= n: x += 1
    return x
def icbrt_up(n):
    x = icbrt_dn(n); return x if x**3 == n else x + 1
nz, J = 7, 60
beta, rho = F(24, 25), F(9, 10)
alpha, delta = F(9, 25), F(2, 25)
CAP = F(10**6)
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
ymin, ymax = min(y), max(y)
y_dn = [dn(v.numerator*D, v.denominator) for v in y]; y_up = [up(v.numerator*D, v.denominator) for v in y]
def Dem(r): return alpha/((1-alpha)*(r+delta))
def q2i(x, hi): return up(x.numerator*D, x.denominator) if hi else dn(x.numerator*D, x.denominator)

def params(r1, r2):
    R1, R2 = 1 + r1, 1 + r2
    T_lo = icbrt_dn(dn((beta*R1).numerator * D**3, (beta*R1).denominator))   # (T_lo/D)^3 <= beta R1
    T_hi = icbrt_up(up((beta*R2).numerator * D**3, (beta*R2).denominator))   # (T_hi/D)^3 >= beta R2
    # kappa bounds: kappa increasing in R, decreasing in Thorn
    klo, khi = [D], [D]
    for k in range(J - 1):
        x = dn(klo[-1] * R1.numerator, R1.denominator); klo.append(dn(x * D, T_hi + x))
        x = up(khi[-1] * R2.numerator, R2.denominator); khi.append(up(x * D, T_lo + x))
    # stage human wealth: H_{k+1} = sum pi (y + H_k) / R ; decreasing in R
    Hhi = [[0]*nz]; Hlo = [[0]*nz]
    for k in range(J - 1):
        Shi = [sum(Pi[z][w] * (y_up[w] + Hhi[-1][w]) for w in range(nz)) for z in range(nz)]
        Slo = [sum(Pi[z][w] * (y_dn[w] + Hlo[-1][w]) for w in range(nz)) for z in range(nz)]
        Hhi.append([up(S.numerator * R1.denominator, S.denominator * R1.numerator) for S in Shi])
        Hlo.append([dn(S.numerator * R2.denominator, S.denominator * R2.numerator) for S in Slo])
    # cohort slope G: G_{k+1} = 1 + G_k (1 - kappa_{k+1}) R
    Ghi, Glo = [D], [D]
    for k in range(J - 1):
        Ghi.append(D + up(Ghi[-1] * (D - klo[k+1]) * R2.numerator, D * R2.denominator))
        Glo.append(D + dn(Glo[-1] * (D - khi[k+1]) * R1.numerator, D * R1.denominator))
    return R1, R2, T_lo, T_hi, klo, khi, Hhi, Hlo, Ghi, Glo

def fsum_pi(z, vals):            # exact Fraction sum_w pi(z,w) vals[w]
    return sum(Pi[z][w] * vals[w] for w in range(nz))

def ceiling_cell(r1, r2):
    R1, R2, T_lo, T_hi, klo, khi, Hhi, Hlo, Ghi, Glo = params(r1, r2)
    # slack hypothesis for ALL stages: y_max + r cap < kappa_k (y_min + R cap)/Thorn
    lhs = ymax + r2 * CAP
    kinf = 1 - F(T_hi, D) / R1
    routeA = kinf > 0 and lhs < kinf * (ymin + R1 * CAP) / F(T_hi, D)
    routeB = lhs <= 0
    # risk human wealth lower bound Hr_lo, and the ceiling intercept upper bound Fc_hi
    Hr = [[0]*nz]; Fc = [[0]*nz]
    for k in range(J - 1):
        new = []
        for z in range(nz):
            xs = [y_dn[w] + Hr[-1][w] for w in range(nz)]
            S = sum(Pi[z][w] * F(D, xs[w])**3 for w in range(nz) if Pi[z][w])   # >= sum pi x^{-3} (x over D)
            m = icbrt_dn((F(D**3) / S).numerator // (F(D**3) / S).denominator)    # m^3 S <= D^3  => m/D <= powerMean
            t1 = dn(m * R2.denominator, R2.numerator)                          # / R, R as large as possible
            t2 = dn((D - khi[k+1]) * y_dn[z], khi[k+1])                         # (1/kappa - 1) y, kappa large
            new.append(max(0, min(t1, t2)))
        Hr.append(new)
        newF = []
        for z in range(nz):
            s = fsum_pi(z, Fc[-1]); s = up(s.numerator, s.denominator)
            b = (D - klo[k+1]) * y_up[z] - klo[k+1] * Hr[-1][z]                # bracket * D^2 ... units: D*D
            G = Ghi[k] if b >= 0 else Glo[k]
            newF.append(s + up(G * b, D * D))
        Fc.append(newF)
    C = sum(nu[z] * Fc[J-1][z] for z in range(nz)) / J / D
    return C, Dem(r2), routeA, routeB, F(T_lo, D), F(T_hi, D), F(klo[-1], D), F(khi[-1], D)

GRID = None
def make_grid():
    g = [i * (D // 100) for i in range(0, 301)]        # 0..3 step 0.01
    a = g[-1]
    while a < 3000 * D:
        a = up(a * 102, 100); g.append(a)
    return g
import bisect
def floor_cell(r1, r2):
    global GRID
    if GRID is None: GRID = make_grid()
    g = GRID; NA = len(g)
    R1, R2, T_lo, T_hi, klo, khi, Hhi, Hlo, Ghi, Glo = params(r1, r2)
    reach = 0
    for j in range(J):
        reach = up(reach * R2.numerator, R2.denominator) + y_up[0]*0 + max(y_up)
    reach_ok = F(reach, D) < CAP
    Rg1 = [dn(a * R1.numerator, R1.denominator) for a in g]
    Lam = [[a for a in g] for _ in range(nz)]
    for k in range(J - 1):                          # Lambda_{k+1} from Lambda_k, with Phi_{k+1}
        kap, H = khi[k+1], Hhi[k+1]
        new = [[0]*NA for _ in range(nz)]
        for z in range(nz):
            for i in range(NA):
                phi = max(0, dn((D - kap) * (y_dn[z] + Rg1[i]), D) - up(kap * H[z], D))
                j = min(NA - 1, bisect.bisect_right(g, phi) - 1)
                s = fsum_pi(z, [Lam[w][j] for w in range(nz)])
                new[z][i] = g[i] + dn(s.numerator, s.denominator)
        Lam = new
    Fl = sum(nu[z] * Lam[z][0] for z in range(nz)) / J / D
    return Fl, Dem(r1), reach_ok, F(reach, D)

if __name__ == "__main__":
    mode, rlo, rhi, w = sys.argv[1], F(sys.argv[2]), F(sys.argv[3]), F(sys.argv[4])
    r = rlo
    while r < rhi:
        r2 = min(r + w, rhi)
        if mode == "ceil":
            C, Dm, A, B, tl, th, kl, kh = ceiling_cell(r, r2)
            print(f"[{float(r):+.4%},{float(r2):+.4%}] C_hi {float(C):8.4f}  D {float(Dm):8.4f}  {'OK ' if C < Dm else 'FAIL'}  slack A {A} B {B}  Thorn [{float(tl):.5f},{float(th):.5f}] kappa59 [{float(kl):.5f},{float(kh):.5f}]", flush=True)
        else:
            Fl, Dm, ok, rc = floor_cell(r, r2)
            print(f"[{float(r):+.4%},{float(r2):+.4%}] F_lo {float(Fl):8.4f}  D {float(Dm):8.4f}  {'OK ' if Fl > Dm else 'FAIL'}  reach60 {float(rc):.0f} {'<cap' if ok else '>=CAP'}", flush=True)
        r = r2

def mesh(segs):
    """segs: list of (start, stop, width) in rate units; returns breakpoints"""
    b = [segs[0][0]]
    for s, e, w in segs:
        x = s
        while x < e:
            x = min(x + w, e); b.append(x)
    return b
def run_mesh(mode, segs):
    import time
    b = mesh(segs); t0 = time.time(); bad = 0; worst = None
    for i in range(len(b) - 1):
        if mode == "ceil":
            C, Dm, A, B, *_ = ceiling_cell(b[i], b[i+1]); ok = C < Dm and (A or B); marg = float(Dm - C)
        else:
            Fl, Dm, rok, _ = floor_cell(b[i], b[i+1]); ok = Fl > Dm and rok; marg = float(Fl - Dm)
        if not ok: bad += 1; print(f"  FAIL cell [{float(b[i]):.4%},{float(b[i+1]):.4%}] margin {marg:.4f}")
        if worst is None or marg < worst[0]: worst = (marg, b[i], b[i+1])
    print(f"{mode}: {len(b)-1} cells, {bad} failures, worst margin {worst[0]:.4f} at [{float(worst[1]):.4%},{float(worst[2]):.4%}], {time.time()-t0:.0f}s")
