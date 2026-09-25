"""Rigorous certificate in exact arithmetic.  All quantities are integers over D = 10**12; every
operation rounds OUTWARD, so every interval printed is a true enclosure.  gamma = 1."""
from fractions import Fraction as F
from math import comb
import sys

D = 10**12
def up(n, d):  return -((-n) // d)          # ceiling division
def dn(n, d):  return n // d                # floor division
def imul(a, b, hi):                          # (a/D)*(b/D) -> /D
    return up(a*b, D) if hi else dn(a*b, D)
def idiv(a, b, hi):                          # (a/D)/(b/D) -> /D
    return up(a*D, b) if hi else dn(a*D, b)
def q2i(x, hi):                              # Fraction -> integer over D
    return up(x.numerator*D, x.denominator) if hi else dn(x.numerator*D, x.denominator)

class I:                                     # interval [lo, hi] as integers over D
    __slots__ = ("l", "h")
    def __init__(s, l, h=None): s.l = l; s.h = h if h is not None else l
    def __add__(s, o): return I(s.l+o.l, s.h+o.h)
    def __sub__(s, o): return I(s.l-o.h, s.h-o.l)
    def __mul__(s, o):
        c = [imul(s.l,o.l,False), imul(s.l,o.h,False), imul(s.h,o.l,False), imul(s.h,o.h,False)]
        c2= [imul(s.l,o.l,True),  imul(s.l,o.h,True),  imul(s.h,o.l,True),  imul(s.h,o.h,True)]
        return I(min(c), max(c2))
    def __truediv__(s, o):
        assert o.l > 0
        c = [idiv(s.l,o.l,False), idiv(s.l,o.h,False), idiv(s.h,o.l,False), idiv(s.h,o.h,False)]
        c2= [idiv(s.l,o.l,True),  idiv(s.l,o.h,True),  idiv(s.h,o.l,True),  idiv(s.h,o.h,True)]
        return I(min(c), max(c2))
    def f(s): return (s.l/D, s.h/D)

def fromF(x): return I(q2i(x, False), q2i(x, True))
ONE = I(D, D)

# ---------------------------------------------------------------- calibration
nz, J = 7, 60
beta, R1, R2, rho = F(24,25), F(26,25), F(53,50), F(9,10)
def rouwenhorst(n, rho):
    p = (1+rho)/2; P = [[p,1-p],[1-p,p]]
    for m in range(3, n+1):
        Q = [[F(0)]*m for _ in range(m)]
        for i in range(m-1):
            for j in range(m-1):
                Q[i][j]+=p*P[i][j]; Q[i][j+1]+=(1-p)*P[i][j]
                Q[i+1][j]+=(1-p)*P[i][j]; Q[i+1][j+1]+=p*P[i][j]
        P = [[Q[i][j]/sum(Q[i]) for j in range(m)] for i in range(m)]
    return P
Pi = rouwenhorst(nz, rho)
raw = [F(301,1000),F(449,1000),F(670,1000),F(1),F(1492,1000),F(2226,1000),F(3320,1000)]
nu = [F(comb(nz-1,i), 2**(nz-1)) for i in range(nz)]
y  = [r/sum(nu[i]*raw[i] for i in range(nz)) for r in raw]
Th1 = beta*R1; q = R1/R2
kap = [F(1)]
for _ in range(J-1): kap.append(kap[-1]*R1/(Th1+kap[-1]*R1))
k59 = kap[J-1]
allow = Th1/(q*(1-k59*R1)) - 1
ALLOW = q2i(allow, False)                     # use the LOWER bound of the allowance
# human wealth, as intervals
Ha = [I(0)]*nz; Hr = [I(0)]*nz
yI = [fromF(v) for v in y]; R1I = fromF(R1)
for k in range(J-1):
    kp = fromF(kap[k+1])
    Ha = [sum([fromF(Pi[z][w])*(yI[w]+Ha[w]) for w in range(nz)], I(0))/R1I for z in range(nz)]
    hm = []
    for z in range(nz):
        acc = I(0)
        for w in range(nz): acc = acc + fromF(Pi[z][w])/(yI[w]+Hr[w])
        hm.append((ONE/acc)/R1I)
    cap = [(ONE/kp - ONE)*yI[z] for z in range(nz)]
    Hr = [I(min(hm[z].l,cap[z].l), min(hm[z].h,cap[z].h)) for z in range(nz)]
KP = fromF(kap[J-1])
print("allowance (lower bound) = %.12f" % (ALLOW/D))
print("kappa_59 = %.12f   H_risk[0] = %s   H_arith[0] = %s" % (float(k59), Hr[0].f(), Ha[0].f()))

# ------------------------------------------------------- objective and the B&B
VX = [[(v>>j)&1 for j in range(nz)] for v in range(1<<nz)]
def objmax(cl, ch, w):
    """exact max of sum w v^2/(sum w v)^2 - 1 over the box, = max over its 2^nz vertices"""
    best = -(1<<62)
    for pat in VX:
        num = I(0); den = I(0)
        for i in range(nz):
            C = I(ch[i]) if pat[i] else I(cl[i])
            v = ONE/C
            num = num + w[i]*v*v
            den = den + w[i]*v
        val = (num/(den*den) - ONE)
        if val.h > best: best = val.h
    return best

def certify(z, blo, bhi, verbose=False):
    w = [fromF(Pi[z][t]) for t in range(nz)]
    b = I(q2i(F(blo),False), q2i(F(bhi),True))
    m  = [yI[t] + R1I*b for t in range(nz)]
    L  = [KP*(m[t]+Hr[t]) for t in range(nz)]
    U  = [KP*(m[t]+Ha[t]) for t in range(nz)]
    U  = [I(min(U[t].l, m[t].l), min(U[t].h, m[t].h)) for t in range(nz)]
    dy = [yI[t+1]-yI[t] for t in range(nz-1)]
    lo = [KP*dy[t] for t in range(nz-1)]; hi = dy
    cl = [L[t].l for t in range(nz)]; ch = [U[t].h for t in range(nz)]
    for t in range(nz):
        if cl[t] >= ch[t]: cl[t] = ch[t]-1
    stack = [(cl, ch)]; nodes = 0
    while stack:
        nodes += 1
        if nodes > 60000: return False, nodes
        a, c = stack.pop()
        okpoly = True
        for t in range(nz-1):
            if c[t+1]-a[t] < lo[t].l or a[t+1]-c[t] > hi[t].h: okpoly = False; break
        if not okpoly: continue
        smin = [dn((max(a[t+1]-c[t], lo[t].l))*D, hi[t].h) for t in range(nz-1)]
        smax = [up((min(c[t+1]-a[t], hi[t].h))*D, max(lo[t].l,1)) for t in range(nz-1)]
        if any(smin[t+1] - smax[t] > 0 for t in range(nz-2)): continue
        if objmax(a, c, w) <= ALLOW: continue
        wd, j = max((c[t]-a[t], t) for t in range(nz))
        if wd <= 1: return False, nodes
        mid = (a[j]+c[j])//2
        a2 = list(a); c2 = list(c); c2[j] = mid
        a3 = list(a); c3 = list(c); a3[j] = mid
        stack.append((a2, c2)); stack.append((a3, c3))
    return True, nodes

if __name__ == "__main__":
    import time
    NB = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    edges = [F(3*i, NB) for i in range(NB+1)]
    allok = True; worst = 0; t0 = time.time()
    for z in range(nz):
        for i in range(NB):
            ok, nd = certify(z, edges[i], edges[i+1])
            worst = max(worst, nd)
            if not ok:
                allok = False
                print("  NOT certified: z=%d, b in [%s, %s] after %d nodes" % (z, edges[i], edges[i+1], nd))
    print("newborn stage, b in [0,3] split into %d intervals x %d states: %s" %
          (NB, nz, "CERTIFIED" if allok else "NOT certified"))
    print("worst node count %d ; %.1f s" % (worst, time.time()-t0))
