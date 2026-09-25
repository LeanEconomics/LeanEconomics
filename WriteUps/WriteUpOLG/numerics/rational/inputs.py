"""Rational calibration: Rouwenhorst chain (rational probabilities) and rational income levels."""
from fractions import Fraction as F
from ri import RI, rmin, rmax

nz, J = 7, 60
beta = F(24, 25)        # 0.96
R1   = F(26, 25)        # 1.04
R2   = F(53, 50)        # 1.06
rho  = F(9, 10)

def rouwenhorst(n, rho):
    p = (1 + rho) / 2
    P = [[p, 1 - p], [1 - p, p]]
    for m in range(3, n + 1):
        Q = [[F(0)] * m for _ in range(m)]
        for i in range(m - 1):
            for j in range(m - 1):
                Q[i][j]     += p * P[i][j]
                Q[i][j + 1] += (1 - p) * P[i][j]
                Q[i + 1][j] += (1 - p) * P[i][j]
                Q[i + 1][j + 1] += p * P[i][j]
        for i in range(m):
            s = sum(Q[i])
            P = P  # placeholder
        P = [[Q[i][j] / sum(Q[i]) for j in range(m)] for i in range(m)]
    return P

Pi = rouwenhorst(nz, rho)
# income levels: rational approximations of exp(linspace(-1.2,1.2,7)), then normalised to mean 1
raw = [F(301,1000), F(449,1000), F(670,1000), F(1), F(1492,1000), F(2226,1000), F(3320,1000)]
# invariant law of Rouwenhorst is binomial(n-1, 1/2)
from math import comb
nu = [F(comb(nz - 1, i), 2 ** (nz - 1)) for i in range(nz)]
m1 = sum(nu[i] * raw[i] for i in range(nz))
y = [r / m1 for r in raw]

def kappa(R):
    Th = beta * R                       # gamma = 1
    k = [F(1)]
    for _ in range(J - 1):
        k.append(k[-1] * R / (Th + k[-1] * R))
    return k, Th

if __name__ == "__main__":
    k1, Th1 = kappa(R1)
    q = R1 / R2
    print("Pi row sums all 1:", all(sum(r) == 1 for r in Pi))
    print("nu sums to 1:", sum(nu) == 1, " mean y =", float(sum(nu[i]*y[i] for i in range(nz))))
    print("y =", [round(float(v), 4) for v in y])
    print("q =", q, "=", float(q), "  Th1 =", Th1, "=", float(Th1))
    print("kappa_59 =", float(k1[J-1]), " kappa_0 =", float(k1[0]))
    allow = Th1 / (q * (1 - k1[J-1] * R1)) - 1
    print("allowance at the newborn stage (EXACT) =", allow, "=", float(allow))
