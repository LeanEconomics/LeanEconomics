"""Rational interval arithmetic with directed rounding (exact, arbitrary precision)."""
from fractions import Fraction as F

DEN = 10**12          # denominator cap; rounding is always OUTWARD

def rd(x, up):
    """Round Fraction x to denominator <= DEN, outward in the given direction."""
    n, d = x.numerator * DEN, x.denominator
    q, r = divmod(n, d)
    if r and up:
        q += 1
    return F(q, DEN)

class RI:
    __slots__ = ("lo", "hi")
    def __init__(self, lo, hi=None):
        if hi is None: hi = lo
        self.lo, self.hi = rd(F(lo), False), rd(F(hi), True)
    def __add__(s, o): return RI(s.lo + o.lo, s.hi + o.hi)
    def __sub__(s, o): return RI(s.lo - o.hi, s.hi - o.lo)
    def __mul__(s, o):
        p = [s.lo*o.lo, s.lo*o.hi, s.hi*o.lo, s.hi*o.hi]
        return RI(min(p), max(p))
    def __truediv__(s, o):
        assert o.lo > 0 or o.hi < 0, "division by an interval containing zero"
        p = [s.lo/o.lo, s.lo/o.hi, s.hi/o.lo, s.hi/o.hi]
        return RI(min(p), max(p))
    def __repr__(s): return "[%.10f, %.10f]" % (float(s.lo), float(s.hi))
    def mid(s): return float((s.lo + s.hi) / 2)

def rmin(a, b): return RI(min(a.lo, b.lo), min(a.hi, b.hi))
def rmax(a, b): return RI(max(a.lo, b.lo), max(a.hi, b.hi))
