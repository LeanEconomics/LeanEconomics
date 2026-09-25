"""Certificate at EVERY stage: each with its own kappa_k, its own human wealth, its own allowance.
Asset argument carried as intervals over [0, BMAX].  Exact integer arithmetic, outward rounding."""
from fractions import Fraction as F
from math import comb
import sys, time

D = 10**12
def up(n,d): return -((-n)//d)
def dn(n,d): return n//d
def imul(a,b,h): return up(a*b,D) if h else dn(a*b,D)
def idiv(a,b,h): return up(a*D,b) if h else dn(a*D,b)
def q2i(x,h): return up(x.numerator*D,x.denominator) if h else dn(x.numerator*D,x.denominator)

class I:
    __slots__=("l","h")
    def __init__(s,l,h=None): s.l=l; s.h=h if h is not None else l
    def __add__(s,o): return I(s.l+o.l, s.h+o.h)
    def __sub__(s,o): return I(s.l-o.h, s.h-o.l)
    def __mul__(s,o):
        a=[imul(s.l,o.l,False),imul(s.l,o.h,False),imul(s.h,o.l,False),imul(s.h,o.h,False)]
        b=[imul(s.l,o.l,True), imul(s.l,o.h,True), imul(s.h,o.l,True), imul(s.h,o.h,True)]
        return I(min(a),max(b))
    def __truediv__(s,o):
        assert o.l>0
        a=[idiv(s.l,o.l,False),idiv(s.l,o.h,False),idiv(s.h,o.l,False),idiv(s.h,o.h,False)]
        b=[idiv(s.l,o.l,True), idiv(s.l,o.h,True), idiv(s.h,o.l,True), idiv(s.h,o.h,True)]
        return I(min(a),max(b))
def fromF(x): return I(q2i(x,False), q2i(x,True))
ONE=I(D,D)

nz,J=7,60
beta,R1,R2,rho=F(24,25),F(26,25),F(53,50),F(9,10)
def rouwen(n,rho):
    p=(1+rho)/2; P=[[p,1-p],[1-p,p]]
    for m in range(3,n+1):
        Q=[[F(0)]*m for _ in range(m)]
        for i in range(m-1):
            for j in range(m-1):
                Q[i][j]+=p*P[i][j]; Q[i][j+1]+=(1-p)*P[i][j]
                Q[i+1][j]+=(1-p)*P[i][j]; Q[i+1][j+1]+=p*P[i][j]
        P=[[Q[i][j]/sum(Q[i]) for j in range(m)] for i in range(m)]
    return P
Pi=rouwen(nz,rho)
raw=[F(301,1000),F(449,1000),F(670,1000),F(1),F(1492,1000),F(2226,1000),F(3320,1000)]
nu=[F(comb(nz-1,i),2**(nz-1)) for i in range(nz)]
y=[r/sum(nu[i]*raw[i] for i in range(nz)) for r in raw]
Th1=beta*R1; q=R1/R2
kap=[F(1)]
for _ in range(J-1): kap.append(kap[-1]*R1/(Th1+kap[-1]*R1))
yI=[fromF(v) for v in y]; R1I=fromF(R1); PiI=[[fromF(Pi[z][w]) for w in range(nz)] for z in range(nz)]
# human wealth at every stage
HA=[[I(0)]*nz]; HR=[[I(0)]*nz]
for k in range(J-1):
    kp=fromF(kap[k+1]); Ha=HA[-1]; Hr=HR[-1]
    HA.append([sum([PiI[z][w]*(yI[w]+Ha[w]) for w in range(nz)],I(0))/R1I for z in range(nz)])
    hm=[]
    for z in range(nz):
        acc=I(0)
        for w in range(nz): acc=acc+PiI[z][w]/(yI[w]+Hr[w])
        hm.append((ONE/acc)/R1I)
    cap=[(ONE/kp-ONE)*yI[z] for z in range(nz)]
    HR.append([I(min(hm[z].l,cap[z].l),min(hm[z].h,cap[z].h)) for z in range(nz)])

VX=[[(v>>j)&1 for j in range(nz)] for v in range(1<<nz)]
def objmax(a,c,w):
    best=-(1<<62)
    for pat in VX:
        num=I(0); den=I(0)
        for i in range(nz):
            C=I(c[i]) if pat[i] else I(a[i])
            v=ONE/C; num=num+w[i]*v*v; den=den+w[i]*v
        val=num/(den*den)-ONE
        if val.h>best: best=val.h
    return best

def certify(k, z, blo, bhi, ALLOW, cap_nodes=120000):
    """k = stage of NEXT period's consumption; box uses kappa_k, H_k."""
    kp=fromF(kap[k]); w=[PiI[z][t] for t in range(nz)]
    b=I(q2i(F(blo),False), q2i(F(bhi),True))
    m=[yI[t]+R1I*b for t in range(nz)]
    L=[kp*(m[t]+HR[k][t]) for t in range(nz)]
    U0=[kp*(m[t]+HA[k][t]) for t in range(nz)]
    U=[I(min(U0[t].l,m[t].l),min(U0[t].h,m[t].h)) for t in range(nz)]
    dy=[yI[t+1]-yI[t] for t in range(nz-1)]
    lo=[kp*dy[t] for t in range(nz-1)]; hi=dy
    a=[L[t].l for t in range(nz)]; c=[U[t].h for t in range(nz)]
    for t in range(nz):
        if a[t]>=c[t]: a[t]=c[t]-1
    st=[(a,c)]; nd=0
    while st:
        nd+=1
        if nd>cap_nodes: return False,nd
        a,c=st.pop()
        bad=False
        for t in range(nz-1):
            if c[t+1]-a[t]<lo[t].l or a[t+1]-c[t]>hi[t].h: bad=True; break
        if bad: continue
        smin=[dn(max(a[t+1]-c[t],lo[t].l)*D, hi[t].h) for t in range(nz-1)]
        smax=[up(min(c[t+1]-a[t],hi[t].h)*D, max(lo[t].l,1)) for t in range(nz-1)]
        if any(smin[t+1]-smax[t]>0 for t in range(nz-2)): continue
        if objmax(a,c,w)<=ALLOW: continue
        wd,j=max((c[t]-a[t],t) for t in range(nz))
        if wd<=1: return False,nd
        mid=(a[j]+c[j])//2
        st.append((list(a),[c[i] if i!=j else mid for i in range(nz)]))
        st.append(([a[i] if i!=j else mid for i in range(nz)],list(c)))
    return True,nd

if __name__=="__main__":
    BMAX=F(int(sys.argv[1])) if len(sys.argv)>1 else F(12)
    NB=int(sys.argv[2]) if len(sys.argv)>2 else 4
    t0=time.time(); allok=True
    for k in range(1,J):
        ALLOW=q2i(Th1/(q*(1-kap[k]*R1))-1, False) if kap[k]*R1<1 else None
        if ALLOW is None:
            print("stage %2d : kappa_k R >= 1, the multiplier is <= 1 unconditionally" % k); continue
        ok=True; worst=0
        for z in range(nz):
            for i in range(NB):
                r,nd=certify(k,z,BMAX*i/NB,BMAX*(i+1)/NB,ALLOW)
                worst=max(worst,nd)
                if not r: ok=False
        allok = allok and ok
        print("stage %2d : allow %.6f -> %s (worst %d nodes, %.0fs elapsed)" %
              (k, ALLOW/D, "CERTIFIED" if ok else "NOT certified", worst, time.time()-t0), flush=True)
    print("ALL STAGES:", "CERTIFIED" if allok else "NOT certified", "in %.0f s" % (time.time()-t0))
