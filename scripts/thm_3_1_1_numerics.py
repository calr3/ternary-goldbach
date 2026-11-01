from mpmath import mp, mpf, sqrt, log, pi, e, zeta, floor, exp
mp.dps = 30
c0 = mpf('31.521'); c2 = 6*pi/(5*sqrt(c0)); L1 = 8*log(2)
zeta3 = mpf('1.27')*zeta(mpf(1.5))**3
def logPlus(y): return max(log(y),0) if y>0 else 0
def minInv(c,d): return 1 if d==0 else min(1, c/d**2)
def muBound(U,q,tq):  # tq = totient(2q)
    if 2*q*q < U: return min(1, mpf(4)/5*(2*q/tq)/log(U/(2*q*q)))
    return 1
def logFB(d): return 2-log(4) if d==0 else min(2-log(4), 96*log(2)/(pi*d)**2)
def b441(x,q,D):
    c1 = 1+L1/(x/D)
    return (2*sqrt(c0*c1)/pi*D*log(e*x/D) + 3*c1/2*(x/q)*logPlus(D/(c2*x/q))*log(q/c2)
      + (2*L1/pi*max(1,log(c0*e**3*q*q/(4*pi*L1*x)))*log(x) + 2*sqrt(c0*c1)/pi*(sqrt(3)+0.5*logPlus(D/(q/2)))*log(q/c2))*q
      + 3*c1/2*sqrt(2*x/c2)*log(2*x/c2) + 20*c0*c2**1.5/(3*pi**2)*sqrt(2*x)*log(2*e*x/c2))
def typeI1(x,d,q,U,phi2q):
    return (x/(2*q)*minInv(c0,pi*d)*(mpf('1.00303')*(2*q/phi2q)+log(x/U)*muBound(U,q,phi2q))
      + x/(2*q)*logFB(d)*muBound(U,q,phi2q) + c0*(0.5-2/pi**2)*(U**2/(4*q*x)*log(exp(0.5)*x/U)+1/e)
      + b441(x,q,U))
def cPlus(x,U,V): return 1+L1/(x/(U*V))
def coefUV(c): return 2*sqrt(c0*c)/pi + 3*c/(2*c2*e)
def coefQ(x,q,U,V,c):
    return (sqrt(c0*c)/pi*(logPlus(2*U/q)+1/e) + 2*L1/pi*max(1,log(c0*e**3*q*q*V/(4*pi*L1*x)))
            + (2*sqrt(3*c0*c)/pi + 3*c/(2*c2) + 55*c0*c2/(6*pi**2)))
def typeI2(x,d,q,Q,U,V,phi2q,eps=mpf('0.07')):
    M0=min(Q/(2*V),U)
    common = (x/(2*q)*minInv(c0,pi*d)*muBound(M0,q,phi2q)*log(V*q)
      + c0*(mpf(1)/8-1/(2*pi**2))/x*(U**2/q*(mpf('0.5004')*V**2+V*q*log(q))+(2*U+q)*mpf('0.5004')*V**2))
    c=cPlus(x,U,V)
    if abs(d) <= 1/(2*c2):
        return common + mpf('1.0004')*coefUV(c)*U*V + mpf('1.0004')*coefQ(x,q,U,V,c)*Q
    ad=abs(d)
    return (common + mpf('1.0004')*(2*sqrt(c0*c)/pi*(1+(1+eps)*(1+V/Q)/e))*U*V
      + mpf('1.0004')*(1.5*c*(2+(1+eps)/eps*logPlus(2*U*V*ad*q/x)))*(x*V/Q)
      + mpf('1.0004')*(35*c0*c2/(3*pi**2))*Q
      + 2*sqrt(c0*c)/pi*(1+eps)*sqrt(3+2*eps)*(x/(ad*q)*(mpf('1.03883')+log(q)+logPlus(6*U*V*ad*q/(sqrt(2)*x)))+mpf('1.0004')*V))
def kap1(x,U,V): return 2/pi**2+zeta3*sqrt(x/V)/U
def typeII637(x,q,U,V,phi):
    L0=log(x/(U*V))
    return (x/sqrt(2*phi)*sqrt((L0+log(2*q)*(log(log(x/U/(2*q)))-log(log(V/(2*q)))))*(mpf('0.60428')*L0+mpf('0.0924')+8*zeta3*sqrt(x/V)/U))
      + 4*sqrt(kap1(x,U,V)*q*x/(2*phi))*(2*sqrt(x/U)+sqrt(log(2*q))*(2*e*sqrt(2*q)+4*sqrt(x/U/log(x/U/(2*q)))))
      + 8*mpf('1.4262')*x*sqrt(kap1(x,U,V)*(0.5+1/U))/sqrt(V))
def typeII640(x,d,q,Q,U,V,phi):
    ad=abs(d); c=ad*q*(1+x/(2*U*Q))/4; L0=log(x/(U*V))
    return (2*x/sqrt(ad*phi)*sqrt((L0+log(c)*(log(log(x/U/c))-log(log(V/c))))*(mpf('0.60428')*L0+mpf('0.0924')+8*zeta3*sqrt(x/V)/U))
      + 4*sqrt(kap1(x,U,V)*q*x/(2*phi))*(2*sqrt(x/U)+sqrt(log(c))*(2*e*sqrt(c)+4*sqrt(x/U/log(x/U/c))))
      + 8*mpf('1.4262')*x*sqrt(kap1(x,U,V)*(0.5+1/U))/sqrt(V))
def R(x,t): return mpf('0.27125')*log(1+log(4*t)/(2*log(9*x**(mpf(1)/3)/(mpf('2.004')*t))))+mpf('0.41415')
def Lf(t,q,phi): return q/phi*(mpf(13)/4*log(t)+mpf('7.82'))+mpf('13.66')*log(t)+mpf('37.55')
CONST=mpf("0.8764")
def thm(x,d,q,phi):
    d0=max(2,abs(d)/4); t=d0*q
    return ((R(x,t)*log(t)+CONST)/sqrt(d0*phi)*x + 2.5*x/sqrt(t) + 2*x/t*Lf(t,q,phi) + mpf('3.36')*x**(mpf(5)/6))
def ours(x,d,q,phi,phi2q):
    t3=x**(mpf(1)/3); Q=mpf(3)/4*t3**2; d0=max(2,abs(d)/4)
    U=floor(t3**2/(9*sqrt(q*d0))); V=floor(9*t3/2)
    i1=typeI1(x,d,q,U,phi2q); i2=typeI2(x,d,q,Q,U,V,phi2q)
    ii=typeII637(x,q,U,V,phi)
    if abs(d)>=8: ii=min(ii,typeII640(x,d,q,Q,U,V,phi))
    return i1,i2,ii,3*log(x)

# ---------------------------------------------------------------------------
# Numerical comparison of our assembled bound (the right-hand sides of the Lean theorems
# typeI1_le, typeI2_le_small/large, typeII_637/640, plus 3 log x) with [B, Theorem 3.1.1]
# for q <= x^{1/3}/6, at the parameters of [B, (6.49)] (U, V rounded down).
# Usage: python3 thm_3_1_1_numerics.py   (needs mpmath, sympy)
if __name__ == "__main__":
    import sys
    from sympy import totient
    import random
    random.seed(1)
    CONST = mpf(sys.argv[1]) if len(sys.argv) > 1 else mpf("0.8764")
    globals()["CONST"] = CONST
    for x in [mpf('2.16e20'), mpf('1e22'), mpf('1e27'), mpf('1e40'), mpf('1e60')]:
        y = x**(mpf(1)/3)/6
        qs = set([1, 2, 3, 6, 30, 210, 2310, 30030, 510510, int(y), int(y/3)])
        for k in range(30):
            qs.add(int(10**(random.uniform(0, float(log(y, 10))))))
        m = (0, None)
        for q in sorted(qs):
            if q < 1 or q > y:
                continue
            phi = mpf(int(totient(q))); phi2q = mpf(int(totient(2*q)))
            dmax = float(8*y/q)
            for d in [0, 0.3, 0.75, 1, 2, 4, 7.99, 8, 16, 300, dmax/10, dmax]:
                if d > dmax:
                    continue
                o = ours(x, mpf(d), q, phi, phi2q); T = thm(x, mpf(d), q, phi); r = sum(o)/T
                if r > m[0]:
                    m = (r, (q, d))
        print(f"x={float(x):.1e}: worst ratio ours/Thm3.1.1 = {float(m[0]):.4f} at (q, delta) = {m[1]}")
